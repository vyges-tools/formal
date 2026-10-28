//! The campaign's stages, in the order `run` calls them: provenance, prepare_rtl, bind_monitors,
//! synthesize, lint, prove_all, replay, mutants. The report is [`crate::report`].

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::Duration;

use regex::Regex;
use serde_json::{json, Map, Value};

use crate::bits::Bits;
use crate::exec::{self, run, sha256, tail};
use crate::manifest::{Item, Manifest, Mutant};

pub type Obj = Map<String, Value>;

/// The programs a campaign drives, resolved once.
#[derive(Clone, Debug)]
pub struct Tools {
    pub lec: String,
    pub yosys: String,
    pub liberty: PathBuf,
    /// Replays counterexamples; without it they are reported unreplayed.
    pub verilator: Option<String>,
    /// Converts SystemVerilog for `[rtl] frontend = "sv2v"`.
    pub sv2v: Option<String>,
}

/// Cells the proof model must not use: power-gating/isolation and probe cells, and enable flops — the
/// prover cannot yet read a `next_state` that refers to the flop's own state, so yosys builds an
/// enable as a mux in front of a plain flop instead.
pub const DEFAULT_DONT_USE: [&str; 4] = ["*lpflow*", "*probe*", "*edfxtp*", "*edfxbp*"];

fn module_re() -> Regex {
    Regex::new(r"(?sm)^module\s+(\w+)\b.*?^endmodule\b").unwrap()
}

fn module_def_re(name: &str) -> Regex {
    Regex::new(&format!(r"(?sm)^module\s+{}\b.*?^endmodule\b", regex::escape(name))).unwrap()
}

fn sh(args: &[&str]) -> Vec<String> {
    args.iter().map(|s| s.to_string()).collect()
}

fn write(p: &Path, s: &str) -> Result<(), String> {
    std::fs::write(p, s).map_err(|e| format!("{}: {e}", p.display()))
}

fn read(p: &Path) -> Result<String, String> {
    std::fs::read_to_string(p).map_err(|e| format!("{}: {e}", p.display()))
}

pub fn now_utc() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0) as i64;
    let (days, rem) = (secs.div_euclid(86400), secs.rem_euclid(86400));
    // civil-from-days (Howard Hinnant)
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = yoe + era * 400 + i64::from(m <= 2);
    format!("{y:04}-{m:02}-{d:02}T{:02}:{:02}:{:02}Z", rem / 3600, rem % 3600 / 60, rem % 60)
}

// ---------------------------------------------------------------------------------------------
// provenance
// ---------------------------------------------------------------------------------------------

/// The RTL's commit (and whether its tree is dirty), a sha256 of every input, the tool versions.
pub fn provenance(m: &Manifest, tools: &Tools) -> Result<Obj, String> {
    let mut p = Obj::new();
    p.insert("manifest".into(), json!(m.path.to_string_lossy()));
    p.insert("manifest_sha256".into(), json!(sha256(&m.path).map_err(|e| e.to_string())?));
    p.insert("run_utc".into(), json!(now_utc()));
    if let Some(repo) = m.repo() {
        let git = |a: &[&str]| -> String {
            let mut cmd = vec!["git".to_string(), "-C".into(), repo.to_string_lossy().into_owned()];
            cmd.extend(a.iter().map(|s| s.to_string()));
            run(&cmd, None, None).map(|r| r.out.trim().to_string()).unwrap_or_default()
        };
        p.insert("rtl_repo".into(), json!(repo.to_string_lossy()));
        let remote = git(&["config", "--get", "remote.origin.url"]);
        let commit = git(&["rev-parse", "HEAD"]);
        p.insert("rtl_remote".into(), json!(remote));
        p.insert("rtl_commit".into(), json!(commit));
        p.insert("rtl_commit_date".into(), json!(git(&["log", "-1", "--format=%cI", "HEAD"])));
        p.insert("rtl_commit_subject".into(), json!(git(&["log", "-1", "--format=%s", "HEAD"])));
        let web = Regex::new(r"^git@github\.com:").unwrap().replace(&remote, "https://github.com/");
        let web = Regex::new(r"\.git$").unwrap().replace(&web, "").into_owned();
        if web.starts_with("https://github.com/") {
            p.insert("rtl_commit_url".into(), json!(format!("{web}/commit/{commit}")));
        }
        let mut a = vec!["status", "--porcelain", "--"];
        let files = m.rtl_files();
        a.extend(files.iter().map(String::as_str));
        p.insert("rtl_dirty".into(), json!(!git(&a).is_empty()));
    }
    let mut rf = Obj::new();
    for f in m.rtl_files() {
        rf.insert(f.clone(), json!(sha256(&m.rtl_path(&f)).map_err(|e| format!("{f}: {e}"))?));
    }
    p.insert("rtl_files".into(), Value::Object(rf));
    p.insert("liberty".into(), json!(tools.liberty.to_string_lossy()));
    p.insert(
        "liberty_sha256".into(),
        json!(sha256(&tools.liberty).map_err(|e| format!("{}: {e}", tools.liberty.display()))?),
    );
    let ver = |c: &[String]| run(c, None, None).map(|r| r.out.trim().to_string()).unwrap_or_default();
    p.insert("yosys".into(), json!(ver(&[tools.yosys.clone(), "-V".into()])));
    p.insert("lec".into(), json!(ver(&[tools.lec.clone(), "--version".into()])));
    p.insert("formal".into(), json!(format!("vyges-formal {}", crate::VERSION)));
    let mut mon = Obj::new();
    for b in &m.binds {
        mon.insert(b.file.clone(), json!(sha256(&m.p(&b.file)).map_err(|e| format!("{}: {e}", b.file))?));
    }
    p.insert("monitors".into(), Value::Object(mon));
    Ok(p)
}

// ---------------------------------------------------------------------------------------------
// prepare_rtl
// ---------------------------------------------------------------------------------------------

/// The top's module closure from a text holding more than the IP: the top, then every module it
/// instantiates, transitively.
pub fn extract_closure(text: &str, top: &str) -> Result<(String, Vec<String>), String> {
    let mut mods: HashMap<String, String> = HashMap::new();
    for c in module_re().captures_iter(text) {
        mods.insert(c[1].to_string(), c[0].to_string());
    }
    if !mods.contains_key(top) {
        return Err(format!("top `{top}` not found in the RTL"));
    }
    let inst = Regex::new(r"(?m)^\s*(\w+)\s*(?:#\s*\(|\s+\w+\s*\()").unwrap();
    let (mut seen, mut todo): (Vec<String>, Vec<String>) = (vec![], vec![top.to_string()]);
    while let Some(n) = todo.pop() {
        if seen.contains(&n) {
            continue;
        }
        seen.push(n.clone());
        for c in inst.captures_iter(&mods[&n]) {
            let cand = c[1].to_string();
            if mods.contains_key(&cand) && !seen.contains(&cand) {
                todo.push(cand);
            }
        }
    }
    let body: Vec<&str> = seen.iter().map(|n| mods[n].as_str()).collect();
    Ok((body.join("\n\n") + "\n", seen))
}

/// The RTL as one Verilog text: the files joined as written (`frontend = "yosys"`, the default), or
/// converted from SystemVerilog by sv2v (`frontend = "sv2v"`) with the include dirs and defines, for
/// the SystemVerilog the yosys frontend does not read (packages, imports, interfaces).
pub fn prepare_rtl(m: &Manifest, tools: &Tools, work: &Path) -> Result<(String, Vec<String>), String> {
    let text = match m.frontend().as_str() {
        "yosys" => {
            let parts = m.rtl_files().iter().map(|f| read(&m.rtl_path(f))).collect::<Result<Vec<_>, _>>()?;
            parts.join("\n")
        }
        "sv2v" => {
            let Some(sv2v) = &tools.sv2v else {
                return Err("[rtl] frontend = \"sv2v\" but sv2v is not installed (or pass --sv2v)".into());
            };
            let mut cmd = vec![sv2v.clone()];
            cmd.extend(m.include_dirs().iter().map(|d| format!("-I{}", m.rtl_path(d).display())));
            cmd.extend(m.defines().iter().map(|d| format!("-D{d}")));
            cmd.extend(m.rtl_files().iter().map(|f| m.rtl_path(f).to_string_lossy().into_owned()));
            let r = run(&cmd, None, None).map_err(|e| format!("cannot run {sv2v}: {e}"))?;
            if !r.ok() {
                return Err(format!("sv2v failed:\n{}", tail(&r.err, 2000)));
            }
            r.out
        }
        other => return Err(format!("[rtl] frontend must be \"yosys\" or \"sv2v\", not {other:?}")),
    };
    let (text, mods) = if m.extract_top() {
        extract_closure(&text, &m.top())?
    } else {
        let mods = module_re().captures_iter(&text).map(|c| c[1].to_string()).collect();
        (text, mods)
    };
    write(&work.join("rtl.v"), &text)?;
    Ok((text, mods))
}

// ---------------------------------------------------------------------------------------------
// bind_monitors
// ---------------------------------------------------------------------------------------------

/// The ids a monitor defines for one kind (`p` property, `c` cover, `a` assumption).
pub fn monitor_ids(src: &str, kind: &str) -> Vec<String> {
    Regex::new(&format!(r"\bvf_{kind}_([a-z][a-z0-9_]*)\b\s*="))
        .unwrap()
        .captures_iter(src)
        .map(|c| c[1].to_string())
        .collect()
}

/// Splice every monitor into its module, with the generated arming, assumption and gating logic.
/// Returns the bound text and, per claim id, the module it lives in.
pub fn bind_monitors(m: &Manifest, text: &str) -> Result<(String, HashMap<String, String>), String> {
    let mut text = text.to_string();
    let mut owner = HashMap::new();
    for b in &m.binds {
        let src = read(&m.p(&b.file))?;
        let (clk, rst) = (&b.clock, &b.reset);
        let rst_on = if b.reset_active_low { format!("~{rst}") } else { rst.clone() };
        let (props, covs, asms) = (monitor_ids(&src, "p"), monitor_ids(&src, "c"), monitor_ids(&src, "a"));
        for i in props.iter().chain(&covs) {
            owner.insert(i.clone(), b.module.clone());
        }
        let mut gen = vec![
            format!("\n\t// ---- vformal: monitor {} bound into {} ----", b.file, b.module),
            "\treg vf_seen_rst;".to_string(),
            format!("\talways @(posedge {clk}) vf_seen_rst <= vf_seen_rst | {rst_on};"),
            format!("\twire vf_armed = vf_seen_rst & ~({rst_on});"),
        ];
        for a in &asms {
            gen.push(format!("\treg vf_av_{a};"));
            gen.push(format!("\talways @(posedge {clk}) if (vf_armed) vf_av_{a} <= vf_av_{a} | ~vf_a_{a};"));
            gen.push(format!("\twire vf_aok_{a} = ~vf_av_{a} & (vf_a_{a} | ~vf_armed);"));
        }
        let items = m
            .properties
            .iter()
            .filter(|p| props.contains(&p.id))
            .map(|p| ("p", p))
            .chain(m.covers.iter().filter(|c| covs.contains(&c.id)).map(|c| ("c", c)));
        for (kind, item) in items {
            for a in &item.assumptions {
                if !asms.contains(a) {
                    return Err(format!("`{}` uses assumption `{a}`, not defined as vf_a_{a} in {}", item.id, b.file));
                }
            }
            let mut terms = vec!["vf_armed".to_string(), format!("vf_{kind}_{}", item.id)];
            terms.extend(item.assumptions.iter().map(|a| format!("vf_aok_{a}")));
            gen.push(format!("\twire vf_g_{} = {};", item.id, terms.join(" & ")));
        }
        let block = format!("{}\n{}\n", src.trim_end(), gen.join("\n"));
        let defs: Vec<_> = module_def_re(&b.module).find_iter(&text).collect();
        if defs.len() != 1 {
            return Err(format!("bind target `{}` defined {} times (need exactly 1)", b.module, defs.len()));
        }
        let end = defs[0].end() - "endmodule".len();
        text = format!("{}{}{}", &text[..end], block, &text[end..]);
    }
    let missing: Vec<&str> =
        m.properties.iter().chain(&m.covers).map(|i| i.id.as_str()).filter(|i| !owner.contains_key(*i)).collect();
    if !missing.is_empty() {
        return Err(format!("no monitor defines vf_p_/vf_c_ for: {missing:?}"));
    }
    Ok((text, owner))
}

// ---------------------------------------------------------------------------------------------
// synthesize
// ---------------------------------------------------------------------------------------------

fn yosys_front(m: &Manifest) -> Vec<String> {
    let top = m.top();
    let defs: Vec<String> = m.defines().iter().map(|d| format!("-D{d}")).collect();
    let mut c = vec![format!("read_verilog -sv {} rtl.bound.v", defs.join(" "))];
    for (k, v) in m.params() {
        c.push(format!("chparam -set {k} {v} {top}"));
    }
    c.extend([format!("hierarchy -check -top {top}"), "proc".into(), "flatten".into()]);
    c
}

/// After flattening, each monitor net carries its instance path; the pass-1 log lists them.
fn flat_names(log: &str, top: &str) -> HashMap<String, String> {
    let re = Regex::new(&format!(r"^{}/(.*\bvf_g_([a-z0-9_]+))$", regex::escape(top))).unwrap();
    let mut names = HashMap::new();
    for line in log.lines() {
        if let Some(c) = re.captures(line.trim()) {
            names.insert(c[2].to_string(), c[1].to_string());
        }
    }
    names
}

fn run_yosys(tools: &Tools, work: &Path, script: &str, log: &str, what: &str) -> Result<(), String> {
    let r = run(&sh(&[&tools.yosys, "-q", "-s", script, "-l", log]), None, Some(work))
        .map_err(|e| format!("cannot run yosys ({}): {e}", tools.yosys))?;
    if !r.ok() {
        return Err(format!("yosys {what} failed; see {}\n{}", work.join(log).display(), tail(&r.err, 2000)));
    }
    Ok(())
}

/// Pass 1 lists the flattened monitor nets; pass 2 renames and exposes them and maps to cells.
pub fn synthesize(m: &Manifest, tools: &Tools, work: &Path, ids: &[String], tag: &str) -> Result<PathBuf, String> {
    let (top, lib) = (m.top(), tools.liberty.to_string_lossy().into_owned());
    let mut p1 = yosys_front(m);
    p1.extend(["select -list w:*vf_g_*".to_string(), format!("write_json {tag}.pre.json")]);
    write(&work.join(format!("{tag}.pass1.ys")), &(p1.join("\n") + "\n"))?;
    run_yosys(tools, work, &format!("{tag}.pass1.ys"), &format!("{tag}.pass1.log"), &format!("pass 1 ({tag})"))?;
    let names = flat_names(&read(&work.join(format!("{tag}.pass1.log")))?, &top);
    let lost: Vec<&String> = ids.iter().filter(|i| !names.contains_key(*i)).collect();
    if !lost.is_empty() {
        return Err(format!("monitor nets not found after flatten ({tag}): {lost:?}"));
    }
    let dont_use = m.synth_list("dont_use").unwrap_or_else(|| DEFAULT_DONT_USE.iter().map(|s| s.to_string()).collect());
    let dont: Vec<String> = dont_use.iter().map(|c| format!("-dont_use {c}")).collect();
    let dont = dont.join(" ");
    let buf = m.synth_str("buffer").unwrap_or_else(|| "sky130_fd_sc_hd__buf_1 A X".into());
    let tie = m.synth_str("tie").unwrap_or_else(|| "sky130_fd_sc_hd__conb_1 HI LO".into());
    let t: Vec<&str> = tie.split_whitespace().collect();
    if t.len() < 3 {
        return Err(format!("[synth] tie must be `CELL HI_PIN LO_PIN`, got {tie:?}"));
    }
    let mut c = yosys_front(m);
    c.push(format!("cd {top}"));
    for i in ids {
        if names[i] != format!("vf_g_{i}") {
            c.push(format!("rename {} vf_g_{i}", names[i]));
        }
    }
    let exposed: Vec<String> = ids.iter().map(|i| format!("w:vf_g_{i}")).collect();
    c.extend([
        "cd ..".to_string(),
        format!("expose {}", exposed.join(" ")),
        format!("synth -top {top}"),
        format!("dfflibmap -liberty {lib} {dont}"),
        format!("abc -liberty {lib} {dont}"),
        "opt_clean -purge".into(),
        format!("hilomap -singleton -hicell {} {} -locell {} {}", t[0], t[1], t[0], t[2]),
        format!("insbuf -buf {buf}"),
        format!("stat -liberty {lib}"),
        format!("write_verilog -noattr -noexpr {tag}.nl.v"),
    ]);
    write(&work.join(format!("{tag}.pass2.ys")), &(c.join("\n") + "\n"))?;
    run_yosys(tools, work, &format!("{tag}.pass2.ys"), &format!("{tag}.pass2.log"), &format!("pass 2 ({tag})"))?;
    Ok(work.join(format!("{tag}.nl.v")))
}

// ---------------------------------------------------------------------------------------------
// lint
// ---------------------------------------------------------------------------------------------

/// Registers by reset style, from the flattened pre-synthesis design.
pub fn lint(work: &Path, tag: &str) -> Result<Obj, String> {
    let d: Value = serde_json::from_str(&read(&work.join(format!("{tag}.pre.json")))?)
        .map_err(|e| format!("{tag}.pre.json: {e}"))?;
    let (mut no_reset, mut sync_reset, mut async_reset, mut monitor) = (vec![], vec![], 0u64, 0u64);
    let idx = Regex::new(r"\[\d+\]$").unwrap();
    let empty = Map::new();
    for module in d["modules"].as_object().unwrap_or(&empty).values() {
        let mut bitname: HashMap<String, String> = HashMap::new();
        for (n, nn) in module["netnames"].as_object().unwrap_or(&empty) {
            if nn.get("hide_name").and_then(Value::as_i64).unwrap_or(0) != 0 {
                continue;
            }
            let bits = nn["bits"].as_array().cloned().unwrap_or_default();
            for (k, bit) in bits.iter().enumerate() {
                let name = if bits.len() > 1 { format!("{n}[{k}]") } else { n.clone() };
                bitname.entry(bit.to_string()).or_insert(name);
            }
        }
        for c in module["cells"].as_object().unwrap_or(&empty).values() {
            let t = c["type"].as_str().unwrap_or("");
            if !t.starts_with('$') || !t.contains("dff") && !t.contains("dlatch") {
                continue;
            }
            let mut qs: Vec<String> = c["connections"]["Q"]
                .as_array()
                .map(|q| {
                    q.iter()
                        .map(|b| idx.replace(bitname.get(&b.to_string()).map(String::as_str).unwrap_or("?"), "").into_owned())
                        .collect()
                })
                .unwrap_or_default();
            qs.sort();
            qs.dedup();
            if qs.iter().any(|q| q.contains("vf_")) {
                monitor += 1;
            } else if t == "$dff" || t == "$dffe" {
                no_reset.extend(qs);
            } else if t.starts_with("$sdff") {
                sync_reset.extend(qs);
            } else {
                async_reset += 1;
            }
        }
    }
    for v in [&mut no_reset, &mut sync_reset] {
        v.sort();
        v.dedup();
    }
    let mut r = Obj::new();
    r.insert("no_reset".into(), json!(no_reset));
    r.insert("sync_reset".into(), json!(sync_reset));
    r.insert("async_reset".into(), json!(async_reset));
    r.insert("monitor".into(), json!(monitor));
    Ok(r)
}

// ---------------------------------------------------------------------------------------------
// prove_all
// ---------------------------------------------------------------------------------------------

/// `vyges-lec prove --never NET`: the verdict, and the counterexample when there is one.
pub fn prove_one(tools: &Tools, netlist: &Path, net: &str, bound: i64, timeout_s: f64, out: &Path) -> Obj {
    let mut cmd = vec![
        tools.lec.clone(),
        "prove".into(),
        netlist.to_string_lossy().into_owned(),
        "--lib".into(),
        tools.liberty.to_string_lossy().into_owned(),
        "--never".into(),
        net.into(),
        "--json".into(),
        "-o".into(),
        out.to_string_lossy().into_owned(),
    ];
    if bound != 0 {
        cmd.extend(["--bound".into(), bound.to_string()]);
    }
    let _ = std::fs::remove_file(out);
    let ran = run(&cmd, Some(Duration::from_secs_f64(timeout_s)), None);
    let mut r = Obj::new();
    r.insert("net".into(), json!(net));
    r.insert("bound".into(), if bound != 0 { json!(bound) } else { Value::Null });
    let secs = ran.as_ref().map(|x| x.secs).unwrap_or(0.0);
    r.insert("seconds".into(), json!((secs * 10.0).round() / 10.0));
    r.insert("cmd".into(), json!(cmd.join(" ")));
    let ran = match ran {
        Ok(x) => x,
        Err(e) => {
            r.insert("verdict".into(), json!("error"));
            r.insert("error".into(), json!(format!("cannot run {}: {e}", tools.lec)));
            return r;
        }
    };
    if ran.timed_out {
        r.insert("verdict".into(), json!("timeout"));
        return r;
    }
    match std::fs::read_to_string(out).ok().and_then(|t| serde_json::from_str::<Value>(&t).ok()) {
        Some(j) => {
            r.insert("verdict".into(), j.get("verdict").cloned().unwrap_or(json!("error")));
            r.insert("registers".into(), j.get("registers").cloned().unwrap_or(Value::Null));
            if let Some(f) = j.get("fails") {
                r.insert("trace".into(), f.clone());
            }
        }
        None => {
            r.insert("verdict".into(), json!("error"));
            let e = if ran.err.is_empty() { &ran.out } else { &ran.err };
            r.insert("error".into(), json!(tail(e, 1500)));
        }
    }
    r
}

pub fn verdict(r: &Obj) -> &str {
    r.get("verdict").and_then(Value::as_str).unwrap_or("error")
}

/// `as-expected` · `FINDING` (a recorded design defect reproduced) · `UNEXPECTED`.
///
/// `expect` comes from the specification. A defect, once triaged, is recorded with the expectation
/// that reproduces it (`fails` / `unreachable`) plus `finding` text, and reads FINDING — never as a
/// pass. A cover's result is also recorded under `cover`.
pub fn classify(item: &Item, kind: &str, r: &mut Obj) -> String {
    let v = verdict(r).to_string();
    let (got, exp) = if kind == "property" {
        let got = match v.as_str() {
            "holds" | "holds_within" => "holds".to_string(),
            "fails" => "fails".into(),
            "timeout" => "undecided".into(),
            o => o.into(),
        };
        (got, item.expect.clone().unwrap_or_else(|| "holds".into()))
    } else {
        let got = match v.as_str() {
            "fails" => "reached".to_string(),
            "holds" => "unreachable".into(),
            "holds_within" => "not-reached".into(),
            "timeout" => "undecided".into(),
            o => o.into(),
        };
        r.insert("cover".into(), json!(got));
        (got, item.expect.clone().unwrap_or_else(|| "reached".into()))
    };
    if got != exp {
        "UNEXPECTED".into()
    } else if item.finding.is_some() && (got == "fails" || got == "unreachable") {
        "FINDING".into()
    } else {
        "as-expected".into()
    }
}

/// `f` over `items` on `jobs` threads; the results come back in `items` order.
pub fn par_map<T: Sync, R: Send>(items: &[T], jobs: usize, f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let next = AtomicUsize::new(0);
    let out: Mutex<Vec<Option<R>>> = Mutex::new((0..items.len()).map(|_| None).collect());
    std::thread::scope(|s| {
        for _ in 0..jobs.max(1).min(items.len().max(1)) {
            s.spawn(|| loop {
                let i = next.fetch_add(1, Ordering::SeqCst);
                if i >= items.len() {
                    break;
                }
                let r = f(&items[i]);
                out.lock().unwrap()[i] = Some(r);
            });
        }
    });
    out.into_inner().unwrap().into_iter().map(|r| r.unwrap()).collect()
}

/// Prove every item; the results keyed by id, in the items' order.
pub fn prove_all(
    m: &Manifest,
    tools: &Tools,
    netlist: &Path,
    work: &Path,
    jobs: usize,
    items: &[(&str, &Item)],
    tag: &str,
) -> Result<Obj, String> {
    let tdir = work.join("proofs").join(tag.replace(':', "_"));
    std::fs::create_dir_all(&tdir).map_err(|e| format!("{}: {e}", tdir.display()))?;
    let res = par_map(items, jobs, |(kind, it)| {
        let bound = it.bound.unwrap_or_else(|| m.default_bound());
        let to = it.timeout_s.unwrap_or_else(|| m.default_timeout_s());
        let mut r = prove_one(tools, netlist, &format!("vf_g_{}", it.id), bound, to, &tdir.join(format!("{}.json", it.id)));
        r.insert("kind".into(), json!(kind));
        let status = classify(it, kind, &mut r);
        r.insert("status".into(), json!(status));
        // A mutant run has no expectations, only kills.
        let shown = if tag == "base" { status.as_str() } else { "" };
        println!(
            "  [{tag}] {kind:8} {:40} {:12} {shown}  {:.1}s",
            it.id,
            verdict(&r),
            r["seconds"].as_f64().unwrap_or(0.0)
        );
        r
    });
    let mut out = Obj::new();
    for ((_, it), r) in items.iter().zip(res) {
        out.insert(it.id.clone(), Value::Object(r));
    }
    Ok(out)
}

// ---------------------------------------------------------------------------------------------
// mutants
// ---------------------------------------------------------------------------------------------

/// The bound text with one mutant applied inside its module.
pub fn apply_mutant(text: &str, mu: &Mutant) -> Result<String, String> {
    let defs: Vec<_> = module_def_re(&mu.module).find_iter(text).collect();
    if defs.len() != 1 {
        return Err(format!("module `{}` defined {} times", mu.module, defs.len()));
    }
    let body = defs[0].as_str();
    let re = Regex::new(&mu.find).map_err(|e| format!("find: {e}"))?;
    let n = re.find_iter(body).count();
    if n != mu.count {
        return Err(format!("pattern matched {n} times in {} (expected {})", mu.module, mu.count));
    }
    let nb = re.replace_all(body, |c: &regex::Captures| crate::pyrepl::expand(&mu.replace, c));
    Ok(format!("{}{}{}", &text[..defs[0].start()], nb, &text[defs[0].end()..]))
}

#[allow(clippy::too_many_arguments)]
pub fn run_mutant(
    m: &Manifest,
    tools: &Tools,
    work: &Path,
    mu: &Mutant,
    bound_text: &str,
    ids: &[String],
    base: &Obj,
    jobs: usize,
) -> Obj {
    let mut o = Obj::new();
    o.insert("id".into(), json!(mu.id));
    let err = |mut o: Obj, e: String| {
        o.insert("status".into(), json!("error"));
        o.insert("error".into(), json!(tail(&e, 1500)));
        o.insert("ok".into(), json!(false));
        o
    };
    let mdir = work.join("mutants").join(&mu.id);
    if let Err(e) = std::fs::create_dir_all(&mdir) {
        return err(o, e.to_string());
    }
    let mt = match apply_mutant(bound_text, mu) {
        Ok(t) => t,
        Err(e) => return err(o, e),
    };
    if let Err(e) = write(&mdir.join("rtl.bound.v"), &mt) {
        return err(o, e);
    }
    let nl = match synthesize(m, tools, &mdir, ids, "mut") {
        Ok(n) => n,
        Err(e) => return err(o, e),
    };
    let holds = |id: &str| matches!(base.get(id).and_then(|r| r["verdict"].as_str()), Some("holds" | "holds_within"));
    let targets: Vec<&str> = if mu.properties.is_empty() {
        m.properties.iter().map(|p| p.id.as_str()).filter(|i| holds(i)).collect()
    } else {
        mu.properties.iter().map(String::as_str).collect()
    };
    let items: Vec<(&str, &Item)> =
        m.properties.iter().filter(|p| targets.contains(&p.id.as_str())).map(|p| ("property", p)).collect();
    let res = match prove_all(m, tools, &nl, &mdir, jobs, &items, &format!("mut:{}", mu.id)) {
        Ok(r) => r,
        Err(e) => return err(o, e),
    };
    let v = |r: &Value| r["verdict"].as_str().unwrap_or("error").to_string();
    let mut killers: Vec<String> = res.iter().filter(|(_, r)| v(r) == "fails").map(|(i, _)| i.clone()).collect();
    killers.sort();
    let status = if !killers.is_empty() {
        "killed"
    } else if res.values().any(|r| matches!(v(r).as_str(), "timeout" | "error")) {
        "undecided"
    } else {
        "SURVIVED"
    };
    o.insert("text".into(), json!(mu.text));
    o.insert("status".into(), json!(status));
    o.insert("killed_by".into(), json!(killers));
    o.insert("expected".into(), json!(mu.expect));
    o.insert("ok".into(), json!((status == "killed") == (mu.expect == "killed")));
    let mut rs = Obj::new();
    for (i, r) in &res {
        rs.insert(i.clone(), json!({"verdict": r["verdict"], "seconds": r["seconds"]}));
    }
    o.insert("results".into(), Value::Object(rs));
    o
}

// ---------------------------------------------------------------------------------------------
// replay: a counterexample confirmed in simulation, a second witness independent of the prover
// ---------------------------------------------------------------------------------------------

/// The flattened RTL with the monitor nets exposed and every register initialised to 0, as the
/// prover assumes.
pub fn build_sim_model(m: &Manifest, tools: &Tools, work: &Path, ids: &[String]) -> Result<PathBuf, String> {
    let top = m.top();
    let sim = work.join("sim");
    std::fs::create_dir_all(&sim).map_err(|e| format!("{}: {e}", sim.display()))?;
    std::fs::copy(work.join("rtl.bound.v"), sim.join("rtl.bound.v")).map_err(|e| format!("rtl.bound.v: {e}"))?;
    let names = flat_names(&read(&work.join("base.pass1.log"))?, &top);
    let mut c = yosys_front(m);
    c.push(format!("cd {top}"));
    for i in ids {
        let Some(n) = names.get(i) else {
            return Err(format!("monitor net for `{i}` not in base.pass1.log"));
        };
        if *n != format!("vf_g_{i}") {
            c.push(format!("rename {n} vf_g_{i}"));
        }
    }
    let exposed: Vec<String> = ids.iter().map(|i| format!("w:vf_g_{i}")).collect();
    c.extend([
        "cd ..".to_string(),
        format!("expose {}", exposed.join(" ")),
        "opt_clean".into(),
        "setundef -zero -init".into(),
        "write_verilog -noattr sim.model.v".into(),
        "write_json sim.model.json".into(),
    ]);
    write(&sim.join("sim.ys"), &(c.join("\n") + "\n"))?;
    run_yosys(tools, &sim, "sim.ys", "sim.log", "sim model")?;
    Ok(sim)
}

fn esc(n: &str) -> String {
    if Regex::new(r"^[A-Za-z_]\w*$").unwrap().is_match(n) {
        n.to_string()
    } else {
        format!("\\{n} ")
    }
}

/// One compiled Verilator testbench around the sim model: it reads a counterexample's inputs from a
/// stimulus file (`+stim=FILE`, one line per cycle, one hex word per input port in `inputs` order)
/// and prints every monitor net per cycle, so each replay is a run, not a compile.
pub struct Replayer {
    pub bin: PathBuf,
    pub inputs: Vec<String>,
    pub widths: HashMap<String, usize>,
}

pub fn build_replayer(
    m: &Manifest,
    tools: &Tools,
    work: &Path,
    ids: &[String],
    show: &[String],
    name: &str,
) -> Result<Replayer, String> {
    let Some(verilator) = &tools.verilator else {
        return Err("verilator not found (install it, or pass --verilator)".into());
    };
    let sim = work.join("sim");
    let top = m.top();
    let model: Value = serde_json::from_str(&read(&sim.join("sim.model.json"))?).map_err(|e| e.to_string())?;
    let ports: Vec<(String, String, usize)> = model["modules"][&top]["ports"]
        .as_object()
        .ok_or("sim.model.json: no ports for the top")?
        .iter()
        .map(|(n, p)| {
            (n.clone(), p["direction"].as_str().unwrap_or("").to_string(), p["bits"].as_array().map_or(0, Vec::len))
        })
        .collect();
    let clk = m.clock();
    let inputs: Vec<String> =
        ports.iter().filter(|(n, d, _)| d == "input" && Some(n) != clk.as_ref()).map(|(n, _, _)| n.clone()).collect();
    let mut cols: Vec<String> = ids.iter().map(|i| format!("vf_g_{i}")).collect();
    cols.extend(show.iter().cloned());
    let mut l = vec!["`timescale 1ns/1ps".to_string(), format!("module {name};")];
    for (n, d, w) in &ports {
        l.push(format!("  {} [{}:0] {};", if d == "input" { "reg" } else { "wire" }, w - 1, esc(n)));
    }
    let conns: Vec<String> = ports.iter().map(|(n, _, _)| format!(".{}({})", esc(n), esc(n))).collect();
    l.push(format!("  {top} dut({});", conns.join(", ")));
    l.extend(
        [
            "  integer fd, rc, k;",
            "  reg [8*4096-1:0] fn;",
            "  initial begin",
            "    if (!$value$plusargs(\"stim=%s\", fn)) $fatal(1, \"no +stim=FILE\");",
            "    fd = $fopen(fn, \"r\");",
            "    if (fd == 0) $fatal(1, \"cannot open the stimulus file\");",
            "    k = 0;",
        ]
        .map(String::from),
    );
    l.extend(inputs.iter().map(|n| format!("    {} = 0;", esc(n))));
    l.push("    while (!$feof(fd)) begin".into());
    if !inputs.is_empty() {
        let fmt = vec!["%h"; inputs.len()].join(" ");
        let args: Vec<String> = inputs.iter().map(|n| esc(n)).collect();
        l.push(format!("      rc = $fscanf(fd, \"{fmt}\\n\", {});", args.join(", ")));
        l.push(format!("      if (rc != {}) break;", inputs.len()));
    }
    if let Some(c) = &clk {
        l.push(format!("      {} = 1'b0;", esc(c)));
    }
    l.push("      #5;".into());
    let shown: Vec<String> = cols.iter().map(|c| format!("{c}=%0d")).collect();
    let vals: Vec<String> =
        cols.iter().map(|c| if c.starts_with("vf_g_") { c.clone() } else { format!("dut.{}", esc(c)) }).collect();
    l.push(format!("      $display(\"cycle %0d: {}\", k, {});", shown.join(" "), vals.join(", ")));
    if let Some(c) = &clk {
        l.push(format!("      {} = 1'b1; #5;", esc(c)));
    }
    l.extend(["      k = k + 1;", "    end", "    $finish;", "  end", "endmodule"].map(String::from));
    let tb = sim.join(format!("{name}.v"));
    write(&tb, &(l.join("\n") + "\n"))?;
    let obj = sim.join(format!("obj_{name}"));
    // Every register starts at 0, as the prover assumes: the model carries its initial values, and
    // --x-initial/--x-assign 0 keep anything else from being randomised.
    let cmd = sh(&[
        verilator,
        "--binary",
        "--timing",
        "-Wno-fatal",
        "-Wno-lint",
        "-Wno-style",
        "--x-initial",
        "0",
        "--x-assign",
        "0",
        "--top-module",
        name,
        "-Mdir",
        &obj.to_string_lossy(),
        "-o",
        name,
        &tb.to_string_lossy(),
        &sim.join("sim.model.v").to_string_lossy(),
    ]);
    let r = run(&cmd, None, Some(&sim)).map_err(|e| format!("cannot run {verilator}: {e}"))?;
    if !r.ok() {
        return Err(format!("verilator failed: {}", tail(if r.err.is_empty() { &r.out } else { &r.err }, 1500)));
    }
    Ok(Replayer {
        bin: obj.join(name),
        inputs,
        widths: ports.into_iter().map(|(n, _, w)| (n, w)).collect(),
    })
}

/// The value of input `n` (`w` bits) in one cycle of a counterexample.
fn input_value(ins: &Obj, n: &str, w: usize) -> Bits {
    let mut v = Bits::default();
    for b in 0..w {
        let key = if w == 1 { n.to_string() } else { format!("{n}[{b}]") };
        if ins.get(&key).is_some_and(truthy) {
            v.set(b);
        }
    }
    v
}

pub fn truthy(v: &Value) -> bool {
    match v {
        Value::Bool(b) => *b,
        Value::Number(n) => n.as_f64().is_some_and(|x| x != 0.0),
        Value::String(s) => !s.is_empty(),
        Value::Null => false,
        _ => true,
    }
}

/// Drive the counterexample's inputs cycle by cycle: the claim's net must be 1 at the failing cycle.
pub fn replay(rep: &Replayer, work: &Path, pid: &str, trace: &Value) -> Obj {
    let sim = work.join("sim");
    let empty = Map::new();
    let lines: Vec<String> = trace["inputs_per_cycle"]
        .as_array()
        .map(|c| c.as_slice())
        .unwrap_or(&[])
        .iter()
        .map(|ins| {
            let ins = ins.as_object().unwrap_or(&empty);
            let words: Vec<String> = rep.inputs.iter().map(|n| input_value(ins, n, rep.widths[n]).hex()).collect();
            words.join(" ")
        })
        .collect();
    let mut o = Obj::new();
    let stim = sim.join(format!("replay_{pid}.stim"));
    if let Err(e) = write(&stim, &(lines.join("\n") + "\n")) {
        o.insert("confirmed".into(), Value::Null);
        o.insert("error".into(), json!(e));
        return o;
    }
    let log = sim.join(format!("replay_{pid}.log"));
    let r = match run(&[rep.bin.to_string_lossy().into_owned(), format!("+stim={}", stim.display())], None, Some(&sim)) {
        Ok(r) => r,
        Err(e) => {
            o.insert("confirmed".into(), Value::Null);
            o.insert("error".into(), json!(e.to_string()));
            return o;
        }
    };
    let _ = std::fs::write(&log, &r.out);
    if !r.ok() {
        o.insert("confirmed".into(), Value::Null);
        o.insert("error".into(), json!(tail(if r.err.is_empty() { &r.out } else { &r.err }, 1500)));
        return o;
    }
    let fail_at = trace["cycle"].as_i64().unwrap_or(-1);
    let hit = Regex::new(&format!(r"(?m)^cycle {fail_at}: .*?\bvf_g_{pid}=(\d+)")).unwrap();
    let confirmed = hit.captures(&r.out).is_some_and(|c| &c[1] == "1");
    let line = Regex::new(r"(?m)^cycle (\d+): (.*)$").unwrap();
    let mine = Regex::new(&format!(r"\bvf_g_{pid}=1\b")).unwrap();
    let first = line.captures_iter(&r.out).find(|c| mine.is_match(&c[2])).and_then(|c| c[1].parse::<i64>().ok());
    o.insert("confirmed".into(), json!(confirmed));
    o.insert("first_hit".into(), first.map_or(Value::Null, |f| json!(f)));
    o.insert("simulator".into(), json!("verilator"));
    o.insert("log".into(), json!(log.to_string_lossy()));
    o
}

/// The programs, from the command line, the environment, the manifest, then the defaults.
pub fn resolve_tools(
    m: &Manifest,
    lec: Option<String>,
    yosys: Option<String>,
    liberty: Option<String>,
    verilator: Option<String>,
    sv2v: Option<String>,
) -> Result<Tools, String> {
    let env = |a: &str, b: &str| std::env::var(a).ok().or_else(|| std::env::var(b).ok()).filter(|s| !s.is_empty());
    // An installed engine's sibling first: a suite install links `vyges-lec` beside this binary.
    let beside = std::env::current_exe()
        .ok()
        .and_then(|e| e.parent().map(|d| d.join("vyges-lec")))
        .filter(|p| p.exists())
        .map(|p| p.to_string_lossy().into_owned());
    let lec = lec
        .or_else(|| env("VYGES_FORMAL_LEC", "VFORMAL_LEC"))
        .or_else(|| m.tool("lec"))
        .or(beside)
        .or_else(|| exec::which("vyges-lec"));
    let yosys = yosys.or_else(|| env("VYGES_FORMAL_YOSYS", "VFORMAL_YOSYS")).or_else(|| m.tool("yosys")).or_else(|| exec::which("yosys"));
    let lib = liberty.or_else(|| env("VYGES_FORMAL_LIBERTY", "VFORMAL_LIBERTY")).or_else(|| m.synth_str("liberty"));
    let verilator = verilator
        .or_else(|| env("VYGES_FORMAL_VERILATOR", "VFORMAL_VERILATOR"))
        .or_else(|| m.tool("verilator"))
        .or_else(|| exec::which("verilator"));
    let sv2v = sv2v.or_else(|| env("VYGES_FORMAL_SV2V", "VFORMAL_SV2V")).or_else(|| m.tool("sv2v")).or_else(|| exec::which("sv2v"));
    let (Some(lec), Some(yosys), Some(lib)) = (lec.clone(), yosys.clone(), lib.clone()) else {
        return Err(format!(
            "need vyges-lec ({}), yosys ({}) and a Liberty ({}) — install the physical engines \
             (`vyges install physical`), put yosys on PATH, and name the Liberty with --liberty or [synth] liberty",
            lec.as_deref().unwrap_or("not found"),
            yosys.as_deref().unwrap_or("not found"),
            lib.as_deref().unwrap_or("not set")
        ));
    };
    let liberty = m.p(&lib);
    if !liberty.is_file() {
        return Err(format!("Liberty not found: {}", liberty.display()));
    }
    let lec = if lec.contains('/') { m.p(&lec).to_string_lossy().into_owned() } else { lec };
    Ok(Tools { lec, yosys, liberty, verilator, sv2v })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn closure_follows_instances_from_the_top_only() {
        let text = "module a(input x);\n  b u_b(.x(x));\nendmodule\nmodule b(input x);\n  c #(.W(1)) u_c(.x(x));\nendmodule\n\
                    module c(input x);\nendmodule\nmodule unused(input x);\nendmodule\n";
        let (body, mods) = extract_closure(text, "a").unwrap();
        assert_eq!(mods, ["a", "b", "c"]);
        assert!(!body.contains("unused"));
        assert!(extract_closure(text, "nope").is_err());
    }

    #[test]
    fn monitor_ids_are_the_assigned_names() {
        let src = "wire vf_p_one = a & b;\nassign vf_c_two = c;\nwire vf_a_three = 1'b1;\nwire x = vf_p_one;";
        assert_eq!(monitor_ids(src, "p"), ["one"]);
        assert_eq!(monitor_ids(src, "c"), ["two"]);
        assert_eq!(monitor_ids(src, "a"), ["three"]);
    }

    fn it(expect: Option<&str>, finding: bool) -> Item {
        Item {
            id: "x".into(),
            text: String::new(),
            claim: String::new(),
            expect: expect.map(String::from),
            finding: finding.then(|| "a defect".into()),
            assumptions: vec![],
            bound: None,
            timeout_s: None,
        }
    }

    fn r(v: &str) -> Obj {
        let mut o = Obj::new();
        o.insert("verdict".into(), json!(v));
        o
    }

    /// A recorded defect reads FINDING, never a pass; a property that changes reads UNEXPECTED.
    #[test]
    fn classify_findings_and_surprises() {
        assert_eq!(classify(&it(None, false), "property", &mut r("holds")), "as-expected");
        assert_eq!(classify(&it(None, false), "property", &mut r("fails")), "UNEXPECTED");
        assert_eq!(classify(&it(Some("fails"), true), "property", &mut r("fails")), "FINDING");
        assert_eq!(classify(&it(Some("fails"), true), "property", &mut r("holds")), "UNEXPECTED");
        assert_eq!(classify(&it(Some("undecided"), false), "property", &mut r("timeout")), "as-expected");
        let mut c = r("holds");
        assert_eq!(classify(&it(Some("unreachable"), true), "cover", &mut c), "FINDING");
        assert_eq!(c["cover"], "unreachable");
        assert_eq!(classify(&it(None, false), "cover", &mut r("fails")), "as-expected");
        assert_eq!(classify(&it(None, false), "cover", &mut r("holds_within")), "UNEXPECTED");
    }

    #[test]
    fn par_map_keeps_order() {
        let v: Vec<u32> = (0..50).collect();
        assert_eq!(par_map(&v, 4, |x| x * 2), v.iter().map(|x| x * 2).collect::<Vec<_>>());
    }

    #[test]
    fn utc_is_iso_8601() {
        assert!(Regex::new(r"^\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ$").unwrap().is_match(&now_utc()));
    }
}
