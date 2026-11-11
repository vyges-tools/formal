//! `report.md` and `report.json`: every result, the commit it belongs to, and how it was produced.

use std::path::Path;

use regex::Regex;
use serde_json::{json, Map, Value};

use crate::bits::Bits;
use crate::flow::{truthy, Obj};
use crate::manifest::{Decode, Manifest};
use crate::record;

const LIMITS: &str = "\
- Results hold only for the RTL commit, parameters, defines and monitors listed under *Scope*, as
  elaborated and synthesized by the tool versions listed there.
- Every proof starts from the **all-zero register state** and counts only after reset has been
  asserted and released (`vf_armed`). Registers listed under *Lint: registers without reset* power up
  unknown in silicon; the model starts them at 0, which is an assumption, not a proof.
- Inputs are unconstrained except by the listed assumptions. In particular, memory read data is free
  unless a memory model is listed — control and address properties must hold for ANY data; arithmetic
  claims need a memory model.
- A *bounded* result (`holds_within N`) says nothing past cycle N.
- A *liveness* claim (\"eventually completes\") is checked as a bounded response: it holds only under
  the stated assumptions and within the stated bound.
- Formal results do not establish timing closure, and do not prove that the written specification is
  the intended one.
";

fn st<'a>(o: &'a Value, k: &str) -> &'a str {
    o.get(k).and_then(Value::as_str).unwrap_or("")
}

/// Seconds as the report shows them: one decimal.
fn secs(v: &Value) -> String {
    format!("{:.1}", v.as_f64().unwrap_or(0.0))
}

/// `name=value`, or the named fields of a packed signal when the manifest describes it.
fn show_input(name: &str, v: &Bits, decodes: &[Decode]) -> String {
    let Some(d) = decodes.iter().find(|d| d.signal == name) else {
        return if v.gt1() { format!("{name}=0x{}", v.hex()) } else { format!("{name}={}", v.hex()) };
    };
    let fields: Vec<String> =
        d.fields.iter().map(|f| format!("{}=0x{}", f.name, v.slice(f.lsb, f.width).hex())).collect();
    format!("{name}({})", fields.join(" "))
}

pub fn trace_excerpt(trace: &Value, max_lines: usize) -> Vec<String> {
    decoded_excerpt(trace, max_lines, &[])
}

/// Per cycle, the bus-grouped inputs that changed since the previous cycle (cycle 0: the non-zero ones).
pub fn decoded_excerpt(trace: &Value, max_lines: usize, decodes: &[Decode]) -> Vec<String> {
    let bit = Regex::new(r"^(.*)\[(\d+)\]$").unwrap();
    let mut out = vec![];
    let mut prev: Vec<(String, Bits)> = vec![];
    let cycles = trace["inputs_per_cycle"].as_array().map(|a| a.as_slice()).unwrap_or(&[]);
    for (cyc, ins) in cycles.iter().enumerate() {
        let mut groups: Vec<(String, Bits)> = vec![];
        let empty = Map::new();
        for (k, v) in ins.as_object().unwrap_or(&empty) {
            let (base, idx) = match bit.captures(k) {
                Some(c) => (c[1].to_string(), c[2].parse::<usize>().unwrap_or(0)),
                None => (k.clone(), 0),
            };
            let pos = match groups.iter().position(|(n, _)| *n == base) {
                Some(p) => p,
                None => {
                    groups.push((base, Bits::default()));
                    groups.len() - 1
                }
            };
            if truthy(v) {
                groups[pos].1.set(idx);
            }
        }
        let mut ch: Vec<&(String, Bits)> = groups
            .iter()
            .filter(|(k, v)| {
                if cyc == 0 {
                    !v.is_zero()
                } else {
                    prev.iter().find(|(n, _)| n == k).map(|(_, p)| p) != Some(v)
                }
            })
            .collect();
        ch.sort_by(|a, b| a.0.cmp(&b.0));
        if ch.is_empty() {
            out.push(format!("cycle {cyc}: (no input change)"));
        } else {
            let parts: Vec<String> = ch.iter().map(|(k, v)| show_input(k, v, decodes)).collect();
            out.push(format!("cycle {cyc}: {}", parts.join(" ")));
        }
        prev = groups;
    }
    if out.len() > max_lines {
        let n = out.len();
        let mut cut = out[..max_lines / 2].to_vec();
        cut.push(format!("... {} cycles elided ...", n - max_lines));
        cut.extend_from_slice(&out[n - max_lines / 2..]);
        out = cut;
    }
    out
}

/// The commit under test — every result in a report belongs to exactly this hash.
pub fn rtl_line(prov: &Obj) -> String {
    let p = Value::Object(prov.clone());
    let Some(h) = prov.get("rtl_commit").and_then(Value::as_str) else {
        return "RTL under test: files listed under *Scope* (not in a git repository)".into();
    };
    let r = match prov.get("rtl_commit_url").and_then(Value::as_str) {
        Some(u) => format!("[`{h}`]({u})"),
        None => format!("`{h}`"),
    };
    let dirty = if prov.get("rtl_dirty").and_then(Value::as_bool).unwrap_or(false) {
        " — ⚠️ **working tree DIRTY: results do not belong to this commit**"
    } else {
        ""
    };
    format!(
        "**RTL under test:** {} @ {r} ({}, “{}”){dirty}",
        st(&p, "rtl_remote"),
        st(&p, "rtl_commit_date"),
        st(&p, "rtl_commit_subject")
    )
}

/// The ids that did not come out as expected: claims in the manifest's order, then mutants.
pub fn unexpected(m: &Manifest, base: &Obj, muts: &[Value]) -> Vec<String> {
    let mut u: Vec<String> = m
        .properties
        .iter()
        .chain(&m.covers)
        .filter(|it| base.get(&it.id).is_some_and(|r| st(r, "status") == "UNEXPECTED"))
        .map(|it| it.id.clone())
        .collect();
    u.extend(muts.iter().filter(|x| !x.get("ok").and_then(Value::as_bool).unwrap_or(false)).map(|x| st(x, "id").to_string()));
    u
}

/// The CLI command lines, with the manifest as the reader would name it.
fn manifest_name(m: &Manifest) -> String {
    m.path.file_name().map(|f| f.to_string_lossy().into_owned()).unwrap_or_else(|| "manifest.toml".into())
}

fn header(m: &Manifest, out_name: &str) -> Vec<String> {
    vec![
        format!(
            "> Generated by **`vyges formal run {} --out {out_name}`** with vyges-formal {} — the formal engine \
             of the [Vyges CLI](https://vyges.com), installed with the physical engines. Monitors are bound into \
             the RTL, every claim is proved or refuted by `vyges-lec`, and every counterexample is replayed in \
             Verilator. How to run it yourself is at the end of this report.",
            manifest_name(m),
            crate::VERSION
        ),
        String::new(),
    ]
}

fn trailer(m: &Manifest, out_name: &str) -> Vec<String> {
    let mf = manifest_name(m);
    [
        "## Run it yourself with the Vyges CLI",
        "",
        "Install the CLI, then the physical engines — `vyges-formal` and the `vyges-lec` prover ship there:",
        "",
        "```sh",
        "curl --proto '=https' --tlsv1.2 -LsSf https://github.com/vyges-tools/cli/releases/latest/download/vyges-installer.sh | sh",
        "# or: brew install vyges/tap/vyges",
        "vyges install physical",
        "```",
        "",
        "A campaign also needs [Yosys](https://github.com/YosysHQ/yosys) and \
         [Verilator](https://github.com/verilator/verilator) on `PATH`, and the Liberty the manifest names \
         (`--liberty FILE` overrides it).",
        "",
        "```sh",
    ]
    .iter()
    .map(|s| s.to_string())
    .chain([
        format!("vyges formal run {mf} --out {out_name}          # prove, replay, mutate, report"),
        format!("vyges formal replay {mf} <id> --out {out_name} --show <signal,...>   # one counterexample, cycle by cycle"),
        format!("vyges formal report {mf} --out {out_name}       # re-render after editing expectations"),
        "```".into(),
        String::new(),
        "The manifest names the RTL (a git repository and its files), the monitors and the module each binds \
         into, and every assumption, property, cover and mutant. `vyges formal --help` lists every option. \
         Exit status: 0 when every result is as expected, 2 when anything is not, 1 on a tool error."
            .into(),
        String::new(),
    ])
    .collect()
}

fn strs_of(v: &Value) -> Vec<String> {
    v.as_array().map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect()).unwrap_or_default()
}

fn code_list(v: &Value) -> String {
    let a = strs_of(v);
    if a.is_empty() {
        "none".into()
    } else {
        a.iter().map(|s| format!("`{s}`")).collect::<Vec<_>>().join(", ")
    }
}

fn opt<'a>(v: &'a Value, k: &str) -> &'a str {
    match st(v, k) {
        "" => "not stated",
        s => s,
    }
}

fn summary(m: &Manifest, prov: &Obj, rec: &Value, unexpected: &[String]) -> Vec<String> {
    let c = &rec["counts"];
    let row = |group: &str, keys: &[&str]| -> String {
        keys.iter().map(|k| format!("{k} {}", c[group][*k])).collect::<Vec<_>>().join(" · ")
    };
    let mut l = vec![
        "## 1. Verification summary".to_string(),
        String::new(),
        format!("_{}_", m.ip_str("description").unwrap_or_default()),
        String::new(),
        rtl_line(prov),
        String::new(),
        format!("**Verdict: {}** (run {})", st(rec, "verdict"), st(&rec["provenance"], "run_utc")),
        String::new(),
        "Every claim below holds only under the assumptions listed for it in section 4.".into(),
        String::new(),
        "| | |".into(),
        "|---|---|".into(),
        format!("| properties | {} |", row("properties", &["PROVEN", "BOUNDED", "FAILED", "UNDECIDED", "VACUOUS", "WAIVED"])),
        format!("| covers | {} |", row("covers", &["REACHED", "UNREACHABLE", "UNDECIDED", "WAIVED"])),
        format!("| counterexamples replayed | {} of {} |", c["counterexamples"]["replayed"], c["counterexamples"]["total"]),
        format!("| mutants detected | {} of {} |", c["mutants"]["detected"], c["mutants"]["total"]),
        String::new(),
    ];
    if !unexpected.is_empty() {
        l.extend([format!("Not as the campaign expected: {}.", unexpected.join(", ")), String::new()]);
    }
    l
}

fn scope(m: &Manifest) -> Vec<String> {
    let mut l: Vec<String> = ["## 2. Scope", "", "| item | value |", "|---|---|"].map(String::from).to_vec();
    l.push(format!("| top | `{}` |", m.top()));
    for (k, val) in m.params() {
        l.push(format!("| param `{k}` | {val} |"));
    }
    l.push(String::new());
    if let Some(n) = m.ip_str("scope_notes") {
        l.extend([n.trim().to_string(), String::new()]);
    }
    l
}

fn plan(m: &Manifest, rec: &Value) -> Vec<String> {
    let mut l = vec!["## 3. Verification plan".to_string(), String::new()];
    let reqs = rec["requirements"].as_array().map(Vec::as_slice).unwrap_or(&[]);
    if reqs.is_empty() {
        l.extend(["No requirements are declared. Claims are grouped by the manifest's `claim` field.".to_string(), String::new()]);
        let mut claims: Vec<&str> = m.properties.iter().map(|p| p.claim.as_str()).collect();
        claims.dedup();
        l.extend([format!("Claim groups: {}.", claims.join(", ")), String::new()]);
        return l;
    }
    l.extend(["| requirement | statement | source | properties | covers |".to_string(), "|---|---|---|---|---|".into()]);
    for q in reqs {
        l.push(format!(
            "| `{}` | {} | {} | {} | {} |",
            st(q, "id"),
            st(q, "text"),
            opt(q, "source"),
            code_list(&q["properties"]),
            code_list(&q["covers"])
        ));
    }
    l.extend([
        String::new(),
        format!("Requirements with no property: {}.", code_list(&rec["requirements_without_property"])),
        String::new(),
        format!("Properties with no requirement: {}.", code_list(&rec["properties_without_requirement"])),
        String::new(),
    ]);
    l
}

fn environment(rec: &Value, lintr: &Obj) -> Vec<String> {
    let e = &rec["environment"];
    let mut l: Vec<String> = ["## 4. Formal environment", "", "### Clocks and resets", "", "| module | clock | reset |", "|---|---|---|"]
        .map(String::from)
        .to_vec();
    for b in e["clocks"].as_array().into_iter().flatten() {
        let low = b["reset_active_low"].as_bool().unwrap_or(true);
        l.push(format!("| `{}` | `{}` | `{}` ({}) |", st(b, "module"), st(b, "clock"), st(b, "reset"), if low { "active low" } else { "active high" }));
    }
    l.extend(
        ["", "### Assumptions", "", "| id | assumption | class | rationale | source |", "|---|---|---|---|---|"].map(String::from),
    );
    for a in e["assumptions"].as_array().into_iter().flatten() {
        l.push(format!("| `{}` | {} | {} | {} | {} |", st(a, "id"), st(a, "text"), opt(a, "class"), opt(a, "rationale"), opt(a, "source")));
    }
    l.extend(["", "### Abstractions", "", "| kind | items |", "|---|---|"].map(String::from));
    for (k, label) in [
        ("black_boxes", "black boxes"),
        ("cut_points", "cut points"),
        ("memory_models", "memory models"),
        ("reduced_parameters", "reduced parameters"),
        ("disabled_logic", "disabled logic"),
        ("registers_without_reset", "registers without reset"),
    ] {
        l.push(format!("| {label} | {} |", code_list(&e[k])));
    }
    let check = match e["setup"]["yosys_check_problems"].as_u64() {
        Some(n) => format!("{n} problems"),
        None => "not run".to_string(),
    };
    l.extend([
        String::new(),
        "### Setup analysis".into(),
        String::new(),
        format!("- Yosys `check` (loops, multiple drivers): {check}"),
        format!("- Assumption sets with no reached cover: {}", code_list(&e["setup"]["unconfirmed_assumption_sets"])),
        format!(
            "- Registers: {} with async reset, {} with sync reset, {} in monitors",
            lintr.get("async_reset").cloned().unwrap_or(json!(0)),
            lintr.get("sync_reset").and_then(Value::as_array).map_or(0, Vec::len),
            lintr.get("monitor").cloned().unwrap_or(json!(0))
        ),
        String::new(),
    ]);
    l
}

fn property_table(m: &Manifest, rec: &Value) -> Vec<String> {
    let mut l: Vec<String> = [
        "## 5. Property results",
        "",
        "| id | requirements | statement | result | depth and engine | assumptions | activation | against expectation | time | evidence |",
        "|---|---|---|---|---|---|---|---|---|---|",
    ]
    .map(String::from)
    .to_vec();
    for it in &m.properties {
        let Some(r) = rec["results"].get(&it.id) else { continue };
        let depth = match r.get("bound").and_then(Value::as_i64) {
            Some(b) if b != 0 => format!("to cycle {b}, {}", st(r, "engine")),
            _ => format!("unbounded, {}", st(r, "engine")),
        };
        let result = match r.get("cause").and_then(Value::as_str) {
            Some(c) => format!("{} ({c})", st(r, "result")),
            None => st(r, "result").to_string(),
        };
        l.push(format!(
            "| `{}` | {} | {} | {result} | {depth} | {} | {} | {} | {}s | `{}` |",
            it.id,
            code_list(&r["requirements"]),
            it.text,
            code_list(&r["assumptions"]),
            st(r, "activation"),
            st(r, "status"),
            secs(&r["seconds"]),
            st(r, "evidence")
        ));
    }
    l.push(String::new());
    l
}

fn cover_table(m: &Manifest, rec: &Value) -> Vec<String> {
    let mut l: Vec<String> = [
        "## 6. Coverage and reachability",
        "",
        "A reached cover shows the assumptions still allow that behaviour. An unreachable cover means either the \
         assumptions are too strong or the logic is dead.",
        "",
    ]
    .map(String::from)
    .to_vec();
    let groups: [(&str, fn(&&crate::manifest::Item) -> bool); 2] =
        [("Claimed covers", |c| !c.id.starts_with("gen_")), ("Generated state covers", |c| c.id.starts_with("gen_"))];
    for (title, keep) in groups {
        let chosen: Vec<_> = m.covers.iter().filter(keep).collect();
        if chosen.is_empty() {
            continue;
        }
        l.extend([format!("### {title}"), String::new(), "| id | statement | result | against expectation | at cycle |".into(), "|---|---|---|---|---|".into()]);
        for it in chosen {
            let Some(r) = rec["results"].get(&it.id) else { continue };
            let cyc = r.get("trace").and_then(|t| t.get("cycle")).map(|c| c.to_string()).unwrap_or_default();
            let result = match r.get("cause").and_then(Value::as_str) {
                Some(c) => format!("{} ({c})", st(r, "result")),
                None => st(r, "result").to_string(),
            };
            l.push(format!("| `{}` | {} | {result} | {} | {cyc} |", it.id, it.text, st(r, "status")));
            if title.starts_with("Generated") && st(r, "result") == "UNREACHABLE" {
                l.push(format!("| | possible dead logic: `{}` | | | |", it.id));
            }
        }
        l.push(String::new());
    }
    l
}

fn finding_blocks(m: &Manifest, base: &Obj, rec: &Value) -> Vec<String> {
    let mut l = vec!["## 7. Findings".to_string(), String::new()];
    let all = rec["findings"].as_array().map(Vec::as_slice).unwrap_or(&[]);
    if all.is_empty() {
        l.extend(["No findings are recorded for this campaign.".to_string(), String::new()]);
    }
    for f in all {
        l.extend([format!("### {} — {}", st(f, "id"), st(f, "title")), String::new(), "| | |".into(), "|---|---|".into()]);
        l.push(format!("| properties | {} |", code_list(&f["properties"])));
        l.push(format!("| state at this commit | {} |", st(f, "state")));
        for (k, label) in [
            ("severity", "severity"),
            ("found_at", "found at"),
            ("expected", "expected"),
            ("root_cause", "root cause"),
            ("disposition", "disposition"),
            ("fix", "fix"),
            ("regression", "regression"),
            ("tracker", "tracker"),
        ] {
            if !st(f, k).is_empty() {
                l.push(format!("| {label} | {} |", st(f, k)));
            }
        }
        l.push(String::new());
    }
    for it in &m.properties {
        let Some(r) = base.get(&it.id) else { continue };
        if st(r, "verdict") != "fails" {
            continue;
        }
        l.extend([format!("### Counterexample — `{}`", it.id), String::new()]);
        if let Some(f) = &it.finding {
            l.extend([f.trim().to_string(), String::new()]);
        }
        if let Some(rp) = r.get("replay").and_then(Value::as_object) {
            let ok = rp.get("confirmed").and_then(Value::as_bool).unwrap_or(false);
            let sim = rp.get("simulator").and_then(Value::as_str).unwrap_or("Verilator");
            let sim = if sim == "verilator" { "Verilator" } else { sim };
            l.extend([
                format!(
                    "Replayed in simulation ({sim}, registers zero-initialised): {}.",
                    if ok { "**confirmed**" } else { "**NOT confirmed** — treat the result as suspect" }
                ),
                String::new(),
            ]);
        }
        let cyc = r["trace"].get("cycle").map(|c| c.to_string()).unwrap_or_else(|| "None".into());
        l.extend([
            format!("`{}` is 1 in cycle {cyc}. Inputs (changes only; full trace in `proofs/base/{}.json`):", st(r, "net"), it.id),
            String::new(),
            "```".into(),
        ]);
        l.extend(decoded_excerpt(&r["trace"], 40, &m.decodes));
        l.extend(["```".to_string(), String::new()]);
    }
    for it in &m.covers {
        if let (Some(f), Some(r)) = (&it.finding, base.get(&it.id)) {
            if st(r, "cover") != "reached" {
                l.extend([format!("**`{}`:** {}", it.id, f.trim()), String::new()]);
            }
        }
    }
    l
}

fn mutation(rec: &Value) -> Vec<String> {
    let mut l: Vec<String> = [
        "## 8. Mutation analysis",
        "",
        "Mutation testing measures the ability of the selected property set to detect the selected injected \
         defects. It does not establish that all possible defects would be detected.",
        "",
        "| mutant | defect injected | run against | detected by | result |",
        "|---|---|---|---|---|",
    ]
    .map(String::from)
    .to_vec();
    for x in rec["mutants"].as_array().into_iter().flatten() {
        let by = if x["killed_by"].as_array().is_some_and(|a| !a.is_empty()) { code_list(&x["killed_by"]) } else { st(x, "error").to_string() };
        let against = if x["run_against"].is_string() { "all properties".to_string() } else { code_list(&x["run_against"]) };
        let ok = x.get("ok").and_then(Value::as_bool).unwrap_or(false);
        let status = if st(x, "status") == "killed" { "Detected" } else { st(x, "status") };
        l.push(format!("| `{}` | {} | {against} | {by} | {status}{} |", st(x, "id"), st(x, "text"), if ok { "" } else { " (UNEXPECTED)" }));
    }
    l.extend([
        String::new(),
        format!("Surviving mutants: {}.", code_list(&rec["mutation"]["survivors"])),
        String::new(),
        format!("Proved properties that detected no mutant: {}.", code_list(&rec["mutation"]["idle_properties"])),
        String::new(),
    ]);
    l
}

fn limits(rec: &Value) -> Vec<String> {
    let mut l = vec!["## 9. Limitations and residual risk".to_string(), String::new()];
    let found = strs_of(&rec["limitations"]);
    if found.is_empty() {
        l.extend(["No campaign-specific limitations were generated.".to_string(), String::new()]);
    } else {
        l.extend(found.iter().map(|x| format!("- {x}")));
        l.push(String::new());
    }
    l.extend(["Standing limits:".to_string(), String::new(), LIMITS.to_string()]);
    l
}

fn appendix(m: &Manifest, prov: &Obj, out_name: &str, stats_log: &Path) -> Vec<String> {
    let p = Value::Object(prov.clone());
    let mut l: Vec<String> = ["## 10. Reproducibility appendix", "", "| item | value |", "|---|---|"].map(String::from).to_vec();
    for k in ["rtl_remote", "rtl_commit", "rtl_commit_date", "rtl_dirty", "run_utc", "platform"] {
        if let Some(x) = prov.get(k) {
            let s = x.as_str().map(str::to_string).unwrap_or_else(|| x.to_string());
            l.push(format!("| {k} | `{s}` |"));
        }
    }
    if let Some(h) = prov.get("manifest_sha256").and_then(Value::as_str) {
        l.push(format!("| manifest | sha256 `{h}` |"));
    }
    let hash = |h: &Value| h.as_str().unwrap_or("").to_string();
    for (f, h) in p["rtl_files"].as_object().into_iter().flatten() {
        l.push(format!("| rtl `{f}` | sha256 `{}` |", hash(h)));
    }
    for (f, h) in p["monitors"].as_object().into_iter().flatten() {
        l.push(format!("| monitor `{f}` | sha256 `{}` |", hash(h)));
    }
    let lib_name = Path::new(st(&p, "liberty")).file_name().map(|f| f.to_string_lossy().into_owned()).unwrap_or_default();
    l.push(format!("| liberty | `{lib_name}` sha256 `{}` |", hash(&p["liberty_sha256"])));
    l.extend(tool_rows(&p));
    l.push(format!("| default timeout | {:.0} s |", m.default_timeout_s()));
    let own: Vec<String> =
        m.properties.iter().chain(&m.covers).filter_map(|i| i.timeout_s.map(|t| format!("`{}` {t:.0} s", i.id))).collect();
    if !own.is_empty() {
        l.push(format!("| per-item timeouts | {} |", own.join(", ")));
    }
    l.push(String::new());
    if let Ok(log) = std::fs::read_to_string(stats_log) {
        if let Some(c) = Regex::new(r"Chip area for (?:top )?module.*?:\s*([\d.]+)").unwrap().captures(&log) {
            l.extend([
                format!("Synthesized for the proof (monitor included): chip area {} µm² — a proof model, not a signoff netlist.", &c[1]),
                String::new(),
            ]);
        }
    }
    l.extend(trailer(m, out_name));
    l
}

/// The count from Yosys's `check`, read from the log beside the synthesis statistics.
fn yosys_problems(stats_log: &Path) -> Option<usize> {
    let re = Regex::new(r"Found and reported (\d+) problems").unwrap();
    let logs = [stats_log.to_path_buf(), stats_log.with_file_name("base.pass1.log")];
    logs.iter().find_map(|f| {
        let text = std::fs::read_to_string(f).ok()?;
        re.captures(&text)?[1].parse().ok()
    })
}

pub fn report(
    m: &Manifest,
    out: &Path,
    prov: &Obj,
    lintr: &Obj,
    base: &Obj,
    muts: &[Value],
    stats_log: &Path,
) -> Result<Vec<String>, String> {
    let out_name = out.file_name().map(|f| f.to_string_lossy().into_owned()).unwrap_or_else(|| "out".into());
    let unexpected = unexpected(m, base, muts);
    let mut j = record::build(m, prov, lintr, base, muts, &unexpected, yosys_problems(stats_log));
    let mut l: Vec<String> = vec![format!("# Formal report — {}", m.name()), String::new()];
    l.extend(header(m, &out_name));
    l.extend(summary(m, prov, &j, &unexpected));
    l.extend(scope(m));
    l.extend(plan(m, &j));
    l.extend(environment(&j, lintr));
    l.extend(property_table(m, &j));
    l.extend(cover_table(m, &j));
    l.extend(finding_blocks(m, base, &j));
    l.extend(mutation(&j));
    l.extend(limits(&j));
    l.extend(appendix(m, prov, &out_name, stats_log));
    let md = out.join("report.md");
    std::fs::write(&md, l.join("\n")).map_err(|e| format!("{}: {e}", md.display()))?;
    let subs = path_subs(m, out, st(&j["provenance"], "liberty"));
    portable_paths(&mut j, &subs);
    let jp = out.join("report.json");
    std::fs::write(&jp, serde_json::to_string_pretty(&j).unwrap() + "\n").map_err(|e| format!("{}: {e}", jp.display()))?;
    Ok(unexpected)
}

/// The machine-specific prefixes `report.json` drops, longest first: the run directory (its paths
/// become relative to it, where `report.json` lives), the RTL repository (written as the manifest
/// spells `[rtl] repo`), the manifest's directory, and the Liberty (its file name; the sha256 next
/// to it says which file it was).
fn path_subs(m: &Manifest, out: &Path, liberty: &str) -> Vec<(String, String)> {
    let mut subs: Vec<(String, String)> = Vec::new();
    let mut dir = |from: &Path, to: &str| {
        let from = from.to_string_lossy().trim_end_matches('/').to_string();
        if !from.is_empty() && from != "/" {
            subs.push((format!("{from}/"), if to.is_empty() { String::new() } else { format!("{to}/") }));
            subs.push((from, if to.is_empty() { ".".into() } else { to.to_string() }));
        }
    };
    dir(out, "");
    if let (Some(repo), Some(written)) = (m.repo(), m.rtl.get("repo").and_then(|r| r.as_str())) {
        dir(&repo, written.trim_end_matches('/'));
    }
    dir(&m.dir, "");
    if let Some(name) = Path::new(liberty).file_name().map(|f| f.to_string_lossy().into_owned()) {
        if Path::new(liberty).is_absolute() {
            subs.insert(0, (liberty.to_string(), name));
        }
    }
    subs.sort_by_key(|(from, _)| std::cmp::Reverse(from.len()));
    subs
}

/// Rewrite every string in `v` with `subs` (applied in order, longest prefix first) and name the
/// programs it ran by their file names. ⛔ `report.json` is published next to `report.md`; an
/// absolute path in it names the machine, the user and the directory layout of whoever ran it.
fn portable_paths(v: &mut Value, subs: &[(String, String)]) {
    let tool = Regex::new(r#"/[^\s"']*/(vyges-lec|vyges-formal|yosys|yosys-abc|verilator|sv2v)\b"#).unwrap();
    match v {
        Value::String(t) => {
            let mut x = t.clone();
            for (from, to) in subs {
                x = x.replace(from.as_str(), to);
            }
            *t = tool.replace_all(&x, "$1").into_owned();
        }
        Value::Array(a) => a.iter_mut().for_each(|e| portable_paths(e, subs)),
        Value::Object(o) => o.values_mut().for_each(|e| portable_paths(e, subs)),
        _ => {}
    }
}

/// The Scope rows naming every program a result depends on. A report written before the
/// simulator was recorded has no `verilator` key, and gets no row rather than an empty one.
fn tool_rows(p: &Value) -> Vec<String> {
    let mut l = vec![format!("| yosys | {} |", st(p, "yosys"))];
    if let Some(s) = p.get("sv2v").and_then(Value::as_str) {
        l.push(format!("| sv2v | {s} |"));
    }
    if let Some(v) = p.get("verilator").and_then(Value::as_str) {
        l.push(format!("| simulator | {v} |"));
    }
    l.push(format!("| prover | {} |", st(p, "lec")));
    l.push(format!("| campaign | {} |", st(p, "formal")));
    l
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    /// A packed request reads as named fields, the report's only view of it without a bit map.
    #[test]
    fn excerpt_decodes_a_packed_signal() {
        use crate::manifest::{Decode, DecodeField};
        let t = json!({"inputs_per_cycle": [{"tl[3]": true, "tl[4]": true, "tl[0]": true}]});
        let d = Decode {
            signal: "tl".into(),
            fields: vec![
                DecodeField { name: "addr".into(), lsb: 3, width: 2 },
                DecodeField { name: "rdy".into(), lsb: 0, width: 1 },
            ],
        };
        assert_eq!(super::decoded_excerpt(&t, 40, &[d]), ["cycle 0: tl(addr=0x3 rdy=0x1)"]);
    }

    /// The tool writes the sections in the specified order and the record its schema requires.
    #[test]
    fn report_has_every_section_and_the_schema_keys() {
        let dir = std::env::temp_dir().join(format!("vf-report-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let mf = dir.join("m.toml");
        std::fs::write(&mf, r#"
[ip]
name = "x"
[rtl]
top = "t"
files = ["t.v"]
[[requirement]]
id = "R-1"
text = "It holds."
[[assumption]]
id = "a"
text = "A."
class = "temporary"
[[property]]
id = "p"
text = "P."
requirements = ["R-1"]
assumptions = ["a"]
activation = "c"
[[cover]]
id = "c"
text = "C."
assumptions = ["a"]
"#).unwrap();
        let m = crate::manifest::Manifest::load(&mf).unwrap();
        let obj = |v: serde_json::Value| v.as_object().unwrap().clone();
        let prov = obj(json!({"rtl_commit": "abcdef0123456789", "rtl_dirty": false}));
        let base = obj(json!({
            "p": {"verdict": "holds", "seconds": 1.0, "status": "as-expected", "net": "vf_g_p"},
            "c": {"verdict": "fails", "cover": "reached", "seconds": 1.0, "status": "as-expected", "net": "vf_g_c"},
        }));
        super::report(&m, &dir, &prov, &obj(json!({})), &base, &[], &dir.join("none.log")).unwrap();
        let md = std::fs::read_to_string(dir.join("report.md")).unwrap();
        let mut at = 0;
        for n in 1..=10 {
            let h = format!("## {n}. ");
            let i = md[at..].find(&h).unwrap_or_else(|| panic!("section {n} missing or out of order"));
            at += i;
        }
        assert!(md.contains("It does not establish that all possible defects would be detected"));
        let j: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(dir.join("report.json")).unwrap()).unwrap();
        assert_eq!(j["verdict"], "CLEAN", "proved, activated, and a clean tree");
        assert_eq!(j["results"]["p"]["result"], "PROVEN");
        assert_eq!(j["results"]["p"]["activation"], "`c`: REACHED");
        let schema: serde_json::Value = serde_json::from_str(include_str!("../schemas/formal-report.schema.json")).unwrap();
        for k in schema["required"].as_array().unwrap() {
            assert!(j.get(k.as_str().unwrap()).is_some(), "report.json lacks {k}");
        }
        std::fs::remove_dir_all(&dir).unwrap();
    }

    /// A counterexample is confirmed by replay, so the simulator's version is part of the result.
    #[test]
    fn scope_names_the_simulator_and_sv2v_when_used() {
        let p = json!({"yosys": "Yosys 0.65", "verilator": "Verilator 5.040 2025-08-30 rev v5.040",
                       "sv2v": "v0.0.13", "lec": "vyges-lec 0.1.49", "formal": "vyges-formal 0.1.49"});
        assert_eq!(super::tool_rows(&p), [
            "| yosys | Yosys 0.65 |",
            "| sv2v | v0.0.13 |",
            "| simulator | Verilator 5.040 2025-08-30 rev v5.040 |",
            "| prover | vyges-lec 0.1.49 |",
            "| campaign | vyges-formal 0.1.49 |",
        ]);
        let old = json!({"yosys": "Yosys 0.65", "lec": "vyges-lec 0.1.48", "formal": "vyges-formal 0.1.48"});
        assert_eq!(super::tool_rows(&old).len(), 3, "an older report.json renders without new rows");
    }

    /// Paths in the run directory become relative to it, the repository reads as the manifest
    /// writes it, the Liberty and the programs by their names; nothing absolute is left.
    #[test]
    fn report_json_paths_are_portable() {
        let subs = vec![
            ("/l/sky.lib".to_string(), "sky.lib".to_string()),
            ("/w/out/".to_string(), String::new()),
            ("/w/out".to_string(), ".".to_string()),
            ("/w/ip/".to_string(), "../ip/".to_string()),
        ];
        let mut v = json!({
            "cmd": "/opt/t/vyges-lec prove /w/out/base.nl.v --lib /l/sky.lib -o /w/out/proofs/base/p.json",
            "rtl_repo": "/w/ip",
            "log": "/w/out/sim/p.log",
            "n": [1, "/usr/local/bin/yosys -V"],
        });
        super::portable_paths(&mut v, &subs);
        assert_eq!(v["cmd"], "vyges-lec prove base.nl.v --lib sky.lib -o proofs/base/p.json");
        assert_eq!(v["log"], "sim/p.log");
        assert_eq!(v["n"][1], "yosys -V");
        assert_eq!(v["rtl_repo"], "/w/ip", "an exact match is the prefix without its slash");
    }

    #[test]
    fn excerpt_groups_buses_and_shows_changes_only() {
        let t = json!({"cycle": 2, "inputs_per_cycle": [
            {"rst_ni": false, "d[0]": true, "d[1]": true},
            {"rst_ni": true, "d[0]": true, "d[1]": true},
            {"rst_ni": true, "d[0]": true, "d[1]": true},
        ]});
        assert_eq!(super::trace_excerpt(&t, 40), ["cycle 0: d=0x3", "cycle 1: rst_ni=1", "cycle 2: (no input change)"]);
    }

    #[test]
    fn excerpt_elides_the_middle_of_a_long_trace() {
        let cyc: Vec<_> = (0..100).map(|i| json!({"a": i % 2 == 1})).collect();
        let x = super::trace_excerpt(&json!({"inputs_per_cycle": cyc}), 40);
        assert_eq!(x.len(), 41);
        assert_eq!(x[20], "... 60 cycles elided ...");
        assert_eq!(x[40], "cycle 99: a=1");
    }
}
