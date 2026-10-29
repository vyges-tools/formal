//! `report.md` and `report.json`: every result, the commit it belongs to, and how it was produced.

use std::path::Path;

use regex::Regex;
use serde_json::{json, Map, Value};

use crate::bits::Bits;
use crate::flow::{truthy, Obj};
use crate::manifest::Manifest;

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

/// Per cycle, the bus-grouped inputs that changed since the previous cycle (cycle 0: the non-zero ones).
pub fn trace_excerpt(trace: &Value, max_lines: usize) -> Vec<String> {
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
            let parts: Vec<String> = ch
                .iter()
                .map(|(k, v)| if v.gt1() { format!("{k}=0x{}", v.hex()) } else { format!("{k}={}", v.hex()) })
                .collect();
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

fn findings_table(m: &Manifest, base: &Obj, prov: &Obj) -> Vec<String> {
    let rows: Vec<_> = m
        .properties
        .iter()
        .chain(&m.covers)
        .filter(|it| base.get(&it.id).is_some_and(|r| st(r, "status") == "FINDING"))
        .collect();
    if rows.is_empty() {
        return vec![];
    }
    let short: String = prov.get("rtl_commit").and_then(Value::as_str).unwrap_or("").chars().take(12).collect();
    let mut l = vec![
        if short.is_empty() { "## Findings".to_string() } else { format!("## Findings at `{short}`") },
        String::new(),
        "Each is a design behaviour the specification forbids, shown for every input sequence (an unreachable \
         cover) or by a counterexample replayed in simulation. Re-run this campaign on a later commit to \
         track each one; a fixed finding turns UNEXPECTED until its `expect` is restored to the spec value."
            .into(),
        String::new(),
        "| id | claim | statement | evidence |".into(),
        "|---|---|---|---|".into(),
    ];
    for it in rows {
        let r = &base[&it.id];
        let ev = if st(r, "cover") == "unreachable" {
            "unreachable for every input sequence".to_string()
        } else {
            let cyc = r.get("trace").and_then(|t| t.get("cycle")).map(|c| c.to_string()).unwrap_or_else(|| "None".into());
            let conf = r.get("replay").and_then(|x| x.get("confirmed")).and_then(Value::as_bool).unwrap_or(false);
            format!("counterexample, cycle {cyc}{}", if conf { ", confirmed in simulation" } else { "" })
        };
        l.push(format!("| `{}` | {} | {} | {ev} |", it.id, it.claim, it.text));
    }
    l.push(String::new());
    l
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
    let props: Vec<_> = m.properties.iter().filter_map(|p| base.get(&p.id).map(|r| (p, r))).collect();
    let covs: Vec<_> = m.covers.iter().filter_map(|c| base.get(&c.id).map(|r| (c, r))).collect();
    let unexpected = unexpected(m, base, muts);
    let v = |r: &Value| st(r, "verdict").to_string();
    let count = |f: &dyn Fn(&Value) -> bool| props.iter().filter(|(_, r)| f(r)).count();
    let p = Value::Object(prov.clone());
    let mut l: Vec<String> = vec![format!("# Formal report — {}", m.name()), String::new()];
    l.extend(header(m, &out_name));
    l.extend([
        format!("_{}_", m.ip_str("description").unwrap_or_default()),
        String::new(),
        rtl_line(prov),
        String::new(),
        format!(
            "Run {} · overall: **{}**",
            st(&p, "run_utc"),
            if unexpected.is_empty() { "ALL AS EXPECTED".to_string() } else { format!("UNEXPECTED: {}", unexpected.join(", ")) }
        ),
        String::new(),
        "## Summary".into(),
        String::new(),
        "| | count |".into(),
        "|---|---|".into(),
        format!("| properties proved (unbounded) | {} |", count(&|r| v(r) == "holds")),
        format!("| properties holding within a bound | {} |", count(&|r| v(r) == "holds_within")),
        format!("| properties failing (counterexample) | {} |", count(&|r| v(r) == "fails")),
        format!(
            "| undecided (timeout / error) | {} |",
            count(&|r| !matches!(v(r).as_str(), "holds" | "holds_within" | "fails"))
        ),
        format!("| covers reached | {} / {} |", covs.iter().filter(|(_, r)| st(r, "cover") == "reached").count(), covs.len()),
        format!("| mutants killed | {} / {} |", muts.iter().filter(|x| st(x, "status") == "killed").count(), muts.len()),
        format!(
            "| **design findings (confirmed counterexamples / dead logic)** | {} |",
            base.values().filter(|r| st(r, "status") == "FINDING").count()
        ),
        format!(
            "| counterexamples confirmed in simulation | {} / {} |",
            base.values()
                .filter(|r| r.get("replay").and_then(|x| x.get("confirmed")).and_then(Value::as_bool).unwrap_or(false))
                .count(),
            base.values().filter(|r| r.get("trace").is_some()).count()
        ),
        String::new(),
    ]);
    l.extend(findings_table(m, base, prov));
    l.extend(["## Scope", "", "| item | value |", "|---|---|"].map(String::from));
    for k in ["rtl_remote", "rtl_commit", "rtl_commit_date", "rtl_dirty"] {
        if let Some(x) = prov.get(k) {
            let s = x.as_str().map(str::to_string).unwrap_or_else(|| x.to_string());
            l.push(format!("| {k} | `{s}` |"));
        }
    }
    l.push(format!("| top | `{}` |", m.top()));
    for (k, val) in m.params() {
        l.push(format!("| param `{k}` | {val} |"));
    }
    let short = |h: &Value| h.as_str().unwrap_or("").chars().take(16).collect::<String>();
    for (f, h) in p["rtl_files"].as_object().into_iter().flatten() {
        l.push(format!("| rtl `{f}` | sha256 `{}…` |", short(h)));
    }
    for (f, h) in p["monitors"].as_object().into_iter().flatten() {
        l.push(format!("| monitor `{f}` | sha256 `{}…` |", short(h)));
    }
    let lib_name = Path::new(st(&p, "liberty")).file_name().map(|f| f.to_string_lossy().into_owned()).unwrap_or_default();
    l.extend([
        format!("| liberty | `{lib_name}` sha256 `{}…` |", short(&p["liberty_sha256"])),
    ]);
    l.extend(tool_rows(&p));
    l.extend([
        String::new(),
        "## Limits of these results".into(),
        String::new(),
        LIMITS.into(),
    ]);
    if let Some(n) = m.ip_str("scope_notes") {
        l.extend([n.trim().to_string(), String::new()]);
    }
    l.extend(["## Assumptions", "", "| id | assumption |", "|---|---|"].map(String::from));
    l.extend(m.assumptions.iter().map(|a| format!("| `{}` | {} |", a.id, a.text)));
    l.extend(
        [
            "",
            "## Properties",
            "",
            "| id | claim | statement | mode | result | expected | status | time |",
            "|---|---|---|---|---|---|---|---|",
        ]
        .map(String::from),
    );
    for (it, r) in &props {
        let mode = match r.get("bound").and_then(Value::as_i64) {
            Some(b) if b != 0 => format!("bounded {b}"),
            _ => "unbounded".into(),
        };
        l.push(format!(
            "| `{}` | {} | {} | {mode} | {} | {} | {} | {}s |",
            it.id,
            it.claim,
            it.text,
            v(r),
            it.expect.as_deref().unwrap_or("holds"),
            st(r, "status"),
            secs(&r["seconds"])
        ));
    }
    let used: Vec<String> = props
        .iter()
        .map(|(it, _)| {
            let a = if it.assumptions.is_empty() { "none".to_string() } else { it.assumptions.join(", ") };
            format!("`{}`: {a}", it.id)
        })
        .collect();
    l.extend([String::new(), format!("Assumptions used: {}", used.join("; ")), String::new()]);
    for (it, r) in &props {
        if v(r) != "fails" {
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
            format!(
                "`{}` is 1 in cycle {cyc}. Inputs (changes only; full trace in `proofs/base/{}.json`):",
                st(r, "net"),
                it.id
            ),
            String::new(),
            "```".into(),
        ]);
        l.extend(trace_excerpt(&r["trace"], 40));
        l.extend(["```".to_string(), String::new()]);
    }
    l.extend(
        [
            "## Covers (non-vacuity)",
            "",
            "A cover that is reached shows the assumptions still allow that behaviour; an unreachable cover means \
             either the assumptions are too strong or the logic is dead.",
            "",
            "| id | statement | result | expected | status | at cycle |",
            "|---|---|---|---|---|---|",
        ]
        .map(String::from),
    );
    for (it, r) in &covs {
        let cyc = r.get("trace").and_then(|t| t.get("cycle")).map(|c| c.to_string()).unwrap_or_default();
        let res = r.get("cover").and_then(Value::as_str).map(str::to_string).unwrap_or_else(|| v(r));
        l.push(format!(
            "| `{}` | {} | {res} | {} | {} | {cyc} |",
            it.id,
            it.text,
            it.expect.as_deref().unwrap_or("reached"),
            st(r, "status")
        ));
    }
    for (it, r) in &covs {
        if let Some(f) = &it.finding {
            if st(r, "cover") != "reached" {
                l.extend([String::new(), format!("**`{}`:** {}", it.id, f.trim())]);
            }
        }
    }
    l.extend(
        [
            "",
            "## Mutants",
            "",
            "Each mutant is an RTL change a property should catch. A survivor means the property set has a gap.",
            "",
            "| id | change | status | killed by |",
            "|---|---|---|---|",
        ]
        .map(String::from),
    );
    for x in muts {
        let killed: Vec<&str> =
            x.get("killed_by").and_then(Value::as_array).map(|a| a.iter().filter_map(Value::as_str).collect()).unwrap_or_default();
        let by = if killed.is_empty() { st(x, "error").to_string() } else { killed.join(", ") };
        let ok = x.get("ok").and_then(Value::as_bool).unwrap_or(false);
        l.push(format!(
            "| `{}` | {} | {}{} | {by} |",
            st(x, "id"),
            st(x, "text"),
            st(x, "status"),
            if ok { "" } else { " (UNEXPECTED)" }
        ));
    }
    let names = |k: &str, n: usize| -> (usize, String) {
        let a: Vec<String> = lintr.get(k).and_then(Value::as_array).map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect()).unwrap_or_default();
        let shown: Vec<String> = a.iter().take(n).map(|s| format!("`{s}`")).collect();
        (a.len(), if a.is_empty() { String::new() } else { format!(" — {}", shown.join(", ")) })
    };
    let (ns, ss) = names("sync_reset", 20);
    let (nn, sn) = names("no_reset", 40);
    l.extend([
        String::new(),
        "## Lint".into(),
        String::new(),
        format!("- registers with async reset: {}", lintr.get("async_reset").cloned().unwrap_or(json!(0))),
        format!("- registers with sync reset: {ns}{ss}"),
        format!("- **registers without reset: {nn}**{sn}"),
        format!("- monitor registers (not design): {}", lintr.get("monitor").cloned().unwrap_or(json!(0))),
        String::new(),
    ]);
    if let Ok(log) = std::fs::read_to_string(stats_log) {
        if let Some(c) = Regex::new(r"Chip area for (?:top )?module.*?:\s*([\d.]+)").unwrap().captures(&log) {
            l.extend([
                format!("Synthesized for the proof (monitor included): chip area {} µm² — a proof model, not a signoff netlist.", &c[1]),
                String::new(),
            ]);
        }
    }
    l.extend(trailer(m, &out_name));
    let md = out.join("report.md");
    std::fs::write(&md, l.join("\n")).map_err(|e| format!("{}: {e}", md.display()))?;
    let mut j = json!({
        "provenance": prov,
        "lint": lintr,
        "results": base,
        "mutants": muts,
        "unexpected": unexpected,
    });
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
