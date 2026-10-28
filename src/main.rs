//! vyges-formal CLI.
//!
//!   vyges-formal run    MANIFEST [--out DIR] [--jobs N] [--only ID,ID] [--no-mutants] [--json]
//!   vyges-formal replay MANIFEST ID --out DIR [--show SIG,SIG]
//!   vyges-formal report MANIFEST --out DIR
//!
//! Exit codes: 0 every result as expected · 2 something unexpected (a claim or a mutant), or usage ·
//! 1 a tool error.

use std::path::{Path, PathBuf};
use std::process::exit;

use serde_json::{json, Value};
use vyges_formal::flow::{self, Obj, Tools};
use vyges_formal::manifest::Manifest;
use vyges_formal::report;

/// A diagnostic as a structured event (`FORMAL-ERROR`, or `FORMAL-WARNING`; `vyges-events/1.0`)
/// instead of a bare stderr line; text after a blank line (the usage) stays plain help.
fn diag_line(msg: String) {
    let (head, help) = match msg.split_once("\n\n") {
        Some((h, rest)) => (h.to_string(), Some(rest.to_string())),
        None => (msg, None),
    };
    let warn = head.starts_with("warning: ");
    let text = head.strip_prefix("error: ").or_else(|| head.strip_prefix("warning: ")).unwrap_or(&head).to_string();
    let (severity, code) =
        if warn { (vyges_events::Severity::Warn, "FORMAL-WARNING") } else { (vyges_events::Severity::Error, "FORMAL-ERROR") };
    vyges_events::emit(&vyges_events::Event::new("vyges-formal", severity, text).with_code(code));
    if let Some(h) = help {
        eprintln!("{h}");
    }
}

macro_rules! diag {
    ($($t:tt)*) => { diag_line(format!($($t)*)) };
}

const USAGE: &str = "\
vyges formal — a formal property campaign on an IP's RTL, to one report

usage:
  vyges formal run    MANIFEST [--out DIR] [--jobs N] [--only ID,ID] [--no-mutants] [--json]
  vyges formal replay MANIFEST ID --out DIR [--show SIGNAL,SIGNAL]
  vyges formal report MANIFEST --out DIR

commands:
  run      bind the manifest's monitors into the RTL, synthesize, prove every property and cover
           with vyges-lec, replay every counterexample in Verilator, re-prove every mutant, and
           write DIR/report.md and DIR/report.json
  replay   replay one counterexample of a finished run, printing the claim and any --show signals
           (flattened names, e.g. u_core.state_q) cycle by cycle
  report   re-render a finished run's report after editing the manifest's expectations or text
           (no proof is re-run; refused if the RTL has moved to another commit since the run)

flags:
  --out DIR        the run's directory (run: default ./formal-<ip name>)
  --jobs N         proofs in parallel (default: half the cores)
  --only ID,ID     run only these properties/covers
  --no-mutants     skip the mutants
  --json           run: print a JSON summary on stdout when done
  --lec P · --yosys P · --verilator P · --sv2v P · --liberty FILE
                   the programs and the Liberty (default: the manifest, then
                   VYGES_FORMAL_LEC / _YOSYS / _VERILATOR / _SV2V / _LIBERTY, then PATH);
                   sv2v only for [rtl] frontend = \"sv2v\" (SystemVerilog packages, imports)
  --describe       print a machine-readable JSON description of every command
  -h, --help · -V, --version

The manifest (TOML) names the RTL ([rtl] repo, files, top, clock, params), the monitors and the
module each binds into ([[bind]]), and every [[assumption]], [[property]], [[cover]] and [[mutant]].
A monitor defines vf_p_<id> (1 = property violated), vf_c_<id> (1 = cover hit) and vf_a_<id>
(0 = assumption broken) from the nets of the module it binds into.

exit: 0 every result as expected · 2 something unexpected, or usage · 1 tool error
";

const COMMANDS: [&str; 3] = ["run", "replay", "report"];

/// The thread block's place in [`DESCRIBE`], filled from loom's wording in the other engines; this
/// engine runs its proofs as child processes, `--jobs` at a time.
const DESCRIBE: &str = r#"{
  "schema": "vyges-tool-descriptor/1.1",
  "name": "formal",
  "summary": "a formal property campaign on an IP's RTL: monitors bound into the design, every property and cover proved or refuted, counterexamples replayed in simulation, mutants to measure the property set, one report",
  "maturity": "structured",
  "provenance_limitations": [
    "Every result belongs to the RTL commit recorded in the report; a dirty working tree is flagged, not refused.",
    "Proofs start from the all-zero register state (the prover's model); a register without reset is listed in the report's lint, and its zero start is an assumption, not a proof.",
    "Inputs are free except for the manifest's assumptions; memory read data is free unless the monitors model it.",
    "A bounded result (holds_within N) says nothing past cycle N; a timeout is undecided, never a pass.",
    "Needs yosys and Verilator on PATH and vyges-lec (installed with the physical engines); without Verilator, counterexamples are reported unreplayed."
  ],
  "invocation": {
    "args_template": ["run", "{manifest}", "--json"],
    "optional": [ { "arg": "out", "flag": "--out" }, { "arg": "jobs", "flag": "--jobs" }, { "arg": "only", "flag": "--only" }, { "arg": "liberty", "flag": "--liberty" } ],
    "emits_json": true
  },
  "commands": [
    {
      "name": "run",
      "summary": "run the campaign the manifest describes and write report.md and report.json",
      "args_template": ["run", "{manifest}", "--json"],
      "optional": [ { "arg": "out", "flag": "--out" }, { "arg": "jobs", "flag": "--jobs" }, { "arg": "only", "flag": "--only" }, { "arg": "liberty", "flag": "--liberty" } ],
      "assertion": { "id": "all-as-expected", "field": "all_as_expected", "pass_when": { "is_true": true } }
    },
    {
      "name": "replay",
      "summary": "replay one counterexample of a finished run in simulation, cycle by cycle",
      "args_template": ["replay", "{manifest}", "{id}", "--out", "{out}"],
      "optional": [ { "arg": "show", "flag": "--show" } ]
    },
    {
      "name": "report",
      "summary": "re-render a finished run's report from its report.json (no proof re-run)",
      "args_template": ["report", "{manifest}", "--out", "{out}"],
      "optional": []
    }
  ],
  "inputs": {
    "type": "object",
    "required": ["manifest"],
    "properties": {
      "manifest": { "type": "string", "description": "path to the campaign manifest (TOML)" },
      "out": { "type": "string", "description": "the run's output directory" },
      "id": { "type": "string", "description": "replay: the property or cover whose counterexample to replay" },
      "show": { "type": "string", "description": "replay: comma-separated flattened signal names to print per cycle" },
      "jobs": { "type": "integer", "description": "run: proofs in parallel" },
      "only": { "type": "string", "description": "run: comma-separated property/cover ids to run" },
      "liberty": { "type": "string", "description": "the Liberty the proof model is mapped to (overrides the manifest)" }
    }
  },
  "consumes": ["rtl", "liberty"],
  "artifacts": [ { "role": "formal_report", "field": "report_path" } ],
  "threads": { "model": "processes", "flag": "--jobs", "default": "half the cores" },
  "assertion": { "id": "all-as-expected", "field": "all_as_expected", "pass_when": { "is_true": true } }
}
"#;

fn opt(args: &[String], name: &str) -> Option<String> {
    args.iter().position(|a| a == name).and_then(|i| args.get(i + 1).cloned())
}

fn fail(msg: impl std::fmt::Display) -> ! {
    diag!("error: {msg}");
    exit(1)
}

fn load(path: &str) -> Manifest {
    Manifest::load(Path::new(path)).unwrap_or_else(|e| fail(e))
}

fn tools(m: &Manifest, args: &[String]) -> Tools {
    flow::resolve_tools(m, opt(args, "--lec"), opt(args, "--yosys"), opt(args, "--liberty"), opt(args, "--verilator"), opt(args, "--sv2v"))
        .unwrap_or_else(|e| fail(e))
}

fn mkdir(p: &Path) {
    std::fs::create_dir_all(p).unwrap_or_else(|e| fail(format!("{}: {e}", p.display())));
}

fn abs(p: &str) -> PathBuf {
    let p = PathBuf::from(p);
    if p.is_absolute() {
        p
    } else {
        std::env::current_dir().map(|d| d.join(&p)).unwrap_or(p)
    }
}

fn cmd_run(args: &[String], manifest: &str) -> i32 {
    let mut m = load(manifest);
    let t = tools(&m, args);
    let out = abs(&opt(args, "--out").unwrap_or_else(|| format!("formal-{}", m.name())));
    mkdir(&out);
    let out = std::fs::canonicalize(&out).unwrap_or(out);
    let jobs = opt(args, "--jobs")
        .map(|j| j.parse::<usize>().unwrap_or_else(|_| fail(format!("--jobs wants a count, got {j:?}"))))
        .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get() / 2).unwrap_or(1).max(1));
    println!("vyges-formal: {} -> {}", m.name(), out.display());
    let prov = flow::provenance(&m, &t).unwrap_or_else(|e| fail(e));
    let (text, mods) = flow::prepare_rtl(&m, &t, &out).unwrap_or_else(|e| fail(e));
    println!("  rtl: {} module(s): {}", mods.len(), mods.join(" "));
    let (bound_text, _owner) = flow::bind_monitors(&m, &text).unwrap_or_else(|e| fail(e));
    std::fs::write(out.join("rtl.bound.v"), &bound_text).unwrap_or_else(|e| fail(e));
    if let Some(only) = opt(args, "--only") {
        let keep: Vec<&str> = only.split(',').collect();
        m.properties.retain(|p| keep.contains(&p.id.as_str()));
        m.covers.retain(|c| keep.contains(&c.id.as_str()));
    }
    let ids: Vec<String> = m.properties.iter().chain(&m.covers).map(|i| i.id.clone()).collect();
    let nl = flow::synthesize(&m, &t, &out, &ids, "base").unwrap_or_else(|e| fail(e));
    let lintr = flow::lint(&out, "base").unwrap_or_else(|e| fail(e));
    println!(
        "  netlist: {}; registers without reset: {}",
        nl.file_name().unwrap().to_string_lossy(),
        lintr["no_reset"].as_array().map_or(0, Vec::len)
    );
    let items: Vec<(&str, &vyges_formal::manifest::Item)> =
        m.properties.iter().map(|p| ("property", p)).chain(m.covers.iter().map(|c| ("cover", c))).collect();
    let mut base = flow::prove_all(&m, &t, &nl, &out, jobs, &items, "base").unwrap_or_else(|e| fail(e));
    // Every counterexample (a failing property, a reached cover) is replayed in simulation.
    replay_all(&m, &t, &out, &ids, &mut base);
    let mut muts: Vec<Value> = vec![];
    if !m.mutants.is_empty() && !args.iter().any(|a| a == "--no-mutants") {
        let per = (jobs / 2).max(1);
        muts = flow::par_map(&m.mutants, 2, |mu| Value::Object(flow::run_mutant(&m, &t, &out, mu, &bound_text, &ids, &base, per)));
    }
    let unexpected =
        report::report(&m, &out, &prov, &lintr, &base, &muts, &out.join("base.pass2.log")).unwrap_or_else(|e| fail(e));
    finish(&out, &unexpected, args.iter().any(|a| a == "--json"))
}

fn replay_all(m: &Manifest, t: &Tools, out: &Path, ids: &[String], base: &mut Obj) {
    if !base.values().any(|r| r.get("trace").is_some()) {
        return;
    }
    if t.verilator.is_none() {
        diag!("warning: verilator not found — counterexamples are reported without a simulation replay");
        return;
    }
    let rep = match flow::build_sim_model(m, t, out, ids).and_then(|_| flow::build_replayer(m, t, out, ids, &[], "vf_replay")) {
        Ok(r) => r,
        Err(e) => {
            diag!("warning: no simulation replay: {e}");
            return;
        }
    };
    for (i, r) in base.iter_mut() {
        let Some(r) = r.as_object_mut() else { continue };
        let Some(trace) = r.get("trace").cloned() else { continue };
        let rp = flow::replay(&rep, out, i, &trace);
        println!("  replay {i:40} confirmed={}", rp.get("confirmed").map_or("None".into(), |c| c.to_string()));
        if rp.get("confirmed") == Some(&json!(false)) {
            r.insert("status".into(), json!("UNEXPECTED"));
        }
        r.insert("replay".into(), Value::Object(rp));
    }
}

fn finish(out: &Path, unexpected: &[String], as_json: bool) -> i32 {
    let md = out.join("report.md");
    if as_json {
        println!(
            "{}",
            json!({"report_path": md.to_string_lossy(), "unexpected": unexpected, "all_as_expected": unexpected.is_empty()})
        );
    }
    if unexpected.is_empty() {
        println!("vyges-formal: report {} — all as expected", md.display());
        0
    } else {
        println!("vyges-formal: report {} — UNEXPECTED: {unexpected:?}", md.display());
        2
    }
}

fn read_run(out: &Path) -> Value {
    let p = out.join("report.json");
    let t = std::fs::read_to_string(&p).unwrap_or_else(|e| fail(format!("{}: {e} (is this a finished run?)", p.display())));
    serde_json::from_str(&t).unwrap_or_else(|e| fail(format!("{}: {e}", p.display())))
}

/// Re-render a finished run. Provenance is re-read, so the RTL must still be at the run's commit.
fn cmd_report(args: &[String], manifest: &str) -> i32 {
    let m = load(manifest);
    let t = tools(&m, args);
    let Some(out) = opt(args, "--out") else {
        diag!("error: `report` needs --out DIR (the run's directory)\n\n{USAGE}");
        exit(2);
    };
    let out = abs(&out);
    let old = read_run(&out);
    let mut prov = flow::provenance(&m, &t).unwrap_or_else(|e| fail(e));
    let was = old["provenance"]["rtl_commit"].as_str().unwrap_or("");
    let now = prov.get("rtl_commit").and_then(Value::as_str).unwrap_or("");
    if !was.is_empty() && now != was {
        fail(format!("the RTL is now at {now}, the run was at {was} — run the campaign again instead"));
    }
    prov.insert("run_utc".into(), old["provenance"]["run_utc"].clone());
    let mut base = old["results"].as_object().cloned().unwrap_or_default();
    // Re-classify against the manifest's current expectations.
    for it in m.properties.iter().chain(&m.covers) {
        if let Some(r) = base.get_mut(&it.id).and_then(Value::as_object_mut) {
            let kind = r.get("kind").and_then(Value::as_str).unwrap_or("property").to_string();
            let s = flow::classify(it, &kind, r);
            let s = if r.get("replay").and_then(|x| x.get("confirmed")) == Some(&json!(false)) { "UNEXPECTED".into() } else { s };
            r.insert("status".into(), json!(s));
        }
    }
    let lintr = old["lint"].as_object().cloned().unwrap_or_default();
    let muts = old["mutants"].as_array().cloned().unwrap_or_default();
    let unexpected =
        report::report(&m, &out, &prov, &lintr, &base, &muts, &out.join("base.pass2.log")).unwrap_or_else(|e| fail(e));
    finish(&out, &unexpected, args.iter().any(|a| a == "--json"))
}

fn cmd_replay(args: &[String], manifest: &str, id: Option<&String>) -> i32 {
    let m = load(manifest);
    let t = tools(&m, args);
    let (Some(id), Some(out)) = (id, opt(args, "--out")) else {
        diag!("error: `replay` needs an ID and --out DIR\n\n{USAGE}");
        exit(2);
    };
    let out = abs(&out);
    let run = read_run(&out);
    let res = run["results"].as_object().cloned().unwrap_or_default();
    let ids: Vec<String> = res.keys().cloned().collect();
    let Some(r) = res.get(id) else { fail(format!("`{id}` is not a result of the run in {}", out.display())) };
    let Some(trace) = r.get("trace") else { fail(format!("`{id}` has no counterexample")) };
    if !out.join("sim").join("sim.model.v").exists() {
        flow::build_sim_model(&m, &t, &out, &ids).unwrap_or_else(|e| fail(e));
    }
    let show: Vec<String> = opt(args, "--show").map(|s| s.split(',').map(String::from).collect()).unwrap_or_default();
    let rep = if show.is_empty() {
        flow::build_replayer(&m, &t, &out, &ids, &[], "vf_replay")
    } else {
        flow::build_replayer(&m, &t, &out, std::slice::from_ref(id), &show, "vf_show")
    }
    .unwrap_or_else(|e| fail(e));
    let rp = flow::replay(&rep, &out, id, trace);
    match rp.get("log").and_then(Value::as_str) {
        Some(log) => print!("{}", std::fs::read_to_string(log).unwrap_or_default()),
        None => println!("{}", Value::Object(rp.clone())),
    }
    let ok = rp.get("confirmed") == Some(&json!(true));
    println!("confirmed in simulation: {} (first hit cycle {})", ok, rp.get("first_hit").cloned().unwrap_or(Value::Null));
    if ok {
        0
    } else {
        2
    }
}

pub fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.iter().any(|a| a == "--describe") {
        print!("{DESCRIBE}");
        return;
    }
    if args.is_empty() || args.iter().any(|a| a == "-h" || a == "--help") {
        print!("{USAGE}");
        return;
    }
    if args.iter().any(|a| a == "-V" || a == "--version") {
        println!("vyges-formal {}", vyges_formal::VERSION);
        return;
    }
    let cmd = args[0].as_str();
    if !COMMANDS.contains(&cmd) {
        diag!("error: unknown command {cmd:?}\n\n{USAGE}");
        exit(2);
    }
    let valued = ["--out", "--jobs", "--only", "--lec", "--yosys", "--verilator", "--sv2v", "--liberty", "--show"];
    let pos: Vec<&String> = args[1..]
        .iter()
        .enumerate()
        .filter(|(i, a)| !a.starts_with('-') && !valued.contains(&args[*i].as_str()))
        .map(|(_, a)| a)
        .collect();
    let Some(manifest) = pos.first() else {
        diag!("error: `{cmd}` needs a MANIFEST\n\n{USAGE}");
        exit(2);
    };
    let code = match cmd {
        "run" => cmd_run(&args, manifest),
        "report" => cmd_report(&args, manifest),
        _ => cmd_replay(&args, manifest, pos.get(1).copied()),
    };
    exit(code);
}

#[cfg(test)]
mod tests {
    #[test]
    fn descriptor_is_json_and_describes_every_command() {
        let d: serde_json::Value = serde_json::from_str(super::DESCRIBE).unwrap();
        let named: Vec<&str> = d["commands"].as_array().unwrap().iter().map(|c| c["name"].as_str().unwrap()).collect();
        assert_eq!(named, super::COMMANDS);
        assert!(["discovered", "structured", "workflow-validated"].contains(&d["maturity"].as_str().unwrap()));
    }
}
