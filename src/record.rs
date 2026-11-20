//! The verification record behind `report.json` and `report.md`: one vocabulary for every result,
//! the campaign verdict, and what each result rests on.
//!
//! A result is reported as what it is. A proof, a bounded check, a timeout and an unreachable cover
//! are counted separately, and nothing here computes a pass rate.

use std::fmt;

use serde_json::{json, Map, Value};

use crate::flow::Obj;
use crate::manifest::{Item, Manifest};

pub const SCHEMA_VERSION: &str = "vyges-formal-report/1.0";

/// What the prover established about one property or cover.
#[must_use]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Proven,
    Bounded,
    Failed,
    Reached,
    Unreachable,
    Undecided,
    Vacuous,
    Waived,
}

impl Outcome {
    pub const ALL: [Outcome; 8] = [
        Outcome::Proven,
        Outcome::Bounded,
        Outcome::Failed,
        Outcome::Reached,
        Outcome::Unreachable,
        Outcome::Undecided,
        Outcome::Vacuous,
        Outcome::Waived,
    ];
}

impl fmt::Display for Outcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Outcome::Proven => "PROVEN",
            Outcome::Bounded => "BOUNDED",
            Outcome::Failed => "FAILED",
            Outcome::Reached => "REACHED",
            Outcome::Unreachable => "UNREACHABLE",
            Outcome::Undecided => "UNDECIDED",
            Outcome::Vacuous => "VACUOUS",
            Outcome::Waived => "WAIVED",
        })
    }
}

/// The campaign's overall state, derived by rule and never set by hand.
#[must_use]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Clean,
    Findings,
    Incomplete,
}

impl fmt::Display for Verdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Verdict::Clean => "CLEAN",
            Verdict::Findings => "FINDINGS",
            Verdict::Incomplete => "INCOMPLETE",
        })
    }
}

/// The facts the verdict is derived from.
#[derive(Clone, Copy, Debug, Default)]
pub struct VerdictInput {
    pub properties: usize,
    pub open_failed: usize,
    pub dead_covers: usize,
    pub undecided: usize,
    pub vacuous: usize,
    pub unexpected: usize,
    pub unconfirmed_assumption_sets: usize,
    pub dirty: bool,
}

/// CLEAN needs evidence: a campaign that ran nothing is INCOMPLETE, never CLEAN.
pub fn verdict(i: VerdictInput) -> Verdict {
    if i.open_failed > 0 || i.dead_covers > 0 {
        return Verdict::Findings;
    }
    let complete = i.properties > 0
        && i.undecided == 0
        && i.vacuous == 0
        && i.unexpected == 0
        && i.unconfirmed_assumption_sets == 0
        && !i.dirty;
    if complete {
        Verdict::Clean
    } else {
        Verdict::Incomplete
    }
}

fn st<'a>(o: &'a Value, k: &str) -> &'a str {
    o.get(k).and_then(Value::as_str).unwrap_or("")
}

fn property_outcome(r: &Value) -> Outcome {
    match st(r, "verdict") {
        "holds" => Outcome::Proven,
        "holds_within" => Outcome::Bounded,
        "fails" => Outcome::Failed,
        _ => Outcome::Undecided,
    }
}

/// A cover not hit within a bound is undecided: only a proof makes it unreachable.
fn cover_outcome(r: &Value) -> Outcome {
    match st(r, "cover") {
        "reached" => Outcome::Reached,
        "unreachable" => Outcome::Unreachable,
        _ => Outcome::Undecided,
    }
}

fn undecided_cause(r: &Value) -> String {
    let secs = r.get("seconds").and_then(Value::as_f64).unwrap_or(0.0);
    match st(r, "verdict") {
        "timeout" => format!("timeout after {secs:.0} s"),
        "error" => format!("tool error: {}", st(r, "error").trim()),
        "holds_within" => {
            format!("not reached within {} cycles", r.get("bound").and_then(Value::as_i64).unwrap_or(0))
        }
        _ => "the prover gave up within its limits".into(),
    }
}

/// `vyges-lec` does not say whether its BDD pre-pass or ABC decided an unbounded result.
fn engine(r: &Value) -> &'static str {
    match r.get("bound").and_then(Value::as_i64) {
        Some(b) if b != 0 => "BMC",
        _ => "PDR or BDD pre-pass",
    }
}

/// Which engine decided the result, read off what `vyges-lec prove` returns. It does not name
/// the engine, so this is what its verdict, bound and register count rule out:
/// - the BDD pre-pass decides a cone in one cycle: it proves a net that is 0 in every state, and
///   fails a net only when the cone has no registers (at cycle 0);
/// - otherwise ABC decides: `pdr` without a bound (and is the only engine that gives up), `bmc`
///   (bmc3) with one (and is the only engine that returns "no failure within N cycles");
/// - the pre-pass hands over to ABC when its BDD outgrows its node limit, which the output does
///   not show either, so a proof is always one of two engines.
///
/// `engine` is set when exactly one engine fits, `candidates` lists every engine that fits, and
/// `basis` says why. Nothing decided (a timeout, an error) has no engine and no candidates.
pub fn decided_by(r: &Value) -> Value {
    let bounded = r.get("bound").and_then(Value::as_i64).is_some_and(|b| b != 0);
    let abc = if bounded { "bmc" } else { "pdr" };
    let registers = r.get("registers").and_then(Value::as_i64);
    let (candidates, basis): (Vec<&str>, String) = match st(r, "verdict") {
        "holds_within" => (vec!["bmc"], "only ABC's bmc3 reports no failure within a bound".into()),
        "undecided" => (vec!["pdr"], "only ABC's pdr gives up; the pre-pass always decides".into()),
        "fails" => match registers {
            Some(n) if n > 0 => (vec![abc], format!("{n} registers in the cone: the BDD pre-pass fails only a cone without registers")),
            Some(_) if bounded => (vec!["bdd-prepass"], "no registers in the cone, and bmc3 refuses a design without registers".into()),
            Some(_) => (
                vec!["bdd-prepass", "pdr"],
                "no registers in the cone: the BDD pre-pass decides it unless its BDD outgrows the node limit; the prover does not say which".into(),
            ),
            None => (vec!["bdd-prepass", abc], "the prover did not report the cone's register count".into()),
        },
        "holds" if bounded && registers == Some(0) => {
            (vec!["bdd-prepass"], "no registers in the cone, and bmc3 refuses a design without registers".into())
        }
        "holds" => (
            vec!["bdd-prepass", abc],
            "a proof comes from the BDD pre-pass (the net is 0 in every state) or from ABC; the prover does not say which".into(),
        ),
        "timeout" => (vec![], format!("nothing decided: the prover was stopped at its {} s timeout", secs_of(r))),
        _ => (vec![], "nothing decided: the prover returned no result".into()),
    };
    let engine = if candidates.len() == 1 { json!(candidates[0]) } else { Value::Null };
    json!({"engine": engine, "candidates": candidates, "basis": basis})
}

fn secs_of(r: &Value) -> String {
    format!("{:.0}", r.get("seconds").and_then(Value::as_f64).unwrap_or(0.0))
}

/// How deep the result reaches, in clock cycles (0: before the first edge).
/// - `bound_reached`: a bounded check found nothing in cycles 0 to `cycles`;
/// - `counterexample` / `witness`: the cycle the property failed or the cover was reached in;
/// - `unbounded`: a proof for every cycle; the prover reports no proof depth, so `cycles` is null;
/// - `none`: nothing was decided, so there is no depth.
///
/// `reason` says why `cycles` is null, and is null when it is not.
pub fn depth(r: &Value) -> Value {
    let cover = st(r, "kind") == "cover";
    let (cycles, kind, reason): (Option<i64>, &str, Option<String>) = match st(r, "verdict") {
        // The prover's own count; a record from before it was kept falls back to the bound it was given.
        "holds_within" => match r.get("cycles").and_then(Value::as_i64).or_else(|| r.get("bound").and_then(Value::as_i64)) {
            Some(n) => (Some(n), "bound_reached", None),
            None => (None, "bound_reached", Some("the prover reported no bound".into())),
        },
        "fails" => {
            let kind = if cover { "witness" } else { "counterexample" };
            match r.get("trace").and_then(|t| t.get("cycle")).and_then(Value::as_i64) {
                Some(c) => (Some(c), kind, None),
                None => (None, kind, Some("the prover returned no trace".into())),
            }
        }
        "holds" => (None, "unbounded", Some("a proof for every cycle; the prover reports no proof depth".into())),
        "undecided" => (None, "none", Some("ABC's pdr gave up; the prover reports no frame reached".into())),
        "timeout" => (None, "none", Some(format!("stopped at the {} s timeout; the prover reports no partial depth", secs_of(r)))),
        _ => (None, "none", Some("the prover returned no result".into())),
    };
    json!({"cycles": cycles, "kind": kind, "reason": reason})
}

fn subset(a: &[String], b: &[String]) -> bool {
    a.iter().all(|x| b.contains(x))
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Trigger {
    Shown,
    Impossible,
    Unconfirmed,
}

/// Whether a property's trigger was shown to occur.
///
/// A witness found under at least the property's assumptions also satisfies the property's. A cover
/// proved unreachable under at most the property's assumptions stays unreachable under them.
/// Anything else does not bear on this property.
fn activation(it: &Item, m: &Manifest, base: &Obj) -> (String, Trigger) {
    let Some(id) = &it.activation else {
        return ("not declared".into(), Trigger::Unconfirmed);
    };
    let found = m.covers.iter().find(|c| &c.id == id);
    let (Some(c), Some(r)) = (found, base.get(id)) else {
        return (format!("`{id}`: not run"), Trigger::Unconfirmed);
    };
    match cover_outcome(r) {
        Outcome::Reached if subset(&it.assumptions, &c.assumptions) => (format!("`{id}`: REACHED"), Trigger::Shown),
        Outcome::Unreachable if subset(&c.assumptions, &it.assumptions) => {
            (format!("`{id}`: UNREACHABLE"), Trigger::Impossible)
        }
        o => (format!("`{id}`: {o}, not under this property's assumptions"), Trigger::Unconfirmed),
    }
}

fn str_list(items: &[String]) -> Value {
    json!(items)
}

fn env_list(m: &Manifest, k: &str) -> Vec<String> {
    m.environment
        .get(k)
        .and_then(toml::Value::as_array)
        .map(|a| a.iter().filter_map(|v| v.as_str().map(str::to_string)).collect())
        .unwrap_or_default()
}

/// The assumption sets with no reached cover under at least those assumptions, so that nothing
/// shows them satisfiable. The empty set needs no witness.
fn unconfirmed_sets(m: &Manifest, base: &Obj) -> Vec<String> {
    let reached: Vec<&Item> = m
        .covers
        .iter()
        .filter(|c| base.get(&c.id).is_some_and(|r| cover_outcome(r) == Outcome::Reached))
        .collect();
    let mut out: Vec<String> = vec![];
    for p in &m.properties {
        if p.assumptions.is_empty() || reached.iter().any(|c| subset(&p.assumptions, &c.assumptions)) {
            continue;
        }
        let set = p.assumptions.join(", ");
        if !out.contains(&set) {
            out.push(set);
        }
    }
    out
}

fn enrich(it: &Item, r: &Value, outcome: Outcome, m: &Manifest, activated: &str) -> Value {
    let mut o: Map<String, Value> = r.as_object().cloned().unwrap_or_default();
    o.insert("result".into(), json!(outcome.to_string()));
    o.insert("engine".into(), json!(engine(r)));
    o.insert("decided_by".into(), decided_by(r));
    o.insert("depth".into(), depth(r));
    o.insert("requirements".into(), str_list(&it.requirements));
    o.insert("assumptions".into(), str_list(&it.assumptions));
    o.insert("activation".into(), json!(activated));
    o.insert("evidence".into(), json!(format!("proofs/base/{}.json", it.id)));
    if outcome == Outcome::Undecided {
        o.insert("cause".into(), json!(undecided_cause(r)));
    }
    if let Some(w) = m.waivers.iter().find(|w| w.id == it.id) {
        o.insert("waiver".into(), json!({"rationale": w.rationale, "owner": w.owner}));
    }
    Value::Object(o)
}

fn tally(values: &[Outcome]) -> Value {
    let mut o = Map::new();
    for k in Outcome::ALL {
        o.insert(k.to_string(), json!(values.iter().filter(|v| **v == k).count()));
    }
    Value::Object(o)
}

/// One kind's counts: how many the manifest declares, how many have no result, one count per
/// result in the vocabulary (zeros included), and the shallowest and deepest bound reached by a
/// bounded check that found nothing.
fn kind_summary(items: &[Item], results: &Map<String, Value>) -> Value {
    let ran: Vec<&Value> = items.iter().filter_map(|it| results.get(&it.id)).collect();
    let outcomes: Vec<Outcome> = ran
        .iter()
        .filter_map(|r| Outcome::ALL.into_iter().find(|o| o.to_string() == st(r, "result")))
        .collect();
    let bounds: Vec<i64> = ran
        .iter()
        .filter(|r| st(&r["depth"], "kind") == "bound_reached")
        .filter_map(|r| r["depth"]["cycles"].as_i64())
        .collect();
    json!({
        "found": items.len(),
        "not_run": items.len() - ran.len(),
        "by_result": tally(&outcomes),
        "bounded_depth": {"min": bounds.iter().min(), "max": bounds.iter().max()},
    })
}

/// The assumptions: how many the manifest declares, and of those how many constrain a property or
/// cover that a REACHED cover shows satisfiable (`witnessed`), how many constrain claims with no such
/// cover (`unwitnessed`), and how many constrain nothing (`unused`). The prover never checks an
/// assumption; a witness only shows it does not rule out the covered behaviour.
fn assumption_summary(m: &Manifest, base: &Obj) -> Value {
    let reached: Vec<&Item> =
        m.covers.iter().filter(|c| base.get(&c.id).is_some_and(|r| cover_outcome(r) == Outcome::Reached)).collect();
    let used = |a: &str| m.properties.iter().chain(&m.covers).any(|it| it.assumptions.iter().any(|x| x == a));
    let (mut witnessed, mut unwitnessed, mut unused) = (0, 0, 0);
    for a in &m.assumptions {
        if reached.iter().any(|c| c.assumptions.contains(&a.id)) {
            witnessed += 1;
        } else if used(&a.id) {
            unwitnessed += 1;
        } else {
            unused += 1;
        }
    }
    json!({"found": m.assumptions.len(), "by_witness": {"witnessed": witnessed, "unwitnessed": unwitnessed, "unused": unused}})
}

/// The `summary` block: the same keys in every record, zeros included.
fn summary(m: &Manifest, base: &Obj, results: &Map<String, Value>) -> Value {
    json!({
        "properties": kind_summary(&m.properties, results),
        "covers": kind_summary(&m.covers, results),
        "assumptions": assumption_summary(m, base),
    })
}

fn findings(m: &Manifest, base: &Obj, results: &Map<String, Value>, short: &str) -> Vec<Value> {
    let mut out = vec![];
    let result_of = |p: &str| results.get(p).map(|r| st(r, "result").to_string());
    let open = |p: &str| matches!(result_of(p).as_deref(), Some("FAILED" | "UNREACHABLE"));
    for f in &m.findings {
        let current: Map<String, Value> =
            f.properties.iter().map(|p| (p.clone(), json!(result_of(p).unwrap_or("not run".into())))).collect();
        let is_open = f.properties.iter().any(|p| open(p));
        let regression = if is_open {
            format!("still failing at {short}")
        } else {
            current
                .iter()
                .map(|(k, v)| format!("`{k}` {} at {short}", v.as_str().unwrap_or("")))
                .collect::<Vec<_>>()
                .join(", ")
        };
        out.push(json!({
            "id": f.id, "title": f.title, "properties": f.properties, "severity": f.severity,
            "found_at": f.found_at, "expected": f.expected, "root_cause": f.root_cause,
            "disposition": f.disposition, "fix": f.fix,
            "tracker": f.tracker.as_deref().filter(|t| !t.contains("://")),
            "state": if is_open { "open" } else { "closed" },
            "current": current, "regression": regression,
        }));
    }
    // Findings the manifest records but no findings file has triaged. One defect, one entry.
    let recorded: Vec<&String> = m.findings.iter().flat_map(|f| &f.properties).collect();
    let mut grouped: Vec<(String, Vec<String>)> = vec![];
    for it in m.properties.iter().chain(&m.covers) {
        let is_finding = base.get(&it.id).is_some_and(|r| st(r, "status") == "FINDING");
        if !is_finding || recorded.contains(&&it.id) {
            continue;
        }
        let text = it.finding.clone().unwrap_or_else(|| it.text.clone());
        match grouped.iter_mut().find(|(t, _)| *t == text) {
            Some((_, ids)) => ids.push(it.id.clone()),
            None => grouped.push((text, vec![it.id.clone()])),
        }
    }
    for (n, (text, ids)) in grouped.into_iter().enumerate() {
        out.push(json!({
            "id": format!("OPEN-{:02}", n + 1), "title": text.trim(), "properties": ids,
            "disposition": "untriaged", "state": "open", "found_at": short,
        }));
    }
    out
}

fn limitations(
    m: &Manifest,
    results: &Map<String, Value>,
    untraced: &[String],
    unconfirmed: &[String],
    check: Option<usize>,
    no_activation: &[String],
) -> Vec<String> {
    let mut l = vec![];
    for it in m.properties.iter().chain(&m.covers) {
        let Some(r) = results.get(&it.id) else { continue };
        match st(r, "result") {
            "UNDECIDED" => l.push(format!("`{}` is undecided: {}.", it.id, st(r, "cause"))),
            "BOUNDED" => l.push(format!(
                "`{}` is checked only through cycle {}.",
                it.id,
                r.get("bound").and_then(Value::as_i64).unwrap_or(0)
            )),
            "VACUOUS" => l.push(format!("`{}` proved, but its trigger cannot occur.", it.id)),
            "WAIVED" => l.push(format!(
                "`{}` is waived by {}: {}.",
                it.id,
                st(&r["waiver"], "owner"),
                st(&r["waiver"], "rationale")
            )),
            _ => {}
        }
    }
    for a in &m.assumptions {
        match a.class.as_deref() {
            Some(c @ ("design-restriction" | "temporary")) => {
                l.push(format!("Assumption `{}` ({c}) can hide a defect: {}", a.id, a.text));
            }
            None => l.push(format!("Assumption `{}` has no stated class or rationale.", a.id)),
            _ => {}
        }
    }
    if m.requirements.is_empty() {
        l.push("No requirements are declared, so claims are not traced to a specification.".into());
    } else if !untraced.is_empty() {
        l.push(format!("Not traced to a requirement: {}.", untraced.join(", ")));
    }
    if !no_activation.is_empty() {
        l.push(format!("{} properties have no confirmed activation cover.", no_activation.len()));
    }
    for s in unconfirmed {
        l.push(format!("No reached cover shows this assumption set is satisfiable: {s}."));
    }
    match check {
        Some(0) => {}
        Some(n) => l.push(format!("Yosys `check` reported {n} design problems; see the run log.")),
        None => l.push("Yosys `check` did not run, so loops and multiple drivers were not examined.".into()),
    }
    l
}

/// Everything `report.json` holds except the path clean-up.
pub fn build(
    m: &Manifest,
    prov: &Obj,
    lintr: &Obj,
    base: &Obj,
    muts: &[Value],
    unexpected: &[String],
    yosys_problems: Option<usize>,
) -> Value {
    let mut results = Map::new();
    let (mut prop_out, mut cov_out) = (vec![], vec![]);
    let mut no_activation = vec![];
    let actionable = |o: Outcome| matches!(o, Outcome::Failed | Outcome::Undecided | Outcome::Unreachable | Outcome::Vacuous);
    let waived = |id: &str| m.waivers.iter().any(|w| w.id == id);
    for it in &m.properties {
        let Some(r) = base.get(&it.id) else { continue };
        let (label, trigger) = activation(it, m, base);
        let mut o = property_outcome(r);
        if trigger == Trigger::Impossible && matches!(o, Outcome::Proven | Outcome::Bounded) {
            o = Outcome::Vacuous;
        }
        if actionable(o) && waived(&it.id) {
            o = Outcome::Waived;
        }
        if trigger != Trigger::Shown {
            no_activation.push(it.id.clone());
        }
        prop_out.push(o);
        results.insert(it.id.clone(), enrich(it, r, o, m, &label));
    }
    for it in &m.covers {
        let Some(r) = base.get(&it.id) else { continue };
        let mut o = cover_outcome(r);
        if actionable(o) && waived(&it.id) {
            o = Outcome::Waived;
        }
        cov_out.push(o);
        results.insert(it.id.clone(), enrich(it, r, o, m, ""));
    }
    let n = |v: &[Outcome], k: Outcome| v.iter().filter(|o| **o == k).count();
    // An item is a dead cover when it was expected to be reached and is not, or is a recorded defect.
    let dead_covers = m
        .covers
        .iter()
        .filter(|c| {
            results.get(&c.id).is_some_and(|r| {
                st(r, "result") == "UNREACHABLE" && matches!(st(r, "status"), "FINDING" | "UNEXPECTED")
            })
        })
        .count();
    let unconfirmed = unconfirmed_sets(m, base);
    let dirty = prov.get("rtl_dirty").and_then(Value::as_bool).unwrap_or(false);
    let v = verdict(VerdictInput {
        properties: prop_out.len(),
        open_failed: n(&prop_out, Outcome::Failed),
        dead_covers,
        undecided: n(&prop_out, Outcome::Undecided) + n(&cov_out, Outcome::Undecided),
        vacuous: n(&prop_out, Outcome::Vacuous),
        unexpected: unexpected.iter().filter(|id| !waived(id)).count(),
        unconfirmed_assumption_sets: unconfirmed.len(),
        dirty,
    });
    let traced = |ids: Vec<String>| json!(ids);
    let requirements: Vec<Value> = m
        .requirements
        .iter()
        .map(|q| {
            let by = |items: &[Item]| -> Vec<String> {
                items.iter().filter(|i| i.requirements.contains(&q.id)).map(|i| i.id.clone()).collect()
            };
            json!({"id": q.id, "text": q.text, "source": q.source,
                   "properties": traced(by(&m.properties)), "covers": traced(by(&m.covers))})
        })
        .collect();
    let untraced: Vec<String> =
        m.properties.iter().filter(|p| p.requirements.is_empty()).map(|p| p.id.clone()).collect();
    let uncovered: Vec<String> = requirements
        .iter()
        .filter(|q| q["properties"].as_array().is_some_and(Vec::is_empty))
        .map(|q| st(q, "id").to_string())
        .collect();
    let no_reset = lintr.get("no_reset").cloned().unwrap_or(json!([]));
    let environment = json!({
        "clocks": m.binds.iter().map(|b| json!({"module": b.module, "clock": b.clock, "reset": b.reset,
            "reset_active_low": b.reset_active_low})).collect::<Vec<_>>(),
        "assumptions": m.assumptions.iter().map(|a| json!({"id": a.id, "text": a.text,
            "rationale": a.rationale, "source": a.source, "class": a.class})).collect::<Vec<_>>(),
        "black_boxes": env_list(m, "black_boxes"),
        "cut_points": env_list(m, "cut_points"),
        "memory_models": env_list(m, "memory_models"),
        "reduced_parameters": env_list(m, "reduced_parameters"),
        "disabled_logic": env_list(m, "disabled_logic"),
        "registers_without_reset": no_reset,
        "setup": {"yosys_check_problems": yosys_problems, "unconfirmed_assumption_sets": unconfirmed},
    });
    let enriched: Vec<Value> = muts
        .iter()
        .map(|x| {
            let mut o = x.as_object().cloned().unwrap_or_default();
            let scope = m.mutants.iter().find(|d| d.id == st(x, "id")).map(|d| d.properties.clone()).unwrap_or_default();
            o.insert("run_against".into(), if scope.is_empty() { json!("all") } else { json!(scope) });
            Value::Object(o)
        })
        .collect();
    let killers: Vec<&str> = muts
        .iter()
        .flat_map(|x| x.get("killed_by").and_then(Value::as_array).into_iter().flatten())
        .filter_map(Value::as_str)
        .collect();
    let idle: Vec<String> = m
        .properties
        .iter()
        .filter(|p| matches!(results.get(&p.id).map(|r| st(r, "result")), Some("PROVEN" | "BOUNDED")))
        .filter(|p| !killers.contains(&p.id.as_str()))
        .map(|p| p.id.clone())
        .collect();
    let survivors: Vec<&str> = muts.iter().filter(|x| st(x, "status") != "killed").map(|x| st(x, "id")).collect();
    // A reached cover's trace is a witness, not a counterexample: only properties count here.
    let failing: Vec<&Value> =
        m.properties.iter().filter_map(|p| base.get(&p.id)).filter(|r| r.get("trace").is_some()).collect();
    let confirmed = |r: &Value| r.get("replay").and_then(|x| x.get("confirmed")).and_then(Value::as_bool).unwrap_or(false);
    let replayed = failing.iter().filter(|r| confirmed(r)).count();
    let traces = failing.len();
    let short: String = prov.get("rtl_commit").and_then(Value::as_str).unwrap_or("").chars().take(12).collect();
    let limits = limitations(m, &results, &untraced, &unconfirmed, yosys_problems, &no_activation);
    json!({
        "schema_version": SCHEMA_VERSION,
        "provenance": prov,
        "verdict": v.to_string(),
        "counts": {
            "properties": tally(&prop_out),
            "covers": tally(&cov_out),
            "counterexamples": {"replayed": replayed, "total": traces},
            "mutants": {"detected": muts.iter().filter(|x| st(x, "status") == "killed").count(), "total": muts.len()},
        },
        "summary": summary(m, base, &results),
        "requirements": requirements,
        "requirements_without_property": uncovered,
        "properties_without_requirement": untraced,
        "environment": environment,
        "lint": lintr,
        "findings": findings(m, base, &results, &short),
        "results": results,
        "mutants": enriched,
        "mutation": {"survivors": survivors, "idle_properties": idle},
        "limitations": limits,
        "unexpected": unexpected,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn clean() -> VerdictInput {
        VerdictInput { properties: 3, ..Default::default() }
    }

    #[test]
    fn a_verdict_needs_evidence() {
        assert_eq!(verdict(clean()), Verdict::Clean);
        assert_eq!(verdict(VerdictInput { properties: 0, ..clean() }), Verdict::Incomplete, "nothing ran");
    }

    #[test]
    fn each_gap_blocks_clean() {
        for i in [
            VerdictInput { undecided: 1, ..clean() },
            VerdictInput { vacuous: 1, ..clean() },
            VerdictInput { unexpected: 1, ..clean() },
            VerdictInput { unconfirmed_assumption_sets: 1, ..clean() },
            VerdictInput { dirty: true, ..clean() },
        ] {
            assert_eq!(verdict(i), Verdict::Incomplete, "{i:?}");
        }
    }

    #[test]
    fn a_defect_outranks_incompleteness() {
        assert_eq!(verdict(VerdictInput { open_failed: 1, undecided: 2, ..clean() }), Verdict::Findings);
        assert_eq!(verdict(VerdictInput { dead_covers: 1, ..clean() }), Verdict::Findings);
    }

    #[test]
    fn a_cover_missed_within_a_bound_is_not_unreachable() {
        assert_eq!(cover_outcome(&json!({"cover": "not-reached"})), Outcome::Undecided);
        assert_eq!(cover_outcome(&json!({"cover": "unreachable"})), Outcome::Unreachable);
    }

    #[test]
    fn undecided_results_say_why() {
        assert_eq!(undecided_cause(&json!({"verdict": "timeout", "seconds": 900.2})), "timeout after 900 s");
        assert_eq!(undecided_cause(&json!({"verdict": "error", "error": " boom\n"})), "tool error: boom");
        assert_eq!(
            undecided_cause(&json!({"verdict": "holds_within", "bound": 20})),
            "not reached within 20 cycles"
        );
    }

    /// What `vyges-lec prove` can decide with (its `prop::never`): the BDD pre-pass proves a net 0
    /// in every state, and fails one only in a cone without registers (cycle 0); ABC's `pdr` runs
    /// without a bound and is the only engine that gives up; `bmc3` runs with one, is the only
    /// engine that returns "no failure within N cycles", and refuses a design without registers.
    #[test]
    fn decided_by_names_only_an_engine_the_output_pins_down() {
        let e = |r: Value| decided_by(&r);
        let one = |r: Value| e(r)["engine"].clone();
        assert_eq!(one(json!({"verdict": "holds_within", "bound": 20, "registers": 9})), "bmc");
        assert_eq!(one(json!({"verdict": "undecided", "bound": null, "registers": 9})), "pdr");
        assert_eq!(one(json!({"verdict": "fails", "bound": null, "registers": 9})), "pdr", "registers rule out the pre-pass");
        assert_eq!(one(json!({"verdict": "fails", "bound": 30, "registers": 9})), "bmc");
        assert_eq!(one(json!({"verdict": "fails", "bound": 30, "registers": 0})), "bdd-prepass");
        assert_eq!(one(json!({"verdict": "holds", "bound": 30, "registers": 0})), "bdd-prepass");
        let p = e(json!({"verdict": "holds", "bound": null, "registers": 9}));
        assert_eq!((p["engine"].clone(), p["candidates"].clone()), (Value::Null, json!(["bdd-prepass", "pdr"])), "a proof: either");
        let p = e(json!({"verdict": "fails", "bound": null, "registers": 0}));
        assert_eq!(p["candidates"], json!(["bdd-prepass", "pdr"]));
        let t = e(json!({"verdict": "timeout", "seconds": 300.04}));
        assert_eq!((t["engine"].clone(), t["candidates"].clone()), (Value::Null, json!([])));
        assert!(st(&t, "basis").contains("300 s"), "{t}");
        for r in [json!({"verdict": "holds"}), json!({"verdict": "error"}), json!({"verdict": "fails", "registers": 3})] {
            assert!(!st(&e(r.clone()), "basis").is_empty(), "every answer says why: {r}");
        }
    }

    /// The depth is the prover's own figure, and null only with a reason.
    #[test]
    fn depth_is_the_bound_reached_or_the_failing_cycle() {
        let d = |r: Value| depth(&r);
        assert_eq!(d(json!({"verdict": "holds_within", "bound": 25, "cycles": 20})), json!({"cycles": 20, "kind": "bound_reached", "reason": null}));
        assert_eq!(d(json!({"verdict": "holds_within", "bound": 25}))["cycles"], 25, "an older record: the bound it was given");
        assert_eq!(d(json!({"verdict": "fails", "kind": "property", "trace": {"cycle": 7}})), json!({"cycles": 7, "kind": "counterexample", "reason": null}));
        assert_eq!(d(json!({"verdict": "fails", "kind": "cover", "trace": {"cycle": 3}}))["kind"], "witness");
        for r in [json!({"verdict": "holds"}), json!({"verdict": "timeout", "seconds": 9.0}), json!({"verdict": "undecided"}), json!({"verdict": "error"})] {
            let x = d(r.clone());
            assert!(x["cycles"].is_null() && !st(&x, "reason").is_empty(), "null with a reason: {r} -> {x}");
        }
    }

    fn manifest(text: &str) -> Manifest {
        let dir = std::env::temp_dir().join(format!("vf-record-test-{}-{}", std::process::id(), text.len()));
        std::fs::create_dir_all(&dir).unwrap();
        let f = dir.join("m.toml");
        std::fs::write(&f, text).unwrap();
        let m = Manifest::load(&f).unwrap();
        std::fs::remove_dir_all(&dir).unwrap();
        m
    }

    /// Every status in the vocabulary is present in the summary, zero or not, and the bounded
    /// depths are the extremes over bounded checks only.
    #[test]
    fn the_summary_keeps_every_key_and_the_bounded_extremes() {
        let m = manifest(
            r#"
[ip]
name = "x"
[rtl]
top = "t"
files = ["t.v"]
[[assumption]]
id = "a"
text = "A."
[[assumption]]
id = "b"
text = "B."
[[assumption]]
id = "z"
text = "Z."
[[property]]
id = "p1"
text = "P1."
assumptions = ["a", "b"]
[[property]]
id = "p2"
text = "P2."
[[property]]
id = "p3"
text = "P3."
[[property]]
id = "p4"
text = "P4."
[[cover]]
id = "c"
text = "C."
assumptions = ["a"]
"#,
        );
        let base: Obj = json!({
            "p1": {"verdict": "holds_within", "bound": 45, "cycles": 45, "kind": "property"},
            "p2": {"verdict": "holds_within", "bound": 20, "cycles": 20, "kind": "property"},
            "p3": {"verdict": "fails", "bound": null, "kind": "property", "registers": 4, "trace": {"cycle": 99}},
            "c": {"verdict": "fails", "cover": "reached", "kind": "cover", "registers": 4, "trace": {"cycle": 2}},
        })
        .as_object()
        .unwrap()
        .clone();
        let j = build(&m, &Obj::new(), &Obj::new(), &base, &[], &[], Some(0));
        let s = &j["summary"];
        let p = &s["properties"];
        assert_eq!((p["found"].clone(), p["not_run"].clone()), (json!(4), json!(1)), "p4 has no result");
        for o in Outcome::ALL {
            assert!(p["by_result"][o.to_string()].is_u64() && s["covers"]["by_result"][o.to_string()].is_u64(), "{o} missing");
        }
        assert_eq!((p["by_result"]["BOUNDED"].clone(), p["by_result"]["FAILED"].clone(), p["by_result"]["PROVEN"].clone()), (json!(2), json!(1), json!(0)));
        assert_eq!(p["bounded_depth"], json!({"min": 20, "max": 45}), "a counterexample's cycle 99 is not a bound");
        assert_eq!(s["covers"]["bounded_depth"], json!({"min": null, "max": null}));
        assert_eq!(s["assumptions"], json!({"found": 3, "by_witness": {"witnessed": 1, "unwitnessed": 1, "unused": 1}}));
        assert_eq!(j["results"]["p3"]["depth"]["cycles"], 99);
        assert_eq!(j["results"]["p3"]["decided_by"]["engine"], "pdr");
        // The schema requires exactly the keys written.
        let schema: Value = serde_json::from_str(include_str!("../schemas/formal-report.schema.json")).unwrap();
        let keys = |v: &Value| -> Vec<String> { v.as_object().unwrap().keys().cloned().collect() };
        let req = |v: &Value| -> Vec<String> { strs(&v["required"]) };
        let ks = &schema["$defs"]["kind_summary"];
        assert_eq!(keys(p), req(ks));
        assert_eq!(keys(&p["by_result"]), req(&ks["properties"]["by_result"]));
        assert_eq!(keys(s), req(&schema["properties"]["summary"]));
        let res = &schema["properties"]["results"]["additionalProperties"]["properties"];
        assert_eq!(keys(&j["results"]["p3"]["decided_by"]), req(&res["decided_by"]));
        assert_eq!(keys(&j["results"]["p3"]["depth"]), req(&res["depth"]));
    }

    fn strs(v: &Value) -> Vec<String> {
        v.as_array().unwrap().iter().map(|x| x.as_str().unwrap().to_string()).collect()
    }
}
