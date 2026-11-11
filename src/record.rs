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
}
