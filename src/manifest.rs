//! The campaign manifest (TOML): the IP, its RTL, the monitors and where each binds, and every
//! assumption, property, cover and mutant.

use std::path::{Path, PathBuf};

use regex::Regex;
use toml::{Table, Value};

/// A property or a cover: one claim, named by its id and carried by the monitor net
/// `vf_p_<id>` (property) or `vf_c_<id>` (cover).
#[derive(Clone, Debug)]
pub struct Item {
    pub id: String,
    pub text: String,
    pub claim: String,
    /// What the specification says: `holds`/`fails` for a property, `reached`/`unreachable`
    /// for a cover. A recorded defect keeps the value that reproduces it, with `finding` set.
    pub expect: Option<String>,
    pub finding: Option<String>,
    pub assumptions: Vec<String>,
    pub bound: Option<i64>,
    pub timeout_s: Option<f64>,
}

#[derive(Clone, Debug)]
pub struct Bind {
    pub module: String,
    pub file: String,
    pub clock: String,
    pub reset: String,
    pub reset_active_low: bool,
}

#[derive(Clone, Debug)]
pub struct Mutant {
    pub id: String,
    pub module: String,
    pub find: String,
    pub replace: String,
    pub count: usize,
    pub text: String,
    pub properties: Vec<String>,
    pub expect: String,
}

#[derive(Clone, Debug)]
pub struct Assumption {
    pub id: String,
    pub text: String,
}

pub struct Manifest {
    pub path: PathBuf,
    pub dir: PathBuf,
    pub ip: Table,
    pub rtl: Table,
    pub synth: Table,
    pub tools: Table,
    pub binds: Vec<Bind>,
    pub assumptions: Vec<Assumption>,
    pub properties: Vec<Item>,
    pub covers: Vec<Item>,
    pub mutants: Vec<Mutant>,
    pub defaults: Table,
}

fn s(t: &Table, k: &str) -> Option<String> {
    t.get(k).and_then(Value::as_str).map(str::to_string)
}

fn req(t: &Table, k: &str, what: &str) -> Result<String, String> {
    s(t, k).ok_or_else(|| format!("{what}: `{k}` is required"))
}

fn tables(raw: &Table, k: &str) -> Vec<Table> {
    raw.get(k)
        .and_then(Value::as_array)
        .map(|a| a.iter().filter_map(|v| v.as_table().cloned()).collect())
        .unwrap_or_default()
}

fn strs(t: &Table, k: &str) -> Vec<String> {
    t.get(k)
        .and_then(Value::as_array)
        .map(|a| a.iter().filter_map(|v| v.as_str().map(str::to_string)).collect())
        .unwrap_or_default()
}

fn num(t: &Table, k: &str) -> Option<f64> {
    t.get(k).and_then(|v| v.as_float().or_else(|| v.as_integer().map(|i| i as f64)))
}

fn item(t: &Table, kind: &str) -> Result<Item, String> {
    let id = req(t, "id", kind)?;
    Ok(Item {
        text: req(t, "text", &format!("{kind} `{id}`"))?,
        claim: s(t, "claim").unwrap_or_default(),
        expect: s(t, "expect"),
        finding: s(t, "finding"),
        assumptions: strs(t, "assumptions"),
        bound: t.get("bound").and_then(Value::as_integer),
        timeout_s: num(t, "timeout_s"),
        id,
    })
}

impl Manifest {
    pub fn load(path: &Path) -> Result<Manifest, String> {
        let path = std::fs::canonicalize(path).map_err(|e| format!("{}: {e}", path.display()))?;
        let text = std::fs::read_to_string(&path).map_err(|e| format!("{}: {e}", path.display()))?;
        let raw: Table = text.parse().map_err(|e| format!("{}: {e}", path.display()))?;
        let sub = |k: &str| raw.get(k).and_then(Value::as_table).cloned().unwrap_or_default();
        let (ip, rtl) = (sub("ip"), sub("rtl"));
        req(&ip, "name", "[ip]")?;
        req(&rtl, "top", "[rtl]")?;
        if strs(&rtl, "files").is_empty() {
            return Err("[rtl]: `files` must list at least one file".into());
        }
        let binds = tables(&raw, "bind")
            .iter()
            .map(|b| {
                Ok(Bind {
                    module: req(b, "module", "[[bind]]")?,
                    file: req(b, "file", "[[bind]]")?,
                    clock: req(b, "clock", "[[bind]]")?,
                    reset: req(b, "reset", "[[bind]]")?,
                    reset_active_low: b.get("reset_active_low").and_then(Value::as_bool).unwrap_or(true),
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let assumptions = tables(&raw, "assumption")
            .iter()
            .map(|a| {
                let id = req(a, "id", "[[assumption]]")?;
                Ok(Assumption { text: req(a, "text", &format!("assumption `{id}`"))?, id })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let properties = tables(&raw, "property").iter().map(|t| item(t, "property")).collect::<Result<Vec<_>, _>>()?;
        let covers = tables(&raw, "cover").iter().map(|t| item(t, "cover")).collect::<Result<Vec<_>, _>>()?;
        let mutants = tables(&raw, "mutant")
            .iter()
            .map(|t| {
                let id = req(t, "id", "[[mutant]]")?;
                let w = format!("mutant `{id}`");
                Ok(Mutant {
                    module: req(t, "module", &w)?,
                    find: req(t, "find", &w)?,
                    replace: req(t, "replace", &w)?,
                    count: t.get("count").and_then(Value::as_integer).unwrap_or(1).max(0) as usize,
                    text: s(t, "text").unwrap_or_default(),
                    properties: strs(t, "properties"),
                    expect: s(t, "expect").unwrap_or_else(|| "killed".into()),
                    id,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        let ids: Vec<&str> = properties.iter().chain(&covers).map(|i| i.id.as_str()).collect();
        let mut dup: Vec<&str> = ids.iter().copied().filter(|i| ids.iter().filter(|j| *j == i).count() > 1).collect();
        dup.sort_unstable();
        dup.dedup();
        if !dup.is_empty() {
            return Err(format!("duplicate property/cover ids: {dup:?}"));
        }
        let idre = Regex::new(r"^[a-z][a-z0-9_]*$").unwrap();
        for i in ids.iter().copied().chain(assumptions.iter().map(|a| a.id.as_str())) {
            if !idre.is_match(i) {
                return Err(format!("id `{i}` must be lowercase [a-z0-9_]"));
            }
        }
        Ok(Manifest {
            dir: path.parent().unwrap().to_path_buf(),
            path,
            ip,
            rtl,
            synth: sub("synth"),
            tools: sub("tools"),
            binds,
            assumptions,
            properties,
            covers,
            mutants,
            defaults: sub("defaults"),
        })
    }

    pub fn name(&self) -> String {
        s(&self.ip, "name").unwrap_or_default()
    }
    pub fn top(&self) -> String {
        s(&self.rtl, "top").unwrap_or_default()
    }
    pub fn clock(&self) -> Option<String> {
        s(&self.rtl, "clock")
    }
    pub fn rtl_files(&self) -> Vec<String> {
        strs(&self.rtl, "files")
    }
    pub fn defines(&self) -> Vec<String> {
        strs(&self.rtl, "defines")
    }
    /// `yosys` (the files as written, the default) or `sv2v` (converted from SystemVerilog).
    pub fn frontend(&self) -> String {
        s(&self.rtl, "frontend").unwrap_or_else(|| "yosys".into())
    }
    /// `include` directories, relative to the repository like the files.
    pub fn include_dirs(&self) -> Vec<String> {
        strs(&self.rtl, "include_dirs")
    }
    pub fn extract_top(&self) -> bool {
        self.rtl.get("extract_top").and_then(Value::as_bool).unwrap_or(false)
    }
    pub fn repo(&self) -> Option<PathBuf> {
        s(&self.rtl, "repo").map(|r| self.p(&r))
    }
    /// `[rtl] params`, in the order written; a string value as written, without quotes.
    pub fn params(&self) -> Vec<(String, String)> {
        self.rtl
            .get("params")
            .and_then(Value::as_table)
            .map(|t| {
                t.iter()
                    .map(|(k, v)| (k.clone(), v.as_str().map(str::to_string).unwrap_or_else(|| v.to_string())))
                    .collect()
            })
            .unwrap_or_default()
    }
    pub fn ip_str(&self, k: &str) -> Option<String> {
        s(&self.ip, k)
    }
    pub fn synth_str(&self, k: &str) -> Option<String> {
        s(&self.synth, k)
    }
    pub fn synth_list(&self, k: &str) -> Option<Vec<String>> {
        self.synth.get(k).map(|_| strs(&self.synth, k))
    }
    pub fn tool(&self, k: &str) -> Option<String> {
        s(&self.tools, k)
    }
    pub fn default_timeout_s(&self) -> f64 {
        num(&self.defaults, "timeout_s").unwrap_or(900.0)
    }
    pub fn default_bound(&self) -> i64 {
        self.defaults.get("bound").and_then(Value::as_integer).unwrap_or(0)
    }

    /// A manifest path: absolute, `~`, `${ENV}`/`$ENV`, or relative to the manifest.
    pub fn p(&self, rel: &str) -> PathBuf {
        let q = PathBuf::from(expand_user(&expand_vars(rel)));
        let q = if q.is_absolute() { q } else { self.dir.join(q) };
        std::fs::canonicalize(&q).unwrap_or_else(|_| normalize(&q))
    }

    pub fn rtl_path(&self, f: &str) -> PathBuf {
        match self.repo() {
            Some(r) => r.join(f),
            None => self.p(f),
        }
    }
}

/// `$VAR` and `${VAR}`; an unset variable is left as written.
pub fn expand_vars(s: &str) -> String {
    let re = Regex::new(r"\$(\w+|\{[^}]*\})").unwrap();
    re.replace_all(s, |c: &regex::Captures| {
        let name = c[1].trim_start_matches('{').trim_end_matches('}');
        std::env::var(name).unwrap_or_else(|_| c[0].to_string())
    })
    .into_owned()
}

fn expand_user(s: &str) -> String {
    match (s.strip_prefix('~'), std::env::var("HOME")) {
        (Some(rest), Ok(h)) if rest.is_empty() || rest.starts_with('/') => format!("{h}{rest}"),
        _ => s.to_string(),
    }
}

/// `a/b/../c` → `a/c`, without touching the filesystem (for a path that does not exist yet).
fn normalize(p: &Path) -> PathBuf {
    let mut out = PathBuf::new();
    for c in p.components() {
        match c {
            std::path::Component::ParentDir => {
                out.pop();
            }
            std::path::Component::CurDir => {}
            c => out.push(c),
        }
    }
    out
}
