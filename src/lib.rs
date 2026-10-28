//! vyges-formal — a formal property campaign on an IP, from RTL to one report.
//!
//! A campaign is a **manifest** (TOML) and a set of **monitors** (Verilog). Each monitor is spliced
//! into the module it watches, where it sees that module's nets, and names its claims as nets:
//! `vf_p_<id>` is 1 when property `<id>` is violated, `vf_c_<id>` is 1 when cover `<id>` is hit,
//! `vf_a_<id>` is 0 when assumption `<id>` is broken. The campaign then:
//!
//! 1. records **provenance**: the RTL's git commit and whether its tree is dirty, and a sha256 of
//!    every input;
//! 2. **binds** the monitors and generates, per module, the arming after reset, the sticky
//!    assumption flags, and one gated net `vf_g_<id>` per claim;
//! 3. **synthesizes** the bound design with yosys, every `vf_g_` net a top-level port, mapped to
//!    the Liberty's cells;
//! 4. **lints** the registers by reset style (a register without reset starts at 0 in the model,
//!    which is an assumption, not a proof);
//! 5. **proves** every claim with `vyges-lec prove --never vf_g_<id>`;
//! 6. **replays** every counterexample in Verilator, a second witness independent of the prover;
//! 7. re-proves each **mutant** of the RTL, which some property must catch;
//! 8. writes `report.md` and `report.json`.
//!
//! Every result belongs to exactly one RTL commit, and the report says which.

// The crate's own name inside it: the command-line entry ([`cli_main`]) is built into the
// library too, and its `vyges_formal::…` paths resolve here.
extern crate self as vyges_formal;

pub mod bits;
pub mod exec;
pub mod flow;
pub mod manifest;
pub mod pyrepl;
pub mod report;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const COPYRIGHT: &str = "© 2026 Vyges. All Rights Reserved.  https://vyges.com";

/// The `vyges-formal` command-line entry (the binary's `main`), built into the library too so a
/// suite binary can link every engine and run the one it is invoked as.
#[cfg(feature = "suite")]
#[doc(hidden)]
#[path = "main.rs"]
pub mod cli_main;
