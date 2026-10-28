# vyges-formal

A **formal property campaign** on an IP's RTL, from a manifest to one report: monitors bound into
the design, every property and cover proved or refuted, every counterexample replayed in
simulation, mutants to measure the property set — and every result tied to the git commit of the
RTL it was run on.

> **Vyges open EDA tools.** Commercial-grade silicon sign-off capability, built on open standards
> and plain file formats — and meant to be accessible to everyone, not only teams who can license a
> six-figure tool. `vyges-formal` opens up property checking early in the design cycle.

## Use it

Through the Vyges CLI, installed with the physical engines:

```sh
curl --proto '=https' --tlsv1.2 -LsSf https://github.com/vyges-tools/cli/releases/latest/download/vyges-installer.sh | sh
# or: brew install vyges/tap/vyges
vyges install physical

vyges formal run manifest.toml --out formal-out          # prove, replay, mutate, report
vyges formal replay manifest.toml <id> --out formal-out --show u_core.state_q
vyges formal report manifest.toml --out formal-out       # re-render after editing expectations
```

`vyges physical formal …` is the same command. A campaign also needs
[Yosys](https://github.com/YosysHQ/yosys) and [Verilator](https://github.com/verilator/verilator) on
`PATH`, and a Liberty for the proof model (`--liberty FILE`, or `[synth] liberty` in the manifest).

Exit status: **0** every result as expected · **2** something unexpected (a claim or a mutant) ·
**1** a tool error. `--json` prints a summary (`report_path`, `unexpected`) when the run ends.

## What a campaign does

1. **Provenance** — the RTL's commit, whether its tree is dirty, and a sha256 of every input.
2. **Bind** — each monitor is spliced into the module it watches, where it sees that module's nets.
   Generated alongside it: `vf_armed` (1 once reset has been asserted and released), a sticky flag
   per assumption, and one gated net `vf_g_<id>` per claim.
3. **Synthesize** — Yosys flattens the bound design, makes every `vf_g_` net a top-level port, and
   maps it to the Liberty's cells.
4. **Lint** — registers by reset style. A register without reset starts at 0 in the model, which is
   an assumption, not a proof; the report lists them.
5. **Prove** — `vyges-lec prove --never vf_g_<id>` for every property and cover, `--jobs` at a time.
6. **Replay** — every counterexample is driven through the flattened RTL in Verilator, a second
   witness independent of the prover. One that does not replay is reported as UNEXPECTED.
7. **Mutants** — each RTL mutant is re-synthesized and re-proved; some property must catch it.
8. **Report** — `report.md` and `report.json`.

## The manifest

```toml
[ip]
name = "my-ip"
description = "One line on what is under proof."
scope_notes = """Configuration, what is and is not claimed."""

[rtl]
repo = "../my-ip"                 # a git repository: the report records its commit
files = ["rtl/my_ip.sv"]          # relative to repo
top = "my_ip"
clock = "clk_i"
params = { DEPTH = 16 }           # chparam on the top
# defines = ["SYNTHESIS"]
# extract_top = true              # keep only the top's module closure (for a file holding more)
# frontend = "sv2v"               # SystemVerilog packages/imports/interfaces: convert with sv2v
# include_dirs = ["rtl"]          # `include search path (sv2v), relative to repo

[synth]
liberty = "${PDK_ROOT}/sky130A/libs.ref/sky130_fd_sc_hd/lib/sky130_fd_sc_hd__tt_025C_1v80.lib"
# buffer = "sky130_fd_sc_hd__buf_1 A X"        # insbuf cell (defaults shown: sky130 hd)
# tie = "sky130_fd_sc_hd__conb_1 HI LO"        # constant cell
# dont_use = ["*lpflow*", "*probe*", "*edfxtp*", "*edfxbp*"]

[defaults]
timeout_s = 900                   # per proof; a timeout is undecided, never a pass
# bound = 0                       # 0 = unbounded proof; N = cycles 0..N only

[[bind]]
module = "my_ip_ctrl"             # the module the monitor is spliced into
file = "mon_ctrl.v"               # relative to the manifest
clock = "clk_i"
reset = "rst_ni"
# reset_active_low = true

[[assumption]]
id = "legal_len"
text = "Software programs a length the IP supports."

[[property]]
id = "done_after_last_stage"
claim = "C2"
text = "DONE is reported only after every stage has run."
assumptions = ["legal_len"]
# expect = "holds"                # what the specification says
# bound = 0 · timeout_s = 900

[[cover]]
id = "done_reached"
text = "A run completes."
# expect = "reached"

[[mutant]]
id = "mu_skip_last_stage"
module = "my_ip_ctrl"
find = "if \\(stage_q == last\\)"    # a regex, matched inside the module
replace = "if (stage_q == last - 1)" # \n, \t and \1 are expanded; $ is literal
text = "Finish one stage early."
# count = 1 · properties = ["..."] · expect = "killed"
```

### Monitors

A monitor is plain Verilog added to the body of the module it binds into, so it reads that module's
nets by name. It names its claims by convention:

| net | meaning |
|---|---|
| `vf_p_<id>` | 1 when property `<id>` is **violated** |
| `vf_c_<id>` | 1 when cover `<id>` is **hit** |
| `vf_a_<id>` | 0 when assumption `<id>` is **broken** |

```verilog
// mon_ctrl.v — bound into my_ip_ctrl
wire vf_p_done_after_last_stage = done_o & (stage_q != last);
wire vf_c_done_reached = done_o;
wire vf_a_legal_len = (len_q >= 8) & (len_q <= 10);
```

A claim counts only once reset has been asserted and released, and only while every assumption it
names has held on every cycle so far.

### Recording a finding

When a property fails because the design is wrong, record it rather than delete it: set `expect`
to the result that reproduces it (`fails`, or `unreachable` for a cover) and add `finding` text.
It then reads **FINDING** in the report — never a pass — and the report tracks it against the RTL
commit. Once the RTL is fixed, the finding turns UNEXPECTED until `expect` is set back to the
specification's value.

## Limits

- Proofs start from the **all-zero register state** and count after reset.
- Inputs are free except for the stated assumptions; memory read data is free unless a monitor
  models the memory, so data-path arithmetic needs a memory model.
- A bounded result says nothing past its bound; a liveness claim is a bounded response.
- A formal result is about the RTL as elaborated with the listed parameters; it does not establish
  timing closure, and it does not prove the specification is the intended one.

## License

Apache-2.0. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
