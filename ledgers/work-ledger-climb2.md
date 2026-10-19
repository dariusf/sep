# Ledger: climb 2, all remaining SL-COMP benchmarks

Started 2026-10-20. Previous ledgers: `ledgers/work-ledger-climb.md` (steps 1-22, T1-T6), `ledgers/work-ledger-post-climb.md` (baseline reset 2026-10-19).

## Goal

Grow the set of SL-COMP benchmarks that `xsearch` proves (and refutes) beyond the two divisions covered today (`qf_shls_entl` 296, `qf_shid_entl` 312: 454 of 608 provable, all proved; valid time 17.6 s at the 2026-10-19 baseline, `evolve/ref/baseline.csv`), one algorithmic improvement after another, and keep pushing total time down. S2S solved all of SL-COMP 2019 in about 60 s; aim lower.

Divisions not yet covered: `qf_shlid_entl` 60, `qf_shidlia_entl` 61, `shid_entl` 73, `shidlia_entl` 181, `onprob_qf_shid_entl` 11, and the sat divisions `qf_shls_sat` 110, `qf_shid_sat` 99, `qf_bsl_sat` 46, `qf_bsllia_sat` 24, `qf_shidlia_sat` 33.

Scope rule (user, 2026-10-20): the goal is the best separation-logic automation. Divisions whose difficulty is a background theory (LIA, bitvectors) are handled by delegating the pure residue to an existing Lean closing tactic (`omega`, `bv_decide`, `simp`), not by building arithmetic reasoning into `xsearch`; the separation-logic part around them is in scope.

## Acceptance criteria

- Monotone per step: full bench on every covered division, diff against the previous accepted CSV by file name: lost list empty; proved (or refuted) count not lower; no problem newly over 3500 ms.
- Standing rules from the previous ledgers hold: keep the `xsimpl` interface and speed it up internally; general tactics only, no hard-coded predicate names, shapes, or constants tuned to problems; no `sorry`, axioms, `native_decide`, `unsafe`; no comments or docstrings in code.
- Commit and push after each milestone; `telegram-ping` the user after each.

## How to use this ledger

Read this file fully, then `git status` and `git log --oneline -5`. An uncommitted `Sep/` edit means a subagent step was in flight: rebuild (`timeout 900 lake build Sep Bench bench`), rerun the bench, and diff before trusting it. Bench: `timeout 2400 lake exe bench --dir <d> ... --timeout 5000 --csv evolve/ref/<name>.csv`; `python3 scripts/bench-report.py` diffs CSVs. Subagents: Opus for implementation, Sonnet for refactoring; each gets the repo path, the rules above, the build and bench commands with timeouts, the previous accepted CSV, one technique, and the acceptance criterion; it reports proved total, gained and lost lists, and directory times. The supervising agent reviews each diff for generality before accepting. Before work: add a backlog item; after: a numbered history entry saying what and why (not how), with counts and times; mark dead ends DEAD END.

## History

(none yet)

## Backlog

- [ ] 1. Do `refactor.md` (split the xsimpl driver out of `Sep/SepLogic.lean` into `Sep/Xsimpl/Core.lean`); verify 454 proved, lost empty; commit.
- [ ] 2. Upgrade toolchain to Lean v4.35.0 (and mathlib to a matching tag); fix breakage; rebench; commit and push.
- [ ] 3. Survey the uncovered divisions: what logic each needs (`qf_shlid`: linear inductive definitions with data? `shid`: quantified; `shidlia`: inductive definitions + LIA; sat divisions: satisfiability checking, needs a model finder or a refutation procedure); what the `Bench/SmtLib` parser and `Bench/Encode` already accept; count parse-error vs unsupported vs failed per division when run as-is.
- [ ] 4. Yolo benchmarks (`Bench/Yolo/Cancel100..800`, `Misc`, `PureThings`): rerun through the driver, record times, decide whether they rejoin the regular bench as a time pressure.
- [ ] 5. Plan the climb from the survey: ordered list of techniques with expected reach per division; execute one subagent step per technique.
