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

1. (2026-10-20) Split the xsimpl driver out of `Sep/SepLogic.lean` into `Sep/Xsimpl/Core.lean` per the (now deleted) `refactor.md`, so that class consumers (`Reordering`, `GrwSepLogic`) stop recompiling on driver edits. Pure move, no namespace changes. Bench `evolve/ref/split.csv`: 454 proved, lost and gained empty, reasons identical. Commit "Split the xsimpl driver into Sep/Xsimpl/Core".
2. (2026-10-20) `Bench/Yolo` moved to its own lake target `Yolo` (lakefile.toml). Reason: this machine has 7 GB RAM and 24 cores; `Bench.Yolo.Cancel500..800` are OOM-killed (exit 137, ~5.8 GB peak each) during `lake build Bench`, on unmodified HEAD too. `lake build Sep Bench bench` now completes (1427 jobs). Build Yolo on demand with `lake build Yolo`.
3. (2026-10-20) Yolo through the bench driver (`lake exe bench --dir yolo --filter <file>`, one file at a time; the whole dir OOM-kills the driver at 7 GB): PureThings 8.8 s, Misc 0.1 s, Cancel100 0.34 s, Cancel200 1.7 s, Cancel300 5.3 s, Cancel400 12.4 s; Cancel500..800 not runnable here. Growth is about cubic in the atom count, so cancellation at scale is a real target for `xsimpl` (memory as much as time). Decision: Cancel100..400 join the regular time measurements as a second pressure; Cancel500..800 become a milestone (first make them run under 7 GB, then under 5 s).

## Backlog

- [x] 1. Do `refactor.md` (split the xsimpl driver out of `Sep/SepLogic.lean` into `Sep/Xsimpl/Core.lean`); verify 454 proved, lost empty; commit.
- [ ] 2. Upgrade toolchain to Lean v4.35.0 (and mathlib to a matching tag); fix breakage; rebench; commit and push.
- [ ] 3. Survey the uncovered divisions. Preliminary (2026-10-20, static read of the files; the driver already lists all 7 entailment dirs in `entlDirs`, the parser AST already has Int, arithmetic, quantifiers, `define-funs-rec`, and `xsearch` already discharges pure residues with `omega`):
  - `qf_shlid_entl` 60 (36 unsat): SPEN dll/nll/skl/lsso and Le's lss/sll; same shapes as `qf_shid_entl`. Expect mostly in reach already.
  - `shid_entl` 73 (70 unsat): Songbird 64, Iosif/SLIDE 9; 70 have an existential at the top of the RHS; 71 multi-predicate (mutual recursion in the SLIDE ones).
  - `qf_shidlia_entl` 61 (50 unsat): Songbird 39, Wu/COMPSPEN 22; Int parameters (length-indexed lists, dll with lengths), inequalities in 48.
  - `shidlia_entl` 181 (all unsat): Songbird; Int parameters, inequalities and RHS existentials (over Int and locations) in every file.
  - `onprob_qf_shid_entl` 11 (7 unsat): Harrsh; mutually recursive tll/atll/ptree; the encoder rejects forward references ("mutually recursive or forward-referenced predicate") unless the group machinery (`c.group`) covers it.
  - Sat divisions ignored for now (user, 2026-10-20). BSL = boolean SL without inductive predicates (CVC4).
  Next: run the bench over all 7 dirs after the refactor builds, to get real parse-error / unsupported / failed / proved counts.
- [x] 4. (see history 3) Yolo benchmarks (`Bench/Yolo/Cancel100..800`, `Misc`, `PureThings`): rerun through the driver, record times, decide whether they rejoin the regular bench as a time pressure.
- [ ] 5. Plan the climb from the survey: ordered list of techniques with expected reach per division; execute one subagent step per technique.
