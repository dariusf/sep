# Ledger: Sep/Xsearch.lean

## Baseline (2026-10-19)

The repo is reset to the best version reached by the manual climb and the phase-3 time climb: step T6 of the previous ledger. Full bench (`qf_shls_entl` + `qf_shid_entl`, 5 s cap, Linux i7-13700): 454 of 608 proved (every provable problem), valid time 17.6 s, invalid time 0.84 s, slowest proved problem 0.40 s. Reference CSV: `ref/baseline.csv`.

The previous ledger (steps 1-22 and T1-T6), the OpenEvolve configuration, evaluator, reference programs and every step CSV, the profiles `PROFILE-T4.md` and `PROFILE-T6.md`, and the uncommitted diffs of the deleted worktrees are archived outside the repo at `/home/darius/projects/sep-archive-2026-10-19/`. Git history on `master` keeps every accepted step.

## Standing rules

- Keep the `xsimpl` interface; speed it up internally, never duplicate it with a parallel normaliser.
- The tactics are general: no overfitting to SL-COMP, no hard-coded predicate names, shapes, or constants tuned to particular problems.
- Every accepted step is monotone: full-bench diff against `ref/baseline.csv` (or the latest accepted CSV) has an empty lost list; proved count 454; no proved problem over 3500 ms.
- No `sorry`, axioms, `native_decide`, `unsafe`; no comments or docstrings in the code.

## How to use this ledger

Verification is `timeout 2400 lake exe bench --dir qf_shls_entl --dir qf_shid_entl --timeout 5000 --csv <out.csv>`, diffed by file name against `ref/baseline.csv`. Before doing work, add a backlog item; after, add a numbered history entry saying what was done and why, with the proved total and valid time; mark dead ends as DEAD END.

## History

(none since the reset)

## Backlog

- [ ] Decide the next phase: continue the time climb (remaining buckets ~2 s each: countermodel check 2.3 s, kernel 1.7 s, xsimpl 2.1 s, compose 0.9 s) or evolve for time and lines from this baseline.
