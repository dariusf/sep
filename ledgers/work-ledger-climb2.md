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
4. (2026-10-20) Upgraded to Lean v4.35.0 and mathlib v4.35.0. Fixes: deprecated names (`Level.zero/one`, `ite_eq_left/right`, `List.getElem_cons_drop`), `requires`/`ensures` are now reserved keywords (parenthesised in HoareTests), the `do` elaborator drops a trailing `pure` so `hoare_step` got a `hoare_of_bind_ret` fallback, `dsimp only [wp]` no longer unfolds through the `Bind` instance so `SymExec` names `wp_bind`/`wp_pure`, and `Bench/Driver.lean` must call `unsafe Lean.enableInitializersExecution` before `importModules (loadExts := true)` (v4.35 throws otherwise; accepted as harness IO setup, the no-`unsafe` rule is about tactic and proof code). Bench `evolve/ref/lean435.csv`: 454 proved, identical set and reasons; proved-problem time 17.75 s to 14.75 s. Yolo Cancel300 5.5 s (was 5.3 s).
5. (2026-10-20) Stock-take over the five uncovered entailment divisions (`evolve/ref/stock.csv`; merged with lean435.csv into `evolve/ref/climb2-base.csv`, 1106 rows, 516 proved). Table and plan below. qf_shlid_entl is already complete (36/36 proved, all 24 sat refuted). Family table script: group `file` by the name prefix before the first digit, join with `:status` from the smt2.

## Backlog

- [x] 1. Do `refactor.md` (split the xsimpl driver out of `Sep/SepLogic.lean` into `Sep/Xsimpl/Core.lean`); verify 454 proved, lost empty; commit.
- [x] 2. Upgrade toolchain to Lean v4.35.0 (and mathlib to a matching tag); fix breakage; rebench; commit and push.
- [x] 3. Survey the uncovered divisions. Preliminary (2026-10-20, static read of the files; the driver already lists all 7 entailment dirs in `entlDirs`, the parser AST already has Int, arithmetic, quantifiers, `define-funs-rec`, and `xsearch` already discharges pure residues with `omega`):
  - `qf_shlid_entl` 60 (36 unsat): SPEN dll/nll/skl/lsso and Le's lss/sll; same shapes as `qf_shid_entl`. Expect mostly in reach already.
  - `shid_entl` 73 (70 unsat): Songbird 64, Iosif/SLIDE 9; 70 have an existential at the top of the RHS; 71 multi-predicate (mutual recursion in the SLIDE ones).
  - `qf_shidlia_entl` 61 (50 unsat): Songbird 39, Wu/COMPSPEN 22; Int parameters (length-indexed lists, dll with lengths), inequalities in 48.
  - `shidlia_entl` 181 (all unsat): Songbird; Int parameters, inequalities and RHS existentials (over Int and locations) in every file.
  - `onprob_qf_shid_entl` 11 (7 unsat): Harrsh; mutually recursive tll/atll/ptree; the encoder rejects forward references ("mutually recursive or forward-referenced predicate") unless the group machinery (`c.group`) covers it.
  - Sat divisions ignored for now (user, 2026-10-20). BSL = boolean SL without inductive predicates (CVC4).
  Done, see history 5.
- [x] 4. (see history 3) Yolo benchmarks (`Bench/Yolo/Cancel100..800`, `Misc`, `PureThings`): rerun through the driver, record times, decide whether they rejoin the regular bench as a time pressure.
- [x] 5. Plan written (below).

## Stock (2026-10-20, `evolve/ref/climb2-base.csv`, Lean v4.35.0, 5 s cap)

| division | provable | proved | refuted | unproved provable | main failure |
|---|---|---|---|---|---|
| qf_shls_entl | 174 | 174 | 122/122 | 0 | |
| qf_shid_entl | 280 | 280 | 32/32 | 0 | |
| qf_shlid_entl | 36 | 36 | 24/24 | 0 | |
| onprob_qf_shid_entl | 7 | 3 | 3/4 | 4 | timeout (Harrsh ptree/leaf-tree/dlgrid) |
| qf_shidlia_entl | 50 | 5 | 5/11 | 45 | no alternative (sls_join 17, Wu dll/ls-entl 9, Songbird dll_len 15, tseg_size 1) |
| shid_entl | 70 | 15 | 3/3 | 55 | no alternative (lsevenodd 18, eolseg 8, tseg/tree 11, ls 6, dll 7, misc) |
| shidlia_entl | 181 | 3 | | 178 | size gap 59, no alternative 119 (all Songbird length-indexed ls/dll/dllnull/dll_rev/sls/tree) |
| total | 798 | 516 | | 282 | |

No parse errors or unsupported problems: the encoder covers every entailment division; the whole gap is `xsearch` technique. Note 6 sat problems in qf_shidlia_entl time out instead of being refuted (the countermodel check requires `Params.val = Int`; arithmetic pures make it incomplete).

## Plan (ordered by reach; one Opus subagent step each, analysis first, design reviewed before implementation)

- [ ] S1. Length-indexed segments (reach ~110: Songbird `ls_len/dlen/plen/ubnd_*` ~80, `dll_len_get`/`dll_ubnd_len_get` 18, `ls_len_split*`, part of qf_shidlia `dll_len_*`). Shape: `P ... n` with an Int parameter that is 0 at the base and `k+1` in the step (`k = n - 1`, `0 ≤ n - 1`); problems use concrete lengths (1000) so unfolding cannot work. Needed, all generic from the unfold equation: an arithmetic-parameter kind in `SegDesc` (affine per step), join `P x u a ✶ P u y b ==> P x y (a+b)`, split `P x y n ✶ ⌈n = a + b ∧ 0 ≤ a ∧ 0 ≤ b⌉ ==> ∃u, P x u a ✶ P u y b` (lfp induction with a universally quantified invariant over a, b; case a = 0 / a > 0 by omega), head/tail peel (`P x y (n+1) ==> ∃u, x ↦ u ✶ P u y n` and the snoc form), witnesses for RHS Int existentials from arithmetic unification against LHS parameters, all side conditions to `omega`. Also fix `sizeGap` so an LHS predicate with an arithmetic parameter is not counted as unable to supply cells.
- [ ] S2. Length-indexed conversions and two-predicate splits (reach ~60: `dllnull_len_split_*` 50, `dll_len_concat_dllrev`, `dllrev_len_concat_dll`, `dllnull_len_entails_dll(rev)_len`, `dll_len_entails_ls/lsrev_len`): conversion inductions (dll ↔ dll_rev ↔ dllnull, dll → ls) carrying the length parameter, composed with S1's split.
- [ ] S3. Data-ordered segments (reach ~25: `sls_join` 21 across both LIA divisions, `sls_get_last_node*` 4): composition with pure payload constraints (`l ≤ a`, bounds threaded through the step); the composition lemma's invariant carries the bound, omega discharges.
- [ ] S4. Wu/COMPSPEN `ldll`/`ls` with lengths and Songbird trees with sizes (reach ~20: dll-entl 5, ls-entl 4, tree_size/tseg_size/tree_tseg_mix 11, tseg_size_join 2): same machinery as S1-S3 on 6-parameter dll and tree segments with size arithmetic.
- [ ] S5. Quantified `shid_entl` families (reach ~55): RHS existentials whose witnesses live inside LHS predicates (unfold-then-witness), parity predicates `ls_even/ls_odd/ls_all` with disjunctive non-recursive wrappers (lsevenodd 18), elseg/olseg conversions (eolseg 8), tree/tseg joins with unknown-rooted segments (11), dll/lsrev conversions with existential RHS (7), ls with existential RHS (6). Analyse per family before briefing.
- [ ] S6. onprob Harrsh trees (4): mutual tll/ptree inductions; timeouts, profile first.
- [ ] S7. Refutation for arithmetic problems: extend the countermodel check to Int parameters so the 6 qf_shidlia sat problems fail fast instead of timing out.
- [ ] T1. Cancellation at scale: Yolo Cancel100..400 grow about cubically (0.34/1.7/5.3/12.4 s); make xsimpl's cancellation and permutation proofs O(n log n) in atoms and memory-bounded, so Cancel500..800 run on 7 GB and all eight are under 5 s. Then the full-suite time.
- [ ] After each step: refresh the family table (script in history 5), pick the next largest unproved family, analyse one problem by hand before briefing.

Verification command for every step from now on: `timeout 3600 lake exe bench --dir qf_shls_entl --dir qf_shid_entl --dir qf_shlid_entl --dir qf_shidlia_entl --dir shid_entl --dir shidlia_entl --dir onprob_qf_shid_entl --timeout 5000 --csv evolve/ref/<step>.csv`, diffed against the previous accepted CSV (first: `evolve/ref/climb2-base.csv`).
