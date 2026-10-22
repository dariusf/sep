# Solving time, proofs and code size against agent hours

Raw data behind the chart "xsearch solving time against hours of agent work" (claude.ai artifact VFZJr2ctCgiqdifgdw34KE). One row per accepted step of the time climb (climb 1, steps 20 to T6) and of climb 2. Measurements on the Linux i7-13700, 5 s cap per problem.

## Columns

- hours: cumulative hours of Claude Code activity on this repository, computed by merging the timestamps of every transcript under `~/.claude/projects/-home-darius-projects-sep/` (main sessions and their `subagents/` directories) into one timeline and summing the gaps between consecutive events, counting a gap only when it is under 30 minutes. The origin is the first event of the 2026-09-25 session. Climb 1 step times were read from the main-thread transcript: a step counts as accepted when the main thread first runs the bench for the next step's CSV. Climb 2 step times are the modification times of the reference CSVs in `evolve/ref/`.
- old divisions s: time on `qf_shls_entl` + `qf_shid_entl` (454 provable of 608). Climb 1 values are the ledger's "valid time" (time on provable problems, including failures at the cap: the first row has 11 failures), from `ledgers/work-ledger-climb.md` histories 27 to 35. Climb 2 values are the sum of `ms` over proved rows of those two directories in the step's CSV, measured inside the seven-division run (standalone runs recorded in the climb 2 ledger are 1.5 to 2.5 s higher: 17.5 s at climb2-base, 18.6 s at the peak, 16.3 s at T1).
- suite proved s / suite total s: sum of `ms` over proved rows / over all rows of the seven entailment divisions (798 problems, 788 valid), from the step's CSV. Blank before the seven-division stock-take.
- proved: problems proved (climb 1: of the 454 provable in two divisions; climb 2: of the 788 valid in seven divisions).
- Xsearch.lean, SegC.lean, xsimpl driver, total lines: `wc -l` at the step's commit. The driver is `Sep/Xsimpl/Core.lean` from 2026-10-20 on, and `Sep/SepLogic.lean` before the split (it carried the driver and the class). Blank for climb 1 steps before the reset: their commits were removed when the repository was reset on 2026-10-19 (the ledger records only `Sep/Xsearch.lean` at some steps: 5885 lines at step 19, 6381 at step 22).

## Not covered

The proof climb before the time climb (steps 1 to 20, 2026-09-22 to 09-24, 289 to 454 proved on a Mac) has no transcripts on this machine and no times comparable to this machine; the step 20 measurement of 240 s was taken on the Mac.

## Data

| step | date | commit | hours | old divisions s | suite proved s | suite total s | proved | Xsearch.lean | SegC.lean | xsimpl driver | total lines | what changed |
|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|
| step 20 (Linux baseline) | 2026-09-25 00:33 |  | 0.39 | 348 |  |  | 443 |  |  |  |  | Wall-clock budgets tuned on a Mac; 11 provable problems fail on this machine |
| step 21 | 2026-09-25 03:05 |  | 2.92 | 219 |  |  | 454 |  |  |  |  | Virtual clock from heartbeats (deterministic budgets), cheaper facts, lazy segment lemmas, failed-subgoal memo |
| step 22 | 2026-09-25 04:25 |  | 4.26 | 187 |  |  | 454 |  |  |  |  | Cell-count pruning, countermodel on induction statements, alternative ordering |
| T2 | 2026-09-26 04:50 |  | 5.68 | 148.3 |  |  | 454 |  |  |  |  | Simp set built once per problem, always-failing xsimpl step removed, cheap defeq at cancel sites |
| T3 | 2026-09-26 06:11 |  | 7.03 | 77.2 |  |  | 454 |  |  |  |  | xsimpl driver works natively on atom lists; no fold/unfold/relevel/simp |
| T4 | 2026-09-26 08:28 |  | 9.32 | 33.3 |  |  | 454 |  |  |  |  | Declarations emitted directly, Meta procedures replace macro searches, Mono as a proof term |
| T5 | 2026-09-26 08:49 |  | 9.67 | 32.5 |  |  | 454 |  |  |  |  | One native xsimpl implementation; folded path and relevel deleted |
| T6 | 2026-09-26 11:44 |  | 12.58 | 17.6 |  |  | 454 |  |  |  |  | Countermodel on a compiled IR, goals built as Expr, native normalisers, caches reset per problem |
| reset | 2026-10-19 23:31 | 3f0c8c7 | 13.02 | 17.6 |  |  | 454 | 7568 | 0 | 2213 | 9781 | Repository reset to T6; evolution artefacts archived; driver still inside SepLogic.lean |
| lean435 | 2026-10-20 02:14 | 3a6d38a | 13.72 | 14.8 |  |  | 454 | 7568 | 0 | 2016 | 9584 | Driver split into Sep/Xsimpl/Core; Lean v4.35.0 and mathlib upgrade |
| climb2-base | 2026-10-20 02:22 | 3a6d38a | 13.84 | 14.8 | 17.2 | 259.0 | 516 | 7568 | 0 | 2016 | 9584 | Stock-take over seven divisions (798 problems, 788 valid) |
| S1 | 2026-10-20 03:22 | e612b75 | 14.86 | 15.1 | 29.9 | 266.2 | 601 | 8672 | 0 | 2016 | 10688 | Arithmetic segment descriptors, split/join/peel lemmas |
| S2 | 2026-10-20 04:01 | f9353c2 | 15.50 | 15.0 | 53.7 | 273.5 | 679 | 9164 | 0 | 2016 | 11180 | Conversions between length-indexed predicates, join-then-split plans |
| S3 | 2026-10-20 04:32 | c60cbbc | 16.01 | 15.0 | 56.1 | 220.1 | 708 | 9918 | 0 | 2016 | 11934 | Data descriptors and the data pass |
| S5a | 2026-10-20 05:13 | 9eb9640 | 16.71 | 15.0 | 68.2 | 176.5 | 745 | 10676 | 114 | 2016 | 12806 | Length abstraction through a Nat-indexed segment with length profiles |
| S5b | 2026-10-20 05:25 | 4a694ec | 16.90 | 15.1 | 68.3 | 167.0 | 754 | 10755 | 114 | 2016 | 12885 | Witness candidates for RHS existentials in predicate arguments |
| C1 st.1 | 2026-10-20 06:33 | 99adbc2 | 18.03 | 15.2 | 63.0 | 159.8 | 761 | 10763 | 255 | 2016 | 13034 | wseg carrier, one parse, Abs/Conc planner replaces ArD |
| C1 st.2 | 2026-10-20 07:52 | 10b3dc8 | 19.36 | 15.2 | 59.4 | 156.5 | 762 | 10266 | 255 | 2016 | 12537 | Data instance through wseg; DatD deleted |
| C1 st.3 | 2026-10-20 08:39 | 5133724 | 20.13 | 14.9 | 60.0 | 156.9 | 762 | 9934 | 150 | 2016 | 12100 | Length profiles through wseg; LenP and segC deleted |
| C1 st.4 | 2026-10-20 09:09 | 32817fa | 20.63 | 14.9 | 63.9 | 153.3 | 776 | 10224 | 150 | 2016 | 12390 | dll and size-indexed trees through wseg |
| C1 st.5 | 2026-10-20 11:08 | 6d0b92e | 22.62 | 15.3 | 73.5 | 147.4 | 780 | 10320 | 150 | 2016 | 12486 | One witness search replaces rootwit, arWitness, exWitAlt |
| C2 st.1 | 2026-10-20 12:58 | 0b31b93 | 23.79 | 15.4 | 63.1 | 136.9 | 780 | 10151 | 150 | 2016 | 12317 | SnocD deleted, lazy plan execution, cheaper arithmetic side goals |
| C2 st.2 | 2026-10-20 14:34 | d84ce78 | 25.39 | 15.7 | 63.9 | 137.8 | 780 | 10498 | 176 | 2016 | 12690 | End-guarded cells and nested cell payloads in wseg |
| C2 st.3a | 2026-10-20 16:44 | a53ba09 | 27.56 | 15.6 | 52.6 | 125.9 | 780 | 10984 | 450 | 2016 | 13450 | Generic Abs/Conc theorems, MetaM omega, one-pass multi-chain planning |
| P11 W | 2026-10-20 17:50 | 22fff8e | 28.66 | 15.6 | 53.8 | 116.9 | 783 | 11227 | 450 | 2016 | 13693 | Invariant facts at wseg entry, empty-segment elimination |
| P11 T | 2026-10-20 18:19 | 8cc2a10 | 29.14 | 15.6 | 54.1 | 117.1 | 785 | 11453 | 450 | 2016 | 13919 | Path-view Abs with predicate payloads, witness case split |
| P11 H | 2026-10-20 19:03 | d13dc38 | 29.88 | 15.5 | 54.1 | 102.1 | 788 | 11621 | 450 | 2016 | 14087 | Helper inlining, multi-cell bases, reversal planning: all 788 valid problems proved |
| C2 st.3b | 2026-10-20 21:08 | 0b624ff | 31.45 | 15.5 | 53.8 | 101.9 | 788 | 12091 | 450 | 2016 | 14557 | Nested payload composition, grouped join/split execution |
| C2 st.3b2 | 2026-10-20 22:48 | 203b7dd | 33.12 | 15.8 | 53.7 | 101.9 | 788 | 12314 | 450 | 2016 | 14780 | Direct LHS rewriting without xsimpl |
| C2 st.3c1 | 2026-10-21 00:24 | d348733 | 34.72 | 15.6 | 51.4 | 99.4 | 788 | 12421 | 450 | 2016 | 14887 | Plan selection inside the backtracking search, cached lemmas |
| C2 st.3c2 | 2026-10-21 01:29 | aa246b7 | 35.80 | 15.7 | 49.5 | 97.5 | 788 | 12616 | 450 | 2016 | 15082 | Invariant lemmas by library instances, shared group proofs |
| C2 st.3c2b | 2026-10-21 04:09 | 59f977d | 38.47 | 15.8 | 46.2 | 94.2 | 788 | 13199 | 1507 | 2016 | 16722 | Generic Abs/Conc/Inv over branch data for all path groups |
| C2 st.3c2c | 2026-10-21 05:17 | a78ed14 | 39.60 | 15.5 | 45.1 | 93.1 | 788 | 13243 | 1507 | 2016 | 16766 | Map attempts gated by cell signature, planner starts from RHS locations |
| C2 st.3c3 | 2026-10-21 09:19 | 3a67543 | 43.63 | 20.8 | 51.1 | 99.1 | 788 | 9874 | 2087 | 2016 | 13977 | Engine deletion: compose/SegDesc, proveInduct modes, ParD, witAlts deleted; attributed regression accepted |
| C2 st.3c4 | 2026-10-21 11:45 | 65ab6ca | 46.07 | 15.1 | 41.5 | 89.4 | 788 | 10136 | 2097 | 2016 | 14249 | LHS rewriting defects fixed, direct proof terms; C2 complete |
| C3 p.2a | 2026-10-21 13:04 | 9cdde0a | 47.39 | 14.8 | 39.7 | 87.6 | 788 | 10269 | 2111 | 2016 | 14396 | One deterministic conversion closer; no xsimpl or search in lemma building |
| C3 p.2b | 2026-10-21 13:59 | 0ba3c4d | 48.30 | 14.4 | 38.1 | 85.9 | 788 | 10007 | 2031 | 2016 | 14054 | One abs induction and one conc theorem over tails |
| C3 p.3 | 2026-10-21 14:41 | d673b04 | 49.02 | 14.2 | 37.6 | 85.4 | 788 | 9836 | 2031 | 2016 | 13883 | One reader of the unfold equation, one carrier derivation |
| C3 p.4 | 2026-10-21 16:28 | a097406 | 50.80 | 14.3 | 37.6 | 85.3 | 788 | 9571 | 2022 | 2016 | 13609 | One pure prover, one permutation prover, one allocation prover; 17 mechanisms deleted |
| C3 p.5a | 2026-10-21 22:03 | f58abad | 56.36 | 14.3 | 37.2 | 44.9 | 788 | 9750 | 2022 | 2016 | 13788 | Int countermodel, omega proof uses folded into the pure prover; sat problems fail fast |
| C3 p.5b | 2026-10-21 22:31 | d02c195 | 56.83 | 14.2 | 37.2 | 43.7 | 788 | 9905 | 2022 | 2016 | 13943 | Countermodel at depth zero replaces sizeGap and fastHopeless |
| C3 p.6 | 2026-10-21 23:07 | 0ec2f4e | 57.44 | 14.2 | 37.2 | 43.7 | 788 | 9851 | 2022 | 2016 | 13889 | One witness search (witSearch) with one ranking and one case split |
| C3 p.7 | 2026-10-22 01:33 | 2a6dcc5 | 59.86 | 14.3 | 37.6 | 44.1 | 788 | 9885 | 2022 | 2016 | 13923 | Bounds derived from the goal or deadline; three clock literals remain |
| C3 p.3b | 2026-10-22 05:22 | 350d744 | 63.68 | 14.3 | 37.5 | 44.0 | 788 | 9966 | 2254 | 2016 | 14236 | One theorem family (gAbs, gConc) with thin corollaries; 50 SegC theorems deleted |
| T0 A | 2026-10-22 06:46 | 812d979 | 65.09 | 14.0 | 36.6 | 43.1 | 788 | 9810 | 2254 | 2016 | 14080 | Fast path is xsimpl only, RHS macro inlining by forced determination |
| T0 B | 2026-10-22 07:02 | 0f62c6f | 65.34 | 13.6 | 35.2 | 41.7 | 788 | 9976 | 2283 | 2016 | 14275 | One witnessed branch closer for pg and gen |
| T1 | 2026-10-22 07:33 | 134c8fa | 65.87 | 13.8 | 35.6 | 42.2 | 788 | 9976 | 2283 | 2102 | 14361 | xsimpl cancellation by a reflected permutation certificate; Yolo Cancel800 0.6 s |
