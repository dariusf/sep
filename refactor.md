# Refactor: split the `xsimpl` driver out of `Sep/SepLogic.lean`

## Why

`Sep/SepLogic.lean` is 2213 lines. The `SepLogic` class, `AffineSepLogic` and the
generic lemmas derived from the class laws occupy lines 1 to 83. Everything after
`namespace Sep.Xsimpl` on line 85 is the entailment simplifier: trace class, the
`xsimpl_fold` / `xsimpl_unfold_class` attributes, `cheapCancel`, the `nt_*` proof
lemmas, the `NCtx` native driver, the caches, and the tactic syntax. `Sep/Xsimpl.lean`
is 99 lines: the `HProp` instance and the bridge lemmas.

So the file called `SepLogic` is the tactic, and the file called `Xsimpl` is an
instance. Two consequences:

- An edit to the class laws (rare) and an edit to the driver (the only remaining
  xsimpl time bucket, ~2 s) look identical to the build and to a reader.
- `Sep/Reordering.lean` and `Sep/GrwSepLogic.lean` import `Sep.SepLogic` for the
  class alone and use none of the tactic, yet they recompile on every driver change.

The import closure after the split should let the class be stable and the driver
be the one file that moves.

## Target layout

| File | Contents | Imports |
|---|---|---|
| `Sep/SepLogic.lean` | `SepLogic`, `AffineSepLogic`, `namespace SepLogic` lemmas (current lines 1 to 83), the `Std.Associative` / `Std.Commutative` instances, and the pure star AC and extraction lemmas that are stated only over the class (current sections `Lemmas`, `PureLemmas`, roughly lines 133 to 250) | `Lean` |
| `Sep/Xsimpl/Core.lean` | `namespace Sep.Xsimpl`: trace class, the two attributes, `cheapCancel` and `cheapDefEq`, `NativeLemmas` (`nt_*`), the `MetaM` star chain helpers, `NCtx`, the caches, `nativeGoal`, `xsimplDriver`, `xsimplClean`, and all `xsimpl_*` syntax and macro rules (current lines 85 to 132 and 252 to 2213) | `Sep.SepLogic` |
| `Sep/Xsimpl.lean` | unchanged content: the `HProp` instance, `@[xsimpl_fold]` bridge lemmas, `parseHstar`, `hstar_hexists_r` | `Sep.HProp`, `Sep.Xsimpl.Core` |

Everything that today imports `Sep.Xsimpl` keeps working unchanged, because
`Sep.Xsimpl` re-exports `Sep.Xsimpl.Core` transitively. Nothing outside the two
files needs to know the driver moved.

The lemma sections between lines 133 and 250 need a decision each: a lemma that
mentions only class operations and is used by the driver goes to `Core`; one that
is useful to any `SepLogic` consumer (star AC, `entails_trans` chains) stays in
`SepLogic`. The split is by audience, not by where the lemma happens to be used
today. When in doubt, keep it in `SepLogic`: `Core` imports it either way.

## Steps

1. **Create `Sep/Xsimpl/Core.lean`** by moving lines 85 to 2213 of `SepLogic.lean`
   verbatim, keeping `namespace Sep.Xsimpl` and the `open` lines. Add
   `import Sep.SepLogic` at the top. Leave the lemma sections (133 to 250) in place
   for now so that step 1 is a pure move with no reordering.

2. **Move the lemma sections.** Cut `section Lemmas` ... `end PureLemmas` out of
   `Core` and paste them after `end SepLogic` in `SepLogic.lean`, outside
   `namespace Sep.Xsimpl`. Fix the namespace: lemmas referenced as
   `Sep.Xsimpl.foo` from `Core` or from `Xsearch.lean` either keep their old name
   via `export`, or the references are updated. Grep first:

   ```sh
   grep -on "Sep\.Xsimpl\.[A-Za-z_]*" Sep/Xsearch.lean Sep/FrameInference.lean Sep/Examples -r | sort | uniq -c
   ```

   Today `Xsearch.lean` uses `parseHstar` (36 times), `xsimplDriver`,
   `xsimplClean`, `withCheapCancel`, `cheapAssumptionCore`, `hstar_hexists_r`.
   `FrameInference.lean` uses `himpl_lhs_eq`, `sep_weaken_leftover` and the
   `xsimpl_*` tactics. None of these are in the lemma sections, so the move is
   expected to be name-neutral.

3. **Point `Sep/Xsimpl.lean` at `Core`.** Replace `import Sep.SepLogic` with
   `import Sep.Xsimpl.Core`. Keep `import Sep.HProp`.

4. **Rename the `SepLogic` docstring header** so it describes only the class.
   The driver gets a header in `Core` (user writes it).

5. **Switch `FrameInference.lean` to `import Sep.Xsimpl.Core`** since it uses the
   tactics. `Reordering.lean` and `GrwSepLogic.lean` keep `import Sep.SepLogic`
   and now stop depending on the driver.

6. **Build and bench.**

   ```sh
   timeout 900 lake build Sep Bench bench
   timeout 2400 lake exe bench --dir qf_shls_entl --dir qf_shid_entl --timeout 5000 --csv evolve/ref/split.csv
   ```

   Diff `evolve/ref/split.csv` against `evolve/ref/baseline.csv`: 454 proved, lost
   list empty, same reason texts. The move changes no code, so any difference is
   a namespace or instance-resolution slip, not a tactic change.

7. **Commit** as one step: "Split the xsimpl driver into Sep/Xsimpl/Core; SepLogic
   holds only the class". Ledger entry under History.

## Optional follow-ups, separate commits

- **Yolo out of the default `Bench` target.** `Bench/Yolo/Cancel100..800` import
  `Sep.Xsearch` and cost 10 to 31 s each to elaborate, serially. They are the
  bulk of a rebuild after any driver change. Add a `[[lean_lib]] name = "Yolo"`
  with `globs = ["Bench.Yolo.+"]`, remove them from the `Bench` glob, and build
  them on demand with `lake build Yolo`. The driver and `bench` executable do not
  import them.

- **Yolo imports.** The Cancel files only need `xsimpl`, but the proof script
  calls `xsearch` (the port of `xsimp'`). Keep `xsearch` for fidelity with
  upstream; this is why they must import `Sep.Xsearch`. `Misc.lean` likewise.

- **`Bench/Fixpoint.lean` imports `Sep.Xsearch`** only for the `xsearch_unfold`
  attribute and `hmono`'s lemma names. If the attribute moved into a small
  `Sep/XsearchAttr.lean`, the encoder would not depend on the 7500-line search
  file, and an edit to the search would not rebuild the encoder. Low value until
  encoder edits become frequent.

## Non-goals

- No change to the `xsimpl` interface or behaviour. The ledger's standing rule
  stays: one implementation, sped up internally.
- No renaming of the `Sep.Xsimpl` namespace. The tactic names and attribute
  names are used by `Examples`, `FrameInference`, `Xsearch` and the ledgers.
- No change to `SepLogic` laws.

## Risks

- **Instance resolution order.** `Sep/Xsimpl.lean` declares the `HProp` instance
  after importing the driver. Today the driver is in scope before the instance
  as well, so this is unchanged.
- **`initialize` ordering.** `cheapCancel`, the trace class, the attributes and
  the three caches are `initialize` blocks. They move together inside `Core`, so
  their relative order is preserved. The attributes must be registered before
  any `@[xsimpl_fold]` use, which is in `Sep/Xsimpl.lean`, downstream.
- **`register_simp_attr`** produces a simp set whose name is global. Moving it
  between files does not change the name.
