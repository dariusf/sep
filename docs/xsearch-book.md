# Entailment Search in Separation Logic: The `xsimpl` and `xsearch` Tactics

## Prerequisites

This text assumes that the reader is familiar with the following material and does not explain it.

- Separation logic: heaps as finite maps from locations to values, the points-to assertion, separating conjunction, the magic wand, existential quantification over heap assertions, pure facts embedded in heap assertions, inductive predicates defined as least fixed points, and entailment between heap assertions.
- The interface of an `xsimpl`-style simplification tactic: it cancels atoms that occur on both sides of an entailment, extracts existentials and pure facts from the left-hand side into the local context, instantiates existentials of the right-hand side, and leaves a residual entailment or residual side conditions.
- Lean 4 and its meta-level programming interface at a working level: `Expr`, `MVarId`, the local context, the monads `MetaM` and `TacticM`, `isDefEq`, `mkAppM` and `instantiateMVars`.

The text does not assume knowledge of the implementation of `xsimpl`, of anything specific to the repository `/home/darius/projects/sep`, or of the SL-COMP benchmark. Where the benchmark matters, the relevant facts are stated.

The text uses the names and notation of `Sep/HProp.lean`. A heap assertion has type `HProp`, which is `Heap → Prop`; `H1 ✶ H2` is separating conjunction, `H1 -✶ H2` the magic wand, `∃✶ x, J x` the existential, `∀✶ x, J x` the universal quantifier over heap assertions (`hforall`, which occurs only inside the search's own lemmas), `⌈P⌉` the pure fact (an assertion that holds of the empty heap exactly when `P` holds), `x ↦ v` the points-to assertion for a single cell, `emp` the empty heap, and `H1 ==> H2` entailment. Locations have type `Loc`, which is `Nat`; the location `0` plays the role of nil. In the benchmark encoding the type of values is `Int`.

Throughout, a code block that quotes a source file contains text copied verbatim from it, and a line consisting of `…` inside such a block marks an omission. The few code blocks that display an example goal or a term derived by the tactic say so in the surrounding text.

## 1. Overview

### 1.1 The problem

The tactic `xsearch` proves entailments `L ==> R` between symbolic heaps. A symbolic heap here is a separating conjunction of points-to cells, pure facts, existentially quantified variables and atoms of user-defined inductive predicates, possibly with disjunctions inside predicate bodies. This is the problem posed by the entailment divisions of SL-COMP, the separation logic competition. The repository translates each SL-COMP problem (an SMT-LIB file) into Lean declarations and a goal; the translation is in `Bench/` and is not part of the subject of this text, but its output determines the shape of every goal that `xsearch` receives, so the relevant conventions are recalled here.

An inductive predicate `p` with parameters `a b` is defined as `lfp F (a, b)`, where `F : (α → HProp) → α → HProp` is a monotone functional and `lfp` is the least fixed point in the lattice of heap predicates, defined impredicatively in `Bench/Fixpoint.lean`:

```lean
def lfp {α : Type} (F : (α → HProp) → α → HProp) : α → HProp :=
  fun a h => ∀ X : α → HProp, (∀ b, F X b ==> X b) → X a h
```

Every predicate comes with an unfold equation, proved from `lfp_unfold` and the monotonicity proof of `F`, and registered with the attribute `@[xsearch_unfold]`. The following definition of an acyclic list segment is taken from `Sep/Tests/XsearchTests.lean`; it has the same form as the translations of SL-COMP problems.

```lean
def f_ls (X : Nat × Nat → HProp) (p : Nat × Nat) : HProp :=
  hor (⌈p.1 = p.2⌉ ✶ emp)
    (∃✶ u : Nat, ⌈p.1 ≠ p.2⌉ ✶ (⌈p.1 ≠ 0⌉ ✶ p.1 ↦ (u : Int)) ✶ X (u, p.2))

theorem m_ls : Mono f_ls := by
  intro X Y hXY a
  apply hor_mono (himpl_refl _)
  apply himpl_hexists; intro u
  exact himpl_frame_r (himpl_frame_r (hXY _))

def p_ls (a b : Nat) : HProp := lfp f_ls (a, b)

@[xsearch_unfold] theorem e_ls (a b : Nat) :
    p_ls a b = hor (⌈a = b⌉ ✶ emp) (∃✶ u : Nat, ⌈a ≠ b⌉ ✶ (⌈a ≠ 0⌉ ✶ a ↦ (u : Int)) ✶ p_ls u b) :=
  congrFun (lfp_unfold f_ls m_ls) (a, b)
```

Four conventions of the translation are visible here and recur throughout.

1. A disjunction of heap assertions is written `hor H1 H2`, a pointwise disjunction defined in the benchmark library. `xsearch` recognises it by the last component of its constant name and converts it to its own copy `hdisj` when it needs to reason about it.
2. Locations are natural numbers. A record with fields `f₀, …, f_{m-1}` stored at `x` becomes the cells `x ↦ f₀ ✶ (x + 1) ↦ f₁ ✶ … ✶ (x + m - 1) ↦ f_{m-1}`, preceded by the guard `⌈x ≠ 0⌉`. The two-field cell of a doubly linked list at `x` with successor `n` and predecessor `p` is therefore `⌈x ≠ 0⌉ ✶ x ↦ n ✶ (x + 1) ↦ p`.
3. Integer-valued parameters (lengths, data) have type `Int`; location-valued parameters have type `Nat`. A location stored in a cell is cast into `Int`.
4. Mutually recursive predicates are defined as one least fixed point over a sum type: the argument of the group's functional is `Sum.inl (a, b)` for the first member, `Sum.inr (Sum.inl (a, b))` for the second, and so on.

A goal is a closed entailment over universally quantified variables, for example

```lean
example (x y z : Nat) :
    ⌈x ≠ 0⌉ ✶ x ↦ (y : Int) ✶ ⌈y ≠ 0⌉ ✶ y ↦ (z : Int) ✶ ⌈z ≠ 0⌉ ✶ z ↦ (0 : Int) ==> p_ls x 0 := by
  xsearch

example (x y : Nat) : p_ls x y ✶ p_ls y 0 ==> p_ls x 0 := by
  xsearch
```

The second example, `p_ls x y ✶ p_ls y 0 ==> p_ls x 0`, is the composition of two segments into one. It is valid because the second segment ends at nil: every cell of the first segment is allocated, so none of its addresses equals `0`, and the guard `⌈a ≠ b⌉` of each unfolded cell of the composite segment holds. The similar entailment `p_ls x y ✶ p_ls y z ==> p_ls x z` is not valid: with `x = z` the left-hand side describes a cycle through `x` and `y`, while `p_ls x x` holds only of the empty heap. These two entailments are the first running examples of this text. Others are `⌈x ≠ 0⌉ ✶ x ↦ y ✶ p_ls y 0 ==> p_ls x 0` (folding one cell into a segment; the guard is needed because location `0` is an ordinary location of the model and may be allocated) and the two-cell doubly linked list, whose definition in the benchmark reads

```
(define-fun-rec dll ((hd_1 Refnode) (p_2 Refnode) (tl_3 Refnode) (n_4 Refnode) (len_5 Int)) Bool
  (or
   (and
    (pto hd_1 (c_node n_4 p_2))
    (and
     (= (- len_5 1) 0)
     (= hd_1 tl_3)))
   (exists
    ((x_6 Refnode) (k Int))
    (and
     (sep
      (pto hd_1 (c_node x_6 p_2))
      (dll x_6 hd_1 tl_3 n_4 k))
     (= k (- len_5 1))
     (<= 1 (- len_5 1))))))
```

(the file is `sl-comp-bench/shidlia_entl/dll_len_get_2_hd_3_lasts.sb.smt2`). In Lean the base branch becomes the star of `⌈hd ≠ 0⌉`, `hd ↦ n`, `(hd + 1) ↦ p` and the pure facts `⌈len - 1 = 0⌉` and `⌈hd = tl⌉` (locations stored in cells are cast into `Int`). A two-cell list from `a` to `b` with predecessor `p` of `a` and successor `n` of `b` is the heap `a ↦ b ✶ (a + 1) ↦ p ✶ b ↦ n ✶ (b + 1) ↦ a`, together with the guards `⌈a ≠ 0⌉` and `⌈b ≠ 0⌉`; it satisfies `dll a p b n 2`.

The benchmark divisions covered by the current code are `qf_shls_entl`, `qf_shid_entl`, `qf_shlid_entl`, `qf_shidlia_entl`, `shid_entl`, `shidlia_entl` and `onprob_qf_shid_entl`: 798 problems labelled valid, of which 10 were found to be mislabelled. All 788 genuinely valid problems are proved. The satisfiability divisions are out of scope. A problem that `xsearch` cannot prove makes the tactic fail; the tactic never proves the negation of an entailment. When this text says that a goal is *refuted*, it means that a check has shown the goal invalid and the tactic stops working on it.

### 1.2 The files

The development consists of five files, presented in this order.

| File | Lines | Content |
|---|---|---|
| `Sep/SepLogic.lean` | 194 | The class `SepLogic` of separation logics and the lemmas `xsimpl` needs about it. |
| `Sep/Xsimpl/Core.lean` | 2102 | The `xsimpl` driver, generic over `SepLogic`, with its own certificate lemmas. |
| `Sep/Xsimpl.lean` | 99 | The `SepLogic` instance for `HProp` and the lemmas that translate between the two vocabularies. |
| `Sep/SegC.lean` | 2283 | The segment carrier `wseg` and every theorem `xsearch` instantiates. |
| `Sep/Xsearch.lean` | 9976 | The tactic `xsearch`. It contains no theorems. |

`Sep/HProp.lean` (959 lines) defines the model and is used but not presented.

### 1.3 The pipeline

The entry point is the macro `xsearch` at the end of `Sep/Xsearch.lean`:

```lean
syntax "xsearch" : tactic
macro_rules
  | `(tactic| xsearch) => `(tactic| xsearch_scope (
      xsearch_refute
      xsearch_cmodel
      xsearch_start
      first
      | (xsimpl_core
         all_goals (try xsimpl_clean)
         xsearch_pure
         done)
      | (try xsearch_eqsubst
         try xsearch_trivpure
         try xsearch_macros
         try xsearch_trivpure
         try xsearch_pfacts
         try xsearch_facts
         first
         | done
         | (xsearch_wseg
            first
            | done
            | xsearch_backtrack)
         | xsearch_wit
         | xsearch_backtrack
         | xsearch_wit cases)))
```

Read from top to bottom, the tactic does the following. A later chapter is devoted to each stage; this list only names them.

1. `xsearch_scope` sets the problem's time budget and runs the rest with information trees disabled.
2. `xsearch_refute` fails at once if the right-hand side mentions, at an address or predicate argument position, a variable that the left-hand side does not mention.
3. `xsearch_cmodel` searches for a countermodel (a concrete heap satisfying the left-hand side and not the right-hand side) and fails if it finds one. This is the only time the full countermodel search runs on the input goal; later, only goals derived by the witness search are checked in the same way.
4. `xsearch_start` resets the per-problem caches.
5. The fast path runs `xsimpl_core`, cleans the residual goals and discharges pure side conditions. If no goal remains, the proof is finished.
6. Otherwise the prefix normalisation runs on the original goal: substitution of pure equalities (`xsearch_eqsubst`), removal of trivial pure facts (`xsearch_trivpure`), unfolding of non-recursive predicates with a forced-determination rule for the right-hand side (`xsearch_macros`), and the introduction of pure facts (`xsearch_pfacts`) and of disequalities between allocated cells (`xsearch_facts`).
7. The segment engine `xsearch_wseg` abstracts every predicate atom into one generic segment, the carrier `wseg`, plans how the left-hand segments compose into the right-hand ones, and executes the plan by instantiating theorems of `Sep/SegC.lean`. If it leaves a goal, the backtracking core gets that goal.
8. If the engine fails, the witness search `xsearch_wit` chooses values for the right-hand existentials and runs the fast path, the engine and the core on each choice.
9. If that fails, the backtracking core `xsearch_backtrack` runs on the normalised goal: a depth-first search over unfoldings, disjunct choices, wand applications and inductions, with one induction mechanism `indCore` and a depth-zero countermodel check at every node.
10. Last, `xsearch_wit cases` repeats the witness search with an arithmetic case split.

### 1.4 Three goals through the pipeline

Before the stages are presented one by one, this section shows which stage decides each of three small goals.

The goal `⌈x ≠ 0⌉ ✶ x ↦ y ==> ∃✶ u, x ↦ u ✶ ⌈x ≠ 0⌉` passes the refutation test (every right-hand address occurs on the left), and the countermodel search finds no heap that satisfies the left-hand side and falsifies the right-hand side. The fast path then proves it: `xsimpl` cancels the cell, choosing `u := y`, and the remaining side condition `x ≠ 0` is a hypothesis. Nothing else runs.

The goal `p_ls x y ✶ p_ls y 0 ==> p_ls x 0` passes the same tests. The fast path fails, because the two sides have no atom in common. The prefix normalisation changes nothing. The segment engine abstracts both left-hand atoms into segments of one carrier, plans to join them into one segment from `x` to `0`, executes the join, and folds the result into `p_ls x 0`. The witness search and the backtracking core do not run.

The goal `p_ls x y ✶ p_ls y z ==> p_ls x z` is refuted by the countermodel search: the heap `{2 ↦ 3, 3 ↦ 2}` with `x = z = 2` and `y = 3` satisfies the left-hand side but not the right-hand side. The tactic fails after a few milliseconds without any search.

### 1.5 The design rules

The present form of the code is the result of a series of measured steps recorded in the ledgers `ledgers/work-ledger-climb.md` and `ledgers/work-ledger-climb2.md`. During the second climb the user fixed rules that the end state satisfies. They explain many features of the code that would otherwise appear arbitrary, so they are stated here and referred to later.

1. **One mechanism per task.** There is one segment engine, one witness search, one backtracking core with one induction mechanism, one lemma builder over one theorem family, one reader of predicate definitions, one pure prover, one permutation prover, one allocation prover and one countermodel. There are no special cases per predicate shape.
2. **Nothing names a predicate.** All knowledge about predicates is derived from their unfold equations. The code names the constants of the model (`HProp.hstar`, `HProp.hsingle`, …), its own library (`hdisj`, `wseg`, …), and the benchmark's `hor`, `lfp`, `lfp_unfold` and `lfp_pre`, but no predicate.
3. **No tuned constants.** Every bound is derived from the goal or from the remaining time. Exactly three numeric literals are tied to the clock: `hbPerVms`, `problemVms` and `cmVms`.
4. **Separation logic only.** The theory automated is separation logic. Linear arithmetic residues are delegated to `omega` with a trimmed context; there is no arithmetic reasoning specific to a background theory.
5. **Theorems live in `SegC`.** `Sep/Xsearch.lean` contains no theorems. Proof terms are built by instantiating the theorems of `Sep/SegC.lean` (and `xsimpl`'s own lemma section).
6. **Deterministic time.** Every time budget reads a virtual clock derived from `IO.getNumHeartbeats`, so runs are reproducible on any machine.

Two further rules from the first climb remain in force: the interface of `xsimpl` is kept stable (it is sped up internally, not duplicated by a parallel normaliser), and the code contains no `sorry`, axioms, `native_decide`, `unsafe`, comments or docstrings.

### 1.6 Plan of the text

Chapter 2 presents the class `SepLogic` and its `HProp` instance. Chapter 3 presents `xsimpl`, which every later stage calls. Chapter 4 presents the theory of the segment carrier, whose theorems the segment engine instantiates. Chapters 5 to 12 follow `Sep/Xsearch.lean` along the pipeline: the entry point, the clock and the refutation test, the countermodel, the shared provers (which the remaining stages call), the cache reset and the fast path, the rest of the prefix normalisation, the segment engine, the witness search and the backtracking core. The order of these chapters is the order in which the macro runs the stages; in particular, the fast path runs directly after `xsearch_start` and before the substitution, trivial-fact, macro and fact steps of the prefix normalisation. Chapter 13 summarises what was measured and rejected and what remains open.

## 2. The Class `SepLogic` and the `HProp` Instance

### 2.1 Why a class

`xsimpl` has clients other than `xsearch`: `FrameInference.lean` and the examples under `Sep/Examples`, among them a Hoare logic and a symbolic executor. `Reordering.lean` and `GrwSepLogic.lean` use the class below directly. The tactic is written against an abstract interface, the class `SepLogic` in `Sep/SepLogic.lean`, so that it depends on no particular model; the only instance in the repository is the one for `HProp` (which `GrwHProp.lean` re-exports at a second universe level). The class fixes the operations a symbolic heap is built from and exactly the laws that `xsimpl` uses:

```lean
class SepLogic (α : Type u) where
  /-- Separating conjunction. -/
  star : α → α → α
  /-- The empty resource, the unit of `star`. -/
  emp : α
  /-- Pure propositions. Named `spure` to avoid clashing with `Monad.pure`. -/
  spure : Prop → α
  /-- Existential quantification. -/
  ex : {A : Sort v} → (A → α) → α
  /-- Separating implication. -/
  wand : α → α → α
  /-- Entailment. -/
  Entails : α → α → Prop
  star_comm : ∀ H1 H2, star H1 H2 = star H2 H1
  star_assoc : ∀ H1 H2 H3, star (star H1 H2) H3 = star H1 (star H2 H3)
  star_emp_l : ∀ H, star emp H = H
  star_emp_r : ∀ H, star H emp = H
  star_ex : ∀ {A : Sort v} (J : A → α) (H : α),
    star (ex J) H = ex (fun x => star (J x) H)
  entails_refl : ∀ H, Entails H H
  entails_trans : ∀ {H1 H2 H3}, Entails H1 H2 → Entails H2 H3 → Entails H1 H3
  entails_antisym : ∀ {H1 H2}, Entails H1 H2 → Entails H2 H1 → H1 = H2
  frame_r : ∀ {H P1 P2}, Entails P1 P2 → Entails (star H P1) (star H P2)
  frame_l : ∀ {H P1 P2}, Entails P1 P2 → Entails (star P1 H) (star P2 H)
  ex_l : ∀ {A : Sort v} {J : A → α} {H}, (∀ x, Entails (J x) H) → Entails (ex J) H
  ex_r : ∀ {A : Sort v} (x : A) {J : A → α} {H}, Entails H (J x) → Entails H (ex J)
  pure_l : ∀ {P : Prop} {H1 H2}, (P → Entails H1 H2) → Entails (star (spure P) H1) H2
  pure_r : ∀ {P : Prop} {H1 H2}, P → Entails H1 H2 → Entails H1 (star (spure P) H2)
  wand_cancel : ∀ H1 H2, Entails (star H1 (wand H1 H2)) H2
  wand_intro : ∀ {H1 P1 P2}, Entails (star H1 P1) P2 → Entails H1 (wand P1 P2)
  wand_curry : ∀ H1 H2 H3, wand (star H1 H2) H3 = wand H1 (wand H2 H3)
```

The second universe parameter `v` of the class is the universe of the binder types of `ex`. A logic whose existentials range over `Prop` as well as over data therefore has instances at several universe levels, and `xsimpl` must find the instance that matches the binder type of each existential it handles (Section 3.3).

`AffineSepLogic` extends the class with the law `entails_emp : ∀ H, Entails H emp`; with it `xsimpl` may discard leftover resources. `HProp` is not affine, so this extension plays no role in `xsearch`.

The class lemmas proved in `Sep/SepLogic.lean` are small consequences of the laws: `hstar_left_comm`, the rewriting lemmas `himpl_lhs_eq`/`himpl_rhs_eq`, extraction and instantiation helpers (`himpl_hexists_l_star`, `himpl_hpure_l`, `himpl_hexists_r_star`, `himpl_hpure_r`), cancellation helpers (`himpl_cancel_lhs`, `himpl_cancel_rhs`), wand application (`himpl_wand_apply_lhs`, `himpl_wand_apply_lhs_emp`), and the identities `hstar_hpure_eq_hexists` that view a pure fact as an existential over its proof. Most of them serve the older single-step tactics of Section 3.11; the native driver uses its own lemma section in `Sep/Xsimpl/Core.lean` instead. Their statements are:

```lean
theorem hstar_left_comm (H1 H2 H3 : α) :
    H1 ∗ (H2 ∗ H3) = H2 ∗ (H1 ∗ H3) := by
…
theorem himpl_lhs_eq {H1 H2 Hr : α} :
    H1 = H2 → (H2 ==> Hr) → (H1 ==> Hr) := by
…
theorem himpl_rhs_eq {Hl H1 H2 : α} :
    H1 = H2 → (Hl ==> H1) → (Hl ==> H2) := by
…
theorem himpl_hexists_l_star {A : Sort v} {J : A → α} {H1 H2 : α} :
    (∀ x, J x ∗ H1 ==> H2) → (ex J ∗ H1 ==> H2) := by
…
theorem himpl_hpure_l {P : Prop} {H : α} :
    (P → (emp : α) ==> H) → (⌜P⌝ ==> H) := by
…
theorem himpl_hexists_r_star {A : Sort v} (x : A) {H1 H2 : α} {J : A → α} :
    (H1 ==> J x ∗ H2) → (H1 ==> ex J ∗ H2) := by
…
theorem himpl_hpure_r {P : Prop} {H : α} :
    P → (H ==> (emp : α)) → (H ==> ⌜P⌝) := by
…
theorem himpl_cancel_rhs {H1 H2 : α} :
    ((emp : α) ==> H2) → (H1 ==> H1 ∗ H2) := by
…
theorem himpl_cancel_lhs {H1 H2 : α} :
    (H2 ==> (emp : α)) → (H1 ∗ H2 ==> H1) := by
…
theorem himpl_wand_apply_lhs {H1 H2 Hl Hr : α} :
    (H2 ∗ Hl ==> Hr) → (H1 ∗ ((H1 -∗ H2) ∗ Hl) ==> Hr) := by
…
theorem himpl_wand_apply_lhs_emp {H1 H2 Hr : α} :
    (H2 ==> Hr) → (H1 ∗ (H1 -∗ H2) ==> Hr) :=
…
theorem hstar_hpure_eq_hexists (P : Prop) (H : α) :
    ⌜P⌝ ∗ H = ex (fun _ : P => H) := by
```

The class also introduces scoped notation (`∗`, `-∗`, `==>`, `emp`, `⌜P⌝`, `∃ₛ`). This notation is distinct from the `HProp` notation of the prerequisites; where this text writes class terms it uses the class notation.

### 2.2 The `HProp` instance

`Sep/Xsimpl.lean` provides the instance. Every operation is the corresponding `HProp` constant and every law is the corresponding theorem of `Sep/HProp.lean`:

```lean
instance instSepLogicHProp : SepLogic HProp where
  star := HProp.hstar
  emp := HProp.hempty
  spure := HProp.hpure
  ex := HProp.hexists
  wand := HProp.hwand
  Entails := HProp.himpl
  star_comm := HProp.hstar_comm
  star_assoc := HProp.hstar_assoc
  star_emp_l := HProp.hstar_hempty_l
  star_emp_r := HProp.hstar_hempty_r
  star_ex := HProp.hstar_hexists
  entails_refl := HProp.himpl_refl
  entails_trans := HProp.himpl_trans
  entails_antisym := HProp.himpl_antisym
  frame_r := HProp.himpl_frame_r
  frame_l := HProp.himpl_frame_l
  ex_l := HProp.himpl_hexists_l
  ex_r := fun {_A} x {_J _H} h => HProp.himpl_hexists_r x h
  pure_l := HProp.himpl_hstar_hpure_l
  pure_r := HProp.himpl_hstar_hpure_r
  wand_cancel := HProp.hwand_cancel
  wand_intro := fun {H1 P1 _P2} h =>
    HProp.himpl_hwand_r (by rw [HProp.hstar_comm P1 H1]; exact h)
  wand_curry := HProp.hwand_curry_eq
```

Because the instance fields are the `HProp` constants themselves, a class term such as `SepLogic.star H1 H2` at this instance is definitionally equal to `HProp.hstar H1 H2`, and a proof of a class entailment at this instance type-checks as a proof of the corresponding `HProp` entailment. This observation is the basis of the native driver: it never rewrites an `HProp` goal into class form; it reads the goal in its concrete constants and emits proof terms built from class lemmas, which the kernel accepts against the concrete goal by unfolding the instance.

The file also contains two families of `rfl` lemmas. The lemmas tagged `@[xsimpl_fold]` state `HProp.hstar H1 H2 = SepLogic.star H1 H2`, `HProp.hempty = SepLogic.emp`, and so on for `hpure`, `hexists`, `hwand` and `himpl`. The lemmas tagged `@[xsimpl_unfold_class]` state the reverse equations. The driver does not rewrite with the fold lemmas; it reads them as data, to learn which concrete constant plays which role and in which argument positions the operands occur (Section 3.2). The unfold lemmas are used to bring a goal written in class notation back to concrete constants. Finally, `parseHstar` splits a star chain written in either vocabulary into its list of conjuncts; `xsearch` uses it in many places.

## 3. `xsimpl`

### 3.1 The interface

`xsimpl` takes a goal `L ==> R` and returns a list of goals. Its contract, which every later chapter relies on, is the following.

- Existentials and pure facts of `L` are introduced into the local context, as new variables and hypotheses.
- Existentials of `R` are replaced by fresh metavariables. Pure facts of `R` become separate goals (one goal of type `P` for each `⌈P⌉`), or are solved at once when `P` is `True`.
- An atom of `L` and an atom of `R` that are definitionally equal cancel. Cancellation may assign the metavariables created for existentials of `R`; the first atom of `L` (in left-to-right order) that unifies with a given atom of `R` is taken. This first-fit choice is a decision about witnesses; Chapters 11 and 12 return to its consequences.
- Wands are handled: a right-hand side that is a single wand `A -✶ B` is introduced (the goal becomes `L ✶ A ==> B`), a left-hand wand `A -✶ B` whose antecedent `A` occurs on the left is applied, and a right-hand `A -✶ A` is removed.
- What remains is a residual entailment between the uncancelled atoms, plus the side goals. A goal that `xsimpl` cannot read at all is returned unchanged.

The tactic `xsimpl` is the composition of `xsimpl_core`, which performs these steps, with `xsimpl_clean` applied to every resulting goal:

```lean
syntax "xsimpl" : tactic
macro_rules
  | `(tactic| xsimpl) => `(tactic| (
      xsimpl_core
      all_goals (
        try xsimpl_clean
      )
    ))
```

`xsimpl_clean` closes a goal by definitional reflexivity of its two sides, by an assumption in the local context, or, in an affine logic, by discarding the left-hand side against `emp`.

### 3.2 Recognising the logic

A goal arrives in the concrete constants of some logic. The driver must determine which constants are the star, the empty heap, the pure embedding, the existential, the wand and the entailment, and where their operands occur among the arguments. This information is recorded in two structures:

```lean
structure NOp where
  name : Name
  arity : Nat
  pos : Array Nat
  deriving Inhabited, BEq
…
structure NCtx where
  carrier : Expr
  u : Level
  entOp : NOp
  starOp : NOp
  empOp : NOp
  pureOp : NOp
  exOp : NOp
  wandOp : Option NOp
  starFn : Expr
  starArgs : Array Expr
  empE : Expr
  entFn : Expr
  entArgs : Array Expr
  lv0 : Level
  inst0 : Expr
  deriving Inhabited
```

An `NOp` describes one concrete operation: its constant name, its arity, and the positions of its operands among the arguments. `foldEntry` derives an `NOp` from a fold lemma: in `HProp.hstar H1 H2 = SepLogic.star H1 H2` the operands of the class operation are found in the arguments of the left-hand side, which gives their positions. `foldEntries` collects these for every lemma tagged `xsimpl_fold`, cached against the list of lemma names.

An `NCtx` describes one logic at one carrier type. Besides the six operations it stores a template (function and fixed arguments) for building stars and entailments, the expression for `emp`, and the default instance `inst0` at universe level `lv0` (0, or 1 if no instance exists at 0). `buildNCtx` assembles it from the fold entries whose left-hand side has the goal's carrier type; `nctxFor?` caches the result per carrier and module. Two fallbacks complete the recognition, both in `sepGoal?`: a goal containing class operations is first rewritten with the `xsimpl_unfold_class` lemmas (by a rewriting procedure, `rewriteWithRfl`, that matches definitionally equal sides, which `simp` cannot do with `rfl` lemmas of this kind), and a goal stated over an abstract carrier with no concrete constants is read by `classNCtx?`, which builds an `NCtx` whose operations are the class projections themselves.

Every proof step is a class lemma applied at the carrier and an instance: `NCtx.lem` applies a lemma at `inst0`, `NCtx.lemAt` at an instance of another level.

### 3.3 The fragment check

Before doing anything, `nativeGoal` checks both sides with `spine`, which walks the star structure and returns `none` if it meets something it cannot handle. The accumulator `SpineAcc` records the universe levels of existential binder types, whether the right-hand side has an existential, and whether an existential over a non-propositional type occurs nested inside another heap assertion. An atom is acceptable if it mentions none of the logic's operations; an atom whose arguments are themselves heap assertions (for example a predicate applied to a heap assertion, or a wand) is acceptable if those arguments pass the same check (`atomCheck`, `nestedSide`). Such nested assertions are normalised in place by congruence (Section 3.4). If the check fails, the goal is returned unchanged.

For each recorded level, `sepInstAt` synthesises the `SepLogic` instance at that level once per module. Existentials over `Prop` (level 0) and over data types (level 1 and above) thus use different instances; the flag `typeEx` records whether any existential over a non-propositional type is present, because the order of extraction below depends on it.

### 3.4 Flattening

The driver works on lists of conjuncts. `NCtx.flat` turns a star tree into a list, reassociating to the right with `nt_assoc` and removing `emp` with `nt_empl`/`nt_empr`, and returns the list with an optional equality proof (no proof when the tree was already a right-nested chain). `NCtx.starL` rebuilds the right-nested chain from a list. `flatN` additionally normalises conjuncts that contain nested heap assertions or the trivial fact `⌈a = a⌉` (which becomes `⌈True⌉`): `itemNorm` descends into existential bodies, wand operands and atom arguments, `nestNorm` flattens a nested star and pulls its existentials outward with `combine` (by `nt_eq_exl`/`nt_eq_exr`), and `wandNorm` curries a wand whose antecedent is a star (by `nt_curry`). All of these return equality proofs assembled with `congrArg` and `funext`, so that a normalised side is related to the original by one equation. `flatGoalL` and `flatGoalR` replace a side of the goal by its flattened form and record the equation in the proof. The equations used by flattening are lemmas of the section `NativeLemmas` (Section 3.5), stated in the class notation:

```lean
theorem nt_assoc.{w, z} {α : Type w} [SepLogic.{w, z} α] (a b c : α) :
    (a ∗ b) ∗ c = a ∗ (b ∗ c) :=
…
theorem nt_empl.{w, z} {α : Type w} [SepLogic.{w, z} α] (a : α) : emp ∗ a = a :=
…
theorem nt_empr.{w, z} {α : Type w} [SepLogic.{w, z} α] (a : α) : a ∗ emp = a :=
…
theorem nt_eq_exl.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} (J : A → α) (q : α) :
    ex J ∗ q = ex (fun x => J x ∗ q) :=
…
theorem nt_eq_exr.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} (q : α) (J : A → α) :
    q ∗ ex J = ex (fun x => q ∗ J x) :=
…
theorem nt_curry.{w, z} {α : Type w} [SepLogic.{w, z} α] (a b c : α) :
    (a ∗ b) -∗ c = a -∗ (b -∗ c) :=
```

### 3.5 The certificate lemmas

`Sep/Xsimpl/Core.lean` has its own lemma section, `NativeLemmas`, stated for an arbitrary `SepLogic` instance. Most are one-line restatements of the class laws in the argument order the driver needs (`nt_trans`, `nt_refl`, `nt_of_eq`, `nt_frame`, `nt_comm`, `nt_swap`, `nt_pushl`, `nt_exl`, `nt_exr`, `nt_purel`, `nt_purer`, and the wand lemmas `nt_wand_l`, `nt_wand_r`, `nt_wand_same`):

```lean
theorem nt_trans.{w, z} {α : Type w} [SepLogic.{w, z} α] {a b c : α}
    (h1 : a ==> b) (h2 : b ==> c) : a ==> c :=
…
theorem nt_refl.{w, z} {α : Type w} [SepLogic.{w, z} α] (a : α) : a ==> a :=
…
theorem nt_of_eq.{w, z} {α : Type w} [SepLogic.{w, z} α] {a b : α} (h : a = b) :
    a ==> b := by
…
theorem nt_frame.{w, z} {α : Type w} [SepLogic.{w, z} α] (c : α) {a b : α}
    (h : a ==> b) : c ∗ a ==> c ∗ b :=
…
theorem nt_comm.{w, z} {α : Type w} [SepLogic.{w, z} α] (a b : α) :
    a ∗ b ==> b ∗ a := by
…
theorem nt_swap.{w, z} {α : Type w} [SepLogic.{w, z} α] (a b c : α) :
    a ∗ (b ∗ c) ==> b ∗ (a ∗ c) := by
…
theorem nt_pushl.{w, z} {α : Type w} [SepLogic.{w, z} α] (a b c : α) :
    a ∗ (b ∗ c) ==> (b ∗ a) ∗ c :=
…
theorem nt_exl.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} {J : A → α} {r : α}
    (k : ∀ x, J x ==> r) : ex J ==> r :=
…
theorem nt_exr.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} (x : A) {J : A → α}
    {l : α} (h : l ==> J x) : l ==> ex J :=
…
theorem nt_purel.{w, z} {α : Type w} [SepLogic.{w, z} α] {P : Prop} {q r : α}
    (k : P → q ==> r) : ⌜P⌝ ∗ q ==> r :=
…
theorem nt_purer.{w, z} {α : Type w} [SepLogic.{w, z} α] {P : Prop} {l q : α}
    (p : P) (h : l ==> q) : l ==> ⌜P⌝ ∗ q :=
…
theorem nt_wand_l.{w, z} {α : Type w} [SepLogic.{w, z} α] (a b : α) {l r : α}
    (h : b ∗ l ==> r) : a ∗ ((a -∗ b) ∗ l) ==> r :=
…
theorem nt_wand_r.{w, z} {α : Type w} [SepLogic.{w, z} α] {l a b : α}
    (h : l ∗ a ==> b) : l ==> a -∗ b :=
…
theorem nt_wand_same.{w, z} {α : Type w} [SepLogic.{w, z} α] (a : α) {l r : α}
    (h : l ==> r) : l ==> (a -∗ a) ∗ r :=
```

Two lemmas carry the cancellation step; their statements are:

```lean
inductive PTree.{w} (α : Type w) where
  | leaf : PTree α
  | node : PTree α → α → PTree α → PTree α

noncomputable def ptGet.{w} {α : Type w} (d : α) (t : PTree α) : Nat → α :=
  PTree.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun _ x _ il ir i => cond (Nat.beq i 0) x (cond (Nat.beq (i % 2) 1) (il (i / 2)) (ir (i / 2 - 1)))) t

noncomputable def listStar.{w, z} {α : Type w} [SepLogic.{w, z} α] (xs : List α) : α :=
  List.rec (motive := fun _ => α) emp
    (fun x r ih => List.rec (motive := fun _ => α) x (fun _ _ _ => x ∗ ih) r) xs

noncomputable def starI.{w, z} {α : Type w} [SepLogic.{w, z} α] (env : PTree α) (l : List Nat) : α :=
  listStar (l.map (ptGet emp env))

noncomputable def bitMask (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun i _ ih => (1 <<< i) ||| ih) l

noncomputable def permChk (l r : List Nat) : Bool :=
  Nat.beq l.length r.length && Nat.beq (bitMask l) (2 ^ l.length - 1) && Nat.beq (bitMask r) (2 ^ l.length - 1)
…
theorem nt_perm_idx.{w, z} {α : Type w} [SepLogic.{w, z} α] (env : PTree α) (l r : List Nat)
    (h : permChk l r = true) : starI env l ==> starI env r := by
…
theorem nt_frame_list.{w, z} {α : Type w} [SepLogic.{w, z} α] (cs : List α) {xs ys : List α}
    (h : listStar xs ==> listStar ys) : listStar (cs ++ xs) ==> listStar (cs ++ ys) := by
…
```

A list of atoms is turned into a star chain by `listStar`, which has the same shape as `NCtx.starL`: the empty list gives `emp`, a singleton gives the atom itself, and `x :: r` gives `x ∗ listStar r`. `PTree` is a binary tree of atoms indexed in the Braun order (index 0 at the root, odd indices in the left subtree, even positive indices in the right), and `ptGet d t i` retrieves the atom with index `i`. `starI env l` is the star of the atoms of `env` listed by the indices in `l`. `permChk l r` is a Boolean test: the two index lists have the same length `n`, and the bit mask of each (the bitwise or of `1 <<< i` over its elements) is `2 ^ n - 1`. Together these say that `l` and `r` both enumerate `0, …, n-1` exactly once, so `r` is a permutation of `l`.

`nt_perm_idx env l r h` then states that the star of the atoms in the order `l` entails the star in the order `r`, given the hypothesis `permChk l r = true`. The driver always supplies the hypothesis as `Eq.refl true`; the kernel checks it by evaluating `permChk` on literal lists, which costs arithmetic on natural number literals (accelerated in the kernel) and no proof search. The left-hand side `starI env (List.range n)` unfolds definitionally to the goal's own star chain, so no conversion proof is needed either. `nt_frame_list cs h` frames a list `cs` of atoms onto both sides of an entailment between lists.

### 3.6 Extraction and instantiation

After flattening, `nativeGoal` extracts the left-hand side. `NCtx.pick` selects the next existential or pure conjunct; it scans from the right, because the earlier simp-based implementation produced hypotheses in that order and clients depend on the order and names of hypotheses. When `typeEx` holds, existentials are taken before pure facts, and when in addition the right-hand side has an existential, the pure facts are then taken from the left end of the list. `lhsRec` builds, in one recursive pass, a single proof term for the whole extraction: for an existential at position `i` it rotates the existential to the outside with `nt_exl_base` and `nt_exl_layer`, applies `nt_exl`, and continues under a new local variable; for a pure fact it pulls the fact to the front with `pullL` and applies `nt_purel`. When there are no existentials but at least two pure facts, `pureBlockPf` first moves all pure facts to the front as one block, so that they are introduced together by `peelPures`. The recursion ends in one fresh metavariable whose type quantifies over all the introduced variables; `lhsBatch` assigns the proof term and introduces all variables and hypotheses with one `introN`. Step T6 of the first climb introduced this single introduction; introducing the names one at a time had made the instantiation of metavariables in the final proof term costly. The rotation lemmas, used here for the left-hand side and below for the right-hand side, are:

```lean
theorem nt_exl_base.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} (J : A → α)
    (q : α) : ex J ∗ q ==> ex (fun x => J x ∗ q) := by
…
theorem nt_exl_layer.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} {K : A → α}
    {x : α} (s : α) (h : x ==> ex K) : s ∗ x ==> ex (fun y => s ∗ K y) :=
…
theorem nt_exr_base.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} (J : A → α)
    (q : α) : ex (fun x => J x ∗ q) ==> ex J ∗ q := by
…
theorem nt_exr_layer.{w, z} {α : Type w} [SepLogic.{w, z} α] {A : Sort z} {K : A → α}
    {x : α} (s : α) (h : ex K ==> x) : ex (fun y => s ∗ K y) ==> s ∗ x :=
```

The right-hand side is then processed by `rhsStep`, repeatedly, again choosing conjuncts with `pick`. An existential is rotated outward with `nt_exr_base`/`nt_exr_layer`, and `nt_exr` is applied with a fresh metavariable `y` as witness; the body, instantiated with `y`, replaces it. A pure fact `⌈P⌉` is removed with `nt_purer` and a fresh metavariable `q : P`, which becomes a side goal. The metavariables created here are recorded in the array `created`.

### 3.7 Cancellation

`cancelScan` computes which atoms cancel. When no atom on either side contains a metavariable, it first pairs syntactically equal atoms through a hash map, which is linear in the number of atoms. The remaining atoms are scanned in the order of the right-hand side; for each, the first live left-hand atom that is definitionally equal (by `cheapDefEq`) is paired with it. When an atom contains metavariables, this check is unification and may assign them. The result is a list of pairs, the surviving left-hand atoms and the surviving right-hand atoms.

`cancelStep` turns the pairing into a proof. Let `sa` be the left-hand atoms, `ta` the right-hand atoms, `cl` and `cr` the cancelled atoms in pairing order, and `sr`, `tr` the survivors. The proof of `starL sa ==> starL ta` is the composition of three steps:

1. `nt_perm_idx` with the index list "indices of `cl`, then indices of `sr`", which reorders `sa` into `cl ++ sr`;
2. `nt_frame_list cl`, applied to a fresh goal `starL sr ==> starL tr`, which yields `listStar (cl ++ sr) ==> listStar (cl ++ tr)`;
3. `nt_perm_idx` over the list `cr ++ tr` with the index list that restores the original order of `ta`.

The kernel identifies `cl` with `cr` because each pair is definitionally equal (after the assignments made by unification). If both survivor lists are empty, the fresh goal is closed by `nt_refl`.

As an example, take `L = A ✶ B ✶ C ✶ D` and `R = C ✶ X ✶ A` with opaque atoms. The hash-map pass pairs `C` with `C` and `A` with `A`, in the order of `R`: `cl = [C, A]`, `sr = [B, D]`, `tr = [X]`. The left permutation is `[2, 0, 1, 3]`, giving `C ✶ A ✶ B ✶ D`; the framing leaves the residual goal `B ✶ D ==> X`; the right permutation over `[C, A, X]` is `[0, 2, 1]`, giving `C ✶ X ✶ A`. The proof has a size linear in the number of atoms; the kernel's lookups in the Braun tree cost a logarithmic factor.

This construction is the result of step T1 of the second climb. Before it, cancellation built a chain of frame and swap lemmas with one restatement of the whole star per cancelled atom, about `3n²` term nodes for `n` atoms, and the instantiation and sharing of that term cost as much as the tactic. The benchmark files `Bench/Yolo/Cancel100` to `Cancel800`, which are pure permutations of opaque atoms, took 0.34, 1.7, 5.3 and 12.4 s for 100 to 400 atoms, and the larger ones exhausted 7 GB of memory. With the reflected certificate all eight take between 0.14 and 0.60 s. An earlier attempt at a reflective proof (during the consolidation of the second climb) had cost 13 s of kernel time; the difference is that `ptGet` recurses on natural number literals through `Nat.beq`, `i % 2` and `i / 2`, which the kernel evaluates directly, and that `listStar` unfolds into the goal's own shape.

### 3.8 Residuals and wands

Several shortcuts close or simplify goals before or after cancellation.

- `wholeEq` closes the goal at once if the two sides, before flattening and without metavariables, are definitionally equal.
- `permClose` handles a goal whose sides contain existentials or pure facts and are, as lists of conjuncts, a permutation of each other: it closes the goal by one cancellation without opening any binder.
- `residualEq` closes the residual goal after cancellation if its two sides are definitionally equal, but allows the check to assign only the metavariables created by this run of `xsimpl`; metavariables owned by the caller (for example frame metavariables of a client tactic) must not be assigned by accident.
- A right-hand conjunct `a -✶ a` is removed by `nt_wand_same`.
- If the residual right-hand side is a single wand `A -✶ B`, `nt_wand_r` turns the goal into `L ✶ A ==> B` and `nativeGoal` recurses on it. Otherwise, if the left-hand side has a wand `A -✶ B` and another conjunct definitionally equal to `A`, `nt_wand_l` replaces the two by `B`, and `nativeGoal` recurses.

### 3.9 A complete run

The following goal exercises every phase:

```
(∃✶ v, x ↦ v ✶ ⌈v = 1⌉) ✶ y ↦ 2 ==> ∃✶ w, y ↦ 2 ✶ x ↦ w ✶ ⌈w = 1⌉
```

Here `v` and `w` range over `Int`, a type at universe level 1, so `typeEx` holds.

1. *Recognition.* `sepGoal?` finds the `HProp` entailment through the fold lemmas; `spine` accepts both sides and records level 1 for both existentials, so the instance at level 1 is synthesised.
2. *Shortcuts.* The sides are not definitionally equal (`wholeEq`), and after flattening they have different numbers of conjuncts (`permClose`).
3. *Left-hand extraction.* The flattened left-hand side is `[∃✶ v, x ↦ v ✶ ⌈v = 1⌉, y ↦ 2]`. `pick` selects the existential; `lhsRec` rotates it outward with `nt_exl_base`, giving `∃✶ v, (x ↦ v ✶ ⌈v = 1⌉) ✶ y ↦ 2`, applies `nt_exl`, and continues under a local `v` with the body, flattened to `[x ↦ v, ⌈v = 1⌉, y ↦ 2]`. Because `typeEx` holds and the right-hand side has an existential, pure facts are now taken from the left: `⌈v = 1⌉` is pulled to the front by `pullL` and removed by `nt_purel` under a local hypothesis `a : v = 1`. Nothing remains to extract, and the recursion ends in a metavariable of type `∀ v (a : v = 1), x ↦ v ✶ y ↦ 2 ==> R`. `lhsBatch` assigns the whole proof term and introduces `v` and `a` with one `introN`.
4. *Right-hand instantiation.* `rhsStep` opens the existential with a metavariable `?w` (`nt_exr`), and the body flattens to `[y ↦ 2, x ↦ ?w, ⌈?w = 1⌉]`. The pure conjunct is removed by `nt_purer` with a metavariable `?q : ?w = 1`, which becomes a side goal.
5. *Cancellation.* The left-hand list is `[x ↦ v, y ↦ 2]` and the right-hand list `[y ↦ 2, x ↦ ?w]`. Because `?w` occurs, the hash-map pass is skipped. In right-hand order, `y ↦ 2` pairs with the left-hand `y ↦ 2`, and `x ↦ ?w` unifies with `x ↦ v`, assigning `?w := v`. Both survivor lists are empty, so the framed goal is closed by `nt_refl`, and the two permutations are `[1, 0]` on the left and `[0, 1]` on the right (the identity, for which `permIdx` produces no step).
6. *Result.* The only remaining goal is the side goal `v = 1`, which `xsimpl_clean` closes with the hypothesis `a`.

### 3.10 The driver

The function `nativeGoal` performs the steps of Sections 3.3 to 3.8 in the order given and returns the list of remaining goals: the pure side goals, the residual goal (or the goals of the recursive call after a wand step), and the metavariables created for right-hand existentials that remained unassigned. It returns `some [g]` if it changed nothing. `nativeOrNone` wraps it and restores the state if it throws. The driver applies it to every goal:

```lean
mutual

partial def driveOne (extra : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) (g : MVarId) :
    TacticM (List MVarId) := do
  if ← g.isAssigned then return []
  withExtra extra ((← nativeOrNone g).getD [g])

partial def withExtra (extra : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
    (hs : List MVarId) : TacticM (List MVarId) := do
  match extra with
  | none => return hs
  | some e =>
    let mut out : List MVarId := []
    for h in hs do
      if ← h.isAssigned then continue
      setGoals [h]
      if ← tryTactic (evalTactic e) then
        for h2 in ← getUnsolvedGoals do
          out := out ++ (← driveOne extra h2)
      else
        out := out ++ [h]
    return out

end

def xsimplDriver (extra : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : TacticM Unit := do
  let mut out : List MVarId := []
  for g in ← getGoals do
    out := out ++ (← driveOne extra g)
  setGoals out
```

The optional `extra` tactic, available as `xsimpl_core_with`, is run on each goal the driver leaves, and the driver recurses on what it produces; clients use it to supply domain-specific steps. `xsearch` always uses `xsimplDriver none`.

### 3.11 Cheap cancellation and legacy steps

The reference `cheapCancel` selects a cheaper definitional equality for cancellation. When it is set and neither atom has metavariables, `cheapDefEq` compares atoms with reducible transparency, and `cancelScan` skips pairs whose head constants differ and are not reducible. Without this, checking whether `p_ls x y` and `p_dll x y z w` are equal may unfold both least fixed points. `xsearch_scope` sets the flag when the goal contains a predicate atom; outside `xsearch`, full transparency remains, because the examples under `Sep/Examples` rely on definitional unfolding during cancellation.

The single-step tactics `xsimpl_cancel_all`, `xsimpl_cancel_wand`, `xsimpl_instantiate_step`, `xsimpl_extract_step`, `xsimpl_wand_intro`, the combinator `xsimpl_step` and `xsimpl_normalize` operate by folding the goal into class notation, applying one class lemma, and unfolding again (`xsimpl_in_class`, `changeWithRfl`, `uniformizeInstances`). They are kept because examples use them. They are not used by `xsimpl` or `xsearch`.

### 3.12 History

`xsimpl` was originally a loop of such single steps over class-folded goals, normalised by `simp`. Steps T3 and T5 of the first climb replaced it by the native driver described here, which reads the concrete logic from the fold lemmas and builds proof terms directly; a profile taken before these steps attributed 96 s of 191 s of instrumented run time over the two original divisions to `xsimpl` (of which 38 s were `simp` normalisation, mostly rebuilding the simp set from syntax on every call); after T3 the driver accounted for about 4 s, and T5 deleted the folded path. Step T1 of the second climb replaced the frame-chain cancellation proof by the reflected permutation certificate.

## 4. The Segment Carrier and Its Theory

`Sep/SegC.lean` contains every theorem that `xsearch` instantiates. The segment engine of Chapter 10 reasons about one generic kind of segment, the *carrier* `wseg`, and relates every user predicate to it by two theorems instantiated per predicate: an abstraction (`P xs ==> ∃ k, wseg … ✶ ⌈condition on k⌉`) and a concretisation (`wseg … ✶ ⌈condition on k⌉ ==> P xs`). The two general results from which all abstractions and concretisations are derived are `gAbs` and `gConc`; they are the only two inductions over predicates in the file. Everything else is either a property of the carrier, a corollary that fixes some arguments of `gAbs` or `gConc`, or a small lemma about the logical vocabulary that `xsearch` uses in proof terms. This chapter presents the carrier, then `gAbs` and `gConc`, then the corollaries, then the vocabulary.

### 4.1 The carrier `wseg`

```lean
def wseg {σ : Type} (c : σ → σ → Int → HProp) : Nat → Int → σ → σ → HProp
  | 0, n, s, t => ⌈s = t ∧ n = 0⌉
  | k + 1, n, s, t => ∃✶ s', ∃✶ w, c s s' w ✶ wseg c k (n - w) s' t
```

`wseg c k n s t` is a path of `k` steps from the state `s` to the state `t`. The type `σ` of states is arbitrary. Each step from a state `s` to a successor state `s'` is described by the *cell relation* `c s s' w`, a heap assertion that owns the step's part of the heap and may carry pure facts relating `s` and `s'`; the integer `w` is the step's *weight*, and `n` is the sum of the weights along the path. The base case requires `s = t` and `n = 0`. The step count `k` and the total weight `n` are kept apart because many predicates have a length parameter that counts something other than steps: a tree segment whose size parameter counts the nodes of off-path subtrees, for instance, has steps of varying weight.

The list segment `p_ls a b` of Section 1.1 becomes a carrier as follows. Its recursive call `p_ls u b` changes the first argument and keeps the second; the first argument is therefore a *moving* component of the state. The second argument would be a fixed parameter, except that the guard `⌈a ≠ b⌉` in every cell mentions it; it is therefore carried along in the state as a *constant* component that every step preserves. The state type is `Nat × Nat`, and the cell relation derived by `xsearch` (written here in the notation of this text) is

```
c s s' w = ∃ u, ⌈s.1 ≠ s.2⌉ ✶ ⌈s.1 ≠ 0⌉ ✶ s.1 ↦ u ✶ ⌈s'.1 = u ∧ s'.2 = s.2 ∧ w = 1⌉
```

with unit weights. Unfolding the definition of `wseg` twice shows what a segment of two steps is:

```
wseg c 2 n s t = ∃ s₁ w₁, c s s₁ w₁ ✶ ∃ s₂ w₂, c s₁ s₂ w₂ ✶ ⌈s₂ = t ∧ (n - w₁) - w₂ = 0⌉
```

For the list segment, the heap `⌈x ≠ 0⌉ ✶ x ↦ y ✶ ⌈y ≠ 0⌉ ✶ y ↦ 0` satisfies `wseg c 2 2 (x, 0) (0, 0)`, with `s₁ = (y, 0)` and both weights 1; the constant component 0 records that both cells are guarded against the end 0. The abstraction of the list segment then reads `p_ls a b ==> ∃ k n, wseg c k n (a, b) (b, b) ✶ ⌈0 ≤ k⌉`, and the concretisation is its converse. A doubly linked list `dll hd p tl n len` has a state with two moving components, the current node and its predecessor; its cell relation contains the two points-to facts `s.1 ↦ x` and `(s.1 + 1) ↦ s.2` and sets the successor state to `(x, s.1)`; its weight is `1` per step and the length parameter `len` is the total weight.

### 4.2 Properties of the carrier

The following properties are proved by induction on the step count, once and for all, for every state type and cell relation.

```lean
theorem wseg_join {σ : Type} (c : σ → σ → Int → HProp) (k₁ k₂ : Nat) (n₁ n₂ : Int) (s t u : σ) :
    wseg c k₁ n₁ s t ✶ wseg c k₂ n₂ t u ==> wseg c (k₁ + k₂) (n₁ + n₂) s u := by
…
theorem wseg_split {σ : Type} (c : σ → σ → Int → HProp) (k₁ k₂ : Nat) (n : Int) (s u : σ) :
    wseg c (k₁ + k₂) n s u ==> ∃✶ t, ∃✶ m, wseg c k₁ m s t ✶ wseg c k₂ (n - m) t u := by
…
theorem wseg_map {σ τ : Type} (c : σ → σ → Int → HProp) (c' : τ → τ → Int → HProp) (f : σ → τ)
    (h : ∀ s s' w, c s s' w ==> c' (f s) (f s') w) (k : Nat) (n : Int) (s t : σ) :
    wseg c k n s t ==> wseg c' k n (f s) (f t) := by
…
theorem wseg_rev {σ τ : Type} (c : σ → σ → Int → HProp) (c' : τ → τ → Int → HProp) (f : σ → τ)
    (h : ∀ s s' w, c s s' w ==> c' (f s') (f s) w) (k : Nat) (n : Int) (s t : σ) :
    wseg c k n s t ==> wseg c' k n (f t) (f s) := by
…
theorem wseg_inv {σ : Type} (c : σ → σ → Int → HProp) (r : σ → σ → Int → Prop)
    (I : Nat → σ → σ → Int → Prop)
    (hc : ∀ s s' w h, c s s' w h → r s s' w) (h0 : ∀ s, I 0 s s 0)
    (hs : ∀ k s s' t w m, r s s' w → I k s' t m → I (k + 1) s t (m + w))
    (k : Nat) (n : Int) (s t : σ) : ∀ h, wseg c k n s t h → I k s t n := by
…
```

- `wseg_join` concatenates two segments that meet at a state; step counts and weights add. `wseg_split` cuts a segment after any number of steps, at an existentially quantified intermediate state and weight.
- `wseg_map` maps a segment over one cell relation to a segment over another along a function on states, given the corresponding implication between cells. The engine uses it to convert between predicates that share a cell layout, for example from a doubly linked list to a singly linked list over the same cells by forgetting the predecessor component. `wseg_map_fr` is the framed version: the per-cell implication may use a frame `F` that is kept aside. `wseg_rev` maps a segment to a segment traversed in the opposite direction, given the implication from each cell to the reversed cell; it relates a doubly linked list read forwards to the same list read backwards.
- `wseg_inv` derives an invariant `I k s t n` of every segment from a pure relation `r s s' w` that each cell implies, given that `I` holds of the empty segment and is preserved by prepending a step. `wseg_inv1` is the instance for unit weights: `n = k` and `k = 0 → s = t`.
- `wseg_nil`, `wseg_zero_elim`, `wseg_cong` (rewriting the indices of a segment along equalities), `wseg_cell`/`wseg_uncell` (a single cell is a one-step segment and conversely), `wseg_one` and `wseg_two_elim` complete the basic set. `wor` is a pointwise disjunction with its introduction and elimination rules, and `pure_l_intro`, `pure_r_intro` and `pure_r_elim` move pure facts.

The statements of the elementary lemmas named in the last item, of `wseg_map_fr`, and of the unit-weight invariant are:

```lean
theorem wseg_nil {σ : Type} (c : σ → σ → Int → HProp) (n : Int) (s t : σ) (h : s = t) (hn : n = 0) :
    (emp : HProp) ==> wseg c 0 n s t := by
…
theorem wseg_zero_elim {σ : Type} (c : σ → σ → Int → HProp) (n : Int) (s t : σ) :
    wseg c 0 n s t ==> ⌈s = t ∧ n = 0⌉ := HProp.himpl_refl _
…
theorem wseg_cong {σ : Type} (c : σ → σ → Int → HProp) {k k' : Nat} {n n' : Int} {s s' t t' : σ}
    (hk : k = k') (hn : n = n') (hs : s = s') (ht : t = t') :
    wseg c k n s t ==> wseg c k' n' s' t' := by
…
theorem wseg_cell {σ : Type} (c : σ → σ → Int → HProp) (s t : σ) (w : Int) :
    c s t w ==> wseg c 1 w s t := by
…
theorem wseg_uncell {σ : Type} (c : σ → σ → Int → HProp) (s t : σ) (n : Int) :
    wseg c 1 n s t ==> c s t n := by
…
theorem wseg_map_fr {σ τ : Type} (c : σ → σ → Int → HProp) (c' : τ → τ → Int → HProp) (f : σ → τ)
    (F : HProp) (h : ∀ s s' w, c s s' w ✶ F ==> c' (f s) (f s') w ✶ F) (k : Nat) (n : Int) (s t : σ) :
    wseg c k n s t ✶ F ==> wseg c' k n (f s) (f t) ✶ F := by
…
theorem pure_r_intro {P : Prop} {H1 H2 : HProp} (hp : P) (h : H1 ==> H2) : H1 ==> H2 ✶ ⌈P⌉ := by
…
theorem pure_l_intro {P : Prop} {H1 H2 : HProp} (hp : P) (h : H1 ==> H2) : H1 ==> ⌈P⌉ ✶ H2 :=
…
theorem pure_r_elim {P : Prop} {H1 H2 : HProp} (h : P → H1 ==> H2) : H1 ✶ ⌈P⌉ ==> H2 := by
…
theorem wseg_two_elim {σ : Type} (c : σ → σ → Int → HProp) (n : Int) (s t : σ) :
    wseg c 2 n s t ==> ∃✶ u, ∃✶ w, c s u w ✶ c u t (n - w) := by
…
theorem wseg_inv1 {σ : Type} (c : σ → σ → Int → HProp) (hc : ∀ s s' w h, c s s' w h → w = 1)
    (k : Nat) (n : Int) (s t : σ) : ∀ h, wseg c k n s t h → n = (k : Int) ∧ (k = 0 → s = t) :=
…
theorem wseg_one {σ : Type} (c : σ → σ → Int → HProp) (s t : σ) (n : Int) : c s t n ==> wseg c 1 n s t :=
…
```

A further group concerns constant components and allocation. `wseg_cst` states that a component that every cell preserves is equal at the two ends. `wseg_retarget` changes a constant component along a segment:

```lean
theorem wseg_retarget {σ : Type} (c : σ → σ → Int → HProp) (f : σ → σ) (loc : σ → Loc) (e : Loc)
    (F : HProp) (hF : safeFar e F) (hc : ∀ s s' w, hasLoc (loc s) (c s s' w))
    (hz : ∀ s s' w h, c s s' w h → loc s ≠ 0)
    (hg : ∀ s s' w, loc s ≠ e → c s s' w ==> c (f s) (f s') w) (k : Nat) (n : Int) (s t : σ) :
    Sep.wseg c k n s t ✶ F ==> Sep.wseg c k n (f s) (f t) ✶ F := by
…
```

Here `loc s` is the address that the cell starting at `s` allocates, and `f` replaces the constant component by a new value `e`. The cells of a list segment `p_ls x y` carry the guard `x_i ≠ y` for each cell address `x_i`; to merge this segment into a segment that ends at `e`, every guard must become `x_i ≠ e`. The theorem provides this when `e` is *safe far* in the frame `F`: `safeFar e F` means `e = 0 ∨ hasLoc e F`, that is, `e` is nil or is allocated in `F`. Since `x_i` is allocated in the cell and nonzero, and the cell is disjoint from `F`, the new guard holds. This is the standard composition rule for precise list segments, `ls x y ✶ ls y z ✶ (z allocated or z = nil) ==> ls x z`. `wseg_retarget_prev` is the variant for a constant compared with the address of the previous cell (a doubly linked list whose cells are guarded by `prev ≠ end`). `hasLoc_wseg_pos` (a segment with at least one step allocates its start), `hasLoc_wseg_ne` (a segment whose start differs from its end allocates its start), `hasLoc_wseg_last`, `wseg_bk_zero` (if the address recorded by the last cell is allocated in the frame, the segment is empty) and `holdsP_abs_prev` supply the allocation facts that the engine needs for these side conditions. The statements of the variant for previous addresses, of the constant-component invariant and of the allocation lemmas are:

```lean
theorem wseg_retarget_prev {σ : Type} (c : σ → σ → Int → HProp) (f : σ → σ) (adr prv : σ → Loc)
    (e : Loc) (F : HProp) (hF : safeFar e F) (hc : ∀ s s' w, hasLoc (adr s) (c s s' w))
    (hz : ∀ s s' w h, c s s' w h → adr s ≠ 0) (hp : ∀ s s' w, holdsP (prv s' = adr s) (c s s' w))
    (hg : ∀ s s' w, prv s ≠ e → c s s' w ==> c (f s) (f s') w) (k : Nat) :
    ∀ (n : Int) (s t : σ), prv s ≠ e →
      Sep.wseg c k n s t ✶ F ==> Sep.wseg c k n (f s) (f t) ✶ F := by
…
theorem wseg_cst {σ K : Type} (c : σ → σ → Int → HProp) (p : σ → K)
    (hc : ∀ s s' w, holdsP (p s' = p s) (c s s' w)) (k : Nat) (n : Int) (s t : σ) :
    holdsP (p t = p s) (wseg c k n s t) :=
…
theorem hasLoc_wseg_pos {σ : Type} (c : σ → σ → Int → HProp) (loc : σ → Loc)
    (hc : ∀ s s' w, hasLoc (loc s) (c s s' w)) (k : Nat) (n : Int) (s t : σ) (hk : 1 ≤ k) :
    hasLoc (loc s) (Sep.wseg c k n s t) := by
…
theorem hasLoc_wseg_ne {σ : Type} (c : σ → σ → Int → HProp) (loc : σ → Loc)
    (hc : ∀ s s' w, hasLoc (loc s) (c s s' w)) (k : Nat) (n : Int) (s t : σ) (h : loc s ≠ loc t) :
    hasLoc (loc s) (Sep.wseg c k n s t) := by
…
theorem hasLoc_wseg_last {σ : Type} (c : σ → σ → Int → HProp) (adr prv : σ → Loc)
    (hc : ∀ s s' w, hasLoc (adr s) (c s s' w)) (hp : ∀ s s' w, holdsP (prv s' = adr s) (c s s' w)) :
    ∀ (k : Nat) (n : Int) (s t : σ), hasLoc (prv t) (Sep.wseg c (k + 1) n s t)
…
theorem wseg_bk_zero {σ : Type} (c : σ → σ → Int → HProp) (adr prv : σ → Loc)
    (hc : ∀ s s' w, hasLoc (adr s) (c s s' w)) (hp : ∀ s s' w, holdsP (prv s' = adr s) (c s s' w))
    (F : HProp) (k : Nat) (n : Int) (s t : σ) (hl : hasLoc (prv t) F) :
    holdsP (k = 0) (Sep.wseg c k n s t ✶ F) := by
…
theorem holdsP_abs_prev {σ : Type} (c : σ → σ → Int → HProp) (adr prv : σ → Loc)
    (hc : ∀ s s' w, hasLoc (adr s) (c s s' w)) (hp : ∀ s s' w, holdsP (prv s' = adr s) (c s s' w))
    (X F : HProp) (st en : σ) (cond : Nat → Prop) (a : Loc)
    (hA : X ==> ∃✶ k, ∃✶ n, Sep.wseg c k n st en ✶ ⌈cond k⌉) (hF : hasLoc a F) (h0 : prv st ≠ a) :
    holdsP (a ≠ prv en) (X ✶ F) := by
…
```

In `wseg_bk_zero` and `holdsP_abs_prev`, `adr s` is the address of the cell starting at `s`, and `prv s'` is the component of the successor state that records it, as in a doubly linked list. If the last cell's recorded predecessor `prv t` is allocated in the frame, the segment has no cell (otherwise that address would be allocated twice); and an address allocated in the frame differs from the predecessor recorded at the end of an abstracted segment.

### 4.3 Branch data and lengths

Many predicates are not a single chain of identical cells. The even-length list, for example, is defined by two mutually recursive predicates: `ls_even x y` is empty (with `x = y`) or one cell followed by `ls_odd`, and `ls_odd x y` is one cell followed by `ls_even`. The step counts of such a predicate form a set that is not an interval. `SegC` describes a group of predicates whose bodies are paths by *branch data* `B : List (List (List (Option Nat)))`: `B[j]` is the list of branches of the `j`-th member of the group, and a branch is a list of items, where `none` stands for one carrier cell and `some j'` for a call to member `j'`. For the even and odd lists, `B = [[[], [none, some 1]], [[none, some 0]]]`. A linear predicate with a base of `kmin` cells has the branch data `gLin kmin`:

```lean
def gLin (kmin : Nat) : List (List (List (Option Nat))) := [[List.replicate kmin none, [none, some 0]]]
```

The admissible step counts of member `j` are given by the least relation closed under the branches:

```lean
def pLenC (S : Nat → Nat → Prop) : List (Option Nat) → Nat → Prop
  | [], k => k = 0
  | none :: r, k => ∃ k', k = k' + 1 ∧ pLenC S r k'
  | some j :: r, k => ∃ k1 k2, k = k1 + k2 ∧ S j k1 ∧ pLenC S r k2

def pLen (B : List (List (List (Option Nat)))) (i k : Nat) : Prop :=
  ∀ S : Nat → Nat → Prop, (∀ i k, (∃ b ∈ pNthK B i [], pLenC S b k) → S i k) → S i k
```

`pLenC S b k` holds when `k` is the length of branch `b`, each cell counting one and each call to member `j'` counting some `k'` with `S j' k'`. `pLen B` is defined impredicatively as the least `S` closed under all branches. For the even and odd lists, `pLen B 0` is the set of even numbers and `pLen B 1` the set of odd numbers; for `gLin kmin`, `pLen` is the set of numbers at least `kmin`:

```lean
theorem pLen_lin (B : List (List (List (Option Nat)))) (j kmin : Nat)
    (hB : pNthK B j [] = [List.replicate kmin none, [none, some j]]) (k : Nat) :
    pLen B j k ↔ kmin ≤ k := by
```

### 4.4 Profiles

The engine reasons about lengths with `omega`, which needs them as linear arithmetic, not as a least fixed point. Every length set that arises is ultimately periodic: there are a threshold `m`, a period `p` and a set of residues `rs` such that `k` belongs to the set exactly when `m ≤ k` and `(k - m) mod p ∈ rs`. This triple is the *profile* of a member, and `phiI m p rs` is the corresponding proposition over `Int`, the form in which it reaches `omega`:

```lean
def phiI (m p : Nat) (rs : List Nat) (n : Int) : Prop :=
  match p with
  | 1 => (m : Int) ≤ n
  | _ => (m : Int) ≤ n ∧ slinR ((n - (m : Int)) % (p : Int)) rs
```

Two Boolean checks with soundness theorems connect profiles to `pLen`. `pChkA B prof` checks that every period is positive and that the profiles are closed under every branch: running a branch over the residues of the members it calls produces only lengths that the profile of the defining member admits, and the threshold is respected. By leastness of `pLen`, this implies that every admissible length satisfies the profile.

`pChkC B prof rk N sps cert` checks the converse, that every length in the profile is admissible, with the help of a certificate. Its arguments are a rank `rk j` for each member `j` (a natural number below the number of members `R`), a bound `N`, a *span* `sps j` for each member (a positive multiple of its period), and, per member, a list of *small entries* and a list of *big rules*. Both kinds of certificate item name a branch of the member and give, for each call item of the branch in order, either a fixed length of the callee (`some c`) or a hole (`none`).

- *Small rule* (`pSmallOk`). For every length `n < N` in the profile of `j`, some small entry `(n, bi, ls)` names a branch `bi` without holes whose cells and fixed callee lengths sum to `n`. Each fixed length `c` of a callee `q` must lie in the profile of `q` and be smaller than `n` in the lexicographic order of (length, rank): `c < n`, or `c = n` and `rk q < rk j`.
- *Big rule* (`pBigOk`). For every residue `r` below the span with `r mod p` in the residues of `j`, some big rule `(r, bi, n0, ls)` names a branch with exactly one hole, a call to some member `q0`, and fixed lengths below `N` for the other calls; `n0` is a representative of the class, with `N ≤ n0 < N + sps j` and `(n0 - m) mod sps j = r`. Let `d` be the number of cells of the branch plus its fixed lengths. The rule requires `0 < d` or `rk q0 < rk j`, and requires that for every length `n ≥ N` of the class the length `n - d` assigned to the hole lie in the profile of `q0` (checked on the residues of `n0 - d - m_{q0}` modulo the period of `q0`).

A length `n ≥ N` of the class of `r` is thus derived through the big rule from the hole length `n - d`, which is strictly smaller when `d > 0` and equal, at a callee of lower rank, when `d = 0`. The soundness proof of `pChkC` is a strong induction on the measure `n · R + rk j`, which decreases in both cases and in the small rule. The soundness theorems are

```lean
theorem pChkA_sound (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (h : pChkA B prof = true) (j k : Nat) (hk : pLen B j k) : pSet prof j k := by
…
theorem pChkC_sound (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat)) (rk : List Nat)
    (N : Nat) (sps : List Nat)
    (cert : List (List (Nat × Nat × List (Option Nat)) × List (Nat × Nat × Nat × List (Option Nat))))
    (hc : pChkC B prof rk N sps cert = true) :
    ∀ μ j n, n * B.length + rk.getD j 0 = μ → j < B.length → inSp prof j n = true → pLen B j n := by
…
```

and their consequences in the form the builder uses are `gPhiA` (an admissible length satisfies `phiI`) and `gPhiC` (a length satisfying `phiI` is admissible):

```lean
theorem gPhiA (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (hA : pChkAK B prof = true) (j m p : Nat) (rs : List Nat) (hpr : pNthK prof j pDflt = (m, p, rs))
    (k : Nat) (hk : pLen B j k) : phiI m p rs (k : Int) := by
…
theorem gPhiC (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (rk : List Nat) (N : Nat) (sps : List Nat)
    (cert : List (List (Nat × Nat × List (Option Nat)) × List (Nat × Nat × Nat × List (Option Nat))))
    (hC : pChkCK B prof rk N sps cert = true) (j m p : Nat) (rs : List Nat) (hj : Nat.blt j (pLenK B) = true)
    (hpr : pNthK prof j pDflt = (m, p, rs)) (k : Nat) (hk : phiI m p rs (k : Int)) : pLen B j k := by
…
```

The hypotheses `hA`, `hC` and `hj` (the member index is below the number of members) are equations `… = true` that the builder supplies as `Eq.refl true`; the kernel discharges them by evaluation. The checks are first run natively in `MetaM`, so a failing check never produces a term. The statements use variants with suffix `K` (`pChkAK`, `pChkCK`, `pNthK`, `pLenK`, …), defined directly by the recursors `List.rec`, `Nat.rec` and `Option.rec`, together with theorems equating them to the computable versions. The kernel evaluates the core library's `List.getD`, `List.all` and `List.range` five to eight times more slowly than direct recursors; on the check `pChkA` for the non-recursive list predicate `ls_nonrec` the `K` versions reduced the kernel time from 3.2 to 0.56 ms.

For the even and odd lists, the profiles are `(0, 2, [0])` and `(1, 2, [0])`: lengths at least 0 with even difference from 0, and lengths at least 1 with even difference from 1. The abstraction of `ls_even x y` yields `phiI 0 2 [0] k`, which unfolds to `0 ≤ k ∧ (k - 0) % 2 = 0`; this is what lets `omega` conclude, for example, that two even segments joined give an even segment.

The check `pChkA` can be followed by hand on these profiles, with `B = [[[], [none, some 1]], [[none, some 0]]]`. For each branch, `pRunA` computes the possible residues, modulo the defining member's period, of the branch's lengths and a lower bound for them, starting from residue 0 and bound 0: a cell adds 1 to every residue and to the bound; a call to member `q` with profile `(m, p, rs)` adds `m + r + p · t` for every `r ∈ rs` and every `t` below the defining member's period, and adds `m` to the bound. For member 0 (period 2), the branch `[]` gives residue 0 and bound 0; the branch `[none, some 1]` gives residue 1 and bound 1 after the cell, then residues `1 + 1 + 0 + 2t mod 2 = 0` and bound 2 after the call. Every residue, shifted by the threshold 0, is in `[0]`, and every bound is at least 0, so the branches of member 0 respect its profile. For member 1, the branch `[none, some 0]` gives residue 1 and bound 1 after the cell, and residues `1 + 0 + 0 + 2t mod 2 = 1` and bound `1 + 0 = 1` after the call to member 0, so the shifted residue `(1 - 1) mod 2 = 0` is in `[0]` and the bound respects the threshold 1. Both periods are positive. The check succeeds, and `pChkA_sound` concludes that every admissible length of member 0 is even and every admissible length of member 1 is odd.

### 4.5 Chains and the abstraction theorem

A branch is instantiated between two states by a chain:

```lean
noncomputable def gChain {σ : Type} (c : σ → σ → Int → HProp) (X : Nat → σ → σ → Int → HProp)
    (b : List (Option Nat)) : σ → σ → Int → HProp :=
  List.rec (motive := fun _ => σ → σ → Int → HProp) (fun s t n => ⌈s = t ∧ n = 0⌉)
    (fun it _ ih s t n => Option.rec (motive := fun _ => HProp)
      (∃✶ s', ∃✶ w, c s s' w ✶ ih s' t (n - w))
      (fun j => ∃✶ s', ∃✶ m, X j s s' m ✶ ih s' t (n - m)) it) b

def gA {σ : Type} (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat))))
    (j : Nat) (s t : σ) (n : Int) : HProp :=
  ∃✶ k, wseg c k n s t ✶ ⌈pLen B j k⌉

def gAny (B : List (List (List (Option Nat)))) (j : Nat) (f : List (Option Nat) → HProp) : HProp :=
  fun h => ∃ b ∈ pNthK B j [], f b h

def gQ {ι σ J : Type} (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat))))
    (mem : ι → Nat) (st : ι → σ) (E : ι → J → σ) (N : ι → J → Int) (T : ι → J → HProp) (a : ι) : HProp :=
  ∃✶ j, gA c B (mem a) (st a) (E a j) (N a j) ✶ T a j
```

`gChain c X b s t n` follows the items of branch `b` from `s` to `t` with total weight `n`; a `none` item is a cell `c`, a `some j` item is `X j` applied to an intermediate state and weight. `gA c B j s t n` is the *abstraction* of member `j`: a segment of some admissible length `k`. `gAny B j f` says that some branch of member `j` satisfies `f`. `gQ` packages the abstraction of one predicate instance `a`: its member index `mem a`, its start state `st a`, and an end state `E a j`, a weight `N a j` and a tail `T a j` that may depend on a *remainder* `j` of an arbitrary type `J`, existentially quantified. The remainder covers the parts of the abstraction that the predicate's arguments do not fix: a missing end component (a list whose last cell's successor is not a parameter), a free weight (no length parameter), or both. The tail is a heap assertion that follows the segment; it covers predicates whose base case contains material that is not a carrier cell.

```lean
theorem gAbs {κ ι σ J : Type} (P : κ → HProp) (G : (κ → HProp) → κ → HProp)
    (hind : ∀ M : κ → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a) (emb : κ → ι)
    (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat)))) (mem : ι → Nat) (st : ι → σ)
    (E : ι → J → σ) (N : ι → J → Int) (T : ι → J → HProp)
    (hstep : ∀ a, G (fun b => gQ c B mem st E N T (emb b)) a ==>
      ∃✶ j, gAny B (mem (emb a)) (fun b => gChain c (gA c B) b (st (emb a)) (E (emb a) j) (N (emb a) j)) ✶
        T (emb a) j)
    (a : κ) : P a ==> gQ c B mem st E N T (emb a) :=
…
```

The hypotheses are: a predicate family `P : κ → HProp` with its functional `G` and its induction principle `hind` (every prefixed point of `G` contains `P`); an embedding `emb` of the predicate's arguments into the instance type `ι`; the carrier data; and the one obligation `hstep`. `hstep` says: unfold the definition of `P` one level, with every recursive occurrence replaced by its abstraction (the functional applied to `fun b => gQ … (emb b)`); the result must entail a chain along one of the member's branches, whose recursive items are abstractions, followed by the tail. The conclusion is the abstraction of every instance. The proof applies `hind` with `gQ ∘ emb` as the prefixed point and closes each step by `gAny_abs`, which joins the abstracted sub-segments of a chain into one segment with `wseg_join` and records the admissible length by the introduction rule of `pLen`:

```lean
theorem gAny_abs {σ : Type} (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat))))
    (j : Nat) (s t : σ) (n : Int) :
    gAny B j (fun b => gChain c (gA c B) b s t n) ==> gA c B j s t n := by
```

The point of this formulation is that `hstep` contains no induction and no recursion: it is a statement about one unfolding of the definition, which the builder proves by matching each disjunct of the body against a branch (Section 10.6). The induction is done once, in this theorem. `gAbs` is stated over an abstract induction principle so that both plain least-fixed-point induction (`lfpG_induct`) and the strengthened form `lfpG_induct_with`, where each recursive occurrence is available both as the predicate and as its abstraction, are instances. The library's least fixed point `lfpG` (a copy of the benchmark's `lfp`, defined in the vocabulary part of the file, Section 4.9) and its two induction principles are as follows; `hwith H1 H2`, the pointwise conjunction of two heap assertions, holds of a heap that satisfies both.

```lean
def lfpG {α : Type} (F : (α → HProp) → α → HProp) : α → HProp :=
  fun a h => ∀ X : α → HProp, (∀ b, F X b ==> X b) → X a h

theorem lfpG_induct {α : Type} (F : (α → HProp) → α → HProp) (X : α → HProp)
    (hX : ∀ b, F X b ==> X b) (a : α) : lfpG F a ==> X a := fun _ hh => hh X hX
…
theorem lfpG_induct_with {α : Type} (F : (α → HProp) → α → HProp) (M : α → HProp)
    (hmono : ∀ X Y : α → HProp, (∀ a, X a ==> Y a) → ∀ a, F X a ==> F Y a)
    (hfold : ∀ a, F (lfpG F) a ==> lfpG F a)
    (hM : ∀ a, F (fun b => hwith (lfpG F b) (M b)) a ==> M a) (a : α) : lfpG F a ==> M a := by
…
```

### 4.6 The concretisation theorem

Concretisation goes in the other direction: a segment of admissible length is folded back into the predicate. The obligations are again per branch, but now a branch is instantiated with *concrete* predicate calls instead of abstractions, along intermediate states and weights produced by splitting the segment:

```lean
noncomputable def gChainC {ι σ : Type} (cv : σ → σ → Int → HProp) (P : ι → HProp)
    (arg : Nat → Bool → σ → σ → Int → ι) (b : List (Option Nat)) :
    (Nat → σ) → (Nat → Int) → HProp → σ → σ → Int → HProp :=
  List.rec (motive := fun _ => (Nat → σ) → (Nat → Int) → HProp → σ → σ → Int → HProp)
    (fun _ _ TT _ _ _ => TT)
    (fun it r ih f g TT s t n => List.rec (motive := fun _ => HProp)
      (Option.rec (motive := fun _ => HProp) (cv s t n ✶ TT) (fun j => P (arg j true s t n)) it)
      (fun _ _ _ => Option.rec (motive := fun _ => HProp)
        (cv s (f 0) (g 0) ✶ ih (fun i => f (i + 1)) (fun i => g (i + 1)) TT (f 0) t (n - g 0))
        (fun j => P (arg j false s (f 0) (g 0)) ✶
          ih (fun i => f (i + 1)) (fun i => g (i + 1)) TT (f 0) t (n - g 0)) it) r) b

def gChainI {σ : Type} (I : Nat → σ → σ → Int → Prop) (b : List (Option Nat)) :
    (Nat → σ) → (Nat → Int) → (Nat → Nat) → σ → σ → Int → Prop :=
  List.rec (motive := fun _ => (Nat → σ) → (Nat → Int) → (Nat → Nat) → σ → σ → Int → Prop)
    (fun _ _ _ s t n => s = t ∧ n = 0)
    (fun it r ih f g kf s t n => List.rec (motive := fun _ => Prop)
      (Option.rec (motive := fun _ => Prop) True (fun _ => I (kf 0) s t n) it)
      (fun _ _ _ => Option.rec (motive := fun _ => Prop)
        (ih (fun i => f (i + 1)) (fun i => g (i + 1)) (fun i => kf (i + 1)) (f 0) t (n - g 0))
        (fun _ => I (kf 0) s (f 0) (g 0) ∧
          ih (fun i => f (i + 1)) (fun i => g (i + 1)) (fun i => kf (i + 1)) (f 0) t (n - g 0)) it) r) b
```

`gChainC cv P arg b f g TT s t n` is the concrete chain of branch `b`: the intermediate states are `f 0, f 1, …` and the intermediate weights `g 0, g 1, …`; a cell item is `cv` (a view of the carrier cell), a call item is `P` applied to the instance computed by `arg`, whose Boolean argument tells whether the call is the last item of the branch; the tail `TT` is attached after the last item. `gChainI I b f g kf s t n` is the pure side information that holds along such a split: the chain's states and weights are consistent, and each call's sub-segment satisfies the carrier invariant `I` at its length `kf i`. The theorem is

```lean
theorem gConc {ι σ J : Type} (c : σ → σ → Int → HProp) (B : List (List (List (Option Nat))))
    (mem : ι → Nat) (st : ι → σ) (E : ι → J → σ) (N : ι → J → Int) (T : ι → J → HProp)
    (arg : ι → J → Nat → Bool → σ → σ → Int → ι × J)
    (hmem : ∀ a jj j l s s' m, j < B.length → mem (arg a jj j l s s' m).1 = j)
    (I : Nat → σ → σ → Int → Prop) (hI : ∀ k n s t, holdsP (I k s t n) (wseg c k n s t))
    (nl : Nat → Bool) (hnl : gNLB nl B = true)
    (hf : ∀ a jj j s s' m k, nl j = true → I k s s' m →
      st (arg a jj j false s s' m).1 = s ∧ N (arg a jj j false s s' m).1 (arg a jj j false s s' m).2 = m ∧
      E (arg a jj j false s s' m).1 (arg a jj j false s s' m).2 = s' ∧
      T (arg a jj j false s s' m).1 (arg a jj j false s s' m).2 = emp)
    (ht : ∀ a jj j s m k, I k s (E a jj) m →
      st (arg a jj j true s (E a jj) m).1 = s ∧
      N (arg a jj j true s (E a jj) m).1 (arg a jj j true s (E a jj) m).2 = m ∧
      E (arg a jj j true s (E a jj) m).1 (arg a jj j true s (E a jj) m).2 = E a jj ∧
      T (arg a jj j true s (E a jj) m).1 (arg a jj j true s (E a jj) m).2 = T a jj)
    (cv : σ → σ → Int → HProp) (hcv : ∀ s t n, c s t n ==> cv s t n) (P : ι → HProp)
    (hbr : ∀ a jj, ∀ b ∈ pNthK B (mem a) [], ∀ f g kf, gChainI I b f g kf (st a) (E a jj) (N a jj) →
      gChainC cv P (fun j l s s' m => (arg a jj j l s s' m).1) b f g (T a jj) (st a) (E a jj) (N a jj) ==> P a)
    (k : Nat) (a : ι) (jj : J) (hk : pLen B (mem a) k) :
    wseg c k (N a jj) (st a) (E a jj) ✶ T a jj ==> P a := by
…
```

Its hypotheses say the following.

- `arg a jj j l s s' m` computes the instance (and remainder) of a call to member `j` on the sub-segment from `s` to `s'` with weight `m`; `hmem` says that the instance belongs to member `j`.
- `I` is an invariant of all segments (`hI`), proved by `wseg_inv` from the cell relation.
- `nl` marks the members that may occur in a non-last position, and `hnl` checks this against `B` by evaluation. For a non-last call, `hf` says that the computed instance starts at `s`, ends at `s'`, has weight `m` and an empty tail; for the last call, `ht` says that it ends at the instance's own end `E a jj` and carries its tail `T a jj`. These conditions may assume the invariant of the sub-segment.
- `cv` is a weakening of the cell (`hcv`), used when the cell is a disjunction of views and a branch needs one particular view.
- `hbr` is the per-branch obligation: under the chain invariant, the concrete chain entails `P a`. This is again a statement about one unfolding of the definition, folded instead of unfolded.

The conclusion holds for every admissible length `k`. The proof is by induction on the derivation of `pLen B (mem a) k`: the derivation selects a branch and lengths for its items, `wseg_split` cuts the segment accordingly, the induction hypothesis folds each call's sub-segment into the predicate, and `hbr` folds the branch. The invariant of a callee's sub-segment is obtained from `hI` before the induction hypothesis consumes the sub-segment.

### 4.7 The corollaries

Instantiating `gAbs` and `gConc` directly at every use proved expensive in the kernel (abstraction 23 % and concretisation 130 % slower on the profile route than with fixed arguments), so the builder instantiates thin corollaries, which fix the carrier arguments and contain no induction of their own. There are two families, chosen by the carrier data.

**The profile family** serves groups of path predicates over locations: every member's body is a sequence of cells of one fixed template `C x u` (for example `⌈x ≠ 0⌉ ✶ x ↦ u`) and calls of members, from the first parameter to the second. The cell relation is `pCell C`, which has unit weight (`pCell_w`):

```lean
def pCell (C : Nat → Nat → HProp) (s s' : Nat) (w : Int) : HProp :=
  ∃✶ u, C s u ✶ ⌈s' = u ∧ w = 1⌉
…
theorem pCell_w (C : Nat → Nat → HProp) : ∀ (s s' : Nat) (w : Int) h, pCell C s s' w h → w = 1 := by
…
def gQP (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (a : Nat × Nat × Nat) : HProp :=
  gQ (pCell C) B (fun a : Nat × Nat × Nat => a.1) (fun a => a.2.1) (fun a (_ : Int) => a.2.2) (fun _ j => j)
    (fun _ _ => emp) a
```

`gAbsPG` is `gAbs` for `gQP`, and `gAbsPGPhi` (with `gAbsPGLe` for period 1) composes it with `gPhiA` to give the abstraction in its final form, with the profile as an arithmetic fact:

```lean
theorem gAbsPG {κ : Type} (P : κ → HProp) (G : (κ → HProp) → κ → HProp)
    (hind : ∀ M : κ → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a) (emb : κ → Nat × Nat × Nat)
    (C : Nat → Nat → HProp) (B : List (List (List (Option Nat))))
    (hstep : ∀ a, G (fun b => gQP C B (emb b)) a ==> gAnyP C B (emb a))
    (a : κ) : P a ==> gQP C B (emb a) :=
…
theorem gAbsPGPhi (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (hA : pChkAK B prof = true) (j m p : Nat) (rs : List Nat) (hpr : pNthK prof j pDflt = (m, p, rs)) (x y : Nat) :
    gQP C B (j, x, y) ==> ∃✶ k, ∃✶ n, wseg (pCell C) k n x y ✶ ⌈phiI m p rs (k : Int)⌉ :=
…
theorem gAbsPGLe (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (prof : List (Nat × Nat × List Nat))
    (hA : pChkAK B prof = true) (j m : Nat) (rs : List Nat) (hpr : pNthK prof j pDflt = (m, 1, rs)) (x y : Nat) :
    gQP C B (j, x, y) ==> ∃✶ k, ∃✶ n, wseg (pCell C) k n x y ✶ ⌈m ≤ k⌉ :=
```

`gConcPG` is `gConc` for this family, with the branch obligations stated through the simpler concrete chain `gChainL`; together with `gPhiC` it concretises a segment whose length satisfies the profile:

```lean
theorem gConcPG (C : Nat → Nat → HProp) (B : List (List (List (Option Nat)))) (Lx : Nat → Nat → Nat → HProp)
    (H : pAllIdx (fun j => ∀ b ∈ pNthK B j [], ∀ (f : Nat → Nat) (x y : Nat),
      gChainL C Lx b f x y ==> Lx j x y) 0 (pLenK B))
    (k j x y : Nat) (n : Int) (hk : pLen B j k) : wseg (pCell C) k n x y ==> Lx j x y := by
…
```

**The generic family** serves every other carrier, with the branch data `gLin kmin`: a base of `kmin` cells and a step of one cell followed by a recursive call. Arbitrary state types, weights, tails, constant components and missing end components are allowed. The base is described by `gBase c kmin s t n`, the chain of `kmin` cells, and by its weight-free form `gBaseF`:

```lean
noncomputable def gBase {σ : Type} (c : σ → σ → Int → HProp) (k : Nat) : σ → σ → Int → HProp :=
  Nat.rec (motive := fun _ => σ → σ → Int → HProp) (fun s t n => ⌈s = t ∧ n = 0⌉)
    (fun k ih s t n => Nat.rec (motive := fun _ => HProp) (c s t n)
      (fun _ _ => ∃✶ s', ∃✶ w, c s s' w ✶ ih s' t (n - w)) k) k
…
noncomputable def gBaseF {σ : Type} (c : σ → σ → Int → HProp) (k : Nat) : σ → σ → HProp :=
  Nat.rec (motive := fun _ => σ → σ → HProp) (fun s t => ⌈s = t⌉)
    (fun k ih s t => Nat.rec (motive := fun _ => HProp) (∃✶ w, c s t w)
      (fun _ _ => ∃✶ s', ∃✶ w, c s s' w ✶ ih s' t) k) k
```

The abstraction theorem of this family replaces the branch obligation of `gAbs` by a disjunction of a base case and a step case with an explicit relation between an instance and its recursive instance:

```lean
theorem gAbsG {α σ J : Type} (P : α → HProp) (G : (α → HProp) → α → HProp)
    (hind : ∀ M : α → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a)
    (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ) (E : α → J → σ) (N : α → J → Int)
    (T : α → J → HProp) (rel : α → α → Int → Prop) (jm : α → α → Int → J → J)
    (hrel : ∀ a a' w, rel a a' w → ∀ j', E a' j' = E a (jm a a' w j') ∧ T a' j' = T a (jm a a' w j') ∧
      N a (jm a a' w j') = N a' j' + w) (L : α → HProp)
    (hL : ∀ a, L a ==> gQ c (gLin kmin) (fun _ => 0) st E N T a) (B : α → HProp)
    (hB : ∀ a, B a ==> ∃✶ j, gBase c kmin (st a) (E a j) (N a j) ✶ T a j)
    (hstep : ∀ a, G (gQ c (gLin kmin) (fun _ => 0) st E N T) a ==>
      wor (B a) (∃✶ a', ∃✶ w, ⌈rel a a' w⌉ ✶ (c (st a) (st a') w ✶ L a')))
    (a : α) : P a ==> gQ c (gLin kmin) (fun _ => 0) st E N T a := by
…
```

In `hstep`, the unfolded body must entail either the base `B a` or one cell from the instance's start state to the start state of a recursive instance `a'`, followed by `L a'`, with the relation `rel a a' w`; `hrel` states that the recursive instance's end, tail and weight are those of `a` shifted along `jm`. `L` is either the abstraction itself or its `hwith` form. Four corollaries fix the remainder type and are what the builder instantiates. The one used for the list segment (Section 4.8), with an integer remainder that carries the free total weight, reads

```lean
theorem gAbsGI {α σ : Type} (P : α → HProp) (G : (α → HProp) → α → HProp)
    (hind : ∀ M : α → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a)
    (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ) (E : α → σ) (L : α → HProp)
    (hL : ∀ a, L a ==> gQ c (gLin kmin) (fun _ => 0) st (fun a _ => E a) (fun _ j => j) (fun _ _ => emp) a)
    (hstep : ∀ a, G (gQ c (gLin kmin) (fun _ => 0) st (fun a _ => E a) (fun _ j => j) (fun _ _ => emp)) a ==>
      wor (gBaseF c kmin (st a) (E a))
        (∃✶ a', ∃✶ w, ⌈∀ j' : Int, E a' = E a ∧ (emp : HProp) = emp ∧ j' + w = j' + w⌉ ✶
          (c (st a) (st a') w ✶ L a')))
    (a : α) (R : Nat → Int → HProp) (hR : ∀ k j, kmin ≤ k → emp ==> R k j) :
    P a ==> ∃✶ k, ∃✶ j, wseg c k j (st a) (E a) ✶ R k j :=
…
```

The four are: `gAbsGU` (remainder `Unit`: the predicate has a length parameter and both ends are determined), `gAbsGI` (remainder `Int`: no length parameter, the weight is free), `gAbsGM` (a missing end component) and `gAbsGMI` (both). `gAbsGP` and `gBaseF_base` connect the forms:

```lean
theorem gBaseF_base {σ : Type} (c : σ → σ → Int → HProp) :
    ∀ (k : Nat) (s t : σ), gBaseF c k s t ==> ∃✶ n, gBase c k s t n
…
theorem gAbsGP {α σ J : Type} (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ) (E : α → J → σ)
    (N : α → J → Int) (T : α → J → HProp) (a : α) (R : Nat → J → HProp)
    (hR : ∀ k j, kmin ≤ k → T a j ==> R k j) :
    gQ c (gLin kmin) (fun _ => 0) st E N T a ==> ∃✶ k, ∃✶ j, wseg c k (N a j) (st a) (E a j) ✶ R k j :=
…
theorem gAbsGU {α σ : Type} (P : α → HProp) (G : (α → HProp) → α → HProp)
    (hind : ∀ M : α → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a)
    (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ) (E : α → Unit → σ) (N : α → Unit → Int)
    (T : α → Unit → HProp) (jm : α → α → Int → Unit → Unit) (L : α → HProp)
    (hL : ∀ a, L a ==> gQ c (gLin kmin) (fun _ => 0) st E N T a)
    (hstep : ∀ a, G (gQ c (gLin kmin) (fun _ => 0) st E N T) a ==>
      wor (gBase c kmin (st a) (E a ()) (N a ()) ✶ T a ())
        (∃✶ a', ∃✶ w, ⌈∀ j', E a' j' = E a (jm a a' w j') ∧ T a' j' = T a (jm a a' w j') ∧
          N a (jm a a' w j') = N a' j' + w⌉ ✶ (c (st a) (st a') w ✶ L a')))
    (a : α) (R : Nat → HProp) (hR : ∀ k, kmin ≤ k → T a () ==> R k) :
    P a ==> ∃✶ k, wseg c k (N a ()) (st a) (E a ()) ✶ R k :=
…
theorem gAbsGM {α σ J : Type} (P : α → HProp) (G : (α → HProp) → α → HProp)
    (hind : ∀ M : α → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a)
    (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ) (E : α → J → σ) (N : α → J → Int)
    (T : α → J → HProp) (jm : α → α → Int → J → J) (L : α → HProp)
    (hL : ∀ a, L a ==> gQ c (gLin kmin) (fun _ => 0) st E N T a)
    (hstep : ∀ a, G (gQ c (gLin kmin) (fun _ => 0) st E N T) a ==>
      wor (∃✶ j, gBase c kmin (st a) (E a j) (N a j) ✶ T a j)
        (∃✶ a', ∃✶ w, ⌈∀ j', E a' j' = E a (jm a a' w j') ∧ T a' j' = T a (jm a a' w j') ∧
          N a (jm a a' w j') = N a' j' + w⌉ ✶ (c (st a) (st a') w ✶ L a')))
    (a : α) (R : Nat → J → HProp) (hR : ∀ k j, kmin ≤ k → T a j ==> R k j) :
    P a ==> ∃✶ k, ∃✶ j, wseg c k (N a j) (st a) (E a j) ✶ R k j :=
…
theorem gAbsGMI {α σ M : Type} (P : α → HProp) (G : (α → HProp) → α → HProp)
    (hind : ∀ M : α → HProp, (∀ a, G M a ==> M a) → ∀ a, P a ==> M a)
    (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ) (E : α → M → σ) (T : α → M → HProp) (L : α → HProp)
    (hL : ∀ a, L a ==> gQ c (gLin kmin) (fun _ => 0) st (fun a (j : M × Int) => E a j.1) (fun _ j => j.2)
      (fun a j => T a j.1) a)
    (hstep : ∀ a, G (gQ c (gLin kmin) (fun _ => 0) st (fun a (j : M × Int) => E a j.1) (fun _ j => j.2)
      (fun a j => T a j.1)) a ==>
      wor (∃✶ m, gBaseF c kmin (st a) (E a m) ✶ T a m)
        (∃✶ a', ∃✶ w, ⌈∀ j' : M × Int, E a' j'.1 = E a j'.1 ∧ T a' j'.1 = T a j'.1 ∧ j'.2 + w = j'.2 + w⌉ ✶
          (c (st a) (st a') w ✶ L a')))
    (a : α) (R : Nat → M × Int → HProp) (hR : ∀ k j, kmin ≤ k → T a j.1 ==> R k j) :
    P a ==> ∃✶ k, ∃✶ j, wseg c k j.2 (st a) (E a j.1) ✶ R k j :=
```

The concretisation theorem of this family is

```lean
theorem gConcG {α σ J : Type} (P : α → HProp) (c : σ → σ → Int → HProp) (kmin : Nat) (st : α → σ)
    (E : α → J → σ) (N : α → J → Int) (T : α → J → HProp) (cal : α → J → σ → Int → α × J)
    (I : Nat → σ → σ → Int → Prop) (hI : ∀ k n s t, holdsP (I k s t n) (wseg c k n s t))
    (ht : ∀ a jj s m k, I k s (E a jj) m → st (cal a jj s m).1 = s ∧ N (cal a jj s m).1 (cal a jj s m).2 = m ∧
      E (cal a jj s m).1 (cal a jj s m).2 = E a jj ∧ T (cal a jj s m).1 (cal a jj s m).2 = T a jj)
    (hb : ∀ a jj, wseg c kmin (N a jj) (st a) (E a jj) ✶ T a jj ==> P a)
    (h1 : ∀ a jj s' w k, I k s' (E a jj) (N a jj - w) → c (st a) s' w ✶ P (cal a jj s' (N a jj - w)).1 ==> P a)
    (k : Nat) (a : α) (jj : J) (hk : kmin ≤ k) : wseg c k (N a jj) (st a) (E a jj) ✶ T a jj ==> P a :=
…
```

with one obligation `hb` for the base (a segment of exactly `kmin` cells folds into the predicate) and one obligation `h1` for the step (a cell followed by the recursive predicate instance computed by `cal` folds into the predicate, under the invariant of the remaining segment).

### 4.8 Instantiation for the list segment

The builder of Chapter 10 instantiates the generic family for `p_ls` as follows. The predicate has no length parameter and both end components are determined (the end is `(b, b)`), so the remainder type is `Int` (it carries the free total weight) and the corollary is `gAbsGI`.

- The predicate family is `fun a => p_ls a.1 a.2` over pairs `a`, and its functional is `f_ls`; the induction principle is `lfpG_induct` at `f_ls`. The library's `lfpG` has the same definition as the benchmark's `lfp`, so the two are definitionally equal and the principle applies to the predicate as stated.
- The start map is `fun a => (a.1, a.2)` and the end map `fun a => (a.2, a.2)`; the weight is the remainder itself; the tail is `emp`; `kmin` is 0.
- The obligation `hstep` is proved per branch of `f_ls` applied to the abstraction (Section 10.6): the base branch `⌈y₀ = y₁⌉ ✶ emp` entails the weight-free base `gBaseF c 0 (y₀, y₁) (y₁, y₁)`, which is `⌈(y₀, y₁) = (y₁, y₁)⌉`; the step branch entails one cell from `(y₀, y₁)` to `(u, y₁)` followed by the abstraction of `p_ls u y₁`, with the relation that the end, tail and weight shift correctly.
- The length condition `R k j` is `⌈0 ≤ k⌉`.

The result is `p_ls a b ==> ∃ k j, wseg c k j (a, b) (b, b) ✶ ⌈0 ≤ k⌉`. For the concretisation, `gConcG` is instantiated with `cal a jj s m = ((s.1, a.2), m)`: the recursive instance starts at the first component of the intermediate state and keeps the parent's constant end `a.2`. The invariant is the equality of the constant component at both ends of a segment (`wseg_cst`); with it, `ht` holds by reflexivity. The base obligation `hb` turns `wseg c 0 jj (a.1, a.2) (a.2, a.2)` into `⌈(a.1, a.2) = (a.2, a.2) ∧ jj = 0⌉` by `wseg_zero_elim` and proves the base branch `⌈a.1 = a.2⌉ ✶ emp`; the step obligation `h1` proves the step branch of `p_ls a.1 a.2` from one cell and `p_ls s'.1 a.2`, with the cell's existential as the witness `u`.

### 4.9 The logical vocabulary

The second half of `Sep/SegC.lean`, in the namespace `Sep.Xsearch`, defines the assertions and properties that occur in proof terms built by `xsearch`, with small lemmas about them.

The central definitions, the two lemmas that move a disequality or a pure fact implied by the left-hand side into the context of an entailment, and the separation lemma `ne_far` are:

```lean
def hasLoc (p : Loc) (H : HProp) : Prop := ∀ h, H h → p ∈ h

def neLocs (p q : Loc) (H : HProp) : Prop := ∀ h, H h → p ≠ q
…
def safeFar (f : Loc) (F : HProp) : Prop := f = 0 ∨ hasLoc f F
…
def holdsP (P : Prop) (H : HProp) : Prop := ∀ h, H h → P
…
theorem himpl_of_neLocs {p q : Loc} {H R : HProp} (hn : neLocs p q H)
    (k : p ≠ q → H ==> R) : H ==> R := fun h hh => k (hn h hh) h hh
…
theorem himpl_of_holds {P : Prop} {H R : HProp} (hn : holdsP P H)
    (k : P → H ==> R) : H ==> R := fun h hh => k (hn h hh) h hh
…
theorem ne_far {a b : Loc} {X F : HProp} (hx : hasLoc a X) (hz : a ≠ 0) (hF : safeFar b F) :
    holdsP (a ≠ b) (X ✶ F) := by
…
```

The definitions and lemmas of this part fall into the following groups.

- `hdisj H1 H2` is the pointwise disjunction used for predicate bodies and multi-view cells, with distribution lemmas (`hdisj_star_l`, `hdisj_star_r`, `hdisj_hexists`), elimination (`hdisj_elim`, `hdisj_star_elim`) and introduction (`hdisj_left`, `hdisj_right`).
- `hasLoc p H` (every heap satisfying `H` contains the location `p`) and `neLocs p q H` (every heap satisfying `H` has `p ≠ q`), with lemmas that propagate them through stars, existentials and disjunctions (`hasLoc_single`, `hasLoc_star_l`, `hasLoc_star_r`, `hasLoc_hexists`, `hasLoc_disj`, `hasLoc_mono`, `neLocs_star`, `neLocs_const`), and `himpl_of_neLocs`, which adds a disequality to the context of an entailment. `safeFar` (Section 4.2) with its introduction rules `safeFar_nil` and `safeFar_step`, `ne_far` and `cell_far` derive disequalities between an allocated address and a safe-far location.
- `lfpG` is a copy of the least fixed point with its induction principles `lfpG_induct` and `lfpG_induct_with` (Section 4.5); `hwith H1 H2` is the pointwise conjunction used by the latter.
- `holdsP P H` says that every heap satisfying `H` satisfies the pure fact `P`; `himpl_of_holds` adds such a fact to the context of an entailment, and `holdsP_of_top`, `holdsP_mono_imp`, `holdsP_and` and `holdsP_ne_symm` manipulate it. `hpack` is a star that the search keeps opaque, `hguard P H` a heap assertion guarded by a pure premise.
- The `inv_*` lemmas (`inv_len0`, `inv_len_step`, `inv_imp0`, `inv_imp_step`, `inv_or0`, `inv_or_step`, `inv_rel0`, `inv_rel_l`, `inv_rel_r`, …) are the base and step facts of the invariants that the engine derives for carriers; the pure prover proves invariant obligations by unifying with them before it calls `omega` (Section 7.1).
- `pure_l_of_holds`, `star_pure_drop`, `star_drop_emp`, `pures_emp_cons`, `pures_conj`, `emp_pure_true`, `pure_l_emp`, `emp_star_intro`, `pDrop`, `pDup`, `pDupNe` and `pEqSymm` are the steps of the direct closing procedures of Sections 10.6 and 10.7, and `hpure_true` turns a trivial pure fact into `emp`. `frame_l_of` and `perm_swap` frame and reorder a star. `wand_use`, `wand_use2` and `fwand_use` are the wand rules of the backtracking core.

The statements of the lemmas named in this list, group by group, are:

```lean
theorem hdisj_star_l (H1 H2 K : HProp) :
    hdisj H1 H2 ✶ K = hdisj (H1 ✶ K) (H2 ✶ K) := by
…
theorem hdisj_star_r (K H1 H2 : HProp) :
    K ✶ hdisj H1 H2 = hdisj (K ✶ H1) (K ✶ H2) := by
…
theorem hdisj_hexists {A : Sort _} (J K : A → HProp) :
    HProp.hexists (fun x => hdisj (J x) (K x))
      = hdisj (HProp.hexists J) (HProp.hexists K) := by
…
theorem hdisj_elim {H1 H2 H : HProp} (h1 : H1 ==> H) (h2 : H2 ==> H) :
    hdisj H1 H2 ==> H := by
…
theorem hdisj_left {H H1 H2 : HProp} (h : H ==> H1) : H ==> hdisj H1 H2 :=
…
theorem hdisj_right {H H1 H2 : HProp} (h : H ==> H2) : H ==> hdisj H1 H2 :=
…
theorem hdisj_star_elim {A B K H : HProp} (h1 : A ✶ K ==> H) (h2 : B ✶ K ==> H) : hdisj A B ✶ K ==> H := by
```

```lean
theorem hasLoc_single (p : Loc) (v : val) : hasLoc p (HProp.hsingle p v) := by
…
theorem hasLoc_star_l {p : Loc} {H1 H2 : HProp} (h1 : hasLoc p H1) :
    hasLoc p (H1 ✶ H2) := by
…
theorem hasLoc_star_r {p : Loc} {H1 H2 : HProp} (h2 : hasLoc p H2) :
    hasLoc p (H1 ✶ H2) := by
…
theorem hasLoc_hexists {A : Sort _} {p : Loc} {J : A → HProp}
    (h : ∀ a, hasLoc p (J a)) : hasLoc p (HProp.hexists J) := by
…
theorem hasLoc_disj {p : Loc} {H1 H2 : HProp} (h1 : hasLoc p H1)
    (h2 : hasLoc p H2) : hasLoc p (hdisj H1 H2) := by
…
theorem hasLoc_mono {p : Loc} {F G : HProp} (h : F ==> G) (hg : hasLoc p G) :
    hasLoc p F := fun hh hf => hg hh (h hh hf)
…
theorem safeFar_nil {f : Loc} {F : HProp} (h : f = 0) : safeFar f F := Or.inl h
…
theorem safeFar_step {a b : Loc} {F : HProp} (h1 : a ≠ b → hasLoc a F)
    (h2 : a = b → safeFar b F) : safeFar a F := by
…
theorem neLocs_star {p q : Loc} {H1 H2 : HProp}
    (h1 : hasLoc p H1) (h2 : hasLoc q H2) : neLocs p q (H1 ✶ H2) := by
…
theorem neLocs_const {p q : Loc} {H : HProp} (h : p ≠ q) : neLocs p q H :=
…
theorem cell_far {H G : HProp} {a e : Loc} (hH : hasLoc a H) (hz : ∀ h, H h → a ≠ 0)
    (hG : safeFar e G) : H ✶ G ==> ⌈a ≠ e⌉ ✶ (H ✶ G) := by
```

```lean
theorem holdsP_of_top {P : Prop} {H : HProp} (h : H ==> ⌈P⌉ ✶ HProp.htop) : holdsP P H :=
…
theorem holdsP_mono_imp {P : Prop} {F G : HProp} (h : F ==> G) (hg : holdsP P G) : holdsP P F :=
…
theorem holdsP_ne_symm {a b : Loc} {H : HProp} (h : holdsP (a ≠ b) H) : holdsP (b ≠ a) H :=
…
theorem holdsP_and {P Q : Prop} {H : HProp} (h1 : holdsP P H) (h2 : holdsP Q H) : holdsP (P ∧ Q) H :=
```

```lean
theorem inv_len0 : (0 : Int) = ((0 : Nat) : Int) := rfl
…
theorem inv_len_step {m w : Int} {k : Nat} (hw : w = 1) (h : m = (k : Int)) :
    m + w = ((k + 1 : Nat) : Int) := by
…
theorem inv_imp0 {α : Sort _} (x : α) : (0 : Nat) = 0 → x = x := fun _ => rfl
…
theorem inv_imp_step {α : Sort _} {k : Nat} (x y : α) : k + 1 = 0 → x = y :=
…
theorem inv_or0 (y : Nat) : (0 : Nat) = 0 ∨ y ≠ 0 := Or.inl rfl
…
theorem inv_or_step {k x y : Nat} (hz : x ≠ 0) (himp : k = 0 → x = y) (hor : k = 0 ∨ y ≠ 0) :
    k + 1 = 0 ∨ y ≠ 0 := by
…
theorem inv_rel0 (x b : Int) : x - x = b * ((0 : Nat) : Int) := by simp
…
theorem inv_rel_l {x y z b : Int} {k : Nat} (hr : x - y = b) (hi : y - z = b * (k : Int)) :
    x - z = b * ((k + 1 : Nat) : Int) := by
…
theorem inv_rel_r {x y z b : Int} {k : Nat} (hi : x - y = b * (k : Int)) (hr : y - z = b) :
    x - z = b * ((k + 1 : Nat) : Int) := by
```

```lean
theorem pEqSymm (a b : Nat) : (⌈a = b⌉ : HProp) ==> ⌈b = a⌉ := by
…
theorem pDrop (P : Prop) : (⌈P⌉ : HProp) ==> emp := by
…
theorem pDup (P : Prop) : (⌈P⌉ : HProp) ==> ⌈P⌉ ✶ ⌈P⌉ := by
…
theorem pDupNe (a b : Nat) : (⌈a ≠ b⌉ : HProp) ==> ⌈a ≠ b⌉ ✶ ⌈b ≠ a⌉ := by
…
theorem hpure_true {P : Prop} (hp : P) : (⌈P⌉ : HProp) = HProp.hempty := by
…
theorem star_pure_drop (H : HProp) (P : Prop) : H ✶ ⌈P⌉ ==> H := by
…
theorem pures_emp_cons {P : Prop} {R : HProp} (h : R ==> emp) : ⌈P⌉ ✶ R ==> emp := by
…
theorem pures_conj {A B : HProp} {P Q : Prop} (ha : A ==> ⌈P⌉) (hb : B ==> ⌈Q⌉) : A ✶ B ==> ⌈P ∧ Q⌉ := by
…
theorem emp_pure_true : (emp : HProp) ==> ⌈True⌉ := HProp.himpl_hempty_hpure trivial
…
theorem pure_l_emp {P : Prop} {R : HProp} (h : P → (emp ==> R)) : ⌈P⌉ ==> R := by
…
theorem emp_star_intro {A B : HProp} (ha : emp ==> A) (hb : emp ==> B) : emp ==> A ✶ B := by
…
theorem star_drop_emp {H R : HProp} (h : R ==> emp) : H ✶ R ==> H :=
…
theorem pure_l_of_holds {H G : HProp} {P : Prop} (hp : holdsP P H) (h : H ==> G) : H ==> ⌈P⌉ ✶ G :=
```

```lean
theorem frame_l_of (H3 : HProp) {H1 H2 : HProp} (h : H1 ==> H2) :
    H1 ✶ H3 ==> H2 ✶ H3 := HProp.himpl_frame_l h
…
theorem perm_swap (A B C : HProp) : A ✶ (B ✶ C) ==> B ✶ (A ✶ C) := by
…
theorem wand_use {A B D C : HProp} (h1 : D ==> A) (h2 : B ==> C) :
    (A -✶ B) ✶ D ==> C := by
…
theorem wand_use2 {A B E F C : HProp} (h1 : E ==> A) (h2 : B ✶ F ==> C) :
    (A -✶ B) ✶ (E ✶ F) ==> C := by
…
theorem fwand_use {α : Sort _} {J : α → HProp} {A B E F C : HProp} (v : α)
    (hj : J v = (A -✶ B)) (h1 : E ==> A) (h2 : B ✶ F ==> C) :
    HProp.hforall J ✶ (E ✶ F) ==> C := by
```

### 4.10 History

`Sep/SegC.lean` was created at step S5a of the second climb for a length-indexed list segment. The first consolidation phase (C1) replaced its content by the carrier `wseg`, which subsumed four separate lemma families, one per kind of predicate (decrementing counters, ordered data, length profiles, back pointers), each with its own join, split and conversion lemmas. At first the abstraction and concretisation lemmas were proved per problem by tactic scripts (one profile measured 38 ms per abstraction and 28 ms per concretisation); generic theorems instantiated per problem replaced these scripts in stages, which grew the file from 450 to 1507 lines. Pass 3b of the third consolidation phase replaced 50 theorems (an abstraction and a concretisation theorem per shape, 11 base lemmas, and the profile family's own inductions) by the two inductions `gAbs` and `gConc` and their thin corollaries; pass T0 replaced four abstraction corollaries by the four remainder-type corollaries above and introduced `gBaseF`. The file has 2283 lines.

## 5. The Entry Point and the Virtual Clock

From this chapter on the subject is `Sep/Xsearch.lean`. The file is organised as a set of tactics, each registered with `elab` or `syntax`/`elab_rules`, and the macro `xsearch` of Section 1.3 composes them. This chapter covers the registry of predicate definitions, the clock and the budgets, and the first two tactics of the macro, `xsearch_scope` and `xsearch_refute`. The third, `xsearch_cmodel`, is the subject of Chapter 6, and the fourth, `xsearch_start`, opens Chapter 8.

### 5.1 The registry of unfold equations

`xsearch` learns about predicates only through their unfold equations. The attribute `@[xsearch_unfold]` records, for each equation `f a₁ … aₙ = body`, the head constant `f` and the lemma name in a persistent environment extension:

```lean
structure UnfoldEntry where
  headFn    : Name
  lemmaName : Name
  deriving Repr, Inhabited
```

Every procedure that needs the definition of a predicate obtains it from `xsearchUnfoldExt.getState`, either by rewriting an occurrence with the lemma (`rewriteOcc`, Section 7.5) or by reading the body (Sections 6.2 and 10.2). A predicate is *recursive* (`isRecPred`) if its head is reachable from its own body through the bodies of other registered predicates; it is *flat* (`isFlatPred`) if it is not recursive and its body is not a disjunction.

### 5.2 The clock

```lean
def hbPerVms : Nat := 44000
def problemVms : Nat := 6000
def cmVms : Nat := 60

def vclock : BaseIO Nat := return (← IO.getNumHeartbeats) / hbPerVms

initialize globalDeadline : IO.Ref Nat ← IO.mkRef 0

def pastGlobal : CoreM Bool := do
  return (← vclock) > (← globalDeadline.get)

initialize searchDeadline : IO.Ref Nat ← IO.mkRef 0
```

All budgets are expressed in *virtual milliseconds*: the number of heartbeats consumed by the Lean process divided by `hbPerVms`. Heartbeats count allocations, so the clock advances with the work done and not with wall time; the same problem gives the same result on any machine and under any load. The clock was introduced in step 21 of the first climb, after a problem had been found to succeed or fail depending on the machine and its load; the value 44000 was calibrated then so that one virtual millisecond was about one wall-clock millisecond on the machine in use. The two other literals are the budget of a whole problem (`problemVms`, 6000 virtual milliseconds) and the cap of the countermodel search (`cmVms`, Section 6.7). These are the only three numeric literals in the file that bound effort.

Two deadlines are kept in global references. `globalDeadline` is set once per problem and is lowered temporarily when a procedure divides the remaining time among alternatives; `pastGlobal` tests it. `searchDeadline` bounds the backtracking core and the lemma builders; `checkDeadline` throws when either deadline has passed. Every other bound in the file is derived from the goal or from the remaining time. The derivations, most of which date from stage 5 of the first consolidation phase and from pass 7 of the third, are:

| Quantity | Derivation |
|---|---|
| time slice of a forced alternative in the core | remaining time / remaining alternatives |
| time per witness tuple | remaining time / remaining tuples |
| share of the segment engine | remaining time × carriers / (carriers + 1) |
| share of a residual round of the engine | remaining time × unmatched atoms after / (unmatched atoms before + 1) |
| time per invariant lemma in the core | search time / invariant alternatives |
| heartbeat limit of one `omega` call | remaining time / (hypotheses + 2) |
| width of a countermodel state set | left-hand atoms + 1 |
| steps per countermodel check | (cells + 1) × size of the compiled right-hand side |
| unfolding fuel in a countermodel check | 2 × heap size |
| chain walk steps in planning | (right-hand atoms + 1)² |
| candidate witness tuples | (candidate terms) × (binders) + 1 |

The quantities in the table belong to stages that later chapters define; they are collected here because all of them are measured on the same clock. Pass 7 removed eight fixed caps (core depth 40, 20000 search nodes, forced depth 6, 400000 countermodel steps, countermodel generation depth 40, split fuel 6, lemma shape depth 3, and a 32-cell limit on fact generation), a weight table for branch ordering and several sentinel encodings, after benchmark runs with every bound halved and doubled changed no outcome.

### 5.3 `xsearch_scope`

```lean
syntax "xsearch_scope " tactic : tactic
elab_rules : tactic
  | `(tactic| xsearch_scope $t) => do
    globalDeadline.set ((← vclock) + problemVms)
    simpOnlyCache.set #[]
    let cheap ← hasPredAtom
    withEnableInfoTree false
      (if cheap then Sep.Xsimpl.withCheapCancel (evalTactic t) else evalTactic t)
```

The scope sets the problem deadline, clears the cache of simp theorem sets, selects cheap cancellation in `xsimpl` (Section 3.11) when the goal contains a predicate atom, and runs the rest of the tactic with information trees disabled, since the information trees of the many internal tactic invocations are not used and cost time. Setting the deadline here, before any other tactic runs, corrects a defect found in pass 7: the countermodel, which runs before `xsearch_start`, used to read the deadline left by the previous problem.

### 5.4 `xsearch_refute`

```lean
elab "xsearch_refute" : tactic => withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  match entailHead? t with
  | none => pure ()
  | some (lhs, rhs) =>
    let heads := (xsearchUnfoldExt.getState (← getEnv)).map (·.headFn)
    for v in rhsVars heads rhs #[] do
      if (lhs.find? (· == v)).isNone then
        throwError "xsearch: unconstrained rhs variable"
```

`rhsVars` collects the variables of the right-hand side that occur as the address of a cell or as an argument of a predicate atom whose arguments are not all equal. If such a variable does not occur anywhere in the left-hand side, the tactic fails. For a cell the reason is semantic: the left-hand heap's domain does not depend on the variable, and choosing the variable outside that domain falsifies the right-hand side, unless the left-hand side is unsatisfiable. For predicate arguments the test has no such semantic justification; it is a heuristic rejection, and no valid benchmark problem is rejected by it. It costs one traversal of each side.

## 6. The Countermodel

### 6.1 Role

A large part of the benchmark consists of invalid entailments, and many goals that the search generates internally are invalid as well (a wrong choice of disjunct, of witness or of unfolding). Proving that a goal is invalid would require a semantic argument; `xsearch` never attempts it. Instead it searches for a *countermodel*: a concrete heap, with concrete values for the goal's variables, that satisfies the left-hand side and does not satisfy the right-hand side. If one is found, the goal is invalid, since the evaluation of both sides on a concrete heap is exact for every construct the procedure accepts, and the tactic (or the current branch of the search) stops. If none is found, nothing follows. The search is incomplete by design, and every construct it does not support makes it answer "not found".

There is one countermodel procedure, `cmFind`. It has two modes. The full mode, with unfolding, runs once on the input goal, in `xsearch_cmodel` at the start of the macro, and on the candidate goals of the witness search, through `goalRefuted`. The depth-zero mode, `cmFind false`, keeps predicate atoms folded and runs at every node of the backtracking core (Section 12.3). A third entry point, `cmPureRefuted`, checks only pure facts and serves the pure prover (Section 7.1).

### 6.2 Reading predicate definitions

The countermodel and the segment engine read predicate definitions through one reader. `cmTable` lists, for each registered predicate, its arity and its body with the parameters as loose bound variables; `cmUnfold` instantiates the body at the arguments of an atom. `wgRead` produces a structured view of a definition:

```lean
structure WgRB where
  raw : Expr
  us : Array Expr
  items : Array Expr
  pures : Array Expr
  deriving Inhabited

structure WgRd where
  p : Name
  inst : Expr
  xs : Array Expr
  tys : Array Expr
  brs : Array WgRB
```

The body is split at the disjunction constant into branches (`wgBranches`). For each branch, `wgFlatEx` flattens the star structure into a list of items, opens existentials into local variables (the field `us`), and inlines *helper* predicates: non-recursive predicates with a single branch, whose body is substituted at the call (`wgHelperBody?`). The fuel of this inlining is the depth of the body expression, so it terminates without a fixed bound. The pure conjuncts of the branch are collected separately.

From this view, `wgLenOf` derives the *length structure* of each branch: the number of cells, the calls with their arguments as linear forms (`CmLin`, a map from variables to integer coefficients plus a constant), and the linear equations among the branch's pure facts:

```lean
structure WgLen where
  xs : Array FVarId
  brs : Array (Nat × Array (Name × Array (Option CmLin)) × Array CmLin × Bool)
```

One fixpoint routine, `wgLenFix`, iterates a monotone function over these branch structures until it stabilises; it is instantiated with different operations by the countermodel (minimum number of cells) and by the profile computation of the segment engine (the set of admissible lengths, Section 10.4). Before pass T0 of the third consolidation the two computations had separate tables; T0 merged them, and all 2294 lines of size and profile output were identical before and after.

### 6.3 Size summaries

For the depth-zero check the countermodel needs, for each predicate, the number of cells an instance can occupy. `cmSzTable` computes a summary per predicate:

```lean
structure CmSz where
  minC : Nat
  lin : Option (Nat × Int × Int)
```

`minC` is the least number of cells, the least fixed point of "cells of the branch plus the minima of the called predicates, minimised over branches", computed by `wgLenFix`. `lin` is an exact size `c · x_j + d` in terms of one parameter `x_j`, when one exists. `cmSzLin` finds it by eliminating the branch existentials with the branch's own equations (`cmElim`), so that the size of each branch is expressed in the parameters, and then solving the resulting linear system for `c` and `d` across all branches; a solution is accepted only if every branch satisfies it. For a list segment with a length parameter `n`, whose recursive branch has one cell and calls itself with `n - 1`, the exact size is `1 · n + 0`. For a doubly linked list with two-field cells it is `2 · n`.

### 6.4 Depth zero

A symbolic state of the left-hand side is a record of cells, pure facts and folded predicate atoms:

```lean
structure CmSt where
  cells : Array (Expr × Expr) := #[]
  pures : Array Expr := #[]
  chunks : Array Expr := #[]
  deriving Inhabited
```

`cmGen` generates states from a heap assertion. A star is processed left to right; a cell or a pure fact is appended to every state; an existential is opened with a fresh variable; a disjunction multiplies the states, of which at most `w` are kept; a predicate atom is either kept as a chunk (in fold mode) or unfolded (Section 6.5). In depth-zero mode the left-hand side is generated in fold mode, and each state is checked by `cmFoot`:

```lean
def cmFoot (szs : Array (Name × CmSz)) (facts : Array Expr) (st : CmSt) (rhs : Expr) : Bool := Id.run do
  let env := cmDetermine ((st.pures ++ facts).foldl (fun acc p => cmLinEqs p acc) #[])
  let val := fun (e : Expr) => (cmLinE e).bind fun l =>
    if l.m.toList.all (fun (f, _) => env.contains f) then
      some (l.m.fold (fun acc f c => acc + c * env.getD f 0) l.k)
    else none
  let ra := (Sep.Xsimpl.parseHstar rhs).filterMap (fun a =>
    if a.getAppFn.constName? == some ``HProp.hsingle then a.getAppArgs[1]? else none)
  if (List.range ra.length).any (fun i => (ra.drop (i + 1)).contains ra[i]!) then return true
  let mut ll := st.cells.size
  let mut lh : Option Nat := some st.cells.size
  for ch in st.chunks do
    let (l, h) := cmSzAtom szs val ch
    ll := ll + l
    lh := do return (← lh) + (← h)
  let (rl, rh) := cmSzE szs val rhs
  if let some h := lh then
    if rl > h then return true
  if let some h := rh then
    if ll > h then return true
  return false
```

`cmDetermine` derives the values of variables forced by linear equations among the state's pure facts and the hypotheses. The state's size is an interval: its cells count one each; a chunk counts its exact size when the size parameter has a determined value, and otherwise the interval from its minimum to infinity. The right-hand side's size interval is computed by `cmSzE`, which takes, for a disjunction, the minimum of the lower bounds and the maximum of the upper bounds. The state refutes the goal if the intervals are disjoint or if two top-level right-hand cells have syntactically the same address. A refuting state counts only if its pure facts, together with the arithmetic hypotheses, have a model; `cmPureModel` decides this with the solver of Section 6.5. Interval arithmetic rather than a constraint system is used because the right-hand size is typically a sum over several unknown lengths.

For example, take a list segment predicate `ls_len x y n` whose length parameter `n` counts its cells, so that its exact size is `n`. The goal `ls_len x y 3 ==> ls_len x y 2` has a left-hand state with one chunk of size exactly 3 and a right-hand side of size exactly 2, and is refuted without unfolding anything. The cost of this test does not depend on the magnitude of the literals; before pass 5b, when the check unfolded predicates, seven such invalid list problems with large literal lengths took 80 to 380 ms each, and afterwards 10 ms.

### 6.5 Concrete models

The full mode first runs the depth-zero test. It then requires that the goal be closed (every local declaration is a natural number or an integer; a proposition in the context disables this part, which is why `goalRefuted` first moves hypotheses into the left-hand side) and that the value type of the model be `Int`, and constructs concrete heaps. The construction has three stages.

**Unfolding policies.** A policy assigns an unfolding level to each top-level conjunct of the left-hand side. At level 0 a predicate atom takes the branches of its body that mention no registered predicate (or, if there are none, those that do not mention the predicate itself). At a level of 1 or more it takes the branches that mention some predicate, if there are any, and otherwise the same branches as at level 0. The atoms inside the chosen branch are generated one level lower (and never below 0), so that level 1 unfolds an atom once and closes the recursion with base branches, and level 2 unfolds it twice. The policies tried are: all atoms at level 1, all at 0, all at 2; for each predicate atom `i`, atom `i` at 0 and the others at 1, and atom `i` at 2 and the others at 1; and for each predicate atom `i`, atom `i` at 1 and every other predicate atom at 0 (only atom `i` is non-empty). The number of states per policy is bounded by the number of left-hand conjuncts plus one. States that are equal after renaming their fresh variables (`cmCanon`) are processed once.

**Values.** `cmPrepare` translates a state into an integer-indexed form: variables become indices, pure facts become terms of the small proposition language `CmP` and values of `CmV`. Variables related by equalities are grouped into classes (`cmBase`, `cmJoin`). `cmSolveM` then assigns values. Linear facts of the form `x + k = y + l`, `x + k ≤ y + l` and `x + k < y + l` become edges of a difference-constraint graph between classes, with an extra node for the constant zero; the Bellman–Ford iteration computes a solution or detects a negative cycle, in which case the state is infeasible. Classes that occur in no constraint receive their literal if they contain one, and otherwise pairwise distinct values far from every constrained value and every cell offset: `bs + wd · k` for `k = 1, 2, …`, where the spacing `wd` (also used as the base `bs`) exceeds the largest absolute constrained value plus the largest offset. Finally every pure fact is evaluated, the cells are evaluated to a heap, and a heap with two cells at one address is rejected. For example, the integer facts `k = n - 1` and `1 ≤ k` give the constraints `val k ≤ val n - 1`, `val n ≤ val k + 1` and `val zero ≤ val k - 1`, together with `val zero ≤ val c` for every constrained class `c`. Starting from all distances 0, the iteration stabilises at `zero = -2`, `k = -1`, `n = 0`, that is, at the values `k = 1` and `n = 2` relative to the zero node.

**Aliasing rounds.** Distinct fresh values make every unconstrained pair of pointers different. Many countermodels need two pointers to be equal instead. Round 0 uses the distinct assignment; round 1 merges, for each pair of variables of type `Nat` of the goal's context and nil (in this order, nil last), their two classes; round 2 merges a fresh variable that occurs in a cell of the state with a goal variable, with nil or with an earlier such fresh variable. Each candidate merge is a separate attempt. `cmDead` skips merges that a disequality among the state's pure facts, a clash of literals or two cells at the same offset from the two classes make impossible, and `cmMergeOf` computes the merged class structure. The rounds form the outer loop and the policies the inner one: every policy is tried with the distinct assignment before any merge is tried.

### 6.6 Checking the right-hand side

For each concrete heap the right-hand side is evaluated exactly. The bodies of the predicates reachable from the goal are compiled once per call into a small intermediate form:

```lean
inductive CmN where
  | star (a b : CmN)
  | emp
  | pure (p : CmP)
  | cell (a v : CmV)
  | ex (isNat : Bool) (slot : Nat) (sym : Bool) (pin : Option CmV) (body : CmN)
  | or (ds : Array CmN)
  | call (p : Nat) (args : Array CmV)
  | unk
  deriving Inhabited
```

`cmConsKI` decides whether the compiled right-hand side can consume the whole heap. A star consumes the heap in two parts; a cell consumes the cell at its address with a matching value; a pure fact is evaluated or added to the constraint store; a disjunction tries each disjunct; a call unfolds the callee's compiled body, with a fuel of twice the heap size; an existential is handled in one of two ways. If the existential is never used as an address (`cmAddrUse` and `cmMark` compute this for every slot of every body by a fixpoint), it is kept *symbolic*: it becomes a fresh variable of the constraint store `CmCs`, which records difference constraints and disequalities and is solved by the same Bellman–Ford iteration at the end. Otherwise it is enumerated over candidate values (`cmCandsI`): the value stored at the address it is pinned to when a cell determines it, and otherwise values near the heap's addresses and contents, the model's values and the values chosen so far on the path, within the largest cell offset, plus one fresh value.

The result is a pair of flags: whether a consumption was found, and whether the evaluation was incomplete (an unsupported construct, an exhausted fuel or step budget). The heap is a countermodel when no consumption was found and the evaluation was complete. The step budget of one check is the heap size plus one, times the size of the compiled program and right-hand side.

### 6.7 Deduplication and the cap

The same heap arises from many policies and merges. `cmFind` keeps a set of checked triples (heap, values of right-hand variables, model values), and `cmIsoKey` computes a key invariant under renaming of the unconstrained addresses, so that models equal up to such a renaming are checked once; on `qf_shls_entl` this reduced the right-hand checks from 26657 to 3798. The whole search stops after `cmVms` virtual milliseconds.

The cap is the one bound in the file that is not derived. Pass T0 measured the alternative of running the search to exhaustion under the derived bounds: all outcomes were unchanged, but the ten problems where the cap fires became three to seven times slower (`dll2-spaghetti-existential` from 521 to 3641 ms; the `tll_slk` problems from 61 to about 250 ms each), 3.6 s in total on `shid_entl`. Shares of the remaining time were also measured and rejected: the remaining time alone cost 3.3 s on `shid_entl`, a third of it divided by the number of policies cost 1.0 s on the original divisions, and a further division by the number of atoms lost `sll-vc01`. The structural reason is that on a valid goal the search has no early signal of validity; it only ends when its candidates are exhausted.

### 6.8 Example

Consider the invalid composition `p_ls x y ✶ p_ls y z ==> p_ls x z` of Section 1.1. The depth-zero test finds nothing: both sides have size at least 0 and no upper bound. With two predicate atoms there are nine policies, of which two produce states already seen; each policy produces one state. Under the first policy, "all atoms at level 1", each left-hand segment is unfolded once into its recursive branch and the recursive atom at level 0 into its base branch, which gives the state with cells `x ↦ u₁`, `y ↦ u₂` and the pure facts `x ≠ y`, `x ≠ 0`, `u₁ = y`, `y ≠ z`, `y ≠ 0`, `u₂ = z`. The classes are `{x}`, `{y, u₁}` and `{z, u₂}`. None of the facts is a linear constraint (the equations hold within classes, and disequalities are not edges), so in round 0 the three classes receive the values `bs + wd · k` with `wd = bs = 1`: `x = 2`, `y = 3`, `z = 4`, and the heap is `{2 ↦ 3, 3 ↦ 4}`. The right-hand side `p_ls 2 4` consumes it: its recursive branch takes the cell at 2, with the existential pinned to 3, then the cell at 3, and the base case `4 = 4` with the empty heap. The other policies give other acyclic segments from `x` to `z`, or the empty heap with `x = y = z`, which the right-hand side consumes as well; round 0 refutes nothing. Round 1 begins again with the first policy. The candidate merges are the pairs of `x`, `y`, `z` and nil, in order. The pair `x, y` is excluded by the fact `x ≠ y`; the pair `x, z` is not excluded by any disequality, literal or shared cell offset, and is the first live candidate. Merging gives `x = z = 2`, `y = 3` and the heap `{2 ↦ 3, 3 ↦ 2}`. Now `p_ls 2 2` requires the empty heap in its base branch and `2 ≠ 2` in its recursive branch; no consumption exists, the evaluation is complete, and the goal is refuted. The tactic fails at `xsearch_cmodel` without any search.

### 6.9 Derived checks

`goalRefuted` applies `cmFind` to the current goal of a search, after moving the hypotheses that are equations or disequalities into the left-hand side as pure facts and quantifying only the variables of the goal; the witness search uses it to discard a candidate tuple before any proof work. The check itself is done by `stmtRefuted`, which closes the statement over these variables and runs `cmFind` on it in an empty local context. `cmPureRefuted p` negates the arithmetic proposition `p` (`cmNeg`) and asks `cmPureModel` whether the hypotheses together with the negation have a model; if they do, `p` does not follow from the hypotheses and the pure prover abandons it without calling `omega`.

### 6.10 History

The countermodel was introduced in step 18 of the first climb as a pre-check: invalid time on the two original divisions fell from 360 s to 3.6 s. Step T6 compiled the check into the integer-indexed form and deduplicated states across policies. Pass 5a of the third consolidation added integer parameters with difference constraints, symbolic existentials, the policy "only atom `i` non-empty" and disjunctions, which turned six timeouts of satisfiable `dll-entl` problems into failures in 11 to 16 ms and cut the time of `qf_shidlia_entl` from 38.8 to 3.6 s; it also absorbed two older futility tests into `cmPureModel`. Pass 5b introduced the depth-zero mode with size summaries, replacing a separate cell-count test (`sizeGap`) and a separate refutation gate (`fastHopeless`). Pass 7 removed the fixed step and depth caps and found that a table of cell offsets had been computed over every predicate registered in the process, so that earlier problems influenced later ones; `cmReachTbl` now restricts the table to the predicates reachable from the goal.

## 7. The Shared Provers

The stages after the countermodel produce three kinds of side obligations over and over: pure arithmetic propositions, permutations of star chains, and allocation facts (an address is allocated in a heap assertion, or two addresses differ because they are allocated in separated parts). Pass 4 of the third consolidation reduced the many procedures that had accumulated for these obligations to one prover per kind. This chapter presents the three provers and the procedures that rewrite the left-hand side of a goal, which the later stages share.

### 7.1 The pure prover

Every pure obligation in `Sep/Xsearch.lean` is proved by `wgProve` (or by `wgSide`, which is `wgProve` without a heap):

```lean
def wgProve (p : Expr) (heap : Option Expr) : TacticM (Expr × Bool) := do
  let p ← instantiateMVars p
  if p.isConstOf ``True then return (mkConst ``True.intro, false)
  if let some (_, l, r) := p.eq? then
    if l == r then return (← mkEqRefl l, false)
  let raw ← wgRawHyps
  if let some pf ← wgHypMatch raw p then return (pf, false)
  wgProveH (← pureHyps raw) p heap

def wgSide (p : Expr) : TacticM Expr := do
  return (← wgProve p none).1
```

The rules are tried in a fixed order, from cheap and syntactic to expensive and semantic.

1. `True`, a reflexive equality, or a hypothesis matching the goal syntactically (`wgHypMatch`, which also accepts the symmetric form of an equality or a disequality).
2. The hypotheses are normalised once (`pureHyps`): conjunctions are split, an equality between pairs is split by injectivity, and projections of explicit pairs are reduced (`wgNorm`). Then `wgDirect` tries, in order: hypothesis matching on the normalised hypotheses; splitting a conjunction; evaluating a closed decidable arithmetic proposition with `decide`; unification with a fixed list of lemmas (`wgLemmaList`: `Ne.symm`, a few lemmas about `Nat`, and the `inv_*` lemmas of Section 4.9), under reducible transparency and after a structural pre-filter `wgShapeOk`, with premises discharged by hypotheses; a non-negativity chain (`arNonneg`, which proves `0 ≤ e` for sums of casts and non-negative literals by `Int.add_nonneg` and `Int.natCast_nonneg`); and definitional equality at reducible transparency.
3. A universally quantified goal is introduced, a propositional premise becoming a hypothesis. An equality between pairs is split by `Prod.ext`.
4. For a conjunction, each leaf is tried directly; the arithmetic leaves that remain are proved together by one call to `omega`.
5. A disequality between addresses, when a heap is given, is tried by separation (`wgNeHeap`, Section 7.3).
6. Before calling `omega`, `cmPureRefuted` (Section 6.9) checks whether the hypotheses admit a model in which the goal is false; if so the obligation is abandoned at once.
7. `omega` is called through `arOmegaCore` and `arOmegaIn`.

`arOmegaIn` is the single place where `omega` is called:

```lean
def arOmegaIn (g : MVarId) (div : Option Nat := none) : TacticM Unit := do
  setGoals [g]
  let nh ← g.withContext do return (← getLCtx).size
  let now ← vclock
  let gd ← globalDeadline.get
  let lim := (if gd > now then (gd - now) / (div.getD (nh + 2)) else 1) * hbPerVms
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := lim }) do
      let some g' ← g.falseOrByContra | return
      g'.withContext do
        let hyps := (← getLocalHyps).toList
        Lean.Elab.Tactic.Omega.omega hyps g')
    (fun _ => throwError "omega: budget")
  setGoals []
```

It calls the `MetaM` core of `omega` directly instead of the tactic (the tactic adds an auxiliary declaration to the environment on every call), with a heartbeat limit equal to the remaining time divided by the number of hypotheses plus two, and turns the limit exception into an ordinary failure. `arOmegaCore` tries up to three contexts in turn: the goal with all propositional hypotheses cleared, when the syntactic linear normaliser `arTriv` shows the goal to be an identity; the goal with only the hypotheses whose variables all occur in the goal (`arTrim` without closure); and the goal with the hypotheses connected to the goal through shared variables (`arTrim` with closure). Feeding `omega` a trimmed context matters: the local context of a search goal contains many facts about unrelated addresses, and `omega` case-splits on every disequality it is given. Before the heartbeat limit and the trimming were introduced (stage 5 of the first consolidation phase), a single `omega` call on one of the `spaghetti` problems took 187 s.

The retry ladder is a measured exception to the rule "no repeated calls per obligation". Pass T0 tried deciding the context once and calling `omega` once per obligation; the number of calls fell from 2768 to 2077 with no change of outcome, but `shidlia_entl` became 3 % slower, because the first, smaller context usually succeeds faster than one call with the full connected context.

The tactic syntax `xsearch_omega` is elaborated to `wgCloseGoal`, which proves the main goal with `wgSide`; it is the form in which other tactics invoke the pure prover.

### 7.2 The permutation prover

```lean
def provePerm (A B : Expr) : MetaM (Option Expr) := do
  let A ← instantiateMVars A
  let B ← instantiateMVars B
  let inst := (← whnfR (← inferType A)).appArg!
  let (S, ps) ← flatEq A
  let (T, pt) ← flatEq B
  unless S.length == T.length do return none
  let sS := starOf inst S
  let sT := starOf inst T
  let some pm := permListPfS inst S sS T sT | return none
  let hty := mkApp (mkConst ``HProp) inst
  let oe := fun (x y h : Expr) => mkAppN (mkConst ``himpl_of_eq) #[inst, x, y, h]
  let tr := fun (x y z p q : Expr) => mkAppN (mkConst ``HProp.himpl_trans) #[inst, x, y, z, p, q]
  let pa := if sS == A then pm else tr A sS sT (oe A sS ps) pm
  if sT == B then return some pa
  return some (tr A sT B pa (oe sT B (mkAppN (mkConst ``Eq.symm [1]) #[hty, B, sT, pt])))
```

`provePerm A B` proves `A ==> B` when the two stars are permutations of each other. `flatEq` flattens each side into a list with an equality proof (returning a reflexivity proof when the side is already a right-nested chain), and `permListPfS` builds the permutation proof by repeatedly pulling the next atom of the target to the front of the source with `permPullPf` (a chain of `perm_swap` steps under frames) and framing it. The proof is quadratic in the number of atoms, which is acceptable at the sizes that occur inside the engine; the large permutations of the benchmark are handled by `xsimpl`'s certificate of Section 3.7. Before pass 4 there were five permutation procedures (`provePermCore` with an `xsimpl` fallback, `provePermFast`, `provePermFlat`, `acPermImp`, and a cache with a cap of 48 atoms); after their replacement no problem needed a fallback.

### 7.3 The allocation prover

Allocation facts are needed for the disequalities that separation implies and for the side conditions of segment retargeting (Section 4.2). One recursive walk finds where a location is allocated: `wgAllocGo p H` descends through stars, existentials and disjunctions (both disjuncts must allocate `p`) to a cell at `p`, and returns a proof of `hasLoc p H` built from `hasLoc_single`, `hasLoc_star_l`, `hasLoc_star_r`, `hasLoc_hexists` and `hasLoc_disj`. A `hasLoc` hypothesis in the context is used directly. For any other atom the walk calls a hook, `wgLocHook`, which the segment engine sets to `wgLocAtom`: a segment with at least one step allocates its start (`hasLoc_wseg_pos`), a segment whose start differs from its end allocates its start (`hasLoc_wseg_ne`), and a predicate atom allocates what its abstraction allocates (`hasLoc_mono` applied to the abstraction lemma). The hook exists because the allocation prover is defined before the engine's lemma builders in the file, and Lean requires definitions before use; the reference is set by an `initialize` declaration after the builders.

On top of the walk sit three entry points. `wgAlloc p H` proves `hasLoc p H`. `wgApart p q H` proves `neLocs p q H` by finding the paths to the cells allocating `p` and `q` and combining them at the star where the paths diverge (`wgPathNe`, with `neLocs_star`), or from a disequality hypothesis (`neLocs_const`). `wgNeHeap lhs a b` proves `holdsP (a ≠ b) lhs`, either by `wgApart` or, when only `a` is allocated by a cell, by `ne_far`: `a` is allocated and nonzero, and `b` is safe far in the rest (`wgFarHook`, set to `wgSafeFar`, Section 10.10). `wgAllocGoal` applies the right entry point to a goal of either form.

### 7.4 Rewriting the left-hand side

The engine and the lemma builders transform goals by applying entailment lemmas to parts of the left-hand side. The common operation is `arRwLhs As lem`. Given atoms `As` of the left-hand side and a lemma `lem : lemL ==> lemR` whose spatial atoms are (up to definitional equality) the atoms `As`, it replaces the goal `lhs ==> rhs` by `lemR ✶ rest ==> rhs`, where `rest` is the left-hand side without `As`. Pure atoms required by `lemL` are taken from the left-hand side when present; otherwise they are proved by `wgProve` with the left-hand side as heap and inserted by `pure_l_intro` or `pure_l_of_holds`, so that the chain stays flat. The left-hand side is then brought into the shape `lemL ✶ rest` by one call to the permutation prover, and excess pure atoms are dropped with `star_pure_drop`. Existentials at the front of `lemR` are introduced, and the new variables are returned. If the direct construction fails, `arRwLhs` falls back to `xsimpl`, except while a lemma is being built (the flag `lemBuilding`), where it fails instead; in pass 2a of the third consolidation this flag was used to establish that no lemma construction needs `xsimpl`.

Several smaller procedures complete the set. `arIntroLhs` introduces the existentials of the left-hand side by direct proof terms, pulling nested existentials outward with `exPull`. `arIntroFacts` adds the pure facts of the left-hand side to the local context through `himpl_of_holds`, splitting conjunctions and pair equations. `arOpenGoal` and `arOpen` replace the leading existentials of the right-hand side by metavariables; `arOpenDeep` also opens existentials nested in stars. `wgSubstAll` substitutes equations between variables (`fastSubstVars`). `wgNorm` reduces projections of explicit pairs and beta-redexes, which arise whenever a carrier's state is a tuple.

Two further procedures assign metavariables. `arAssign L rs` matches each right-hand atom containing metavariables against the left-hand atoms by unification, in the order of a ranking of left-hand atoms that a later section (11.2) defines, backtracking over the choices. `arSolve n0 pieces rpures` assigns unknown lengths: given the total length `n0` of a left-hand chain and the right-hand pieces with their lengths (literals, expressions, or metavariables), it first uses equations among the right-hand pure facts, then tries each unknown in turn as the one that takes the slack `n0 - Σ others` while the other unknowns take their minimum, and accepts the first assignment for which the pure prover proves the sum equation, the lower bounds and the right-hand arithmetic facts.

### 7.5 Unfolding and distribution

`rewriteOcc entries occ` rewrites one occurrence of a predicate atom with its unfold equation (`eqProofFor` finds the equation instance by unification) and then distributes the resulting disjunction with `xsearch_distr`. `distrCore` first replaces the benchmark's disjunction constant by `hdisj` (`replaceHor`), then rewrites the goal so that every disjunction is outermost: `hdisj` is pushed out of stars and existentials by `hdisj_star_l`, `hdisj_star_r` and `hdisj_hexists`, stars are reassociated, and trivial pure facts are normalised. The rewriting is done by the native normaliser `DistrCtx.norm`, which returns an equality proof assembled from congruences; it is used on the fragment `distrSafe` and falls back to `simp only` with the same lemmas outside it. After distribution, a left-hand disjunction can be split by `hdisj_elim` and a right-hand one decided by `hdisj_left` or `hdisj_right`.

## 8. The Cache Reset and the Fast Path

### 8.1 `xsearch_start`

After the countermodel search, `xsearch_start` resets the per-problem state: the failure memo of the core, the forced-depth counter, the flag that marks lemma building, and the caches of invariants, flat and recursive predicate tests, derived invariants, size summaries, carriers, profile groups, lemmas, used-constant lists and maps between carriers. The rule that no cache survives from one problem to the next was introduced in step T6 of the first climb, after nine caches were found to leak across problems.

### 8.2 The fast path

After `xsearch_start`, and before any normalisation, the macro tries to prove the goal with `xsimpl` alone:

```lean
      | (xsimpl_core
         all_goals (try xsimpl_clean)
         xsearch_pure
         done)
```

Many entailments of the benchmark need no reasoning about inductive predicates: both sides consist of cells, pure facts and predicate atoms that occur identically on both sides, and cancellation leaves only pure side conditions. For these goals the fast path is the whole proof. `xsimpl_core` cancels what it can; `xsimpl_clean` closes residual entailments whose sides are definitionally equal or that are hypotheses; `xsearch_pure` disposes of the remaining pure goals. For each remaining goal, `xsearch_pure` first tries `contraClose`, which closes any goal, entailment or not, when the context contains `a ≠ a` or `False`. Entailments are then left alone; on every other goal it tries `rfl`, `assumption`, `trivial`, `Ne.symm` with an assumption, and finally `xsearch_omega` (the pure prover). If any goal remains, `done` fails, and the alternative branch of the macro starts again from the original goal.

As an example, take `⌈x ≠ 0⌉ ✶ x ↦ y ==> ∃✶ u, x ↦ u ✶ ⌈x ≠ 0⌉`. `xsimpl` introduces the hypothesis `x ≠ 0`, replaces `u` by a metavariable `?u`, turns `⌈x ≠ 0⌉` on the right into a side goal `x ≠ 0`, and cancels `x ↦ y` against `x ↦ ?u`, assigning `?u := y`. The residual `emp ==> emp` is closed by reflexivity and the side goal by `assumption`.

Before pass T0 the fast path also unfolded predicates, under a per-problem counter of unfoldings. Region A of T0 removed the unfolding step and the thirteen helpers that served it; the two problems that had needed it (`append_dll_slk-1` and `-7`) are now handled by the forced-determination rule of `xsearch_macros` (Section 9.3).

## 9. The Rest of the Prefix Normalisation

If the fast path fails, the second branch of the macro normalises the original goal before the engines run. The steps are cheap and each is wrapped in `try`, so a step that does not apply has no effect.

### 9.1 Substitution of equalities

`xsearch_eqsubst` looks for pure facts `⌈a = b⌉` on the left-hand side in which one side is a variable. For each such fact not already in the context, it adds the equation as a hypothesis through `himpl_of_holds` (the left-hand side is kept unchanged; `holdsPf?` proves that the fact holds of every heap satisfying the left-hand side), and then substitutes all equations between variables with `fastSubstVars`. After substitution the pure fact has become `⌈e = e⌉`.

### 9.2 Trivial pure facts

`xsearch_trivpure` replaces every pure fact `⌈a = a⌉` or `⌈True⌉` on either side by `emp` (lemma `hpure_true`) and removes the resulting `emp` conjuncts. It runs once after the substitution and once after the unfolding of the next section, which can expose further trivial facts.

For example, `⌈x ≠ 0⌉ ✶ x ↦ y ✶ ⌈y = z⌉ ✶ p_ls z 0 ==> p_ls x 0` becomes, after substitution of `z` by `y` and removal of `⌈y = y⌉`, the goal `⌈x ≠ 0⌉ ✶ x ↦ y ✶ p_ls y 0 ==> p_ls x 0`, with the hypothesis `y = z` gone into the substitution.

### 9.3 Non-recursive predicates and forced determination

SL-COMP problems often define non-recursive predicates in terms of others: a predicate that is a single cell with some pure facts, or a wrapper such as "a doubly linked list whose two ends are linked to each other by existentials". `xsearch_macros` unfolds such definitions. It first classifies the registered predicates:

```lean
elab "xsearch_macros" : tactic => withMainContext do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let heads := entries.map (·.headFn)
  let mut ms : Array Name := #[]
  let mut ls : Array Name := #[]
  let mut rs : Array Name := #[]
  for e in entries do
    let ty := (← getConstInfo e.lemmaName).type
    let k ← forallTelescopeReducing ty fun _ concl => do
      match concl.eq? with
      | some (_, _, body) =>
          if isHorConst body then pure 0
          else if (collectOccs heads body #[]).isEmpty then pure 2
          else if ← isRecPred e.headFn then pure 0
          else pure 1
      | none => pure 0
    let det ← forallTelescopeReducing ty fun _ concl => do
      match concl.eq? with
      | some (_, _, body) =>
          let (bd, n) := exPeel body
          pure ((List.range n).all (fun i => bvarDetermined bd i))
      | none => pure false
    if k == 2 && !ms.contains e.headFn then ms := ms.push e.headFn
    if k == 1 && !ls.contains e.headFn then ls := ls.push e.headFn
    if det && !rs.contains e.headFn then rs := rs.push e.headFn
```

A predicate is a *macro* (class 2, list `ms`) if its body is not a disjunction and mentions no registered predicate; it is a *wrapper* (class 1, list `ls`) if its body is not a disjunction, mentions predicates, and the predicate is not recursive. A predicate is *determined* (list `rs`) if every existential at the front of its body is fixed by a pure equation to a term that mentions no other existential (`bvarDetermined`). The procedure then repeats the following choice until nothing applies:

1. unfold the first occurrence of a macro anywhere in the goal;
2. otherwise, unfold the first left-hand occurrence of a wrapper that does not occur on the right;
3. otherwise, unfold the first right-hand occurrence of a determined wrapper that does not occur on the left;
4. otherwise, try forced determination on the right-hand occurrences of wrappers that are not determined and, after the normalisation described below, do not occur on the left.

The rules are asymmetric for a reason. Unfolding on the left loses nothing: the existentials of the body become local variables. Unfolding on the right creates existentials that need witnesses, and choosing them early can be wrong; it is done only when the witnesses are forced. Rule 3 covers witnesses forced by equations in the body itself. Rule 4, `heapDet`, covers witnesses forced by the left-hand heap. It is applied after the left-hand side has been normalised (existentials introduced by `arIntroLhs` and equations substituted), and only when the normalised right-hand side contains no existential anywhere. The existentials of the wrapper's body are replaced by metavariables, and a binder is declared determined when

- it is one side of a pure equation of the body whose other side has no undetermined binder, or
- it is the value of a cell of the body whose address has no undetermined binder and coincides syntactically with the address of exactly one left-hand cell; the binder's value is then that cell's value.

Determinations are substituted into the remaining body, which may determine further binders, until nothing changes. If every binder is determined, the occurrence is unfolded, its existentials are moved to the front, and `witInst` instantiates them with the determined values. This is one witness decision, made by the same instantiation procedure that the witness search uses (Section 11.1).

As a small example, let `cyc x` be the non-recursive predicate `∃ u, ⌈x ≠ 0⌉ ✶ x ↦ u ✶ p_ls u x`, a wrapper that is not determined by equations. In the goal `⌈x ≠ 0⌉ ✶ x ↦ y ✶ p_ls y x ==> cyc x`, the binder `u` is the value of the body's cell at the address `x`, which has no undetermined binder and coincides with the address of exactly one left-hand cell, `x ↦ y`. Rule 4 therefore determines `u := y`, unfolds `cyc x` and instantiates the existential, leaving the goal `⌈x ≠ 0⌉ ✶ x ↦ y ✶ p_ls y x ==> ⌈x ≠ 0⌉ ✶ x ↦ y ✶ p_ls y x` (with the hypothesis `x ≠ 0` added by the normalisation), whose two sides consist of the same atoms. Before the macro step the fast path could not prove the goal: under cheap cancellation `xsimpl` does not compare `cyc x` with atoms of other heads, and it unfolds no predicate.

In the two problems `append_dll_slk-1` and `-7`, the right-hand side is a wrapper whose two existentials are linked to each other and fixed only by the heap: one is the successor stored in a left-hand cell, the other is determined through an equation with the first. Rule 4 determines both. Two alternative forms of the rule were measured and rejected in pass T0: deciding on the left-hand side before normalisation could not determine the second binder, because the left-hand equation was still under an existential; and taking as a determination the candidate of a binder when the ranking of candidates by matching arguments (which Section 11.2 defines) proposes exactly one lost `lsegex4_slk-1`, where the candidate was wrong.

### 9.4 Pure facts and disequalities

`xsearch_pfacts` adds left-hand disequalities `⌈a ≠ b⌉` to the context, again through `himpl_of_holds`, when one of the two sides is an argument of a predicate atom and not the address of a cell; these are the facts that later reasoning about segment ends needs as hypotheses (the pure prover and the countermodel read hypotheses, not heap assertions). `xsearch_facts` adds, for every pair of distinct addresses of top-level left-hand cells, the hypothesis that they differ. The proof of each disequality is built by the allocation prover's path construction (`wgPathNe`), and all of them are introduced by one proof term with `himpl_of_neLocs`. A former limit of 32 cells on this step was removed in pass 7.

## 10. The Segment Engine `xsearch_wseg`

### 10.1 The idea

The segment engine proves entailments in which predicate atoms on the left must be recombined into differently shaped predicate atoms on the right: joining segments, splitting a segment at a point determined by lengths, folding cells into a segment, converting between predicates that describe the same cells. Instead of reasoning about each predicate separately, it relates every predicate to the carrier `wseg` of Chapter 4 and works with segments of the carrier. One run has three phases.

1. **Parse.** For each predicate occurring in the goal, derive a carrier: a state type, a cell relation, the positions of the start and end states among the predicate's arguments, the minimal step count, and side information. The derivation is cached per predicate.
2. **Plan.** For one carrier, find a chain of left-hand pieces (abstracted predicate atoms and single cells) from a start state to an end state and a matching chain of right-hand pieces with the same ends, such that the lengths are consistent.
3. **Execute.** Rewrite the left-hand pieces into carrier segments with the abstraction lemmas, join them into one segment, split it into the right-hand pieces, rewrite the right-hand atoms into carrier segments with the concretisation lemmas, and match the segments.

The proof term is built entirely by instantiating theorems of `Sep/SegC.lean`. A run that leaves unmatched right-hand atoms continues with a new round on the residual goal.

The entry tactic is short:

```lean
elab "xsearch_wseg" : tactic => do
  witDetermined
  wgPass
```

`witDetermined` (Section 11.1) first instantiates right-hand existentials that are fixed by equations; `wgPass` (Section 10.11) does the rest.

### 10.2 The carrier record

The result of the parse is a record `WgP`:

```lean
structure WgP where
  pname : Name
  inst : Expr
  tys : Array Expr
  mov : Array Nat
  ai : Option Nat
  sty : Expr
  cLam : Expr
  preLam : Expr
  nextLam : Expr
  usTys : Array Expr
  endSpec : Array (Option Nat × Option Expr)
  kmin : Nat
  stepIdx : Nat
  tailLam : Option Expr := none
  relLam : Expr
  invLam : Expr
  profLam : Option Expr := none
  cellData : Array (Expr × Expr × Array Expr × Expr × Nat) := #[]
  wLam : Option Expr := none
  disj : Nat × Nat := (0, 1)
  via : Bool := false
  unitW : Bool := true
  cst : Array Nat := #[]
  gloc : Array (Nat × Nat) := #[]
  gprev : Array (Nat × Nat × Nat) := #[]
  prevAdr : Array (Nat × Nat) := #[]
  rels : Array (Nat × Int × Int × Bool) := #[]
  pg : Bool := false
  baseIdx : Nat := 0
  stepW : Array (Nat × Option Nat × Expr) := #[]
  baseW : Option (Array (Expr × Array Expr × Expr) × Array Expr × Option (Array (Nat × Nat × Nat))) := none
  viaW : Array (Nat × Nat × Nat × Array Expr × Expr × Option (Array (Nat × Nat))) := #[]
  deriving Inhabited
```

The fields have the following meaning, illustrated on the list segment `p_ls a b` (Section 4.1) and on the doubly linked list `dll hd p tl n len` (Section 1.1).

- `pname`, `inst`, `tys`: the predicate, the instance of the class `Params` (which fixes the type of values stored in cells), and the types of its parameters.
- `mov`: the indices of the parameters that form the state, in order. For `p_ls` these are `[0, 1]`; for `dll` they are `[0, 1]` (the current node and its predecessor).
- `ai`: the index of the counter parameter, if any: an integer parameter that the recursive call decreases by the step's weight. For `dll` it is `some 4` (`len`); for `p_ls` it is `none`.
- `sty`: the state type, the tuple of the types of the `mov` parameters.
- `cLam`: the cell relation `fun s s' w => …`; `preLam` and `nextLam`: the cell's heap assertion and the successor state as functions of the state components and the cell's own existentials, whose types are `usTys`.
- `endSpec`: for each state component, where its end value comes from: a parameter (`some f`), a constant (`none, some c`), or nowhere (`none, none`), in which case the end component is *missing* and becomes part of the remainder of Section 4.5. For `p_ls` the end state is `(b, b)`; for `dll` it is `(n, tl)`.
- `kmin`: the number of cells in the base case (0 for `p_ls`, 1 for `dll`); `baseIdx` and `stepIdx`: the indices of the base branch and of the first step branch in the body.
- `tailLam`: the tail, for base cases that contain material other than carrier cells.
- `relLam`: a pure relation that every cell implies (unit weight or non-negative weight, linear relations between consecutive integer components, non-nil previous addresses); `invLam`: the invariant of every segment that follows from it by `wseg_inv`.
- `profLam`: the length condition when it is not `kmin ≤ k`, namely a profile `phiI` (Section 4.4).
- `cellData`: for predicates with several step branches, one *view* per branch (its cell assertion, successor state, existential types and weight); the cell relation is then the disjunction (`hdisj`) of the views. `wgViews` turns such a record into one record per view, in which `preLam`, `nextLam` and `usTys` are the view's, `wLam` is the view's weight and `disj` is the pair (view index, number of views) that selects the view inside the disjunction.
- `via`: the carrier is borrowed from another predicate (Section 10.4).
- `unitW`: every step has weight one, so the total weight equals the step count.
- `cst`: the indices of constant state components (the end `b` of `p_ls`); `gloc`: pairs (constant component, address component) such that each cell guards its address against the constant (`s.1 ≠ s.2` for `p_ls`); `gprev` and `prevAdr`: components holding the previous cell's address when cells are also guarded against it, as in doubly linked lists whose cells carry a guard `prev ≠ end`; `rels`: linear relations between consecutive integer components, such as `s'.d ≤ s.d` for sorted data.
- `pg`: the carrier comes from the profile route.
- `stepW`, `baseW`, `viaW`: witnesses recorded during the parse, from which the lemma builder obtains the existential witnesses of each branch without search (Section 10.6).

`wgPOf` computes the carrier of a predicate, trying three derivations in order, and caches the result: the profile route `wgParseProf` (Section 10.4), the generic derivation `wgCarrier` (Section 10.3), and the borrowed derivation `wgParseVia` (Section 10.4). All three read the definition through `wgRead` (Section 6.2); before pass 3 of the third consolidation there were five separate readers.

### 10.3 Deriving a carrier

`wgCarrier` derives a carrier from the reader's view of a definition. It requires exactly one base branch (a branch without a recursive call) and at least one step branch, each step branch containing exactly one recursive call with all arguments. The derivation proceeds as follows.

1. **Counter.** An integer parameter `i` is a counter if the base branch has a pure fact mentioning only `i`, and in every step branch the recursive call's argument at position `i` is an existential `a` related to `i` by a linear equation in which `i` and `a` have opposite unit coefficients (`wgCntW`). The equation gives the step's weight `w = i - a` as an expression; if every step's weight is the literal 1, the carrier has unit weight. For `dll`, the base fact `len - 1 = 0` mentions only `len`, and the step fact `k = len - 1` gives weight 1.
2. **Moving and constant components.** The moving components are the parameters, other than the counter, whose argument in the recursive call differs from the parameter itself; they must be the same in every step branch and have type `Nat` or `Int`. A fixed parameter of type `Nat` that a step branch mentions outside the recursive call and outside the counter's equations is *promoted* to a constant component. The end parameter `b` of `p_ls` is promoted because of the guard `⌈a ≠ b⌉`. Without promotion, the cell relation would mention a parameter that is not part of the state, and the carrier would not be a closed description of a step.
3. **Views.** For each step branch, the cell's heap assertion consists of the branch's items other than the recursive call, with pure facts that mention the counter or unpromoted fixed parameters removed (they are accounted for by the weight and by the invariant). The successor state is read off the recursive call's arguments. The cell relation is the existential closure over the branch's remaining existentials of the heap assertion together with the pure fact `s' = successor ∧ w = weight`; with several step branches it is the disjunction of these views.
4. **Side relations.** Guards of the form `constant ≠ address` give `gloc`; linear relations between an integer component and its successor give `rels`; a component whose successor value is the current cell's address, when the address is guarded by `≠ 0` and the component by a guard against another term, gives `prevAdr` and `gprev`. From these, `relLam` and `invLam` are assembled. The invariant states `n = k` (or `0 ≤ n` for non-unit weights), the relations scaled by `k`, `k = 0 → s = t` for related components, and `k = 0 ∨ prev ≠ 0` for previous-address components.
5. **Base absorption.** If the base branch contains cells, the cell pattern of the first view is matched repeatedly against them, starting from the start state, until no cell matches; the number of matched cells is `kmin`, the state reached determines the end specification, and the unmatched base items (with the pure facts that mention only their variables) form the tail. For `dll`, one base cell `hd ↦ n ✶ (hd + 1) ↦ p` matches the pattern with successor `(n, hd)`, and the base equation `hd = tl` turns the second component into the parameter `tl`: `kmin = 1` and the end state is `(n, tl)`. If the base branch has no cells, the end specification is read from its equations (`a = b` gives the end `b` for the start `a`). Otherwise the base branch becomes the tail of a zero-length segment.

The two examples give the following abstractions, in which `c` stands for each predicate's derived cell relation:

```
p_ls a b                ==> ∃ k n, wseg c k n (a, b) (b, b) ✶ ⌈0 ≤ k⌉
dll hd p tl n len       ==> ∃ k, wseg c k len (hd, p) (n, tl) ✶ ⌈1 ≤ k⌉
```

The two-cell list of Section 1.1 is a segment of this carrier with `k = 2` from `(a, p)` to `(n, b)`.

### 10.4 Profile carriers and borrowed carriers

**Profile carriers.** Groups of predicates whose bodies are paths of one cell template between two location parameters, such as the even and odd lists, take the profile route. `wgPathInfo` accepts a definition when it has two `Nat` parameters, every branch is a path from the first parameter to the second through cells of one template `C x u` (a points-to fact whose address is guarded against at most one term, such as `⌈x ≠ 0⌉`) and calls of two-argument predicates, and the only other pure fact is the base equation between the two parameters. `wgPGBuild` collects the group by following the calls, builds the branch data `B`, and computes each member's length set up to a window `W = 4 · (total number of items) + 4` with `wgLenFix` over Boolean tables (`wgPGTable`). `wgPhi` reads off the threshold `m` (the least admissible length in the window), the period `p` (the least `p ≤ W / 4` such that the table is `p`-periodic from `m` to the end of the window) and the residues (the `r < p` with `m + r` admissible). Then `pChkA` is evaluated natively; if it succeeds, `wgPGCert` constructs the certificate of `pChkC`, and `pChkC` is evaluated natively on it. If any of the three steps fails, the route is abandoned. `wgPGCert` proceeds as follows.

- *Ranks.* A member `j` must have a higher rank than a member `q` when `j` has a branch without cells that calls `q` and whose other calls can all have length 0; then a length of `j` can be derived from an equal length of `q`. The ranks are the lengths of the longest such dependency paths; a cycle makes the construction fail.
- *Spans and big rules.* With `L` the least common multiple of the periods, the span of member `j` is the least multiple `p · t` with `t ≤ L` such that every residue class modulo `p · t` that the profile contains has a big rule (`wgPGRule`): the first branch, the first hole position and the first choice of fixed lengths (admissible lengths up to `W`, found by `wgPGFixed`) that satisfy the conditions of Section 4.4.
- *The bound.* `N` is the largest of 1, `d + m_{q0}` over the chosen big rules, and `c + 1` over their fixed lengths `c`; the construction fails if `N > W`.
- *Small entries.* For each admissible `n < N`, the first branch whose calls can split the length `n` minus its cells among admissible callee lengths that are smaller in (length, rank) (`wgPGSplit`). Otherwise the abstraction lemmas of all members are built at once by `wgPGAbsAll`, one `lfpG_induct` per group with a case split over the sum type of the group's arguments, and the concretisation lemma by `wgPGConcAll`. `wgParseProf` then produces a carrier record with the flag `pg`, the state type `Nat`, the cell relation `pCell C`, unit weight, `kmin` equal to the threshold, and `profLam` when the period is not 1.

The list segment `p_ls` does not take this route: its cells carry two guards, `a ≠ b` and `a ≠ 0`, against different terms, and `wgPathInfo` rejects it. It takes the generic route with a constant component instead.

**Borrowed carriers.** Some predicates are not paths of their own cells but can be seen as paths of another predicate's carrier. A binary tree `tree x` is a path from the root to nil along one child at each node, with the subtree at the other child as a payload of the cell; this is the cell relation of a tree segment `tseg x y`, whose views (hole in the left subtree, hole in the right subtree) are exactly such cells. `wgParseVia` accepts a predicate `p` whose parameters are exactly a `Nat` start `x` and optionally an `Int` size, with exactly one non-recursive branch, consisting of pure facts only, and at least one recursive branch. The base branch may fix `x` only by an equation `x = c` with a closed term `c`. The procedure scans the registered predicates in order and derives, by the generic route `wgCarrier`, the carrier of each; it takes the first carrier that has one moving component, several views of which at least one mentions `p`, and a counter exactly when `p` has a size parameter. For each branch of `p`, each view of the carrier and each recursive atom of the branch, it then tries to unify the spatial atoms of the view's cell with the atoms of the branch, with the chosen recursive atom as the continuation of the path (its first argument must be the view's successor state). Each successful match is recorded in `viaW` as a tuple of the branch index, the view index, the index of the recursive atom, the witnesses of the cell's existentials and the weight (both as functions of the parameters and the branch's existentials), and an inverse map that expresses each existential of the branch as a cell existential or an argument of the recursive atom. The result is the other predicate's carrier with the flag `via`, the predicate's own name and parameter types, the end fixed to the constant `c` of the base equation (for a tree, nil) or left open when the base has no such equation, and `kmin = 0`. The carrier is returned even if no match was recorded. Its abstraction is proved with `lfpG_induct_with` (Section 4.9), because the off-path children are kept as predicate atoms of the payload, which the inductive hypothesis must also describe as predicates.

### 10.5 The lemma cache

Every lemma of the engine is built by a function `wg…Of` that calls `wgLem` with a key:

```lean
def wgLem (key : String) (build : TacticM Expr) : TacticM (Option Expr) := do
  if let some r := (← wgLCache.get).findSome? (fun e => if e.1 == key then some e.2 else none) then
    match r with
    | none => return none
    | some e =>
      if ← wgValid e then return r
      wgLCache.modify (·.filter (·.1 != key))
  let saved ← getGoals
  let st ← saveState
  let old ← lemBuilding.get
  lemBuilding.set true
  let r ← try withLCtx {} {} (some <$> build) catch _ => do st.restore; pure none
  lemBuilding.set old
  setGoals saved
  wgLCache.modify (·.push (key, r))
  return r
```

A lemma is built once per problem in an empty local context, so that it is a closed term that can be reused at any goal. Failures are cached as well. `wgValid` checks that every constant used by a cached term still exists, since the search restores saved states and an earlier state may lack declarations created later. The flag `lemBuilding` is set during construction (Section 7.4). The lemma kinds and their keys are:

| Key | Built by | Statement |
|---|---|---|
| `abs:P` | `wgBuildAbs` | `P xs ==> ∃ k …, wseg … ✶ tail ✶ ⌈condition k⌉` |
| `conc:P` | `wgBuildConc` | `condition k → (wseg … ✶ tail ==> P xs)` |
| `inv:…` | `wgBuildInv`, `wgBuildInvPG` | `holdsP (invariant k s t n) (wseg c k n s t)` |
| `ci:…` | `wgBuildCI` | one view's cell assertion entails a one-step segment |
| map (cache `wgMCache`) | `wgBuildMap` | a segment of one carrier entails a segment of another (`wseg_map` or `wseg_rev`) |
| `ret:…`, `retp:…` | `wgBuildRet`, `wgBuildRetPrev` | retargeting a constant component (`wseg_retarget`, `wseg_retarget_prev`) |
| `hc:…` | `wgBuildHc` | each cell allocates the address component |
| `bk:…` | `wgBuildBk` | a segment whose last cell's address is allocated in the frame is empty (`wseg_bk_zero`) |
| `lo:P` | `wgBuildLo` | `holdsP (kmin ≤ len) (P xs)` for counter predicates |
| `fact:P` | `wgBuildFact` | `holdsP (∃ k …, invariant ∧ condition) (P xs)` |

`wgPrebuild` builds the lemmas needed by a chosen plan before the plan is executed; the planner itself builds nothing. This order was established in stage 3 of the first consolidation phase; before it, lemmas were built while candidate plans were explored.

### 10.6 Building abstractions and concretisations

**The witnessed branch closer.** The per-branch obligations of `gAbs` and `gConc` (Sections 4.5 to 4.7) are entailments between one branch of an unfolded definition and one chain of the carrier, or the converse. They are proved by one procedure, `wgClose`, which takes its existential witnesses from the carrier record instead of searching for them:

```lean
inductive WgW where
  | ex (e : Expr)
  | sel (d : Nat)
…
def wgClose (inst lhs tgt : Expr) (plan : Array Expr → Expr →
    TacticM (Expr × List WgW × (Expr → Expr → Option (Expr × Expr)) × Option (Expr × Expr × Expr))) : TacticM Expr :=
  wgOpenL inst tgt lhs #[] fun T vs => do
    let (R, ws, leafF, post) ← plan vs T
    let pf ← wgOpenR inst T R ws fun R' => wgCloseFin inst T R' leafF
    return match post with
      | some (mid, en, p) => wgTrans inst T mid en pf p
      | none => pf
```

`wgOpenL` introduces the existentials of the left-hand side as local variables, inlining helper predicates in the same order as the reader does, and calls `plan` with the introduced variables. `plan` returns the target `R`, a list of witness instructions `ws`, an optional rewriting of individual leaves, and an optional final step. `wgOpenR` consumes the instructions while descending into `R`: an instruction `.ex e` instantiates the next existential with `e`, and `.sel d` selects view `d` of a multi-view cell (a disjunction) by `hdisj_left`/`hdisj_right`; `wgDeepR` does the same inside stars, beta-redexes and helper predicates. No unification takes place and no alternative is tried. `wgCloseFin` closes the remaining entailment `T ==> R'`, in which both sides are now explicit, in three attempts: a structural proof on the raw sides, in which pure facts of `R'` are found among those of `T` or duplicated from a disequality (`pDup`, `pDupNe`) or are trivial (`wgTriv`), spatial atoms are matched by a permutation, and superfluous pure facts are dropped with `pDrop`; the same after `wgNorm` has reduced projections; and, last, the introduction of the left-hand pure facts as hypotheses, substitution of equations, and the structural proof with the remaining pure facts sent to the pure prover. On the profile route the terms produced are identical to those of the former profile-specific closer; all 607 profile lemmas of `qf_shid_entl` and `shid_entl` hashed equal when this was checked in pass T0.

The witnesses come from the parse. For a step branch, `wgStepWit` returns the recursive instance (the argument tuple of the recursive call), the weight expression, the view index, and the cell's own existentials (the branch's existentials minus the counter's); for the base branch, `wgBaseWit` returns the intermediate states and cell existentials recorded during base absorption (`baseW`); for a borrowed carrier, the abstraction takes, for each branch, the first `viaW` entry whose recursive atom has index 0 and emits the selection of its view followed by its witnesses, and the concretisation takes, for each view, the first entry with that view and uses its branch and its inverse map.

**Abstraction on the generic route.** `wgBuildAbs` builds, for a carrier record `P`, a closed proof of `∀ xs, P xs ==> target`, where the target is produced by `wgAbsTarget`: `∃ k n missing, wseg c k n start end ✶ tail ✶ ⌈condition k⌉`, with `n` replaced by the counter argument when there is one. On the generic route it

1. obtains the predicate's functional `F` from its definition (`functionalOf?` unfolds the predicate to `lfp F args`) and forms the instance type (the tuple of the parameters), the start map, the end map with the remainder, the weight map and the tail map (`wgGenData`, `wgGenJ`);
2. forms the abstraction `Q := gQ c (gLin kmin) (fun _ => 0) st E N T`;
3. unfolds `F Q ys` for variable arguments `ys`, splits the body into branches, and proves each branch against the disjunction `wor base step` by `wgClose`, choosing the base or the step side according to whether the branch contains a recursive occurrence;
4. selects the corollary by the remainder type (`gAbsGU`, `gAbsGI`, `gAbsGM`, `gAbsGMI`, Section 4.7), passing `lfpG_induct` (or, for a borrowed carrier, `lfpG_induct_with` together with the monotonicity proof stored in the predicate's unfold lemma) as the induction principle;
5. converts the corollary's conclusion to the target form by `wgGConv` when the two differ syntactically.

For `p_ls`, step 3 produces two obligations. The base branch `⌈y₀ = y₁⌉ ✶ emp` must entail the zero-cell base `⌈(y₀, y₁) = (y₁, y₁)⌉`; `wgCloseFin` introduces `y₀ = y₁`, substitutes, and the remaining fact is trivial. The step branch `∃ u, ⌈y₀ ≠ y₁⌉ ✶ (⌈y₀ ≠ 0⌉ ✶ y₀ ↦ u) ✶ Q (u, y₁)` must entail `∃ a' w, ⌈rel⌉ ✶ (c (y₀, y₁) (st a') w ✶ Q a')`; the witnesses are `a' := (u, y₁)` (the recursive call's arguments), `w := 1` (the step weight) and the cell's existential `u`, and after instantiation both sides contain the same atoms and the pure facts are present or trivial. Neither proof involves a search.

**Abstraction on the profile route.** The lemmas of a whole group were built when the profile carrier was derived (Section 10.4); `wgBuildAbs` composes the member's lemma with `gAbsPGPhi` (or `gAbsPGLe` for period 1), passing the profile triple and the check `pChkAK B prof = true` as `Eq.refl true`.

**Concretisation.** `wgBuildConc` builds `∀ k xs missing n, condition k → (wseg c k n start end ✶ tail ==> P xs)`. On the generic route it instantiates `gConcG` with

- `cal`, which computes the recursive instance from a state and a weight (constant components are taken from the parent instance, the counter from the weight);
- an invariant `I` with its proof `hI`: the carrier invariant (Section 10.7) when the carrier has a tail or several views and `True` otherwise, in either case extended, when the carrier has constant components, by their equality at both ends (`wseg_cst`);
- `ht`, proved by reflexivity (the computed instance's start, weight, end and tail are definitionally those required);
- `hb`, the base case: the `kmin`-cell segment is eliminated by `wseg_zero_elim`, `wseg_uncell` or `wseg_two_elim`, the base branch of the unfold equation is selected by `wgBranchTo`, and `wgClose` proves the branch with the inverse of the base witnesses;
- `h1`, the step case: for each view of the cell, the step branch is selected and closed by `wgClose`; when the predicate has a counter, the lower-bound lemma `lo` supplies `kmin ≤ len` for the recursive instance as a hypothesis.

On the profile route `wgBuildConc` applies the group's concretisation (built by `wgPGConcAll` from `gConcPG`) to the derivation provided by `gPhiC`.

### 10.7 The other lemmas

- **Invariant.** `wgBuildInv` instantiates `wseg_inv` with the carrier's `relLam` and `invLam`. Its three obligations (each cell implies the relation; the invariant holds of the empty segment; prepending a cell preserves it) are pure, after the cell's pure facts have been extracted (each disjunct of a multi-view cell separately, via `wgSplitDisj`), and are proved by `wgSide`, normally by unification with the `inv_*` lemmas. On the profile route `wgBuildInvPG` uses `wseg_inv1` with `pCell_w`.
- **Cell introduction.** `wgBuildCI` proves that one view's cell assertion, at given state and existentials, entails a one-step segment, by `wseg_cell` and the closer `convClose` (below).
- **Maps.** `wgMapOf A B` looks for a map from carrier `A` to carrier `B`: the identity if the cell relations coincide; otherwise, if `B` has at most as many state components as `A` and the two cells have the same *signature* (the sorted list of field offsets with, for each field, whether its value is a literal), each injective map of `B`'s components into `A`'s and each direction is tried by `wgBuildMap`, which proves the per-cell implication and instantiates `wseg_map` or `wseg_rev`. The signature test was added when the skip-list predicates of `qf_shlid_entl`, whose cells have incompatible layouts, caused 284 futile map constructions over that division (328 ms).
- **Retargeting.** `wgBuildRet P j l` instantiates `wseg_retarget` for constant component `j` guarded against address component `l`; the per-cell obligation (the cell with the old constant entails the cell with the new one, given that the address differs from the new constant) is closed by `convClose`. `wgBuildRetPrev` does the same with `wseg_retarget_prev`.
- **Allocation.** `wgBuildHc` proves that every cell allocates its address component (used by `hasLoc_wseg_pos` in the hook of Section 7.3); `wgBuildBk` instantiates `wseg_bk_zero`.
- **Facts.** `wgBuildLo` proves `holdsP (kmin ≤ len) (P xs)` for predicates with a counter, and `wgBuildFact` proves that every instance has a step count satisfying the invariant and the length condition; both rewrite the atom with its abstraction and prove the pure fact with the pure prover.

`convClose` is an older closer that remains for cell introduction, maps, retargeting and empty payloads: it introduces the left-hand existentials and facts, substitutes, unfolds helper predicates, opens the right-hand existentials as metavariables, assigns them by solving address equations (`convEqs`) and by matching atoms (`arAssign`), and finishes with `finishDirect` or `pureEntDirect`. Routing these lemmas through `wgClose` with witnesses from the carrier would delete it; this is item 1 of the remaining backlog (Chapter 13).

### 10.8 Entry

The pass is

```lean
def wgPass : TacticM Unit := do
  unless ← wgUnfoldHelpers true do
    let exL ← withMainContext do
      let t ← instantiateMVars (← (← getMainGoal).getType)
      let some (lhs, _) := entailHead? t | return false
      return (flatStar lhs #[]).any (·.isAppOf ``HProp.hexists)
    if exL then
      let _ ← arIntroLhs
  let (L, R) ← withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    if t.hasExprMVar then throwError "wg: mvars"
    let some (lhs, rhs) := entailHead? t | throwError "wg: not an entailment"
    let (body, _) ← arOpen rhs
    pure (flatStar lhs #[], flatStar body #[])
  let cands ← wgCands (L ++ R)
  if cands.isEmpty then throwError "wg: no predicate"
  if ← wgEntry then return
  let gd ← globalDeadline.get
  let now ← vclock
  globalDeadline.set (now + (gd - now) * cands.size / (cands.size + 1))
  try wgPassBody cands finally globalDeadline.set gd
```

`wgPass` begins by unfolding wrappers that expose a predicate occurring nowhere else in the goal (`wgUnfoldHelpers true`), or else by introducing left-hand existentials. It computes the candidate carriers, one per distinct cell relation among the predicates of the goal (`wgCands`), and fails if there are none; it also fails if the goal contains metavariables. Then `wgEntry` performs the checks that do not depend on a plan:

```lean
def wgEntry : TacticM Bool := do
  arIntroFacts
  wgLowFacts
  wgBkDrop
  if ← (try wgDupAlloc catch _ => pure false) then return true
  unless ← wgSegCycle do return false
  let ks ← wgEntryFacts
  if ← wgFalseClose then return true
  wgDropEmpty ks
  return false
```

- `arIntroFacts` moves the left-hand pure facts into the context.
- `wgLowFacts` adds `kmin ≤ len` for every left-hand predicate atom with a counter.
- `wgBkDrop` handles back pointers: for a predicate whose cells record the previous address, if the previous address at the end of a left-hand segment is allocated elsewhere on the left, the segment must be empty (`wseg_bk_zero`), and it is replaced by the equations of an empty segment; otherwise disequalities derived from `holdsP_abs_prev` are added.
- `wgDupAlloc` closes the goal if two left-hand cells have the same address (`hstar_hsingle_same_loc` gives `False`).
- `wgSegCycle` tests whether the start and end parameters of the left-hand segments form a directed cycle. Only then are the invariant facts of all left-hand atoms added (`wgEntryFacts`), `wgFalseClose` tries to prove `False` from them, and `wgDropEmpty` replaces every segment whose step count the pure prover shows to be zero by the equations of an empty segment.

The cycle condition is the only configuration in which the invariants force a contradiction or an empty segment. In the problem `dll-entl-04`, lengths decrease along two segments that point at each other, which forces two lengths to be equal and contradicts a disequality; in `dll-entl-03` four segments of a cycle must be empty. Adding the facts without the cycle test cost 1.5 s on `shid_entl` and 1.1 s on `shidlia_entl` with no gain.

Finally `wgPass` restricts the deadline to the share `carriers / (carriers + 1)` of the remaining time and runs `wgPassBody`.

### 10.9 Planning

The planner works on one carrier `P` at a time and is called with a continuation `onPlan` that executes a plan and reports success. Its data are the pieces of a chain and the plan:

```lean
structure WgPc where
  cell : Bool
  pred : Name := .anonymous
  atom : Expr := default
  idx : Option Nat := none
  st : Array Expr := #[]
  en : Array Expr := #[]
  len : Expr := default
  lo : Int := 0
  phs : Array Expr := #[]
  req : Option Expr := none
  deriving Inhabited

structure WgPlan where
  car : WgP
  lp : Array WgPc
  rp : Array WgPc
  rl : Array Expr
  deriving Inhabited
```

A piece is either a cell (`cell = true`) or an abstracted predicate atom with its start and end states in `P`'s coordinates, its length, its minimal length and, on the right, the length requirement of its predicate. A plan consists of the carrier, the left-hand pieces, the right-hand pieces and the right-hand lengths.

`wgPlanFor` proceeds as follows.

1. **Left-hand pieces.** `wgLhsPieces` maps each left-hand predicate atom whose carrier has a map to `P` into `P`'s coordinates. For each atom it introduces placeholder variables for the step count and for missing end components, and adds as local hypotheses the atom's length condition and invariant at the placeholder; the arithmetic of planning can then be checked by the pure prover without building any lemma. Tails of these atoms are added to the list of left-hand atoms.
2. **Right-hand side.** The right-hand existentials are replaced by metavariables. The start and end states of the right-hand predicate atoms are computed; they restrict which left-hand pieces and cells may start a chain (when the right-hand starts contain no metavariable, a start is a candidate only if one of its components, other than the constant ones, is a component of a right-hand start or a right-hand cell address) and which chain ends are of interest.
3. **Starts.** The candidate start states are the starts of the left-hand pieces and the states of left-hand cells that match the cell pattern. For each start, `wgWalkL` builds a chain greedily: from the current state, take the next unused left-hand piece whose start unifies with it (constant components are ignored), else the next left-hand cell that matches the cell pattern at the current state. The starts are ordered by the length of their chains, longest first; the sort is not stable, so the order among chains of equal length is not that of the left-hand side.
4. **Right-hand walk.** For each start and each prefix of its chain, from the longest, `wgWalkR` searches for a sequence of unused right-hand atoms from the same start to the prefix's end. A right-hand cell is matched against the cell pattern; a right-hand predicate atom must have a map from `P`. The search makes two passes, the first accepting only atoms whose start, in all components including the constant ones, equals the current state syntactically, the second accepting unification; when the end of a right-hand atom is an existential shared with other atoms, the ends of the left-hand pieces are tried as hints. The number of steps of one walk is bounded by `(R + 1)²` for `R` right-hand atoms.
5. **Acceptance.** When a right-hand sequence reaches the end, `okEnd` checks it: common trailing cells are removed from both sides; the two ends unify (up to equalities the pure prover shows, for integer components); every constant component has one value along the right-hand pieces, which is propagated into the left-hand cells; the linear relations between consecutive cells hold (`wgRelLink`); no left-hand cell violates its own guard; the plan is not trivial (a single piece on each side with the same predicate is no progress); and `arSolve` finds right-hand lengths whose sum is the sum of the left-hand lengths, which satisfy the minimal lengths and the length requirements of the right-hand predicates and the right-hand arithmetic facts. A plan whose lengths are all determined is passed to `onPlan`; if it succeeds, planning stops.

### 10.10 Execution

`wgExec` executes a plan in the following steps.

1. **Abstraction.** Each left-hand predicate piece is rewritten by its abstraction lemma with `arRwLhs`; the placeholders of planning are replaced by the variables the abstraction introduces, and the invariant of the new segment is added as a fact (`wgInvFact`). If the piece's carrier is mapped to `P`, the map lemma converts the segment.
2. **Constant components.** For each constant component, the target value is the one of the last right-hand piece. A left-hand segment whose constant differs is retargeted (`wgRetarget`) to nil when the component is guarded against addresses and the target value is not nil, and to the target value otherwise; retargeting to nil is always possible, because nil is safe far in any frame. Segments retargeted to nil are retargeted once more to the target value after they have been joined, which requires the target value to be safe far in the remaining frame. `wgSafeFar` proves this: the value is nil, or it is the address of a cell of the frame, or it is the start of a guarded segment of the frame. In the last case either the segment is non-empty and allocates its start, or it is empty and the value equals the segment's end, for which the same argument is repeated (`safeFar_step`), with a check against cycles.
3. **Cells.** Each left-hand cell piece is converted into a one-step segment by the cell-introduction lemma (`wgCellMatch` instantiates it at the matched cell).
4. **Groups.** The left-hand and right-hand pieces are cut into groups wherever a left-hand piece ends at the same state as a right-hand piece. This keeps the join and split local: for two lists that correspond piece by piece but in reversed order, joining everything and splitting by length would introduce fresh intermediate states where the original states are known.
5. **Join and split.** Within each group the left-hand segments are joined by `wseg_join` into one segment, which is split by `wseg_split` at the planned right-hand lengths. A right-hand cell piece is converted back into a cell by `wseg_uncell`. When the plan covers fewer right-hand predicate atoms than remain unmatched (so that later rounds will follow), and a group has exactly one right-hand piece of nonzero length, which is a predicate atom, and at least two left-hand parts, the join is deferred: the left-hand segments stay separate, and the join is performed on the right-hand side instead, after the right-hand atom has been concretised. A join on the left would turn the start of every inner segment into an interior point of one segment; later rounds may need these starts as allocated addresses (for example to prove that a retargeting value is safe far), and the allocation lemma `hasLoc_wseg_pos` applies only to segment starts. The deferral was introduced in part one of stage 3c of the second consolidation phase.
6. **Right-hand side.** Each right-hand predicate atom is rewritten by its concretisation lemma (`wgRwRhs`), so that the right-hand side contains a carrier segment and the length condition; a map lemma converts between carriers when needed. Each right-hand segment is then unified with a left-hand segment of the same carrier and the two are made syntactically equal by `wseg_cong`, whose index equations are proved by the pure prover; when constants differ, the left-hand segment is retargeted first. A right-hand piece of length zero is closed by `wseg_nil`.

**Example.** Consider `⌈x ≠ 0⌉ ✶ x ↦ y ✶ p_ls y 0 ==> p_ls x 0`. The carrier of `p_ls` is the one of Section 10.3, with constant component 1 guarded against the address component 0. The entry adds the hypothesis `x ≠ 0` and finds no cycle. Planning: the left-hand piece of `p_ls y 0` runs from `(y, 0)` to `(0, 0)` with step count `k₁`, minimal length 0 and the hypotheses `0 ≤ k₁` and the invariant. The right-hand atom `p_ls x 0` runs from `(x, 0)` to `(0, 0)`; its start `x` admits the left-hand cell `x ↦ y` as a chain start, with state `(x, ?)`. From there `wgWalkL` takes the cell (successor `(y, ?)`) and then the segment, so the chain ends at `(0, 0)`. The right-hand walk takes `p_ls x 0` in its second pass: the first pass compares all components, and the constant component of the chain's start is still open. In `okEnd` the constant component of the cell is set to 0, the guard `x ≠ 0` is not violated syntactically, and `arSolve` assigns to the right-hand length the whole left-hand length `1 + k₁`; its lower bound `0 ≤ 1 + k₁` is accepted by the syntactic normaliser `arTriv` without a call to the pure prover. Execution: `p_ls y 0` is abstracted to `wseg c k₁ n₁ (y, 0) (0, 0)` with `n₁ = k₁`; the cell, together with the guard `⌈x ≠ 0⌉` (needed twice by the cell pattern, once as `s.1 ≠ s.2` and once as `s.1 ≠ 0`, the second copy proved from the hypothesis), becomes `wseg c 1 1 (x, 0) (y, 0)`; the two are joined into `wseg c (1 + k₁) (1 + n₁) (x, 0) (0, 0)`; `p_ls x 0` on the right is rewritten by its concretisation to `⌈0 ≤ k⌉ ✶ wseg c k n (x, 0) (0, 0)` with metavariables `k` and `n`, which unification assigns. The remaining pure fact `0 ≤ 1 + k₁` is proved during the finish.

For `p_ls x y ✶ p_ls y 0 ==> p_ls x 0` the plan joins two abstracted segments, `(x, y) → (y, y)` and `(y, 0) → (0, 0)`. The first carries the constant `y`, the target constant is 0, so it is retargeted to 0 by `wseg_retarget`, whose frame condition `safeFar 0 F` holds by `safeFar_nil`. For the invalid `p_ls x y ✶ p_ls y z ==> p_ls x z` the same plan would need to retarget the first segment to `z`, and `safeFar z F` fails because `z` is neither nil nor allocated in the rest of the left-hand side; the plan fails, consistently with the countermodel of Section 6.8.

**A doubly linked list.** The goal `⌈a ≠ 0⌉ ✶ a ↦ b ✶ (a + 1) ↦ p ✶ ⌈b ≠ 0⌉ ✶ b ↦ n ✶ (b + 1) ↦ a ==> dll a p b n 2` folds two cells into a list of length 2 (the cell values are cast into `Int`, which is omitted here). The carrier of `dll` has the state `(current, predecessor)`, the counter `len` with unit weight, `kmin = 1`, and the end state `(n, tl)` (Section 10.3). The right-hand atom runs from `(a, p)` to `(n, b)` with length 2. The left-hand cell at `a` matches the cell pattern at the state `(a, p)` with successor `(b, a)`; the cell at `b` matches at `(b, a)` with successor `(n, b)`. The chain of the two cells reaches the right-hand end, and `arSolve` has nothing to assign: it checks `1 + 1 = 2` and `1 ≤ 2`, both identities for the syntactic normaliser `arTriv`. Execution converts the two cells into one-step segments by the cell-introduction lemma, joins them into `wseg c (1 + 1) (1 + 1) (a, p) (n, b)`, and rewrites `dll a p b n 2` into `⌈1 ≤ k⌉ ✶ wseg c k 2 (a, p) (n, b)`. Unification assigns `k := 1 + 1`, and the weight `1 + 1` is equated with the literal 2 by the pure prover. The remaining fact `1 ≤ 1 + 1` is closed during the finish.

**A split at an unknown point.** Let `ls_len x y m` be a list segment with an integer length parameter, whose base branch is `⌈x = y⌉ ✶ ⌈m = 0⌉` and whose step branch is `∃ u m', ⌈m' = m - 1⌉ ✶ ⌈x ≠ 0⌉ ✶ x ↦ u ✶ ls_len u y m'`, without a guard against the end. (The recursive call takes the existential `m'`, tied to `m` by an equation, because `wgCarrier` recognises a counter only in this form; the counter `len` of `dll` has the same form.) Its carrier has one moving component (the current location), unit weight, the counter `m`, and the end `y`. The goal `ls_len x z 5 ==> ∃✶ y, ls_len x y 2 ✶ ls_len y z 3` asks for the point `y` at which the segment is split. On entry the existential is still a binder; `wgPass` refuses a goal that contains metavariables. Planning opens `y` as a metavariable `?y`. The left-hand chain is the single piece from `x` to `z`, whose length is the counter argument 5. The right-hand walk takes `ls_len x ?y 2` in its first pass. Its end `?y` also occurs in the other right-hand atom, so the end `z` of the left-hand piece is tried as a value of `?y` before `?y` is left open. With `?y := z` the walk continues with `ls_len z z 3`, which starts at the current state and ends at the end of the chain, and `okEnd` accepts the plan: the ends agree, and `arSolve` checks `2 + 3 = 5` and the minimal lengths. The assignment `?y := z` exists only in the planning state: the continuation restores the state of the round, and `wgExec` uses the planned right-hand ends only to cut groups between left-hand pieces, of which there is one. Execution abstracts the left-hand atom to a segment of weight 5, rewrites its step count to `2 + 3` by `wseg_cong` (the pure prover derives the equation from the invariant, which states that the step count equals the weight), and splits it by `wseg_split` after 2 steps, which introduces an intermediate state `t` and weight `w` and leaves a segment of 3 steps from `t` to `z`. The right-hand existential is opened afresh as `?y'`, and both right-hand atoms are concretised. Unifying the first right-hand segment with the first piece assigns `?y' := t`, and the length 2 is matched with `w` by the pure prover, using the invariant of the piece. The first plan therefore succeeds, and the alternative that leaves `?y` open is never tried. The witness for `y` is produced by the split, not by the planning hint and not by enumeration.

### 10.11 Rounds and finishing

`wgRound` controls planning and execution for a set of candidate carriers. A carrier with several views is tried as itself and then once per further view. For each carrier, `wgPlanFor` is called with the following continuation: restore the state at the start of the round, build the plan's lemmas (`wgPrebuild`), execute the plan (if execution fails and the carrier has guarded constant components, execute again with every guarded constant component whose target is not nil retargeted through nil), and then

- if every remaining right-hand atom has a counterpart (it is a carrier segment, contains a metavariable, or occurs on the left), finish with `wgFinish`;
- otherwise (including when the finish fails), if the number of unmatched right-hand atoms has decreased, start a new round on the residual goal, with the candidates recomputed from the residual and the deadline lowered to the share `n₁ / (n₀ + 1)` of the remaining time, where `n₀` and `n₁` are the numbers of right-hand atoms that are neither pure facts nor carrier segments, before and after.

Residual states that have failed are remembered by a key (`wgStateKey`: the multisets of the left-hand atoms and of the right-hand atoms, without pure facts and without atoms that mention variables introduced after the first round, with segments reduced to their cell relation, start state and end state), and a residual round on a remembered state fails immediately. Plan selection is thus part of one backtracking search: each candidate plan is an alternative, and a plan that makes progress without finishing leads to a sub-search.

For example, in `p_ls x y ✶ p_ls y 0 ✶ p_ls a b ✶ p_ls b 0 ==> p_ls x 0 ✶ p_ls a 0` the two right-hand atoms are unmatched at the start (`n₀ = 2`). The candidate starts are `(x, y)` and `(a, b)`, each with a chain of two pieces. A plan follows one chain, so it covers one right-hand atom; which of the two chains is tried first is decided by the sort of step 3 of Section 10.9, and the two cases are symmetric. Suppose the chain from `a` comes first. The walk takes `p_ls a 0` in its second pass (the constant `b` of the chain's start differs from 0) and reaches `(0, 0)`. The plan covers one right-hand atom, fewer than `n₀`, so the join is deferred: the segment of `p_ls a b` is retargeted to 0, both segments stay on the left, and on the right the segment of the concretised `p_ls a 0` is replaced by the star of the two left-hand segments, by a proof that the star entails it (`wseg_join` followed by `wseg_cong`). After execution the right-hand side contains these segments, a pure fact and the atom `p_ls x 0`, which has no counterpart on the left, so the goal cannot be finished. One unmatched atom remains (`n₁ = 1 < n₀`), and a residual round runs with `n₁ / (n₀ + 1)`, a third, of the remaining time. In that round nothing is deferred (the plan covers the one remaining atom): the segment from `x` is retargeted to 0, joined with the segment of `p_ls y 0` and folded into `p_ls x 0`, after which the goal is finished.

`wgFinish` assigns the remaining right-hand metavariables by matching (`arAssign`) and closes the goal by `finishDirect` (one rewrite of the left-hand side to the right-hand side, dropping pure facts), or else by `xsimpl` followed by the pure prover.

`wgPassBody` adds two fallbacks when the first round fails. The first, `wgFoldPayloads`, handles carriers whose cells contain atoms of other predicates, the *payload predicates* of the carrier (`wgPayPreds`: the heads of the non-cell, non-pure atoms of a view's cell other than the carrier's own predicate). It applies only when the left-hand side contains a cell and some candidate carrier has payload predicates. For each right-hand atom of such a carrier whose start and end contain no metavariable, `wgFoldPath` walks the carrier's path from the start to the end through the left-hand side: at each step it either passes over a left-hand atom of the same predicate that starts at the current state, or matches a left-hand cell against the carrier's cell on its points-to atoms only. For each payload atom of a matched cell that is fully instantiated and absent from the left-hand side, three steps follow.

1. The payload's own payloads are folded first, by a recursive call of `wgFoldPath` along the payload's path.
2. `wgPayChain` searches, without building any proof, for the left-hand atoms (segments or cells of the payload's carrier) that lead from the payload's start to its end.
3. If that chain is non-empty, `wgPayApply` proves that the left-hand side entails the payload atom together with the left-hand side minus the chain, by a round of the engine on the payload's carrier alone (`wgRound #[Q]`), and replaces the left-hand side accordingly. If the chain is empty, `wgPayEmpty` proves `emp ==> a` for the payload atom `a` from its base branch and adds it to the left-hand side.

If the left-hand side has changed, the candidates are recomputed and a new round runs. Otherwise, or if that round fails, the second fallback unfolds all non-recursive wrappers (`wgUnfoldHelpers`) and runs a new round. Unfolding all wrappers at the entry of the pass instead was measured to cost 110 ms on `elseg4_slk`.

### 10.12 History

The engine has its origin in the second climb. Steps S1 to S5a added four kinds of segment descriptors (decrementing counters, ordered data, length profiles, and back pointers in design), each with its own lemmas and planning pass, raising the number of proved problems from 516 to 745. The first consolidation phase (C1, five stages) replaced them by the one carrier `wseg`, one parse and one planner, and added multi-branch carriers, borrowed carriers and a second round, reaching 780. The second phase (C2) made `wseg` cover what the older engines of the first climb covered (end-guarded cells with retargeting, nested payloads, previous-address guards) and fast enough to replace them; the deletion of those engines (about 3800 lines, among them the composition engine, four induction modes and the parity descriptors) was committed with a temporary time regression of 6.2 s on the original divisions, closed in the following step. The third phase (C3) removed `xsimpl` and all search from lemma building, replaced the per-shape builders by the two theorem-instantiating builders, merged the readers, and reduced the provers to one per obligation kind. Pass T0 introduced the witnessed closer `wgClose` and the shared length derivation.

## 11. The Witness Search

### 11.1 The problem and stage 0

An existential on the right-hand side needs a witness. Most witnesses are found as a side effect of other steps: `xsimpl` assigns them by unification when it cancels atoms, and the segment engine assigns them by unification of states. Some goals, however, are provable only with a witness that no unification proposes at the right moment, typically a location in the middle of a left-hand segment, or one of several locations whose correctness depends on arithmetic. The witness search `witSearch` is the one procedure that chooses witnesses by enumeration. It has three stages.

Stage 0, `witDetermined`, instantiates every right-hand existential that a pure equation of its body fixes to a term without other bound variables. It repeatedly peels the existentials at the front of the right-hand side; if the innermost one has such an equation, it applies `HProp.himpl_hexists_r` with that term; if the right-hand side is a star containing a determined existential, the existentials are first pulled to the front. The procedure is called by the witness search, by the segment engine on entry, and by the backtracking core's normalisation at every node; it involves no choice.

### 11.2 Ranking candidates

A candidate for a binder is ranked by how many right-hand atoms propose it. `witScore l r free` compares a left-hand atom `l` with a right-hand atom `r` of the same head: if every argument of `r` that does not contain a binder (`free`) equals the corresponding argument of `l`, the score is the number of such agreeing arguments; otherwise there is no score. `witRanked L Rs m free` collects the proposals for the binder `m`: for each right-hand atom `r` in which `m` occurs at position `p` (or as `m + k`), and each left-hand atom `l` that `witScore` accepts, the argument of `l` at position `p` (minus `k`) is a candidate. Candidates are ordered by the number of right-hand atoms that propose them and then by the total score. `witOrder` orders the left-hand atoms for one right-hand atom by score, with the original order as tie-break; `arAssign` (Section 7.4) uses this order.

For example, with the left-hand side `p_ls x y ✶ p_ls y 0` and the right-hand side `∃ u, p_ls x u ✶ p_ls u 0`, the atom `p_ls x u` and the left-hand `p_ls x y` agree in their first argument, which proposes `u := y`; the atom `p_ls u 0` and the left-hand `p_ls y 0` agree in their second argument, which proposes `u := y` again. The candidate `y` has two votes.

### 11.3 Candidate tuples

`witCands` opens the right-hand existentials as metavariables and selects the *location binders*: the leading binders of type `Nat` that occur in a spatial right-hand atom. The stage applies only to goals of a certain shape (every binder is a location binder, both sides consist of cells and predicate atoms, at least one of them a predicate). The candidate terms are the *roots* (first arguments of left-hand atoms), the *holes* (their other location arguments) and nil. For each binder the fallback candidates follow the ranked ones: roots, holes and nil if the binder is the first argument of some right-hand atom, holes, nil and roots otherwise. `witTuples` enumerates tuples depth first, ranking each binder's candidates after substituting the choices already made for the earlier binders, and stops at `(number of candidate terms) × (number of binders) + 1` tuples.

### 11.4 Stage 1

`witStage1` tries the tuples in order. For each tuple it instantiates the binders (`witInst`), discards the tuple if the instantiated goal is refuted by the countermodel (`goalRefuted`, Section 6.9), and otherwise runs the continuation with the deadline set to the remaining time divided by the number of remaining tuples. The continuation is `witEngine`:

```lean
def witEngine : TacticM Unit := do
  evalTactic (← `(tactic| first
    | (xsimpl_core
       all_goals (try xsimpl_clean)
       xsearch_pure
       done)
    | (xsearch_wseg
       first
       | done
       | xsearch_backtrack)
    | xsearch_backtrack))
```

that is, the fast path, the segment engine followed by the core, and the core alone. A tuple succeeds only if no goal remains. The procedure `witSearch` dispatches between stage 1 and the case-splitting form of Section 11.5:

```lean
def witSearch (k : TacticM Unit) (cases : Bool) : TacticM Unit := do
  unless cases do
    witDetermined
    let _ ← tryTactic (evalTactic (← `(tactic| conv_rhs => simp only
      [Sep.Xsearch.hstar_hexists_rr, HProp.hstar_hexists, HProp.hstar_assoc])))
    let (shape, tuples) ← witCands
    unless shape do throwError "wit: shape"
    witStage1 tuples k
    return
  let entries ← arEntries
  let heads := entries.map (·.headFn)
  let occs := (← wgLhs).filter fun x => match x.getAppFn.constName? with
    | some n => heads.contains n
    | none => false
  for o in occs do
    if ← pastGlobal then break
    let s ← saveState
    try
      rewriteOcc entries o
      let leaves ← wgSplitDisj
      for leaf in leaves do
        setGoals [leaf]
        if ← wgFalseClose then continue
        witCasesRun k
      if (← getUnsolvedGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "wit: no witness"
```

### 11.5 Stage 2: case split

Some goals have no single witness: the right witness depends on a case distinction that the goal's arithmetic forces. In `tree_size_split-1` the left-hand side is a tree of size at least 10 and the right-hand side splits it at an existential location `u`; after one unfolding of the tree, `u` must be the left child if the left subtree has at least two nodes, and the right child otherwise. The form `xsearch_wit cases` handles such goals. For each left-hand predicate occurrence it unfolds the occurrence, splits the left-hand disjunctions (`wgSplitDisj`), discards the cases whose facts are contradictory (`wgFalseClose`), and runs `witCasesRun` on each remaining case. `witCasesRun` computes the candidate tuples and passes them to `witStage2`, which proceeds as follows.

1. For each tuple, `witResidual` instantiates the binders, assigns the remaining right-hand metavariables by matching (skipping atoms without a match), and collects the right-hand pure conjuncts that have become closed but that the pure prover cannot prove. These are the tuple's *conditions*.
2. If the disjunction, over the tuples with conditions, of the conjunction of each tuple's conditions is provable by the pure prover, the goal is split by `byCases` into one case per tuple, each case having its tuple's conditions as a hypothesis (the last case receives the negations of the others' instead), and each case is instantiated with its tuple.
3. The continuation runs on each case, with the remaining time divided equally.

In `tree_size_split-1`, among the candidates (the left child, the right child and nil) the two children have the conditions `2 ≤ k` and `2 ≤ s2`, where `k` and `s2` are the sizes of the two subtrees; the size equation `k + s2 + 1 = n` with `n ≥ 10` implies their disjunction, which the pure prover shows.

### 11.6 Placement

The macro runs stage 1 (`xsearch_wit`) after the segment engine and before the backtracking core, and stage 2 (`xsearch_wit cases`) last. Running stage 2 before the core cost 306 ms on `qf_shid_entl` (problems such as `tll_slk-9` and `node-tll` that the core proves quickly). The core itself does not call the witness search; the backtracking core instead takes witnesses from `xsimpl`'s unification during its normalisation (Section 12.2).

That unification is the one witness decision that remains outside `witSearch` (item 4 of the remaining backlog). Pass 7 measured the alternative of keeping right-hand binders closed through the core's normalisation, by packing them into an opaque `hpack`, and offering the witness search at the binder nodes: four problems were lost (`16.tst`, `tll_slk-12`, `tll_slk-13`, `tree_size_split-1`) and the time grew by 9.3 s on `qf_shid_entl`, 5.2 s on `shid_entl` and 14.7 s on `shidlia_entl`. First-fit unification costs one unification per pair of atoms, and the correct witness is often determined only after other atoms have been cancelled, which `xsimpl` does in the same pass.

### 11.7 History

Before pass 6 of the third consolidation, witnesses were chosen by several separate mechanisms: a prefix tactic for determined binders (`xsearch_exwit`), a tuple enumeration with positional pairings (`xsearch_witness`, `witEnum`, `witPairs`), the case-splitting search (`xsearch_witcase`), matching votes for the cell address bound at a disjunct (`exVotes`, `exChoice`), and the matching order of `arAssign`. Pass 6 merged them into `witSearch` with one ranking, `witScore`/`witOrder`/`witRanked`, which also serves `arAssign` and the core's choice of witnesses at disjunctions (Section 12.4). The same pass identified `xsimpl`'s unification inside the core as a further witness decision, the one discussed in Section 11.6.

## 12. The Backtracking Core `xsearch_backtrack`

### 12.1 Structure

The backtracking core is the most general stage; it receives the goals that the segment engine and the first stage of the witness search do not prove. It is a depth-first search over goals. At each node it normalises the goal with `xsimpl`, and if goals remain it chooses among a list of alternatives (an unfolding, a disjunct, a wand application, an induction), applies one, and recurses on the resulting goals; on failure it restores the state and tries the next alternative.

```lean
elab "xsearch_backtrack" : tactic => do
  searchDeadline.set (← globalDeadline.get)
  searchSolve true
…
partial def searchSolve (inv : Bool) : TacticM Unit := do
  checkDeadline
  normGoals
  let gs ← getUnsolvedGoals
  if gs.isEmpty then return
  for g in gs do
    if ← g.isAssigned then continue
    setGoals [g]
    branchGoal inv
    unless (← getUnsolvedGoals).isEmpty do
      throwError "xsearch: subgoal remained"
  setGoals []
```

`searchSolve` normalises all current goals and then requires every remaining goal to be closed by `branchGoal`. The flag `inv` allows the invariant alternatives of Section 12.6; it is `true` at the top level and `false` inside the proof of an invariant lemma, so that invariant proofs do not nest. This flag replaced, in pass 7, a gate that allowed invariants only in the top four levels of the search, together with a fixed search fuel of 8 and a fixed 2600 ms for each invariant proof.

### 12.2 Normalisation at a node

```lean
def normGoals : TacticM Unit := do
  allTry distrCore
  allTry witDetermined
  Sep.Xsimpl.xsimplDriver none
  cleanAll
  let mut acc : List MVarId := []
  for g in ← getUnsolvedGoals do
    let s0 ← goalSig g
    let st ← saveState
    let g1 ← try fastSubstVars g catch _ => do st.restore; pure g
    let same ← if g1 == g then pure true else pure ((← goalSig g1) == s0)
    setGoals [g1]
    unless same do
      Sep.Xsimpl.xsimplDriver none
      cleanAll
    acc := acc ++ (← getUnsolvedGoals)
  setGoals acc
  evalTactic (← `(tactic| xsearch_pure))
```

`normGoals` distributes disjunctions outward (Section 7.5), instantiates determined witnesses (Section 11.1), runs `xsimpl` on every goal and cleans the results, substitutes equations between variables and runs `xsimpl` again if the substitution changed a goal, and finally disposes of pure goals with `xsearch_pure` (Section 8.2). All witness choices of `xsimpl` happen here: when cancellation unifies a right-hand atom containing a metavariable with a left-hand atom, the metavariable is assigned (Section 11.6).

### 12.3 Before the alternatives

`branchGoal` handles one goal. It first checks the deadlines, then consults the failure memo: a goal without metavariables is identified by its type, the free variables of its context, the `inv` flag and the depth of forced alternatives (`failKey`), and it fails at once if a goal with the same type, the same context variables and the same forced depth failed before with an `inv` flag at least as permissive. Failures are recorded only if they did not result from an exhausted deadline (`failAdd`). The goal is then prepared:

- `xsearch_distr` distributes disjunctions once more;
- an opaque star `hpack` is unfolded when the goal contains no wand;
- if the context contains hypotheses `hasLoc p H`, `xsearch_hfacts` adds, for each such location `p` and each cell address `l` occurring anywhere in the left-hand side, the hypothesis `l ≠ p`, proved through `himpl_of_neLocs` by the allocation prover after a cheap feasibility test (`mayNeLocs`). No stage of `xsearch` introduces a `hasLoc` hypothesis into the context of a goal: the allocation facts of Section 7.3 are proof terms consumed inside proofs, and the benchmark translation produces no `hasLoc`. The step therefore acts only on goals whose context already contains such hypotheses when `xsearch` is called, and it does nothing on the benchmark;
- the depth-zero countermodel (Section 6.4) is checked: `cmFind false` refutes the goal if the size intervals of the two sides are disjoint or the right-hand side has two cells at one address. Because the check runs at every node, a choice of disjunct or unfolding that makes the sizes of the two sides incompatible is rejected at the node that follows it, before any deeper search.

### 12.4 The alternatives

The list of alternatives depends on the form of the goal.

**Left-hand disjunction.** If the left-hand side is a disjunction, the only alternative is `hdisj_elim`: both disjuncts must be proved.

**Right-hand disjunction.** If the right-hand side is a disjunction, the alternatives are the two sides, ordered by a lexicographic comparison of counts computed for each disjunct (`branchCounts`): fewer pure facts that are refuted syntactically (`a ≠ a`), more right-hand cells whose address is the address of a left-hand cell, more right-hand cells whose address is the root of a left-hand predicate atom, more reflexive equations; ties are broken by the number of predicates the disjunct mentions that the left-hand side does not. When the first existential of a disjunct is the address of one of its cells and the ranking of Section 11.2 proposes at least two candidates for it, each candidate is offered as a separate alternative (choose the side and instantiate the witness) before the plain choice. The counts replaced, in pass 7, a weighted score with a tuned weight table.

**Otherwise.** The alternatives are collected from the atoms of the two sides and concatenated in the following order.

1. *Early unfoldings.* If the right-hand side contains non-recursive, non-flat predicates whose bodies need more cell heads than the left-hand side offers, and the left-hand side has exactly one recursive predicate atom, unfolding that atom comes first (`earlyLhsOccs`).
2. *Instantiation of quantified atoms.* `forallAlts` instantiates a left-hand `∀✶`-quantified wand with each left-hand cell address for which every spatial atom of the wand antecedents is syntactically equal to a distinct left-hand atom (`fwand_use`); `hwithAlts` projects the left-hand `hwith` atoms to their components (`projPf`), offering whole-goal alternatives: all atoms to their left components; for each atom, that atom to its right component with the others unchanged; and, when there are at least two, all atoms to their right components. If every right component has the head of a right-hand atom, the last alternative comes first; if some right component mentions such a predicate, the per-atom alternatives come first; otherwise the left projections come first; `specAlts` instantiates all leading variables of a left-hand `∀✶` atom by unifying the conclusion of its wand chain with a right-hand atom (`specByRhs`) and replaces the atom by the instantiated wand chain; and the invariant alternatives of Section 12.6.
3. *Induction.* If the left-hand side has exactly one spatial atom, it is a predicate atom, and the right-hand side contains a different predicate, the induction alternative `indAlt` (Section 12.5).
4. *Wands.* For each left-hand wand `A -✶ B`, `wandAlt` reduces the goal to `D ==> A` and `B ==> R`, where `D` is the rest of the left-hand side (`wand_use`); `wandAltS` does the same with only the left-hand atoms that occur in `A` used for `A` and the rest framed (`wand_use2`).
5. *Forced unfoldings.* A right-hand predicate occurrence is *forced* if its argument at the position that the predicate's definition uses as a cell address (`headIdxOf`) is the address of a left-hand cell: the right-hand predicate must then describe that cell.
6. *Flat predicates.* Left-hand occurrences of flat predicates (non-recursive, single-branch) are unfolded.
7. *Right-hand unfoldings*, early if there is no forced occurrence and the left-hand side has cells.
8. *Late unfoldings* of left-hand occurrences of non-flat, non-recursive predicates.
9. If there is no forced occurrence, all remaining right-hand and left-hand occurrences.

The alternatives are tried in order:

```lean
  for (ai, (isF, alt)) in alts.zipIdx.map (fun (x,i) => (i,x)) do
    checkDeadline
    let s ← saveState
    let oldDl ← searchDeadline.get
    let sliced := isF && (← forcedDepth.get) == 0 && ai + 1 < alts.size
    if isF then forcedDepth.modify (· + 1)
    if sliced then
      let now ← vclock
      let gd ← globalDeadline.get
      let slice := if gd > now then (gd - now) / (alts.size - ai) else 0
      searchDeadline.set (min oldDl (now + slice))
    try
      alt
      searchSolve inv
      if isF then forcedDepth.modify (fun k => k - 1)
      if sliced then searchDeadline.set oldDl
      return
    catch _ =>
      if isF then forcedDepth.modify (fun k => k - 1)
      if sliced then searchDeadline.set oldDl
      s.restore
  if let some k := fk then failAdd k
  throwError "xsearch: no alternative succeeded"
```

A forced alternative at forced depth 0 that is not the last alternative receives a slice of the remaining time, the remaining time divided by the number of remaining alternatives, so that one forced unfolding cannot consume the whole budget. Every alternative is followed by `searchSolve` on the goals it produces; the first success ends the node.

### 12.5 Induction

The core has one induction mechanism, `indCore`, which proves `A ==> M` for a predicate atom `A` and a motive `M` by `lfpG_induct_with`:

```lean
def indCore (A M inst : Expr) : TacticM (Expr × List MVarId) := do
  let some (F, ta) ← functionalOf? A | throwError "ind: not a fixpoint"
  let aty ← inferType ta
  if aty.isAppOf ``Sum then throwError "ind: mutual"
  let some p := A.getAppFn.constName? | throwError "ind: head"
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let some ent := entries.find? (·.headFn == p) | throwError "ind: unfold"
  let some val := (← getConstInfo ent.lemmaName).value? (allowOpaque := true) | throwError "ind: value"
  let some un := val.find? (fun e => e.isAppOf `Bench.lfp_unfold) | throwError "ind: lfp"
  let hmono := un.getAppArgs.back!
  let tup := stripInj ta
  let X ← withLocalDeclD `b aty fun b => do
    let pm ← projMap tup b
    let P ← if tup == ta && pm.map (·.1) == A.getAppArgs then pure (mkAppN A.getAppFn (pm.map (·.2)))
      else mkAppM ``lfpG #[F, b]
    mkLambdaFVars #[b] (← mkAppM ``hwith #[P, M.beta #[b]])
  let hfold ← withLocalDeclD `a aty fun a => do
    mkLambdaFVars #[a] (mkAppN (mkConst `Bench.lfp_pre) #[inst, aty, F, hmono, a])
  let saved ← getGoals
  let hM ← indSetup F X aty 0 (some M)
  let obl ← getGoals
  setGoals saved
  return (← mkAppM ``lfpG_induct_with #[F, M, hmono, hfold, hM, ta], obl)
```

It obtains the functional `F` and the argument tuple of `A`, rejects mutual groups (a sum-typed argument), takes the monotonicity proof from the value of the predicate's unfold lemma (which the benchmark proves with `Bench.lfp_unfold`), and builds the induction with the strengthened hypothesis `hwith (A at b) (M b)` for every recursive occurrence `b`. The obligation, one goal per branch of the body after `indSetup` has split sum and product variables, unfolded the functional (`xsearch_delta` unfolds one definition on the left-hand side) and normalised the result (`indNormGoal`: beta reduction, reduction of `Sum.elim` and pair projections, removal of `emp`), is returned to the caller as a list of goals.

`indAlt A R` uses the goal itself as the motive. If the right-hand side is a single atom with the same arguments as `A` and a different head, the motive is that predicate; otherwise the motive is the right-hand side with the variable arguments of `A` replaced by the corresponding projections of the tuple, guarded (`hguard`) by equations for the arguments of `A` that are not variables. The obligations are proved by the search: after the alternative, `searchSolve` runs on them, and the `hwith` atoms they contain are handled by the projection alternatives of item 2 above.

For a conversion `P a b ==> Q a b` between two single recursive predicates over the same arguments, the motive is `fun t => Q t.1 t.2`, and the obligations are the branches of `P`'s body with each recursive occurrence `P u b` replaced by `hwith (P u b) (Q u b)`. In a list-like definition, the base obligation `⌈a = b⌉ ==> Q a b` is proved by unfolding `Q`, and the step obligation `∃ u, a ↦ u ✶ hwith (P u b) (Q u b) ==> Q a b` by projecting `hwith` to `Q u b` and folding one cell of `Q`.

### 12.6 Derived invariants

Some goals need a lemma relating two predicates that no single unfolding provides: an instance of the left-hand predicate `a`, completed by some missing part `Q`, yields an instance of the right-hand predicate `r`. Such a lemma has the form `a xs ==> ∀✶ ws, Q -✶ C`, where `C` is an instance of `r`, and the core derives candidate lemmas of this form from the two definitions.

`deriveA a r` requires `a` to be recursive. A parameter of `a` is *fixed* if every recursive occurrence in the body of `a` passes it unchanged, and *free* otherwise. For each base branch of `a` that contains at least one cell, and each recursive branch of `r`, instantiated with metavariables for the parameters of `r` and for its existentials, `deriveA` matches the atoms of the branch of `r` (the pattern) into the atoms of the base branch of `a` (the target) by `matchInto`: every spatial atom of the pattern must unify with a distinct spatial atom of the target, pure atoms are ignored on both sides, an unmatched cell of the pattern makes the match fail, and exactly one non-cell atom of the pattern must remain unmatched. That atom becomes the antecedent `Q`. The conclusion `C` is the instance of `r` at the parameters as assigned by the match, rewritten along the pure equations of the base branch so that a free parameter of `a` is replaced by an equal fixed one. The candidate is rejected if `Q` or `C` mentions an existential of the base branch or `C` still mentions a free parameter. The metavariables that remain unassigned in `C` and then in `Q` become the universally quantified variables `ws` (`mkInvLam`).

`deriveB a r` serves a non-recursive target `r` (the core calls it exactly when `r` is not recursive). For each base branch of `a` that contains cells, it tries every branch of `r` that has the same number of cells, all unifying with the cells of the base branch, and exactly one further spatial atom, of a recursive predicate other than `a`; that atom becomes the antecedent. A pure equation of the branch of `r` between a metavariable and a ground term is a choice point (the ground term or any term equal to it by the base equations of `a`); at most two choice points are allowed, and all combinations are enumerated. The candidates of both procedures are cached per pair of predicates.

**Example.** The benchmark problem `dll-mid-entails-dll-rev` defines a doubly linked list read forwards, `DLL_plus hd p tl n`, with the base branch `⌈hd = tl⌉ ✶ ⌈hd ≠ 0⌉ ✶ hd ↦ p ✶ (hd + 1) ↦ n` and the recursive branch `∃ x, ⌈hd ≠ 0⌉ ✶ hd ↦ p ✶ (hd + 1) ↦ x ✶ DLL_plus x hd tl n`, and the same list read backwards, `DLL_plus_rev hd p tl n`, with the same base branch and the recursive branch `∃ x, ⌈tl ≠ 0⌉ ✶ tl ↦ x ✶ (tl + 1) ↦ n ✶ DLL_plus_rev hd p x tl` (the cells are written in the encoding of Section 1.1, the casts are omitted, and the display is derived from the problem file, not quoted). The parameters `tl` and `n` of `DLL_plus` are fixed, `hd` and `p` free. `deriveA DLL_plus DLL_plus_rev` instantiates the recursive branch of `DLL_plus_rev` at `?h ?q ?t ?m`; the cell `?t ↦ ?x` unifies with `hd ↦ p` and `(?t + 1) ↦ ?m` with `(hd + 1) ↦ n`, which assigns `?t := hd`, `?x := p` and `?m := n`. The atom `DLL_plus_rev ?h ?q p hd` remains unmatched and becomes `Q`. The conclusion `DLL_plus_rev ?h ?q hd n` mentions the free parameter `hd`, which the base equation `hd = tl` replaces by `tl`. The candidate lemma is

```
DLL_plus hd p tl n ==> ∀✶ h q, DLL_plus_rev h q p hd -✶ DLL_plus_rev h q tl n
```

a forward list from `hd` to `tl`, completed by a backward list that ends at its predecessor `p` and links to `hd`, is a backward list ending at `tl`. This trace follows the code of `deriveA`; whether the search uses this candidate on the problem depends on which alternative succeeds first.

`invAlts` proposes candidates only when the left-hand side contains no wand, no `hwith` atom and no `∀✶` atom; it then takes, for each recursive left-hand predicate atom and each different predicate heading a top-level right-hand atom, the candidates of `deriveA` (recursive target) or `deriveB` (non-recursive target). Each candidate becomes one alternative, `invUseAlt`. When it is tried, it first instantiates the candidate at the arguments of the left-hand atom and checks relevance: some argument of an atom of the wand antecedents must be the address of a left-hand cell; otherwise the alternative fails without any proof attempt. It then proves the candidate by `proveInv`, which applies `indCore` with the candidate as motive and runs the search itself, with `inv = false`, on each obligation after introducing the universally quantified variables and moving the wand antecedent to the left-hand side. The time of one proof is the time remaining to the search deadline divided by the number of candidates at the node; results, failures included, are cached per problem. If the candidate has universally quantified variables, `specByRhs` must instantiate all of them by unifying the conclusion of the wand chain with a right-hand atom; otherwise the alternative fails. Finally `replaceAtomAlt` replaces the left-hand atom by the instantiated wand chain (by `frame_l_of` after a permutation), and the wand alternatives of Section 12.4 finish the proof; because the left-hand side now contains a wand, no further invariant alternative is offered below this node.

Invariant alternatives are offered at every node of the outer search whose goal has no metavariables and whose sides are not disjunctions, and never inside the proof of an invariant (`inv = false`). They remain because switching them off loses five problems (`dll-mid-entails-dll-rev`, two `tll-pp` and two `tree-pp` problems), as measured in stage 3c of the second consolidation phase.

### 12.7 Example

The goal `⌈x ≠ 0⌉ ✶ x ↦ y ✶ p_ls y 0 ==> p_ls x 0` of Section 10.10 is proved by the segment engine before the core runs; it is used here to show how the core would proceed. Normalisation introduces the hypothesis `x ≠ 0`; `xsimpl` finds nothing to cancel. In `branchGoal` neither side is a disjunction. The right-hand occurrence `p_ls x 0` is forced, because the definition of `p_ls` uses its first parameter as a cell address and `x` is the address of the left-hand cell. Unfolding it and distributing gives a right-hand disjunction of `⌈x = 0⌉ ✶ emp` and `∃ u, ⌈x ≠ 0⌉ ✶ (⌈x ≠ 0⌉ ✶ x ↦ u) ✶ p_ls u 0`. At the next node the second disjunct is preferred, because its cell `x ↦ u` has the address of a left-hand cell. After `hdisj_right` selects it, normalisation by `xsimpl` replaces `u` by a metavariable, cancels `x ↦ y` against `x ↦ ?u`, assigning `?u := y`, cancels `p_ls y 0`, and leaves the side goals `x ≠ 0`, which `xsearch_pure` closes by assumption. Had the first disjunct been chosen instead, the goal `⌈x ≠ 0⌉ ✶ x ↦ y ✶ p_ls y 0 ==> ⌈x = 0⌉ ✶ emp` would have been refuted at its node by the depth-zero countermodel: the left-hand side occupies at least one cell and the right-hand side exactly none.

### 12.8 History

The core is the oldest part of `xsearch`; the first climb developed it, with an induction procedure of four modes (`proveInduct`), segment composition by descriptors, parity descriptors, wand and quantifier alternatives and derived invariants, from 289 to 454 proved problems of the two original divisions. In the second climb the segment engine took over the reasoning about segments, and part three of stage 3c of the second consolidation phase deleted the core's specialised procedures; the four induction modes became the single mechanism `indCore`, used both by `indAlt` and by `proveInv`. Restricting `indAlt` to goals with a single left-hand predicate atom and a different right-hand predicate was necessary for time: without the restriction, `ls-entl-06` took 4.9 s instead of 1.4 s. Pass 7 replaced the fixed depth, node and forced-depth caps by the deadline mechanism and the derived time slices, and the branch-ordering weights by the lexicographic counts.

## 13. Measurements, Rejected Alternatives and Open Items

### 13.1 The end state

At the closing entry of the second climb's ledger, all 788 genuinely valid entailment problems of the seven covered divisions are proved, and the 10 problems found to be mislabelled (seven of the `ls_dlen`, `ls_plen` and `ls_ubnd_dlen` variants of `get_last`, `get_two_lasts` and `split_mid_node`, `tseg_size_split-1` and `-2`, and `dlgrid-left-right`) fail or time out, as they must. No problem of a satisfiability division is proved. The time to prove the 788 problems is 35.6 s in total and 42.2 s including the failing problems; the original two divisions take 16.3 s, against 17.5 s at the start of the second climb; the slowest proved problem takes 812 ms. The `Yolo` cancellation files with 100 to 800 atoms take 0.14 to 0.60 s each. `Sep/Xsearch.lean` has 9976 lines and no theorems (12091 lines at the start of the second consolidation phase), `Sep/SegC.lean` 2283 lines, `Sep/Xsimpl/Core.lean` 2102 lines.

The mechanisms of the end state, in the terms of the preceding chapters, are: prefix normalisation (refutation by unconstrained variables, the countermodel once per goal, cache reset, substitution of equations, removal of trivial facts, unfolding of non-recursive predicates with forced-determination inlining, pure facts, cell disequalities); the fast path `xsimpl_core`; one segment engine over one carrier, with back-allocation reasoning and plan selection inside; one witness search with three stages; one backtracking core with one induction mechanism and the depth-zero countermodel at every node. The lemma builder instantiates one theorem family (`gAbs` and `gConc` with their corollaries) from one reader, one carrier derivation and one length derivation, with one witnessed branch closer and no use of `xsimpl` or search. There is one pure prover with one call site for `omega`, one permutation prover, one allocation prover and one countermodel, and `xsimpl` cancels by a reflected permutation certificate.

### 13.2 Measured and rejected

The ledgers record the following alternatives, each measured and kept out of the code. They are listed because each one is a plausible design that a reader might propose.

- **Proofs of list permutations by `List.Perm`.** The kernel reduces every `List.append`; slower than the chain of swap lemmas (Section 7.2).
- **Reflective AC normalisation in the lemma builder.** Kernel time 13 s; the reflected certificate of Section 3.7 avoids the cost by evaluating only natural-number literals.
- **A closed-term selection proof by reflection**: also 13 s of kernel time.
- **A list-based star** (a star over a list of atoms, defined by recursion on the list) in the permutation proofs of left-hand rewriting: four times slower than the chain of frame and swap lemmas.
- **A forced single-atom plan path** in the segment engine: +3.6 s.
- **An emptiness implication for every address component** in carrier invariants: lost `ls-entl-07` and slowed `shidlia_entl`.
- **Routing single-member groups through the ordinary parse** instead of the profile route: lost 19 problems (`eolseg`, `lsleftright`, `odd-lseg3`).
- **An invariant conjunct "a non-empty segment's start differs from its end"**: 30 ms per doubly-linked-list problem; replaced by the allocation lemma `hasLoc_wseg_pos`.
- **Skipping the countermodel on the `bolognesa` problems**: 53 of 110 are invalid with no existentials or pure facts and only the countermodel refutes them; skipping it gives 53 timeouts, and running it after the engine costs 133 s.
- **Unfolding the countermodel to literal values** (the first attempt of pass 5b).
- **A per-atom unfolding marker and a distinct-heads budget** in the former fast-path unfolding: lost `append_dll_slk-1` and `-7`.
- **Holding right-hand binders closed through the core's normalisation** (pass 7 and T0): lost four problems and about 29 s (Section 11.6).
- **Deleting `cmVms` by running the countermodel to exhaustion** (T0): no change of outcome, +3.6 s on `shid_entl` (Section 6.7).
- **One `omega` call per obligation** (T0): +3 % on `shidlia_entl` (Section 7.1).
- **Taking a unique positional candidate as a determination** in `xsearch_macros` (T0): lost `lsegex4_slk-1` (Section 9.3).
- **Routing profile carriers through `convClose`** (pass 3b): profile concretisations twice as slow.

### 13.3 Remaining backlog

The closing entry lists five open items, none required for the end state.

1. **One closer in the lemma builder.** `wgClose` overlaps the older `convClose` family (`arOpenDeepE`, `arIntroLhs`, `finishDirect`, `puresEmpPf`, `pureEntDirect`, the star walkers and a multiset pre-check). Routing cell introduction, maps, retargeting and root witnesses through `wgClose` with witnesses from the carrier would delete `convClose`, `arAssign`, `convEqs`, `wgSplitMVar`, `pureEntDirect` and `finishDirect`.
2. **`cmVms`** is the one bound without a time-neutral derivation; exhaustion costs 3.6 s on `shid_entl`.
3. **The `omega` retry ladder.** One call per obligation costs 3 % on `shidlia_entl`.
4. **`xsimpl`'s first-fit instantiation** inside the core's normalisation is the one witness decision outside `witSearch`; holding the binders costs four proofs and about 29 s.
5. **The generic abstraction's base case** still costs about 130 µs per small lemma more than the deleted shape-specific base lemmas on the smallest problems, although the division totals are back at the level before the change.

A sixth item records only that some plan lines of the ledger were superseded by later entries. The satisfiability divisions remain out of scope.
