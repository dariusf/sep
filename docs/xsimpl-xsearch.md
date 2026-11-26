# `xsimpl` and `xsearch`

This text describes two tactics of the Sep library for proving separation logic entailments in Lean 4. The first, `xsimpl`, simplifies an entailment by a fixed sequence of rules and returns the part it could not prove. The second, `xsearch`, is a prover for entailments between formulas that mention inductively defined predicates; it either proves the goal completely or fails.

The emphasis is on what each tactic does to a goal and on which properties of that behaviour a user may depend. The implementation is discussed only as far as is needed to explain those properties.

## Assumed background

The reader is assumed to know separation logic well: separating conjunction and implication, the frame rule, pure assertions, existential quantification over assertions, inductive predicates such as list segments, and the difference between linear and affine logics.

The reader is assumed to know the basics of Lean: terms and types, propositions as types, type classes, tactic proofs, the goal display, and common tactics such as `intro`, `apply`, `simp` and `omega`.

No knowledge of Lean metaprogramming is assumed. The few notions that are needed are introduced where they are first used.

## Notation

The library's concrete logic is the type `HProp` of predicates over heaps. Its notation is used throughout.

| Notation | Meaning |
|---|---|
| `H ==> H'` | entailment |
| `H ✶ H'` | separating conjunction (right associative) |
| `emp` | empty heap |
| `⌈P⌉` | pure assertion: `P` holds and the heap is empty |
| `∃✶ x, H` | existential quantification |
| `H -✶ H'` | separating implication (wand) |
| `p ↦ v` | singleton heap |

Separating conjunction binds more loosely than the wand, so `H1 ✶ H2 -✶ H3` is displayed for `H1 ✶ (H2 -✶ H3)`. Parentheses are written explicitly in this text.

---

# Chapter 1. `xsimpl`

## 1.1 Purpose

`xsimpl` is applied to a goal of the form `H ==> H'`. It is intended for entailments in which the two sides differ only by rearrangement, by the position of quantifiers and pure assertions, and by wands that can be eliminated directly. An example is

```lean
example {H K : HProp} {J : Nat → HProp} :
    (∃✶ x, J x ✶ ⌈x > 0⌉) ✶ H ✶ (H -✶ K) ==> ∃✶ y, K ✶ ⌈y > 0⌉ ✶ J y := by
  xsimpl
```

The tactic does not search. Each of its rules applies in at most one way, and no rule application is undone. Its result on a given goal is therefore predictable. When it cannot finish a proof, it does not fail; it returns the simplified goal to the user.

## 1.2 The fragment: the `SepLogic` class

`xsimpl` is not specific to `HProp`. It is written against a type class that lists the connectives and the laws the tactic uses.

```lean
class SepLogic (α : Type u) where
  star : α → α → α
  emp : α
  spure : Prop → α
  ex : {A : Sort v} → (A → α) → α
  wand : α → α → α
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

Three points about this class determine what the tactic can and cannot do.

First, the structural laws of `star` are equations, not entailments in both directions. The tactic may therefore rewrite with them anywhere, including under a wand or inside the argument of a predicate.

Second, the class contains no rule for discarding resources. A logic that permits discarding is declared an instance of a second class.

```lean
class AffineSepLogic (α : Type u) extends SepLogic α where
  entails_emp : ∀ H, Entails H emp
```

`xsimpl` uses `entails_emp` in exactly one place, described in Section 1.4.7. `HProp` is not an instance of `AffineSepLogic`, so on `HProp` the tactic treats every resource linearly.

Third, the class says nothing about points-to assertions, disjunction, or inductive predicates. Every formula that is not built from the six operations is opaque to the tactic.

A concrete logic is connected to the class by an instance and by two families of lemmas, each proved by `rfl`, that translate between the logic's own constants and the class operations. For `HProp` these are, for example,

```lean
@[xsimpl_fold] theorem fold_hstar (H1 H2 : HProp) :
    HProp.hstar H1 H2 = SepLogic.star H1 H2 := rfl

@[xsimpl_unfold_class] theorem unfold_star (H1 H2 : HProp) :
    SepLogic.star H1 H2 = HProp.hstar H1 H2 := rfl
```

with one such pair for each of the six operations. The tactic reads the `xsimpl_fold` lemmas to learn which constants of the goal play the roles of `star`, `emp`, and so on. A goal may also be stated directly with the class operations.

## 1.3 The view of a goal: items

The tactic regards each side of an entailment as a finite list. The elements of the list are called *items*.

The items of a formula are obtained by decomposing it along `✶` and removing `emp`. Thus `(H1 ✶ emp) ✶ (H2 ✶ H3)` is the list `[H1, H2, H3]`, and `emp` is the empty list. The decomposition is justified by `star_assoc`, `star_emp_l` and `star_emp_r`.

There are four kinds of item.

- A *pure item* is `⌈P⌉`.
- An *existential item* is `∃✶ x, H`.
- A *wand item* is `H1 -✶ H2`.
- An *atom* is anything else: a points-to assertion, an application of a predicate, a variable of type `HProp`, and so on.

Items are normalised before use. The body of an existential item, both sides of a wand item, and those arguments of an atom that themselves contain separation logic operations are flattened in the same manner. A wand whose premise is a conjunction is curried by `wand_curry`, so that `(H1 ✶ H2) -✶ H3` becomes `H1 -✶ (H2 -✶ H3)`. A pure item `⌈t = t⌉` becomes `⌈True⌉`.

Three further notions from Lean's internals are needed.

A *metavariable* is a placeholder for a term that is not yet known, written `?x`. It has a type and a context, the list of variables and hypotheses that the eventual term may mention. A goal is itself a metavariable whose type is the statement to be proved; a tactic solves a goal by supplying a term for it, and that term may contain new metavariables, which become the new goals. `xsimpl` uses metavariables for the witnesses of existential quantifiers on the right-hand side.

Two terms are *definitionally equal* if computation makes them identical, where computation consists of unfolding definitions and evaluating function applications. For example, `1 + 1` and `2` are definitionally equal.

The *unifier* is the procedure by which Lean decides whether two terms are definitionally equal. If the terms contain metavariables, the unifier is permitted to assign them in order to make the terms equal. Two terms *unify* if the unifier succeeds on them.

## 1.4 The algorithm

The tactic processes a goal `L ==> R` in the following order. Each step is described and then applied to the example of Section 1.1,

```
(∃✶ x, J x ✶ ⌈x > 0⌉) ✶ H ✶ (H -✶ K)  ==>  ∃✶ y, K ✶ ⌈y > 0⌉ ✶ J y
```

### 1.4.1 Immediate closure

If neither side contains a metavariable and the two sides are definitionally equal as whole formulas, the goal is closed by reflexivity.

Otherwise the left side is flattened into its list of items. If the right side flattens to a list of the same length, no item contains a metavariable, and every item of one side can be paired with an item of the other by the comparison described in Section 1.4.4, the goal is closed by a permutation. This case exists so that goals such as `H1 ✶ (∃✶ x, J x) ==> (∃✶ x, J x) ✶ H1` are proved without opening the quantifier.

In the example neither condition holds.

### 1.4.2 Extraction on the left

Every existential item and every pure item on the left is moved into the proof context.

An item `∃✶ x, H` is removed from the list, a new variable `x` is introduced into the context, and the items of `H` take the place of the removed item. The rule used is `ex_l`, after `star_ex` has moved the quantifier to the outside of the conjunction. An item `⌈P⌉` is removed and a hypothesis of type `P` is introduced. The rule used is `pure_l`.

The step is repeated until the left side consists only of wand items and atoms. In particular, quantifiers and pure assertions that appear only after an outer quantifier has been opened are also extracted.

In the example the left list is `[∃✶ x, J x ✶ ⌈x > 0⌉, H, H -✶ K]`. Extraction introduces `x : Nat` and a hypothesis `x > 0`, and leaves `[J x, H, H -✶ K]`.

Both rules are equivalences: the goal after extraction is provable exactly when the goal before it is. Extraction therefore never turns a provable goal into an unprovable one.

### 1.4.3 Instantiation on the right

Every existential item and every pure item on the right is removed.

An item `∃✶ y, H` is replaced by the items of `H` with `y` replaced by a new metavariable `?y`. The rule used is `ex_r`. The tactic does not choose the witness at this point. An item `⌈P⌉` is removed and a new goal `P` is created. The rule used is `pure_r`. If `P` is `True` the new goal is closed at once.

The step is repeated until the right side consists only of wand items and atoms.

In the example the right list is `[∃✶ y, K ✶ ⌈y > 0⌉ ✶ J y]`. Instantiation creates `?y`, creates the goal `?y > 0`, and leaves `[K, J ?y]`.

Instantiation is performed after extraction for the following reason. The context of `?y` is the context at the moment of its creation. Because `x` has already been introduced, `?y` may later be assigned a term that mentions `x`. In the opposite order the witness could not depend on the variables bound on the left.

### 1.4.4 Cancellation

Items that occur on both sides are removed from both. The rule is the frame rule: from `L' ==> R'` infer `A ✶ L' ==> A ✶ R'`.

Pairs are found in two passes.

1. If no item on either side contains a metavariable, each right item is paired with the first unused left item that is syntactically identical to it.
2. The remaining right items are taken from left to right. Each is compared with the unused left items, from left to right, by Lean's unifier, and is paired with the first one for which unification succeeds. An item that is a bare metavariable, on either side, is never paired.

Witnesses are determined in the second pass. When the right item `J ?y` is unified with the left item `J x`, the unifier assigns `?y := x`.

Unification decides *definitional* equality and nothing stronger. `J (1 + 1)` cancels against `J 2`, since `1 + 1` reduces to `2`. `J (a + b)` does not cancel against `J (b + a)` for variables `a` and `b`, since commutativity of addition is a theorem and not a reduction.

In the example the first pass does not apply, because `J ?y` contains a metavariable. In the second pass `K` matches no left item, and `J ?y` is unified with `J x`. The remaining goal is

```
H ✶ (H -✶ K)  ==>  K
```

and the side goal has become `x > 0`.

If cancellation leaves both lists empty, the goal is closed. If it leaves two formulas that are definitionally equal, the goal is closed by reflexivity.

### 1.4.5 Wands on the right

Two rules apply to wand items that remain on the right.

A right item `A -✶ A` is removed. It holds of the empty heap, so it imposes no obligation.

If the right side then consists of a single wand item `A -✶ B`, the goal `L ==> A -✶ B` is replaced by `L ✶ A ==> B`, by `wand_intro`, and the whole algorithm is run again on the new goal from Section 1.4.1. This rule is an equivalence, since `wand_intro` is one direction of the adjunction between `✶` and `-✶`. It is not applied to a wand that occurs together with other items on the right, where no such equivalence is available.

### 1.4.6 Wands on the left

If the previous rule did not apply and the left side contains a wand item `A -✶ B` together with another item that unifies with `A`, both are replaced by `B`. The rule is `wand_cancel`. The whole algorithm is then run again on the new goal.

The premise `A` must be matched by a single left item. Since premises are curried during normalisation, a wand `(A1 ✶ A2) -✶ B` has become `A1 -✶ (A2 -✶ B)`, and it is eliminated in two successive rounds when both `A1` and `A2` are present on the left.

In the example `H` matches the premise of `H -✶ K`. The goal becomes `K ==> K`, and the second run closes it by Section 1.4.1.

Since cancellation precedes this step, a wand that also occurs unchanged on the right is cancelled rather than eliminated. `H ✶ (H -✶ K) ==> (H -✶ K) ✶ H` is proved by cancellation alone.

### 1.4.7 Cleanup

Each goal that remains, whether an entailment or a side goal, is given to a final step that tries the following and stops at the first success.

For an entailment `L ==> R`:

1. reflexivity, if `L` and `R` unify;
2. a hypothesis in the context whose statement is the goal;
3. if `R` is `emp` and the logic is an instance of `AffineSepLogic`, the rule `entails_emp`.

For any other goal:

1. a hypothesis in the context whose statement is the goal;
2. if the goal is an equation `a = b` without metavariables, reflexivity, where only definitions marked reducible and type class instances are unfolded. (A definition may be marked *reducible* by its author, which permits automation to unfold it without restriction.)

In the example the side goal `x > 0` is closed by the hypothesis introduced in Section 1.4.2. No goals remain.

The third rule for entailments is the only use of affinity. In an affine logic the goal `H1 ✶ H2 ==> H1` is proved, because cancellation leaves `H2 ==> emp`. On `HProp` the same goal is returned as `H2 ==> emp`.

## 1.5 The result

When `xsimpl` does not prove a goal, it leaves goals of three kinds, in this order.

1. At most one entailment `L' ==> R'`, the *residual*. `L'` and `R'` consist of the items that were not cancelled, in their original relative order. If one side is empty it is displayed as `emp`.
2. One goal `P` for each pure item `⌈P⌉` of the right side that the cleanup did not prove.
3. One goal for each witness that unification did not determine. Its statement is the type of the witness.

The variables and hypotheses introduced by extraction appear in the context of the residual and of the side goals. They carry inaccessible names, displayed as `x✝` and `a✝`; use `rename_i` or `next` to name them.

Some examples follow. The goals shown are those reported by Lean after the tactic.

```lean
example {H1 H2 H3 H4 : HProp} : H1 ✶ H2 ✶ H3 ==> H2 ✶ H4
-- ⊢ H1 ✶ H3 ==> H4

example {H : HProp} {P Q : Prop} : H ==> ⌈P⌉ ✶ H ✶ ⌈Q⌉
-- ⊢ P
-- ⊢ Q

example {H : HProp} : H ==> ∃✶ x : Nat, ⌈x > 3⌉ ✶ H
-- ⊢ ?x > 3
-- ⊢ ℕ

example {H : HProp} {P Q : Prop} : ⌈P⌉ ✶ H ✶ ⌈Q⌉ ==> H ✶ ⌈P ∧ Q⌉
-- a✝¹ : Q
-- a✝ : P
-- ⊢ P ∧ Q
```

In the third example the witness is unconstrained and the context contains no variable of type `ℕ`. The user may supply the witness by solving the second goal first, for instance with `case x => exact 4`, after which the first goal reads `4 > 3`.

## 1.6 Properties a user may rely on

**The tactic does not fail.** If a goal is not an entailment in a registered logic, or contains a construct the tactic cannot traverse, or admits no rule, the goal is left exactly as it was. Lean's linter then reports that the tactic did nothing. `xsimpl` acts on every goal currently open, not only the first.

**The result is sound.** Every step constructs a proof term from the class lemmas and from lemmas derived from them. Lean's kernel, the small trusted program that checks every proof term independently of the tactics that produced it, checks the complete term when the enclosing theorem is finished. A defect in the tactic can cause a goal to be left unproved or an error to be reported; it cannot cause a false statement to be accepted.

**Resources are not discarded.** Without an `AffineSepLogic` instance, an item that is not cancelled remains in the residual.

**Extraction and wand introduction preserve provability.** After these steps the goal is provable if and only if it was before.

**Opaque items are compared, never inspected.** An atom is cancelled only against an item that unifies with it. The tactic does not itself unfold predicate definitions, does not use equations from the context, and does not reason about points-to assertions beyond comparing them.

**Bare metavariables of type `HProp` are neither cancelled nor assigned.** An item `?F` on either side is never cancelled and never assigned by the cancellation step. This reserves such metavariables for frame inference, described in Section 1.7.

The remaining properties are limitations. Each identifies a step that can turn a provable goal into an unprovable residual.

**Witnesses are chosen by the first match.** Cancellation commits to the first pair that unifies and does not revisit the choice.

```lean
example {J : Nat → HProp} : J 1 ✶ J 2 ==> ∃✶ x, J x ✶ ⌈x = 2⌉
-- ⊢ J 2 ==> emp
-- ⊢ 1 = 2
```

The right item `J ?x` is unified with the first left item, `J 1`. The witness `2` would have succeeded. When the choice matters, instantiate the quantifier by hand before calling the tactic, or reorder the left side.

**Matching is up to definitional equality only.** A hypothesis `a = b` in the context does not make `J a` cancel against `J b`. Rewrite with the hypothesis first.

**A witness cannot mention variables that are introduced later.** The metavariables for the quantifiers of the original right side are created in the first run of Section 1.4.3. If a wand step then exposes a new existential on the left, its variable is extracted in the second run of the algorithm and is not in the context of the earlier metavariables.

```lean
example {H1 : HProp} {J : Nat → HProp} :
    H1 ✶ (H1 -✶ ∃✶ x, J x ✶ ⌈x = 1⌉) ==> ∃✶ y, J y
-- x✝ : ℕ
-- a✝ : x✝ = 1
-- ⊢ J x✝ ==> J ?x
-- ⊢ ℕ
```

**Cleanup by hypothesis applies to every open goal, including goals whose statement is a data type and not a proposition.** The cleanup step closes a goal when some hypothesis has the goal's statement as its type. A witness goal whose statement is a type such as `ℕ` is therefore closed by a variable of that type, if the context contains one.

```lean
example {H : HProp} (n : Nat) : H ==> ∃✶ x : Nat, ⌈x > 3⌉ ✶ H
-- ⊢ n > 3
```

Here the witness was unconstrained, the cleanup chose `n`, and the remaining goal may be unprovable. The same applies to goals that were open before the tactic was called. If the goal list contains an unassigned metavariable `?F : HProp`, the cleanup assigns it some variable of type `HProp` from the context. When a witness or a frame is to be chosen deliberately, use `xsimpl_core`, which omits the cleanup, and then solve that goal explicitly.

**Wand elimination is eager.** A wand on the left is eliminated as soon as its premise is present, provided cancellation has not already removed it. If the right side required the premise for another purpose, the residual will be unprovable.

## 1.7 Related tactics

`xsimpl_core` is `xsimpl` without the cleanup of Section 1.4.7.

`xsimpl_core_with t` extends the algorithm by a user tactic `t`. After the steps of Sections 1.4.1 to 1.4.6, each remaining goal is given to `t`. If `t` fails on a goal, the goal is kept. If `t` succeeds, the algorithm is run again on every goal that `t` produced, and those results are given to `t` in turn. The loop ends when `t` fails on every remaining goal.

Frame inference is implemented in this way, by the tactic `xsimpl_granular_frames`. In the goal

```lean
example {H1 H2 H3 : HProp} : ∃ F, H1 ✶ H2 ✶ H3 ==> H1 ✶ F := by
  refine ⟨?F, ?_⟩
  xsimpl_granular_frames
```

the right side contains the bare metavariable `?F`. The steps of Section 1.4 cancel `H1` and stop, since cancellation never assigns such a metavariable. The extension tactic then assigns `?F := H2 ✶ ?F'`, with `?F'` new; the next run cancels `H2`; and so on, until the left side is empty and the last metavariable is assigned `emp`. The result is `?F := H2 ✶ H3`. A metavariable on the left is treated symmetrically and receives the items that the right side lacks, which gives biabduction.

The library also provides one tactic for each phase taken alone: `xsimpl_normalize`, `xsimpl_extract_step`, `xsimpl_instantiate_step`, `xsimpl_cancel_all`, `xsimpl_cancel_wand`, `xsimpl_wand_intro`, and `xsimpl_step`, which applies the first of these that makes progress. They are useful for stepping through a proof by hand. Unlike `xsimpl`, each of them fails when it has nothing to do.

## 1.8 Implementation

The implementation is in `Sep/Xsimpl/Core.lean`. This section explains its organisation and two design decisions that affect behaviour: the direct construction of proof terms, and the notion of equality used in matching.

### Terms, goals and proof construction

A Lean tactic is a program that runs during *elaboration*, the phase in which Lean processes a source file and converts each declaration into a checked term. It has access to the current goals, each of which is a metavariable. The statement of a goal is a value of type `Expr`, the data type of Lean terms: an `Expr` is a tree whose nodes are constants, applications, binders, variables and metavariables. A tactic inspects the tree, builds another `Expr` that is a proof of the statement, possibly containing new metavariables, and assigns it to the goal.

`xsimpl` works at this level throughout. It does not call `simp`, `apply` or `rw`. For each step it constructs the proof term directly as an application of a lemma to explicit arguments. For example, the function that performs one instantiation step on the right creates a metavariable `m` for the new goal and assigns to the old goal the term

```
nt_exr A ?y K L m
```

where `A` is the type of the bound variable, `?y` the witness metavariable, `K` the body of the quantifier as a function of the bound variable, and `L` the left side. The tactic supplies every argument itself, including those that the statement marks as implicit; the two arguments for the logic and its instance are omitted here. `nt_exr` is the class rule `ex_r` under another name:

```lean
theorem nt_exr {α : Type w} [SepLogic α] {A : Sort z} (x : A) {J : A → α} {l : α}
    (h : l ==> J x) : l ==> ex J
```

The file begins with about forty such lemmas, prefixed `nt_`, one for each elementary step: transitivity, framing, commutation, moving a quantifier across a conjunction in either direction, extraction and instantiation of pure and existential items, and the wand rules.

Direct construction was chosen for speed and for predictability. General tactics such as `simp` traverse and check again terms whose shape `xsimpl` already knows, and their behaviour depends on the set of lemmas in scope.

### Recognising the logic

The function `sepGoal?` determines which logic a goal belongs to. It reads the lemmas tagged `xsimpl_fold`, finds the one whose left side has the same head constant as the goal (the *head constant* of a term `f a b` is the constant `f` that is applied), and from the whole family builds a record, `NCtx`, that tells the rest of the code how to recognise and construct each connective of this logic. If no registered logic matches, it tries to read the goal as one stated in the class operations. If that also fails, the goal is not an entailment known to the tactic and is left unchanged.

Because the connectives are located through this record, the tactic operates on the user's own constants. Residual goals are displayed in the logic's notation without a translation step.

A check called `spine` then traverses both sides and verifies that every construct is one the later phases can handle. If it is not, the goal is again left unchanged.

### The main function

`nativeGoal` carries out Sections 1.4.1 to 1.4.6 in sequence. Its helpers correspond to the phases.

| Function | Phase |
|---|---|
| `flat`, `flatN`, `itemNorm`, `wandNorm` | flattening and normalisation of items |
| `wholeEq`, `permClose` | immediate closure |
| `lhsBatch`, `lhsRec` | extraction on the left |
| `rhsStep` | one instantiation on the right |
| `cancelScan`, `cancelStep` | cancellation |
| `residualEq` | closure of a residual by reflexivity |

`nativeGoal` calls itself after a wand step. It is wrapped by `nativeOrNone`, which saves the complete *tactic state*, that is, the goal list and the assignment of every metavariable, beforehand and restores it if any error occurs. Because of this wrapper the tactic never fails and never leaves a partially transformed goal.

`xsimplDriver` applies `nativeOrNone` to every open goal and implements the loop of `xsimpl_core_with`. `xsimplClean` is the cleanup. The tactic itself is a *macro*, a rule that replaces one piece of syntax by another before it is run. Its expansion has two lines:

```lean
macro_rules
  | `(tactic| xsimpl) => `(tactic| (
      xsimpl_core
      all_goals (
        try xsimpl_clean
      )
    ))
```

### Permutations by computation

Cancellation must prove that the left list is a permutation of the cancelled items followed by the remainder, and likewise on the right. A proof assembled from individual uses of commutativity and associativity has a size quadratic in the length of the list. The tactic instead uses a single lemma whose hypothesis is a computation.

```lean
theorem nt_perm_idx {α : Type w} [SepLogic α] (env : PTree α) (l r : List Nat)
    (h : permChk l r = true) : starI env l ==> starI env r
```

Here `env` is a table of the items, `l` and `r` are lists of indices into the table, `starI env l` is the conjunction of the items selected by `l`, and `permChk l r` is a Boolean function that checks that `l` and `r` are both permutations of `0, …, n-1`. The tactic supplies the two index lists and the proof `Eq.refl true` for `h`. The kernel accepts this proof by evaluating `permChk`, which takes time linear in the list. This technique, in which a proof obligation is discharged by running a verified checker inside the kernel, is called proof by reflection.

### Matching

Cancellation compares items with `cheapDefEq`. By default this is Lean's unifier `isDefEq` at the default transparency. The *transparency* is a setting of the unifier that determines which definitions it may unfold; the default setting unfolds ordinary definitions. Section 1.4.4 described the consequences.

`xsearch`, the subject of the next chapter, calls `xsimpl` many times on goals that contain recursive predicates. For such goals it switches the comparison of metavariable-free items to *reducible* transparency, under which only definitions explicitly marked reducible are unfolded. In that mode two atoms cancel only if they are equal up to such unfoldings. The switch is internal to `xsearch` and does not affect direct uses of `xsimpl`.

---

# Chapter 2. `xsearch`

## 2.1 Purpose

`xsearch` is applied to a goal `H ==> H'` over `HProp` in which either side may mention inductively defined predicates. Typical goals are

```lean
example (x y z : Nat) :
    ⌈x ≠ 0⌉ ✶ x ↦ (y : Int) ✶ ⌈y ≠ 0⌉ ✶ y ↦ (z : Int) ✶ ⌈z ≠ 0⌉ ✶ z ↦ (0 : Int)
      ==> p_ls x 0 := by
  xsearch

example (x y : Nat) : p_ls x y ✶ p_ls y 0 ==> p_ls x 0 := by
  xsearch
```

where `p_ls a b` is a list segment from `a` to `b`. The first goal requires the predicate on the right to be unfolded three times and each unfolding to be matched against a cell. The second cannot be proved by unfolding at all; it needs an inductive argument.

`xsimpl` proves neither goal, because it treats `p_ls x 0` as an atom. `xsearch` differs from `xsimpl` in three respects.

- It unfolds predicates, chooses between disjuncts, and backtracks when a choice fails.
- It either closes the goal or fails with an error. It never returns a simplified goal.
- It is not designed to be predictable. It is a sequence of specialised procedures, tried one after another under a time budget.

The tactic was developed against the entailment divisions of the SL-COMP 2019 benchmark suite, and much of its code was produced by automated program search scored on those problems. This origin explains two features of its design. The procedures are tuned to the shapes of formula that occur in the benchmarks, and the tactic contains a component whose only purpose is to recognise invalid entailments quickly, since a large part of the benchmark problems are invalid.

## 2.2 The input language

`xsearch` is specific to `HProp`. It recognises the following constructs.

- The connectives of Chapter 1: `✶`, `emp`, `⌈P⌉`, `∃✶`, `-✶`.
- Cells `p ↦ v`. Locations have type `Nat`. Several components assume that values have type `Int`, with a location stored as a value through the coercion from `Nat`.
- Disjunction of heap predicates, written `hor` in the examples of this chapter.
- Predicates registered by the user.

### Registering a predicate

A predicate is made known to the tactic by an equation tagged with the attribute `xsearch_unfold`. The left side of the equation must be an application of a constant; that constant is the *head* of the predicate.

```lean
@[xsearch_unfold] theorem e_ls (a b : Nat) :
    p_ls a b = hor (⌈a = b⌉ ✶ emp)
      (∃✶ u : Nat, ⌈a ≠ b⌉ ✶ (⌈a ≠ 0⌉ ✶ a ↦ (u : Int)) ✶ p_ls u b) := ...
```

The right side is the *body*. The tactic never inspects the definition of `p_ls`; everything it knows about the predicate it reads from this equation. To *unfold* an occurrence `p_ls s t` is to rewrite the goal with the equation instantiated at `s` and `t`.

The tactic classifies each predicate from its body.

- A predicate is *recursive* if its head is reachable from its own body through the bodies of registered predicates.
- A non-recursive predicate whose body is not a disjunction and mentions no registered predicate is a *macro*. Macros are always unfolded.
- The remaining non-recursive predicates are unfolded during preprocessing under the conditions stated in Section 2.5, and otherwise during search.

### Conventions that are matched by name

Three constructs are recognised by the name of a constant, not by its definition. A construct that does not follow its convention is not recognised by the tactic.

*Disjunction.* The library defines `hdisj H1 H2 := fun h => H1 h ∨ H2 h`. In a goal or a body, any constant whose last name component is `hor` is treated as disjunction and replaced by `hdisj`. A goal may also use `hdisj` directly. The replacement is justified by definitional equality, so the user's `hor` must have the same definition as `hdisj`, and its arguments must be the `Params` instance followed by the two disjuncts. (`Params` is the library's type class that fixes the type of values stored in the heap; `HProp` depends on an instance of it.)

*Least fixed points.* A predicate is recognised as a least fixed point if unfolding its definition by one step yields an application of a constant whose last name component is `lfp`, applied to a functional and an argument. The library's own least fixed point is `lfpG F a := fun h => ∀ X, (∀ b, F X b ==> X b) → X a h`, and its lemmas are stated for `lfpG`; the user's `lfp` must be definitionally equal to it. One component of the tactic, the segment engine of Section 2.7, applies only to such predicates.

*Fixed-point lemmas.* The proof by fixed-point induction of Section 2.6, and one of the recognition paths of the segment engine, obtain the monotonicity proof of the functional from an occurrence of the constant `Bench.lfp_unfold` in the proof of the unfold equation, and use `Bench.lfp_pre`. These names are fixed in the code. For a predicate defined outside the namespace `Bench`, these two components fail and the tactic proceeds with the others.

## 2.3 Structure of the tactic

The tactic is the following macro. The combinator `first | t1 | t2 | …` runs `t1`; if `t1` fails it restores the state and runs `t2`; and so on. It fails if every alternative fails. `try t` runs `t` and ignores its failure. `done` succeeds exactly when no goals remain.

```lean
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

Read from top to bottom, the macro has five parts.

1. `xsearch_scope` sets the time budget (Section 2.9) and, if the goal mentions a registered predicate, switches `xsimpl` to the restricted matching described at the end of Chapter 1.
2. `xsearch_refute` and `xsearch_cmodel` reject goals that appear to be invalid (Section 2.4). `xsearch_start` clears the caches left by earlier calls.
3. The first alternative of the outer `first` is `xsimpl` followed by a prover for pure goals. If this closes every goal, the tactic terminates successfully. Goals without predicates are usually proved here.
4. Otherwise the goal is preprocessed (Section 2.5).
5. Four proof procedures, called *engines*, are then tried in a fixed order: the segment engine `xsearch_wseg` (Section 2.7), the witness enumerator `xsearch_wit` (Section 2.8), the backtracking search `xsearch_backtrack` (Section 2.6), and the witness enumerator with case analysis. If the segment engine succeeds but leaves goals open, the backtracking search is run on those goals.

The order of the engines reflects their cost and their reliability on the benchmark problems. The segment engine is deterministic on the class of goals it accepts, and it fails quickly on goals outside that class. The backtracking search is general and may consume the whole budget.

## 2.4 Rejection of invalid goals

Two checks run before any proof is attempted. Each ends the tactic with an error if it concludes that the entailment does not hold.

### Unconstrained variables

`xsearch_refute` collects the free variables of the right side that occur as the address of a cell or as an argument of a registered predicate. Occurrences under `✶` and `∃✶` are examined; occurrences under a disjunction are not. An atom whose arguments are all identical, such as `p_ls x x`, is skipped. If a collected variable does not occur anywhere in the left side, the tactic fails with

```
xsearch: unconstrained rhs variable
```

The justification is that the left side then places no constraint on the variable, whereas the right side does.

The check is syntactic and reads only the entailment. It does not consult the hypotheses in the context.

```lean
example (p q : Nat) (v : Int) (h : q = p) : p ↦ v ==> q ↦ v := by
  xsearch   -- error: xsearch: unconstrained rhs variable
```

This goal is valid. Substitute such equations with `subst` before calling the tactic.

### Countermodels

`xsearch_cmodel` looks for a counterexample to the entailment. It has two phases.

The first phase compares footprints. For each side it computes bounds on the number of cells the side can occupy. A cell counts as one. For a registered predicate the procedure derives, from the unfold equation, a lower bound on its number of cells, and where possible an exact count as a linear function of one argument. If the two sides cannot have the same number of cells, and the pure assertions of the left side together with the arithmetic hypotheses of the context are satisfiable over the integers, the phase reports a counterexample. This phase unfolds nothing.

The second phase constructs explicit models. It runs only when the context contains nothing but variables of type `Nat` and `Int`, and values are of type `Int`. It unfolds each predicate on the left to a depth of zero, one or two, in several combinations. From each resulting formula it builds a concrete heap and a concrete value for every variable, taking variables to be distinct unless forced equal and then also trying to identify one pair. It checks that the heap satisfies the left side. It then decides, by exhaustive search over the ways the right side can be unfolded and its existentials instantiated, whether the same heap satisfies the right side. The search over instantiations draws candidate values from the heap and from the variables. If the search completes without finding a derivation, the heap is reported as a counterexample. If the search is cut off by any bound, nothing is reported.

A reported counterexample ends the tactic with

```
xsearch: countermodel
```

Both goals below are invalid, and both are rejected with this error. In the first, `y` need not be null. In the second, `z` may be an address inside the first segment.

```lean
example (x y : Nat) : p_ls x y ==> p_ls x 0
example (x y z : Nat) : p_ls x y ✶ p_ls y z ==> p_ls x z
```

### Status of the verdict

The verdict is a reason for the tactic to stop. It is not a proof, and no proof term is built from it. A wrong verdict causes the tactic to fail on a valid goal; it cannot cause an invalid goal to be accepted.

Wrong verdicts are possible. The first phase checks the pure part of the left side for satisfiability but not the heap. A goal whose left side is contradictory as a heap is valid, and is rejected:

```lean
example (x : Nat) : x ↦ (1 : Int) ✶ x ↦ (2 : Int) ==> emp := by
  xsearch   -- error: xsearch: countermodel
```

The first phase is also run at every node of the backtracking search, where a positive verdict discards that branch only.

## 2.5 Preprocessing

The preprocessing steps are deterministic and are not undone. Each either improves the goal or leaves it unchanged. Most of them skip goals that contain metavariables.

**Substitution of equalities** (`xsearch_eqsubst`). For each pure item `⌈a = b⌉` on the left in which `a` or `b` is a variable, the equation is added to the context and the variable is eliminated by substitution throughout the goal.

**Removal of trivial pure items** (`xsearch_trivpure`). Items `⌈t = t⌉` and `⌈True⌉` are deleted from both sides.

**Macro expansion** (`xsearch_macros`). Occurrences of macros are unfolded wherever they appear. A non-recursive, non-disjunctive predicate that mentions other predicates is unfolded on the left if it does not also occur on the right. On the right it is unfolded if every existential variable of its body can be determined, either by a pure equation of the body or by a cell of the body whose address is already held by exactly one cell of the left side.

**Disequalities stated on the left** (`xsearch_pfacts`). A pure item `⌈a ≠ b⌉` on the left is copied into the context when `a` or `b` is an argument of some predicate occurrence in the goal.

**Disequalities from separation** (`xsearch_facts`). For every two cells `p ↦ _` and `q ↦ _` at the top level of the left side, the hypothesis `p ≠ q` is added to the context. This is the only step of the tactic that uses the meaning of `✶` on cells directly, beyond its algebraic laws. The number of hypotheses is quadratic in the number of cells.

**The one-point rule** (`witDetermined`, run inside the engines). If the right side is `∃✶ x, … ⌈x = t⌉ …` with `t` not mentioning the bound variables, the quantifier is instantiated with `t`.

### Pure goals

Wherever a goal that is not an entailment arises, the tactic `xsearch_pure` attempts it. It first looks for a contradiction in the context, namely a hypothesis `False` or `a ≠ a`. It then tries, in this order: `rfl`; a hypothesis that states the goal; `trivial`; a hypothesis that states a disequality in the opposite orientation; and a prover for arithmetic side conditions.

The arithmetic prover first tries to match the goal against the hypotheses and against a short fixed list of lemmas about `Nat`. It evaluates closed numeric propositions. For everything else it calls Lean's `omega`, with all hypotheses of the context available. `omega` decides linear arithmetic over `Nat` and `Int`. No other decision procedure and no `simp` set is used for pure goals. A pure obligation is therefore proved only if it is closed by one of the simple steps above or lies within linear arithmetic.

## 2.6 The backtracking search

This engine is a depth-first search over proof steps. It consists of two mutually recursive procedures.

`searchSolve` takes the current list of goals. It normalises them, and then calls `branchGoal` on each goal that remains, in order. It fails if any goal remains unsolved.

`branchGoal` takes one entailment. It computes an ordered list of *alternatives*. Each alternative is a proof step that replaces the goal by zero or more new goals. `branchGoal` tries the alternatives in order: it applies the step and calls `searchSolve` on the result. If that succeeds, `branchGoal` succeeds. If it fails, the state is restored to what it was before the step, and the next alternative is tried. If all alternatives fail, `branchGoal` fails.

Since `searchSolve` requires every goal produced by a step to be solved, a step that splits a goal into two succeeds only if both parts are proved.

### Normalisation

Before any choice is made, `searchSolve` applies the following to every goal.

1. Disjunctions are moved to the outside: `✶` is distributed over disjunction, and an existential over a disjunction is split into a disjunction of existentials.
2. The one-point rule is applied.
3. `xsimpl` is run, including its cleanup.
4. Equations in the context whose one side is a variable are eliminated by substitution, and `xsimpl` is run again on any goal this changed.
5. `xsearch_pure` is run on the pure goals.

Almost all of the proof construction takes place in step 3. The search itself only decides which predicate to unfold and which disjunct to take; after each such decision `xsimpl` extracts, instantiates and cancels. The behaviour of `xsimpl` described in Chapter 1 therefore carries over. In particular, existential witnesses on the right are found by unification during cancellation, and the first match is taken.

### Pruning

At the start of `branchGoal`, two tests may fail the goal immediately.

The search records every goal on which `branchGoal` has failed, together with its context. If the same goal with the same context is reached again, it fails at once. Goals containing metavariables are not recorded.

The footprint phase of the countermodel check is run on the goal. A positive verdict fails the goal.

### Alternatives

The list of alternatives depends on the shape of the goal after normalisation.

**The left side is a disjunction.** There is one alternative: case analysis. The goal `hdisj H1 H2 ==> R` is replaced by `H1 ==> R` and `H2 ==> R`.

**The right side is a disjunction.** The alternatives are to prove the left disjunct and to prove the right disjunct. They are ordered by a score computed for each disjunct against the left side. A disjunct that contains `⌈a ≠ a⌉` is ranked last. Otherwise the disjunct is preferred that has more cells whose address is the address of a cell on the left, then more cells whose address is an argument of a predicate on the left. Ties are broken in favour of the disjunct that mentions fewer predicates absent from the left.

**Neither side is a disjunction.** The alternatives are, in outline and in order:

1. unfolding the single recursive predicate on the left, when the left side has fewer cells than some non-recursive predicate on the right requires;
2. steps for universally quantified wands (an item `∀ x, A -✶ B`, which a heap satisfies if it satisfies `A -✶ B` for every `x`), for non-separating conjunctions (an item that a heap satisfies if it satisfies both conjuncts), and for synthesised lemmas. The first instantiates a quantified wand on the left at the address of a cell on the left, or so that its conclusion matches an atom on the right. The second selects one conjunct of a non-separating conjunction on the left. The third is described below;
3. fixed-point induction, described below;
4. elimination of a wand `A -✶ B` on the left, with either the whole remainder of the left side or a syntactically matching part of it used to prove `A`;
5. *forced* unfoldings, defined below;
6. unfolding a non-recursive predicate on the left;
7. unfolding a predicate on the right;
8. unfolding a recursive predicate on the left.

An occurrence of a predicate on the right is *forced* when its root argument is the address of a cell on the left. The root argument of a predicate is the parameter that is the address of the first cell in its body. The justification is that a predicate rooted at an allocated address can only be established by consuming that cell, which requires the predicate to be unfolded. When forced occurrences exist, alternatives 7 and 8 are not offered at that node.

### An example

Consider the goal

```
⌈x ≠ 0⌉ ✶ x ↦ y ✶ p_ls y 0  ==>  p_ls x 0
```

Normalisation runs `xsimpl`, which moves `x ≠ 0` into the context. Nothing cancels.

`branchGoal` finds that the occurrence `p_ls x 0` on the right is forced: the root argument of `p_ls` is its first, and `x` is the address of a cell on the left. The forced unfolding rewrites the right side to

```
hdisj (⌈x = 0⌉ ✶ emp) (∃✶ u, ⌈x ≠ 0⌉ ✶ (⌈x ≠ 0⌉ ✶ x ↦ u) ✶ p_ls u 0)
```

`searchSolve` is called. Normalisation changes nothing, and `branchGoal` is entered with a disjunction on the right. The second disjunct contains a cell at `x`, which is the address of a cell on the left; the first contains none. The second disjunct is tried first, giving

```
x ↦ y ✶ p_ls y 0  ==>  ∃✶ u, ⌈x ≠ 0⌉ ✶ (⌈x ≠ 0⌉ ✶ x ↦ u) ✶ p_ls u 0
```

`searchSolve` is called again, and this time normalisation finishes the proof. `xsimpl` replaces `u` by `?u`, creates two goals `x ≠ 0`, cancels `x ↦ ?u` against `x ↦ y`, which assigns `?u := y`, and cancels `p_ls y 0`. The cleanup closes both pure goals by the hypothesis.

Had the second disjunct failed, the state would have been restored and the first disjunct tried.

### Fixed-point induction

Some entailments between recursive predicates cannot be proved by unfolding, because unfolding the predicate on the left yields a goal of the same form. An example is `P x ==> Q x`, where `P` and `Q` are two recursive definitions of the same structure. For goals whose left side, apart from pure items, is a single predicate occurrence `P args`, and whose right side mentions a different predicate, the search offers induction.

The second goal of Section 2.1, `p_ls x y ✶ p_ls y 0 ==> p_ls x 0`, is not of this shape, since its left side has two occurrences. The backtracking search alone does not prove it. It is proved by the segment engine of Section 2.7.

A predicate defined as a least fixed point of a functional `F` satisfies the following principle, stated in the library as `lfpG_induct_with`.

```lean
theorem lfpG_induct_with {α : Type} (F : (α → HProp) → α → HProp) (M : α → HProp)
    (hmono : ∀ X Y : α → HProp, (∀ a, X a ==> Y a) → ∀ a, F X a ==> F Y a)
    (hfold : ∀ a, F (lfpG F) a ==> lfpG F a)
    (hM : ∀ a, F (fun b => hwith (lfpG F b) (M b)) a ==> M a) (a : α) : lfpG F a ==> M a
```

Here `hwith H1 H2` is the non-separating conjunction: a heap satisfies it if it satisfies both `H1` and `H2`. To prove `P a ==> M a` for all `a` it suffices to prove the premise `hM`: the body of `P`, in which each recursive occurrence `P b` has been replaced by `hwith (P b) (M b)`, entails `M a`. The conjunct `M b` is the induction hypothesis. The conjunct `P b` is kept because the proof of a case may need the predicate itself and not the hypothesis.

The tactic takes `M` to be the right side of the goal, generalised over the arguments of the left predicate. It applies the principle and passes the premise `hM` to the search as a new goal. In that goal each `hwith` gives rise to alternatives that select one of its two conjuncts.

### Synthesised lemmas

For a recursive predicate `a` on the left and a different predicate `r` on the right, the search may conjecture a lemma of the form

```
a xs  ==>  ∀ ws, (Q -✶ r ys)
```

Here `∀ ws, H` is universal quantification over heap predicates: a heap satisfies it if it satisfies `H` for every value of `ws`. The lemma states that `a xs` together with an additional resource `Q` entails `r ys`. The candidates for `Q` are obtained by matching the base case of `a` against a recursive case of `r` and taking the single atom that remains unmatched. Each conjecture is proved by fixed-point induction on `a`, with the search itself proving the cases; within that proof no further lemmas are conjectured. A proved lemma is used by replacing the occurrence of `a` on the left by the wand, which alternative 4 then eliminates. Proofs and failed attempts are cached for the duration of the call.

## 2.7 The segment engine

The backtracking search handles the composition of segments only through induction, and induction requires a goal of a restricted shape. The segment engine treats composition directly. It applies to predicates that describe a path through the heap.

### The generic segment

The library defines one predicate to which all such paths are mapped.

```lean
def wseg {σ : Type} (c : σ → σ → Int → HProp) : Nat → Int → σ → σ → HProp
  | 0, n, s, t => ⌈s = t ∧ n = 0⌉
  | k + 1, n, s, t => ∃✶ s', ∃✶ w, c s s' w ✶ wseg c k (n - w) s' t
```

`wseg c k n s t` is a path of exactly `k` steps from state `s` to state `t`. The parameter `c s s' w` is the heap occupied by one step from `s` to `s'`, and `w` is the *weight* of the step. The index `n` is the sum of the weights. A state is a tuple; for a singly linked list it contains the current address, and for other structures it may contain a previous address, a remaining length, or values that do not change along the path.

Because the number of steps is an explicit index, the laws for joining, splitting and converting paths are lemmas, each proved once by induction on `k`.

```lean
wseg_join  : wseg c k₁ n₁ s t ✶ wseg c k₂ n₂ t u ==> wseg c (k₁ + k₂) (n₁ + n₂) s u
wseg_split : wseg c (k₁ + k₂) n s u ==> ∃✶ t, ∃✶ m, wseg c k₁ m s t ✶ wseg c k₂ (n - m) t u
wseg_cell  : c s t w ==> wseg c 1 w s t
wseg_uncell : wseg c 1 n s t ==> c s t n
wseg_nil   : s = t → n = 0 → emp ==> wseg c 0 n s t
wseg_cong  : k = k' → n = n' → s = s' → t = t' → wseg c k n s t ==> wseg c k' n' s' t'
wseg_map   : (∀ s s' w, c s s' w ==> c' (f s) (f s') w) →
             wseg c k n s t ==> wseg c' k n (f s) (f t)
```

### Recognition

For each registered predicate the engine attempts to read, from the unfold equation, a description of the predicate as a path. In the principal case the following must hold.

- The predicate is a least fixed point in the sense of Section 2.2.
- Its body has exactly one branch without a recursive occurrence, and every other branch has exactly one.
- Some parameters, of type `Nat` or `Int`, are passed to the recursive occurrence with a changed value. These are the *moving* parameters and form the state.
- Optionally one `Int` parameter decreases by a fixed linear amount at each step. It is the *counter*, and the amount is the weight.

From the recursive branches the engine constructs the step relation `c`. From the base branch it determines how a path ends: which state components are fixed, and which cells, if any, the base case itself occupies. Parameters that do not change but occur in the cells or the pure assertions of a step are added to the state as constant components.

If no description is found for a predicate, the engine does not use that predicate. If none of the predicates in the goal is recognised, the engine fails and the next engine is tried.

### Per-predicate lemmas

For a recognised predicate `P` the engine proves the lemmas that connect it to `wseg`. They are proved when first needed and kept for the duration of the call. The two essential ones are, schematically,

```
Abs  :  P xs  ==>  ∃ k n …, wseg c k n s t ✶ tail ✶ ⌈cond k⌉
Conc :  cond k  →  wseg c k n s t ✶ tail  ==>  P xs
```

where `s` and `t` are the start and end states determined by `xs`, `tail` is the heap of the base case, and `cond k` restricts the admissible number of steps. `Abs` is proved by fixed-point induction on `P`. `Conc` is obtained from a general lemma of the library, whose premises are that a segment of minimal length folds into `P` and that one further step in front of a `P` folds into `P`.

Further lemmas are derived as required: an invariant that holds of every segment, such as `n = k` when all weights are one; a lemma turning one cell into a segment of length one; a lemma mapping the segments of one predicate to those of another whose cells have the same layout; and lemmas that change a constant component of the state. The last kind is needed to compose predicates such as `p_ls`, whose step asserts that the current address differs from the end address. A segment ending at `y` can be converted to a segment with a different end only if none of its steps is located at the new end, and the lemma requires the new end to be null or to be allocated in the remainder of the heap.

### Planning and execution

Given a goal, the engine proceeds in rounds. In each round it chooses one recognised predicate as the *carrier* and expresses a part of both sides in terms of the carrier's `wseg`.

*Left side.* Each cell and each predicate occurrence on the left that can be mapped to the carrier is a *piece* with a start state and an end state. From a chosen start, the engine follows pieces whose start is the current state until none applies. This traversal is deterministic.

*Right side.* The existentials of the right side are replaced by metavariables. From the same start, the engine searches for a sequence of cells and predicate occurrences of the right side that covers the same path. This search backtracks, under a bound quadratic in the size of the right side.

*Lengths.* Each piece has a symbolic number of steps. The engine solves for the lengths of the right pieces: the total must equal the total of the left pieces, at most one unknown length absorbs the difference, and every other unknown length is set to its minimum. The resulting conditions are proved by the arithmetic prover of Section 2.5.

*Execution.* When a plan is found the engine rewrites the left pieces with `Abs` and `wseg_cell`, joins them with `wseg_join`, splits the result at the lengths computed for the right side with `wseg_split`, and rewrites the right pieces backwards with `Conc` and `wseg_uncell`. What remains on both sides is passed to `xsimpl` and the pure prover.

If the goal is not closed, and the number of predicate occurrences and cells on the right has decreased, another round is run on the remainder.

For `p_ls x y ✶ p_ls y 0 ==> p_ls x 0` the plan has two left pieces, from `x` to `y` and from `y` to `0`, and one right piece from `x` to `0`. The left pieces become segments of lengths `k₁` and `k₂`. The end of the first is changed from `y` to `0`, which is permitted because `0` is null. The two are joined into a segment of length `k₁ + k₂`, and `Conc` turns it into `p_ls x 0`.

### Preliminary steps

Before planning, the engine introduces the existentials and pure assertions of the left side into the context and adds, for each predicate on the left that has a counter, the lower bound on that counter. It closes the goal outright if two cells on the left have the same address. If the left pieces form a cycle, it derives the consequences, which either contradict the context or force some pieces to be empty.

### Sets of admissible lengths

For some predicates the number of steps is restricted to a set that is not an interval: a list of even length, or a family of mutually recursive path predicates. For these the engine computes the set of admissible lengths of each predicate up to a bound, conjectures that the set is eventually periodic, with a minimum `m`, a period `p` and a set of residues, and uses the conjecture as `cond k`. The conjecture is verified by two checking functions defined in the library, each with a soundness theorem, one for each direction of the equivalence between "length `k` is derivable from the branches" and "`k` belongs to the periodic set". The engine supplies the data for the checks, and the kernel evaluates them, as in the permutation check of Section 1.8. If the conjecture or a check fails, the predicate is handled by the principal case or not at all.

## 2.8 The witness engines

The engines described so far determine an existential witness on the right in one of three ways: by the one-point rule, by unification in `xsimpl`, or by the plan of the segment engine. `xsearch_wit` handles goals in which none of these suffices because the bound variable occurs only as the argument of predicates.

It applies when the right side is a sequence of existentials over locations followed by cells and predicates only, and the left side also consists of cells and predicates. For each bound variable it collects candidate terms from the left side. A term is a candidate if it occurs on the left in the same argument position of an atom with the same head; candidates supported by more atoms are ranked first. The remaining terms of type `Nat` on the left, and `0`, are added at the end. For each tuple of candidates in turn, the engine instantiates the quantifiers, discards the tuple if the countermodel check refutes the instantiated goal, and otherwise runs the other engines on it within a share of the remaining time.

`xsearch_wit cases` is tried last. It applies when no single tuple of witnesses is correct for all values of the variables. It unfolds a predicate on the left, splits the resulting disjunction, and in each case determines for each candidate tuple the pure conditions under which the tuple would work. It then performs a case analysis on those conditions, having first proved that they are exhaustive, and uses the corresponding tuple in each case.

## 2.9 Time

The tactic measures time in *heartbeats*, the unit by which Lean accounts for computation, and not in seconds. The budget of one call is 264 million heartbeats. It is fixed in the code and cannot be set from the tactic syntax.

Since heartbeats count computation steps, a call on a given goal in a given environment (the collection of declarations available at that point of the file) consumes the same number on every machine. Success or failure of the tactic does not depend on the speed or load of the machine.

The budget is divided as the search proceeds. At the outermost level of the backtracking search, a forced unfolding that is not the last alternative receives an equal share of what remains, so that a single branch cannot consume the whole budget. The witness enumerator divides the remaining budget among the tuples still to be tried. When a share is exhausted the branch fails and the search continues with the next alternative.

Lean enforces its own limit on every declaration through the option `maxHeartbeats`, whose default is 200 million heartbeats. Both figures are in the same unit, and Lean's limit is the lower. A search can therefore never use the tactic's full budget unless the option is raised. A long search is therefore stopped by Lean with a `(deterministic) timeout` error before the tactic's own accounting ends it. This error is not an ordinary tactic failure and is not intercepted by `first`; the alternatives that would have followed are not tried.

## 2.10 Properties a user may rely on

**The tactic closes the goal or fails.** On failure the goal and the context are unchanged. On success no goals remain. The hypotheses added during preprocessing are therefore never visible.

**The result is sound.** Every step that contributes to a successful proof constructs a proof term: an application of a library lemma, a rewrite with a registered equation, a term produced by `xsimpl` or `omega`, or a lemma synthesised during the call. The kernel checks the complete term. The countermodel check, the failure record, the scoring of disjuncts, the classification of predicates and the plans of the segment engine influence only which proof is attempted. The source contains no `sorry`, no additional axiom and no use of `native_decide`, a tactic that trusts the result of compiled code without a check by the kernel.

**The result is reproducible.** For a fixed goal, environment and Lean version, the tactic performs the same computation on each run.

**Failure is not evidence of invalidity.** The tactic is incomplete in each of its parts, and its rejection checks can err, as shown in Section 2.4.

Only the first three messages below indicate why the tactic stopped.

| Message | Meaning |
|---|---|
| `xsearch: unconstrained rhs variable` | rejected by the syntactic check of Section 2.4 |
| `xsearch: countermodel` | rejected by the countermodel check |
| `(deterministic) timeout` | stopped by Lean's heartbeat limit |
| `wit: no witness`, `wit: no case`, `wit: goal`, `wg: goal` and similar | every engine failed; the text is that of the last one tried and carries no further information |

The following limitations have been observed or follow from the description above.

**Matching is syntactic.** Within `xsearch`, atoms that mention predicates cancel only when they are equal up to reducible unfolding. Most auxiliary procedures compare terms for syntactic identity. Addresses written `x + 0` and `x` are different terms to the tactic. Normalise such expressions beforehand.

**Hypotheses in the context are used only for pure reasoning.** Arithmetic hypotheses are available to `omega`, and an entailment that is literally a hypothesis closes a goal of the same statement. Equations in the context are not used by the rejection checks, as the example in Section 2.4 shows.

**A witness is chosen before a case split on the left.** Normalisation runs `xsimpl` before `branchGoal` considers the shape of the goal. If the right side begins with an existential and the left side is a disjunction, the quantifier is instantiated by a single metavariable, and both cases must then agree on its value.

```lean
example (x : Nat) : hor (x ↦ (1 : Int)) (x ↦ (2 : Int)) ==> ∃✶ v : Int, x ↦ v := by
  xsearch   -- fails
```

The same statement with the quantifier inside a disjunction on the right is proved.

**A contradictory left side may be rejected.** See Section 2.4.

**The naming conventions of Section 2.2 are required.** A disjunction not named `hor` or `hdisj`, or a fixed point not named `lfp`, is an opaque atom.

**The linearity of `HProp` is respected.** A goal that would require a resource to be discarded, such as `H ✶ x ↦ 1 ==> x ↦ 1`, fails.

In practice the tactic is used to close a goal in one step. When it fails, the usual remedies are to perform by hand the step the tactic did not find, such as an unfolding, an instantiation or a case split, and to call it again on the resulting goals; or to use `xsimpl` to see what remains after cancellation.

## 2.11 Implementation

The implementation is the single file `Sep/Xsearch.lean` of about ten thousand lines, supported by the lemma library `Sep/SegC.lean`. The file has no internal documentation. Its definitions are grouped by name prefix.

| Prefix | Component |
|---|---|
| `cm` | countermodel check |
| `distr`, `hor` | normalisation of disjunction |
| `wit` | witness ranking and enumeration |
| `inv`, `derive` | synthesised lemmas |
| `ind` | fixed-point induction |
| `wg` | segment engine, and proofs of allocation and disequality |
| `ar` | arithmetic and pure side conditions |
| `searchSolve`, `branchGoal` | backtracking search |

Four mechanisms of Lean's metaprogramming framework account for the behaviour described in this chapter.

**The attribute.** `xsearch_unfold` is declared together with an *environment extension*, a table stored in Lean's environment alongside the declarations. When the attribute is placed on a theorem, a handler checks that the statement is an equation whose left side has a constant at its head, and adds the pair of head and theorem name to the table. The table is saved in compiled files, so predicates registered in an imported module are available. The tactic reads the table at each call.

**Backtracking.** The tactic state, comprising the goal list and the assignment of every metavariable, can be saved as a value and restored later. Each alternative in `branchGoal` is run in the pattern

```lean
let s ← saveState
try
  alt
  searchSolve inv
  return
catch _ =>
  s.restore
```

The argument `inv` records whether lemma synthesis is permitted. Restoring undoes every metavariable assignment made since the save, including the witnesses chosen by unification and the partial proof term. A failed alternative therefore has no effect on the tactic state. The combinator `first` at the top level works in the same way, which is why a failed call leaves the goal unchanged.

**Mutable state outside the tactic state.** Deadlines, the record of failed goals, and the caches of classifications and synthesised lemmas are held in global mutable references. They are not restored by backtracking. This is intended: a goal that failed in one branch should still be known to fail in another. `xsearch_start` resets them at the beginning of each call, so that no information passes from one call to the next.

**Proof terms.** As in `xsimpl`, most steps build their proof terms directly from named lemmas of the library and assign them to the goal after checking that the type of the term matches the goal. Synthesised lemmas are not added to the environment. Each is a closed term kept in a cache and inserted into the final proof wherever it is used, so that the kernel checks it as part of the theorem being proved.
