import Sep.Reordering
import Sep.Xsimpl

open scoped SepLogic

namespace Sep.Reordering.Tests

universe u

variable {α : Type u} [SepLogic α]

def mockPts (l v : Nat) : α := ⌜l = v⌝

def mockInv (_ι : Nat) (P : α) : α := P

notation:max ι " ↦ₜ " P => mockInv ι P

section Basic
variable (A B C D X : α) (F : Nat → α)

/-! ## sl_pull -/

-- Head: already at the head, so `sl_pull` is a no-op.
example (h : A ∗ (B ∗ (C ∗ D)) ==> X) : A ∗ (B ∗ (C ∗ D)) ==> X := by
  sl_pull A
  exact h

-- Middle of a right-nested tree.
example (h : B ∗ (A ∗ (C ∗ D)) ==> X) : A ∗ (B ∗ (C ∗ D)) ==> X := by
  sl_pull B
  exact h

-- Last atom of a right-nested tree.
example (h : D ∗ (A ∗ (B ∗ C)) ==> X) : A ∗ (B ∗ (C ∗ D)) ==> X := by
  sl_pull D
  exact h

-- Left-nested source: the tree is flattened first, so parenthesisation on the
-- source side is irrelevant and the result is always right-nested.
example (h : C ∗ (A ∗ (B ∗ D)) ==> X) : ((A ∗ B) ∗ C) ∗ D ==> X := by
  sl_pull C
  exact h

-- Mixed nesting.
example (h : D ∗ (A ∗ (B ∗ C)) ==> X) : (A ∗ B) ∗ (C ∗ D) ==> X := by
  sl_pull D
  exact h

-- Two interchangeable copies of the same atom are not an ambiguity: both
-- choices give the same reshaped tree, so no `(occs := …)` is needed.
example (h : B ∗ (A ∗ B) ==> X) : A ∗ (B ∗ B) ==> X := by
  sl_pull B
  exact h

/-! ## Patterns -/

-- Head constant with holes.
example (h : mockPts 1 2 ∗ (A ∗ B) ==> X) : A ∗ ((mockPts 1 2 : α) ∗ B) ==> X := by
  sl_pull (mockPts _ _ : α)
  exact h

-- Fully explicit atom.
example (h : mockPts 1 2 ∗ (A ∗ B) ==> X) : A ∗ ((mockPts 1 2 : α) ∗ B) ==> X := by
  sl_pull (mockPts 1 2 : α)
  exact h

-- Pure conjunct, via `⌜_⌝`.
example (h : ⌜(1 : Nat) = 1⌝ ∗ (A ∗ B) ==> X) : A ∗ (⌜(1 : Nat) = 1⌝ ∗ B) ==> X := by
  sl_pull (⌜_⌝ : α)
  exact h

-- Notation-only pattern: `ι ↦ₜ P` elaborates to `mockInv ι P` before matching,
-- so a pattern written in notation matches an atom written either way.
example (h : mockInv 3 B ∗ (A ∗ C) ==> X) : A ∗ ((3 ↦ₜ B) ∗ C) ==> X := by
  sl_pull (3 ↦ₜ (_ : α))
  exact h

/-! ## `(occs := n)` -/

example (h : mockPts 1 1 ∗ (A ∗ mockPts 2 2) ==> X) :
    (mockPts 1 1 : α) ∗ (A ∗ mockPts 2 2) ==> X := by
  sl_pull (mockPts _ _ : α) (occs := 1)
  exact h

example (h : mockPts 2 2 ∗ ((mockPts 1 1 : α) ∗ A) ==> X) :
    (mockPts 1 1 : α) ∗ (A ∗ mockPts 2 2) ==> X := by
  sl_pull (mockPts _ _ : α) (occs := 2)
  exact h

/-! ## `sl_pull` error cases -/

-- No atom matches: the error lists the atoms in scope.
example (h : A ∗ (B ∗ C) ==> X) : A ∗ (B ∗ C) ==> X := by
  fail_if_success sl_pull D
  exact h

-- Genuinely ambiguous (the two matches give different reshapings): the error
-- lists them and asks for `(occs := n)`.
example (h : (mockPts 1 1 : α) ∗ (A ∗ mockPts 2 2) ==> X) :
    (mockPts 1 1 : α) ∗ (A ∗ mockPts 2 2) ==> X := by
  fail_if_success sl_pull (mockPts _ _ : α)
  exact h

-- `occs` out of range.
example (h : A ∗ B ==> X) : A ∗ B ==> X := by
  fail_if_success sl_pull A (occs := 2)
  exact h

-- A pattern matching only a *strict subterm* of an atom does not match: the
-- match unit is the whole atom.  Here `⌜_⌝` does not match `mockPts 1 2`, even
-- though `mockPts` unfolds to a pure conjunct, because matching runs at
-- reducible transparency and the atom is not `∗`-decomposed further.
example (h : A ∗ ((mockPts 1 2 : α) ∗ B) ==> X) : A ∗ ((mockPts 1 2 : α) ∗ B) ==> X := by
  fail_if_success sl_pull (⌜_⌝ : α)
  exact h

-- A `∗`-shaped pattern is rejected outright: use `sl_perm` for whole trees.
example (h : A ∗ (B ∗ C) ==> X) : A ∗ (B ∗ C) ==> X := by
  fail_if_success sl_pull (A ∗ B)
  exact h

/-! ## `sl_perm`: full-tree reshaping -/

-- Fully named target; parenthesisation is significant.
example (h : (D ∗ C) ∗ (B ∗ A) ==> X) : A ∗ (B ∗ (C ∗ D)) ==> X := by
  sl_perm (D ∗ C) ∗ (B ∗ A)
  exact h

-- With `_` holes: the named atoms (`D`, `B`) are placed first, then the
-- leftovers fill the holes in left-to-right source order (`A`, then `C`).
example (h : D ∗ (A ∗ (C ∗ B)) ==> X) : A ∗ (B ∗ (C ∗ D)) ==> X := by
  sl_perm D ∗ (_ ∗ (_ ∗ B))
  exact h

-- `emp` may be *added* by the target.
example (h : B ∗ (emp ∗ A) ==> X) : A ∗ B ==> X := by
  sl_perm B ∗ (emp ∗ A)
  exact h

-- ... and *removed*: an `emp` in the source need not appear in the target.
example (h : B ∗ A ==> X) : A ∗ (emp ∗ B) ==> X := by
  sl_perm B ∗ A
  exact h

-- A permutation that is already in place is a no-op.
example (h : A ∗ (B ∗ C) ==> X) : A ∗ (B ∗ C) ==> X := by
  sl_perm A ∗ (B ∗ C)
  exact h

-- Regression: dropping the source's `emp` leaves a *single* atom, and the
-- reshaping equality `A ∗ emp = A` is then closed by the `emp` cleanup alone.
-- The AC step that follows must tolerate an already-closed goal.
example (h : A ==> X) : A ∗ emp ==> X := by
  sl_perm A
  exact h

/-! ## `sl_perm` error cases -/

-- Multiset mismatch: too few atoms in the target.  The error prints both lists.
example (h : A ∗ (B ∗ C) ==> X) : A ∗ (B ∗ C) ==> X := by
  fail_if_success sl_perm A ∗ B
  exact h

-- Multiset mismatch: too many.
example (h : A ∗ B ==> X) : A ∗ B ==> X := by
  fail_if_success sl_perm A ∗ (B ∗ C)
  exact h

-- A named target atom that does not occur in the source at all.
example (h : A ∗ B ==> X) : A ∗ B ==> X := by
  fail_if_success sl_perm D ∗ A
  exact h

/-! ## `at h` -/

example (h : A ∗ (B ∗ C) ==> X) : C ∗ (A ∗ B) ==> X := by
  sl_pull C at h
  guard_hyp h : C ∗ (A ∗ B) ==> X
  exact h

example (h : A ∗ (B ∗ C) ==> X) : (C ∗ B) ∗ A ==> X := by
  sl_perm (C ∗ B) ∗ A at h
  guard_hyp h : (C ∗ B) ∗ A ==> X
  exact h

/-! ## Under a binder

The reshaping equality is stated `∀`-quantified over the binders the tree lives
under, so a tree mentioning a *bound* variable — a postcondition `fun v => …` —
is rewritten just like a top-level one.  Here the tree sits under `∃ₛ v` and
mentions `v` through `F v`. -/

example (h : (∃ₛ v : Nat, F v ∗ (A ∗ B)) ==> X) : (∃ₛ v : Nat, A ∗ (F v ∗ B)) ==> X := by
  sl_pull (F _ : α)
  exact h

-- Regression: a tree under a binder it does *not* mention.  The reshaping
-- equality must not be quantified over that binder — a `∀ v` whose `v` does not
-- occur in the pattern leaves `simp` with an uninstantiable metavariable and the
-- rewrite silently never fires.  This is the shape of every postcondition whose
-- resources do not depend on the returned value.
example (h : (∃ₛ _v : Nat, C ∗ (A ∗ B)) ==> X) : (∃ₛ _v : Nat, A ∗ (C ∗ B)) ==> X := by
  sl_pull C
  exact h

example (h : (∃ₛ v : Nat, (F v ∗ B) ∗ A) ==> X) : (∃ₛ v : Nat, A ∗ (F v ∗ B)) ==> X := by
  sl_perm (F _ ∗ B) ∗ A
  exact h

/-! ## Patterns mentioning tactic-introduced variables

Regression: the pattern is elaborated in the *main goal's* local context, not the
declaration's, so it may mention variables the proof script itself introduced.
Here `v` exists only after `intro`. -/

example (h : ∀ v : Nat, F v ∗ (A ∗ B) ==> X) : ∀ v : Nat, A ∗ (F v ∗ B) ==> X := by
  intro v
  sl_pull (F v)
  exact h v

example (h : ∀ v : Nat, (F v ∗ B) ∗ A ==> X) : ∀ v : Nat, A ∗ (F v ∗ B) ==> X := by
  intro v
  sl_perm (F v ∗ B) ∗ A
  exact h v

/-! ## End-to-end: the ParIncr fork-setup reshuffle

The pre is `A ∗ (B ∗ B)` and the next proof step wants `B ∗ (A ∗ B)`.  This is
exactly the `apply hoare_pre _ (show _ ⊢ _ from entails_of_eq (by sep_ac))`
idiom the tactics replace: one `sl_pull` puts the entailment into the shape the
next rule expects — no `show`, no `sepConj_mono` tower, no directional step. -/

example (hnext : B ∗ (A ∗ B) ==> X) : A ∗ (B ∗ B) ==> X := by
  sl_pull B
  exact hnext

-- The same, naming the target shape outright.
example (hnext : B ∗ (A ∗ B) ==> X) : A ∗ (B ∗ B) ==> X := by
  sl_perm B ∗ (A ∗ B)
  exact hnext

end Basic

end Sep.Reordering.Tests

/-! ## At a concrete instance

The same tactics over `Sep.Xsimpl`'s `SepLogic HProp`, with the reshaped goal
handed straight to `xsimpl`: nothing beyond the instance is needed. -/

namespace Sep.Xsimpl

variable [Params] (A B X : HProp)

example (h : SepLogic.Entails (B ∗ (A ∗ B)) X) :
    SepLogic.Entails (A ∗ (B ∗ B)) X := by
  sl_pull B
  exact h

example : SepLogic.Entails (A ∗ (B ∗ B)) (B ∗ (A ∗ B)) := by
  sl_pull B (occs := 1)
  xsimpl

end Sep.Xsimpl
