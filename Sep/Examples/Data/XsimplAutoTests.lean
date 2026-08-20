import Sep.Examples.Data.XsimplAuto
open Lean Meta Elab Tactic
open HProp Notation Sep.XsimplAuto

instance : Params where val := Nat

-- ============================================================
-- Predicate 1: llist  (singly-linked list)
-- ============================================================

def llist : Loc → List Nat → HProp
  | _, []      => hempty
  | p, v :: vs => hexists fun q : Loc =>
      (p ↦ v) ✶ ((p + 1) ↦ q) ✶ llist q vs

@[xsimpl_unfold] theorem llist_nil (p : Loc) :
    llist p [] = emp := rfl

@[xsimpl_unfold] theorem llist_cons (p : Loc) (v : Nat) (vs : List Nat) :
    llist p (v :: vs) = ∃✶ q : Loc, (p ↦ v) ✶ ((p + 1) ↦ q) ✶ llist q vs := rfl

-- ============================================================
-- Predicate 2: pair  (two values stored at consecutive locations)
-- ============================================================

def pair (p : Loc) (a b : Nat) : HProp :=
  (p ↦ a) ✶ ((p + 1) ↦ b)

@[xsimpl_unfold] theorem pair_unfold (p : Loc) (a b : Nat) :
    pair p a b = (p ↦ a) ✶ ((p + 1) ↦ b) := rfl

-- ============================================================
-- Tests: xsimpl_auto (attribute-registered predicates)
-- ============================================================

-- llist nil: unfolded to emp and cancelled
example (p : Loc) : llist p [] ==> emp := by xsimpl_auto

-- llist single cons: unfold exposes the ∃ and heap atoms
example (p : Loc) (v : Nat) (vs : List Nat) :
    llist p (v :: vs) ==>
      ∃✶ q : Loc, (p ↦ v) ✶ ((p + 1) ↦ q) ✶ llist q vs := by
  xsimpl_auto

-- llist frame: xsimpl_auto unfolds both sides and cancels matching atoms
example (p : Loc) (v : Nat) (H : HProp) :
    H ✶ llist p [v] ==> llist p [v] ✶ H := by
  xsimpl_auto

-- pair: unfolded and cancelled
example (p : Loc) (a b : Nat) :
    pair p a b ==> (p ↦ a) ✶ ((p + 1) ↦ b) := by
  xsimpl_auto

-- pair frame: xsimpl_auto unfolds pair on both sides
example (p : Loc) (a b : Nat) (H : HProp) :
    H ✶ pair p a b ==> pair p a b ✶ H := by
  xsimpl_auto

-- Both predicates in the same goal: xsimpl_auto unfolds each on demand
example (p q : Loc) (v a b : Nat) (H : HProp) :
    H ✶ llist p [v] ✶ pair q a b ==> pair q a b ✶ llist p [v] ✶ H := by
  xsimpl_auto

-- ============================================================
-- Tests: xsimpl_with (inline lemmas, no attribute needed)
-- ============================================================

-- Same goals as above but using xsimpl_with instead of xsimpl_auto
example (p : Loc) (v : Nat) (H : HProp) :
    H ✶ llist p [v] ==> llist p [v] ✶ H := by
  xsimpl_with [llist_nil, llist_cons]

example (p : Loc) (a b : Nat) (H : HProp) :
    H ✶ pair p a b ==> pair p a b ✶ H := by
  xsimpl_with [pair_unfold]

-- Mixed: inline lemmas cover both predicates
example (p q : Loc) (v a b : Nat) (H : HProp) :
    H ✶ llist p [v] ✶ pair q a b ==> pair q a b ✶ llist p [v] ✶ H := by
  xsimpl_with [llist_nil, llist_cons, pair_unfold]
