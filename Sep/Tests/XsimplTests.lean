import Sep.HProp
import Sep.Xsimpl
import Sep.FrameInference
open HProp Notation

instance UnitParams : Params where
  val := Unit

-- ============================================================
-- 1. Normalization Tests
-- ============================================================

example {H} : H ✶ emp ==> H := by
  xsimpl

example {H} : emp ✶ H ==> H := by
  xsimpl

example {H1 H2} : H1 ✶ emp ✶ H2 ==> H1 ✶ H2 := by
  xsimpl

example {H} : H ==> H ✶ emp := by
  xsimpl

example {H} : H ==> emp ✶ H := by
  xsimpl

example {P H1 H2} : H1 ✶ ⌈P⌉ ✶ H2 ==> ⌈P⌉ ✶ H1 ✶ H2 := by
  xsimpl

example {A} {J : A → HProp} {H1 H2} : H1 ✶ (∃✶ x, J x) ✶ H2 ==> ∃✶ x, H1 ✶ J x ✶ H2 := by
  xsimpl

-- ============================================================
-- 2. Extraction Tests
-- ============================================================

example {P H} : ⌈P⌉ ✶ H ==> H := by
  xsimpl

example {P H} : H ✶ ⌈P⌉ ==> H := by
  xsimpl

example {P} (_p : P) : ⌈P⌉ ==> ⌈P⌉ := by
  xsimpl

example {P} (_p : P) : ⌈P⌉ ✶ ⌈P⌉ ==> ⌈P⌉ := by
  xsimpl

example {A} {J : A → HProp} : (∃✶ x, J x) ==> ∃✶ x, J x := by
  xsimpl

example {A} {J : A → HProp} {H} : (∃✶ x, J x) ✶ H ==> ∃✶ x, J x ✶ H := by
  xsimpl

-- ============================================================
-- 3. Instantiation Tests
-- ============================================================

example {A a H} {J : A → HProp} : J a ✶ H ==> ∃✶ x, J x ✶ H := by
  xsimpl

example {A a} {J : A → HProp} : J a ==> ∃✶ x, J x := by
  xsimpl

example {P H} (p : P) : H ==> ⌈P⌉ ✶ H := by
  xsimpl

-- ============================================================
-- 4. Cancellation Tests
-- ============================================================

example {H1 H2} : H1 ✶ H2 ==> H2 ✶ H1 := by
  xsimpl

example {H1 H2 H3} : H1 ✶ H2 ✶ H3 ==> H2 ✶ H3 ✶ H1 := by
  xsimpl

example {H1 H2 H3 H4 H5} :
    (H5 ✶ H4 ✶ H3 ✶ H2 ✶ H1) ==> (H1 ✶ H2 ✶ H3 ✶ H4 ✶ H5) := by
  xsimpl

example {H} : H ✶ H ✶ H ==> H ✶ H ✶ H := by
  xsimpl

example {H1 H2 H3 H4} : ((H1 ✶ H2) ✶ H3) ✶ H4 ==> H1 ✶ (H2 ✶ (H3 ✶ H4)) := by
  xsimpl

example {H1 H2} : H1 ✶ H1 ✶ H2 ✶ H2 ==> H2 ✶ H1 ✶ H2 ✶ H1 := by
  xsimpl

-- ============================================================
-- 5. Wand Cleanup Tests
-- ============================================================

example {H1 H2} : H1 ✶ (H1 -✶ H2) ==> H2 := by
  xsimpl

example {H1 H2 H3} : H1 ✶ (H1 -✶ H2) ✶ H3 ==> H2 ✶ H3 := by
  xsimpl

example {H1 H2 H3} : (H1 ✶ H2) ✶ ((H1 ✶ H2) -✶ H3) ==> H3 := by
  xsimpl

-- ============================================================
-- 6. Partial Cancellation Tests
-- ============================================================

-- Canceling H1 and H3 should leave exactly `H2 ==> emp`.
example {H1 H2 H3} (h : H2 ==> emp) : H1 ✶ H2 ✶ H3 ==> H3 ✶ H1 := by
  xsimpl

-- Canceling H2 should leave `H1 ✶ H3 ==> H4`.
example {H1 H2 H3 H4} (h : H1 ✶ H3 ==> H4) : H1 ✶ H2 ✶ H3 ==> H2 ✶ H4 := by
  xsimpl

-- ============================================================
-- 7. Deeply Nested / Left-Associative Tests
-- ============================================================

-- Left associative on LHS, checking if H1 and H3 can be extracted.
example {H1 H2 H3 H4} (h : H2 ✶ H4 ==> emp) : ((H1 ✶ H2) ✶ H3) ✶ H4 ==> H1 ✶ H3 := by
  xsimpl

-- Nested on RHS.
example {H1 H2 H3} (h : emp ==> H3) : H1 ✶ H2 ==> H2 ✶ (H3 ✶ H1) := by
  xsimpl

-- ============================================================
-- 8. Chained Wand Tests
-- ============================================================

-- The tactic should be able to apply wand cancellation recursively.
example {H1 H2 H3} : H1 ✶ (H1 -✶ H2) ✶ (H2 -✶ H3) ==> H3 := by
  xsimpl

-- ============================================================
-- 9. Nested Extraction and Pure Edge Cases
-- ============================================================

-- Pure fact hidden underneath an existential quantifier.
example {A} {J : A → HProp} {P : Prop} : (∃✶ x, ⌈P⌉ ✶ J x) ==> ⌈P⌉ ✶ ∃✶ x, J x := by
  xsimpl

-- Extracting a pure fact leaving only implicit emp.
example {P : Prop} : ⌈P⌉ ==> emp := by
  xsimpl

-- Instantiating a pure fact from an implicit emp.
example {P : Prop} (p : P) : emp ==> ⌈P⌉ := by
  xsimpl

-- ============================================================
-- 10. Wand Edge Cases
-- ============================================================

-- Residual Goals (Non-Exact RHS):
-- Expected residual: `H2 ==> H3`
example {H1 H2 H3} (h : H2 ==> H3) : H1 ✶ (H1 -✶ H2) ==> H3 := by
  xsimpl

-- Out-of-Order Consequent:
-- Expected: Closes goal
example {H1 H2 H3} : H1 ✶ (H1 -✶ (H2 ✶ H3)) ==> H3 ✶ H2 := by
  xsimpl

-- Wand with Framing:
-- Expected residual: `H2 ✶ H3 ==> H4`
example {H1 H2 H3 H4} (h : H2 ✶ H3 ==> H4) : H1 ✶ H3 ✶ (H1 -✶ H2) ==> H4 := by
  xsimpl

-- Wand introduction (the adjunction), fired as a safe step.
example {H1 H2} : H1 ==> H2 -✶ (H2 ✶ H1) := by
  xsimpl

example {H1} : (emp : HProp) ==> H1 -✶ H1 := by
  xsimpl

-- A wand left over after cancellation is still introduced.
example {H1 H2 H3} : H1 ✶ H2 ==> H1 ✶ (H3 -✶ (H3 ✶ H2)) := by
  xsimpl

-- Curried wand: two introductions in sequence.
example {H1 H2 H3} : H1 ==> H2 -✶ (H3 -✶ (H3 ✶ H2 ✶ H1)) := by
  xsimpl

-- Wand over a compound premise (normalized by hwand_curry, then introduced).
example {H1 H2 H3} : H1 ==> (H2 ✶ H3) -✶ (H3 ✶ H1 ✶ H2) := by
  xsimpl

-- Introduction exposes a pure conjunct to extract.
example {H1 H2 : HProp} {P : Prop} (h : P → (H1 ==> H2)) :
    H1 ==> (⌈P⌉ -✶ H2) := by
  xsimpl; exact h ‹P›

-- Introduction exposes an existential to instantiate.
example {H1 : HProp} {J : Nat → HProp} :
    (J 0) ==> H1 -✶ ∃✶ x, H1 ✶ J x := by
  xsimpl

-- Introduction, then cancellation against the moved premise, with residual.
example {H1 H2 H3} (h : H2 ==> H3) : H2 ==> H1 -✶ (H1 ✶ H3) := by
  xsimpl

-- Intro on the right combines with wand elimination on the left.
example {H1 H2 H3} : (H1 -✶ H2) ==> H1 -✶ (H3 -✶ (H2 ✶ H3)) := by
  xsimpl

-- ============================================================
-- 11. `HProp` is linear: no affine drops
-- ============================================================

-- A leftover on the left is not dropped; the residual `H2 ==> emp` survives.
/--
error: unsolved goals
case a
H1 H2 : HProp
⊢ H2 ==> emp
-/
#guard_msgs in
example {H1 H2} : H1 ✶ H2 ==> H1 := by
  xsimpl

-- With no frame metavariable, the frame step still errors.
/-- error: xsimpl_frame_step: no frame metavariable on the RHS -/
#guard_msgs in
example {H1 H2} : H1 ✶ H2 ==> H1 := by
  xsimpl_frame_step
