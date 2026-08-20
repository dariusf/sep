import Sep.HProp
import Sep.Xsimpl
import Sep.Examples.SymEx.SymExec
import Sep.Examples.Biab.FrameInference
import Sep.Examples.Hoare.Hoare

open Lean Meta Elab Tactic
open HProp Notation
open Sep.SymExec
open Sep.Xsimpl
open Sep.Hoare
open Cmd

instance NatParams : Params where
  val := Nat

instance {n : Nat} : OfNat val n where
  ofNat := n

-- Basic end-to-end: each hoare_step should leave a Hoare triple (never a raw entailment).
-- hoare_close handles the terminal `pure v` case.
/--
trace: case a
p✝ : Loc
⊢ requires (p✝ ↦ 42)
    ensures x. emp {
      write✝ p✝ 0
      let v ← read✝ p✝
      free✝ p✝
      pure v
    }
---
trace: case a.a
p✝ : Loc
⊢ requires (p✝ ↦ 0)
    ensures x. emp {
      let v ← read✝ p✝
      free✝ p✝
      pure v
    }
---
trace: case a.a.a
p✝ : Loc
⊢ requires (p✝ ↦ 0)
    ensures x. emp {
      free✝ p✝
      pure 0
    }
---
trace: case a.a.a.a
p✝ : Loc
⊢ requires emp
    ensures x. emp {
      pure 0
    }
-/
#guard_msgs in
example :
    requires emp
    ensures _. emp {
      let p ← alloc 42
      write p 0
      let v ← read p
      free p
      pure v
    } := by
  hoare_step -- requires p ↦ 42 ensures _. emp { write p 0; ... }
  trace_state
  hoare_step -- requires p ↦ 0  ensures _. emp { let v ← read p; ... }
  trace_state
  hoare_step -- requires p ↦ v  ensures _. emp { free p; pure v }
  trace_state
  hoare_step -- requires emp    ensures _. emp { pure v }
  trace_state
  hoare_close

-- With extra resources in precondition (framing):
-- only `p ↦ 42` is touched; `q ↦ 99` should be preserved in Frame.
example {p q : Loc} :
    requires ((p ↦ 42) ✶ (q ↦ 99))
    ensures v. ((p ↦ v) ✶ (q ↦ 99)) {
      let v ← read p
      pure v
    } := by
  hoare_step
  hoare_close

-- Biabduction: existential Frame.
-- The user leaves an HProp metavariable `Frame` in the postcondition;
-- biabduction discovers it (here `Frame := q ↦ 99`).
/--
trace: case h.a
p q : Loc
⊢ requires (p ↦ 42 ✶ q ↦ 99)
    ensures v. (p ↦ v ✶ ?w) {
      pure 42
    }

case w
p q : Loc
⊢ HProp
-/
#guard_msgs in
example {p q : Loc} : ∃ Frame,
    requires ((p ↦ 42) ✶ (q ↦ 99))
    ensures v. ((p ↦ v) ✶ Frame) {
      let v ← read p
      pure v
    } := by
  apply Exists.intro
  hoare_step
  trace_state
  hoare_close

-- Biabduction: existential AntiFrame.
-- The user leaves `AntiFrame` open in the precondition; biabduction abduces
-- the missing resources needed by `free p; free q` (here `AntiFrame := q ↦ ?v`).
-- The AntiFrame stays threaded across multiple `hoare_step`s.
/--
trace: case h.a
p q : Loc
⊢ requires ?h.P_Rest
    ensures x. emp {
      free✝ q
      pure ()
    }

case h.P_Rest
p q : Loc
⊢ HProp
---
trace: case h.a.a
p q : Loc
⊢ requires ?h.a.P_Rest
    ensures x. emp {
      pure ()
    }

case h.a.P_Rest
p q : Loc
⊢ HProp
-/
#guard_msgs in
example {p q : Loc} : ∃ AntiFrame,
    requires ((p ↦ 42) ✶ AntiFrame)
    ensures _. emp {
      free p
      free q
      pure ()
    } := by
  apply Exists.intro
  hoare_step
  trace_state
  hoare_step
  trace_state
  hoare_close

-- Biabduction: both AntiFrame (pre) and Frame (post).
-- `free q` requires abducing `q ↦ ?v` into AntiFrame; `r ↦ 99` is framed into Frame.
/--
trace: case h.h.a
p q r : Loc
⊢ requires (p ↦ 42 ✶ r ↦ 99 ✶ ?w)
    ensures v. (p ↦ v ✶ ?h.w) {
      free✝ q
      pure 42
    }

case h.w
p q r : Loc
⊢ HProp

case w
p q r : Loc
⊢ HProp
---
trace: case h.h.a.a
p q r : Loc
⊢ requires (p ↦ 42 ✶ r ↦ 99)
    ensures v. (p ↦ v ✶ ?h.w) {
      pure 42
    }

case h.w
p q r : Loc
⊢ HProp
-/
#guard_msgs in
example {p q r : Loc} : ∃ AntiFrame Frame,
    requires ((p ↦ 42) ✶ (r ↦ 99) ✶ AntiFrame)
    ensures v. ((p ↦ v) ✶ Frame) {
      let v ← read p
      free q
      pure v
    } := by
  apply Exists.intro
  apply Exists.intro
  hoare_step
  trace_state
  hoare_step
  trace_state
  hoare_close
