import Sep.HProp
import Sep.Xsimpl
import Sep.Examples.SymEx.SymExec
open HProp Notation
open Sep.SymExec
open Cmd

instance NatParams : Params where
  val := Nat

instance {n : Nat} : OfNat val n where
  ofNat := n

example : emp ==> wp (alloc 42) (fun p => p ↦ 42) := by
  sym_exec

example {p : Loc} : (p ↦ 42) ==> wp (read p) (fun v => (p ↦ v) ✶ ⌈v = 42⌉) := by
  sym_exec

example {p : Loc} : (p ↦ 42) ==> wp (write p 0) (fun _ => p ↦ 0) := by
  sym_exec

example {p : Loc} : (p ↦ 42) ==> wp (free p) (fun _ => emp) := by
  sym_exec

example : emp ==> wp (do
  let p ← alloc 42
  write p 0
  let v ← read p
  free p
  pure v
) (fun v => ⌈v = 0⌉) := by
  sym_exec

-- A test that requires biabduction:
-- The program reads from `p`, writes to `q`, and then frees `r`.
-- The initial state only has `p ↦ 42`, `s ↦ 99`.
-- We must abduce `q ↦ ?v` and `r ↦ ?v2` (AntiFrame) and frame out `s ↦ 99` and the final `p ↦ 42` and `q ↦ 10` (Frame).
example {p q r s : Loc} : ∃ AntiFrame Frame,
    (p ↦ 42) ✶ (s ↦ 99) ✶ AntiFrame ==>
    wp (do
      let v ← read p
      write q 10
      free r
      pure v
    ) (fun v => ⌈v = 42⌉ ✶ Frame) := by
  apply Exists.intro
  apply Exists.intro
  sym_exec_abduce

-- To validate that extracting existentials and evaluating wands allows perfect execution,
-- we manually provide the AntiFrame (the missing memory for q and r)
example {p q r s : Loc} : ∃ Frame,
    (p ↦ 42) ✶ (s ↦ 99) ✶ (q ↦ 55) ✶ (r ↦ 77) ==>
    wp (do
      let v ← read p
      write q 10
      free r
      pure v
    ) (fun v => ⌈v = 42⌉ ✶ Frame) := by
  apply Exists.intro
  sym_exec_abduce

-- ============================================================
-- Step-by-Step Symbolic Execution API
-- ============================================================
-- To provide a highly granular API for stepping through programs (useful for debugging
-- where an automated `sym_exec` fails), we can manually step through the weakest
-- precondition evaluation using the individual MetaM tactics!
example : emp ==> wp (do
  let p ← alloc 42
  write p 0
  let v ← read p
  free p
  pure v
) (fun v => ⌈v = 0⌉) := by
  dsimp only [wp]

  -- 1. Execute `alloc 42`
  -- extracts the `∀✶ p` and evaluates the `-✶` to move `p ↦ 42` to LHS
  xsimpl_symexec_step
  xsimpl_symexec_step

  -- 2. Execute `write p 0`
  -- strips `∃✶ v0`, cancels `p ↦ 42` against `p ↦ ?v0`, evaluates `-✶`
  xsimpl_instantiate_step
  xsimpl_cancel_all
  xsimpl_symexec_step

  -- 3. Execute `read p`
  -- strips `∃✶ v`, cancels `p ↦ 0` against `p ↦ ?v`, evaluates `-✶`
  xsimpl_instantiate_step
  xsimpl_cancel_all
  xsimpl_symexec_step

  -- 4. Execute `free p`
  -- strips `∃✶ v0`, cancels `p ↦ 0` against `p ↦ ?v0`
  xsimpl_instantiate_step
  xsimpl_cancel_all

  -- 5. Close the pure postcondition and remaining `emp ==> emp`
  xsimpl_instantiate_step
  all_goals (
    try xsimpl_clean
    try rfl
  )
