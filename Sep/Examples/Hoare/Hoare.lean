import Sep.HProp
import Sep.Xsimpl
import Sep.Examples.SymEx.SymExec
import Sep.Examples.Biab.FrameInference

open Lean Meta Elab Tactic
open HProp Notation
open Sep.SymExec
open Sep.Xsimpl

namespace Sep.Hoare

variable [Params]

def hoare {A : Type} (P : HProp) (c : Cmd A) (Q : A → HProp) : Prop :=
  P ==> wp c Q

/--
  We define 4 separate syntax rules to handle the Cartesian product of two AST variations
  required by Lean's strict Pretty Printer (Unexpander):

  1. Binder Type (`ident` vs `hole`): The user might name the return variable (`v.`) or discard it (`_.`).
     Lean parses these as fundamentally different AST nodes (`ident` vs `hole`).
     *Why not `binderIdent`?* While built-in tactics like `intro` support both via `binderIdent`, custom
     macros cannot pattern match on a generic `binderIdent` followed by a literal `.` without complex
     custom C++ parsing logic. Attempting to parse `_.` natively as a binder fails as an `invalid atom`.

  2. Body Type (`term` vs `doSeq`): A multi-line block `{ let x ← ... }` parses as a `doSeq`.
     However, when symbolic execution reduces the program to a single final command (e.g. `pure v`),
     Lean optimizes the AST into a standard `term`.
     *Why not programmatically unexpand a `term` into a `doSeq`?* Lean's pretty printer (`unexpander`) is
     extremely strict about AST types. If we try to dynamically wrap a `term` into a `doSeq` block in the
     unexpander to satisfy a single `doSeq` syntax rule, Lean crashes with a type error:
     `Application type mismatch: expected Lean.TSyntax doSeq, got term`.

  Providing all 4 rules guarantees the unexpander can always perfectly format the goal state without crashing.
-/
syntax (name := hoareTerm) (priority := low) "requires " term:max ppLine "ensures " ident ". " term:max " {" ppIndent(ppLine term) ppLine "}" : term
syntax (name := hoareDo) (priority := high) "requires " term:max ppLine "ensures " ident ". " term:max " {" ppIndent(doSeq) ppLine "}" : term
syntax (name := hoareTermHole) (priority := low) "requires " term:max ppLine "ensures " hole ". " term:max " {" ppIndent(term) ppLine "}" : term
syntax (name := hoareDoHole) (priority := high) "requires " term:max ppLine "ensures " hole ". " term:max " {" ppIndent(doSeq) ppLine "}" : term

@[macro hoareTerm] def macroHoareTerm : Lean.Macro
  | `(hoareTerm| requires $P ensures $x:ident . $Q { $c }) => `(hoare $P $c (fun $x => $Q))
  | _ => Lean.Macro.throwUnsupported

@[macro hoareDo] def macroHoareDo : Lean.Macro
  | `(hoareDo| requires $P ensures $x:ident . $Q { $c }) => `(hoare $P (do $c) (fun $x => $Q))
  | _ => Lean.Macro.throwUnsupported

@[macro hoareTermHole] def macroHoareTermHole : Lean.Macro
  | `(hoareTermHole| requires $P ensures $_:hole . $Q { $c }) => `(hoare $P $c (fun _ => $Q))
  | _ => Lean.Macro.throwUnsupported

@[macro hoareDoHole] def macroHoareDoHole : Lean.Macro
  | `(hoareDoHole| requires $P ensures $_:hole . $Q { $c }) => `(hoare $P (do $c) (fun _ => $Q))
  | _ => Lean.Macro.throwUnsupported

@[app_unexpander hoare]
def unexpandHoare : Lean.PrettyPrinter.Unexpander
  | `($(_) $P do $c:doSeq fun $x:ident => $Q) => `(hoareDo| requires $P ensures $x . $Q { $c })
  | `($(_) $P $c fun $x:ident => $Q) => `(hoareTerm| requires $P ensures $x . $Q { $c })
  | `($(_) $P do $c:doSeq fun _ => $Q) => `(hoareDoHole| requires $P ensures _ . $Q { $c })
  | `($(_) $P $c fun _ => $Q) => `(hoareTermHole| requires $P ensures _ . $Q { $c })
  | _ => throw ()

-- Structural Hoare Rules for Symbolic Execution
theorem hoare_bind_alloc {A : Type} (v : val) (k : Loc → Cmd A) (P : HProp) (Q : A → HProp) :
  (∀ p, hoare (P ✶ (p ↦ v)) (k p) Q) →
  hoare P (Cmd.bind (Cmd.alloc v) k) Q := by
  intro H
  dsimp [hoare, wp] at *
  apply HProp.himpl_hforall_r
  intro p
  apply HProp.himpl_hwand_r
  rw [HProp.hstar_comm]
  apply H p

theorem hoare_bind_read {A : Type} (p : Loc) (v : val) (k : val → Cmd A) (P P_Rest : HProp) (Q : A → HProp) :
  (P ==> (p ↦ v) ✶ P_Rest) →
  hoare ((p ↦ v) ✶ P_Rest) (k v) Q →
  hoare P (Cmd.bind (Cmd.read p) k) Q := by
  intro H1 H2
  dsimp [hoare, wp] at *
  apply HProp.himpl_trans
  · exact H1
  · apply HProp.himpl_hexists_r v
    apply HProp.himpl_frame_r
    apply HProp.himpl_hwand_r
    exact H2

theorem hoare_bind_write {A : Type} (p : Loc) (v : val) (k : Unit → Cmd A) (P P_Rest : HProp) (Q : A → HProp) :
  (P ==> ∃✶ v0, (p ↦ v0) ✶ P_Rest) →
  hoare ((p ↦ v) ✶ P_Rest) (k ()) Q →
  hoare P (Cmd.bind (Cmd.write p v) k) Q := by
  intro H1 H2
  dsimp [hoare, wp] at *
  apply HProp.himpl_trans
  · exact H1
  · apply HProp.himpl_hexists_l
    intro v0
    apply HProp.himpl_hexists_r v0
    apply HProp.himpl_frame_r
    apply HProp.himpl_hwand_r
    exact H2

theorem hoare_bind_free {A : Type} (p : Loc) (k : Unit → Cmd A) (P P_Rest : HProp) (Q : A → HProp) :
  (P ==> ∃✶ v0, (p ↦ v0) ✶ P_Rest) →
  hoare P_Rest (k ()) Q →
  hoare P (Cmd.bind (Cmd.free p) k) Q := by
  intro H1 H2
  dsimp [hoare, wp] at *
  apply HProp.himpl_trans
  · exact H1
  · apply HProp.himpl_hexists_l
    intro v0
    apply HProp.himpl_hexists_r v0
    apply HProp.himpl_frame_r
    exact H2

theorem hoare_bind_ret {A B : Type} (a : B) (k : B → Cmd A) (P : HProp) (Q : A → HProp) :
  hoare P (k a) Q →
  hoare P (Cmd.bind (Cmd.ret a) k) Q := by
  intro H
  dsimp [hoare, wp] at *
  apply H

theorem hoare_ret {A : Type} (a : A) (P : HProp) (Q : A → HProp) :
  (P ==> Q a) →
  hoare P (Cmd.ret a) Q := by
  intro H
  dsimp [hoare, wp] at *
  apply H

elab "hoare_step" : tactic => withMainContext do
  evalTactic (← `(tactic| (
    first
    | apply hoare_bind_alloc
    | apply hoare_bind_read
    | apply hoare_bind_write
    | apply hoare_bind_free
    | apply hoare_bind_ret
  )))

  -- After read/write/free, the first subgoal is the frame solver:
  --   `P ==> ∃✶ v, (p ↦ v) ✶ ?P_Rest`
  -- Solve it automatically with biabduction so the user never sees a raw entailment.
  evalTactic (← `(tactic| try xsimpl_granular_frames))

  -- `xsimpl` works with the `SepLogic` class operations; a frame it infers is
  -- therefore stated in class form, and that form escapes through the frame
  -- metavariable into the sibling goals we own. Restore `HProp`'s own constants
  -- everywhere before continuing, so the Hoare rules keep matching.
  evalTactic (← `(tactic| all_goals (try xsimpl_unfold_goal)))

  -- For commands that bind variables (alloc, read), the continuation is `∀ x, HT[...] ...`.
  -- Introduce the bound variable so the user sees a Hoare triple.
  evalTactic (← `(tactic| try with_reducible intro))

  -- Clean up residual `emp`s.
  evalTactic (← `(tactic| try simp only [HProp.hstar_hempty_l, HProp.hstar_hempty_r, HProp.hstar_assoc]))

/--
  Close a terminal Hoare triple `hoare P (Cmd.ret a) Q` (i.e. `requires P ensures x. Q { pure a }`)
  by proving the entailment `P ==> Q a` via `xsimpl`.
  Combine with biabduction (`xsimpl_granular_frames`) to also infer any residual Frame.
-/
elab "hoare_close" : tactic => withMainContext do
  evalTactic (← `(tactic| (
    first
    | apply hoare_ret
    | (apply hoare_bind_ret; apply hoare_ret)
  )))
  evalTactic (← `(tactic| (
    first
    | xsimpl_granular_frames
    | xsimpl
    | assumption
  )))
  -- As in `hoare_step`: undo any class-form leakage through inferred frames.
  evalTactic (← `(tactic| all_goals (try xsimpl_unfold_goal)))

end Sep.Hoare
