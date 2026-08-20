import Sep.HProp
import Sep.Xsimpl
import Sep.Examples.Biab.FrameInference

open Lean Meta Elab Tactic
open HProp Notation

namespace Sep.SymExec

variable [Params]

-- Add rules for extracting ∀✶ from RHS and -✶ from RHS
syntax "xsimpl_symexec_step" : tactic
macro_rules
  | `(tactic| xsimpl_symexec_step) => `(tactic| (
      first
      | (apply HProp.himpl_hforall_r; intro)
      | apply HProp.himpl_hwand_r
    ))

inductive Cmd : Type → Type 1 where
  | ret : {A : Type} → A → Cmd A
  | bind : {A B : Type} → Cmd B → (B → Cmd A) → Cmd A
  | alloc : val → Cmd Loc
  | read : Loc → Cmd val
  | write : Loc → val → Cmd Unit
  | free : Loc → Cmd Unit

instance : Bind Cmd where
  bind := Cmd.bind

instance : Pure Cmd where
  pure := Cmd.ret

-- ============================================================
-- Pretty-printing: convert Cmd back to do-notation
-- ============================================================

-- Each primitive renders as its short name (valid when `open Cmd` or equivalent is in scope).
@[app_unexpander Sep.SymExec.Cmd.alloc]
def unexpandCmdAlloc : Lean.PrettyPrinter.Unexpander
  | `($(_) $v) => `(alloc $v)
  | _ => throw ()

@[app_unexpander Sep.SymExec.Cmd.read]
def unexpandCmdRead : Lean.PrettyPrinter.Unexpander
  | `($(_) $p) => `(read $p)
  | _ => throw ()

@[app_unexpander Sep.SymExec.Cmd.write]
def unexpandCmdWrite : Lean.PrettyPrinter.Unexpander
  | `($(_) $p $v) => `(write $p $v)
  | _ => throw ()

@[app_unexpander Sep.SymExec.Cmd.free]
def unexpandCmdFree : Lean.PrettyPrinter.Unexpander
  | `($(_) $p) => `(free $p)
  | _ => throw ()

@[app_unexpander Sep.SymExec.Cmd.ret]
def unexpandCmdRet : Lean.PrettyPrinter.Unexpander
  | `($(_) $a) => `(pure $a)
  | _ => throw ()

/--
  Render `Cmd.bind e (fun x => k)` back to do-notation.

  In Lean 4, `doLetArrow` uses `doElemParser` (not `termParser`) for the RHS of `←`, so we
  cannot write `let $x ← $e` in a quotation when `$e : TSyntax term`. We work around this by
  unsafely recasting the term syntax node as a `doElem` — valid because `doExpr := termParser`
  (any term IS a doElem syntactically).

  Flattening: if the body `k` is a `do { ... }` block, we spread its items directly into the
  outer block (via the `$s*` splat) rather than nesting, producing a flat sequence.
-/
@[app_unexpander Sep.SymExec.Cmd.bind]
def unexpandCmdBind : Lean.PrettyPrinter.Unexpander
  -- Binding form with flattening (body is already a do-block)
  | `($(_) $e fun $x:ident => do { $s* }) => do
    let eDE : TSyntax `doElem := ⟨e.raw⟩
    let la ← `(doElem| let $x:ident ← $eDE)
    `(do { $la:doElem; $s* })
  -- Binding form, atomic body
  | `($(_) $e fun $x:ident => $k) => do
    let eDE : TSyntax `doElem := ⟨e.raw⟩
    let kDE : TSyntax `doElem := ⟨k.raw⟩
    let la ← `(doElem| let $x:ident ← $eDE)
    `(do { $la:doElem; $kDE:doElem })
  -- Sequencing form with flattening (body is already a do-block)
  | `($(_) $e fun _ => do { $s* }) => do
    let eDE : TSyntax `doElem := ⟨e.raw⟩
    `(do { $eDE:doElem; $s* })
  -- Sequencing form, atomic body
  | `($(_) $e fun _ => $k) => do
    let eDE : TSyntax `doElem := ⟨e.raw⟩
    let kDE : TSyntax `doElem := ⟨k.raw⟩
    `(do { $eDE:doElem; $kDE:doElem })
  | _ => throw ()

def wp {A : Type} (c : Cmd A) (Q : A → HProp) : HProp :=
  match c with
  | Cmd.ret a => Q a
  | Cmd.bind m f => wp m (fun x => wp (f x) Q)
  | Cmd.alloc v => ∀✶ p, (p ↦ v) -✶ Q p
  | Cmd.read p => ∃✶ v, (p ↦ v) ✶ ((p ↦ v) -✶ Q v)
  | Cmd.write p v => ∃✶ v0, (p ↦ v0) ✶ ((p ↦ v) -✶ Q ())
  | Cmd.free p => ∃✶ v0, (p ↦ v0) ✶ Q ()

syntax "xsimpl_symexec_steps" : tactic
macro_rules
  | `(tactic| xsimpl_symexec_steps) => `(tactic| (
      first
      | xsimpl_symexec_step
      | xsimpl_abduce_step
      | xsimpl_frame_step
    ))

syntax "sym_exec" : tactic
macro_rules
  | `(tactic| sym_exec) => `(tactic| (
      dsimp only [wp]
      xsimpl_core_with xsimpl_symexec_step
      all_goals (
        try xsimpl_clean
        try rfl
      )
    ))

syntax "sym_exec_abduce" : tactic
macro_rules
  | `(tactic| sym_exec_abduce) => `(tactic| (
      dsimp only [wp]
      xsimpl_core_with xsimpl_symexec_steps
      try xsimpl_close_frames
      try xsimpl_normalize
      all_goals (
        try xsimpl_clean
        try rfl
      )
    ))

end Sep.SymExec
