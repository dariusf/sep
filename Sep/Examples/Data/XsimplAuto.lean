import Sep.Xsimpl
import Lean
open Lean Meta Elab Tactic
open HProp Notation

/-!
# Generic fold/unfold extension for xsimpl

Provides an `@[xsimpl_unfold]` attribute that registers equation lemmas for data
structure predicates, and a `xsimpl_auto` tactic that automatically unfolds any
registered predicate atom encountered during xsimpl.

## Usage

```lean
-- Register fold/unfold lemmas for a predicate:
@[xsimpl_unfold] theorem llist_nil  : llist p []       = emp     := rfl
@[xsimpl_unfold] theorem llist_cons : llist p (v :: vs) = ∃✶ q, ... := rfl

-- Run xsimpl with automatic unfolding:
example : llist p [v] ✶ H ==> H ✶ llist p [v] := by xsimpl_auto

-- Or provide lemmas inline without the attribute:
example : llist p [v] ✶ H ==> H ✶ llist p [v] := by xsimpl_with [llist_nil, llist_cons]
```
-/

namespace Sep.XsimplAuto

-- ============================================================
-- Environment extension: unfold registry
-- ============================================================

/-- An entry in the xsimpl unfold registry: the predicate's head function and the
    equation lemma used to unfold it. -/
structure UnfoldEntry where
  headFn    : Name  -- e.g. `Sep.LList.llist`
  lemmaName : Name  -- e.g. `Sep.LList.llist_cons`
  deriving Repr, Inhabited

initialize xsimplUnfoldExt :
    SimplePersistentEnvExtension UnfoldEntry (Array UnfoldEntry) ←
  registerSimplePersistentEnvExtension {
    name          := `xsimplUnfoldDb
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[]
    addEntryFn    := fun s e => s.push e
    toArrayFn     := List.toArray
  }

-- ============================================================
-- Attribute @[xsimpl_unfold]
-- ============================================================

/-- Extract the head constant of the LHS from an equation lemma
    `∀ ..., f args = rhs`. -/
def headFnOfEqLemma (name : Name) : MetaM (Option Name) := do
  let info ← getConstInfo name
  forallTelescopeReducing info.type fun _ concl => do
    match concl.getAppFnArgs with
    | (``Eq, #[_, lhs, _]) =>
      let fn := lhs.getAppFn
      return if fn.isConst then some fn.constName! else none
    | _ => return none

initialize xsimplUnfoldAttr : Unit ←
  registerBuiltinAttribute {
    name  := `xsimpl_unfold
    descr := "Register a fold/unfold equation lemma for the xsimpl_auto tactic"
    add   := fun declName _stx _persistent => MetaM.run' do
      let headFn? ← headFnOfEqLemma declName
      match headFn? with
      | none =>
        throwError "@[xsimpl_unfold] {declName}: \
          must be an equation lemma of the form `f ... = ...`"
      | some headFn =>
        modifyEnv (xsimplUnfoldExt.addEntry · { headFn, lemmaName := declName })
    erase := fun _declName => pure ()
  }

-- ============================================================
-- Generic unfold step
-- ============================================================

/-- Build unfold entries from a list of lemma names (for the inline `xsimpl_with` form). -/
def extraEntries (lemmaNames : Array Name) : MetaM (Array UnfoldEntry) :=
  lemmaNames.filterMapM fun lemName => do
    let headFn? ← headFnOfEqLemma lemName
    return headFn?.map ({ headFn := ·, lemmaName := lemName })

/-- The standard normalization lemmas always added alongside fold/unfold rewrites. -/
private def normLemmas : Array Name :=
  #[``HProp.hstar_hexists, ``Sep.Xsimpl.hstar_hexists_r,
    ``HProp.hstar_hempty_l, ``HProp.hstar_hempty_r]

/-- Core unfold step used by both `xsimpl_auto` and `xsimpl_with`.
    - Checks LHS and RHS atoms for any predicate whose head function appears in
      `entries` (the combined registered + inline set).
    - On the first match, applies `simp only` with all lemmas for that head function
      plus the standard normalization lemmas.
    - Returns `true` if a rewrite was performed. -/
def unfoldStep (entries : Array UnfoldEntry) : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let (fn, args) := goalType.getAppFnArgs
  unless fn == ``HProp.himpl && args.size == 3 do return false
  let lhs := args[1]!
  let rhs := args[2]!

  -- Collect all registered head functions
  let allFns := entries.map (·.headFn)

  -- Find the first atom in LHS or RHS whose head is registered
  let items := Sep.Xsimpl.parseHstar lhs ++ Sep.Xsimpl.parseHstar rhs
  let foundFn? := items.findSome? fun item =>
    item.getAppFn.constName?.filter (allFns.contains ·)

  let some headFn := foundFn? | return false

  -- Collect the simp lemmas for this head function
  let foldLemmas := entries.filterMap (fun e =>
    if e.headFn == headFn then some e.lemmaName else none)

  trace[xsimpl] m!"xsimpl_auto: unfolding {headFn} using {foldLemmas}"

  let allNames := foldLemmas ++ normLemmas
  let lemmaTerms ← allNames.mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
  evalTactic (← `(tactic| simp only [$lemmaTerms,*]))
  return true

-- ============================================================
-- Registered-only step (used by xsimpl_auto)
-- ============================================================

/-- One unfold step using only the `@[xsimpl_unfold]` registry. -/
elab "xsimpl_unfold_step" : tactic => withMainContext do
  let entries := xsimplUnfoldExt.getState (← getEnv)
  unless ← unfoldStep entries do
    throwError "xsimpl_unfold_step: no registered predicate atom in goal"

/-- `xsimpl` extended with automatic unfolding of all `@[xsimpl_unfold]`-registered predicates.
    Registered lemmas are applied on demand as unfold steps interleaved with the standard
    xsimpl cancellation machinery. -/
syntax "xsimpl_auto" : tactic
macro_rules
  | `(tactic| xsimpl_auto) => `(tactic| (
      xsimpl_core_with xsimpl_unfold_step
      all_goals (try xsimpl_clean)))

-- ============================================================
-- Inline form: xsimpl_with [lemma1, lemma2, ...]
-- ============================================================

/-- `xsimpl` with inline fold/unfold lemmas (simp-style), without needing `@[xsimpl_unfold]`.
    The provided lemmas are applied via `simp only` as unfold steps interleaved with the
    standard xsimpl simplification loop. -/
elab "xsimpl_with" "[" lemmas:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  withMainContext do
  -- Extract Name from simpLemma syntax
  let names ← lemmas.getElems.filterMapM fun stx => do
    if let `(Lean.Parser.Tactic.simpLemma| $id:ident) := stx then
      return some id.getId
    return none
  -- Build the combined entry set: registry + inline lemmas
  let regEntries := xsimplUnfoldExt.getState (← getEnv)
  let inlineEntries ← extraEntries names
  let allEntries := regEntries ++ inlineEntries
  -- Run xsimpl_core_with a step that consults allEntries
  -- We implement this as a loop here rather than going through a new tactic name,
  -- since we need to close over `allEntries`.
  evalTactic (← `(tactic| try xsimpl_normalize))
  let mut cont := true
  while cont do
    cont := false
    let goals ← getUnsolvedGoals
    if goals.isEmpty then break
    -- Try standard xsimpl_step first, then our unfold step
    let stdOk ← tryTactic (evalTactic (← `(tactic| xsimpl_step)))
    if stdOk then
      evalTactic (← `(tactic| try xsimpl_normalize))
      cont := true
    else
      let unfOk ← unfoldStep allEntries
      if unfOk then
        evalTactic (← `(tactic| try xsimpl_normalize))
        cont := true
  -- Final cleanup (close remaining emp ==> emp or similar)
  evalTactic (← `(tactic| all_goals (try xsimpl_clean)))

end Sep.XsimplAuto
