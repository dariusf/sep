import Sep.SepLogic

/-!
# sl_pull and sl_perm

Two tactics that reshape separating conjunctions in place, anywhere in the goal (or in a hypothesis with `at h`), by equality.
-/

open Lean Meta Elab Tactic

namespace Sep.Reordering

/-! ## `∗`-tree surgery -/

/-- The head constant of separating conjunction. -/
private def starHead : Name := ``SepLogic.star

/-- The head constant of the empty resource. -/
private def empHead : Name := ``SepLogic.emp

/-- View a term as a separating conjunction: its two factors, together with the
head applied to its leading (type and instance) arguments, which rebuilds a
conjunction at the same instance. -/
private def starParts? (e : Expr) : Option (Expr × Expr × (Expr → Expr → Expr)) := do
  let f := e.getAppFn
  let .const n _ := f | none
  guard (n == starHead)
  let args := e.getAppArgs
  guard (args.size ≥ 2)
  let pre := args.extract 0 (args.size - 2)
  let a := args[args.size - 2]!
  let b := args[args.size - 1]!
  some (a, b, fun x y => mkAppN (mkAppN f pre) #[x, y])

/-- The rebuilder for a `∗`-tree: the connective at the tree's own instance. -/
private def starMk? (e : Expr) : Option (Expr → Expr → Expr) :=
  (starParts? e).map (·.2.2)

/-- Is this term headed by `∗`? -/
private def isStar (e : Expr) : Bool := (starParts? e).isSome

/-- Is this term the empty resource? -/
private def isEmp (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => n == empHead
  | _ => false

/-- The atoms of a `∗`-tree, left to right. -/
private partial def atomsOf (e : Expr) : Array Expr :=
  match starParts? e with
  | some (a, b, _) => atomsOf a ++ atomsOf b
  | none => #[e]

/-- Rebuild a right-nested `∗`-tree from a non-empty atom list, using `f` for
the connective. -/
private def mkStarTree (f : Expr → Expr → Expr) (atoms : Array Expr) : Option Expr :=
  if atoms.isEmpty then none
  else
    let last := atoms[atoms.size - 1]!
    some <| (atoms.extract 0 (atoms.size - 1)).foldr (fun a acc => f a acc) last

/-- The tree obtained by moving the `i`-th atom of `tree` to the head, keeping
the others in their original relative order and right-nesting the result. -/
private def reshape (tree : Expr) (i : Nat) : Option Expr := do
  let f ← starMk? tree
  let atoms := atomsOf tree
  mkStarTree f (#[atoms[i]!] ++ atoms.eraseIdx! i)

/-! ## Locating trees in a goal -/

/-- A maximal `∗`-tree found in a term.  `expr` may contain *loose bound
variables* referring to `binders`, the telescope of enclosing binders it was
found under (outermost first, each type relative to the preceding ones).  Use
`withTree` to work with it. -/
private structure StarTree where
  /-- The tree, with loose bound variables for `binders`. -/
  expr : Expr
  /-- The enclosing binder telescope, outermost first. -/
  binders : Array (Name × Expr)
  deriving Inhabited

/-- Re-enter a tree's binder telescope: runs `k` with fresh free variables for
the binders and the tree instantiated with them. -/
private def withTree {α : Type} [Inhabited α] (t : StarTree) (k : Array Expr → Expr → TacticM α) :
    TacticM α :=
  withLocalDeclsD (t.binders.map fun (n, ty) => (n, fun xs => pure (ty.instantiateRev xs)))
    fun xs => k xs (t.expr.instantiateRev xs)

/-- Collect the maximal `∗`-trees of a term, in traversal order, descending
under binders.  A tree's atoms are traversed too, so a `∗`-tree hidden inside a
postcondition lambda under another tree's atom is found as well. -/
private partial def collectTrees (e : Expr) : Array StarTree :=
  go e #[] #[]
where
  go (e : Expr) (bs : Array (Name × Expr)) (acc : Array StarTree) : Array StarTree :=
    if isStar e then
      (atomsOf e).foldl (fun acc a => goChildren a bs acc) (acc.push ⟨e, bs⟩)
    else
      goChildren e bs acc
  goChildren (e : Expr) (bs : Array (Name × Expr)) (acc : Array StarTree) : Array StarTree :=
    match e with
    | .app .. =>
      (e.getAppArgs).foldl (fun acc a => go a bs acc) (go e.getAppFn bs acc)
    | .lam n ty b _ => go b (bs.push (n, ty)) acc
    | .forallE n ty b _ => go b (bs.push (n, ty)) acc
    | .mdata _ b => go b bs acc
    | .proj _ _ b => go b bs acc
    | .letE _ ty v b _ => go b (bs.push (`x, ty)) (go v bs (go ty bs acc))
    | _ => acc

/-- Format an atom list for error messages. -/
private def fmtAtoms (atoms : Array Expr) : MetaM MessageData := do
  let ms ← atoms.mapM fun a => do return m!"  {← instantiateMVars a}"
  return MessageData.joinSep ms.toList "\n"

/-! ## Proving and applying the reshaping equality -/

/-- The reshaping equality `∀ xs, lhs = rhs`, quantified over only those binders
of `xs` the equality actually mentions (directly, or through the type of another
kept binder).  Quantifying over an unused binder would leave `simp` with a
metavariable it cannot instantiate from the pattern, and the rewrite would
silently never fire. -/
private def mkTreeEq (xs : Array Expr) (lhs rhs : Expr) : TacticM Expr := do
  let eq ← mkEq lhs rhs
  let mut keep : Array Expr := #[]
  for x in xs.reverse do
    let mut used := eq.containsFVar x.fvarId!
    unless used do
      for y in keep do
        if (← inferType y).containsFVar x.fvarId! then used := true
    if used then keep := keep.push x
  mkForallFVars keep.reverse eq

/-- Prove a closed `∀ xs, lhs = rhs` by AC normalisation of `∗` plus the `emp`
unit laws.  Throws if the equality does not hold up to those moves. -/
private def proveTreeEq (ty : Expr) : TacticM Expr := do
  let goal ← mkFreshExprSyntheticOpaqueMVar ty
  let stx ← `(tactic|
    (intros
     -- The `emp` cleanup may already close the goal (a pure unit move), in which
     -- case there is nothing left to close by `ac_rfl`; an unclosed goal is
     -- caught by the emptiness check below, so `try` loses no failure.
     try simp only [SepLogic.star_emp_l, SepLogic.star_emp_r]
     try first
       | rfl
       | ac_rfl))
  let rem ← Tactic.run goal.mvarId! (Tactic.evalTactic stx)
  unless rem.isEmpty do
    throwError "sl: could not prove the reshaping equality{indentExpr ty}"
  instantiateMVars goal

/-- Rewrite the goal (or a hypothesis) with a proved reshaping equality.

The equality is turned into a `simp` theorem *by hand*, with `perm := false`: a
reshaping is by construction a permutation of its own left-hand side, and simp's
ordered rewriting would refuse to apply half of them. -/
private def rewriteWith (proof : Expr) (loc : Option FVarId) : TacticM Unit := do
  let ty ← instantiateMVars (← inferType proof)
  let (_, _, body) ← forallMetaTelescope ty
  let some (_, lhs, _) := body.eq?
    | throwError "sl: internal: the reshaping fact is not an equality"
  let keys ← withSimpGlobalConfig <| DiscrTree.mkPath lhs (noIndexAtArgs := false)
  let thm : SimpTheorem :=
    { keys, proof, origin := .other `slConv, rfl := false, perm := false }
  let thms := ({} : SimpTheorems).addSimpEntry (.thm thm)
  let ctx ← Simp.mkContext (config := {}) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let goal ← getMainGoal
  -- `simp` reports an unchanged goal by returning it, not by failing; a
  -- reshaping that quietly fails to apply would be far worse than an error.
  match loc with
  | none =>
    let before ← goal.getType
    let (res, _) ← simpTarget goal ctx
    replaceMainGoal res.toList
    if let some g := res then
      if (← g.getType) == before then
        throwError "sl: the reshaping equality did not apply to the goal"
  | some fv =>
    let before ← fv.getType
    let (res, _) ← simpLocalDecl goal fv ctx
    replaceMainGoal (res.map (·.2)).toList
    if let some (fv', g) := res then
      if (← g.withContext fv'.getType) == before then
        throwError "sl: the reshaping equality did not apply to `{Expr.fvar fv}`"

/-- The no-op case: the tree is already in the requested shape.  The goal is
restated (a fresh, definitionally equal metavariable) rather than left untouched,
so that an intentionally idempotent call still counts as a proof step. -/
private def noOp (loc : Option FVarId) : TacticM Unit := do
  if loc.isNone then
    let goal ← getMainGoal
    let fresh ← mkFreshExprSyntheticOpaqueMVar (← goal.getType)
    goal.assign fresh
    replaceMainGoal [fresh.mvarId!]

/-- The maximal `∗`-trees of the current goal, or of the hypothesis `loc`. -/
private def treesOf (loc : Option FVarId) : TacticM (Array StarTree) := do
  let e ← match loc with
    | none => getMainTarget
    | some fv => fv.getType
  return collectTrees (← instantiateMVars e)

/-- Elaborate a pattern at a given type. -/
private def elabPatternAt (stx : Term) (ty : Expr) : TacticM Expr := do
  let e ← Term.withSynthesize (postpone := .no) <| Term.elabTerm stx (some ty)
  instantiateMVars e

/-- Elaborate a pattern at the type of a `∗`-tree present in the goal, so that
notation-only patterns get an expected type.  Used for the `∗`-shape check and
for error messages; matching re-elaborates inside the tree's own telescope. -/
private def elabPattern (stx : Term) (trees : Array StarTree) : TacticM Expr := do
  let some t := trees[0]? | throwError "sl: no separating conjunction in the goal"
  let ty ← withTree t fun _ tree => inferType tree
  elabPatternAt stx ty

/-- Does `pat` match the whole atom `a`?  Tested at reducible transparency, with
the metavariable assignments rolled back. -/
private def matchesAtom (pat a : Expr) : MetaM Bool :=
  withoutModifyingState <| withReducible <| isDefEq pat a

/-! ## `sl_pull` -/

/-- The implementation of `sl_pull`. -/
private def slPullCore (patStx : Term) (occ : Option Nat) (loc : Option FVarId) :
    TacticM Unit := do
  let trees ← treesOf loc
  if trees.isEmpty then throwError "sl_pull: no separating conjunction found"
  let pat ← elabPattern patStx trees
  if isStar pat then
    throwError "sl_pull: the pattern{indentExpr pat}\nis itself a `∗`-tree; \
      `sl_pull` moves a single atom.  Use `sl_perm` to reshape a whole tree."
  -- Every (tree, atom index) whose atom matches the pattern, in traversal order.
  -- Two matches that would produce the very same rewrite — interchangeable
  -- copies of one atom, say — are not a genuine ambiguity, so they are merged.
  let mut hits : Array (Nat × Nat) := #[]
  for hi : ti in [0:trees.size] do
    hits ← withTree trees[ti] fun _ tree => do
      -- The pattern is re-elaborated inside the tree's telescope: its holes must
      -- be allowed to be filled with the tree's own bound variables.
      let patIn ← elabPatternAt patStx (← inferType tree)
      let atoms := atomsOf tree
      let mut hits := hits
      for hj : ai in [0:atoms.size] do
        if ← matchesAtom patIn atoms[ai] then
          unless hits.any fun (ti', ai') =>
              ti' == ti && reshape tree ai' == reshape tree ai do
            hits := hits.push (ti, ai)
      return hits
  if hits.isEmpty then
    let atoms ← trees.flatMapM fun t => withTree t fun _ tree => pure (atomsOf tree)
    throwError "sl_pull: no atom matches{indentExpr pat}\nthe atoms in scope are:\n\
      {← fmtAtoms atoms}"
  let (ti, ai) ← match occ with
    | some n =>
      if n ≥ 1 && n - 1 < hits.size then pure hits[n - 1]!
      else throwError "sl_pull: (occs := {n}) is out of range; {hits.size} atoms match"
    | none =>
      if hits.size > 1 then
        let ms ← hits.mapM fun (ti, ai) =>
          withTree trees[ti]! fun _ tree => pure (atomsOf tree)[ai]!
        throwError "sl_pull: {hits.size} atoms match{indentExpr pat}\n\
          namely:\n{← fmtAtoms ms}\ndisambiguate with `(occs := n)`"
      pure hits[0]!
  -- Build `∀ xs, tree = reshaped` inside the tree's binder telescope, so that
  -- the statement that leaves it is closed.
  let ty? ← withTree trees[ti]! fun xs tree => do
    match reshape tree ai with
    | none => throwError "sl_pull: internal: not a `∗`-tree"
    | some rhs => if rhs == tree then pure none else return some (← mkTreeEq xs tree rhs)
  let some ty := ty? | return (← noOp loc)
  rewriteWith (← proveTreeEq ty) loc

/-- **`sl_pull pat`** — move the atom matching `pat` to the head of its
separating conjunction, keeping the other atoms in their original relative order
and right-nesting the result.

The pattern is a term with `_` holes (`inv ι _`, `_ ↦ᵥ _`, `⌜_⌝`, or a fully
explicit atom), elaborated at the type of the conjuncts and matched against whole
*atoms* — the leaves of the flattened `∗`-tree — up to reducible defeq.  A
pattern matching only a strict subterm of an atom does not match, and a
`∗`-shaped pattern is rejected.

The tree may sit anywhere in the goal, including under a binder (a postcondition
`fun v => …`).  With `at h` the hypothesis `h` is reshaped instead.

If no atom matches, the atoms in scope are listed; if several genuinely distinct
ones do, they are listed and `(occs := n)` selects the `n`-th in traversal order.
The rewrite is by an equality proved from associativity, commutativity and the
`emp` unit laws only — nothing is duplicated, dropped or weakened — and that
equality is discharged before the goal is touched, so failure is clean.  Pulling
an atom that is already at the head is a no-op. -/
syntax (name := slPull) "sl_pull " term (" (occs" " := " num ")")? (" at " ident)? : tactic

elab_rules : tactic
  | `(tactic| sl_pull $pat:term $[(occs := $n)]? $[at $h:ident]?) =>
    -- In the main goal's context: the pattern may mention variables the tactic
    -- script itself introduced, which are absent from the declaration's context.
    withMainContext do
      let occ := n.map (·.getNat)
      match h with
      | none => slPullCore pat occ none
      | some h => slPullCore pat occ (some (← getFVarId h))

/-! ## `sl_perm` -/

/-- Copy a target tree's shape, mapping each leaf to the source atom it was
matched with (`emp` leaves to the source instance's `emp`), and rebuilding the
connective at the source's instance. -/
private partial def rebuildShape (starOf : Expr → Expr → Expr) (empE : Expr)
    (assign : Array (Expr × Expr)) (t : Expr) : Expr :=
  match starParts? t with
  | some (a, b, _) =>
    starOf (rebuildShape starOf empE assign a) (rebuildShape starOf empE assign b)
  | none =>
    if isEmp t then empE
    else match assign.find? fun (l, _) => l == t with
      | some (_, r) => r
      | none => t

/-- Try to reshape `tree` (already instantiated, under binders `xs`) into the
target elaborated from `tgtStx`.  Returns the closed `∀ xs, tree = target`, or
`none` if the named target atoms do not all occur in this tree. -/
private def permTreeEq? (tgtStx : Term) (xs : Array Expr) (tree : Expr) :
    TacticM (Option Expr) := do
  let tgt ← elabPatternAt tgtStx (← inferType tree)
  let tgtAtoms := atomsOf tgt
  let named := tgtAtoms.filter fun a => !a.isMVar && !isEmp a
  let holes := tgtAtoms.filter fun a => a.isMVar
  let srcAtoms := atomsOf tree
  -- Consume the source atoms: named target atoms first, then the `_` holes in
  -- left-to-right order over what is left.  `emp` is ignored on both sides.
  let mut pool := (srcAtoms.filter (!isEmp ·)).toList
  let mut assign : Array (Expr × Expr) := #[]
  for na in named do
    match ← pool.findM? (matchesAtom na ·) with
    | none => return none
    | some a =>
      unless ← isDefEq na a do return none
      pool := pool.erase a
      assign := assign.push (na, a)
  if holes.size ≠ pool.length then
    throwError "sl_perm: the target is not a permutation of the source.\n\
      source atoms:\n{← fmtAtoms srcAtoms}\ntarget atoms:\n{← fmtAtoms tgtAtoms}"
  for (hole, a) in holes.zip pool.toArray do
    unless ← isDefEq hole a do
      throwError "sl_perm: could not fill the hole{indentExpr hole}\nwith{indentExpr a}"
    assign := assign.push (hole, a)
  -- Rebuild the target's *shape* out of the source's own atoms, connective and
  -- `emp`.  Elaborating the target on its own can pick a different (universe-)
  -- instance of `SepLogic`; taking only the shape from it keeps the equality
  -- inside the instance the goal actually uses.
  let some source := starParts? tree
    | throwError "sl_perm: internal: not a `∗`-tree"
  let f := tree.getAppFn
  let lvls := f.constLevels!
  let pre := tree.getAppArgs.extract 0 (tree.getAppArgs.size - 2)
  let empE := mkAppN (mkConst empHead lvls) pre
  let rhs := rebuildShape source.2.2 empE assign tgt
  return some (← mkTreeEq xs tree rhs)

/-- The implementation of `sl_perm`. -/
private def slPermCore (tgtStx : Term) (loc : Option FVarId) : TacticM Unit := do
  let trees ← treesOf loc
  if trees.isEmpty then throwError "sl_perm: no separating conjunction found"
  -- The tree to rewrite is the first one containing all the named target atoms.
  let mut ty? : Option Expr := none
  for t in trees do
    if ty?.isNone then
      ty? ← withTree t fun xs tree => permTreeEq? tgtStx xs tree
  let some ty := ty?
    | throwError "sl_perm: no `∗`-tree in the goal contains all of the target's \
        named atoms"
  -- A target that is already in place is a no-op.
  if let some (_, lhs, rhs) := (← forallTelescope ty fun _ b => pure b).eq? then
    if lhs == rhs then return (← noOp loc)
  rewriteWith (← proveTreeEq ty) loc

/-- **`sl_perm tgt`** — reshape a separating conjunction into exactly the tree
`tgt`, parenthesisation included.

`tgt` is a full `∗`-tree whose atoms may be `_` holes.  Named atoms are matched
against whole source atoms exactly as for `sl_pull`, and they must all live in a
single maximal `∗`-tree of the goal — that tree is the one rewritten.  The
remaining source atoms then fill the `_` holes left to right.  `emp` leaves may
be added or removed freely by the target.

The target must be a permutation of the source atoms up to associativity,
commutativity and `emp`; otherwise both atom lists are printed.  The rewrite is
by a proved equality, discharged before the goal is touched, so failure is clean.
`at h` reshapes a hypothesis instead of the goal. -/
syntax (name := slPerm) "sl_perm " term (" at " ident)? : tactic

elab_rules : tactic
  | `(tactic| sl_perm $tgt:term $[at $h:ident]?) =>
    withMainContext do
      match h with
      | none => slPermCore tgt none
      | some h => slPermCore tgt (some (← getFVarId h))

end Sep.Reordering
