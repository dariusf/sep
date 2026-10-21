import Sep.Xsimpl
import Sep.SegC
import Lean
open Lean Meta Elab Tactic
open HProp Notation

namespace Sep.Xsearch

-- # EVOLVE-BLOCK-START

structure UnfoldEntry where
  headFn    : Name
  lemmaName : Name
  deriving Repr, Inhabited

initialize xsearchUnfoldExt :
    SimplePersistentEnvExtension UnfoldEntry (Array UnfoldEntry) ←
  registerSimplePersistentEnvExtension {
    name          := `xsearchUnfoldDb
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[]
    addEntryFn    := fun s e => s.push e
    toArrayFn     := List.toArray
  }

def headFnOfEqLemma (name : Name) : MetaM (Option Name) := do
  let info ← getConstInfo name
  forallTelescopeReducing info.type fun _ concl => do
    match concl.getAppFnArgs with
    | (``Eq, #[_, lhs, _]) =>
      let fn := lhs.getAppFn
      return if fn.isConst then some fn.constName! else none
    | _ => return none

initialize xsearchUnfoldAttr : Unit ←
  registerBuiltinAttribute {
    name  := `xsearch_unfold
    descr := "Register an unfold equation lemma for the xsearch tactic"
    add   := fun declName _stx _persistent => MetaM.run' do
      match ← headFnOfEqLemma declName with
      | none =>
        throwError "@[xsearch_unfold] {declName}: must be an equation lemma of the form `f ... = ...`"
      | some headFn =>
        modifyEnv (xsearchUnfoldExt.addEntry · { headFn, lemmaName := declName })
    erase := fun _declName => pure ()
  }

def hbPerVms : Nat := 44000

def vclock : BaseIO Nat := return (← IO.getNumHeartbeats) / hbPerVms

initialize globalDeadline : IO.Ref Nat ← IO.mkRef 0

def pastGlobal : CoreM Bool := do
  return (← vclock) > (← globalDeadline.get)

initialize searchDeadline : IO.Ref Nat ← IO.mkRef 0
initialize searchNodes : IO.Ref Nat ← IO.mkRef 0
initialize unfoldBudget : IO.Ref Nat ← IO.mkRef 0

private def normLemmas : Array Name :=
  #[``HProp.hstar_hexists, ``Sep.Xsimpl.hstar_hexists_r,
    ``HProp.hstar_hempty_l, ``HProp.hstar_hempty_r]

initialize bodySigCache : IO.Ref (Array (Name × Bool × Array Name)) ← IO.mkRef #[]

def rwConst (n : Name) : TacticM Bool := do
  let st ← saveState
  try
    let g ← getMainGoal
    let r ← g.withContext do g.rewrite (← g.getType) (← mkConstWithFreshMVarLevels n)
    let g' ← g.replaceTargetEq r.eNew r.eqProof
    replaceMainGoal (g' :: r.mvarIds)
    let s2 ← saveState
    try withReducible g'.applyRfl catch _ => s2.restore
    return true
  catch _ =>
    st.restore
    return false

initialize simpOnlyCache : IO.Ref (Array (Array Name × SimpTheorems)) ← IO.mkRef #[]

def simpOnlyThms (lemmas : Array Name) : MetaM SimpTheorems := do
  match (← simpOnlyCache.get).find? (·.1 == lemmas) with
  | some (_, t) => return t
  | none =>
    let mut thms : SimpTheorems := {}
    for n in [``eq_self, ``iff_self] do
      thms ← thms.addConst n
    for n in lemmas do
      thms ← thms.addConst n
    simpOnlyCache.modify (·.push (lemmas, thms))
    return thms

def simpOnlyTarget (lemmas : Array Name) : TacticM Bool := do
  let thms ← simpOnlyThms lemmas
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let s ← saveState
  try
    let _ ← simpLocation ctx #[{}] none (.targets #[] true)
    return true
  catch _ =>
    s.restore
    return false

def allGoalsTry (t : TacticM Unit) : TacticM Unit := do
  let mut acc : List MVarId := []
  for g in ← getGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    let s ← saveState
    try t catch _ => s.restore
    acc := acc ++ (← getUnsolvedGoals)
  setGoals acc

def isHorHead (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => n.components.getLast? == some `hor
  | _ => false

def predSig (allFns : Array Name) (e : Expr) : Array Name :=
  let cs := e.getUsedConstants.filter (allFns.contains ·)
  cs.foldl (fun acc c => if acc.contains c then acc else acc.push c) #[] |>.qsort Name.lt

def bodySig (entries : Array UnfoldEntry) (hd : Name) : MetaM (Bool × Array Name) := do
  match (← bodySigCache.get).find? (·.1 == hd) with
  | some (_, b, sg) => return (b, sg)
  | none =>
  let allFns := entries.map (·.headFn)
  let mut isH := false
  let mut sg : Array Name := #[]
  for e in entries do
    if e.headFn == hd then
      let ty := (← getConstInfo e.lemmaName).type
      let (b, g) ← forallTelescopeReducing ty fun _ concl => do
        match concl.eq? with
        | some (_, _, body) => pure (isHorHead body, predSig allFns body)
        | none => pure (false, #[])
      isH := isH || b
      for c in g do
        unless sg.contains c do sg := sg.push c
  let sgs := sg.qsort Name.lt
  bodySigCache.modify (·.push (hd, isH, sgs))
  return (isH, sgs)

def horPartner (entries : Array UnfoldEntry) (sg : Array Name) (r : Expr) : MetaM Bool := do
  let allFns := entries.map (·.headFn)
  if isHorHead r then return predSig allFns r == sg
  match r.getAppFn.constName? with
  | some n =>
      if allFns.contains n then
        let (bh, bs) ← bodySig entries n
        return !bh || bs == sg
      if n == ``HProp.hsingle || n == ``HProp.hpure || n == ``HProp.hempty then return false
      return true
  | none => return !r.isFVar

def horStuck (entries : Array UnfoldEntry) (mine other : List Expr) : MetaM Bool := do
  let allFns := entries.map (·.headFn)
  for h in mine do
    if isHorHead h && !other.contains h then
      let sg := predSig allFns h
      unless ← other.anyM (horPartner entries sg) do return true
  return false

partial def fastSubstVars (g : MVarId) : MetaM MVarId := g.withContext do
  let lctx ← getLCtx
  let mut keys : Array FVarId := #[]
  for d in lctx do
    if let some (_, a, b) ← matchEq? (← instantiateMVars d.type) then
      if a.isFVar || b.isFVar then
        keys := keys.push d.fvarId
        if a.isFVar then keys := keys.push a.fvarId!
        if b.isFVar then keys := keys.push b.fvarId!
  if keys.isEmpty then return g
  for d in lctx do
    if keys.contains d.fvarId then
      if let some g' ← subst? g d.fvarId then
        return ← fastSubstVars g'
  return g

elab "xsearch_subst" : tactic => liftMetaTactic fun g => return [← fastSubstVars g]

variable [Params]

def applyConstT (n : Name) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  replaceMainGoal (← g.apply (← mkConstWithFreshMVarLevels n))

initialize wgLocHook : IO.Ref (Expr → Expr → TacticM (Option Expr)) ← IO.mkRef (fun _ _ => pure none)
partial def wgCellWalk (H : Expr) (pre : List Bool) (acc : Array (Expr × List Bool)) : Array (Expr × List Bool) :=
  match H.getAppFnArgs with
  | (``HProp.hsingle, #[_, a, _]) => acc.push (a, pre.reverse)
  | (``HProp.hstar, #[_, a, b]) => wgCellWalk b (false :: pre) (wgCellWalk a (true :: pre) acc)
  | _ => acc

partial def wgCellPath? (p H : Expr) : Option (List Bool) :=
  match H.getAppFnArgs with
  | (``HProp.hsingle, #[_, a, _]) => if a == p then some [] else none
  | (``HProp.hstar, #[_, a, b]) => match wgCellPath? p a with
    | some l => some (true :: l)
    | none => (wgCellPath? p b).map (false :: ·)
  | _ => none

partial def wgLift (p H : Expr) (leaf : Expr) : List Bool → Option Expr
  | [] => some leaf
  | d :: rest => match H.getAppFnArgs with
    | (``HProp.hstar, #[inst, a, b]) =>
      if d then (wgLift p a leaf rest).map fun h => mkAppN (mkConst ``hasLoc_star_l) #[inst, p, a, b, h]
      else (wgLift p b leaf rest).map fun h => mkAppN (mkConst ``hasLoc_star_r) #[inst, p, a, b, h]
    | _ => none

partial def wgPathNe (p q H hp hq : Expr) : List Bool → List Bool → Option Expr
  | d :: P, e :: Q => match H.getAppFnArgs with
    | (``HProp.hstar, #[inst, a, b]) =>
      if d && e then (wgPathNe p q a hp hq P Q).map fun h => mkAppN (mkConst ``neLocs_star_l) #[inst, p, q, a, b, h]
      else if !d && !e then (wgPathNe p q b hp hq P Q).map fun h => mkAppN (mkConst ``neLocs_star_r) #[inst, p, q, a, b, h]
      else if d then do
        let h1 ← wgLift p a hp P
        let h2 ← wgLift q b hq Q
        some (mkAppN (mkConst ``neLocs_star) #[inst, p, q, a, b, h1, h2])
      else do
        let h1 ← wgLift q a hq Q
        let h2 ← wgLift p b hp P
        some (mkAppN (mkConst ``neLocs_star') #[inst, p, q, a, b, h1, h2])
    | _ => none
  | _, _ => none

partial def wgLeafAt (H : Expr) : List Bool → Option Expr
  | [] => some H
  | d :: rest => match H.getAppFnArgs with
    | (``HProp.hstar, #[_, a, b]) => wgLeafAt (if d then a else b) rest
    | _ => none

def wgCells (H : Expr) : Array (Expr × List Bool) := wgCellWalk H [] #[]

def wgCellLoc? (p H : Expr) : MetaM (Option Expr) := do
  let some P := wgCellPath? p H | return none
  let some (.app (.app (.app _ inst) a) v) := wgLeafAt H P | return none
  wgLift p H (mkApp3 (mkConst ``hasLoc_single) inst a v) P |> pure

structure WgLocHy where
  locs : Array (Expr × Expr × Expr) := #[]
  nes : Array (Expr × Expr × Expr) := #[]

def wgLocHyps (nes : Bool := false) : MetaM WgLocHy := do
  let mut r : WgLocHy := {}
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless d.type.isAppOf ``hasLoc || (nes && d.type.isAppOf ``Ne) do continue
    let ty ← if d.type.hasMVar then instantiateMVars d.type else pure d.type
    match ty.getAppFnArgs with
    | (``hasLoc, #[_, l, H]) => r := { r with locs := r.locs.push (l, H, d.toExpr) }
    | (``Ne, #[_, a, b]) => r := { r with nes := r.nes.push (a, b, d.toExpr) }
    | _ => pure ()
  return r

partial def wgAllocGo (hy : WgLocHy) (rich : Bool) (p H : Expr) : TacticM (Option Expr) := do
  if let some (_, _, h) := hy.locs.find? (fun (l, G, _) => l == p && G == H) then return some h
  match H.getAppFnArgs with
  | (``HProp.hsingle, #[inst, a, v]) =>
    if a == p || ((a.hasMVar || p.hasMVar) && (← isDefEq a p)) then
      return some (mkApp3 (mkConst ``hasLoc_single) inst a v)
    return none
  | (``HProp.hstar, #[inst, a, b]) =>
    if let some h ← wgAllocGo hy rich p a then return some (mkAppN (mkConst ``hasLoc_star_l) #[inst, p, a, b, h])
    if let some h ← wgAllocGo hy rich p b then return some (mkAppN (mkConst ``hasLoc_star_r) #[inst, p, a, b, h])
    return none
  | (``hdisj, #[inst, a, b]) =>
    let some h1 ← wgAllocGo hy rich p a | return none
    let some h2 ← wgAllocGo hy rich p b | return none
    return some (mkAppN (mkConst ``hasLoc_disj) #[inst, p, a, b, h1, h2])
  | (``HProp.hexists, #[inst, A, J]) =>
    let .lam n ty body bi := J | return none
    let lv ← getLevel A
    withLocalDecl n bi ty fun v => do
      let some h ← wgAllocGo hy rich p (body.instantiate1 v) | return none
      return some (mkAppN (mkConst ``hasLoc_hexists [lv]) #[inst, A, p, J, ← mkLambdaFVars #[v] h])
  | (``HProp.hpure, _) | (``HProp.hempty, _) => return none
  | _ => if rich && (H.find? (· == p)).isSome then (← wgLocHook.get) p H else return none

partial def wgLocPath (hy : WgLocHy) (rich : Bool) (p H : Expr) : TacticM (Option (List Bool × Expr)) := do
  match H.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) =>
    if let some (l, h) ← wgLocPath hy rich p a then return some (true :: l, h)
    if let some (l, h) ← wgLocPath hy rich p b then return some (false :: l, h)
    return none
  | _ => return (← wgAllocGo hy rich p H).map ([], ·)

def wgAllocIn (hy : WgLocHy) (rich : Bool) (p H : Expr) : TacticM (Option Expr) := do
  if let some h ← wgCellLoc? p H then return some h
  if let some (_, _, h) := hy.locs.find? (fun (l, G, _) => l == p && G == H) then return some h
  let some (P, h) ← wgLocPath hy rich p H | return none
  return wgLift p H h P

def wgAlloc (p H : Expr) : TacticM (Option Expr) := do
  wgAllocIn (← wgLocHyps) true (← instantiateMVars p) (← instantiateMVars H)

partial def wgApartIn (hy : WgLocHy) (top : Array (Expr × List Bool)) (p q H : Expr) : TacticM (Option Expr) := do
  let inst := H.getAppArgs[0]!
  for (a, b, h) in hy.nes do
    if a == p && b == q then
      return some (mkAppN (mkConst ``neLocs_const) #[inst, p, q, H, h])
    if a == q && b == p then
      return some (mkAppN (mkConst ``neLocs_const) #[inst, p, q, H, ← mkAppM ``Ne.symm #[h]])
  match H.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) =>
    if a.isAppOfArity ``HProp.hpure 2 then
      let P := a.appArg!
      return ← withLocalDeclD `hp P fun hp => do
        let hy' := if let some (_, x, y) := P.ne? then { hy with nes := hy.nes.push (x, y, hp) } else hy
        let some h ← wgApartIn hy' top p q b | return none
        return some (mkAppN (mkConst ``neLocs_pure_star) #[inst, p, q, P, b, ← mkLambdaFVars #[hp] h])
    let some (P, hp) ← wgLocPath hy (!top.any (·.1 == p)) p H | return none
    let some (Q, hq) ← wgLocPath hy (!top.any (·.1 == q)) q H | return none
    return wgPathNe p q H hp hq P Q
  | (``hdisj, #[_, a, b]) =>
    let some h1 ← wgApartIn hy top p q a | return none
    let some h2 ← wgApartIn hy top p q b | return none
    return some (mkAppN (mkConst ``neLocs_disj) #[inst, p, q, a, b, h1, h2])
  | (``HProp.hexists, #[_, A, J]) =>
    let .lam n ty body bi := J | return none
    let lv ← getLevel A
    withLocalDecl n bi ty fun v => do
      let some h ← wgApartIn hy top p q (body.instantiate1 v) | return none
      return some (mkAppN (mkConst ``neLocs_hexists [lv]) #[inst, A, p, q, J, ← mkLambdaFVars #[v] h])
  | _ => return none

def wgApart (p q H : Expr) : TacticM (Option Expr) := do
  let H ← instantiateMVars H
  wgApartIn (← wgLocHyps true) (wgCells H) (← instantiateMVars p) (← instantiateMVars q) H

def wgAllocGoal (g : MVarId) : TacticM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some h ← (match t.getAppFnArgs with
    | (``hasLoc, #[_, p, H]) => wgAlloc p H
    | (``neLocs, #[_, p, q, H]) => wgApart p q H
    | _ => pure none) | return false
  g.assign h
  return true

def isHorConst (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => n.components.getLast? == some `hor
  | _ => false

partial def replaceHor (e : Expr) : Expr :=
  match e with
  | .app .. =>
      if isHorConst e && e.getAppNumArgs ≥ 2 then
        let args := (e.getAppArgs).map replaceHor
        let n := args.size
        mkAppN (mkConst ``hdisj) (args[0:n-2].toArray.push args[n-2]! |>.push args[n-1]!)
      else
        let f := replaceHor e.getAppFn
        mkAppN f ((e.getAppArgs).map replaceHor)
  | .lam n t b bi => .lam n (replaceHor t) (replaceHor b) bi
  | .forallE n t b bi => .forallE n (replaceHor t) (replaceHor b) bi
  | .mdata _ b => replaceHor b
  | _ => e

def hasDisjExpr (e : Expr) : Bool :=
  (e.find? (fun s =>
    (isHorConst s || s.getAppFn.constName? == some ``hdisj)
      && s.getAppNumArgs ≥ 2)).isSome

def distrRedex (s : Expr) : Bool :=
  match s.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) =>
      a.isAppOfArity ``HProp.hstar 3 || a.isAppOfArity ``hdisj 3
        || b.isAppOfArity ``hdisj 3 || isHorConst a || isHorConst b
  | (``HProp.hexists, #[_, _, j]) =>
      match j with
      | .lam _ _ b _ => b.isAppOfArity ``hdisj 3 || isHorConst b
      | _ => true
  | (``Eq, #[_, a, b]) => a == b
  | (``Iff, #[a, b]) => a == b
  | _ => false

structure DistrCtx where
  inst : Expr
  hty : Expr

namespace DistrCtx

def hs (c : DistrCtx) (a b : Expr) : Expr := mkApp3 (mkConst ``HProp.hstar) c.inst a b

def hd (c : DistrCtx) (a b : Expr) : Expr := mkApp3 (mkConst ``hdisj) c.inst a b

def trans (c : DistrCtx) (a b d : Expr) (p q : Option Expr) : Option Expr :=
  match p, q with
  | none, q => q
  | p, none => p
  | some p, some q => some (mkAppN (mkConst ``Eq.trans [1]) #[c.hty, a, b, d, p, q])

def refl (c : DistrCtx) (a : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [1]) c.hty a

def cong2 (c : DistrCtx) (f a a' b b' : Expr) (pa pb : Option Expr) : Option Expr :=
  if pa.isNone && pb.isNone then none else
  let fty := mkForall `x .default c.hty c.hty
  let h1 := mkAppN (mkConst ``congrArg [1, 1])
    #[c.hty, fty, a, a', f, pa.getD (c.refl a)]
  some (mkAppN (mkConst ``congr [1, 1])
    #[c.hty, c.hty, mkApp f a, mkApp f a', b, b', h1, pb.getD (c.refl b)])

partial def post (c : DistrCtx) (e : Expr) : MetaM (Expr × Option Expr) := do
  if e.isAppOfArity ``HProp.hstar 3 then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    if b.isAppOfArity ``hdisj 3 then
      let b1 := b.appFn!.appArg!
      let b2 := b.appArg!
      let p1 := mkAppN (mkConst ``hdisj_star_r) #[c.inst, a, b1, b2]
      let (r1, q1) ← c.post (c.hs a b1)
      let (r2, q2) ← c.post (c.hs a b2)
      let mid := c.hd (c.hs a b1) (c.hs a b2)
      let res := c.hd r1 r2
      let q := c.cong2 (mkApp (mkConst ``hdisj) c.inst) (c.hs a b1) r1 (c.hs a b2) r2 q1 q2
      return (res, c.trans e mid res (some p1) q)
    if a.isAppOfArity ``hdisj 3 then
      let a1 := a.appFn!.appArg!
      let a2 := a.appArg!
      let p1 := mkAppN (mkConst ``hdisj_star_l) #[c.inst, a1, a2, b]
      let (r1, q1) ← c.post (c.hs a1 b)
      let (r2, q2) ← c.post (c.hs a2 b)
      let mid := c.hd (c.hs a1 b) (c.hs a2 b)
      let res := c.hd r1 r2
      let q := c.cong2 (mkApp (mkConst ``hdisj) c.inst) (c.hs a1 b) r1 (c.hs a2 b) r2 q1 q2
      return (res, c.trans e mid res (some p1) q)
    if a.isAppOfArity ``HProp.hstar 3 then
      let a1 := a.appFn!.appArg!
      let a2 := a.appArg!
      let p1 := mkAppN (mkConst ``HProp.hstar_assoc) #[c.inst, a1, a2, b]
      let (r2, q2) ← c.post (c.hs a2 b)
      let mid := c.hs a1 (c.hs a2 b)
      let e2 := c.hs a1 r2
      let q := c.cong2 (mkApp (mkConst ``HProp.hstar) c.inst) a1 a1 (c.hs a2 b) r2 none q2
      let (r3, q3) ← c.post e2
      return (r3, c.trans e e2 r3 (c.trans e mid e2 (some p1) q) q3)
    return (e, none)
  if e.isAppOfArity ``HProp.hexists 3 then
    let lam := e.appArg!
    let .lam n ty body bi := lam | return (e, none)
    unless body.isAppOfArity ``hdisj 3 do return (e, none)
    let A := e.appFn!.appArg!
    let J := Expr.lam n ty body.appFn!.appArg! bi
    let K := Expr.lam n ty body.appArg! bi
    let lv ← getLevel A
    let p1 := mkAppN (mkConst ``hdisj_hexists [lv]) #[c.inst, A, J, K]
    let ex := mkApp2 (mkConst ``HProp.hexists [lv]) c.inst A
    let (r1, q1) ← c.post (mkApp ex J)
    let (r2, q2) ← c.post (mkApp ex K)
    let mid := c.hd (mkApp ex J) (mkApp ex K)
    let res := c.hd r1 r2
    let q := c.cong2 (mkApp (mkConst ``hdisj) c.inst) (mkApp ex J) r1 (mkApp ex K) r2 q1 q2
    return (res, c.trans e mid res (some p1) q)
  return (e, none)

partial def normProp (P : Expr) : MetaM (Expr × Option Expr) := do
  if P.isAppOfArity ``Eq 3 && P.appFn!.appArg! == P.appArg! then
    let α := P.appFn!.appFn!.appArg!
    return (mkConst ``True, some (mkApp2 (mkConst ``eq_self [← getLevel α]) α P.appArg!))
  if P.isAppOfArity ``Iff 2 && P.appFn!.appArg! == P.appArg! then
    return (mkConst ``True, some (mkApp (mkConst ``iff_self) P.appArg!))
  if P.isAppOfArity ``And 2 then
    let a := P.appFn!.appArg!
    let b := P.appArg!
    let (a', pa) ← normProp a
    let (b', pb) ← normProp b
    if pa.isNone && pb.isNone then return (P, none)
    let prop := mkSort Level.zero
    let fty := mkForall `x .default prop prop
    let rf := fun (x : Expr) => mkApp2 (mkConst ``Eq.refl [1]) prop x
    let h1 := mkAppN (mkConst ``congrArg [1, 1]) #[prop, fty, a, a', mkConst ``And, pa.getD (rf a)]
    return (mkApp2 (mkConst ``And) a' b', some (mkAppN (mkConst ``congr [1, 1])
      #[prop, prop, mkApp (mkConst ``And) a, mkApp (mkConst ``And) a', b, b', h1, pb.getD (rf b)]))
  if (P.find? (fun s => s.isAppOfArity ``Iff 2 || s.isLambda || s.isMData || s.isLet
      || s.isProj || s.isHeadBetaTarget
      || (s.isAppOfArity ``Eq 3 && s.appFn!.appArg! == s.appArg!))).isSome then
    throwError "distr: prop"
  return (P, none)

partial def norm (c : DistrCtx) (e : Expr) : MetaM (Expr × Option Expr) := do
  if e.isAppOfArity ``HProp.hpure 2 then
    let (P', pP) ← normProp e.appArg!
    match pP with
    | none => return (e, none)
    | some pP =>
      let prop := mkSort Level.zero
      let f := mkApp (mkConst ``HProp.hpure) c.inst
      return (mkApp f P', some (mkAppN (mkConst ``congrArg [1, 1])
        #[prop, c.hty, e.appArg!, P', f, pP]))
  if e.isAppOfArity ``HProp.hstar 3 || e.isAppOfArity ``hdisj 3 then
    let f := e.appFn!.appFn!
    let a := e.appFn!.appArg!
    let b := e.appArg!
    let (a', pa) ← c.norm a
    let (b', pb) ← c.norm b
    let e1 := mkApp2 f a' b'
    let p1 := c.cong2 f a a' b b' pa pb
    if e.isAppOfArity ``hdisj 3 then return (e1, p1)
    let (e2, p2) ← c.post e1
    return (e2, c.trans e e1 e2 p1 p2)
  if e.isAppOfArity ``HProp.hexists 3 then
    let .lam n ty body bi := e.appArg! | throwError "distr: exists"
    let (e1, p1) ← withLocalDecl n bi ty fun x => do
      let (b', pb) ← c.norm (body.instantiate1 x)
      match pb with
      | none => return (e, none)
      | some pb =>
        let fe ← mkFunExt (← mkLambdaFVars #[x] pb)
        return (mkApp e.appFn! (← mkLambdaFVars #[x] b'), some (← mkCongrArg e.appFn! fe))
    let (e2, p2) ← c.post e1
    return (e2, c.trans e e1 e2 p1 p2)
  return (e, none)

end DistrCtx

namespace DistrCtx

mutual

partial def exPost (c : DistrCtx) (e : Expr) : MetaM (Expr × Option Expr) := do
  if e.isAppOfArity ``HProp.hstar 3 then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    if a.isAppOfArity ``HProp.hexists 3 then
      let A := a.appFn!.appArg!
      let J := a.appArg!
      let .lam _ _ body _ := J | throwError "exnorm: lam"
      let lv := a.getAppFn.constLevels!
      let p1 := mkAppN (mkConst ``HProp.hstar_hexists lv) #[c.inst, A, J, b]
      let e1 := mkApp3 (mkConst ``HProp.hexists lv) c.inst A (.lam `x A (c.hs body b) .default)
      let (e2, p2) ← c.exNorm e1
      return (e2, c.trans e e1 e2 (some p1) p2)
    if a.isAppOfArity ``HProp.hempty 1 then
      return (b, some (mkApp2 (mkConst ``HProp.hstar_hempty_l) c.inst b))
    if b.isAppOfArity ``HProp.hempty 1 then
      return (a, some (mkApp2 (mkConst ``HProp.hstar_hempty_r) c.inst a))
    return (e, none)
  return (e, none)

partial def exNorm (c : DistrCtx) (e : Expr) : MetaM (Expr × Option Expr) := do
  if e.isAppOfArity ``HProp.hpure 2 then
    let (P', pP) ← normProp e.appArg!
    match pP with
    | none => return (e, none)
    | some pP =>
      let f := mkApp (mkConst ``HProp.hpure) c.inst
      return (mkApp f P', some (mkAppN (mkConst ``congrArg [1, 1])
        #[mkSort Level.zero, c.hty, e.appArg!, P', f, pP]))
  if e.isAppOfArity ``HProp.hstar 3 then
    let f := e.appFn!.appFn!
    let a := e.appFn!.appArg!
    let b := e.appArg!
    let (a', pa) ← c.exNorm a
    let (b', pb) ← c.exNorm b
    let e1 := mkApp2 f a' b'
    let p1 := c.cong2 f a a' b b' pa pb
    let (e2, p2) ← c.exPost e1
    return (e2, c.trans e e1 e2 p1 p2)
  if e.isAppOfArity ``HProp.hexists 3 then
    let .lam n ty body bi := e.appArg! | throwError "exnorm: exists"
    return ← withLocalDecl n bi ty fun x => do
      let (b', pb) ← c.exNorm (body.instantiate1 x)
      match pb with
      | none => return (e, none)
      | some pb =>
        let fe ← mkFunExt (← mkLambdaFVars #[x] pb)
        return (mkApp e.appFn! (← mkLambdaFVars #[x] b'), some (← mkCongrArg e.appFn! fe))
  if e.isApp then
    let fn := e.getAppFn
    let args := e.getAppArgs
    let mut cur := args
    let mut pf : Option Expr := none
    for i in [0 : args.size] do
      let (a', pa) ← c.exNorm args[i]!
      let some pa := pa | continue
      let f ← withLocalDeclD `y (← inferType args[i]!) fun y =>
        mkLambdaFVars #[y] (mkAppN fn (cur.set! i y))
      let step ← mkCongrArg f pa
      pf := some (← match pf with
        | none => pure step
        | some p0 => mkEqTrans p0 step)
      cur := cur.set! i a'
    return (mkAppN fn cur, pf)
  return (e, none)

end

end DistrCtx

partial def exSafe (e : Expr) : Bool :=
  if e.isAppOfArity ``HProp.hexists 3 then
    exSafe e.appFn! && match e.appArg! with
      | .lam _ _ b _ => exSafe b
      | _ => false
  else if e.isAppOfArity ``HProp.hpure 2 then
    (e.appArg!.find? (fun s => s.isAppOfArity ``HProp.hstar 3 || s.isAppOfArity ``HProp.hempty 1
        || s.isAppOfArity ``HProp.hexists 3)).isNone
  else
    match e with
    | .app .. => (e.getAppFn.isConst || e.getAppFn.isFVar) && e.getAppArgs.all exSafe
    | .const .. | .fvar _ | .lit _ | .sort _ | .bvar _ => true
    | _ => false

def exNormTarget : TacticM Bool := do
  let gs ← getGoals
  let some g := gs.head? | return false
  if ← g.isAssigned then return false
  g.withContext do
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``HProp.himpl 3 do return false
  let inst := t.appFn!.appFn!.appArg!
  let L := t.appFn!.appArg!
  let R := t.appArg!
  unless exSafe L && exSafe R do return false
  let c : DistrCtx := { inst, hty := mkApp (mkConst ``HProp) inst }
  let some (L', pL) ← (try some <$> c.exNorm L catch _ => pure none) | return false
  let some (R', pR) ← (try some <$> c.exNorm R catch _ => pure none) | return false
  if pL.isNone && pR.isNone then return true
  let t' := mkApp3 (mkConst ``HProp.himpl) inst L' R'
  let fty := mkForall `x .default c.hty (mkSort Level.zero)
  let f := mkApp (mkConst ``HProp.himpl) inst
  let h1 := mkAppN (mkConst ``congrArg [1, 1]) #[c.hty, fty, L, L', f, pL.getD (c.refl L)]
  let pf := mkAppN (mkConst ``congr [1, 1])
    #[c.hty, mkSort Level.zero, mkApp f L, mkApp f L', R, R', h1, pR.getD (c.refl R)]
  let g' ← g.replaceTargetEq t' pf
  replaceMainGoal [g']
  return true

def unfoldStep (entries : Array UnfoldEntry) : TacticM Bool := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let (fn, args) := goalType.getAppFnArgs
  unless fn == ``HProp.himpl && args.size == 3 do return false
  let allFns := entries.map (·.headFn)
  let lItems := Sep.Xsimpl.parseHstar args[1]!
  let rItems := Sep.Xsimpl.parseHstar args[2]!
  if (← horStuck entries lItems rItems) || (← horStuck entries rItems lItems) then return false
  let items := lItems ++ rItems
  let some headFn := items.findSome? (fun item =>
      item.getAppFn.constName?.filter (allFns.contains ·)) | return false
  let (bIsHor, bSig) ← bodySig entries headFn
  if bIsHor then
    let inL := lItems.any (fun e => e.getAppFn.constName? == some headFn)
    let x? := items.find? (fun e => e.getAppFn.constName? == some headFn)
    match x? with
    | some x =>
        let other := if inL then rItems else lItems
        unless other.contains x do
          unless ← other.anyM (fun r => liftM (horPartner entries bSig r)) do return false
    | none => pure ()
  if (← unfoldBudget.get) == 0 then return false
  if ← pastGlobal then return false
  let foldLemmas := entries.filterMap fun e =>
    if e.headFn == headFn then some e.lemmaName else none
  for n in foldLemmas do
    let ok ← rwConst n
    if ok then
      unfoldBudget.modify (· - 1)
      unless ← exNormTarget do
        let _ ← simpOnlyTarget normLemmas
      return true
  return false

elab "xsearch_unfold_step" : tactic => withMainContext do
  unless ← unfoldStep (xsearchUnfoldExt.getState (← getEnv)) do
    throwError "xsearch_unfold_step: no registered predicate atom in goal"

partial def distrSafe (e : Expr) : Bool :=
  if e.isAppOfArity ``HProp.hstar 3 || e.isAppOfArity ``hdisj 3 then
    distrSafe e.appFn!.appArg! && distrSafe e.appArg!
  else if e.isAppOfArity ``HProp.hexists 3 then
    match e.appArg! with
    | .lam _ _ b _ => distrSafe b
    | _ => false
  else if e.isAppOfArity ``HProp.hpure 2 then
    (e.appArg!.find? (fun s => s.isAppOfArity ``HProp.hstar 3 || s.isAppOfArity ``hdisj 3
        || s.isAppOfArity ``HProp.hexists 3)).isNone
  else
    (e.find? (fun s =>
      s.isAppOfArity ``HProp.hstar 3 || s.isAppOfArity ``hdisj 3
        || s.isAppOfArity ``HProp.hexists 3 || s.isLambda || s.isMData || s.isLet
        || s.isProj || s.isAppOfArity ``Iff 2 || s.isHeadBetaTarget
        || (s.isAppOfArity ``Eq 3 && s.appFn!.appArg! == s.appArg!))).isNone

def distrNative (g : MVarId) : TacticM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  if t.isAppOfArity ``hasLoc 3 then
    let H := t.appArg!
    unless distrSafe H do return false
    let c : DistrCtx := { inst := t.appFn!.appFn!.appArg!,
                          hty := mkApp (mkConst ``HProp) t.appFn!.appFn!.appArg! }
    let some (H', pH) ← (try some <$> c.norm H catch _ => pure none) | return false
    let some pH := pH | return true
    let g' ← g.replaceTargetEq (mkApp t.appFn! H') (← mkCongrArg t.appFn! pH)
    replaceMainGoal [g']
    return true
  unless t.isAppOfArity ``HProp.himpl 3 do return false
  let inst := t.appFn!.appFn!.appArg!
  let L := t.appFn!.appArg!
  let R := t.appArg!
  unless distrSafe L && distrSafe R do return false
  let c : DistrCtx := { inst, hty := mkApp (mkConst ``HProp) inst }
  let some (L', pL) ← (try some <$> c.norm L catch _ => pure none) | return false
  let some (R', pR) ← (try some <$> c.norm R catch _ => pure none) | return false
  if pL.isNone && pR.isNone then return true
  let t' := mkApp3 (mkConst ``HProp.himpl) inst L' R'
  let fty := mkForall `x .default c.hty (mkSort Level.zero)
  let f := mkApp (mkConst ``HProp.himpl) inst
  let h1 := mkAppN (mkConst ``congrArg [1, 1]) #[c.hty, fty, L, L', f, pL.getD (c.refl L)]
  let pf := mkAppN (mkConst ``congr [1, 1])
    #[c.hty, mkSort Level.zero, mkApp f L, mkApp f L', R, R', h1, pR.getD (c.refl R)]
  let g' ← g.replaceTargetEq t' pf
  replaceMainGoal [g']
  return true

def distrCore : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  if hasDisjExpr t then
    let g ←
      if (t.find? (fun s => isHorConst s && s.getAppNumArgs ≥ 2)).isSome then
        (g.change (replaceHor t))
      else pure g
    replaceMainGoal [g]
    if (t.find? distrRedex).isNone then return
    let lems := #[``hdisj_star_l, ``hdisj_star_r, ``hdisj_hexists, ``HProp.hstar_assoc]
    let native ← distrNative g
    unless native do
      let _ ← simpOnlyTarget lems

elab "xsearch_distr" : tactic => distrCore

def entailHead? (t : Expr) : Option (Expr × Expr) :=
  match t.getAppFnArgs with
  | (``HProp.himpl, #[_, l, r]) => some (l, r)
  | (``SepLogic.Entails, #[_, _, l, r]) => some (l, r)
  | _ => none

def isDisj (e : Expr) : Bool :=
  e.getAppFn.constName? == some ``hdisj && e.getAppNumArgs ≥ 2

partial def collectOccs (heads : Array Name) (e : Expr) (acc : Array Expr) :
    Array Expr :=
  let acc :=
    match e.getAppFn.constName? with
    | some n => if heads.contains n && !acc.any (· == e) then acc.push e else acc
    | none => acc
  match e with
  | .app f a => collectOccs heads a (collectOccs heads f acc)
  | .lam _ t b _ => collectOccs heads b (collectOccs heads t acc)
  | .forallE _ t b _ => collectOccs heads b (collectOccs heads t acc)
  | .mdata _ b => collectOccs heads b acc
  | _ => acc

def eqProofFor (lemName : Name) (occ : Expr) : MetaM (Option Expr) := do
  let info ← getConstInfo lemName
  let lvls ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let c := mkConst lemName lvls
  let (args, _, ty) ← forallMetaTelescope (← inferType c)
  match ty.eq? with
  | some (_, lhs, _) =>
      if ← isDefEq lhs occ then return some (mkAppN c args) else return none
  | none => return none

def rewriteOcc (entries : Array UnfoldEntry) (occ : Expr) : TacticM Unit :=
  withMainContext do
    let some hd := occ.getAppFn.constName? | throwError "xsearch: bad occurrence"
    for e in entries do
      if e.headFn == hd then
        match ← eqProofFor e.lemmaName occ with
        | some pf =>
            let g ← getMainGoal
            let r ← g.rewrite (← g.getType) pf
            let g' ← g.replaceTargetEq r.eNew r.eqProof
            replaceMainGoal (g' :: r.mvarIds)
            evalTactic (← `(tactic| xsearch_distr))
            return
        | none => pure ()
    throwError "xsearch: no unfold lemma applies"

def contraClose (g : MVarId) : MetaM Bool := g.withContext do
  let gt ← instantiateMVars (← g.getType)
  if gt.hasExprMVar then return false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    match ty.getAppFnArgs with
    | (``Ne, #[_, a, b]) =>
        if a == b then
          let pf ← mkAppOptM ``absurd
            #[some (← mkAppM ``Eq #[a, b]), some gt, some (← mkEqRefl a),
              some d.toExpr]
          g.assign pf
          return true
    | (``False, _) =>
        g.assign (← mkAppOptM ``False.elim #[some gt, some d.toExpr])
        return true
    | _ => pure ()
  return false

syntax "xsearch_omega" : tactic

elab "xsearch_pure" : tactic => do
  let gs ← getUnsolvedGoals
  let mut acc : List MVarId := []
  for g in gs do
    if ← g.isAssigned then continue
    let t ← instantiateMVars (← g.getType)
    if ← (try contraClose g catch _ => pure false) then continue
    if (entailHead? t).isSome || (← pastGlobal) then
      acc := acc ++ [g]
    else
      setGoals [g]
      let _ ← tryTactic (evalTactic (← `(tactic|
        first | rfl | assumption | trivial
              | (apply Ne.symm; assumption)
              | xsearch_omega)))
      acc := acc ++ (← getUnsolvedGoals)
  setGoals acc

def cellGroup? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``HProp.hsingle, args) =>
      if args.size ≥ 2 then some (args[args.size-2]!, args[args.size-1]!) else none
  | (``HProp.hstar, _) =>
      let items := Sep.Xsimpl.parseHstar e
      let isCell := fun (i : Expr) => i.getAppFn.constName? == some ``HProp.hsingle
      let isPure := fun (i : Expr) => i.getAppFn.constName? == some ``HProp.hpure
      if items.any isPure && items.all (fun i => isCell i || isPure i) then
        match items.find? isCell with
        | some c =>
            let args := c.getAppArgs
            if args.size ≥ 2 then some (args[args.size-2]!, args[args.size-1]!)
            else none
        | none => none
      else none
  | _ => none

def atomHead? (e : Expr) : Option Expr :=
  (cellGroup? e).map (·.1)

partial def ptoLocsOf (e : Expr) (acc : Array Expr) : Array Expr :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) => ptoLocsOf b (ptoLocsOf a acc)
  | (``HProp.hsingle, args) =>
      if args.size < 2 then acc else
      let l := args[args.size-2]!
      if acc.any (· == l) then acc else acc.push l
  | _ => acc

def predArg0? (heads : Array Name) (e : Expr) : Option Expr :=
  match e.getAppFn.constName? with
  | some n => if heads.contains n then e.getAppArgs.back? else none
  | none => none

partial def branchScore (heads : Array Name) (lhsAtoms : List Expr) (e : Expr) :
    Int :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) =>
      branchScore heads lhsAtoms a + branchScore heads lhsAtoms b
  | (``HProp.hexists, args) =>
      match args.back? with
      | some (.lam _ _ b _) => branchScore heads lhsAtoms b
      | _ => 0
  | (``HProp.hsingle, args) =>
      if args.size < 2 then 0 else
      let a := args[args.size-2]!
      if lhsAtoms.any (fun l => atomHead? l == some a) then 3
      else if lhsAtoms.any (fun l => predArg0? heads l == some a) then 1
      else -4
  | (``HProp.hpure, #[_, p]) =>
      match p.getAppFnArgs with
      | (``Eq, #[_, a, b]) => if a == b then 2 else -1
      | (``Ne, #[_, a, b]) => if a == b then -4 else 0
      | _ => 0
  | _ => 0

def factsCore : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  match t.getAppFnArgs with
  | (``HProp.himpl, #[inst, lhs, rhs]) =>
    if t.hasExprMVar then return ()
    let locs := ptoLocsOf lhs #[]
    if locs.size > 32 then return ()
    let top := wgCells lhs
    let ps := locs.map fun l => (top.find? (·.1 == l)).map (·.2)
    let mut facts : Array (Name × Expr × Expr × Expr × Expr) := #[]
    for i in [0 : locs.size] do
      for j in [i+1 : locs.size] do
        if ← pastGlobal then break
        let p := locs[i]!
        let q := locs[j]!
        if p == q then continue
        let some P := ps[i]! | continue
        let some Q := ps[j]! | continue
        let some (.app (.app (.app _ i1) a1) v1) := wgLeafAt lhs P | continue
        let some (.app (.app (.app _ i2) a2) v2) := wgLeafAt lhs Q | continue
        match wgPathNe p q lhs (mkApp3 (mkConst ``hasLoc_single) i1 a1 v1)
            (mkApp3 (mkConst ``hasLoc_single) i2 a2 v2) P Q with
        | some npf =>
            facts := facts.push (Name.mkSimple s!"hxne{i}_{j}", p, q, npf, ← mkAppM ``Ne #[p, q])
        | none => pure ()
    if facts.isEmpty then return ()
    let ty ← facts.foldrM (fun f acc => mkArrow f.2.2.2.2 acc) t
    let mv ← mkFreshExprSyntheticOpaqueMVar ty
    let n := facts.size
    let mut body := mkAppN mv ((Array.range n).map (fun i => mkBVar (n - 1 - i)))
    let mut k := n
    while k > 0 do
      k := k - 1
      let (nm, p, q, npf, nt) := facts[k]!
      body := mkAppN (mkConst ``himpl_of_neLocs)
        #[inst, p, q, lhs, rhs, npf, .lam nm nt body .default]
    let pf := body
    goal.assign pf
    let (_, g2) ← mv.mvarId!.introN facts.size (facts.map (·.1)).toList
    replaceMainGoal [g2]
  | _ => pure ()

elab "xsearch_facts" : tactic => withMainContext do
  factsCore

def checkDeadline : TacticM Unit := do
  if ← pastGlobal then
    throwError "xsearch: global budget exhausted"
  if (← vclock) > (← searchDeadline.get) then
    throwError "xsearch: time budget exhausted"
  if (← searchNodes.get) == 0 then
    throwError "xsearch: node budget exhausted"

def withLemCache {κ : Type} [BEq κ] (cache : IO.Ref (Array (κ × Option Expr)))
    (key : κ) (ms : Nat) (clamp : Bool) (k : TacticM Expr) : TacticM (Option Expr) := do
  match (← cache.get).findSome? (fun e => if e.1 == key then some e.2 else none) with
  | some r => return r
  | none =>
  cache.modify (·.push (key, none))
  let st ← saveState
  let saved ← getGoals
  let oldD ← searchDeadline.get
  let now ← vclock
  searchDeadline.set (if clamp then min oldD (now + ms) else now + ms)
  let res ← try (do let v ← k; setGoals saved; pure (some v))
    catch _ => do st.restore; setGoals saved; pure none
  searchDeadline.set oldD
  cache.modify (fun arr => #[(key, res)] ++ arr.filter (fun e => !(e.1 == key)))
  return res

def isLfpConst (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => n.components.getLast? == some `lfp
  | _ => false

def functionalOf? (occ : Expr) : MetaM (Option (Expr × Expr)) := do
  match ← unfoldDefinition? occ with
  | none => return none
  | some e =>
    let e ← whnfCore e
    if isLfpConst e && e.getAppNumArgs ≥ 3 then
      let args := e.getAppArgs
      return some (args[args.size - 2]!, args[args.size - 1]!)
    else return none

elab "xsearch_delta" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  match entailHead? t with
  | some (l, r) =>
      match ← unfoldDefinition? l with
      | some l' =>
          let l' ← whnfCore l'
          let t' ← mkAppM ``HProp.himpl #[l', r]
          replaceMainGoal [← g.change t']
      | none => pure ()
  | none => pure ()

initialize forcedDepth : IO.Ref Nat ← IO.mkRef 0

def starOf (inst : Expr) : List Expr → Expr
  | [] => mkApp (mkConst ``HProp.hempty) inst
  | [a] => a
  | a :: rest => mkApp3 (mkConst ``HProp.hstar) inst a (starOf inst rest)

def mkStarOf (inst : Expr) (l : List Expr) : MetaM Expr := pure (starOf inst l)

partial def permPullPf (inst : Expr) (S : List Expr) (sS : Expr) (k : Nat) :
    Option (Expr × Expr) :=
  match S with
  | [] => none
  | s0 :: S1 =>
    if k == 0 then some (mkApp2 (mkConst ``HProp.himpl_refl) inst sS, sS)
    else
    match S1 with
    | [] => none
    | _ =>
      let hs := mkApp3 (mkConst ``HProp.hstar) inst
      let t0 := S1[k-1]!
      let S1' := S1.eraseIdx (k-1)
      if S1'.isEmpty then some (mkApp3 (mkConst ``perm_comm) inst s0 t0, hs t0 s0)
      else
      let sS1 := sS.appArg!
      match permPullPf inst S1 sS1 (k-1) with
      | none => none
      | some (p1, tS1) =>
        let R := tS1.appArg!
        let mid := hs s0 tS1
        let tgt := hs t0 (hs s0 R)
        let fr := mkAppN (mkConst ``frame_r_of) #[inst, s0, sS1, tS1, p1]
        let sw := mkAppN (mkConst ``perm_swap) #[inst, s0, t0, R]
        some (mkAppN (mkConst ``HProp.himpl_trans) #[inst, sS, mid, tgt, fr, sw], tgt)

partial def permListPfS (inst : Expr) (S : List Expr) (sS : Expr) (T : List Expr) (sT : Expr) :
    Option Expr :=
  if S == T && sS == sT then some (mkApp2 (mkConst ``HProp.himpl_refl) inst sS) else
  match T with
  | [] => if S.isEmpty then some (mkApp2 (mkConst ``HProp.himpl_refl) inst sS) else none
  | t0 :: T' =>
    match S.findIdx? (· == t0) with
    | none => none
    | some k =>
    let S' := S.eraseIdx k
    if T'.isEmpty then
      if S'.isEmpty then some (mkApp2 (mkConst ``HProp.himpl_refl) inst t0) else none
    else if S'.isEmpty then none
    else
    match permPullPf inst S sS k with
    | none => none
    | some (pull, tP) =>
      let sS' := tP.appArg!
      let sT' := sT.appArg!
      match permListPfS inst S' sS' T' sT' with
      | none => none
      | some rest =>
        let fr := mkAppN (mkConst ``frame_r_of) #[inst, t0, sS', sT', rest]
        some (mkAppN (mkConst ``HProp.himpl_trans) #[inst, sS, tP, sT, pull, fr])

partial def rnFlat (e : Expr) : Option (List Expr) :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) =>
    if a.isAppOf ``HProp.hstar || a.isAppOf ``HProp.hempty then none
    else (rnFlat b).map (a :: ·)
  | (``HProp.hempty, _) => none
  | _ => some [e]

partial def flatEq (e : Expr) : MetaM (List Expr × Expr) := do
  if e.isAppOfArity ``HProp.hstar 3 then
    if let some L := rnFlat e then
      return (L, mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``HProp) e.getAppArgs[0]!) e)
  match e.getAppFnArgs with
  | (``HProp.hstar, #[inst, a, b]) =>
    let hty := mkApp (mkConst ``HProp) inst
    let hs := mkApp3 (mkConst ``HProp.hstar) inst
    let trans := fun (x y z p q : Expr) =>
      mkAppN (mkConst ``Eq.trans [1]) #[hty, x, y, z, p, q]
    match a.getAppFnArgs with
    | (``HProp.hstar, #[_, a1, a2]) =>
        let e' := hs a1 (hs a2 b)
        let (L, p) ← flatEq e'
        return (L, trans e e' (starOf inst L)
          (mkAppN (mkConst ``HProp.hstar_assoc) #[inst, a1, a2, b]) p)
    | (``HProp.hempty, _) =>
        let (L, p) ← flatEq b
        return (L, trans e b (starOf inst L)
          (mkApp2 (mkConst ``HProp.hstar_hempty_l) inst b) p)
    | _ =>
        let (Lb, pb) ← flatEq b
        let mid := starOf inst Lb
        let pc := mkAppN (mkConst ``congrArg [1, 1])
          #[hty, hty, b, mid, mkApp2 (mkConst ``HProp.hstar) inst a, pb]
        if Lb.isEmpty then
          return ([a], trans e (hs a mid) a pc
            (mkApp2 (mkConst ``HProp.hstar_hempty_r) inst a))
        else
          return (a :: Lb, pc)
  | (``HProp.hempty, #[inst]) =>
      return ([], mkApp2 (mkConst ``Eq.refl [1]) (mkApp (mkConst ``HProp) inst) e)
  | _ => return ([e], ← mkEqRefl e)

def provePerm (A B : Expr) : MetaM (Option Expr) := do
  let A ← instantiateMVars A
  let B ← instantiateMVars B
  let inst := (← whnfR (← inferType A)).appArg!
  let (S, ps) ← flatEq A
  let (T, pt) ← flatEq B
  unless S.length == T.length do return none
  let sS := starOf inst S
  let sT := starOf inst T
  let some pm := permListPfS inst S sS T sT | return none
  let hty := mkApp (mkConst ``HProp) inst
  let oe := fun (x y h : Expr) => mkAppN (mkConst ``himpl_of_eq) #[inst, x, y, h]
  let tr := fun (x y z p q : Expr) => mkAppN (mkConst ``HProp.himpl_trans) #[inst, x, y, z, p, q]
  let pa := if sS == A then pm else tr A sS sT (oe A sS ps) pm
  if sT == B then return some pa
  return some (tr A sT B pa (oe sT B (mkAppN (mkConst ``Eq.symm [1]) #[hty, B, sT, pt])))

def wandParts? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``HProp.hwand, args) =>
      if args.size == 3 then some (args[1]!, args[2]!) else none
  | _ => none

def wandAlt (lhs rhs : Expr) (L : List Expr) (i : Nat) : TacticM Unit :=
  withMainContext do
    let W := L[i]!
    let some (A, B) := wandParts? W | throwError "wand: not a wand"
    let g ← getMainGoal
    let gt ← instantiateMVars (← g.getType)
    let inst := gt.getAppArgs[0]!
    let D ← mkStarOf inst (L.eraseIdx i)
    match ← provePerm lhs (← mkAppM ``HProp.hstar #[W, D]) with
    | none => throwError "wand: perm"
    | some h1 =>
      let mv1 ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[D, A])
      let mv2 ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[B, rhs])
      let full ← mkAppM ``HProp.himpl_trans
        #[h1, ← mkAppM ``wand_use #[mv1, mv2]]
      unless ← isDefEq (← inferType full) gt do throwError "wand: mismatch"
      g.assign full
      replaceMainGoal [mv1.mvarId!, mv2.mvarId!]

def wandAltS (lhs rhs : Expr) (L : List Expr) (i : Nat) (ks : List Nat) :
    TacticM Unit := withMainContext do
  let W := L[i]!
  let some (A, B) := wandParts? W | throwError "wands: not a wand"
  let g ← getMainGoal
  let gt ← instantiateMVars (← g.getType)
  let inst := gt.getAppArgs[0]!
  let E ← mkStarOf inst (ks.map (fun m => L[m]!))
  let F ← mkStarOf inst ((List.range L.length).filterMap
    (fun m => if m == i || ks.contains m then none else some L[m]!))
  match ← provePerm lhs (← mkAppM ``HProp.hstar
      #[W, ← mkAppM ``HProp.hstar #[E, F]]) with
  | none => throwError "wands: perm"
  | some h1 =>
    let mv1 ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[E, A])
    let mv2 ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl
      #[← mkAppM ``HProp.hstar #[B, F], rhs])
    let full ← mkAppM ``HProp.himpl_trans
      #[h1, ← mkAppM ``wand_use2 #[mv1, mv2]]
    unless ← isDefEq (← inferType full) gt do throwError "wands: mismatch"
    g.assign full
    replaceMainGoal [mv1.mvarId!, mv2.mvarId!]

partial def stripInj (e : Expr) : Expr :=
  match e.getAppFnArgs with
  | (``Sum.inl, args) => if args.size == 3 then stripInj args[2]! else e
  | (``Sum.inr, args) => if args.size == 3 then stripInj args[2]! else e
  | _ => e

partial def splitVar (g : MVarId) (fv : FVarId) : MetaM (List MVarId) := do
  let ty ← g.withContext do whnf (← fv.getType)
  match ty.getAppFn.constName? with
  | some n =>
      if n == ``Sum || n == ``Prod then
        let subs ← g.cases fv
        let mut acc : List MVarId := []
        for sub in subs do
          let mut gs := [sub.mvarId]
          for f in sub.fields do
            match f with
            | .fvar fid =>
                let mut gs2 : List MVarId := []
                for gg in gs do
                  gs2 := gs2 ++ (← splitVar gg fid)
                gs := gs2
            | _ => pure ()
          acc := acc ++ gs
        return acc
      else return [g]
  | none => return [g]

partial def defNorm (e : Expr) : Expr :=
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs.map defNorm
    if fn.isLambda then defNorm (fn.betaRev args.reverse) else
    let fn := defNorm fn
    if fn.isLambda then defNorm (fn.betaRev args.reverse) else
    if fn.isConstOf ``Sum.elim && args.size ≥ 6 then
      let x := args[5]!
      let rest := args.extract 6 args.size
      if x.isAppOfArity ``Sum.inl 3 then defNorm (mkAppN args[3]! (#[x.appArg!] ++ rest))
      else if x.isAppOfArity ``Sum.inr 3 then defNorm (mkAppN args[4]! (#[x.appArg!] ++ rest))
      else mkAppN fn args
    else if (fn.isConstOf ``Prod.fst || fn.isConstOf ``Prod.snd) && args.size ≥ 3
        && args[2]!.isAppOfArity ``Prod.mk 4 then
      let pr := args[2]!.getAppArgs
      defNorm (mkAppN (if fn.isConstOf ``Prod.fst then pr[2]! else pr[3]!) (args.extract 3 args.size))
    else mkAppN fn args
  | .lam n t b bi =>
    let b' := defNorm b
    if b'.isApp && b'.appArg! == .bvar 0 && !b'.appFn!.hasLooseBVar 0 then
      b'.appFn!.lowerLooseBVars 1 1
    else .lam n (defNorm t) b' bi
  | .forallE n t b bi => .forallE n (defNorm t) (defNorm b) bi
  | _ => e

partial def defSafe (e : Expr) : Bool :=
  match e with
  | .app f a => defSafe f && defSafe a
  | .lam _ t b _ | .forallE _ t b _ => defSafe t && defSafe b
  | .const .. | .fvar _ | .lit _ | .sort _ | .bvar _ => true
  | _ => false

namespace DistrCtx

partial def empNorm (c : DistrCtx) (e : Expr) : MetaM (Expr × Option Expr) := do
  if e.isAppOfArity ``HProp.hpure 2 then
    let (P', pP) ← normProp e.appArg!
    match pP with
    | none => return (e, none)
    | some pP =>
      let f := mkApp (mkConst ``HProp.hpure) c.inst
      return (mkApp f P', some (mkAppN (mkConst ``congrArg [1, 1])
        #[mkSort Level.zero, c.hty, e.appArg!, P', f, pP]))
  if e.isAppOfArity ``HProp.hstar 3 then
    let f := e.appFn!.appFn!
    let a := e.appFn!.appArg!
    let b := e.appArg!
    let (a', pa) ← c.empNorm a
    let (b', pb) ← c.empNorm b
    let e1 := mkApp2 f a' b'
    let p1 := c.cong2 f a a' b b' pa pb
    if a'.isAppOfArity ``HProp.hempty 1 then
      return (b', c.trans e e1 b' p1 (some (mkApp2 (mkConst ``HProp.hstar_hempty_l) c.inst b')))
    if b'.isAppOfArity ``HProp.hempty 1 then
      return (a', c.trans e e1 a' p1 (some (mkApp2 (mkConst ``HProp.hstar_hempty_r) c.inst a')))
    return (e1, p1)
  if e.isAppOfArity ``HProp.hexists 3 then
    let .lam n ty body bi := e.appArg! | throwError "empnorm: exists"
    return ← withLocalDecl n bi ty fun x => do
      let (b', pb) ← c.empNorm (body.instantiate1 x)
      match pb with
      | none => return (e, none)
      | some pb =>
        let fe ← mkFunExt (← mkLambdaFVars #[x] pb)
        return (mkApp e.appFn! (← mkLambdaFVars #[x] b'), some (← mkCongrArg e.appFn! fe))
  if e.isApp then
    let fn := e.getAppFn
    let args := e.getAppArgs
    let mut cur := args
    let mut pf : Option Expr := none
    for i in [0 : args.size] do
      let (a', pa) ← c.empNorm args[i]!
      let some pa := pa | continue
      let f ← withLocalDeclD `y (← inferType args[i]!) fun y =>
        mkLambdaFVars #[y] (mkAppN fn (cur.set! i y))
      let step ← mkCongrArg f pa
      pf := some (← match pf with
        | none => pure step
        | some p0 => mkEqTrans p0 step)
      cur := cur.set! i a'
    return (mkAppN fn cur, pf)
  if e.isLambda || e.isForall then throwError "empnorm: binder"
  return (e, none)

end DistrCtx

def indNormGoal (g : MVarId) : MetaM (Option MVarId) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  unless t.isAppOfArity ``HProp.himpl 3 do return none
  unless defSafe t do return none
  let t1 := defNorm t
  unless t1.isAppOfArity ``HProp.himpl 3 do return none
  let inst := t1.appFn!.appFn!.appArg!
  let L := t1.appFn!.appArg!
  let R := t1.appArg!
  let c : DistrCtx := { inst, hty := mkApp (mkConst ``HProp) inst }
  let some (L', pL) ← (try some <$> c.empNorm L catch _ => pure none) | return none
  let some (R', pR) ← (try some <$> c.empNorm R catch _ => pure none) | return none
  let g1 ← if t1 == t then pure g else g.replaceTargetDefEq t1
  if pL.isNone && pR.isNone then return some g1
  let t' := mkApp3 (mkConst ``HProp.himpl) inst L' R'
  let fty := mkForall `x .default c.hty (mkSort Level.zero)
  let f := mkApp (mkConst ``HProp.himpl) inst
  let h1 := mkAppN (mkConst ``congrArg [1, 1]) #[c.hty, fty, L, L', f, pL.getD (c.refl L)]
  let pf := mkAppN (mkConst ``congr [1, 1])
    #[c.hty, mkSort Level.zero, mkApp f L, mkApp f L', R, R', h1, pR.getD (c.refl R)]
  return some (← g1.replaceTargetEq t' pf)

def indSetup (F X aty : Expr) (post : Nat := 0) (T : Option Expr := none) : TacticM Expr := do
  let hXType ← withLocalDeclD `indb aty fun b => do
    mkForallFVars #[b] (← mkAppM ``HProp.himpl #[mkApp2 F X b, mkApp (T.getD X) b])
  let hXMv ← mkFreshExprSyntheticOpaqueMVar hXType
  let (fv, g1) ← hXMv.mvarId!.intro `indb
  setGoals (← splitVar g1 fv)
  evalTactic (← `(tactic| all_goals (try xsearch_delta)))
  let mut out : List MVarId := []
  for g in ← getGoals do
    if ← g.isAssigned then continue
    match ← (try indNormGoal g catch _ => pure none) with
    | some g' => out := out ++ [g']
    | none =>
      setGoals [g]
      evalTactic (← `(tactic| try dsimp only))
      allGoalsTry (do let _ ← simpOnlyTarget #[``Sum.elim_inl,
        ``Sum.elim_inr, ``HProp.hstar_hempty_l, ``HProp.hstar_hempty_r])
      out := out ++ (← getGoals)
  setGoals out
  if post ≥ 2 then evalTactic (← `(tactic| all_goals apply HProp.himpl_hwand_r))
  if post == 1 || post == 2 then
    evalTactic (← `(tactic| (all_goals (try xsearch_distr)
                             all_goals (try apply Sep.Xsearch.hdisj_elim))))
  return hXMv

partial def projMap (ta t : Expr) : MetaM (Array (Expr × Expr)) := do
  match ta.getAppFnArgs with
  | (``Prod.mk, args) =>
      if args.size == 4 then
        let l ← projMap args[2]! (← mkAppM ``Prod.fst #[t])
        let r ← projMap args[3]! (← mkAppM ``Prod.snd #[t])
        return l ++ r
      else return #[(ta, t)]
  | _ => return #[(ta, t)]

def hasLocLocs : TacticM (Array Expr) := withMainContext do
  let mut acc : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    match (← instantiateMVars d.type).getAppFnArgs with
    | (``hasLoc, args) =>
        if args.size ≥ 2 then
          let p := args[args.size-2]!
          if !acc.any (· == p) then acc := acc.push p
    | _ => pure ()
  return acc

partial def deepPtoLocs (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc :=
    match atomHead? e with
    | some l => if acc.any (· == l) then acc else acc.push l
    | none => acc
  match e with
  | .app f a => deepPtoLocs a (deepPtoLocs f acc)
  | .lam _ _ b _ => deepPtoLocs b acc
  | .mdata _ b => deepPtoLocs b acc
  | _ => acc

def ctxLocs (g : MVarId) : MetaM (Array (Expr × Expr × Expr)) := g.withContext do
  let mut acc : Array (Expr × Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    match (← instantiateMVars d.type).getAppFnArgs with
    | (``hasLoc, #[_, l, H]) => acc := acc.push (l, H, d.toExpr)
    | _ => pure ()
  return acc

partial def locOff (e : Expr) : Expr × Nat :=
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      match b.nat? with
      | some k => let (x, n) := locOff a; (x, n + k)
      | none => (e, 0)
  | _ =>
      match e.nat? with
      | some k => (mkNatLit 0, k)
      | none => (e, 0)

def mayEqLoc (a b : Expr) : MetaM Bool := do
  if a == b then return true
  let (x, i) := locOff a
  let (y, j) := locOff b
  if x == y then return i == j
  let atomic : Expr → MetaM Bool := fun z => do
    if z.nat? == some 0 then return true
    match z with
    | .fvar f => return !(← f.getDecl).isLet
    | _ => return false
  return !((← atomic x) && (← atomic y))

def opaqueAtom (e : Expr) : MetaM Bool := do
  match e with
  | .fvar _ => return true
  | _ =>
    match e.getAppFn with
    | .const _ _ => return (← functionalOf? e).isSome
    | _ => return false

partial def mayHasLoc (hy : Array (Expr × Expr × Expr)) (p e : Expr) : MetaM Bool := do
  if e.hasMVar then return true
  for (l, H, _) in hy do
    if H == e && (← mayEqLoc l p) then return true
  match e.getAppFnArgs with
  | (``HProp.hsingle, args) => if args.size == 3 then mayEqLoc args[1]! p else return true
  | (``HProp.hstar, #[_, a, b]) =>
      if a.getAppFn.constName? == some ``HProp.hpure then return true
      if ← mayHasLoc hy p a then return true
      mayHasLoc hy p b
  | (``hpack, #[_, a, b]) =>
      if ← mayHasLoc hy p a then return true
      mayHasLoc hy p b
  | (``hdisj, #[_, a, b]) =>
      if ← mayHasLoc hy p a then mayHasLoc hy p b else return false
  | (``HProp.hempty, _) => return false
  | (``HProp.hpure, _) => return false
  | _ => return !(← opaqueAtom e)

partial def mayNeLocs (hy : Array (Expr × Expr × Expr)) (p q e : Expr) : MetaM Bool := do
  if e.hasMVar then return true
  let split : Option (Expr × Expr) :=
    match e.getAppFnArgs with
    | (``HProp.hstar, #[_, a, b]) => some (a, b)
    | (``hpack, #[_, a, b]) => some (a, b)
    | _ => none
  match split with
  | none =>
    match e.getAppFnArgs with
    | (``HProp.hsingle, _) => return false
    | (``HProp.hempty, _) => return false
    | (``HProp.hpure, _) => return false
    | (``HProp.hexists, _) => return false
    | (``hdisj, _) => return false
    | _ => return !(← opaqueAtom e)
  | some (a, b) =>
    if (← mayHasLoc hy p a) && (← mayHasLoc hy q b) then return true
    if (← mayHasLoc hy q a) && (← mayHasLoc hy p b) then return true
    if ← mayNeLocs hy p q a then return true
    mayNeLocs hy p q b

def tryAddNe (p q : Expr) (nm : Name) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let ne ← mkAppM ``Ne #[p, q]
  let known ← (← getLCtx).anyM fun d => do
    if d.isImplementationDetail then return false
    return (← instantiateMVars d.type) == ne
  if known then return ()
  let hy ← ctxLocs goal
  match entailHead? target with
  | some (lhs, _) =>
      unless ← mayNeLocs hy p q lhs do throwError "ne: impossible"
  | none => pure ()
  let c ← mkConstWithFreshMVarLevels ``himpl_of_neLocs
  let cty ← inferType c
  let (margs, _, concl) ← forallMetaTelescope cty
  let mut names : Array Name := #[]
  let mut it := cty
  while it.isForall do
    names := names.push it.bindingName!
    it := it.bindingBody!
  unless ← isDefEq concl target do throwError "ne: shape"
  match names.findIdx? (· == `p), names.findIdx? (· == `q) with
  | some ip, some iq =>
      unless ← isDefEq margs[ip]! p do throwError "ne: p"
      unless ← isDefEq margs[iq]! q do throwError "ne: q"
  | _, _ => throwError "ne: names"
  match ← goal.apply (← instantiateMVars (mkAppN c margs)) with
  | [g1, g2] =>
      unless ← wgAllocGoal g1 do throwError "ne: open"
      let (_, g3) ← g2.intro nm
      setGoals [g3]
  | _ => throwError "ne: goals"

elab "xsearch_hfacts" : tactic => withMainContext do
  let cs ← hasLocLocs
  if cs.isEmpty then return ()
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let locs :=
    match entailHead? t with
    | some (lhs, _) => deepPtoLocs lhs #[]
    | none => #[]
  for i in [0 : locs.size] do
    for j in [0 : cs.size] do
      if locs[i]! == cs[j]! then continue
      let st ← saveState
      try tryAddNe locs[i]! cs[j]! (Name.mkSimple s!"hxnh{i}_{j}")
      catch _ => st.restore

partial def holdsLift? (inst P atom pf e : Expr) : Option Expr :=
  if e == atom then some pf else
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) =>
      match holdsLift? inst P atom pf a with
      | some h => some (mkAppN (mkConst ``holdsP_star_l) #[inst, P, a, b, h])
      | none =>
        match holdsLift? inst P atom pf b with
        | some h => some (mkAppN (mkConst ``holdsP_star_r) #[inst, P, a, b, h])
        | none => none
  | _ => none

partial def holdsPf? (inst q e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``HProp.hpure, #[_, p]) =>
      if p == q then some (mkAppN (mkConst ``holdsP_pure) #[inst, q]) else none
  | (``HProp.hstar, #[_, a, b]) =>
      match holdsPf? inst q a with
      | some h => some (mkAppN (mkConst ``holdsP_star_l) #[inst, q, a, b, h])
      | none =>
        match holdsPf? inst q b with
        | some h => some (mkAppN (mkConst ``holdsP_star_r) #[inst, q, a, b, h])
        | none => none
  | _ => none

partial def pureProps (e : Expr) (acc : Array Expr) : Array Expr :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) => pureProps b (pureProps a acc)
  | (``HProp.hpure, #[_, q]) => if acc.any (· == q) then acc else acc.push q
  | _ => acc

partial def exPeel (e : Expr) : Expr × Nat := Id.run do
  let mut bd := e
  let mut n := 0
  while bd.getAppFn.constName? == some ``HProp.hexists && n < 12 do
    match bd.getAppArgs.back? with
    | some lam =>
        if lam.isLambda then
          bd := lam.bindingBody!
          n := n + 1
        else break
    | none => break
  return (bd, n)

def bvarDetermined (body : Expr) (i : Nat) : Bool := Id.run do
  let tgt : Expr := .bvar i
  for it in Sep.Xsimpl.parseHstar body do
    match it.getAppFnArgs with
    | (``HProp.hpure, #[_, pr]) =>
        match pr.getAppFnArgs with
        | (``Eq, #[_, a, b]) =>
            if a == tgt && !b.hasLooseBVars then return true
            if b == tgt && !a.hasLooseBVars then return true
        | _ => pure ()
    | _ => pure ()
  return false

def exDetermined (e : Expr) : Bool :=
  let (bd, n) := exPeel e
  n > 0 && bvarDetermined bd (n - 1)

elab "xsearch_trivpure" : tactic => withMainContext do
  for _ in [0 : 64] do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (lhs, rhs) := entailHead? t | return ()
    if t.hasExprMVar then return ()
    let inst := t.getAppArgs[0]!
    let mut found : Option (Expr × Expr) := none
    for q in pureProps lhs (pureProps rhs #[]) do
      if found.isSome then break
      match q.getAppFnArgs with
      | (``Eq, #[_, a, b]) =>
          if a == b then found := some (q, ← mkEqRefl a)
      | (``True, _) => found := some (q, mkConst ``trivial)
      | _ => pure ()
    match found with
    | none => return ()
    | some (q, pf) =>
      let eq ← mkAppOptM ``hpure_true #[some inst, some q, some pf]
      let g ← getMainGoal
      let r ← g.rewrite (← g.getType) eq
      let g' ← g.replaceTargetEq r.eNew r.eqProof
      replaceMainGoal (g' :: r.mvarIds)
      let _ ← simpOnlyTarget #[``HProp.hstar_hempty_l, ``HProp.hstar_hempty_r]

def exwitCore : TacticM Unit := withMainContext do
  for _ in [0 : 12] do
    if ← pastGlobal then return ()
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (_, rhs) := entailHead? t | return ()
    if t.hasExprMVar then return ()
    let isEx := fun (e : Expr) =>
      e.getAppFn.constName? == some ``HProp.hexists
    if isEx rhs then
      let (body, depth) := exPeel rhs
      if depth == 0 then return ()
      let tgt : Expr := .bvar (depth - 1)
      let mut wit : Option Expr := none
      for it in Sep.Xsimpl.parseHstar body do
        if wit.isSome then break
        match it.getAppFnArgs with
        | (``HProp.hpure, #[_, pr]) =>
            match pr.getAppFnArgs with
            | (``Eq, #[_, a, b]) =>
                if a == tgt && !b.hasLooseBVars then wit := some b
                else if b == tgt && !a.hasLooseBVars then wit := some a
            | _ => pure ()
        | _ => pure ()
      let some w := wit | return ()
      let g ← getMainGoal
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``HProp.himpl_hexists_r)
      let mut rem : List MVarId := []
      for gg in gs do
        if ← gg.isAssigned then continue
        let ty ← instantiateMVars (← gg.getType)
        if ← isProp ty then rem := rem ++ [gg]
        else
          unless ← isDefEq (mkMVar gg) w do return ()
      replaceMainGoal rem
      evalTactic (← `(tactic| try beta_reduce))
    else
      let items := Sep.Xsimpl.parseHstar rhs
      unless items.any (fun it => isEx it && exDetermined it) do return ()
      let prog ← tryTactic (evalTactic (← `(tactic| conv_rhs => simp only
        [Sep.Xsearch.hstar_hexists_rr, HProp.hstar_hexists, HProp.hstar_assoc])))
      unless prog do return ()

elab "xsearch_exwit" : tactic => exwitCore

def eqSubstCore : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  match t.getAppFnArgs with
  | (``HProp.himpl, #[inst, lhs, rhs]) =>
    if t.hasExprMVar then return ()
    let mut g := goal
    let mut k := 0
    for q in pureProps lhs #[] do
      unless q.getAppFn.constName? == some ``Eq do continue
      let qa := q.getAppArgs
      unless qa.size == 3 do continue
      if qa[1]! == qa[2]! then continue
      unless qa[1]!.isFVar || qa[2]!.isFVar do continue
      let known ← g.withContext do
        (← getLCtx).anyM fun dcl => do
          if dcl.isImplementationDetail then return false
          return (← instantiateMVars dcl.type) == q
      if known then continue
      let some pf := holdsPf? inst q lhs | continue
      let mv ← g.withContext do mkFreshExprSyntheticOpaqueMVar (← mkArrow q t)
      g.assign (mkAppN (mkConst ``himpl_of_holds) #[inst, q, lhs, rhs, pf, mv])
      let (_, g2) ← mv.mvarId!.intro (Name.mkSimple s!"hxeq{k}")
      k := k + 1
      g := g2
    replaceMainGoal [g]
    if k > 0 then
      evalTactic (← `(tactic| try xsearch_subst))
  | _ => pure ()

elab "xsearch_eqsubst" : tactic => withMainContext do
  eqSubstCore

elab "xsearch_pfacts" : tactic => withMainContext do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  match t.getAppFnArgs with
  | (``HProp.himpl, #[inst, lhs, rhs]) =>
    if t.hasExprMVar then return ()
    let heads := (xsearchUnfoldExt.getState (← getEnv)).map (·.headFn)
    let mut ends : Array Expr := #[]
    for a in Sep.Xsimpl.parseHstar lhs ++ Sep.Xsimpl.parseHstar rhs do
      match a.getAppFn.constName? with
      | some n =>
          if heads.contains n then
            for x in a.getAppArgs do
              if !ends.any (· == x) then ends := ends.push x
      | none => pure ()
    let plocs := ptoLocsOf lhs #[]
    let mut g := goal
    let mut k := 0
    for q in pureProps lhs #[] do
      unless q.getAppFn.constName? == some ``Ne do continue
      let qa := q.getAppArgs
      unless qa.size == 3 do continue
      let a := qa[1]!
      let b := qa[2]!
      let useful :=
        (!plocs.any (· == a) && ends.any (· == a))
          || (!plocs.any (· == b) && ends.any (· == b))
      unless useful do continue
      let known ← g.withContext do
        (← getLCtx).anyM fun dcl => do
          if dcl.isImplementationDetail then return false
          return (← instantiateMVars dcl.type) == q
      if known then continue
      let some pf := holdsPf? inst q lhs | continue
      let mv ← g.withContext do mkFreshExprSyntheticOpaqueMVar (← mkArrow q t)
      g.assign (mkAppN (mkConst ``himpl_of_holds) #[inst, q, lhs, rhs, pf, mv])
      let (_, g2) ← mv.mvarId!.intro (Name.mkSimple s!"hxpf{k}")
      k := k + 1
      g := g2
    replaceMainGoal [g]
  | _ => pure ()

partial def pureConjs (p : Expr) (acc : Array Expr) : Array Expr :=
  match p.getAppFnArgs with
  | (``And, #[a, b]) => pureConjs b (pureConjs a acc)
  | _ => acc.push p

partial def peelExG {α : Type} (e : Expr) (acc : Array Expr)
    (k : Array Expr → Expr → MetaM α) : MetaM α := do
  match e.getAppFnArgs with
  | (``HProp.hexists, args) =>
      match args.back? with
      | some lam =>
        if lam.isLambda then
          lambdaTelescope lam fun vs bd =>
            if vs.size == 1 then peelExG bd (acc ++ vs) k else k acc e
        else k acc e
      | none => k acc e
  | _ => k acc e

partial def flatStar (e : Expr) (acc : Array Expr) : Array Expr :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) => flatStar b (flatStar a acc)
  | (``HProp.hempty, _) => acc
  | _ => acc.push e

initialize recPredCache : IO.Ref (Array (Name × Bool)) ← IO.mkRef #[]

def directRefs (entries : Array UnfoldEntry) (heads : Array Name) (p : Name) :
    MetaM (Array Name) := do
  let mut acc : Array Name := #[]
  for e in entries do
    if e.headFn != p then continue
    let ty := (← getConstInfo e.lemmaName).type
    let rs ← forallTelescopeReducing ty fun _ concl => do
      match concl.eq? with
      | some (_, _, body) =>
          pure ((collectOccs heads body #[]).filterMap (·.getAppFn.constName?))
      | none => pure heads
    for r in rs do
      if !acc.contains r then acc := acc.push r
  return acc

def isRecPred (p : Name) : MetaM Bool := do
  match (← recPredCache.get).findSome? (fun e =>
      if e.1 == p then some e.2 else none) with
  | some b => return b
  | none =>
    let entries := xsearchUnfoldExt.getState (← getEnv)
    let heads := entries.map (·.headFn)
    let mut seen : Array Name := #[]
    let mut work ← directRefs entries heads p
    let mut r := false
    for _ in [0 : heads.size + 1] do
      match work.back? with
      | none => break
      | some q =>
        work := work.pop
        if q == p then
          r := true
          break
        if seen.contains q then continue
        seen := seen.push q
        for n in ← directRefs entries heads q do
          if !seen.contains n then work := work.push n
    recPredCache.modify (·.push (p, r))
    return r

initialize flatPredCache : IO.Ref (Array (Name × Bool)) ← IO.mkRef #[]

def isFlatPred (p : Name) : MetaM Bool := do
  match (← flatPredCache.get).findSome? (fun e =>
      if e.1 == p then some e.2 else none) with
  | some b => return b
  | none =>
    let entries := xsearchUnfoldExt.getState (← getEnv)
    let mut r := false
    if !(← isRecPred p) then
      for e in entries do
        if e.headFn != p then continue
        let ty := (← getConstInfo e.lemmaName).type
        let v ← forallTelescopeReducing ty fun _ concl => do
          match concl.eq? with
          | some (_, _, body) => pure (!isHorConst body)
          | none => pure false
        r := r || v
    flatPredCache.modify (·.push (p, r))
    return r

initialize cmCounter : IO.Ref Nat ← IO.mkRef 0
initialize cmSteps : IO.Ref Nat ← IO.mkRef 0

abbrev CmHeap := Array (Int × Int)

structure CmSt where
  cells : Array (Expr × Expr) := #[]
  pures : Array Expr := #[]
  deriving Inhabited

def cmFresh : IO Expr := do
  let n ← cmCounter.modifyGet (fun n => (n, n + 1))
  return .fvar ⟨Name.mkNum `_xcm n⟩

def cmTable : MetaM (Array (Name × Nat × Expr)) := do
  let mut out := #[]
  for e in xsearchUnfoldExt.getState (← getEnv) do
    if out.any (·.1 == e.headFn) then continue
    let ty := (← getConstInfo e.lemmaName).type
    let mut b := ty
    let mut n := 0
    while b.isForall do
      b := b.bindingBody!
      n := n + 1
    match b.eq? with
    | some (_, l, r) =>
        let args := l.getAppArgs
        if l.getAppFn.constName? == some e.headFn && args.size == n &&
            (List.range n).all (fun i => args[i]! == .bvar (n - 1 - i)) then
          out := out.push (e.headFn, n, r)
    | none => pure ()
  return out

def cmUnfold (tbl : Array (Name × Nat × Expr)) (e : Expr) : Option Expr :=
  match e.getAppFn.constName? with
  | some nm =>
      match tbl.find? (·.1 == nm) with
      | some (_, n, r) =>
          let args := e.getAppArgs
          if args.size == n then some (r.instantiateRev args) else none
      | none => none
  | none => none

partial def cmVal (env : Std.HashMap FVarId Int) (e : Expr) : Option Int :=
  match e with
  | .fvar f => env[f]?
  | .lit (.natVal n) => some n
  | .mdata _ b => cmVal env b
  | _ =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) => cmVal env n
    | (``Nat.cast, #[_, _, a]) => cmVal env a
    | (``NatCast.natCast, #[_, _, a]) => cmVal env a
    | (``Int.ofNat, #[a]) => cmVal env a
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
        match cmVal env a, cmVal env b with
        | some x, some y => some (x + y)
        | _, _ => none
    | (``HSub.hSub, #[t, _, _, _, a, b]) =>
        match cmVal env a, cmVal env b with
        | some x, some y =>
            if t.isConstOf ``Nat then some (if x ≥ y then x - y else 0) else some (x - y)
        | _, _ => none
    | (``Neg.neg, #[t, _, a]) =>
        if t.isConstOf ``Int then (cmVal env a).map (fun x => -x) else none
    | _ => none

partial def cmHasPred (tbl : Array (Name × Nat × Expr)) (e : Expr) : Bool :=
  match e.getAppFn.constName? with
  | some nm => tbl.any (·.1 == nm) ||
      (e.isApp && e.getAppArgs.any (cmHasPred tbl))
  | none =>
    match e with
    | .lam _ _ b _ => cmHasPred tbl b
    | .mdata _ b => cmHasPred tbl b
    | .app f a => cmHasPred tbl f || cmHasPred tbl a
    | _ => false

def cmOr (e : Expr) : Bool := (isHorConst e || e.isAppOf ``hdisj) && e.getAppNumArgs ≥ 2

partial def cmDisjs (e : Expr) : Array Expr :=
  if cmOr e then
    let xs := e.getAppArgs
    cmDisjs xs[xs.size - 2]! ++ cmDisjs xs[xs.size - 1]!
  else #[e]

partial def cmGen (tbl : Array (Name × Nat × Expr)) (lv depth : Nat) (e : Expr)
    (sts : Array CmSt) : MetaM (Option (Array CmSt)) := do
  if sts.isEmpty then return some sts
  if depth > 40 then return none
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) =>
      match ← cmGen tbl lv depth a sts with
      | some s1 => cmGen tbl lv depth b s1
      | none => return none
  | (``HProp.hempty, #[_]) => return some sts
  | (``HProp.hpure, #[_, p]) => return some (sts.map fun s => { s with pures := s.pures.push p })
  | (``HProp.hsingle, #[_, a, v]) =>
      return some (sts.map fun s => { s with cells := s.cells.push (a, v) })
  | (``HProp.hexists, #[_, _, j]) =>
      match j with
      | .lam _ _ b _ => cmGen tbl lv depth (b.instantiate1 (← cmFresh)) sts
      | _ => return none
  | _ =>
    if cmOr e then
      let mut out := #[]
      for d in cmDisjs e do
        match ← cmGen tbl lv (depth + 1) d sts with
        | some s => out := out ++ s
        | none => return none
      return some (out.extract 0 48)
    match cmUnfold tbl e with
    | none => return none
    | some body =>
      let ds := cmDisjs body
      let rec_ := ds.filter (cmHasPred tbl)
      let base0 := ds.filter (fun d => !cmHasPred tbl d)
      let self := e.getAppFn.constName?
      let base := if base0.isEmpty then
          ds.filter (fun d => (d.find? (fun s => s.getAppFn.constName? == self && self.isSome)).isNone)
        else base0
      let chosen := if lv == 0 then base else if rec_.isEmpty then base else rec_
      if chosen.isEmpty then return none
      let mut out := #[]
      for d in chosen do
        match ← cmGen tbl (lv - 1) (depth + 1) d sts with
        | some s => out := out ++ s
        | none => return none
      return some (out.extract 0 48)

partial def cmFVars (e : Expr) (acc : Array FVarId) : Array FVarId :=
  match e with
  | .fvar f => if acc.contains f then acc else acc.push f
  | .app f a => cmFVars a (cmFVars f acc)
  | .mdata _ b => cmFVars b acc
  | .lam _ t b _ => cmFVars b (cmFVars t acc)
  | .forallE _ t b _ => cmFVars b (cmFVars t acc)
  | _ => acc

partial def cmAtom (e : Expr) : Option (Sum FVarId Int) :=
  match e with
  | .fvar f => some (.inl f)
  | .mdata _ b => cmAtom b
  | _ =>
    match e.getAppFnArgs with
    | (``Nat.cast, #[_, _, a]) => cmAtom a
    | (``NatCast.natCast, #[_, _, a]) => cmAtom a
    | (``Int.ofNat, #[a]) => cmAtom a
    | _ => (cmVal {} e).map .inr

partial def cmEqs (p : Expr) (acc : Array (Expr × Expr)) : Array (Expr × Expr) :=
  match p.getAppFnArgs with
  | (``Eq, #[_, a, b]) => acc.push (a, b)
  | (``And, #[a, b]) => cmEqs b (cmEqs a acc)
  | _ => acc

abbrev CmCls := Array (Array (Sum FVarId Int))

def cmJoin (cls : CmCls) (a b : Expr) : CmCls :=
  match cmAtom a, cmAtom b with
  | some x, some y =>
      let ix := cls.findIdx? (·.contains x)
      let iy := cls.findIdx? (·.contains y)
      match ix, iy with
      | some i, some j =>
          if i != j then (cls.set! i (cls[i]! ++ cls[j]!)).eraseIdx! j else cls
      | some i, none => cls.set! i (cls[i]!.push y)
      | none, some j => cls.set! j (cls[j]!.push x)
      | none, none => cls.push #[x, y]
  | _, _ => cls

def cmBase (vars : Array FVarId) (st : CmSt) : CmCls := Id.run do
  let mut allV := vars
  for (a, v) in st.cells do
    allV := cmFVars v (cmFVars a allV)
  for p in st.pures do
    allV := cmFVars p allV
  let mut cls : CmCls := allV.map (fun f => #[.inl f])
  for p in st.pures do
    for (a, b) in cmEqs p #[] do
      cls := cmJoin cls a b
  return cls

inductive CmV where
  | var (i : Nat)
  | lit (n : Int)
  | add (a b : CmV)
  | subN (a b : CmV)
  | sub (a b : CmV)
  | neg (a : CmV)
  | unk
  deriving Inhabited

inductive CmP where
  | eq (a b : CmV)
  | ne (a b : CmV)
  | le (a b : CmV)
  | lt (a b : CmV)
  | not (a : CmP)
  | and (a b : CmP)
  | or (a b : CmP)
  | imp (a b : CmP)
  | tt
  | ff
  | unk
  deriving Inhabited

partial def cmCV (ix : Std.HashMap FVarId Nat) (e : Expr) : CmV :=
  match e with
  | .fvar f => match ix[f]? with
    | some i => .var i
    | none => .unk
  | .lit (.natVal n) => .lit n
  | .mdata _ b => cmCV ix b
  | _ =>
    match e.getAppFnArgs with
    | (``OfNat.ofNat, #[_, n, _]) => cmCV ix n
    | (``Nat.cast, #[_, _, a]) => cmCV ix a
    | (``NatCast.natCast, #[_, _, a]) => cmCV ix a
    | (``Int.ofNat, #[a]) => cmCV ix a
    | (``HAdd.hAdd, #[_, _, _, _, a, b]) => .add (cmCV ix a) (cmCV ix b)
    | (``HSub.hSub, #[t, _, _, _, a, b]) =>
        if t.isConstOf ``Nat then .subN (cmCV ix a) (cmCV ix b) else .sub (cmCV ix a) (cmCV ix b)
    | (``Neg.neg, #[t, _, a]) => if t.isConstOf ``Int then .neg (cmCV ix a) else .unk
    | _ => .unk

partial def cmCP (ix : Std.HashMap FVarId Nat) (p : Expr) : CmP :=
  match p.getAppFnArgs with
  | (``Eq, #[_, a, b]) => .eq (cmCV ix a) (cmCV ix b)
  | (``Ne, #[_, a, b]) => .ne (cmCV ix a) (cmCV ix b)
  | (``LE.le, #[_, _, a, b]) => .le (cmCV ix a) (cmCV ix b)
  | (``LT.lt, #[_, _, a, b]) => .lt (cmCV ix a) (cmCV ix b)
  | (``GE.ge, #[_, _, a, b]) => .le (cmCV ix b) (cmCV ix a)
  | (``GT.gt, #[_, _, a, b]) => .lt (cmCV ix b) (cmCV ix a)
  | (``Not, #[a]) => .not (cmCP ix a)
  | (``And, #[a, b]) => .and (cmCP ix a) (cmCP ix b)
  | (``Or, #[a, b]) => .or (cmCP ix a) (cmCP ix b)
  | (``True, #[]) => .tt
  | (``False, #[]) => .ff
  | _ =>
    match p with
    | .forallE _ a b _ => if b.hasLooseBVars then .unk else .imp (cmCP ix a) (cmCP ix b)
    | .mdata _ b => cmCP ix b
    | _ => .unk

def CmV.eval (env : Array (Option Int)) : CmV → Option Int
  | .var i => env[i]?.join
  | .lit n => some n
  | .add a b => match a.eval env, b.eval env with
    | some x, some y => some (x + y)
    | _, _ => none
  | .subN a b => match a.eval env, b.eval env with
    | some x, some y => some (if x ≥ y then x - y else 0)
    | _, _ => none
  | .sub a b => match a.eval env, b.eval env with
    | some x, some y => some (x - y)
    | _, _ => none
  | .neg a => (a.eval env).map (fun x => -x)
  | .unk => none

def CmP.eval (env : Array (Option Int)) : CmP → Option Bool
  | .eq a b => match a.eval env, b.eval env with
    | some x, some y => some (x == y)
    | _, _ => none
  | .ne a b => match a.eval env, b.eval env with
    | some x, some y => some (x != y)
    | _, _ => none
  | .le a b => match a.eval env, b.eval env with
    | some x, some y => some (decide (x ≤ y))
    | _, _ => none
  | .lt a b => match a.eval env, b.eval env with
    | some x, some y => some (decide (x < y))
    | _, _ => none
  | .not a => (a.eval env).map (!·)
  | .and a b => match a.eval env, b.eval env with
    | some false, _ => some false
    | _, some false => some false
    | some true, some true => some true
    | _, _ => none
  | .or a b => match a.eval env, b.eval env with
    | some true, _ => some true
    | _, some true => some true
    | some false, some false => some false
    | _, _ => none
  | .imp a b => match a.eval env, b.eval env with
    | some false, _ => some true
    | _, some true => some true
    | some true, some false => some false
    | _, _ => none
  | .tt => some true
  | .ff => some false
  | .unk => none

abbrev CmClsI := Array (Array (Sum Nat Int))

def CmV.lin : CmV → Option (Option Nat × Int)
  | .var i => some (some i, 0)
  | .lit n => some (none, n)
  | .add a b => do
    let (u, k) ← a.lin
    let (v, l) ← b.lin
    match u, v with
    | some _, some _ => none
    | some i, none | none, some i => some (some i, k + l)
    | none, none => some (none, k + l)
  | .sub a b => do
    let (u, k) ← a.lin
    let (v, l) ← b.lin
    if v.isSome then none else some (u, k - l)
  | _ => none

partial def cmAtoms (p : CmP) (acc : Array CmP) : Array CmP :=
  match p with
  | .and a b => cmAtoms b (cmAtoms a acc)
  | _ => acc.push p

def cmLins (ps : Array CmP) : Array (Option Nat × Int × Option Nat × Int × Int × Bool) := Id.run do
  let mut out := #[]
  for p in ps do
    for q in cmAtoms p #[] do
      let (a, b, c, two) := match q with
        | .eq a b => (a, b, (0 : Int), true)
        | .le a b => (a, b, 0, false)
        | .lt a b => (a, b, -1, false)
        | _ => (CmV.unk, CmV.unk, 0, false)
      let some (u, k) := a.lin | continue
      let some (v, l) := b.lin | continue
      if u.isNone && v.isNone then continue
      out := out.push (u, k, v, l, c, two)
  return out

structure CmPre where
  lins : Array (Option Nat × Int × Option Nat × Int × Int × Bool)
  allV : Array FVarId
  ix : Std.HashMap FVarId Nat
  pures : Array CmP
  cells : Array (CmV × CmV)
  base : CmClsI

def cmAtomI (ix : Std.HashMap FVarId Nat) (e : Expr) : Option (Sum Nat Int) :=
  match cmAtom e with
  | some (.inl f) => ix[f]?.map .inl
  | some (.inr n) => some (.inr n)
  | none => none

def cmPrep (vars : Array FVarId) (st : CmSt) (cls : CmCls) : Option CmPre := Id.run do
  let mut allV := vars
  for (a, v) in st.cells do
    allV := cmFVars v (cmFVars a allV)
  for p in st.pures do
    allV := cmFVars p allV
  let mut ix : Std.HashMap FVarId Nat := {}
  for i in [0 : allV.size] do
    ix := ix.insert allV[i]! i
  let mut base : CmClsI := #[]
  for c in cls do
    let mut ci := #[]
    for a in c do
      match a with
      | .inl f => match ix[f]? with
        | some i => ci := ci.push (.inl i)
        | none => return none
      | .inr n => ci := ci.push (.inr n)
    base := base.push ci
  let pures := st.pures.map (cmCP ix)
  let cells := st.cells.map (fun (a, v) => (cmCV ix a, cmCV ix v))
  return some ⟨cmLins pures, allV, ix, pures, cells, base⟩

def cmSameI (cls : CmClsI) (x y : Sum Nat Int) : Bool :=
  match cls.findIdx? (·.contains x) with
  | some i => cls[i]!.contains y
  | none => false

structure CmFb where
  clsOf : Std.HashMap Nat Nat := {}
  litOf : Array (Option Int) := #[]
  pairs : Std.HashSet (Nat × Nat) := {}
  lits : Std.HashSet (Nat × Int) := {}
  offs : Std.HashMap Nat (Array Int) := {}

partial def cmNeAtoms (p : CmP) (acc : Array (CmV × CmV)) : Array (CmV × CmV) :=
  match p with
  | .and a b => cmNeAtoms b (cmNeAtoms a acc)
  | .ne a b => acc.push (a, b)
  | .not (.eq a b) => acc.push (a, b)
  | _ => acc

def cmFbOf (pre : CmPre) : CmFb := Id.run do
  let mut clsOf : Std.HashMap Nat Nat := {}
  let mut litOf : Array (Option Int) := #[]
  for ci in [0 : pre.base.size] do
    let mut lit : Option Int := none
    for a in pre.base[ci]! do
      match a with
      | .inl i => clsOf := clsOf.insert i ci
      | .inr n => if lit.isNone then lit := some n
    litOf := litOf.push lit
  let key := fun (a b : Nat) => if a ≤ b then (a, b) else (b, a)
  let mut pairs : Std.HashSet (Nat × Nat) := {}
  let mut lits : Std.HashSet (Nat × Int) := {}
  for p in pre.pures do
    for (a, b) in cmNeAtoms p #[] do
      match a, b with
      | .var i, .var j =>
          match clsOf[i]?, clsOf[j]? with
          | some ci, some cj => pairs := pairs.insert (key ci cj)
          | _, _ => pure ()
      | .var i, .lit n | .lit n, .var i =>
          match clsOf[i]? with
          | some ci => lits := lits.insert (ci, n)
          | none => pure ()
      | _, _ => pure ()
  let mut offs : Std.HashMap Nat (Array Int) := {}
  for (a, _) in pre.cells do
    let r : Option (Nat × Int) := match a with
      | .var i => some (i, 0)
      | .add (.var i) (.lit k) => some (i, k)
      | _ => none
    match r with
    | some (i, k) =>
        match clsOf[i]? with
        | some ci => offs := offs.insert ci ((offs.getD ci #[]).push k)
        | none => pure ()
    | none => pure ()
  return { clsOf, litOf, pairs, lits, offs }

def cmDead (fb : CmFb) (pre : CmPre) (x y : Sum Nat Int) : Bool :=
  let key := fun (a b : Nat) => if a ≤ b then (a, b) else (b, a)
  let litCls := fun (n : Int) => pre.base.findIdx? (·.contains (.inr n))
  let clash := fun (a b : Option Int) => match a, b with
    | some m, some n => m != n
    | _, _ => false
  match x, y with
  | .inl i, .inl j =>
      match fb.clsOf[i]?, fb.clsOf[j]? with
      | some ci, some cj =>
          fb.pairs.contains (key ci cj) || clash (fb.litOf[ci]?.join) (fb.litOf[cj]?.join) ||
            (ci != cj && (fb.offs.getD ci #[]).any ((fb.offs.getD cj #[]).contains ·))
      | _, _ => false
  | .inl i, .inr n | .inr n, .inl i =>
      match fb.clsOf[i]? with
      | some ci =>
          fb.lits.contains (ci, n) || clash (fb.litOf[ci]?.join) (some n) ||
            (match litCls n with
              | some cn => fb.pairs.contains (key ci cn) ||
                  (ci != cn && (fb.offs.getD ci #[]).any ((fb.offs.getD cn #[]).contains ·))
              | none => false)
      | none => false
  | _, _ => false

def cmSolveM (pre : CmPre) (mi : Nat) (mj : Option Nat) (extra : Array (Sum Nat Int)) :
    Option (Array (Option Int) × CmHeap × Array Int × Nat) := Id.run do
  let nb := pre.base.size
  let mut cs : Array (Array (Sum Nat Int)) := #[]
  for ci in [0 : nb + 1] do
    if mj == some ci then continue
    if ci == nb && mi != nb then continue
    cs := cs.push (if ci == nb then extra else if ci == mi then pre.base[ci]! ++ extra else pre.base[ci]!)
  let n := cs.size
  let mut varCls : Array (Option Nat) := Array.replicate pre.allV.size none
  let mut lits : Array (Option Int) := #[]
  for ci in [0 : n] do
    let mut lit : Option Int := none
    for a in cs[ci]! do
      match a with
      | .inr m => match lit with
        | none => lit := some m
        | some m' => if m != m' then return none
      | .inl i => varCls := varCls.set! i (some ci)
    lits := lits.push lit
  let z := n
  let mut es : Array (Nat × Nat × Int) := #[]
  let mut used : Array Bool := Array.replicate (n + 1) false
  for (u, k, v, l, c, two) in pre.lins do
    let node := fun (w : Option Nat) => match w with
      | some i => varCls[i]?.join
      | none => some z
    let some x := node u | continue
    let some y := node v | continue
    if x == y then continue
    es := es.push (y, x, l - k + c)
    if two then es := es.push (x, y, k - l)
    used := used.set! x true |>.set! y true
  for ci in [0 : n] do
    unless used[ci]! do continue
    if let some m := lits[ci]! then
      es := es.push (z, ci, m) |>.push (ci, z, -m)
    es := es.push (ci, z, 0)
  let mut d : Array Int := Array.replicate (n + 1) 0
  if !es.isEmpty then
    let mut changed := true
    let mut it := 0
    while changed do
      if it > n + 1 then return none
      changed := false
      it := it + 1
      for (y, x, c) in es do
        if d[y]! + c < d[x]! then
          d := d.set! x (d[y]! + c)
          changed := true
  let mut k := 0
  let mut env : Array (Option Int) := Array.replicate pre.allV.size none
  let mut vals : Array Int := #[]
  for ci in [0 : n] do
    let v ← if used[ci]! then pure (d[ci]! - d[z]!)
      else match lits[ci]! with
        | some m => pure m
        | none =>
          k := k + 1
          pure (Int.ofNat (100000 + 1000 * k))
    let mut hasVar := false
    for a in cs[ci]! do
      match a with
      | .inl i =>
          env := env.set! i (some v)
          hasVar := true
      | .inr _ => pure ()
    if hasVar then vals := vals.push v
  for p in pre.pures do
    unless p.eval env == some true do return none
  let mut h : CmHeap := #[]
  for (a, v) in pre.cells do
    match a.eval env, v.eval env with
    | some x, some y => h := h.push (x, y)
    | _, _ => return none
  h := h.qsort (fun x y => x.1 < y.1)
  for i in [1 : h.size] do
    if h[i - 1]!.1 == h[i]!.1 then return none
  let mut out : Array Int := #[]
  for v in vals.qsort (· < ·) do
    if out.back? != some v then out := out.push v
  return some (env, h, out, k)

def cmIsoKey (k : Nat) (h : CmHeap) (rv : Array (Option Int)) (vals : Array Int) :
    Array (Nat × Int × Nat × Int) × Array (Option (Nat × Int)) × Array (Nat × Int) := Id.run do
  let kOf := fun (v : Int) =>
    if v ≥ 101000 && v < 100000 + 1000 * (k + 1) then (v - 100000).toNat / 1000 else 0
  let mut start : Array Nat := Array.replicate (k + 1) h.size
  for idx in [0 : h.size] do
    let c := kOf h[idx]!.1
    if c != 0 && start[c]! == h.size then start := start.set! c idx
  let mut lab : Array Nat := Array.replicate (k + 1) 0
  let mut order : Array Nat := #[]
  let mut si := 0
  let mut i := 0
  let nr := rv.size
  while si < nr + h.size + vals.size || i < order.size do
    if i < order.size then
      let b := order[i]!
      i := i + 1
      let mut idx := start[b]!
      while idx < h.size && kOf h[idx]!.1 == b do
        let c := kOf h[idx]!.2
        if c != 0 && lab[c]! == 0 then
          order := order.push c
          lab := lab.set! c order.size
        idx := idx + 1
    else
      let v := if si < nr then rv[si]!.getD 0 else if si < nr + h.size then h[si - nr]!.1
        else vals[si - nr - h.size]!
      let c := kOf v
      if c != 0 && lab[c]! == 0 then
        order := order.push c
        lab := lab.set! c order.size
      si := si + 1
  let enc := fun (v : Int) => match kOf v with
    | 0 => (0, v)
    | c => (lab[c]!, v - 100000 - 1000 * c)
  let mut hk : Array (Nat × Int × Nat × Int) := #[]
  for (a, w) in h do
    if kOf a == 0 then
      let (l, o) := enc w
      hk := hk.push (0, a, l, o)
  for b in order do
    let mut idx := start[b]!
    while idx < h.size && kOf h[idx]!.1 == b do
      let (a, w) := h[idx]!
      let (l, o) := enc w
      hk := hk.push (lab[b]!, a - 100000 - 1000 * b, l, o)
      idx := idx + 1
  let lt := fun (p q : Nat × Int) => p.1 < q.1 || (p.1 == q.1 && p.2 < q.2)
  return (hk, rv.map (·.map enc), (vals.map enc).qsort lt)

def cmMergeOf (fb : CmFb) (pre : CmPre) (x y : Sum Nat Int) :
    Nat × Option Nat × Array (Sum Nat Int) :=
  let clsOfA := fun (a : Sum Nat Int) => match a with
    | .inl i => fb.clsOf[i]?
    | .inr n => pre.base.findIdx? (·.contains (.inr n))
  match clsOfA x, clsOfA y with
  | some i, some j => if i != j then (i, some j, pre.base[j]!) else (i, none, #[])
  | some i, none => (i, none, #[y])
  | none, some j => (j, none, #[x])
  | none, none => (pre.base.size, none, #[x, y])

structure CmPrepped where
  pre : CmPre
  fb : CmFb
  atoms1 : Option (Array (Sum Nat Int))
  atoms2 : Option (Array (Sum Nat Int))
  rvIdx : Array (Option Nat)

def cmPrepare (vars : Array FVarId) (ptrs : Array Expr) (rvs : Array FVarId) (st : CmSt) :
    Option CmPrepped := do
  let pre ← cmPrep vars st (cmBase vars st)
  let fakes := (st.cells.foldl (fun acc (a, v) => cmFVars v (cmFVars a acc)) #[]).filter
    (fun f => !vars.contains f)
  let nil := mkNatLit 0
  let a1 := (ptrs.push nil).mapM (cmAtomI pre.ix)
  let a2 := (ptrs.push nil ++ fakes.map Expr.fvar).mapM (cmAtomI pre.ix)
  return { pre, fb := cmFbOf pre, atoms1 := a1, atoms2 := a2, rvIdx := rvs.map (pre.ix[·]?) }

def cmCanon (vars : Array FVarId) (st : CmSt) : Array Expr := Id.run do
  let mut fr : Array FVarId := #[]
  for (a, v) in st.cells do
    fr := cmFVars v (cmFVars a fr)
  for p in st.pures do
    fr := cmFVars p fr
  fr := fr.filter (!vars.contains ·)
  let xs := fr.map Expr.fvar
  let ys := (List.range fr.size).toArray.map (fun i => Expr.fvar ⟨Name.mkNum `_xcmc i⟩)
  let rn := fun (e : Expr) => e.replaceFVars xs ys
  let mut out : Array Expr := #[]
  for (a, v) in st.cells do
    out := out.push (rn a) |>.push (rn v)
  out := out.push (mkConst `_xcmsep)
  for p in st.pures do
    out := out.push (rn p)
  return out

partial def cmPin (x : Expr) (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) =>
      match cmPin x a with
      | some r => some r
      | none => cmPin x b
  | (``HProp.hexists, #[_, _, j]) =>
      match j with
      | .lam _ _ b _ => cmPin x b
      | _ => none
  | (``HProp.hsingle, #[_, a, v]) =>
      if cmAtom v == cmAtom x && cmAtom x != none && !a.hasLooseBVars
          && (a.find? (· == x)).isNone then some a else none
  | _ => none

inductive CmN where
  | star (a b : CmN)
  | emp
  | pure (p : CmP)
  | cell (a v : CmV)
  | ex (isNat : Bool) (slot : Nat) (sym : Bool) (pin : Option CmV) (body : CmN)
  | or (ds : Array CmN)
  | call (p : Nat) (args : Array CmV)
  | unk
  deriving Inhabited

partial def cmCompile (tbl : Array (Name × Nat × Expr)) (ix : Std.HashMap FVarId Nat)
    (next : Nat) (e : Expr) : CmN :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) => .star (cmCompile tbl ix next a) (cmCompile tbl ix next b)
  | (``HProp.hempty, #[_]) => .emp
  | (``HProp.hpure, #[_, p]) => .pure (cmCP ix p)
  | (``HProp.hsingle, #[_, a, v]) => .cell (cmCV ix a) (cmCV ix v)
  | (``HProp.hexists, #[_, _, j]) =>
      match j with
      | .lam _ bt b _ =>
          let isNat := bt.isConstOf ``Nat
          if !(isNat || bt.isConstOf ``Int) then .unk else
          let x := mkFVar ⟨.num `_xcmslot next⟩
          let body := b.instantiate1 x
          let ix' := ix.insert x.fvarId! next
          .ex isNat next false ((cmPin x body).map (cmCV ix)) (cmCompile tbl ix' (next + 1) body)
      | _ => .unk
  | _ =>
    if cmOr e then
      .or ((cmDisjs e).map (cmCompile tbl ix next))
    else
      match e.getAppFn.constName? with
      | some nm =>
          match tbl.findIdx? (·.1 == nm) with
          | some k =>
              if e.getAppNumArgs == tbl[k]!.2.1 then .call k (e.getAppArgs.map (cmCV ix)) else .unk
          | none => .unk
      | none => .unk

def cmCompileTbl (tbl : Array (Name × Nat × Expr)) : Array CmN :=
  tbl.map fun (_, n, r) =>
    let xs := (List.range n).toArray.map (fun i => mkFVar ⟨.num `_xcmslot i⟩)
    let ix := (List.range n).foldl (fun m i => m.insert ⟨.num `_xcmslot i⟩ i) {}
    cmCompile tbl ix n (r.instantiateRev xs)

structure CmEv where
  prog : Array CmN
  off : Nat
  gvals : Array Int

abbrev CmM := StateM (Nat × Nat)

def cmTick : CmM Bool := do
  let (s, c) ← get
  if s == 0 then return false
  set (s - 1, c)
  return true

def cmCount : CmM Nat := do
  let (s, c) ← get
  set (s, c + 1)
  return c

partial def CmV.slots (v : CmV) (acc : Array Nat) : Array Nat :=
  match v with
  | .var i => acc.push i
  | .add a b | .subN a b | .sub a b => b.slots (a.slots acc)
  | .neg a => a.slots acc
  | _ => acc

partial def cmAddrSlots (au : Array (Array Bool)) (e : CmN) (acc : Array Nat) : Array Nat :=
  match e with
  | .star a b => cmAddrSlots au b (cmAddrSlots au a acc)
  | .cell a _ => a.slots acc
  | .ex _ _ _ _ body => cmAddrSlots au body acc
  | .or ds => ds.foldl (fun acc d => cmAddrSlots au d acc) acc
  | .call k args => (List.range args.size).foldl (fun acc j =>
      if ((au[k]?).bind (·[j]?)).getD true then args[j]!.slots acc else acc) acc
  | _ => acc

def cmAddrUse (prog : Array CmN) (arity : Array Nat) : Array (Array Bool) := Id.run do
  let mut au := arity.map (fun n => Array.replicate n false)
  for _ in [0 : arity.foldl (· + ·) 0 + 1] do
    let nu := (List.range prog.size).toArray.map fun k =>
      let s := cmAddrSlots au prog[k]! #[]
      (List.range arity[k]!).toArray.map (s.contains ·)
    if nu == au then break
    au := nu
  return au

partial def cmMark (au : Array (Array Bool)) (e : CmN) : CmN :=
  match e with
  | .star a b => .star (cmMark au a) (cmMark au b)
  | .ex isNat slot _ pin body =>
    let b := cmMark au body
    .ex isNat slot (pin.isNone && !(cmAddrSlots au b #[]).contains slot) pin b
  | .or ds => .or (ds.map (cmMark au))
  | e => e

abbrev CmL := Nat × Int

def CmV.sym (env : Array (Option CmL)) : CmV → Option CmL
  | .var i => env[i]?.join
  | .lit n => some (0, n)
  | .add a b => do
    let (u, k) ← a.sym env
    let (v, l) ← b.sym env
    if u == 0 then some (v, k + l) else if v == 0 then some (u, k + l) else none
  | .sub a b => do
    let (u, k) ← a.sym env
    let (v, l) ← b.sym env
    if v == 0 then some (u, k - l) else if u == v then some (0, k - l) else none
  | .subN a b => do
    let (u, k) ← a.sym env
    let (v, l) ← b.sym env
    if u == 0 && v == 0 then some (0, if k ≥ l then k - l else 0) else none
  | .neg a => do
    let (u, k) ← a.sym env
    if u == 0 then some (0, -k) else none
  | .unk => none

structure CmCs where
  n : Nat := 0
  es : Array (Nat × Nat × Int) := #[]
  nes : Array (CmL × CmL) := #[]
  deriving BEq, Inhabited

def CmCs.le (cs : CmCs) (a b : CmL) : Option CmCs :=
  if a.1 == b.1 then (if a.2 ≤ b.2 then some cs else none)
  else some { cs with es := cs.es.push (b.1, a.1, b.2 - a.2) }

def CmCs.solve (cs : CmCs) : Option (Array Int) := Id.run do
  let mut d : Array Int := Array.replicate (cs.n + 1) 0
  let mut changed := true
  let mut it := 0
  while changed do
    if it > cs.n + 1 then return none
    changed := false
    it := it + 1
    for (y, x, c) in cs.es do
      if d[y]! + c < d[x]! then
        d := d.set! x (d[y]! + c)
        changed := true
  let z := d[0]!
  return some (d.map (· - z))

def CmCs.final (cs : CmCs) : Option Bool :=
  match cs.solve with
  | none => some false
  | some v =>
    let val := fun (l : CmL) => v[l.1]! + l.2
    if cs.nes.all (fun (a, b) => val a != val b) then some true else none

partial def CmP.sym (env : Array (Option CmL)) (cs : CmCs) : CmP → Option (Bool × CmCs)
  | .eq a b => do
    let la ← a.sym env
    let lb ← b.sym env
    if la.1 == 0 && lb.1 == 0 then return (la.2 == lb.2, cs)
    match cs.le la lb >>= (·.le lb la) with
    | some cs' => some (true, cs')
    | none => some (false, cs)
  | .le a b => do
    let la ← a.sym env
    let lb ← b.sym env
    match cs.le la lb with
    | some cs' => some (true, cs')
    | none => some (false, cs)
  | .lt a b => do
    let la ← a.sym env
    let lb ← b.sym env
    match cs.le (la.1, la.2 + 1) lb with
    | some cs' => some (true, cs')
    | none => some (false, cs)
  | .ne a b => do
    let la ← a.sym env
    let lb ← b.sym env
    if la.1 == 0 && lb.1 == 0 then return (la.2 != lb.2, cs)
    if la == lb then return (false, cs)
    some (true, { cs with nes := cs.nes.push (la, lb) })
  | .not (.eq a b) => CmP.sym env cs (.ne a b)
  | .not p => do
    let (r, cs') ← p.sym env cs
    if cs' == cs then some (!r, cs) else none
  | .and a b => do
    let (r, c1) ← a.sym env cs
    if !r then return (false, cs)
    b.sym env c1
  | .or a b =>
    match a.sym env cs, b.sym env cs with
    | some (true, c), _ => if c == cs then some (true, cs) else none
    | _, some (true, c) => if c == cs then some (true, cs) else none
    | some (false, _), some (false, _) => some (false, cs)
    | _, _ => none
  | .imp a b =>
    match a.sym env cs, b.sym env cs with
    | some (false, _), _ => some (true, cs)
    | _, some (true, c) => if c == cs then some (true, cs) else none
    | some (true, c), some (false, _) => if c == cs then some (false, cs) else none
    | _, _ => none
  | .tt => some (true, cs)
  | .ff => some (false, cs)
  | .unk => none

structure CmRes where
  outs : Array (CmHeap × CmCs) := #[]
  inc : Bool := false
  deriving Inhabited

def CmRes.join (a b : CmRes) : CmRes :=
  { outs := b.outs.foldl (fun acc o => if acc.contains o then acc else acc.push o) a.outs,
    inc := a.inc || b.inc }

def cmCandsI (ev : CmEv) (env : Array (Option CmL)) (path : Array Int) (h : CmHeap)
    (isNat : Bool) (pin : Option CmV) : CmM (Array Int) := do
  let _ ← cmCount
  let mut cands : Array Int := #[]
  let mut pinned := false
  match pin.bind (·.sym env) with
  | some (0, av) =>
      pinned := true
      match h.find? (·.1 == av) with
      | some (_, v) => cands := #[v]
      | none => pure ()
  | _ => pure ()
  unless pinned do
    let n ← cmCount
    let c0 := Int.ofNat (1000000000 + 1000 * n)
    cands := #[c0]
    let mut cs : Std.HashSet Int := Std.HashSet.emptyWithCapacity.insert c0
    let add := fun (b0 : Int) (st : Array Int × Std.HashSet Int) => Id.run do
      let mut (cands, cs) := st
      for i in [0 : ev.off + 1] do
        for c in #[b0 + i, b0 - i] do
          unless cs.contains c do
            cs := cs.insert c
            cands := cands.push c
      return (cands, cs)
    let mut st := add 0 (cands, cs)
    for (a, v) in h do
      st := add v (add a st)
    for v in ev.gvals do
      st := add v st
    for v in path do
      st := add v st
    cands := st.1
  if isNat then cands := cands.filter (· ≥ 0)
  return cands

def cmFresh? (cs : CmCs) (isNat : Bool) : CmCs × CmL :=
  let x := cs.n + 1
  ({ cs with n := x, es := if isNat then cs.es.push (x, 0, 0) else cs.es }, (x, 0))

def cmCellS (env : Array (Option CmL)) (cs : CmCs) (a v : CmV) (h : CmHeap) :
    Option (Option (CmHeap × CmCs)) := do
  let (u, x) ← a.sym env
  if u != 0 then none
  let lv ← v.sym env
  match h.find? (·.1 == x) with
  | none => some none
  | some (_, y) =>
    if lv.1 == 0 then
      return if lv.2 == y then some (h.filter (·.1 != x), cs) else none
    match cs.le lv (0, y) >>= (·.le (0, y) lv) with
    | some cs' => if cs'.solve.isSome then some (some (h.filter (·.1 != x), cs')) else some none
    | none => some none

mutual

partial def cmConsI (ev : CmEv) (env : Array (Option CmL)) (cs : CmCs) (path : Array Int) (fuel : Nat)
    (e : CmN) (h : CmHeap) : CmM CmRes := do
  unless ← cmTick do return { inc := true }
  match e with
  | .star a b =>
      let r1 ← cmConsI ev env cs path fuel a h
      let mut acc : CmRes := { inc := r1.inc }
      for (o, c) in r1.outs do
        acc := acc.join (← cmConsI ev env c path fuel b o)
      return acc
  | .emp => return { outs := #[(h, cs)] }
  | .pure p =>
      match p.sym env cs with
      | some (true, cs') => if cs' != cs && cs'.solve.isNone then return {} else return { outs := #[(h, cs')] }
      | some (false, _) => return {}
      | none => return { inc := true }
  | .cell a v =>
      match cmCellS env cs a v h with
      | some (some o) => return { outs := #[o] }
      | some none => return {}
      | none => return { inc := true }
  | .ex isNat _ sym pin body =>
      if sym then
        let (cs', l) := cmFresh? cs isNat
        return ← cmConsI ev (env.push (some l)) cs' path fuel body h
      let cands ← cmCandsI ev env path h isNat pin
      let mut acc : CmRes := {}
      for c in cands do
        acc := acc.join (← cmConsI ev (env.push (some (0, c))) cs (path.push c) fuel body h)
      return acc
  | .or ds =>
      let mut acc : CmRes := {}
      for d in ds do
        acc := acc.join (← cmConsI ev env cs path fuel d h)
      return acc
  | .call k args =>
      if fuel == 0 then return { inc := true }
      cmConsI ev (args.map (·.sym env)) cs path (fuel - 1) ev.prog[k]! h
  | .unk => return { inc := true }

partial def cmConsKI (ev : CmEv) (env : Array (Option CmL)) (cs : CmCs) (path : Array Int) (fuel : Nat)
    (e : CmN) (h : CmHeap) : CmM (Bool × Bool) := do
  unless ← cmTick do return (false, true)
  let fin := fun (h : CmHeap) (c : CmCs) => if !h.isEmpty then (false, false) else match c.final with
    | some r => (r, false)
    | none => (false, true)
  match e with
  | .star a b =>
      let r1 ← cmConsI ev env cs path fuel a h
      let mut inc := r1.inc
      for (o, c) in r1.outs do
        let (f, i) ← cmConsKI ev env c path fuel b o
        inc := inc || i
        if f then return (true, inc)
      return (false, inc)
  | .emp => return fin h cs
  | .pure p =>
      match p.sym env cs with
      | some (true, cs') => return fin h cs'
      | some (false, _) => return (false, false)
      | none => return (false, true)
  | .cell a v =>
      match cmCellS env cs a v h with
      | some (some (o, c)) => return fin o c
      | some none => return (false, false)
      | none => return (false, true)
  | .ex isNat _ sym pin body =>
      if sym then
        let (cs', l) := cmFresh? cs isNat
        return ← cmConsKI ev (env.push (some l)) cs' path fuel body h
      let cands ← cmCandsI ev env path h isNat pin
      let mut inc := false
      for c in cands do
        let (f, i) ← cmConsKI ev (env.push (some (0, c))) cs (path.push c) fuel body h
        inc := inc || i
        if f then return (true, inc)
      return (false, inc)
  | .or ds =>
      let mut inc := false
      for d in ds do
        let (f, i) ← cmConsKI ev env cs path fuel d h
        inc := inc || i
        if f then return (true, inc)
      return (false, inc)
  | .call k args =>
      if fuel == 0 then return (false, true)
      cmConsKI ev (args.map (·.sym env)) cs path (fuel - 1) ev.prog[k]! h
  | .unk => return (false, true)

end

partial def cmMaxOff (e : Expr) (acc : Nat) : Nat :=
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
      let acc := match cmVal {} b with
        | some n => max acc n.natAbs
        | none => acc
      cmMaxOff b (cmMaxOff a acc)
  | _ =>
    match e with
    | .app f a => cmMaxOff a (cmMaxOff f acc)
    | .lam _ t b _ => cmMaxOff b (cmMaxOff t acc)
    | .forallE _ t b _ => cmMaxOff b (cmMaxOff t acc)
    | .mdata _ b => cmMaxOff b acc
    | _ => acc

partial def cmItems (e : Expr) : Array Expr :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) => cmItems a ++ cmItems b
  | _ => #[e]

def witPairs (L : Array Expr) (r : Expr) (free : Expr → Bool) : Array (Nat × Expr) := Id.run do
  let ra := r.getAppArgs
  let mut out : Array (Nat × Expr) := #[]
  for l in L do
    let la := l.getAppArgs
    unless la.size == ra.size && l.isAppOf ``HProp.hsingle == r.isAppOf ``HProp.hsingle do continue
    let mut ok := true
    let mut sc := 0
    for m in [0 : ra.size] do
      if free ra[m]! then continue
      if ra[m]! == la[m]! then sc := sc + 1 else ok := false
    if ok then out := out.push (sc, l)
  return out

partial def cellHeads (nr : Array Name) (e : Expr) : Nat :=
  let isHead := fun (s : Expr) =>
    (s.getAppFn.constName? == some ``HProp.hsingle && s.getAppNumArgs ≥ 2 &&
      s.getAppArgs[s.getAppNumArgs - 2]!.getAppFn.constName? != some ``HAdd.hAdd)
    || (match s.getAppFn.constName? with
        | some n => nr.contains n && s.getAppNumArgs > 0
        | none => false)
  if isHorConst e && e.getAppNumArgs ≥ 2 then
    let a := e.getAppArgs
    max (cellHeads nr a[a.size-2]!) (cellHeads nr a[a.size-1]!)
  else
    let rec go (x : Expr) (acc : Nat) : Nat :=
      let acc := if isHead x then acc + 1 else acc
      match x with
      | .app f a => go a (go f acc)
      | .lam _ _ b _ => go b acc
      | .mdata _ b => go b acc
      | _ => acc
    go e 0

def earlyLhsOccs (entries : Array UnfoldEntry) (heads : Array Name)
    (lhs rhs : Expr) : TacticM (Array Expr) := do
  let mut cap := 0
  let mut nr : Array Name := #[]
  for h in heads do
    if !(← isRecPred h) && !nr.contains h then nr := nr.push h
  for o in collectOccs heads rhs #[] do
    match o.getAppFn.constName? with
    | some nm =>
        if !(← isRecPred nm) && !(← isFlatPred nm) then
          for e in entries do
            if e.headFn != nm then continue
            let ty := (← getConstInfo e.lemmaName).type
            let c ← forallTelescopeReducing ty fun _ concl => do
              match concl.eq? with
              | some (_, _, body) => pure (cellHeads nr body)
              | none => pure 0
            cap := max cap c
    | none => pure ()
  if cap == 0 then return #[]
  if cellHeads nr lhs ≥ cap then return #[]
  let mut out : Array Expr := #[]
  for o in Sep.Xsimpl.parseHstar lhs do
    match o.getAppFn.constName? with
    | some nm => if heads.contains nm && (← isRecPred nm) then out := out.push o
    | none => pure ()
  if out.size != 1 then return #[]
  return out

partial def stripExProp (e : Expr) : MetaM Expr := do
  match e.getAppFnArgs with
  | (``HProp.hexists, args) =>
      match args.back? with
      | some lam =>
          if lam.isLambda && !lam.bindingBody!.hasLooseBVars
              && (← isProp lam.bindingDomain!) then
            stripExProp lam.bindingBody!
          else pure e
      | none => pure e
  | _ => pure e

partial def wandChain (e : Expr) (acc : Array Expr) : Array Expr × Expr :=
  match wandParts? e with
  | some (A, B) => wandChain B (acc.push A)
  | none => (acc, e)

partial def curryEq (inst : Expr) (ants : List Expr) (B : Expr) : MetaM Expr := do
  match ants with
  | [] => throwError "fw: empty"
  | [_] => mkEqRefl (← mkAppM ``HProp.hwand #[ants[0]!, B])
  | A :: rest =>
      let R ← mkStarOf inst rest
      let e1 ← mkAppM ``HProp.hwand_curry_eq #[A, R, B]
      let e2 ← curryEq inst rest B
      let f ← withLocalDeclD `fwz (← inferType B) fun z => do
        mkLambdaFVars #[z] (← mkAppM ``HProp.hwand #[A, z])
      mkEqTrans e1 (← mkCongrArg f e2)

def fwandAlt (lhs rhs : Expr) (L : List Expr) (i : Nat) (v A B : Expr)
    (ks : List Nat) (hj : Expr) : TacticM Unit := withMainContext do
  let W := L[i]!
  let g ← getMainGoal
  let gt ← instantiateMVars (← g.getType)
  let inst := gt.getAppArgs[0]!
  let E ← mkStarOf inst (ks.map (fun k => L[k]!))
  let F ← mkStarOf inst ((L.zipIdx.filter (fun (_, j) =>
    j != i && !ks.contains j)).map (·.1))
  match ← provePerm lhs (← mkAppM ``HProp.hstar #[W, ← mkAppM ``HProp.hstar #[E, F]]) with
  | none => throwError "fw: perm"
  | some h0 =>
    let mv1 ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[E, A])
    let mv2 ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``HProp.himpl #[← mkAppM ``HProp.hstar #[B, F], rhs])
    let J := W.appArg!
    let hj ← mkExpectedTypeHint hj (← mkEq (mkApp J v) (← mkAppM ``HProp.hwand #[A, B]))
    let n := (← getConstInfo ``fwand_use).type.getForallArity
    let args : Array (Option Expr) := (Array.range n).map (fun k =>
      if k == n - 10 then some J else if k == n - 4 then some v
      else if k == n - 3 then some hj else if k == n - 2 then some mv1
      else if k == n - 1 then some mv2 else none)
    let full ← mkAppM ``HProp.himpl_trans
      #[h0, ← mkAppOptM ``fwand_use args]
    unless ← isDefEq (← inferType full) gt do throwError "fw: mismatch"
    g.assign full
    replaceMainGoal [mv1.mvarId!, mv2.mvarId!]

def forallAlts (lhs rhs : Expr) (L : List Expr) :
    TacticM (Array (Bool × TacticM Unit)) := withMainContext do
  let mut out : Array (Bool × TacticM Unit) := #[]
  let locs := ptoLocsOf lhs #[]
  for i in [0 : L.length] do
    let W := L[i]!
    unless W.getAppFn.constName? == some ``HProp.hforall do continue
    let J := W.appArg!
    let dom ← inferType J
    unless dom.isForall do continue
    let inst := (← inferType W).appArg!
    for v in locs do
      unless ← isDefEq (← inferType v) dom.bindingDomain! do continue
      let (ants, B) := wandChain (mkApp J v).headBeta #[]
      if ants.isEmpty then continue
      let mut core : Array Expr := #[]
      for a in ants do
        core := core ++ (flatStar (← stripExProp a) #[]).filter (fun a =>
          a.getAppFn.constName? != some ``HProp.hpure)
      let mut ks : List Nat := []
      let mut ok := !core.isEmpty
      for a in core do
        match (List.range L.length).find? (fun m =>
            m != i && !ks.contains m && L[m]! == a) with
        | some m => ks := ks ++ [m]
        | none => ok := false
      if ok then
        let A ← mkStarOf inst ants.toList
        let hj ← mkEqSymm (← curryEq inst ants.toList B)
        out := out.push (false, fwandAlt lhs rhs L i v A B ks hj)
  return out

partial def horBranches (e : Expr) (acc : Array Expr) : Array Expr :=
  if isHorConst e && e.getAppNumArgs ≥ 2 then
    let a := e.getAppArgs
    horBranches a[a.size-1]! (acc.push a[a.size-2]!)
  else acc.push e

partial def peelExM (e : Expr) : MetaM Expr := do
  match e.getAppFnArgs with
  | (``HProp.hexists, args) =>
      match args.back? with
      | some lam =>
          if lam.isLambda then
            let m ← mkFreshExprMVar lam.bindingDomain!
            peelExM (lam.bindingBody!.instantiate1 m)
          else pure e
      | none => pure e
  | _ => pure e

def unfoldLemma (p : Name) : MetaM (Option Name) := do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  return (entries.find? (·.headFn == p)).map (·.lemmaName)

def isCellAtom (e : Expr) : Bool := e.getAppFn.constName? == some ``HProp.hsingle

def isPureAtom (e : Expr) : Bool := e.getAppFn.constName? == some ``HProp.hpure

def pureEq? (e : Expr) : Option (Expr × Expr) :=
  if isPureAtom e then
    match e.appArg!.eq? with
    | some (_, a, b) => some (a, b)
    | none => none
  else none

def matchInto (pat tgt : Array Expr) : MetaM (Option (Array Expr)) := do
  let mut used : Array Nat := #[]
  let mut miss : Array Expr := #[]
  for a in pat do
    if isPureAtom a then continue
    let mut got := false
    for j in [0 : tgt.size] do
      if used.contains j || isPureAtom tgt[j]! then continue
      if ← (try checkpointDefEq (isDefEq a tgt[j]!) catch _ => pure false) then
        used := used.push j
        got := true
        break
    unless got do
      if isCellAtom a then return none
      miss := miss.push a
  return some miss

def mkInvLam (xs : Array Expr) (A C : Expr) : MetaM (Option Expr) := do
  let A ← instantiateMVars A
  let C ← instantiateMVars C
  let mut ms : Array MVarId := #[]
  for m in (← getMVars C) ++ (← getMVars A) do
    unless ms.contains m do ms := ms.push m
  let mut tys : Array Expr := #[]
  for m in ms do
    let t ← instantiateMVars (← m.getType)
    if t.hasExprMVar then return none
    tys := tys.push t
  withLocalDeclsD (tys.mapIdx fun i t => (Name.mkSimple s!"ivw{i}", fun _ => pure t))
    fun ws => do
      let sub := fun (e : Expr) => e.replace (fun s => match s with
        | .mvar m => (ms.findIdx? (· == m)).map (ws[·]!)
        | _ => none)
      let mut body ← mkAppM ``HProp.hwand #[sub A, sub C]
      for w in ws.reverse do
        body ← mkAppM ``HProp.hforall #[← mkLambdaFVars #[w] body]
      let lam ← instantiateMVars (← mkLambdaFVars xs body)
      if lam.hasExprMVar || lam.hasFVar then return none
      return some lam

initialize invDCache : IO.Ref (Array (Name × Name × Array Expr)) ← IO.mkRef #[]

def deriveA (a r : Name) : MetaM (Array Expr) := withoutModifyingState do
  let some la ← unfoldLemma a | return #[]
  let some lr ← unfoldLemma r | return #[]
  forallTelescopeReducing (← getConstInfo la).type fun xs concl => do
    let some (_, _, body) := concl.eq? | return #[]
    let occs := (collectOccs #[a] body #[]).filter (·.getAppNumArgs == xs.size)
    if occs.isEmpty then return #[]
    let fixed := (Array.range xs.size).filter (fun k =>
      occs.all (fun o => o.getAppArgs[k]? == some xs[k]!))
    let isFixed := fun (e : Expr) => fixed.any (fun k => xs[k]! == e)
    let isFree := fun (e : Expr) => xs.contains e && !isFixed e
    let mut out : Array Expr := #[]
    for br in horBranches body #[] do
      if !(collectOccs #[a] br #[]).isEmpty then continue
      let res ← peelExG br #[] fun us bd => do
        let atoms := flatStar bd #[]
        unless atoms.any isCellAtom do return none
        let (rvs, _, rc) ← forallMetaTelescopeReducing (← getConstInfo lr).type
        let some (_, _, rbody) := rc.eq? | return none
        for rb in horBranches rbody #[] do
          if (collectOccs #[r] rb #[]).isEmpty then continue
          let rbd ← peelExM rb
          let s ← saveState
          match ← matchInto (flatStar rbd #[]) atoms with
          | some miss =>
            if miss.size == 1 then
              let Q ← instantiateMVars miss[0]!
              let mut C ← instantiateMVars (mkAppN (mkConst r) rvs)
              for atm in atoms do
                match pureEq? atm with
                | some (u, v) =>
                    if isFree u && isFixed v then C := C.replaceFVar u v
                    else if isFree v && isFixed u then C := C.replaceFVar v u
                | none => pure ()
              let bad := fun (e : Expr) => us.any (fun u => e.containsFVar u.fvarId!)
              let freeIn := xs.any (fun x => isFree x && C.containsFVar x.fvarId!)
              if !bad Q && !bad C && !freeIn then
                if let some lam ← mkInvLam xs Q C then return some lam
          | none => pure ()
          s.restore
        return none
      if let some lam := res then
        unless out.contains lam do out := out.push lam
    return out

def deriveB (p v : Name) : MetaM (Array Expr) := withoutModifyingState do
  let some lp ← unfoldLemma p | return #[]
  let some lv ← unfoldLemma v | return #[]
  forallTelescopeReducing (← getConstInfo lp).type fun xs concl => do
    let some (_, _, body) := concl.eq? | return #[]
    if (collectOccs #[p] body #[]).isEmpty then return #[]
    let mut out : Array Expr := #[]
    for br in horBranches body #[] do
      if !(collectOccs #[p] br #[]).isEmpty then continue
      let res ← peelExG br #[] fun us bd => do
        let atoms := flatStar bd #[]
        let cells := atoms.filter isCellAtom
        if cells.isEmpty then return #[]
        let peqs := atoms.filterMap pureEq?
        let (vvs, _, vc) ← forallMetaTelescopeReducing (← getConstInfo lv).type
        let some (_, _, vbody) := vc.eq? | return #[]
        let mut acc : Array Expr := #[]
        for vb in horBranches vbody #[] do
          let vbd ← peelExM vb
          let vatoms := flatStar vbd #[]
          let vcells := vatoms.filter isCellAtom
          if vcells.size != cells.size then continue
          let ctx := vatoms.filter (fun e => !isPureAtom e && !isCellAtom e)
          unless ctx.size == 1 do continue
          let some cn := ctx[0]!.getAppFn.constName? | continue
          if cn == p || !(← isRecPred cn) then continue
          let s ← saveState
          match ← matchInto vcells cells with
          | some miss =>
            if miss.isEmpty then
              let mut choices : Array (MVarId × Array Expr) := #[]
              let mut okB := true
              for e in vatoms.filterMap pureEq? do
                let l ← instantiateMVars e.1
                let r ← instantiateMVars e.2
                let cands := fun (t : Expr) =>
                  (peqs.filterMap (fun (a, b) =>
                    if a == t then some b else if b == t then some a else none)).push t
                if let .mvar m := l then
                  unless r.hasExprMVar do choices := choices.push (m, cands r)
                else if let .mvar m := r then
                  unless l.hasExprMVar do choices := choices.push (m, cands l)
                else if l != r then okB := false
              if okB && choices.size ≤ 2 then
                let mut combos : Array (Array Expr) := #[#[]]
                for (_, cs) in choices do
                  combos := combos.flatMap (fun c => cs.map (c.push ·))
                for combo in combos do
                  let s2 ← saveState
                  for k in [0 : choices.size] do
                    choices[k]!.1.assign combo[k]!
                  let A := ctx[0]!
                  let C := mkAppN (mkConst v) vvs
                  let bad := fun (e : Expr) => us.any (fun u => e.containsFVar u.fvarId!)
                  if !bad (← instantiateMVars A) && !bad (← instantiateMVars C) then
                    if let some lam ← mkInvLam xs A C then
                      unless acc.contains lam do acc := acc.push lam
                  s2.restore
          | none => pure ()
          s.restore
        return acc
      for lam in res do
        unless out.contains lam do out := out.push lam
    return out

def deriveInv (a r : Name) (strong : Bool) : MetaM (Array Expr) := do
  let key := if strong then r ++ `strong else r
  match (← invDCache.get).findSome? (fun e =>
      if e.1 == a && e.2.1 == key then some e.2.2 else none) with
  | some r => return r
  | none =>
    let res ← try (if strong then deriveB a r else deriveA a r) catch _ => pure #[]
    invDCache.modify (·.push (a, key, res))
    return res

initialize invCache : IO.Ref (Array ((Name × Expr × Bool) × Option Expr)) ← IO.mkRef #[]

partial def invIntroGoal (g : MVarId) : MetaM (List MVarId) := do
  let t ← instantiateMVars (← g.getType)
  let some (_, r) := entailHead? t | return [g]
  if r.getAppFn.constName? == some ``HProp.hforall then
    match ← g.apply (← mkConstWithFreshMVarLevels ``HProp.himpl_hforall_r) with
    | [g1] =>
        let (_, g2) ← g1.intro `ivw
        invIntroGoal g2
    | _ => return [g]
  else if r.getAppFn.constName? == some ``HProp.hwand then
    match ← g.apply (← mkConstWithFreshMVarLevels ``HProp.himpl_hwand_r) with
    | [g1] => return [g1]
    | _ => return [g]
  else return [g]

def indCore (A M inst : Expr) : TacticM (Expr × List MVarId) := do
  let some (F, ta) ← functionalOf? A | throwError "ind: not a fixpoint"
  let aty ← inferType ta
  if aty.isAppOf ``Sum then throwError "ind: mutual"
  let some p := A.getAppFn.constName? | throwError "ind: head"
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let some ent := entries.find? (·.headFn == p) | throwError "ind: unfold"
  let some val := (← getConstInfo ent.lemmaName).value? (allowOpaque := true) | throwError "ind: value"
  let some un := val.find? (fun e => e.isAppOf `Bench.lfp_unfold) | throwError "ind: lfp"
  let hmono := un.getAppArgs.back!
  let tup := stripInj ta
  let X ← withLocalDeclD `b aty fun b => do
    let pm ← projMap tup b
    let P ← if tup == ta && pm.map (·.1) == A.getAppArgs then pure (mkAppN A.getAppFn (pm.map (·.2)))
      else mkAppM ``lfpG #[F, b]
    mkLambdaFVars #[b] (← mkAppM ``hwith #[P, M.beta #[b]])
  let hfold ← withLocalDeclD `a aty fun a => do
    mkLambdaFVars #[a] (mkAppN (mkConst `Bench.lfp_pre) #[inst, aty, F, hmono, a])
  let saved ← getGoals
  let hM ← indSetup F X aty 0 (some M)
  let obl ← getGoals
  setGoals saved
  return (← mkAppM ``lfpG_induct_with #[F, M, hmono, hfold, hM, ta], obl)

def proveInv (solve : Nat → TacticM Unit) (p : Name) (inv : Expr) (strong : Bool) :
    TacticM (Option Expr) :=
  withLemCache invCache (p, inv, strong) 2600 true do
  let pty := (← getConstInfo p).type
  let pf ← forallTelescope pty fun xs _ => do
    let pxs := mkAppN (mkConst p) xs
    let some (_, ta) ← functionalOf? pxs | throwError "inv: lfp"
    unless stripInj ta == ta do throwError "inv: group"
    let aty ← inferType ta
    let W := inv.beta xs
    let stmt ← mkAppM ``HProp.himpl #[pxs, W]
    let M ← withLocalDeclD `t aty fun t => do
      let pm ← projMap ta t
      unless pm.map (·.1) == xs do throwError "inv: args"
      mkLambdaFVars #[t] (W.replaceFVars xs (pm.map (·.2)))
    let (key, obl) ← indCore pxs M stmt.getAppArgs[0]!
    let mut gs : List MVarId := []
    for g in obl do
      gs := gs ++ (← invIntroGoal g)
    setGoals gs
    evalTactic (← `(tactic| (all_goals (try xsearch_distr)
                             all_goals (try apply Sep.Xsearch.hdisj_elim))))
    solve 8
    unless (← getUnsolvedGoals).isEmpty do throwError "inv: open"
    unless ← isDefEq (← inferType key) stmt do throwError "inv: type"
    let key ← mkExpectedTypeHint key stmt
    let pf ← instantiateMVars (← mkLambdaFVars xs key)
    if pf.hasMVar then throwError "inv: mvar"
    pure pf
  pure pf

def replaceAtomAlt (lhs rhs : Expr) (L : List Expr) (i : Nat) (pf B : Expr) :
    TacticM Unit := withMainContext do
  let g ← getMainGoal
  let gt ← instantiateMVars (← g.getType)
  let inst := gt.getAppArgs[0]!
  let D ← mkStarOf inst (L.eraseIdx i)
  match ← provePerm lhs (← mkAppM ``HProp.hstar #[L[i]!, D]) with
  | none => throwError "rep: perm"
  | some h1 =>
    let mv ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``HProp.himpl #[← mkAppM ``HProp.hstar #[B, D], rhs])
    let full ← mkAppM ``HProp.himpl_trans
      #[h1, ← mkAppM ``HProp.himpl_trans #[← mkAppM ``frame_l_of #[D, pf], mv]]
    unless ← isDefEq (← inferType full) gt do throwError "rep: mismatch"
    g.assign full
    replaceMainGoal [mv.mvarId!]

def specByRhs (W : Expr) (Rs : List Expr) : MetaM (Option (Expr × Expr)) := do
  let mut cur := W
  let mut pf ← mkAppM ``HProp.himpl_refl #[W]
  let mut ms : Array Expr := #[]
  while cur.getAppFn.constName? == some ``HProp.hforall do
    let J := cur.appArg!
    let jt ← whnf (← inferType J)
    unless jt.isForall do break
    let m ← mkFreshExprMVar jt.bindingDomain!
    pf ← mkAppM ``HProp.himpl_trans #[pf, ← mkAppM ``HProp.hforall_specialize #[m, J]]
    cur := (mkApp J m).headBeta
    ms := ms.push m
  if ms.isEmpty then return none
  let (_, B) := wandChain cur #[]
  for r in Rs do
    if r.hasExprMVar then continue
    let s ← saveState
    if ← (try isDefEq B r catch _ => pure false) then
      let ok ← ms.allM (fun m => do return !(← instantiateMVars m).hasExprMVar)
      if ok then
        return some (← instantiateMVars pf, ← instantiateMVars cur)
    s.restore
  return none

partial def stripForalls (e : Expr) : MetaM Expr := do
  if e.getAppFn.constName? == some ``HProp.hforall then
    let J := e.appArg!
    let jt ← whnf (← inferType J)
    unless jt.isForall do return e
    withLocalDeclD `sfv jt.bindingDomain! fun v => stripForalls (mkApp J v).headBeta
  else return e

def specAlt (lhs rhs : Expr) (L Rs : List Expr) (i : Nat) : TacticM Unit :=
  withMainContext do
    let some (pf, B) ← specByRhs L[i]! Rs | throwError "spec: none"
    replaceAtomAlt lhs rhs L i pf B

def isHwith (e : Expr) : Bool :=
  e.getAppFn.constName? == some ``hwith && e.getAppNumArgs == 3

def projPf (inst : Expr) (L : List Expr) (right : Nat) (allR : Bool := false) :
    MetaM (Expr × List Expr) := do
  match L with
  | [] => pure (← mkAppM ``HProp.himpl_refl #[mkApp (mkConst ``HProp.hempty) inst], [])
  | a :: rest =>
    let (pa, a') ←
      if isHwith a then
        let aa := a.getAppArgs
        if right == 0 || allR then pure (← mkAppM ``hwith_r #[aa[1]!, aa[2]!], aa[2]!)
        else pure (← mkAppM ``hwith_l #[aa[1]!, aa[2]!], aa[1]!)
      else pure (← mkAppM ``HProp.himpl_refl #[a], a)
    if rest.isEmpty then return (pa, [a'])
    let (pr, rest') ← projPf inst rest (if right == 0 then L.length + 1 else right - 1) allR
    return (← mkAppM ``HProp.himpl_frame_lr #[pa, pr], a' :: rest')

def hwithAlt (lhs rhs : Expr) (L : List Expr) (right : Nat) (allR : Bool := false) : TacticM Unit :=
  withMainContext do
    let g ← getMainGoal
    let gt ← instantiateMVars (← g.getType)
    let inst := gt.getAppArgs[0]!
    let (pp, L') ← projPf inst L right allR
    let src ← mkStarOf inst L
    let h1 ←
      if src == lhs then mkAppM ``HProp.himpl_refl #[lhs]
      else match ← provePerm lhs src with
        | some h => pure h
        | none => throwError "hw: perm"
    let mv ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``HProp.himpl #[← mkStarOf inst L', rhs])
    let full ← mkAppM ``HProp.himpl_trans
      #[h1, ← mkAppM ``HProp.himpl_trans #[pp, mv]]
    unless ← isDefEq (← inferType full) gt do throwError "hw: mismatch"
    g.assign full
    replaceMainGoal [mv.mvarId!]

def hwithAlts (lhs rhs : Expr) (L Rs : List Expr) : Array (Bool × TacticM Unit) :=
  if !L.any isHwith then #[] else
  let lefts := #[(false, hwithAlt lhs rhs L (L.length + 1))]
  let rights := ((List.range L.length).filter (fun i => isHwith L[i]!)).toArray.map
      (fun i => (false, hwithAlt lhs rhs L i))
  let hs := Rs.filterMap (·.getAppFn.constName?)
  let pref := L.any (fun e => isHwith e &&
    (e.getAppArgs[2]!.find? (fun s => match s.getAppFn.constName? with
      | some n => hs.contains n
      | none => false)).isSome)
  let all := if rights.size ≥ 2 then #[(false, hwithAlt lhs rhs L (L.length + 1) true)] else #[]
  let allPref := L.all (fun e => !isHwith e || match e.getAppArgs[2]!.getAppFn.constName? with
    | some n => hs.contains n
    | none => false)
  if allPref then all ++ rights ++ lefts
  else if pref then rights ++ lefts ++ all else lefts ++ rights ++ all

def specAlts (lhs rhs : Expr) (L Rs : List Expr) : Array (Bool × TacticM Unit) :=
  ((List.range L.length).filter (fun i =>
    L[i]!.getAppFn.constName? == some ``HProp.hforall)).toArray.map
      (fun i => (false, specAlt lhs rhs L Rs i))

def invUseAlt (solve : Nat → TacticM Unit) (lhs rhs : Expr) (L Rs : List Expr)
    (i : Nat) (a : Name) (inv : Expr) (strong : Bool) : TacticM Unit :=
  withMainContext do
    let A := L[i]!
    let W0 := (inv.beta A.getAppArgs).headBeta
    let (ants0, _) := wandChain (← stripForalls W0) #[]
    let locs := ((L.eraseIdx i) ++ [A]).foldl (fun acc e => ptoLocsOf e acc) #[]
    unless ants0.any (fun an => (flatStar an #[]).any (fun b =>
        b.getAppArgs.any (fun v => locs.contains v))) do
      throwError "inv: irrelevant"
    let some lem ← proveInv solve a inv strong | throwError "inv: lemma"
    let pf := mkAppN lem A.getAppArgs
    let W := (inv.beta A.getAppArgs).headBeta
    match ← specByRhs W Rs with
    | some (pf2, B) =>
        replaceAtomAlt lhs rhs L i (← mkAppM ``HProp.himpl_trans #[pf, pf2]) B
    | none =>
        if W.getAppFn.constName? == some ``HProp.hforall then throwError "inv: spec"
        replaceAtomAlt lhs rhs L i pf W

def absentPreds (heads : Array Name) (atoms : List Expr) (e : Expr) : Nat :=
  let hs := atoms.filterMap (·.getAppFn.constName?)
  let ab := (collectOccs heads e #[]).filterMap (fun o => match o.getAppFn.constName? with
    | some c => if hs.contains c then none else some c
    | none => none)
  (ab.foldl (fun (acc : Array Name) c => if acc.contains c then acc else acc.push c) #[]).size

partial def branchScoreD (heads : Array Name) (atoms : List Expr) (e : Expr) : Int :=
  if isDisj e then
    let a := e.getAppArgs
    max (branchScoreD heads atoms a[a.size-2]!) (branchScoreD heads atoms a[a.size-1]!)
  else branchScore heads atoms e

partial def absentPredsD (heads : Array Name) (atoms : List Expr) (e : Expr) : Nat :=
  if isDisj e then
    let a := e.getAppArgs
    min (absentPredsD heads atoms a[a.size-2]!) (absentPredsD heads atoms a[a.size-1]!)
  else absentPreds heads atoms e

def invAlts (solve : Nat → TacticM Unit) (heads : Array Name) (lhs rhs : Expr)
    (L Rs : List Expr) : TacticM (Array (Bool × TacticM Unit)) := do
  let mut out : Array (Bool × TacticM Unit) := #[]
  if L.any (fun e => (wandParts? e).isSome || isHwith e
      || e.getAppFn.constName? == some ``HProp.hforall) then return out
  for i in [0 : L.length] do
    let some a := L[i]!.getAppFn.constName? | continue
    unless heads.contains a do continue
    unless ← isRecPred a do continue
    let mut seen : Array Name := #[]
    for rr in Rs do
      let some r := rr.getAppFn.constName? | continue
      if r == a || !heads.contains r || seen.contains r then continue
      seen := seen.push r
      let strong := !(← isRecPred r)
      for inv in ← deriveInv a r strong do
        out := out.push (false, invUseAlt solve lhs rhs L Rs i a inv strong)
  return out

initialize failMemo : IO.Ref (Std.HashMap Expr (Array (Nat × Array FVarId × Nat × Nat × Nat))) ←
  IO.mkRef {}

def failKey (fuel : Nat) : TacticM (Option (Expr × Array FVarId × Nat × Nat × Nat)) := do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  if t.hasMVar then return none
  let fs := (← g.getDecl).lctx.foldl (fun acc d =>
    if d.isImplementationDetail then acc else acc.push d.fvarId) #[]
  return some (t, fs, fuel, ← forcedDepth.get, 0)

def failSeen (k : Expr × Array FVarId × Nat × Nat × Nat) : BaseIO Bool := do
  let (t, fs, fuel, a, b) := k
  match (← failMemo.get)[t]? with
  | some arr => return arr.any (fun (f, fs', a', b', c') => f ≥ fuel && fs' == fs && a' == a && b' * 1000 + c' == b)
  | none => return false

def failAdd (k : Expr × Array FVarId × Nat × Nat × Nat) : TacticM Unit := do
  if (← vclock) > (← searchDeadline.get) || (← pastGlobal) || (← searchNodes.get) == 0 then
    return
  let (t, fs, fuel, a, b) := k
  failMemo.modify fun m => m.insert t ((m.getD t #[]).push (fuel, fs, a, b / 1000, b % 1000))

def goalSig (g : MVarId) : MetaM (Expr × Array FVarId) := do
  let t ← instantiateMVars (← g.getType)
  let fs := (← g.getDecl).lctx.foldl (fun acc d => acc.push d.fvarId) #[]
  return (t, fs)

def allTry (t : TacticM Unit) : TacticM Unit := do
  let mut acc : List MVarId := []
  for g in ← getGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    let st ← saveState
    try t catch _ => st.restore
    acc := acc ++ (← getUnsolvedGoals)
  setGoals acc

def cleanAll : TacticM Unit := allTry Sep.Xsimpl.xsimplClean

def normGoals : TacticM Unit := do
  allTry distrCore
  allTry exwitCore
  Sep.Xsimpl.xsimplDriver none
  cleanAll
  let mut acc : List MVarId := []
  for g in ← getUnsolvedGoals do
    let s0 ← goalSig g
    let st ← saveState
    let g1 ← try fastSubstVars g catch _ => do st.restore; pure g
    let same ← if g1 == g then pure true else pure ((← goalSig g1) == s0)
    setGoals [g1]
    unless same do
      Sep.Xsimpl.xsimplDriver none
      cleanAll
    acc := acc ++ (← getUnsolvedGoals)
  setGoals acc
  evalTactic (← `(tactic| xsearch_pure))

def cmFind : TacticM Bool := withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (lhs, rhs) := entailHead? t | return false
  unless t.getAppFn.constName? == some ``HProp.himpl do return false
  if t.hasExprMVar then return false
  unless ← isDefEq (mkApp (mkConst ``Params.val) t.getAppArgs[0]!) (mkConst ``Int) do
    return false
  let mut vars : Array FVarId := #[]
  let mut ptrs : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isConstOf ``Nat then
      vars := vars.push d.fvarId
      ptrs := ptrs.push d.toExpr
    else if ty.isConstOf ``Int then vars := vars.push d.fvarId
    else return false
  let tbl ← cmTable
  let off := min 8 (tbl.foldl (fun a (_, _, r) => cmMaxOff r a) (cmMaxOff t 0))
  let items := cmItems lhs
  let pidx := (List.range items.size).toArray.filter (fun i => (cmUnfold tbl items[i]!).isSome)
  let lvOf (pol : Nat → Nat) : Array Nat := (List.range items.size).toArray.map pol
  let mut pols : Array (Array Nat) := #[lvOf (fun _ => 1), lvOf (fun _ => 0), lvOf (fun _ => 2)]
  for i in pidx do
    pols := pols.push (lvOf (fun j => if j == i then 0 else 1))
    pols := pols.push (lvOf (fun j => if j == i then 2 else 1))
  for i in pidx do
    pols := pols.push (lvOf (fun j => if j == i || !pidx.contains j then 1 else 0))
  let nil := mkNatLit 0
  let t0 ← vclock
  cmSteps.set 400000
  let mut stCache : Array (Option (Array (Option CmPrepped))) := Array.replicate pols.size none
  let rvs := cmFVars rhs #[]
  let mut seen : Std.HashSet (CmHeap × Array (Option Int) × Array Int) := {}
  let mut seenIso : Std.HashSet (Array (Nat × Int × Nat × Int) × Array (Option (Nat × Int)) × Array (Nat × Int)) := {}
  let mut stSeen : Std.HashSet (Array Expr) := {}
  let prog0 := cmCompileTbl tbl
  let au := cmAddrUse prog0 (tbl.map (·.2.1))
  let prog := prog0.map (cmMark au)
  let rhsN := cmMark au (cmCompile tbl ((List.range vars.size).foldl (fun m i => m.insert vars[i]! i) {})
    vars.size rhs)
  for round in [0 : 3] do
    for pi in [0 : pols.size] do
      if (← vclock) > t0 + 60 then return false
      if (← cmSteps.get) == 0 then return false
      let sts ← match stCache[pi]! with
        | some s => pure s
        | none =>
          let mut sts : Array CmSt := #[{}]
          let mut ok := true
          for i in [0 : items.size] do
            match ← cmGen tbl (pols[pi]!)[i]! 0 items[i]! sts with
            | some s => sts := s.extract 0 48
            | none => ok := false
          let s := if ok then sts else #[]
          let mut s' : Array (Option CmPrepped) := #[]
          for st in s do
            let ck := cmCanon vars st
            unless stSeen.contains ck do
              stSeen := stSeen.insert ck
              s' := s'.push (cmPrepare vars ptrs rvs st)
          stCache := stCache.set! pi (some s')
          pure s'
      for sp? in sts do
        let some sp := sp? | return false
        let pre := sp.pre
        let some atomsI := (if round == 2 then sp.atoms2 else sp.atoms1) | return false
        let mut cands : Array (Nat × Option Nat × Array (Sum Nat Int)) := #[]
        if round == 0 then cands := #[(pre.base.size + 1, none, #[])]
        else
          let fb := sp.fb
          for hi : i in [0 : atomsI.size] do
            for hj : j in [i + 1 : atomsI.size] do
              if (round == 1 || j ≥ ptrs.size + 1) && !cmSameI pre.base atomsI[i] atomsI[j]
                  && !cmDead fb pre atomsI[i] atomsI[j] then
                cands := cands.push (cmMergeOf fb pre atomsI[i] atomsI[j])
        for (mi, mj, extra) in cands do
          if (← vclock) > t0 + 60 then return false
          match cmSolveM pre mi mj extra with
          | none => pure ()
          | some (envA, h, vals, k) =>
            let rv := sp.rvIdx.map (fun i? => i?.bind (fun i => envA[i]?.join))
            let key := (h, rv, vals)
            if seen.contains key then continue
            seen := seen.insert key
            let iso := cmIsoKey k h rv vals
            if seenIso.contains iso then continue
            seenIso := seenIso.insert iso
            let rem ← cmSteps.get
            let bud := min rem 5000
            let ev : CmEv := { prog, off, gvals := envA.filterMap id }
            let cnt0 ← cmCounter.get
            let ((found, inc), (left, cnt)) :=
              (cmConsKI ev ((envA.extract 0 vars.size).map (·.map ((0 : Nat), ·))) {} #[] (2 * h.size + 8)
                rhsN h).run (bud, cnt0)
            cmCounter.set cnt
            cmSteps.set (rem - (bud - left))
            if !inc && !found then return true
  return false

def cmNeg (p : Expr) : MetaM (Option (Array Expr)) := do
  let num := fun (t : Expr) => t.isConstOf ``Nat || t.isConstOf ``Int
  match p.getAppFnArgs with
  | (``False, _) => return some #[]
  | (``Ne, #[t, a, b]) => if num t then return some #[← mkEq a b] else return none
  | (``Not, #[q]) => match q.eq? with
    | some (t, a, b) => if num t then return some #[← mkEq a b] else return none
    | none => return none
  | (``Eq, #[t, a, b]) => if num t then return some #[← mkAppM ``Ne #[a, b]] else return none
  | (``LE.le, #[t, _, a, b]) => if num t then return some #[← mkAppM ``LT.lt #[b, a]] else return none
  | (``LT.lt, #[t, _, a, b]) => if num t then return some #[← mkAppM ``LE.le #[b, a]] else return none
  | (``GE.ge, #[t, _, a, b]) => if num t then return some #[← mkAppM ``LT.lt #[a, b]] else return none
  | (``GT.gt, #[t, _, a, b]) => if num t then return some #[← mkAppM ``LE.le #[a, b]] else return none
  | _ => return none

def cmFact (t : Expr) : Bool :=
  match t.getAppFnArgs with
  | (``Eq, #[ty, _, _]) | (``Ne, #[ty, _, _]) => ty.isConstOf ``Nat || ty.isConstOf ``Int
  | (``LE.le, _) | (``LT.lt, _) | (``GE.ge, _) | (``GT.gt, _) | (``Not, _) | (``And, _) | (``Or, _)
  | (``False, _) => true
  | _ => t.isForall && !t.bindingBody!.hasLooseBVars

def cmPureModel (facts : Array Expr) : MetaM Bool := do
  let mut vars : Array FVarId := #[]
  for f in facts.foldl (fun acc p => cmFVars p acc) #[] do
    let ty ← instantiateMVars (← f.getType)
    if ty.isConstOf ``Nat || ty.isConstOf ``Int then vars := vars.push f
  let st : CmSt := { pures := facts }
  let some pre := cmPrep vars st (cmBase vars st) | return false
  return (cmSolveM pre pre.base.size none #[]).isSome

partial def cmPureRefuted (p : Expr) : MetaM Bool := do
  let p ← instantiateMVars p
  if let some (a, b) := p.and? then return (← cmPureRefuted a) || (← cmPureRefuted b)
  let some neg ← cmNeg p | return false
  let mut facts : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if cmFact ty && (← isProp ty) then facts := facts.push ty
  cmPureModel (facts ++ neg)

elab_rules : tactic
  | `(tactic| xsearch_omega) => do
    let g ← getMainGoal
    if ← g.withContext (do cmPureRefuted (← g.getType)) then
      throwError "xsearch_omega: not entailed"
    evalTactic (← `(tactic| omega))

def stmtRefuted (xs : Array Expr) (lhs rhs : Expr) : TacticM Bool := do
  let stmt ← mkForallFVars xs (← mkAppM ``HProp.himpl #[lhs, rhs])
  if stmt.hasMVar then return false
  let s ← saveState
  let r ← try
      withLCtx {} #[] do
        forallTelescope stmt fun _ body => do
          let mv ← mkFreshExprMVar body
          setGoals [mv.mvarId!]
          cmFind
    catch _ => pure false
  s.restore
  return r

initialize cmPending : IO.Ref Bool ← IO.mkRef false

def goalRefuted : TacticM Bool := withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (lhs, rhs) := entailHead? t | return false
  if t.hasExprMVar then return false
  let inst := t.getAppArgs[0]!
  let mut vs : Array Expr := #[]
  let mut ps : Array Expr := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isConstOf ``Nat || ty.isConstOf ``Int then vs := vs.push d.toExpr
    else if ← isProp ty then
      match ty.getAppFn.constName? with
      | some ``Eq | some ``Ne | some ``Not => ps := ps.push ty
      | _ => return false
    else return false
  let mut L := lhs
  for p in ps do
    L ← mkAppM ``HProp.hstar #[← mkAppOptM ``HProp.hpure #[inst, p], L]
  stmtRefuted (vs.filter fun v => L.containsFVar v.fvarId! || rhs.containsFVar v.fvarId!) L rhs

def cmCheckPending : TacticM Unit := do
  if ← cmPending.get then
    cmPending.set false
    if ← goalRefuted then throwError "xsearch: countermodel"

initialize minCellCache : IO.Ref (Array (Name × Nat)) ← IO.mkRef #[]

partial def minCellsE (tbl : Array (Name × Nat)) (e : Expr) : Nat :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) => minCellsE tbl a + minCellsE tbl b
  | (``HProp.hsingle, #[_, _, _]) => 1
  | (``HProp.hexists, #[_, _, .lam _ _ b _]) => minCellsE tbl b
  | _ =>
    if (isHorConst e || e.getAppFn.constName? == some ``hdisj) && e.getAppNumArgs ≥ 2 then
      let xs := e.getAppArgs
      min (minCellsE tbl xs[xs.size - 2]!) (minCellsE tbl xs[xs.size - 1]!)
    else match e.getAppFn.constName? with
      | some nm => ((tbl.find? (·.1 == nm)).map (·.2)).getD 0
      | none => 0

def minCellsTbl : MetaM (Array (Name × Nat)) := do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let c ← minCellCache.get
  if entries.all (fun e => c.any (·.1 == e.headFn)) then return c
  let mut bodies : Array (Name × Expr) := #[]
  for e in entries do
    if bodies.any (·.1 == e.headFn) then continue
    let mut b := (← getConstInfo e.lemmaName).type
    while b.isForall do b := b.bindingBody!
    match b.eq? with
    | some (_, l, r) =>
        if l.getAppFn.constName? == some e.headFn then bodies := bodies.push (e.headFn, r)
        else bodies := bodies.push (e.headFn, mkConst `none)
    | none => bodies := bodies.push (e.headFn, mkConst `none)
  let inf := 1000000
  let mut tbl := bodies.map (fun (n, _) => (n, inf))
  for _ in [0 : bodies.size + 1] do
    tbl := bodies.map (fun (n, r) => (n, min inf (minCellsE tbl r)))
  let res := tbl.map (fun (n, v) => (n, if v ≥ inf then 0 else v))
  minCellCache.set (res ++ c.filter (fun e => !res.any (·.1 == e.1)))
  minCellCache.get

def exactCells? (atoms : List Expr) : Option Nat :=
  atoms.foldl (fun acc a => acc.bind fun n =>
    match a.getAppFn.constName? with
    | some ``HProp.hsingle => some (n + 1)
    | some ``HProp.hpure => some n
    | some ``HProp.hempty => some n
    | _ => none) (some 0)

def sizeGap (lhs rhs : Expr) : MetaM Bool := do
  let el := exactCells? (Sep.Xsimpl.parseHstar lhs)
  let er := exactCells? (Sep.Xsimpl.parseHstar rhs)
  let tbl ← minCellsTbl
  let ra := (Sep.Xsimpl.parseHstar rhs).filterMap (fun a =>
    if a.getAppFn.constName? == some ``HProp.hsingle then a.getAppArgs[1]? else none)
  if (List.range ra.length).any (fun i => (ra.drop (i + 1)).contains ra[i]!) then return true
  if let some n := el then
    if minCellsE tbl rhs > n then return true
  if let some m := er then
    if minCellsE tbl lhs > m then return true
  return false

partial def indReflConj (P : Expr) : MetaM Expr := do
  match P.getAppFnArgs with
  | (``And, #[a, b]) => return mkApp4 (mkConst ``And.intro) a b (← indReflConj a) (← indReflConj b)
  | (``Eq, #[_, l, r]) =>
    unless ← isDefEq l r do throwError "ind: guard"
    mkExpectedTypeHint (← mkEqRefl l) P
  | _ => throwError "ind: guard shape"

def indAlt (A rhs : Expr) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let gt ← instantiateMVars (← g.getType)
  if gt.hasExprMVar then throwError "ind: mvars"
  let some (_, ta) ← functionalOf? A | throwError "ind: not a fixpoint"
  let aty ← inferType ta
  let tup := stripInj ta
  let rAtoms := (Sep.Xsimpl.parseHstar rhs).filter (fun a => !a.isAppOf ``HProp.hpure)
  let posGen := match rAtoms with
    | [r] => r.getAppNumArgs == A.getAppNumArgs && r.getAppArgs == A.getAppArgs && r.getAppFn != A.getAppFn
    | _ => false
  let M ← withLocalDeclD `t aty fun t => do
    let pm ← projMap tup t
    if posGen then
      let r := rAtoms.head!
      return ← mkLambdaFVars #[t] (mkAppN r.getAppFn (pm.map (·.2)))
    let mut subF : Array Expr := #[]
    let mut subV : Array Expr := #[]
    let mut eqs : Array (Expr × Expr) := #[]
    for (e, pr) in pm do
      let e : Expr := e
      if e.isFVar && !subF.contains e then
        subF := subF.push e
        subV := subV.push pr
      else eqs := eqs.push (pr, e)
    let R := rhs.replaceFVars subF subV
    let gs ← eqs.mapM fun (pr, e) => mkEq pr (Expr.replaceFVars e subF subV)
    let body ← if h : gs.size = 0 then pure R else do
      let mut c := gs[gs.size - 1]
      for i in [0 : gs.size - 1] do c ← mkAppM ``And #[gs[gs.size - 2 - i]!, c]
      mkAppM ``hguard #[c, R]
    mkLambdaFVars #[t] body
  let saved ← getGoals
  let (key, obl) ← indCore A M gt.getAppArgs[0]!
  let mut out : List MVarId := []
  for o in obl do
    setGoals [o]
    let t ← instantiateMVars (← o.getType)
    let mut cur : List MVarId := [o]
    if let some (_, r) := entailHead? t then
      if r.isAppOf ``hguard then
        let gs ← o.apply (← mkConstWithFreshMVarLevels ``hguard_intro)
        cur := []
        for g2 in gs do
          let (_, g3) ← g2.intro1P
          setGoals [g3]
          evalTactic (← `(tactic| try xsearch_subst))
          cur := cur ++ (← getGoals)
    out := out ++ cur
  let kt ← instantiateMVars (← inferType key)
  let some (_, kr) := entailHead? kt | throwError "ind: key"
  let kr ← whnfCore (← instantiateMVars kr)
  let close ← if kr.isAppOf ``hguard then do
      let pf ← indReflConj kr.appFn!.appArg!
      mkAppM ``HProp.himpl_trans #[key, ← mkAppOptM ``hguard_elim #[none, kr.appFn!.appArg!, kr.appArg!, pf]]
    else pure key
  unless ← isDefEq (← inferType close) gt do throwError "ind: type"
  g.assign close
  setGoals (saved.erase g ++ out)

def headIdxOf (p : Name) : MetaM Nat := do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let some ent := entries.find? (·.headFn == p) | return 0
  forallTelescopeReducing (← getConstInfo ent.lemmaName).type fun xs concl => do
    let some (_, _, body) := concl.eq? | return 0
    let some e := body.find? (fun e => e.isAppOfArity ``HProp.hsingle 3 && xs.contains e.appFn!.appArg!)
      | return 0
    return (xs.idxOf e.appFn!.appArg!)

def exArgMatch (tgt r l : Expr) : Option (Option Expr) :=
  if r == tgt then some (some l)
  else if !r.hasLooseBVars then (if r == l then some none else none)
  else if r.isAppOfArity ``HAdd.hAdd 6 && l.isAppOfArity ``HAdd.hAdd 6
      && r.appArg! == l.appArg! && r.appFn!.appArg! == tgt then
    some (some l.appFn!.appArg!)
  else if r.getAppFn.isBVar || r.isBVar then some none
  else if r.hasLooseBVar tgt.bvarIdx! then none
  else some none

def exVotes (L : List Expr) (D : Expr) : Array Expr := Id.run do
  let (body, depth) := exPeel D
  if depth == 0 then return #[]
  let tgt : Expr := .bvar (depth - 1)
  let R := Sep.Xsimpl.parseHstar body
  unless R.any (fun it => it.isAppOf ``HProp.hsingle
      && it.getAppArgs[it.getAppNumArgs - 2]? == some tgt) do return #[]
  let mut votes : Array (Expr × Nat) := #[]
  for r in R do
    unless r.hasLooseBVar (depth - 1) do continue
    let some hr := r.getAppFn.constName? | continue
    let ra := r.getAppArgs
    for l in L do
      unless l.getAppFn.constName? == some hr && l.getAppNumArgs == ra.size do continue
      let la := l.getAppArgs
      let mut w : Option Expr := none
      let mut ok := true
      for i in [0 : ra.size] do
        match exArgMatch tgt ra[i]! la[i]! with
        | none => ok := false
        | some none => pure ()
        | some (some c) =>
          if c.hasLooseBVars then ok := false
          else match w with
            | some w0 => if w0 != c then ok := false
            | none => w := some c
        unless ok do break
      if ok then
        if let some c := w then
          votes := match votes.findIdx? (·.1 == c) with
            | some j => votes.modify j (fun (e, k) => (e, k + 1))
            | none => votes.push (c, 1)
  return (votes.qsort (fun a b => a.2 > b.2)).map (·.1)

def exChoice (side : Name) (w : Expr) : TacticM Unit := do
  applyConstT side
  withMainContext do
  let g ← getMainGoal
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``HProp.himpl_hexists_r)
  let mut rem : List MVarId := []
  for gg in gs do
    if ← gg.isAssigned then continue
    if ← isProp (← gg.getType) then rem := rem ++ [gg]
    else unless ← isDefEq (mkMVar gg) w do throwError "exc"
  replaceMainGoal rem
  evalTactic (← `(tactic| try beta_reduce))

mutual

partial def searchSolve (fuel : Nat) : TacticM Unit := do
  checkDeadline
  normGoals
  let gs ← getUnsolvedGoals
  if gs.isEmpty then return
  if fuel == 0 then throwError "xsearch: depth exhausted"
  for g in gs do
    if ← g.isAssigned then continue
    setGoals [g]
    branchGoal fuel
    unless (← getUnsolvedGoals).isEmpty do
      throwError "xsearch: subgoal remained"
  setGoals []

partial def branchGoal (fuel : Nat) : TacticM Unit := do
  checkDeadline
  let fk ← failKey fuel
  if let some k := fk then
    if ← failSeen k then throwError "xsearch: known failure"
  evalTactic (← `(tactic| try xsearch_distr))
  let btg ← instantiateMVars (← (← getMainGoal).getType)
  if (btg.find? (fun s => s.getAppFn.constName? == some ``hpack)).isSome
      && (btg.find? (fun s =>
        s.getAppFn.constName? == some ``HProp.hwand)).isNone then
    let _ ← simpOnlyTarget #[``hpack_eq]
  unless (← hasLocLocs).isEmpty do
    evalTactic (← `(tactic| try xsearch_hfacts))
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (lhs, rhs) := entailHead? t | throwError "xsearch: not an entailment"
  if ← sizeGap lhs rhs then throwError "xsearch: size gap"
  cmCheckPending
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let heads := entries.map (·.headFn)
  let mut alts : Array (Bool × TacticM Unit) := #[]
  if isDisj lhs then
    alts := alts.push (false, applyConstT ``hdisj_elim)
  else if isDisj rhs then
    let args := rhs.getAppArgs
    let n := args.size
    let atoms := Sep.Xsimpl.parseHstar lhs
    let sa := branchScoreD heads atoms args[n-2]!
    let sb := branchScoreD heads atoms args[n-1]!
    let l : TacticM Unit := applyConstT ``hdisj_left
    let r : TacticM Unit := applyConstT ``hdisj_right
    let side := fun (nm : Name) (D : Expr) (plain : TacticM Unit) =>
      let ws := if t.hasExprMVar then #[] else exVotes atoms D
      if ws.size ≥ 2 then ws.map (fun w => (false, exChoice nm w)) |>.push (false, plain)
      else #[(false, plain)]
    let la := side ``hdisj_left args[n-2]! l
    let ra := side ``hdisj_right args[n-1]! r
    if sa > sb || (sa == sb && absentPredsD heads atoms args[n-2]!
        ≤ absentPredsD heads atoms args[n-1]!) then alts := la ++ ra
    else alts := ra ++ la
  else
    let L := Sep.Xsimpl.parseHstar lhs
    let Rs := Sep.Xsimpl.parseHstar rhs
    let ptoLocs := ptoLocsOf lhs #[]
    let occsR := collectOccs heads rhs #[]
    let mut forced : Array Expr := #[]
    for o in occsR do
      let hi ←
        match o.getAppFn.constName? with
        | some nm => headIdxOf nm
        | none => pure 0
      match o.getAppArgs[hi]? with
      | some a => if ptoLocs.any (· == a) then forced := forced.push o
      | none => pure ()
    let ivs ← if fuel ≥ 36 && !t.hasExprMVar then invAlts searchSolve heads lhs rhs L Rs
      else pure #[]
    for i in [0 : L.length] do
      match wandParts? L[i]! with
      | none => pure ()
      | some (A, _) =>
        alts := alts.push (false, wandAlt lhs rhs L i)
        let As := Sep.Xsimpl.parseHstar A
        if As.length ≥ 1 && As.length < L.length then
          let mut ks : List Nat := []
          let mut okS := true
          let allPure := As.all (fun aa =>
            aa.getAppFn.constName? == some ``HProp.hpure)
          for aa in As do
            if aa.getAppFn.constName? == some ``HProp.hpure then continue
            match (List.range L.length).find? (fun m =>
                m != i && !ks.contains m && L[m]! == aa) with
            | some m => ks := ks ++ [m]
            | none => okS := false
          if okS && (!ks.isEmpty || allPure) && ks.length + 1 < L.length then
            alts := alts.push (false, wandAltS lhs rhs L i ks)
    let fdeep := (← forcedDepth.get) ≥ 6
    for o in forced do
      unless fdeep do alts := alts.push (true, rewriteOcc entries o)
    let lhsOccs := collectOccs heads lhs #[]
    for o in lhsOccs do
      match o.getAppFn.constName? with
      | some nm =>
          if ← isFlatPred nm then alts := alts.push (false, rewriteOcc entries o)
      | none => pure ()
    let mut late : Array (Bool × TacticM Unit) := #[]
    for o in lhsOccs do
      match o.getAppFn.constName? with
      | some nm =>
          if !(← isFlatPred nm) && !(← isRecPred nm) then
            late := late.push (false, rewriteOcc entries o)
      | none => pure ()
    let rwEarly := forced.isEmpty && !ptoLocs.isEmpty
    alts := alts ++ (if rwEarly then occsR.map (fun o => (false, rewriteOcc entries o))
      else #[]) ++ late
    let Lnp := L.filter (fun a => !a.isAppOf ``HProp.hpure)
    let inds : Array (Bool × TacticM Unit) := match Lnp with
      | [A] => if (A.getAppFn.constName?.map heads.contains).getD false
          && occsR.any (fun o => o.getAppFn != A.getAppFn)
          then #[(false, indAlt A rhs)] else #[]
      | _ => #[]
    let pre := (← forallAlts lhs rhs L) ++ hwithAlts lhs rhs L Rs ++ specAlts lhs rhs L Rs ++ ivs
    let early ← if t.hasExprMVar then pure #[] else earlyLhsOccs entries heads lhs rhs
    alts := (early.map (fun o => (false, rewriteOcc entries o))) ++ pre ++ inds ++ alts
    if forced.isEmpty then
      unless rwEarly do
        for o in occsR do
          alts := alts.push (false, rewriteOcc entries o)
      for o in collectOccs heads lhs #[] do
        unless early.contains o do alts := alts.push (false, rewriteOcc entries o)
  for (ai, (isF, alt)) in alts.zipIdx.map (fun (x,i) => (i,x)) do
    checkDeadline
    let s ← saveState
    let oldDl ← searchDeadline.get
    let sliced := isF && (← forcedDepth.get) == 0 && ai + 1 < alts.size
    if isF then forcedDepth.modify (· + 1)
    if sliced then
      let now ← vclock
      let gd ← globalDeadline.get
      let slice := if gd > now then (gd - now) / 2 else 0
      searchDeadline.set (min oldDl (now + max (min slice 1500) 600))
    try
      searchNodes.modify (fun n => n - 1)
      alt
      cmPending.set sliced
      searchSolve (fuel - 1)
      cmPending.set false
      if isF then forcedDepth.modify (fun k => k - 1)
      if sliced then searchDeadline.set oldDl
      return
    catch _ =>
      cmPending.set false
      if isF then forcedDepth.modify (fun k => k - 1)
      if sliced then searchDeadline.set oldDl
      s.restore
  if let some k := fk then failAdd k
  throwError "xsearch: no alternative succeeded"

end

def arIntT : Expr := mkConst ``Int

partial def arIntProp (c : Expr) : Bool :=
  match c.getAppFnArgs with
  | (``Eq, #[ty, _, _]) => ty == arIntT
  | (``Ne, #[ty, _, _]) => ty == arIntT
  | (``LE.le, #[ty, _, _, _]) => ty == arIntT
  | (``LT.lt, #[ty, _, _, _]) => ty == arIntT
  | (``Not, #[p]) => arIntProp p
  | (``Or, #[a, b]) => arIntProp a && arIntProp b
  | (``And, #[a, b]) => arIntProp a && arIntProp b
  | _ => false

structure ArPiece where
  cell : Bool
  len : Expr
  lo : Int := 0
  deriving Inhabited

initialize arLitCache : IO.Ref (Std.HashMap Int Expr) ← IO.mkRef {}
initialize arOpCache : IO.Ref (Std.HashMap (Name × Expr) Expr) ← IO.mkRef {}

def arIntLit (v : Int) : MetaM Expr := do
  if let some e := (← arLitCache.get)[v]? then return e
  let e ← mkAppOptM ``OfNat.ofNat #[arIntT, mkRawNatLit v.natAbs, none]
  let e ← if v < 0 then mkAppM ``Neg.neg #[e] else pure e
  let e ← instantiateMVars e
  unless e.hasMVar do arLitCache.modify (·.insert v e)
  return e

def arBin (op : Name) (a b : Expr) : MetaM Expr := do
  let ty ← instantiateMVars (← inferType a)
  if ty.hasFVar || ty.hasMVar then return ← mkAppM op #[a, b]
  if let some f := (← arOpCache.get)[(op, ty)]? then return mkApp2 f a b
  let e ← instantiateMVars (← mkAppM op #[a, b])
  let f := e.appFn!.appFn!
  unless f.hasFVar || f.hasMVar do arOpCache.modify (·.insert (op, ty) f)
  return e

def arAdd (a b : Expr) : MetaM Expr := arBin ``HAdd.hAdd a b
def arSub (a b : Expr) : MetaM Expr := arBin ``HSub.hSub a b
def arEq (a b : Expr) : MetaM Expr := arBin ``Eq a b
def arLe (a b : Expr) : MetaM Expr := arBin ``LE.le a b

def arExists (inst : Expr) (vs : Array Expr) (body : Expr) : MetaM Expr := do
  let mut acc := body
  for i in [0 : vs.size] do
    let v := vs[vs.size - 1 - i]!
    let lam ← mkLambdaFVars #[v] acc
    acc ← mkAppOptM ``HProp.hexists #[inst, ← inferType v, lam]
  return acc

def arClearProps (g : MVarId) : MetaM MVarId := g.withContext do
  let mut lctx ← getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    if ← isProp (← instantiateMVars d.type) then lctx := lctx.erase d.fvarId
  let m ← withLCtx lctx (← getLocalInstances) (mkFreshExprSyntheticOpaqueMVar (← g.getType))
  g.assign m
  return m.mvarId!

def arTrim (g : MVarId) (closure : Bool := true) : MetaM MVarId := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let mut lctx ← getLCtx
  let mut props : Array (LocalDecl × Array FVarId) := #[]
  let mut changed := false
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ← isProp ty then props := props.push (d, (Lean.collectFVars {} ty).fvarIds)
  let mut vars := (Lean.collectFVars {} t).fvarIds
  let mut grew := closure
  while grew do
    grew := false
    for (_, fs) in props do
      if fs.any vars.contains && !fs.all vars.contains then
        for f in fs do
          unless vars.contains f do vars := vars.push f
        grew := true
  for (d, fs) in props do
    unless (if closure then fs.any vars.contains else fs.all vars.contains) || fs.isEmpty do
      lctx := lctx.erase d.fvarId
      changed := true
  unless changed do return g
  let m ← withLCtx lctx (← getLocalInstances) (mkFreshExprSyntheticOpaqueMVar t)
  g.assign m
  return m.mvarId!

partial def arLinI (e : Expr) : Array (Expr × Int) × Int :=
  let merge := fun (a b : Array (Expr × Int)) (s : Int) => Id.run do
    let mut r := a
    for (t, c) in b do
      match r.findIdx? (·.1 == t) with
      | some i => r := r.set! i (t, r[i]!.2 + s * c)
      | none => r := r.push (t, s * c)
    return r.filter (·.2 != 0)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[ty, _, _, _, a, b]) =>
      if ty != arIntT && ty != mkConst ``Nat then (#[(e, 1)], 0) else
      let (x, c) := arLinI a
      let (y, d) := arLinI b
      (merge x y 1, c + d)
  | (``HSub.hSub, #[ty, _, _, _, a, b]) =>
      if ty != arIntT then (#[(e, 1)], 0) else
      let (x, c) := arLinI a
      let (y, d) := arLinI b
      (merge x y (-1), c - d)
  | (``OfNat.ofNat, #[ty, l, _]) =>
      match l with
      | .lit (.natVal v) => if ty == arIntT || ty == mkConst ``Nat then (#[], v) else (#[(e, 1)], 0)
      | _ => (#[(e, 1)], 0)
  | _ => (#[(e, 1)], 0)

def arLinDiff (a b : Expr) : Array (Expr × Int) × Int :=
  let (ts, k) := arLinI a
  let (us, j) := arLinI b
  let d := us.foldl (fun acc (t, c) => match acc.findIdx? (·.1 == t) with
    | some i => acc.set! i (t, acc[i]!.2 - c)
    | none => acc.push (t, -c)) ts
  (d.filter (·.2 != 0), k - j)

partial def arTriv (p : Expr) : Bool :=
  match p.getAppFnArgs with
  | (``And, #[a, b]) => arTriv a && arTriv b
  | (``True, #[]) => true
  | (``Eq, #[ty, a, b]) => (ty == arIntT || ty == mkConst ``Nat) &&
      (let (d, k) := arLinDiff a b; d.isEmpty && k == 0)
  | (``LE.le, #[ty, _, a, b]) =>
      if ty == mkConst ``Nat then (let (d, k) := arLinDiff b a; k ≥ 0 && d.all (·.2 > 0))
      else ty == arIntT && (let (d, k) := arLinDiff b a
        k ≥ 0 && d.all (fun (t, c) => c > 0 && t.isAppOfArity ``Nat.cast 3))
  | _ => false

def arOmegaIn (g : MVarId) (div : Option Nat := none) : TacticM Unit := do
  setGoals [g]
  let nh ← g.withContext do return (← getLCtx).size
  let now ← vclock
  let gd ← globalDeadline.get
  let lim := (if gd > now then (gd - now) / (div.getD (nh + 2)) else 1) * hbPerVms
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context (fun c => { c with maxHeartbeats := lim }) do
      let some g' ← g.falseOrByContra | return
      g'.withContext do
        let hyps := (← getLocalHyps).toList
        Lean.Elab.Tactic.Omega.omega hyps g')
    (fun _ => throwError "omega: budget")
  setGoals []

def wgNeSides (p : Expr) : Option (Expr × Expr) :=
  match p.ne? with
  | some (_, a, b) => some (a, b)
  | none => (p.not?.bind (·.eq?)).map fun (_, a, b) => (a, b)

def wgHypMatch (hyps : Array (Expr × Expr)) (p : Expr) : MetaM (Option Expr) := do
  if let some (_, h) := hyps.find? (·.1 == p) then return some h
  if let some (_, l, r) := p.eq? then
    for (ty, h) in hyps do
      if let some (_, l', r') := ty.eq? then
        if l == r' && r == l' then return some (← mkEqSymm h)
  if let some (a, b) := wgNeSides p then
    for (ty, h) in hyps do
      if let some (c, d) := wgNeSides ty then
        if c == a && d == b then return some h
        if c == b && d == a then return some (← mkAppM ``Ne.symm #[h])
  return none

def wgRawHyps : MetaM (Array (Expr × Expr)) := do
  let mut raw : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ← isProp ty then raw := raw.push (ty, d.toExpr)
  return raw

def arByHyp (p : Expr) : MetaM (Option Expr) := do
  wgHypMatch (← wgRawHyps) (← instantiateMVars p)

def arOmegaCore (p : Expr) (saved : List MVarId) : TacticM Expr := do
  let tiers : Array (MVarId → MetaM MVarId) := if !p.hasFVar then #[pure] else
    (if arTriv p then #[arClearProps] else #[]) ++ #[(arTrim · false), (arTrim · true)]
  let mut err : Option Exception := none
  for tr in tiers do
    let m ← mkFreshExprSyntheticOpaqueMVar p
    try
      arOmegaIn (← tr m.mvarId!)
      setGoals saved
      return ← instantiateMVars m
    catch e => err := some e
  setGoals saved
  throw (err.getD (Exception.error .missing "omega"))

partial def arSplitAnd (g : MVarId) (h : Expr) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← inferType h)
  if let some (_, l, r) := ty.eq? then
    if l.isAppOfArity ``Prod.mk 4 && r.isAppOfArity ``Prod.mk 4 then
      let g1 ← g.assert `hpq (← mkAppM ``And #[← mkAppM ``Eq #[l.getAppArgs[2]!, r.getAppArgs[2]!],
        ← mkAppM ``Eq #[l.getAppArgs[3]!, r.getAppArgs[3]!]]) (← mkAppM ``Prod.mk.inj #[h])
      let (h1, g2) ← g1.intro1P
      return ← arSplitAnd g2 (mkFVar h1)
  match ty.getAppFnArgs with
  | (``And, #[a, b]) =>
      let g1 ← g.assert `hal a (← mkAppM ``And.left #[h])
      let (h1, g2) ← g1.intro1P
      let g3 ← arSplitAnd g2 (mkFVar h1)
      g3.withContext do
        let g4 ← g3.assert `har b (← mkAppM ``And.right #[h])
        let (h2, g5) ← g4.intro1P
        arSplitAnd g5 (mkFVar h2)
  | _ => return g

def arIntroFacts : TacticM Unit := withMainContext do
  let mut g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (lhs, rhs) := entailHead? t | return
  let inst := t.getAppArgs[0]!
  let qs := pureProps lhs #[]
  if qs.isEmpty then return
  let mut knownSet : Std.HashSet Expr := {}
  for dcl in ← getLCtx do
    if dcl.isImplementationDetail then continue
    knownSet := knownSet.insert (← instantiateMVars dcl.type)
  for q in qs do
    if knownSet.contains q then continue
    knownSet := knownSet.insert q
    let some pf := holdsPf? inst q lhs | continue
    let tcur ← instantiateMVars (← g.getType)
    let mv ← g.withContext do mkFreshExprSyntheticOpaqueMVar (← mkArrow q tcur)
    g.assign (mkAppN (mkConst ``himpl_of_holds) #[inst, q, lhs, rhs, pf, mv])
    let (h, g2) ← mv.mvarId!.intro1P
    g ← arSplitAnd g2 (mkFVar h)
  replaceMainGoal [g]

partial def exPull (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match e.getAppFnArgs with
  | (``HProp.hstar, #[inst, a, b]) =>
    let hty := mkApp (mkConst ``HProp) inst
    let hs := mkApp (mkConst ``HProp.hstar) inst
    let viaL := fun (a' pa : Expr) => do
      let some (lv, A, J) := (match a'.getAppFn, a'.getAppArgs with
        | .const _ [u], #[_, A, J] => some (u, A, J)
        | _, _ => none) | return none
      let e1 := mkApp2 hs a' b
      let p1 := mkAppN (mkConst ``congrArg [1, 1]) #[hty, hty, a, a', mkLambda `x .default hty (mkApp2 hs (.bvar 0) b), pa]
      let eq := mkAppN (mkConst ``HProp.hstar_hexists [lv]) #[inst, A, J, b]
      let some (_, _, r) := (← inferType eq).eq? | return none
      return some (r, mkAppN (mkConst ``Eq.trans [1]) #[hty, e, e1, r, p1, eq])
    let viaR := fun (b' pb : Expr) => do
      let some (lv, A, J) := (match b'.getAppFn, b'.getAppArgs with
        | .const _ [u], #[_, A, J] => some (u, A, J)
        | _, _ => none) | return none
      let e1 := mkApp2 hs a b'
      let p1 := mkAppN (mkConst ``congrArg [1, 1]) #[hty, hty, b, b', mkApp hs a, pb]
      let eq := mkAppN (mkConst ``Sep.Xsearch.hstar_hexists_rr [lv]) #[inst, A, a, J]
      let some (_, _, r) := (← inferType eq).eq? | return none
      return some (r, mkAppN (mkConst ``Eq.trans [1]) #[hty, e, e1, r, p1, eq])
    if a.isAppOfArity ``HProp.hexists 3 then
      return ← viaL a (mkApp2 (mkConst ``Eq.refl [1]) hty a)
    if let some (a', pa) ← exPull a then
      return ← viaL a' pa
    if b.isAppOfArity ``HProp.hexists 3 then
      return ← viaR b (mkApp2 (mkConst ``Eq.refl [1]) hty b)
    if let some (b', pb) ← exPull b then
      return ← viaR b' pb
    return none
  | _ => return none

partial def arIntroLhs : TacticM (Array Expr) := do
  let mut out : Array Expr := #[]
  for _ in [0 : 24] do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some (lhs, _) := entailHead? t | break
    if lhs.isAppOf ``HProp.hexists then
      let direct ← g.withContext do
        match lhs.getAppFn, lhs.getAppArgs with
        | .const _ [lv], #[inst, A, J@(.lam n _ body bi)] =>
          let some (_, rhs) := entailHead? t | return none
          let mty ← withLocalDecl n bi A fun v => do
            mkForallFVars #[v] (mkApp3 (mkConst ``HProp.himpl) inst (← Core.betaReduce (body.instantiate1 v)) rhs)
          let m ← mkFreshExprSyntheticOpaqueMVar mty
          g.assign (mkAppN (mkConst ``HProp.himpl_hexists_l [lv]) #[inst, A, rhs, J, m])
          return some m.mvarId!
        | _, _ => return none
      if let some m := direct then
        let (x, g2) ← m.intro1P
        replaceMainGoal [g2]
        out := out.push (mkFVar x)
        continue
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``HProp.himpl_hexists_l)
      let gs ← gs.filterM fun m => do return !(← m.isAssigned)
      let [g1] := gs | throwError "ar: hexists_l"
      let (x, g2) ← g1.intro1P
      let g3 ← g2.withContext do
        g2.change (← Core.betaReduce (← instantiateMVars (← g2.getType)))
      replaceMainGoal [g3]
      out := out.push (mkFVar x)
    else if (lhs.find? (·.isAppOf ``HProp.hexists)).isSome then
      let pulled ← g.withContext do (try exPull lhs catch _ => pure none)
      if let some (lhs', h) := pulled then
        let some (_, rhs) := entailHead? t | break
        let inst := t.getAppArgs[0]!
        let m ← g.withContext do mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``HProp.himpl) inst lhs' rhs)
        g.assign (mkAppN (mkConst ``HProp.himpl_trans) #[inst, lhs, lhs', rhs,
          mkAppN (mkConst ``himpl_of_eq) #[inst, lhs, lhs', h], m])
        replaceMainGoal [m.mvarId!]
        continue
      let ok ← tryTactic (evalTactic (← `(tactic| conv_lhs => simp only
        [HProp.hstar_hexists, Sep.Xsearch.hstar_hexists_rr, HProp.hstar_assoc])))
      unless ok do break
      let t2 ← instantiateMVars (← (← getMainGoal).getType)
      if t2 == t then break
    else break
  arIntroFacts
  return out

partial def arNonneg (t : Expr) : MetaM (Option Expr) := do
  let (``LE.le, #[ty, _, z, e]) := t.getAppFnArgs | return none
  unless z.int? == some 0 || z.nat? == some 0 do return none
  if ty == mkConst ``Nat then return some (mkApp (mkConst ``Nat.zero_le) e)
  unless ty == arIntT do return none
  if let some pf ← arByHyp t then return some pf
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    let some pa ← arNonneg (← mkAppM ``LE.le #[z, a]) | return none
    let some pb ← arNonneg (← mkAppM ``LE.le #[z, b]) | return none
    return some (mkAppN (mkConst ``Int.add_nonneg) #[a, b, pa, pb])
  | (``Nat.cast, #[_, _, n]) => return some (mkApp (mkConst ``Int.natCast_nonneg) n)
  | _ =>
    if let some v := e.int? then
      if v ≥ 0 then return some (← mkDecideProof t)
    return none

initialize lemBuilding : IO.Ref Bool ← IO.mkRef false

initialize wgFarHook : IO.Ref (Expr → Expr → TacticM (Option Expr)) ← IO.mkRef (fun _ _ => pure none)

def wgFar (lhs a b : Expr) : TacticM (Option Expr) := do
  let L := flatStar lhs #[]
  let some i := L.findIdx? (fun e => e.isAppOfArity ``HProp.hsingle 3 && e.getAppArgs[1]! == a) | return none
  let some hz ← withMainContext do
      let nz ← mkAppM ``Ne #[a, mkNatLit 0]
      (← getLCtx).findDeclM? fun d => do
        if d.isImplementationDetail then return none
        return if (← instantiateMVars d.type) == nz then some d.toExpr else none
    | return none
  let X := L[i]!
  let inst := lhs.getAppArgs[0]!
  let F := starOf inst (L.eraseIdx! i).toList
  let some hF ← (← wgFarHook.get) b F | return none
  let T := mkApp3 (mkConst ``HProp.hstar) inst X F
  let some imp ← provePerm lhs T | return none
  let hx := mkAppN (mkConst ``hasLoc_single) #[inst, a, X.getAppArgs[2]!]
  let core := mkAppN (mkConst ``ne_far) #[inst, a, b, X, F, hx, hz, hF]
  let pf ← mkAppM ``holdsP_mono_imp #[imp, core]
  return some pf

def wgNormStep (e : Expr) : MetaM Expr := do
  let e ← Core.betaReduce e
  Meta.transform e (post := fun t => do
    match t.getAppFnArgs with
    | (``Prod.fst, #[_, _, p]) =>
      if p.isAppOfArity ``Prod.mk 4 then return .visit p.getAppArgs[2]! else return .continue
    | (``Prod.snd, #[_, _, p]) =>
      if p.isAppOfArity ``Prod.mk 4 then return .visit p.getAppArgs[3]! else return .continue
    | _ => return .continue)

def wgNorm (e : Expr) : MetaM Expr := do
  let mut cur := e
  for _ in [0 : 8] do
    let nxt ← wgNormStep cur
    if nxt == cur then return cur
    cur := nxt
  return cur

def wgConj (l : Array Expr) : MetaM Expr := do
  if l.isEmpty then return mkConst ``True
  let mut acc := l[l.size - 1]!
  for i in [0 : l.size - 1] do acc ← mkAppM ``And #[l[l.size - 2 - i]!, acc]
  return acc

def wgNeHeap (lhs a b : Expr) : TacticM (Option Expr) := do
  let lhs ← instantiateMVars lhs
  if let some h ← wgApartIn (← wgLocHyps) (wgCells lhs) a b lhs then
    return some (← mkExpectedTypeHint h (← mkAppM ``holdsP #[← mkAppM ``Ne #[a, b], lhs]))
  if let some h ← wgFar lhs a b then return some h
  if let some h ← wgFar lhs b a then return some (← mkAppM ``holdsP_ne_symm #[h])
  return none

partial def wgShapeOk (pat tgt : Expr) (d : Nat) (top : Bool := false) : Bool :=
  if d == 0 || pat.isBVar || pat.isMVar || pat.hasLooseBVars && !pat.isApp then true else
  match pat, tgt with
  | .lit a, .lit b => a == b
  | .app .., .app .. =>
    match pat.getAppFn, tgt.getAppFn with
    | .const a _, .const b _ =>
      let ok := a == b || (top && a == ``LT.lt && b == ``LE.le)
      ok && (a != b || (pat.getAppNumArgs == tgt.getAppNumArgs &&
        (pat.getAppArgs.zip tgt.getAppArgs).all fun (u, v) => wgShapeOk u v (d - 1)))
    | .const .., .fvar .. => false
    | _, _ => true
  | .app .., .fvar .. => !pat.getAppFn.isConst
  | .const a _, .const b _ => a == b
  | _, _ => true

def wgStrip (e : Expr) : Nat × Expr := Id.run do
  let mut e := e
  let mut n := 0
  while e.isForall do
    n := n + 1
    e := e.bindingBody!
  return (n, e)

def wgLemmaList : Array Name := #[``Ne.symm, ``Nat.zero_le, ``Nat.le_refl, ``Nat.pos_of_ne_zero, ``Nat.le_add_left,
  ``inv_hyp, ``inv_ne_of_eq, ``inv_len0, ``inv_imp0, ``inv_or0, ``inv_rel0, ``inv_rel0z, ``inv_rel0le, ``inv_rel0zle,
  ``inv_len_step, ``inv_imp_step, ``inv_or_step, ``inv_rel_l, ``inv_rel_r, ``inv_rel_lz, ``inv_rel_lle, ``inv_rel_rle,
  ``inv_rel_lzle]

initialize wgLemTab : IO.Ref (Array (Name × Nat × Expr)) ← IO.mkRef #[]

def wgLemTable : MetaM (Array (Name × Nat × Expr)) := do
  let t ← wgLemTab.get
  unless t.isEmpty do return t
  let t ← wgLemmaList.mapM fun L => do
    let (n, b) := wgStrip (← getConstInfo L).type
    return (L, n, b)
  wgLemTab.set t
  return t

def wgByLemmas (inst goal : Expr) (hyps : Array (Expr × Expr)) : MetaM (Option Expr) := do
  let (arG, gb) := wgStrip goal
  for (L, arL, lb) in ← wgLemTable do
    if arL < arG then continue
    if arG == 0 && (lb.isBVar || lb.getAppArgs.all (·.isBVar)) then continue
    unless wgShapeOk lb gb 3 true do continue
    let s ← saveState
    let c ← mkConstWithFreshMVarLevels L
    let cty ← inferType c
    let ar := fun (e : Expr) => (wgStrip e).1
    let (mvs, _, ty) ← forallMetaTelescopeReducing cty (some (ar cty - ar goal))
    for mv in mvs do
      if (← inferType mv).isConstOf ``Params then mv.mvarId!.assign inst
    if ← withReducible (isDefEq ty goal) then
      let mut ok := true
      for mv in mvs do
        if (← instantiateMVars mv).isMVar then
          let mty ← instantiateMVars (← inferType mv)
          if ← isProp mty then
            let mut found := false
            let hd := mty.getAppFn.constName?
            let syn := !mty.hasMVar
            for (hty, hpf) in hyps do
              if hty.getAppFn.constName? != hd then continue
              if syn then
                if hty == mty then
                  mv.mvarId!.assign hpf
                  found := true
                  break
                continue
              let s2 ← saveState
              if ← withReducible (isDefEq mty hty) then
                mv.mvarId!.assign hpf
                found := true
                break
              s2.restore
            unless found do
              ok := false
              break
      if ok then
        let pf ← instantiateMVars (mkAppN c mvs)
        if !pf.hasExprMVar then return some pf
    s.restore
  return none

partial def pureHyps (hyps : Array (Expr × Expr)) : MetaM (Array (Expr × Expr)) := do
  let mut out : Array (Expr × Expr) := #[]
  let mut todo := hyps
  while !todo.isEmpty do
    let (ty, pf) := todo.back!
    todo := todo.pop
    let ty ← instantiateMVars ty
    let ty' ← if (ty.find? (fun e => e.isAppOf ``Prod.fst || e.isAppOf ``Prod.snd || e.isHeadBetaTarget)).isSome
      then wgNorm ty else pure ty
    let pf' ← if ty' == ty then pure pf else mkExpectedTypeHint pf ty'
    if let some (a, b) := ty'.and? then
      todo := todo.push (a, mkApp3 (mkConst ``And.left) a b pf') |>.push (b, mkApp3 (mkConst ``And.right) a b pf')
      continue
    if let some (_, l, r) := ty'.eq? then
      if l.isAppOfArity ``Prod.mk 4 && r.isAppOfArity ``Prod.mk 4 then
        let inj ← mkAppM ``Prod.mk.inj #[pf']
        todo := todo.push (← inferType inj, inj)
        continue
    out := out.push (ty', pf')
  return out



partial def wgNumProp (p : Expr) : Bool :=
  match p.getAppFnArgs with
  | (``And, #[a, b]) | (``Or, #[a, b]) => wgNumProp a && wgNumProp b
  | (``Not, #[a]) => wgNumProp a
  | (``Eq, #[ty, _, _]) | (``Ne, #[ty, _, _]) | (``LE.le, #[ty, _, _, _]) | (``LT.lt, #[ty, _, _, _]) =>
    ty.isConstOf ``Nat || ty.isConstOf ``Int
  | (``True, _) | (``False, _) => true
  | _ => false

partial def wgLeaves (p : Expr) (acc : Array Expr) : Array Expr :=
  match p.and? with
  | some (a, b) => wgLeaves b (wgLeaves a acc)
  | none => acc.push p

def wgArith (p : Expr) : Bool :=
  !p.isForall && !(match p.eq? with
    | some (_, l, _) => l.isAppOfArity ``Prod.mk 4
    | none => false)

def wgConjProj (cs : Array Expr) (pf : Expr) (j : Nat) : MetaM Expr := do
  let mut cur := pf
  for i in [0 : j] do
    cur := mkApp3 (mkConst ``And.right) cs[i]! (← wgConj (cs.extract (i + 1) cs.size)) cur
  if j + 1 < cs.size then
    return mkApp3 (mkConst ``And.left) cs[j]! (← wgConj (cs.extract (j + 1) cs.size)) cur
  return cur

partial def wgAndTree (p : Expr) (leaf : Expr → TacticM Expr) : TacticM Expr := do
  match p.and? with
  | some (a, b) => return mkApp4 (mkConst ``And.intro) a b (← wgAndTree a leaf) (← wgAndTree b leaf)
  | none => leaf p

partial def wgDirect (hyps : Array (Expr × Expr)) (p : Expr) : TacticM (Option Expr) := do
  if p.isConstOf ``True then return some (mkConst ``True.intro)
  if let some (_, l, r) := p.eq? then
    if l == r then return some (← mkEqRefl l)
  if let some pf ← wgHypMatch hyps p then return some pf
  if let some (a, b) := p.and? then
    let some pa ← wgDirect hyps a | return none
    let some pb ← wgDirect hyps b | return none
    return some (mkApp4 (mkConst ``And.intro) a b pa pb)
  if !p.hasFVar && !p.hasMVar && wgNumProp p then
    if let some d ← (try some <$> mkDecide p catch _ => pure none) then
      if (← whnfD d).isConstOf ``Bool.true then return some (← mkDecideProof p)
  if let some pf ← wgByLemmas (mkConst ``Unit) p hyps then return some pf
  if let some pf ← arNonneg p then
    if ← isDefEq (← inferType pf) p then return some pf
  if let some (_, l, r) := p.eq? then
    if !p.hasExprMVar && (← withReducible (isDefEq l r)) then return some (← mkEqRefl l)
  return none

partial def wgProveH (hyps : Array (Expr × Expr)) (p0 : Expr) (heap : Option Expr) : TacticM (Expr × Bool) := do
  let p0 ← instantiateMVars p0
  let p ← if (p0.find? (fun e => e.isAppOf ``Prod.fst || e.isAppOf ``Prod.snd || e.isHeadBetaTarget)).isSome
    then wgNorm p0 else pure p0
  let fin := fun (pf : Expr) => do if p == p0 then pure pf else mkExpectedTypeHint pf p0
  if let some pf ← wgDirect hyps p then return (← fin pf, false)
  let sub := fun (q : Expr) => do return (← wgProveH hyps q none).1
  if let .forallE n ty body bi := p then
    let pf ← withLocalDecl n bi ty fun v => do
      let hs ← if ← isProp ty then pure (hyps ++ (← pureHyps #[(ty, v)])) else pure hyps
      mkLambdaFVars #[v] (← (wgProveH hs (body.instantiate1 v) none)).1
    return (← fin pf, false)
  if let some (_, l, r) := p.eq? then
    if l.isAppOfArity ``Prod.mk 4 && r.isAppOfArity ``Prod.mk 4 then
      let la := l.getAppArgs
      let ra := r.getAppArgs
      let h1 ← sub (← mkEq la[2]! ra[2]!)
      let h2 ← sub (← mkEq la[3]! ra[3]!)
      return (← fin (← mkAppM ``Prod.ext #[h1, h2]), false)
  if p.and?.isSome then
    let cs := wgLeaves p #[]
    let dir ← cs.mapM (wgDirect hyps)
    let rest := ((Array.range cs.size).filter fun i => dir[i]!.isNone && wgArith cs[i]!).map (cs[·]!)
    for c in rest do
      if ← cmPureRefuted c then throwError "side: futile"
    let restPf ← if rest.isEmpty then pure none else some <$> arOmegaCore (← wgConj rest) (← getGoals)
    return (← fin (← wgAndTree p fun c => do
      if let some i := cs.idxOf? c then
        if let some d := dir[i]! then return d
      if let some j := rest.idxOf? c then
        if let some r := restPf then return ← wgConjProj rest r j
      sub c), false)
  if let some h := heap then
    if let some (a, b) := wgNeSides p then
      let h ← instantiateMVars h
      if let some pf ← wgNeHeap h a b then return (pf, true)
  if ← cmPureRefuted p then throwError "side: futile"
  return (← fin (← arOmegaCore p (← getGoals)), false)

def wgProve (p : Expr) (heap : Option Expr) : TacticM (Expr × Bool) := do
  let p ← instantiateMVars p
  if p.isConstOf ``True then return (mkConst ``True.intro, false)
  if let some (_, l, r) := p.eq? then
    if l == r then return (← mkEqRefl l, false)
  let raw ← wgRawHyps
  if let some pf ← wgHypMatch raw p then return (pf, false)
  wgProveH (← pureHyps raw) p heap

def wgSide (p : Expr) : TacticM Expr := do
  return (← wgProve p none).1

def wgCloseGoal (g : MVarId) : TacticM Unit := g.withContext do
  let t ← instantiateMVars (← g.getType)
  if (entailHead? t).isSome then throwError "ar: open entailment"
  g.assign (← wgSide t)

def wgCloseAll : TacticM Unit := do
  for g in ← getUnsolvedGoals do
    unless ← g.isAssigned do wgCloseGoal g
  setGoals []

def arRwLhs (As : List Expr) (lem0 : Expr) : TacticM (Array Expr) := do
  withMainContext do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some (lhs, rhs) := entailHead? t | throwError "ar: not an entailment"
    let inst := t.getAppArgs[0]!
    let lty ← instantiateMVars (← inferType lem0)
    let some (lemL0, lemR) := entailHead? lty | throwError "ar: lemma shape"
    let lemAtoms := (flatStar lemL0 #[]).filter (!·.isAppOf ``HProp.hpure)
    let mut unmatched := As.toArray
    let mut swaps : Array (Expr × Expr) := #[]
    for q in lemAtoms do
      if let some i := unmatched.idxOf? q then
        unmatched := unmatched.eraseIdx! i
      else
        swaps := swaps.push (q, q)
    let mut swapped : Array (Expr × Expr) := #[]
    for (q, _) in swaps do
      let mut hit : Option Nat := none
      for i in [0 : unmatched.size] do
        if unmatched[i]!.getAppFn == q.getAppFn && (← isDefEq unmatched[i]! q) then
          hit := some i
          break
      if let some i := hit then
        swapped := swapped.push (q, unmatched[i]!)
        unmatched := unmatched.eraseIdx! i
    let lemL := if swapped.isEmpty then lemL0 else
      lemL0.replace (fun e => (swapped.find? (·.1 == e)).map (·.2))
    let lem ← if swapped.isEmpty then pure lem0 else
      mkExpectedTypeHint lem0 (mkApp3 (mkConst ``HProp.himpl) inst lemL lemR)
    let mut rest := flatStar lhs #[]
    for x in As do
      match rest.idxOf? x with
      | some i => rest := rest.eraseIdx! i
      | none => throwError "ar: atom not found"
    let lemL' ← instantiateMVars lemL
    let mut miss : Array Expr := #[]
    let mut asRem := As.toArray
    for q in flatStar lemL' #[] do
      unless q.isAppOf ``HProp.hpure do continue
      if let some i := asRem.idxOf? q then
        asRem := asRem.eraseIdx! i
        continue
      match rest.idxOf? q with
      | some i => rest := rest.eraseIdx! i
      | none => miss := miss.push q
    let restE := starOf inst rest.toList
    let hs := mkApp3 (mkConst ``HProp.hstar) inst
    let tr := fun (a b c p q : Expr) => mkAppN (mkConst ``HProp.himpl_trans) #[inst, a, b, c, p, q]
    let noRest := rest.isEmpty
    let tgt := if noRest then lemL else hs lemL restE
    let m1 ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``HProp.himpl) inst lhs tgt)
    let fast : Option Expr ← id do
      let mut base := lhs
      let mut pf := mkApp2 (mkConst ``HProp.himpl_refl) inst lhs
      for q in miss do
        let P := q.appArg!
        let some (hp, held) ← (try some <$> wgProve P (some (← instantiateMVars lhs)) catch _ => pure none)
          | return none
        pf := if held then mkAppN (mkConst ``pure_l_of_holds) #[inst, lhs, base, P, hp, pf]
          else mkAppN (mkConst ``Sep.pure_l_intro) #[inst, P, lhs, base, hp, pf]
        base := hs q base
      let mut extra := flatStar (← instantiateMVars base) #[]
      for b in flatStar (← instantiateMVars tgt) #[] do
        match extra.idxOf? b with
        | some i => extra := extra.eraseIdx! i
        | none => return none
      unless extra.all (·.isAppOf ``HProp.hpure) do return none
      let mut padded := tgt
      let mut drops : Array Expr := #[]
      let mut tops : Array Expr := #[]
      for q in extra do
        drops := drops.push (mkAppN (mkConst ``star_pure_drop) #[inst, padded, q.appArg!])
        tops := tops.push padded
        padded := hs padded q
      let some imp ← (if base == padded then pure (some (mkApp2 (mkConst ``HProp.himpl_refl) inst base))
        else provePerm base padded) | return none
      let mut fin := tr lhs base padded pf imp
      let mut cur := padded
      for i' in [0 : drops.size] do
        let i := drops.size - 1 - i'
        fin := tr lhs cur tops[i]! fin drops[i]!
        cur := tops[i]!
      return some fin
    match fast with
    | some pf => m1.mvarId!.assign pf
    | none =>
      if ← lemBuilding.get then throwError "ar: no direct rewrite"
      setGoals [m1.mvarId!]
      Sep.Xsimpl.xsimplDriver none
      cleanAll
      wgCloseAll
    if noRest then
      let m2 ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``HProp.himpl) inst lemR rhs)
      g.assign (tr lhs lemL rhs m1 (tr lemL lemR rhs lem m2))
      setGoals [m2.mvarId!]
    else
    let m2 ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``HProp.himpl) inst (hs lemR restE) rhs)
    let fr := mkAppN (mkConst ``HProp.himpl_frame_l) #[inst, lemL, lemR, restE, lem]
    let pf2 := tr (hs lemL restE) (hs lemR restE) rhs fr m2
    g.assign (tr lhs (hs lemL restE) rhs m1 pf2)
    setGoals [m2.mvarId!]
  let mut out : Array Expr := #[]
  for _ in [0 : 16] do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some (lhs, _) := entailHead? t | break
    if lhs.isAppOfArity ``HProp.hexists 3 then
      let x ← withMainContext do
        let g := (← getMainGoal)
        let gs ← g.apply (← mkConstWithFreshMVarLevels ``HProp.himpl_hexists_l)
        let gs ← gs.filterM fun m => do return !(← m.isAssigned)
        let [g1] := gs | throwError "ar: hexists_l"
        let (x, g2) ← g1.intro1P
        let g3 ← g2.withContext do
          g2.change (← Core.betaReduce (← instantiateMVars (← g2.getType)))
        replaceMainGoal [g3]
        pure (mkFVar x)
      out := out.push x
      continue
    match lhs.getAppFnArgs with
    | (``HProp.hstar, #[_, ex, rest]) =>
      unless ex.isAppOf ``HProp.hexists do break
      let J := ex.appArg!
      let g' ← g.withContext do
        let eq ← mkAppM ``HProp.hstar_hexists #[J, rest]
        let some (_, _, nl) := (← inferType eq).eq? | throwError "ar: hexists"
        let some (_, rhs) := entailHead? t | throwError "ar: goal"
        let inst := t.getAppArgs[0]!
        let m ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``HProp.himpl) inst nl rhs)
        g.assign (mkAppN (mkConst ``HProp.himpl_trans) #[inst, lhs, nl, rhs,
          mkAppN (mkConst ``himpl_of_eq) #[inst, lhs, nl, eq], m])
        pure m.mvarId!
      replaceMainGoal [g']
      let x ← withMainContext do
        let g := (← getMainGoal)
        let gs ← g.apply (← mkConstWithFreshMVarLevels ``HProp.himpl_hexists_l)
        let gs ← gs.filterM fun m => do return !(← m.isAssigned)
        let [g1] := gs | throwError "ar: hexists_l"
        let (x, g2) ← g1.intro1P
        let g3 ← g2.withContext do
          g2.change (← Core.betaReduce (← instantiateMVars (← g2.getType)))
        replaceMainGoal [g3]
        pure (mkFVar x)
      out := out.push x
    | _ => break
  return out

def arOpenGoal : TacticM (Array Expr) := do
  let mut ws : Array Expr := #[]
  let d ← do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    pure (t.approxDepth.toNat + 1)
  for _ in [0 : d] do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some (lhs, rhs) := entailHead? t | break
    unless rhs.isAppOf ``HProp.hexists do break
    let lam := rhs.appArg!
    unless lam.isLambda do break
    let w ← g.withContext do mkFreshExprMVar lam.bindingDomain!
    let inst := t.getAppArgs[0]!
    let body := lam.bindingBody!.instantiate1 w
    let m ← g.withContext do
      mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[lhs, body])
    g.assign (← mkAppOptM ``HProp.himpl_hexists_r #[inst, lam.bindingDomain!, w, lhs, lam, m])
    replaceMainGoal [m.mvarId!]
    ws := ws.push w
  return ws

partial def arOpenDeepE (e : Expr) (ws : IO.Ref (Array Expr)) : MetaM (Expr × Expr) := do
  match e.getAppFnArgs with
  | (``HProp.hexists, #[inst, ty, lam]) =>
    if !lam.isLambda then return (e, ← mkAppM ``HProp.himpl_refl #[e])
    let w ← mkFreshExprMVar ty
    ws.modify (·.push w)
    let (b', pb) ← arOpenDeepE (lam.bindingBody!.instantiate1 w) ws
    let ex ← mkAppOptM ``HProp.himpl_hexists_r #[inst, ty, w, b', lam, pb]
    return (b', ex)
  | (``HProp.hstar, #[_, a, b]) =>
    let (a', pa) ← arOpenDeepE a ws
    let (b', pb) ← arOpenDeepE b ws
    if a' == a && b' == b then return (e, ← mkAppM ``HProp.himpl_refl #[e])
    return (← mkAppM ``HProp.hstar #[a', b'], ← mkAppM ``HProp.himpl_frame_lr #[pa, pb])
  | _ => return (e, ← mkAppM ``HProp.himpl_refl #[e])

def arOpenDeep : TacticM (Array Expr) := do
  let g ← getMainGoal
  g.withContext do
    let t ← instantiateMVars (← g.getType)
    let some (lhs, rhs) := entailHead? t | return #[]
    let ws ← IO.mkRef #[]
    let (r', pr) ← arOpenDeepE rhs ws
    if r' == rhs then return #[]
    let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[lhs, r'])
    g.assign (← mkAppM ``HProp.himpl_trans #[m, pr])
    replaceMainGoal [m.mvarId!]
    ws.get

def arGoal (ty : Expr) : TacticM Expr := do
  let m ← mkFreshExprSyntheticOpaqueMVar ty
  setGoals [m.mvarId!]
  return m

def arEntries : MetaM (Array UnfoldEntry) := return xsearchUnfoldExt.getState (← getEnv)

def arCast (k : Expr) : MetaM Expr := do
  if let some f := (← arOpCache.get)[(``Nat.cast, arIntT)]? then return mkApp f k
  let e ← instantiateMVars (← mkAppOptM ``Nat.cast #[arIntT, none, k])
  let f := e.appFn!
  unless f.hasFVar || f.hasMVar do arOpCache.modify (·.insert (``Nat.cast, arIntT) f)
  return e

def arSum : List Expr → MetaM Expr
  | [] => arIntLit 0
  | [x] => pure x
  | x :: r => do arAdd x (← arSum r)

def arConj : List Expr → MetaM Expr
  | [] => pure (mkConst ``True)
  | [x] => pure x
  | x :: r => do mkAppM ``And #[x, ← arConj r]

def arOpen (rhs : Expr) : MetaM (Expr × Array Expr) := do
  let mut e := rhs
  let mut ms : Array Expr := #[]
  for _ in [0 : rhs.approxDepth.toNat + 1] do
    unless e.isAppOf ``HProp.hexists do break
    let lam := e.appArg!
    unless lam.isLambda do break
    let m ← mkFreshExprMVar (some lam.bindingDomain!)
    ms := ms.push m
    e := lam.bindingBody!.instantiate1 m
  return (e, ms)

def arSolve (n0 : Expr) (pieces : Array ArPiece) (rpures : Array Expr) :
    TacticM (Option (Array Expr)) := do
  for c in rpures do
    for cc in pureConjs c #[] do
      match cc.getAppFnArgs with
      | (``Eq, #[ty, x, y]) =>
        if ty == arIntT then
          let x ← instantiateMVars x
          let y ← instantiateMVars y
          if x.isMVar && !y.hasExprMVar then
            let _ ← isDefEq x y
          else if y.isMVar && !x.hasExprMVar then
            let _ ← isDefEq y x
      | _ => pure ()
  let lens ← pieces.mapM (fun p => instantiateMVars p.len)
  if lens.any (fun l => l.hasExprMVar && !l.isMVar) then return none
  let mut unk : Array Expr := #[]
  let mut unkLo : Array Int := #[]
  for (l, pc) in lens.zip pieces do
    if l.isMVar && !unk.contains l then
      unk := unk.push l
      unkLo := unkLo.push pc.lo
  let cands : Array (Option Nat) :=
    if unk.isEmpty then #[none] else (Array.range unk.size).map some
  for cnd in cands do
    let s ← saveState
    let r ← try (do
        for i in [0 : unk.size] do
          if cnd != some i then
            unless ← isDefEq unk[i]! (← arIntLit unkLo[i]!) do throwError "ar: assign"
        if let some i := cnd then
          let mut others : List Expr := []
          for l in lens do
            let l ← instantiateMVars l
            unless l == unk[i]! do others := others ++ [l]
          unless ← isDefEq unk[i]! (← arSub n0 (← arSum others)) do throwError "ar: slack"
        let ls ← lens.mapM instantiateMVars
        if ls.any (·.hasExprMVar) then throwError "ar: open length"
        let mut ps : List Expr := [← arEq (← arSum ls.toList) n0]
        for i in [0 : pieces.size] do
          unless pieces[i]!.cell do ps := ps ++ [← arLe (← arIntLit pieces[i]!.lo) ls[i]!]
        for c in rpures do
          for cc in pureConjs (← instantiateMVars c) #[] do
            if arIntProp cc && !cc.hasExprMVar then ps := ps ++ [cc]
        let hard := ps.filter (!arTriv ·)
        unless hard.isEmpty do
          let _ ← wgSide (← arConj hard)
        pure (some ls))
      catch _ => pure none
    if r.isSome then return r
    s.restore
  return none

partial def arAssign (L : Array Expr) (rs : List Expr) (used : Array Nat) : MetaM Bool := do
  match rs with
  | [] => return true
  | r :: rest =>
    for j in [0 : L.size] do
      if used.contains j then continue
      unless L[j]!.getAppFn == r.getAppFn do continue
      let s ← saveState
      if ← (try checkpointDefEq (isDefEq r L[j]!) catch _ => pure false) then
        if ← arAssign L rest (used.push j) then return true
      s.restore
    return false

partial def wgBranches (e : Expr) (acc : Array Expr) : Array Expr :=
  if isHorConst e && e.getAppNumArgs ≥ 2 then
    let a := e.getAppArgs
    wgBranches a[a.size - 1]! (wgBranches a[a.size - 2]! acc)
  else acc.push e

def wgHelperBody? (q : Name) (args : Array Expr) : MetaM (Option Expr) := do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let some ent := entries.find? (·.headFn == q) | return none
  let ty := (← getConstInfo ent.lemmaName).type
  forallTelescopeReducing ty fun xs concl => do
    unless xs.size == args.size do return none
    let some (_, _, body) := concl.eq? | return none
    if (wgBranches body #[]).size != 1 then return none
    if (body.find? (·.isConstOf q)).isSome then return none
    if ← isRecPred q then return none
    return some (body.replaceFVars xs args)

def wgUnfoldHelpers (onlyNew : Bool := false) : TacticM Bool := do
  let entries ← arEntries
  let mut any := false
  let fuel ← withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (lhs, rhs) := entailHead? t | return 0
    let (rb, _) ← arOpen rhs
    return (flatStar lhs #[] ++ flatStar rb #[]).size * entries.size
  for _ in [0 : fuel] do
    let occ? ← withMainContext do
      let t ← instantiateMVars (← (← getMainGoal).getType)
      let some (lhs, rhs) := entailHead? t | return none
      let (rb, _) ← arOpen rhs
      let atoms := flatStar lhs #[] ++ flatStar rb #[]
      for a in atoms do
        let some q := a.getAppFn.constName? | continue
        unless entries.any (·.headFn == q) do continue
        let some b ← wgHelperBody? q a.getAppArgs | continue
        if onlyNew then
          let others := (atoms.erase a).filterMap (·.getAppFn.constName?)
          let fresh := b.getUsedConstants.any fun c =>
            entries.any (·.headFn == c) && !others.contains c
          unless fresh do continue
        return some a
      return none
    let some o := occ? | break
    unless ← tryTactic (rewriteOcc entries o) do break
    any := true
  if any then
    let nestedR ← withMainContext do
      let t ← instantiateMVars (← (← getMainGoal).getType)
      let some (_, rhs) := entailHead? t | return false
      let (rb, _) ← arOpen rhs
      return (flatStar rb #[]).any (·.isAppOf ``HProp.hexists)
    if nestedR then
      let _ ← tryTactic (evalTactic (← `(tactic| conv_rhs => simp only
        [Sep.Xsearch.hstar_hexists_rr, HProp.hstar_hexists, HProp.hstar_assoc])))
    let _ ← arIntroLhs
  return any

partial def puresEmpPf (inst : Expr) : List Expr → Option Expr
  | [] => some (mkApp2 (mkConst ``HProp.himpl_refl) inst (mkApp (mkConst ``HProp.hempty) inst))
  | [q] => if q.isAppOfArity ``HProp.hpure 2 then some (mkApp2 (mkConst ``Sep.pDrop) inst q.appArg!) else none
  | q :: rest =>
    if q.isAppOfArity ``HProp.hpure 2 then
      (puresEmpPf inst rest).map fun h =>
        mkAppN (mkConst ``pures_emp_cons) #[inst, q.appArg!, starOf inst rest, h]
    else none

def finishDirect : TacticM Bool := do
  let (inst, rhs, As) ← withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    let some (_, rhs) := entailHead? t | throwError "fin: goal"
    if t.hasExprMVar then throwError "fin: mvars"
    pure (t.getAppArgs[0]!, rhs, (flatStar rhs #[]).filter (!·.isAppOf ``HProp.hpure))
  if As.isEmpty then return false
  let _ ← arRwLhs As.toList (mkApp2 (mkConst ``HProp.himpl_refl) inst rhs)
  withMainContext do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some (lhs, rhs') := entailHead? t | return false
    if lhs == rhs' then
      g.assign (mkApp2 (mkConst ``HProp.himpl_refl) inst rhs')
      replaceMainGoal []
      return true
    unless lhs.isAppOfArity ``HProp.hstar 3 && lhs.appFn!.appArg! == rhs' do return false
    let restE := lhs.appArg!
    let some h := puresEmpPf inst (if restE.isAppOf ``HProp.hempty then [] else (flatStar restE #[]).toList)
      | return false
    unless starOf inst (flatStar restE #[]).toList == restE || restE.isAppOf ``HProp.hempty do return false
    g.assign (mkAppN (mkConst ``star_drop_emp) #[inst, rhs', restE, h])
    replaceMainGoal []
    return true

partial def wgSplitDisj (fuel : Nat := 6) : TacticM (List MVarId) := do
  let _ ← arIntroLhs
  let hasD ← withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (lhs, _) := entailHead? t | return false
    pure ((lhs.find? (·.isAppOf ``hdisj)).isSome)
  if !hasD || fuel == 0 then return [← getMainGoal]
  evalTactic (← `(tactic| try xsearch_distr))
  unless ← tryTactic (applyConstT ``hdisj_elim) do return [← getMainGoal]
  let gs ← getGoals
  let mut out : List MVarId := []
  for g in gs do
    setGoals [g]
    out := out ++ (← wgSplitDisj (fuel - 1))
  return out

structure WgP where
  pname : Name
  inst : Expr
  tys : Array Expr
  mov : Array Nat
  ai : Option Nat
  sty : Expr
  cLam : Expr
  preLam : Expr
  nextLam : Expr
  usTys : Array Expr
  endSpec : Array (Option Nat × Option Expr)
  kmin : Nat
  stepIdx : Nat
  tailLam : Option Expr := none
  relLam : Expr
  invLam : Expr
  profLam : Option Expr := none
  cellData : Array (Expr × Expr × Array Expr × Expr × Nat) := #[]
  wLam : Option Expr := none
  disj : Nat × Nat := (0, 1)
  via : Bool := false
  unitW : Bool := true
  cst : Array Nat := #[]
  gloc : Array (Nat × Nat) := #[]
  gprev : Array (Nat × Nat × Nat) := #[]
  prevAdr : Array (Nat × Nat) := #[]
  rels : Array (Nat × Int × Int × Bool) := #[]
  pg : Bool := false
  baseIdx : Nat := 0
  deriving Inhabited

def wgProjSlow (s : Expr) (j n : Nat) : MetaM Expr := do
  let mut acc := s
  for _ in [0 : j] do acc ← mkAppM ``Prod.snd #[acc]
  if j + 1 < n then acc ← mkAppM ``Prod.fst #[acc]
  return acc

def wgTupleTy (tys : Array Expr) : MetaM Expr := do
  let mut acc := tys[tys.size - 1]!
  for i in [0 : tys.size - 1] do
    let a := tys[tys.size - 2 - i]!
    acc := mkApp2 (mkConst ``Prod [← getDecLevel a, ← getDecLevel acc]) a acc
  return acc

def wgTuple (cs : Array Expr) : MetaM Expr := do
  let mut acc := cs[cs.size - 1]!
  let mut accTy ← inferType acc
  for i in [0 : cs.size - 1] do
    let c := cs[cs.size - 2 - i]!
    let cTy ← inferType c
    let u ← getDecLevel cTy
    let v ← getDecLevel accTy
    acc := mkApp4 (mkConst ``Prod.mk [u, v]) cTy accTy c acc
    accTy := mkApp2 (mkConst ``Prod [u, v]) cTy accTy
  instantiateMVars acc

def wgProj (s : Expr) (j n : Nat) : MetaM Expr := do
  if n == 1 then return s
  let mut acc := s
  let mut ty ← whnfR (← instantiateMVars (← inferType s))
  for _ in [0 : j] do
    unless ty.isAppOfArity ``Prod 2 do return ← wgProjSlow s j n
    let lv := ty.getAppFn.constLevels!
    acc := mkApp3 (mkConst ``Prod.snd lv) ty.appFn!.appArg! ty.appArg! acc
    ty ← whnfR ty.appArg!
  if j + 1 < n then
    unless ty.isAppOfArity ``Prod 2 do return ← wgProjSlow s j n
    let lv := ty.getAppFn.constLevels!
    acc := mkApp3 (mkConst ``Prod.fst lv) ty.appFn!.appArg! ty.appArg! acc
  instantiateMVars acc

partial def wgComps (e : Expr) (n : Nat) : MetaM (Array Expr) := do
  let e ← instantiateMVars e
  if n ≤ 1 then return #[e]
  if e.isAppOfArity ``Prod.mk 4 then
    return #[e.getAppArgs[2]!] ++ (← wgComps e.getAppArgs[3]! (n - 1))
  (Array.range n).mapM fun j => do wgNorm (← wgProj e j n)

def wgNormAll : TacticM Unit := withMainContext do
  let mut g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let ty' ← wgNorm ty
    unless ty' == ty do g ← g.changeLocalDecl d.fvarId ty'
  let t ← instantiateMVars (← g.getType)
  let t' ← wgNorm t
  unless t' == t do g ← g.change t'
  replaceMainGoal [g]

def wgDecls {m : Type → Type} [Monad m] (tys : Array Expr) (nm : String) :
    Array (Name × (Array Expr → m Expr)) :=
  tys.mapIdx fun i t => (Name.mkSimple (nm ++ toString i), fun _ => pure t)

def wgUnifySt (a b : Array Expr) : MetaM Bool := do
  if a.size != b.size then return false
  let s ← saveState
  for (x, y) in a.zip b do
    unless ← (try checkpointDefEq (isDefEq x y) catch _ => pure false) do
      s.restore
      return false
  return true

def wgUnifyStC (cst : Array Nat) (a b : Array Expr) : MetaM Bool := do
  if a.size != b.size then return false
  let s ← saveState
  for i in [0 : a.size] do
    if cst.contains i then continue
    unless ← (try checkpointDefEq (isDefEq a[i]! b[i]!) catch _ => pure false) do
      s.restore
      return false
  return true

partial def wgLinA (e : Expr) : Option (Array (Expr × Int) × Int) :=
  let merge := fun (a b : Array (Expr × Int)) (s : Int) => Id.run do
    let mut r := a
    for (t, c) in b do
      match r.findIdx? (·.1 == t) with
      | some i => r := r.set! i (t, r[i]!.2 + s * c)
      | none => r := r.push (t, s * c)
    return r.filter (·.2 != 0)
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
      let (x, c) ← wgLinA a
      let (y, d) ← wgLinA b
      pure (merge x y 1, c + d)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do
      let (x, c) ← wgLinA a
      let (y, d) ← wgLinA b
      pure (merge x y (-1), c - d)
  | (``Neg.neg, #[_, _, a]) => do
      let (x, c) ← wgLinA a
      pure (x.map (fun (t, v) => (t, -v)), -c)
  | (``OfNat.ofNat, #[_, l, _]) =>
      match l with
      | .lit (.natVal v) => some (#[], v)
      | _ => none
  | _ => if e.isFVar then some (#[(e, 1)], 0) else none

def wgLinExpr (ts : Array (Expr × Int)) (c : Int) : MetaM Expr := do
  let mut acc ← arIntLit c
  for (t, v) in ts do
    let tv ← if v == 1 then pure t else mkAppM ``HMul.hMul #[← arIntLit v, t]
    acc ← arAdd tv acc
  return acc

def wgRel? (n a c : Expr) : Option (Int × Int × Bool) :=
  let lin := fun (e : Expr) => do
    let (ts, k) ← wgLinA e
    unless ts.all (fun (t, _) => t == n || t == a) do none
    let cf := fun (v : Expr) => (ts.find? (·.1 == v)).map (·.2) |>.getD 0
    pure (cf n, cf a, k)
  let lf := fun (x y : Expr) => do
    let (x1, y1, c1) ← lin x
    let (x2, y2, c2) ← lin y
    let cn := x1 - x2
    if y1 - y2 == -cn && (cn == 1 || cn == -1) then some (cn, -(c1 - c2)) else none
  match c.getAppFnArgs with
  | (``Eq, #[_, x, y]) => (lf x y).map fun (s, b) => (s, b, true)
  | (``LE.le, #[_, _, x, y]) => (lf x y).map fun (s, b) => (s, b, false)
  | (``LT.lt, #[_, _, x, y]) => (lf x y).map fun (s, b) => (s, b - 1, false)
  | (``GE.ge, #[_, _, x, y]) => (lf y x).map fun (s, b) => (s, b, false)
  | (``GT.gt, #[_, _, x, y]) => (lf y x).map fun (s, b) => (s, b - 1, false)
  | _ => none

partial def wgFlatEx {α : Type} (p : Name) (todo : List Expr) (vs items : Array Expr) (fuel : Nat)
    (k : Array Expr → Array Expr → MetaM α) : MetaM α := do
  match todo with
  | [] => k vs items
  | it :: rest =>
    if it.isAppOf ``HProp.hexists && fuel > 0 then
      return ← peelExG it #[] fun us bd =>
        if us.isEmpty then wgFlatEx p rest vs (items.push it) fuel k
        else wgFlatEx p ((flatStar bd #[]).toList ++ rest) (vs ++ us) items (fuel - 1) k
    if let some q := it.getAppFn.constName? then
      if q != p && fuel > 0 then
        if let some b ← wgHelperBody? q it.getAppArgs then
          return ← wgFlatEx p ((flatStar b #[]).toList ++ rest) vs items (fuel - 1) k
    wgFlatEx p rest vs (items.push it) fuel k

structure WgRB where
  raw : Expr
  us : Array Expr
  items : Array Expr
  pures : Array Expr
  deriving Inhabited

structure WgRd where
  p : Name
  inst : Expr
  xs : Array Expr
  tys : Array Expr
  brs : Array WgRB

partial def wgReadBrs {α : Type} (p : Name) (fuel : Nat) (brs : List Expr) (acc : Array WgRB)
    (k : Array WgRB → MetaM α) : MetaM α :=
  match brs with
  | [] => k acc
  | b :: rest => wgFlatEx p (flatStar b #[]).toList #[] #[] fuel fun us items =>
      wgReadBrs p fuel rest (acc.push { raw := b, us, items, pures := items.foldl (fun a it =>
        if it.isAppOfArity ``HProp.hpure 2 then pureConjs it.appArg! a else a) #[] }) k

def wgRead {α : Type} (p : Name) (k : WgRd → MetaM (Option α)) : MetaM (Option α) := do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let some ent := entries.find? (·.headFn == p) | return none
  forallTelescopeReducing (← getConstInfo ent.lemmaName).type fun xs concl => do
    let some (eqT, _, body) := concl.eq? | return none
    let brs := wgBranches body #[]
    let fuel := brs.foldl (fun a b => a + b.approxDepth.toNat) 0
    wgReadBrs p fuel brs.toList #[] fun rbs => do
      k { p, inst := eqT.appArg!, xs, tys := ← xs.mapM inferType, brs := rbs }

initialize wgPCache : IO.Ref (Array (Name × Option WgP)) ← IO.mkRef #[]
initialize wgLCache : IO.Ref (Array (String × Option Expr)) ← IO.mkRef #[]
initialize wgUsedCache : IO.Ref (Array (Expr × Array Name)) ← IO.mkRef #[]
initialize wgMCache : IO.Ref (Array ((Name × Name) × Option (Array Nat × Bool × Option Expr))) ←
  IO.mkRef #[]

def wgPathInfo (rd : WgRd) : MetaM (Option (Expr × Option Expr × Array (Array (Bool × Name)))) := do
    let xs := rd.xs
    unless xs.size == 2 do return none
    for x in xs do
      unless ← isDefEq (← inferType x) (mkConst ``Nat) do return none
    let inst := rd.inst
    let mut cLam : Option Expr := none
    let mut brs : Array (Array (Bool × Name)) := #[]
    for rb in rd.brs do
      let r ← (do
        let items := rb.items
        let mut cells : Array (Expr × Expr × Expr) := #[]
        let mut atoms : Array (Name × Expr × Expr) := #[]
        let pures := rb.pures
        for it in items do
          match it.getAppFnArgs with
          | (``HProp.hpure, _) => pure ()
          | (``HProp.hsingle, #[_, a, v]) => cells := cells.push (a, v, it)
          | _ =>
            match it.getAppFn.constName? with
            | some q =>
              if it.getAppNumArgs == 2 then
                atoms := atoms.push (q, it.getAppArgs[0]!, it.getAppArgs[1]!)
              else return none
            | none => return none
        let mut cl : Option Expr := none
        let mut nexts : Array Expr := #[]
        for (a, v, h) in cells do
          let fvs := (Lean.collectFVars {} v).fvarIds
          unless fvs.size == 1 do return none
          let nx := mkFVar fvs[0]!
          nexts := nexts.push nx
          let gs := pures.filter (fun q => match q.getAppFnArgs with
            | (``Ne, #[_, x, y]) => x == a || y == a
            | _ => false)
          let other := fun (q : Expr) => match q.getAppFnArgs with
            | (``Ne, #[_, x, y]) => if x == a then y else x
            | _ => q
          if gs.any (fun q => other q != other gs[0]!) then return none
          let guard := gs[0]?
          let ta ← inferType a
          let tn ← inferType nx
          let lam ← withLocalDeclD `la ta fun la => withLocalDeclD `lb tn fun lb => do
            let hs := (h.replaceFVar a la).replaceFVar nx lb
            let body ← match guard with
              | some g => mkAppM ``HProp.hstar #[← mkAppOptM ``HProp.hpure #[inst, g.replaceFVar a la], hs]
              | none => pure hs
            mkLambdaFVars #[la, lb] body
          if lam.hasFVar then return none
          if let some c0 := cl then
            unless c0 == lam do return none
          else cl := some lam
        for q in pures do
          match q.getAppFnArgs with
          | (``Ne, #[_, x, y]) => unless cells.any (fun c => c.1 == x || c.1 == y) do return none
          | (``Eq, #[_, x, y]) => unless (x == xs[0]! && y == xs[1]!) || (x == xs[1]! && y == xs[0]!) do return none
          | (``True, _) => pure ()
          | _ => return none
        let mut cur := xs[0]!
        let mut used : Array Nat := #[]
        let mut usedA : Array Nat := #[]
        let mut ps : Array (Bool × Name) := #[]
        for _ in [0 : cells.size + atoms.size] do
          match (Array.range cells.size).find? (fun i => !used.contains i && cells[i]!.1 == cur) with
          | some i =>
            used := used.push i
            ps := ps.push (true, .anonymous)
            cur := nexts[i]!
          | none =>
            match (Array.range atoms.size).find? (fun i => !usedA.contains i && atoms[i]!.2.1 == cur) with
            | some i =>
              usedA := usedA.push i
              ps := ps.push (false, atoms[i]!.1)
              cur := atoms[i]!.2.2
            | none => break
        unless used.size == cells.size && usedA.size == atoms.size do return none
        if ps.isEmpty then
          unless pures.any (fun q => q.isAppOf ``Eq) do return none
        else unless cur == xs[1]! do return none
        return some (cl, ps) : MetaM (Option (Option Expr × Array (Bool × Name))))
      let some (cl, ps) := r | return none
      if let some l := cl then
        if let some c0 := cLam then
          unless c0 == l do return none
        else cLam := some l
      brs := brs.push ps
    return some (inst, cLam, brs)

def wgPhi (S : Array Bool) : Option (Nat × Nat × Array Nat) := do
  let m ← (Array.range S.size).find? (fun i => S[i]!)
  let p ← (List.range (S.size / 4)).map (· + 1) |>.find? (fun p => (List.range S.size).all (fun n =>
    n < m || n + p ≥ S.size || S[n]! == S[n + p]!))
  let rs := (List.range p).filter (fun r => m + r < S.size && S[m + r]!)
  some (m, p, rs.toArray)

def wgPhiExpr (m p : Nat) (rs : Array Nat) (n : Expr) : MetaM Expr := do
  let ge ← mkAppM ``LE.le #[← arIntLit m, n]
  if p == 1 then return ge
  let d ← mkAppM ``HMod.hMod #[← mkAppM ``HSub.hSub #[n, ← arIntLit m], ← arIntLit p]
  let mut alts : Array Expr := #[]
  for r in rs do alts := alts.push (← mkAppM ``Eq #[d, ← arIntLit r])
  let mut disj := alts[alts.size - 1]!
  for i in [0 : alts.size - 1] do disj ← mkAppM ``Or #[alts[alts.size - 2 - i]!, disj]
  mkAppM ``And #[ge, disj]

structure WgPGI where
  inst : Expr
  C : Expr
  ms : Array Name
  B : Expr
  prof : Array (Nat × Nat × Array Nat)
  profE : Expr
  hA : Expr
  rkE : Expr
  NE : Expr
  spsE : Expr
  certE : Expr
  hC : Expr
  absT : Array Expr
  concG : Expr
  pbrs : Array (Array (Array (Bool × Name)))
  deriving Inhabited

initialize wgPGCache : IO.Ref (Array (Array Name × Option WgPGI)) ← IO.mkRef #[]

def wgPGTable (bs : Array (Array (Array (Option Nat)))) (W : Nat) : Array (Array Bool) := Id.run do
  let R := bs.size
  let mut S := Array.replicate R (Array.replicate (W + 1) false)
  for _ in [0 : R * (W + 1) + 1] do
    let mut changed := false
    for j in [0 : R] do
      for br in bs[j]! do
        let mut cur := Array.replicate (W + 1) false
        let nc := (br.filter (·.isNone)).size
        if nc ≤ W then cur := cur.set! nc true
        for it in br do
          if let some q := it then
            let sq := S[q]!
            let mut nxt := Array.replicate (W + 1) false
            for a in [0 : W + 1] do
              if cur[a]! then
                for b in [0 : W + 1 - a] do
                  if sq[b]! then nxt := nxt.set! (a + b) true
            cur := nxt
        for n in [0 : W + 1] do
          if cur[n]! && !S[j]![n]! then
            S := S.modify j (·.set! n true)
            changed := true
    if !changed then break
  return S

def wgInS (pr : Nat × Nat × Array Nat) (n : Nat) : Bool :=
  pr.1 ≤ n && pr.2.2.contains ((n - pr.1) % pr.2.1)

partial def wgPGSplit (vals : Nat → Array Nat) (calls : List Nat) (t : Nat) : Option (List Nat) :=
  match calls with
  | [] => if t == 0 then some [] else none
  | q :: rest => (vals q).findSome? fun c =>
      if c ≤ t then (wgPGSplit vals rest (t - c)).map (c :: ·) else none

partial def wgPGFixed (vals : Nat → Array Nat) (calls : List Nat) (ok : List Nat → Bool) (acc : List Nat) :
    Option (List Nat) :=
  match calls with
  | [] => if ok acc.reverse then some acc.reverse else none
  | q :: rest => (vals q).findSome? fun c => wgPGFixed vals rest ok (c :: acc)

def wgPGRule (bs : Array (Array (Array (Option Nat)))) (prof : Array (Nat × Nat × Array Nat)) (rk : Array Nat)
    (vals : Nat → Array Nat) (j sp mj r : Nat) : Option (Nat × Nat × Array (Option Nat) × Nat × Nat × Nat) := Id.run do
  for bi in [0 : bs[j]!.size] do
    let br := bs[j]!
    let br := br[bi]!
    let nc := (br.filter (·.isNone)).size
    let calls := br.filterMap id
    for l0 in [0 : calls.size] do
      let q0 := calls[l0]!
      let (mq, pq, rsq) := prof[q0]!
      let others := (calls.eraseIdxIfInBounds l0).toList
      let ok := fun (cs : List Nat) =>
        let d := nc + cs.foldl (· + ·) 0
        (0 < d || rk[q0]! < rk[j]!) &&
        (List.range pq).all (fun t =>
          let n := mj + r + sp * (d + mq + t)
          rsq.contains ((n - d - mq) % pq))
      if let some cs := wgPGFixed vals others ok [] then
        let d := nc + cs.foldl (· + ·) 0
        let mut ls : Array (Option Nat) := #[]
        let mut ci := 0
        for l in [0 : calls.size] do
          if l == l0 then ls := ls.push none
          else
            ls := ls.push (some cs[ci]!)
            ci := ci + 1
        let nn := cs.foldl (fun a c => max a (c + 1)) (d + mq)
        return some (r, bi, ls, d, q0, nn)
  return none

def wgPGCert (bs : Array (Array (Array (Option Nat)))) (prof : Array (Nat × Nat × Array Nat)) (W : Nat) :
    Option (Array Nat × Nat × Array Nat ×
      Array (Array (Nat × Nat × Array (Option Nat)) × Array (Nat × Nat × Nat × Array (Option Nat)))) := Id.run do
  let R := bs.size
  let mut edges : Array (Nat × Nat) := #[]
  for j in [0 : R] do
    for br in bs[j]! do
      if br.any (·.isNone) then continue
      let calls := br.filterMap id
      for l in [0 : calls.size] do
        let others := (calls.eraseIdxIfInBounds l)
        if others.all (fun q => wgInS prof[q]! 0) then edges := edges.push (j, calls[l]!)
  let mut rk := Array.replicate R 0
  let mut stable := false
  for _ in [0 : R + 1] do
    let mut nrk := rk
    for (a, b) in edges do
      if nrk[a]! < rk[b]! + 1 then nrk := nrk.set! a (rk[b]! + 1)
    if nrk == rk then
      stable := true
      break
    rk := nrk
  unless stable && rk.all (· < R) do return none
  let vals := fun (q : Nat) => ((List.range (W + 1)).filter (wgInS prof[q]!)).toArray
  let mut bigs : Array (Array (Nat × Nat × Nat × Array (Option Nat) × Nat × Nat)) := #[]
  let L := prof.foldl (fun a pr => a * pr.2.1 / Nat.gcd a pr.2.1) 1
  let mut N := 1
  let mut sps : Array Nat := #[]
  for j in [0 : R] do
    let (mj, pj, rsj) := prof[j]!
    let mut chosen : Option (Nat × Array (Nat × Nat × Array (Option Nat) × Nat × Nat × Nat)) := none
    for t in [1 : L + 1] do
      if chosen.isSome then break
      let sp := pj * t
      let mut bj : Array (Nat × Nat × Array (Option Nat) × Nat × Nat × Nat) := #[]
      let mut okAll := true
      for r in (List.range sp).filter (fun r => rsj.contains (r % pj)) do
        match wgPGRule bs prof rk vals j sp mj r with
        | some e => bj := bj.push e
        | none =>
          okAll := false
          break
      if okAll then chosen := some (sp, bj)
    let some (sp, bj) := chosen | return none
    for (_, _, _, _, _, nn) in bj do N := max N nn
    sps := sps.push sp
    bigs := bigs.push (bj.map fun (r, bi, ls, d, q0, _) => (r, bi, 0, ls, d, q0))
  if N > W then return none
  let mut cert : Array (Array (Nat × Nat × Array (Option Nat)) × Array (Nat × Nat × Nat × Array (Option Nat))) := #[]
  for j in [0 : R] do
    let mj := prof[j]!.1
    let mut sm : Array (Nat × Nat × Array (Option Nat)) := #[]
    for n in [0 : N] do
      unless wgInS prof[j]! n do continue
      let mut got : Option (Nat × Array (Option Nat)) := none
      for bi in [0 : bs[j]!.size] do
        if got.isSome then break
        let br := bs[j]!
        let br := br[bi]!
        let nc := (br.filter (·.isNone)).size
        if nc > n then continue
        let calls := (br.filterMap id).toList
        let vq := fun (q : Nat) => (vals q).filter (fun c => c < n || (c == n && rk[q]! < rk[j]!))
        if let some cs := wgPGSplit vq calls (n - nc) then
          got := some (bi, (cs.map some).toArray)
      match got with
      | some (bi, ls) => sm := sm.push (n, bi, ls)
      | none => return none
    let sp := sps[j]!
    let bg := bigs[j]!.map fun (r, bi, _, ls, _, _) =>
      let n0 := if N ≤ mj + r then mj + r else mj + r + sp * ((N - mj - r + sp - 1) / sp)
      (r, bi, n0, ls)
    cert := cert.push (sm, bg)
  return some (rk, N, sps, cert)

def wgPGNat : Expr := mkConst ``Nat

def wgPGTup (j : Nat) (x y : Expr) : Expr :=
  let np := mkApp2 (mkConst ``Prod [0, 0]) wgPGNat wgPGNat
  mkApp4 (mkConst ``Prod.mk [0, 0]) wgPGNat np (mkNatLit j) (mkApp4 (mkConst ``Prod.mk [0, 0]) wgPGNat wgPGNat x y)

def wgPGAt (inst C B : Expr) (j : Nat) (x y : Expr) : Expr :=
  mkAppN (mkConst ``Sep.pG) #[inst, C, B, wgPGTup j x y]

partial def wgPGInj (e : Expr) (acc : Nat := 0) : Nat × Expr :=
  if e.isAppOfArity ``Sum.inl 3 then (acc, e.appArg!)
  else if e.isAppOfArity ``Sum.inr 3 then wgPGInj e.appArg! (acc + 1)
  else (acc, e)

def wgPGWalk (leaves : Array Expr) (x y : Expr) (call : Expr → Option (Nat × Expr × Expr)) :
    Option (Array (Option Nat × Expr × Expr) × Option Bool) := Id.run do
  let mut items : Array (Option Nat × Expr × Expr) := #[]
  let mut eqs : Option Bool := none
  for l in leaves do
    match l.getAppFnArgs with
    | (``HProp.hsingle, #[_, a, v]) =>
      unless v.isAppOfArity ``Nat.cast 3 do return none
      items := items.push (none, a, v.appArg!)
    | (``HProp.hpure, #[_, pr]) =>
      match pr.getAppFnArgs with
      | (``Ne, #[_, _, _]) => pure ()
      | (``Eq, #[_, a, b]) =>
        if a == x && b == y then eqs := some true
        else if a == y && b == x then eqs := some false
        else return none
      | _ => return none
    | (``HProp.hempty, _) => pure ()
    | _ =>
      match call l with
      | some (q, s, t) => items := items.push (some q, s, t)
      | none => return none
  if items.isEmpty then
    if eqs.isNone then return none
    return some (#[], eqs)
  if eqs.isSome then return none
  let mut cur := x
  let mut used : Array Bool := Array.replicate items.size false
  let mut out : Array (Option Nat × Expr × Expr) := #[]
  for _ in [0 : items.size] do
    match (Array.range items.size).find? (fun i => !used[i]! && items[i]!.2.1 == cur) with
    | some i =>
      used := used.set! i true
      out := out.push items[i]!
      cur := items[i]!.2.2
    | none => return none
  unless cur == y do return none
  return some (out, none)

def wgPGChain (inst C : Expr) (leaf : Nat → Expr → Expr → Expr) (items : Array (Option Nat × Expr × Expr))
    (x y : Expr) : Expr :=
  if items.isEmpty then mkApp2 (mkConst ``HProp.hpure) inst (mkApp3 (mkConst ``Eq [1]) wgPGNat x y)
  else starOf inst (items.toList.map fun (k, s, t) => match k with
    | none => C.beta #[s, t]
    | some q => leaf q s t)

partial def wgPGExL (inst : Expr) (br tgt : Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  if br.isAppOfArity ``HProp.hexists 3 then
    let A := br.appFn!.appArg!
    unless A == wgPGNat do throwError "pg: ex"
    let lam := br.appArg!
    withLocalDeclD `v A fun v => do
      let pf ← wgPGExL inst (lam.beta #[v]) tgt k
      let pfl ← mkLambdaFVars #[v] pf
      return mkAppN (mkConst ``HProp.himpl_hexists_l [1]) #[inst, A, tgt, lam, pfl]
  else k br

def wgPGIsNe (e : Expr) : Bool := e.isAppOfArity ``HProp.hpure 2 && e.appArg!.isAppOfArity ``Ne 3

partial def wgPGFrameS (inst : Expr) (leafF : Expr → Option (Expr × Expr)) (e : Expr) :
    StateM (Array Expr) (Expr × Option Expr) := do
  if e.isAppOfArity ``HProp.hstar 3 then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    let (a', pa) ← wgPGFrameS inst leafF a
    let (b', pb) ← wgPGFrameS inst leafF b
    if pa.isNone && pb.isNone then return (e, none)
    let ra := pa.getD (mkApp2 (mkConst ``HProp.himpl_refl) inst a)
    let rb := pb.getD (mkApp2 (mkConst ``HProp.himpl_refl) inst b)
    return (mkApp3 (mkConst ``HProp.hstar) inst a' b',
      some (mkAppN (mkConst ``HProp.himpl_frame_lr) #[inst, a, a', b, b', ra, rb]))
  if wgPGIsNe e then
    let st ← get
    match st.findIdx? (· == e) with
    | some i =>
      set (st.eraseIdxIfInBounds i)
      return (e, none)
    | none => return (mkApp (mkConst ``HProp.hempty) inst, some (mkApp2 (mkConst ``Sep.pDrop) inst e.appArg!))
  match leafF e with
  | some (e', pf) => return (e', some pf)
  | none => return (e, none)

partial def wgPGFirst (inst tgt repl pf : Expr) (e : Expr) : StateM Bool (Expr × Option Expr) := do
  if (← get) then return (e, none)
  if e.isAppOfArity ``HProp.hstar 3 then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    let (a', pa) ← wgPGFirst inst tgt repl pf a
    let (b', pb) ← wgPGFirst inst tgt repl pf b
    if pa.isNone && pb.isNone then return (e, none)
    let ra := pa.getD (mkApp2 (mkConst ``HProp.himpl_refl) inst a)
    let rb := pb.getD (mkApp2 (mkConst ``HProp.himpl_refl) inst b)
    return (mkApp3 (mkConst ``HProp.hstar) inst a' b',
      some (mkAppN (mkConst ``HProp.himpl_frame_lr) #[inst, a, a', b, b', ra, rb]))
  if e == tgt then
    set true
    return (repl, some pf)
  return (e, none)

def wgPGNeFix (inst chain Tw : Expr) : Option (Expr × Option Expr) := Id.run do
  let mut have_ := (flatStar chain #[]).filter wgPGIsNe
  let mut need : Array Expr := #[]
  for l in (flatStar Tw #[]).filter wgPGIsNe do
    match have_.findIdx? (· == l) with
    | some i => have_ := have_.eraseIdxIfInBounds i
    | none => need := need.push l
  let mut cur := chain
  let mut pf : Option Expr := none
  for n in need do
    let pr := n.appArg!
    let a := pr.getAppArgs[1]!
    let b := pr.getAppArgs[2]!
    let sym := mkApp2 (mkConst ``HProp.hpure) inst (mkApp3 (mkConst ``Ne [1]) (pr.getAppArgs[0]!) b a)
    let leaves := flatStar cur #[]
    let (src, lp) := if leaves.contains n then (n, mkApp2 (mkConst ``Sep.pDup) inst pr)
      else (sym, mkAppN (mkConst ``Sep.pDupNe) #[inst, b, a])
    unless leaves.contains src do return none
    let ((cur', p1), _) := (wgPGFirst inst src (mkApp3 (mkConst ``HProp.hstar) inst src n) lp cur).run false
    let some p1 := p1 | return none
    pf := some (match pf with
      | some p0 => mkAppN (mkConst ``HProp.himpl_trans) #[inst, chain, cur, cur', p0, p1]
      | none => p1)
    cur := cur'
  return some (cur, pf)

partial def wgPGSel (inst H : Expr) (e : Expr) (k : Nat) (pf : Expr) : Expr :=
  if isHorConst e && e.getAppNumArgs ≥ 2 then
    let a := e.getAppArgs
    let l := a[a.size - 2]!
    let r := a[a.size - 1]!
    let nl := (wgBranches l #[]).size
    if k < nl then mkAppN (mkConst ``hdisj_left) #[inst, H, l, r, wgPGSel inst H l k pf]
    else mkAppN (mkConst ``hdisj_right) #[inst, H, l, r, wgPGSel inst H r (k - nl) pf]
  else pf

partial def wgPGElim (inst tgt : Expr) (e : Expr) (pfs : Array Expr) (i : Nat) : Expr × Nat :=
  if isHorConst e && e.getAppNumArgs ≥ 2 then
    let a := e.getAppArgs
    let l := a[a.size - 2]!
    let r := a[a.size - 1]!
    let (pl, i1) := wgPGElim inst tgt l pfs i
    let (pr, i2) := wgPGElim inst tgt r pfs i1
    (mkAppN (mkConst ``hdisj_elim) #[inst, l, r, tgt, pl, pr], i2)
  else (pfs[i]!, i + 1)

def wgPGList (ty : Expr) (l : List Expr) : Expr :=
  l.foldr (fun a acc => mkApp3 (mkConst ``List.cons [0]) ty a acc) (mkApp (mkConst ``List.nil [0]) ty)

def wgPGLty : Expr := mkApp (mkConst ``List [0]) (mkApp (mkConst ``Option [0]) wgPGNat)

def wgPGBj (B : Expr) (j : Nat) : Expr :=
  mkApp4 (mkConst ``Sep.pNthK) (mkApp (mkConst ``List [0]) wgPGLty) B (mkNatLit j)
    (mkApp (mkConst ``List.nil [0]) wgPGLty)

partial def wgPGCases (inst np F Xf : Expr) (sumTy : Nat → Expr) (wrap : Nat → Expr → Expr) (pfs : Array Expr)
    (k i : Nat) (s : Expr) : MetaM Expr := do
  if i + 1 == k then return mkApp pfs[i]! s
  let mot ← withLocalDeclD `s (sumTy i) fun s => do
    let a := wrap i s
    mkLambdaFVars #[s] (mkApp3 (mkConst ``HProp.himpl) inst (mkApp2 F Xf a) (mkApp Xf a))
  let inr ← withLocalDeclD `s (sumTy (i + 1)) fun s' => do
    mkLambdaFVars #[s'] (← wgPGCases inst np F Xf sumTy wrap pfs k (i + 1) s')
  return mkAppN (mkConst ``Sum.casesOn [0, 0, 0]) #[np, sumTy (i + 1), mot, s, pfs[i]!, inr]

def wgPGAbsGroup (inst C B : Expr) (ms : Array Name) (bs : Array (Array (Array (Option Nat))))
    (F : Expr) (mem : Array (Nat × Nat)) (absT : Array (Option Expr)) : MetaM (Array (Nat × Expr)) := do
  let nat := wgPGNat
  let np := mkApp2 (mkConst ``Prod [0, 0]) nat nat
  let some Fn := F.constName? | throwError "pg: F"
  let some Fv := (← getConstInfo Fn).value? | throwError "pg: Fv"
  let .lam _ xTy fb _ := Fv | throwError "pg: Flam"
  let aty := xTy.bindingDomain!
  let k := mem.size
  let order ← (List.range k).toArray.mapM fun li => match mem.find? (·.1 == li) with
    | some m => pure m.2
    | none => throwError "pg: order"
  let hpT := mkApp (mkConst ``HProp) inst
  let sumTy := fun (i : Nat) => Id.run do
    let mut acc := np
    for _ in [0 : k - 1 - i] do acc := mkApp2 (mkConst ``Sum [0, 0]) np acc
    return acc
  let fst := fun (e : Expr) => mkApp3 (mkConst ``Prod.fst [0, 0]) nat nat e
  let snd := fun (e : Expr) => mkApp3 (mkConst ``Prod.snd [0, 0]) nat nat e
  let mut Xe : Expr := default
  for t in [0 : k] do
    let li := k - 1 - t
    let lam ← withLocalDeclD `p np fun pv => mkLambdaFVars #[pv] (wgPGAt inst C B order[li]! (fst pv) (snd pv))
    Xe := if t == 0 then lam else mkAppN (mkConst ``Sum.elim [0, 0, 1]) #[np, sumTy (li + 1), hpT, lam, Xe]
  let hstep ← withLocalDeclD `X xTy fun Xf => do
    let body := fb.instantiate1 Xf
    let mut cur := body
    let mut arms : Array Expr := #[]
    for li in [0 : k] do
      if li + 1 < k then
        unless cur.isAppOfArity ``Sum.elim 5 do throwError "pg: elim"
        arms := arms.push cur.getAppArgs[3]!
        cur := cur.getAppArgs[4]!
      else arms := arms.push cur
    let callF := fun (l : Expr) => Id.run do
      if l.isApp && l.appFn! == Xf then
        let (li, pl) := wgPGInj l.appArg!
        unless pl.isAppOfArity ``Prod.mk 4 do return none
        let some j := order[li]? | return none
        return some (j, pl.appFn!.appArg!, pl.appArg!)
      match l.getAppFn.constName? with
      | some q =>
        if l.getAppNumArgs == 2 && ms.contains q then return some (ms.idxOf q, l.appFn!.appArg!, l.appArg!)
        return none
      | none => return none
    let leafF := fun (l : Expr) => Id.run do
      if l.isApp && l.appFn! == Xf then
        let (li, pl) := wgPGInj l.appArg!
        let some j := order[li]? | return none
        let e' := wgPGAt inst C B j pl.appFn!.appArg! pl.appArg!
        return some (e', mkApp2 (mkConst ``HProp.himpl_refl) inst e')
      match l.getAppFn.constName? with
      | some q =>
        if l.getAppNumArgs == 2 && ms.contains q then
          let j := ms.idxOf q
          if let some (some ab) := absT[j]? then
            let s := l.appFn!.appArg!
            let t := l.appArg!
            return some (wgPGAt inst C B j s t, mkApp2 ab s t)
        return none
      | none => return none
    let mut pfs : Array Expr := #[]
    for li in [0 : k] do
      let j := order[li]!
      let arm := arms[li]!
      unless arm.isLambda && arm.bindingDomain! == np do throwError "pg: arm"
      let pfl ← withLocalDeclD `p np fun pv => do
        let x := fst pv
        let y := snd pv
        let armB := arm.beta #[pv]
        let tgt := wgPGAt inst C B j x y
        let brs := wgBranches armB #[]
        let mut bpfs : Array Expr := #[]
        for br in brs do
          let pf ← wgPGExL inst br tgt fun T => do
            let leaves := flatStar T #[]
            let some (items, eqs) := wgPGWalk leaves x y callF | throwError "pg: walk"
            let bl := items.map (·.1)
            let some bi := bs[j]!.findIdx? (· == bl) | throwError "pg: branch"
            let leafF2 := fun (l : Expr) =>
              if eqs == some false && l.isAppOfArity ``HProp.hpure 2 && l.appArg!.isAppOfArity ``Eq 3 then
                some (mkApp2 (mkConst ``HProp.hpure) inst (mkApp3 (mkConst ``Eq [1]) nat x y),
                  mkAppN (mkConst ``Sep.pEqSymm) #[inst, y, x])
              else leafF l
            let chain := wgPGChain inst C (fun q s t => wgPGAt inst C B q s t) items x y
            let ((T', pf1), _) := (wgPGFrameS inst leafF2 T).run ((flatStar chain #[]).filter wgPGIsNe)
            let pf2 ← if T' == chain then pure (mkApp2 (mkConst ``HProp.himpl_refl) inst chain) else
              match ← provePerm T' chain with
              | some p => pure p
              | none => throwError "pg: perm"
            let pfT := match pf1 with
              | some p1 => mkAppN (mkConst ``HProp.himpl_trans) #[inst, T, T', chain, p1, pf2]
              | none => pf2
            let nodes := (items.map (·.2.2)).pop
            let f ← withLocalDeclD `i nat fun iv =>
              mkLambdaFVars #[iv] (mkApp4 (mkConst ``Sep.pNthK) nat (wgPGList nat nodes.toList) iv (mkNatLit 0))
            let Bj := wgPGBj B j
            let hi := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
            let hb := mkAppN (mkConst ``Sep.pMem) #[wgPGLty, Bj, mkNatLit bi, mkApp (mkConst ``List.nil [0])
              (mkApp (mkConst ``Option [0]) nat), hi]
            return mkAppN (mkConst ``Sep.pG_intro) #[inst, C, B, mkNatLit j, x, y, toExpr bl.toList, hb, f, T, pfT]
          bpfs := bpfs.push pf
        let (pfArm, _) := wgPGElim inst tgt armB bpfs 0
        mkLambdaFVars #[pv] pfArm
      pfs := pfs.push pfl
    let wrap := fun (i : Nat) (s : Expr) => Id.run do
      let mut e := s
      for t in [0 : i] do
        let lvl := i - 1 - t
        e := mkApp3 (mkConst ``Sum.inr [0, 0]) np (sumTy (lvl + 1)) e
      return e
    let st ← withLocalDeclD `b aty fun b => do mkLambdaFVars #[b] (← wgPGCases inst np F Xf sumTy wrap pfs k 0 b)
    let l ← mkLambdaFVars #[Xf] st
    return l.bindingBody!.instantiate1 Xe
  let mut out : Array (Nat × Expr) := #[]
  for j in order do
    let e ← withLocalDeclD `x nat fun x => withLocalDeclD `y nat fun y => do
      let some (_, ta) ← functionalOf? (mkApp2 (mkConst ms[j]!) x y) | throwError "pg: ta"
      mkLambdaFVars #[x, y] (mkAppN (mkConst ``lfpG_induct) #[inst, aty, F, Xe, hstep, ta])
    out := out.push (j, e)
  return out

def wgPGAbsAll (inst C B : Expr) (ms : Array Name) (bs : Array (Array (Array (Option Nat)))) :
    MetaM (Array Expr) := do
  let nat := wgPGNat
  let mut grp : Array (Expr × Array (Nat × Nat)) := #[]
  for j in [0 : ms.size] do
    let (F, li) ← withLocalDeclD `x nat fun x => withLocalDeclD `y nat fun y => do
      let some (F, ta) ← functionalOf? (mkApp2 (mkConst ms[j]!) x y) | throwError "pg: functional"
      return (F, (wgPGInj ta).1)
    match grp.findIdx? (·.1 == F) with
    | some g => grp := grp.modify g fun (f, l) => (f, l.push (li, j))
    | none => grp := grp.push (F, #[(li, j)])
  let mut absT : Array (Option Expr) := Array.replicate ms.size none
  for _ in [0 : grp.size] do
    for (F, mem) in grp do
      if mem.all (fun m => absT[m.2]!.isSome) then continue
      let own := mem.map (·.2)
      let deps := own.foldl (fun acc j => acc ++ (bs[j]!.foldl (fun a br => a ++ br.filterMap id) #[])) #[]
      unless deps.all (fun d => own.contains d || absT[d]!.isSome) do continue
      for (j, e) in ← wgPGAbsGroup inst C B ms bs F mem absT do absT := absT.set! j (some e)
  unless absT.all (·.isSome) do throwError "pg: groups"
  return absT.map (·.get!)

partial def wgPGIntro (inst H : Expr) (e : Expr) (ws : List Expr) (k : Expr → MetaM Expr) : MetaM Expr := do
  if e.isAppOfArity ``HProp.hexists 3 then
    let A := e.appFn!.appArg!
    let lam := e.appArg!
    let w :: rest := ws | throwError "pg: witness"
    let pf ← wgPGIntro inst H (lam.beta #[w]) rest k
    return mkAppN (mkConst ``HProp.himpl_hexists_r [1]) #[inst, A, w, H, lam, pf]
  else k e

def wgPGConcAll (inst C B : Expr) (ms : Array Name) (bs : Array (Array (Array (Option Nat)))) : MetaM Expr := do
  let nat := wgPGNat
  let fty := mkApp (mkConst ``HProp) inst
  let pty ← mkArrow nat (← mkArrow nat fty)
  let MsE := wgPGList pty (ms.toList.map mkConst)
  let gc := mkAppN (mkConst ``Sep.pG_conc) #[inst, C, B, MsE]
  let gcT ← inferType gc
  let Pidx := gcT.bindingDomain!.getAppArgs[0]!
  let entries ← arEntries
  let R := ms.size
  let mut comps : Array Expr := #[]
  for i in [0 : R] do
    let Pi ← whnfCore (Pidx.beta #[mkNatLit i])
    let Pb ← forallBoundedTelescope Pi (some 2) fun bh body => mkLambdaFVars #[bh[0]!] body
    let some ent := entries.find? (·.headFn == ms[i]!) | throwError "pg: unfold"
    let mut prfs : Array Expr := #[]
    for bi in [0 : bs[i]!.size] do
      let pf ← withLocalDeclD `f (← mkArrow nat nat) fun f => withLocalDeclD `x nat fun x =>
        withLocalDeclD `y nat fun y => do
        let eqPf := mkApp2 (mkConst ent.lemmaName) x y
        let some (_, lhs, rhs) := (← inferType eqPf).eq? | throwError "pg: eq"
        let brs := wgBranches rhs #[]
        let some br := brs[bi]? | throwError "pg: br"
        let callF := fun (l : Expr) => match l.getAppFn.constName? with
          | some q => if l.getAppNumArgs == 2 && ms.contains q then some (ms.idxOf q, l.appFn!.appArg!, l.appArg!) else none
          | none => none
        let (items, eqs, ws) ← peelExG br #[] fun vs T => do
          let some (items, eqs) := wgPGWalk (flatStar T #[]) x y callF | throwError "pg: cwalk"
          unless items.map (·.1) == bs[i]![bi]! do throwError "pg: cbranch"
          let nodes := (items.map (·.2.2)).pop
          let mut ws : Array Expr := #[]
          for v in vs do
            let some pos := nodes.findIdx? (· == v) | throwError "pg: node"
            ws := ws.push (mkApp f (mkNatLit pos))
          let sub := fun (e : Expr) => e.replaceFVars vs ws
          return (items.map (fun (q, s, t) => (q, sub s, sub t)), eqs, ws)
        let chain := wgPGChain inst C (fun q s t => mkApp2 (mkConst ms[q]!) s t) items x y
        let (chainB, pre) := if eqs == some false then
            (mkApp2 (mkConst ``HProp.hpure) inst (mkApp3 (mkConst ``Eq [1]) nat y x),
              some (mkAppN (mkConst ``Sep.pEqSymm) #[inst, x, y]))
          else (chain, none)
        let pfBr ← wgPGIntro inst chain br ws.toList fun Tw => do
          let some (chainC, pfx) := wgPGNeFix inst chainB Tw | throwError "pg: ne"
          let p ← if chainC == Tw then pure (mkApp2 (mkConst ``HProp.himpl_refl) inst Tw) else
            match ← provePerm chainC Tw with
            | some p => pure p
            | none => throwError "pg: cperm"
          let p := match pfx with
            | some q => mkAppN (mkConst ``HProp.himpl_trans) #[inst, chainB, chainC, Tw, q, p]
            | none => p
          return match pre with
            | some q => mkAppN (mkConst ``HProp.himpl_trans) #[inst, chain, chainB, Tw, q, p]
            | none => p
        let pfSel := wgPGSel inst chain rhs bi pfBr
        let back := mkAppN (mkConst ``himpl_of_eq) #[inst, rhs, lhs,
          mkApp4 (mkConst ``Eq.symm [1]) fty lhs rhs eqPf]
        mkLambdaFVars #[f, x, y] (mkAppN (mkConst ``HProp.himpl_trans) #[inst, chain, rhs, lhs, pfSel, back])
      prfs := prfs.push pf
    let lits := bs[i]!.toList.map (fun b => toExpr b.toList)
    let mut acc := mkApp2 (mkConst ``Sep.pAll_nil) wgPGLty Pb
    for t in [0 : prfs.size] do
      let bi := prfs.size - 1 - t
      acc := mkAppN (mkConst ``Sep.pAll_cons) #[wgPGLty, Pb, lits[bi]!, toExpr ((bs[i]!.toList.drop (bi + 1)).map (·.toList)),
        prfs[bi]!, acc]
    comps := comps.push acc
  let mut H := mkConst ``True.intro
  for t in [0 : R] do
    let i := R - 1 - t
    let a := Pidx.beta #[mkNatLit i]
    let b := mkApp3 (mkConst ``Sep.pAllIdx) Pidx (mkNatLit (i + 1)) (mkNatLit (R - 1 - i))
    H := mkApp4 (mkConst ``And.intro) a b comps[i]! H
  withLocalDeclD `j nat fun j => withLocalDeclD `x nat fun x => withLocalDeclD `y nat fun y => do
    mkLambdaFVars #[j, x, y] (mkAppN gc #[H, j, x, y])

def wgPGBuild (p : Name) : MetaM (Option WgPGI) := do
  let mut todo : Array Name := #[p]
  let mut infos : Array (Name × Expr × Option Expr × Array (Array (Bool × Name))) := #[]
  while !todo.isEmpty do
    let q := todo.back!
    todo := todo.pop
    if infos.any (·.1 == q) then continue
    let some (inst, c, brs) ← wgRead q wgPathInfo | return none
    infos := infos.push (q, inst, c, brs)
    for br in brs do
      for (isC, nm) in br do
        if !isC && !infos.any (·.1 == nm) && !todo.contains nm then todo := todo.push nm
  let ms := infos.map (·.1)
  let some C := (infos.filterMap (·.2.2.1))[0]? | return none
  unless infos.all (fun i => i.2.2.1.all (· == C)) do return none
  let inst := infos[0]!.2.1
  let bs : Array (Array (Array (Option Nat))) := infos.map fun i =>
    i.2.2.2.map fun br => br.map fun (isC, nm) => if isC then none else some (ms.idxOf nm)
  let W := 4 * (bs.foldl (fun a b => a + b.foldl (fun c br => c + br.size) 0) 0) + 4
  let tab := wgPGTable bs W
  let mut prof : Array (Nat × Nat × Array Nat) := #[]
  for j in [0 : bs.size] do
    let some (m, per, rs) := wgPhi tab[j]! | return none
    prof := prof.push (m, per, rs)
  let Bv : List (List (List (Option Nat))) := bs.toList.map fun b => b.toList.map (·.toList)
  let profV : List (Nat × Nat × List Nat) := prof.toList.map fun (m, per, rs) => (m, per, rs.toList)
  unless Sep.pChkA Bv profV do return none
  let some (rk, N, sps, cert) := wgPGCert bs prof W | return none
  let certV := cert.toList.map fun (sm, bg) =>
    (sm.toList.map (fun (n, bi, ls) => (n, bi, ls.toList)), bg.toList.map (fun (r, bi, n0, ls) => (r, bi, n0, ls.toList)))
  unless Sep.pChkC Bv profV rk.toList N sps.toList certV do return none
  let B := toExpr Bv
  let tru := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  try
    let absT ← wgPGAbsAll inst C B ms bs
    let concG ← wgPGConcAll inst C B ms bs
    return some { inst, C, ms, B, prof, profE := toExpr profV, hA := tru, rkE := toExpr rk.toList, NE := toExpr N,
                  spsE := toExpr sps.toList, certE := toExpr certV, hC := tru, absT, concG,
                  pbrs := infos.map (·.2.2.2) }
  catch _ => return none

def wgPGOf (p : Name) : MetaM (Option WgPGI) := do
  if let some (_, r) := (← wgPGCache.get).find? (·.1.contains p) then return r
  let r ← wgPGBuild p
  wgPGCache.modify (·.push (match r with
    | some I => I.ms
    | none => #[p], r))
  return r

def wgParseProf (p : Name) : MetaM (Option WgP) := do
  let some I ← wgPGOf p | return none
  let j := I.ms.idxOf p
  let inst := I.inst
  let c := I.C
  let (m, per, rs) := I.prof[j]!
  let brs := I.pbrs[j]!
  let phiLam ← withLocalDeclD `n arIntT fun n => do mkLambdaFVars #[n] (← wgPhiExpr m per rs n)
  let nat := mkConst ``Nat
  let one ← arIntLit 1
  let preLam ← withLocalDeclD `x nat fun x => withLocalDeclD `u nat fun u => do
    mkLambdaFVars #[x, u] (starOf inst (flatStar (c.beta #[x, u]) #[]).toList)
  let nextLam ← withLocalDeclD `x nat fun x => withLocalDeclD `u nat fun u => mkLambdaFVars #[x, u] u
  let cLam ← withLocalDeclD `s nat fun s => withLocalDeclD `s' nat fun s' =>
    withLocalDeclD `w arIntT fun w => withLocalDeclD `u nat fun u => do
      let eqs ← wgConj #[← mkAppM ``Eq #[s', u], ← mkAppM ``Eq #[w, one]]
      let body ← mkAppM ``HProp.hstar #[c.beta #[s, u], ← mkAppOptM ``HProp.hpure #[inst, eqs]]
      mkLambdaFVars #[s, s', w] (← arExists inst #[u] body)
  let relLam ← withLocalDeclD `s nat fun s => withLocalDeclD `s' nat fun s' =>
    withLocalDeclD `w arIntT fun w => do mkLambdaFVars #[s, s', w] (← mkAppM ``Eq #[w, one])
  let invLam ← withLocalDeclD `k nat fun k => withLocalDeclD `s nat fun s =>
    withLocalDeclD `t nat fun t => withLocalDeclD `n arIntT fun n => do
      mkLambdaFVars #[k, s, t, n] (← wgConj #[← mkAppM ``Eq #[n, ← arCast k],
        ← mkArrow (← mkAppM ``Eq #[k, mkNatLit 0]) (← mkAppM ``Eq #[s, t])])
  return some { pname := p, inst := inst, tys := #[nat, nat], mov := #[0], ai := none, sty := nat,
                cLam := cLam, preLam := preLam, nextLam := nextLam, usTys := #[nat],
                endSpec := #[(some 1, none)], kmin := m, stepIdx := (brs.findIdx? (·.any (!·.1))).getD 0,
                relLam := relLam, invLam := invLam, profLam := if per == 1 then none else some phiLam,
                pg := true, baseIdx := (brs.findIdx? (·.all (·.1))).getD 0 : WgP }

def wgCntW (n a : Expr) (xs us pures : Array Expr) : MetaM (Option (Expr × Bool × Option (Expr × Expr))) := do
  let mut r : Option (Expr × Bool × Option (Expr × Expr)) := none
  for c in pures do
    let some (_, l, rr) := c.eq? | continue
    let some (ts, k) := wgLinA (← arSub l rr) | continue
    let cn := (ts.find? (·.1 == n)).map (·.2) |>.getD 0
    let ca := (ts.find? (·.1 == a)).map (·.2) |>.getD 0
    unless (cn == 1 || cn == -1) && ca == -cn do continue
    let rest := ts.filter (fun (t, _) => t != n && t != a)
    if rest.any (fun (t, _) => xs.contains t) then continue
    let w ← wgLinExpr (rest.map (fun (t, v) => (t, -v * cn))) (-k * cn)
    let defn := if l.isFVar && us.contains l && !rr.isFVar then some (rr, l)
      else if rr.isFVar && us.contains rr && !l.isFVar then some (l, rr) else none
    r := some (w, rest.isEmpty && -k * cn == 1, defn)
  return r

def wgCommon {β : Type} [BEq β] (xs : Array (Array β)) : Array β :=
  match xs[0]? with
  | some a => a.filter fun r => xs.all (·.contains r)
  | none => #[]

def wgCarrier (rd : WgRd) : MetaM (Option WgP) := do
  let p := rd.p
  let xs := rd.xs
  let inst := rd.inst
  let tys := rd.tys
  let brs := rd.brs
  let isCall := fun (e : Expr) => e.getAppFn.constName? == some p
  let pconj := fun (items : Array Expr) => items.foldl (fun acc it => match it.getAppFnArgs with
    | (``HProp.hpure, #[_, pr]) => pureConjs pr acc
    | _ => acc) #[]
  let steps := (Array.range brs.size).filter fun b => (brs[b]!.raw.find? (·.isConstOf p)).isSome
  let bases := (Array.range brs.size).filter (!steps.contains ·)
  unless steps.size ≥ 1 && bases.size == 1 do return none
  let si := steps[0]!
  let bus := brs[bases[0]!]!.us
  let bItems := brs[bases[0]!]!.items
  let bp := brs[bases[0]!]!.pures
  let SU := steps.map (brs[·]!.us)
  let SI := steps.map (brs[·]!.items)
  let ns := steps.size
  let mut RA : Array (Array Expr) := #[]
  for items in SI do
    let recs := items.filter isCall
    unless recs.size == 1 do return none
    unless recs[0]!.getAppNumArgs == xs.size do return none
    RA := RA.push recs[0]!.getAppArgs
  let mut cnt : Option (Nat × Array (Nat × Expr × Bool × Option (Expr × Expr))) := none
  for i in [0 : xs.size] do
    unless ← isDefEq tys[i]! arIntT do continue
    let onlyI := fun (c : Expr) => (c.find? (· == xs[i]!)).isSome &&
      (c.find? (fun e => e.isFVar && e != xs[i]!)).isNone
    unless bp.any onlyI do continue
    let mut ws : Array (Nat × Expr × Bool × Option (Expr × Expr)) := #[]
    for t in [0 : ns] do
      let some ka := SU[t]!.findIdx? (· == RA[t]![i]!) | break
      let some (w, u, defn) ← wgCntW xs[i]! SU[t]![ka]! xs SU[t]! brs[steps[t]!]!.pures | break
      ws := ws.push (ka, w, u, defn)
    if ws.size == ns then cnt := some (i, ws)
  let ci := cnt.map (·.1)
  let mov0s := RA.map fun ra => (Array.range xs.size).filter (fun i => ci != some i && ra[i]! != xs[i]!)
  let mov0 := mov0s[0]!
  unless mov0s.all (· == mov0) do return none
  if mov0.isEmpty then return none
  for i in mov0 do
    unless (← isDefEq tys[i]! (mkConst ``Nat)) || (← isDefEq tys[i]! arIntT) do return none
  let fixAll := (Array.range xs.size).filter (fun i => ci != some i && !mov0.contains i)
  let cv := fun (t : Nat) => match cnt with
    | some (i, ws) => #[xs[i]!, SU[t]![ws[t]!.1]!]
    | none => #[]
  let ment := fun (e : Expr) (vs : Array Expr) => vs.any (fun v => (e.find? (· == v)).isSome)
  let mut promo : Array Nat := #[]
  for i in fixAll do
    unless ← isDefEq tys[i]! (mkConst ``Nat) do continue
    let v := xs[i]!
    let hit := (Array.range ns).any fun t => SI[t]!.any fun it =>
      if isCall it then false
      else if let (``HProp.hpure, #[_, pr]) := it.getAppFnArgs then
        (pureConjs pr #[]).any (fun c => (c.find? (· == v)).isSome && !ment c (cv t))
      else (it.find? (· == v)).isSome
    if hit then promo := promo.push i
  let mov := mov0 ++ promo
  let fixd := fixAll.filter (!promo.contains ·)
  let fvs := fixd.map (xs[·]!)
  let movX := mov.map (xs[·]!)
  let nm := mov.size
  let sty ← wgTupleTy (mov.map (tys[·]!))
  let one ← arIntLit 1
  let mut PR : Array (Array Expr) := #[]
  let mut UX : Array (Array Expr) := #[]
  let mut WE : Array Expr := #[]
  for t in [0 : ns] do
    let defn := match cnt with
      | some (_, ws) => ws[t]!.2.2.2
      | none => none
    let mut pre : Array Expr := #[]
    for it in SI[t]! do
      if isCall it then continue
      if let (``HProp.hpure, #[_, pr]) := it.getAppFnArgs then
        let cs := (pureConjs pr #[]).map fun c => match defn with
          | some (e, v) => c.replace (fun s => if s == e then some v else none)
          | none => c
        for c in cs do
          if ment c fvs && !ment c (cv t) then
            for v in (xs ++ SU[t]!).filter (fun v => (c.find? (· == v)).isSome) do
              unless ← isDefEq (← inferType v) arIntT do return none
        let keep := cs.filter fun c => !ment c (cv t) && !ment c fvs &&
          !(match c.eq? with
            | some (_, l, r) => l == r
            | none => false)
        unless keep.isEmpty do pre := pre.push (← mkAppOptM ``HProp.hpure #[inst, ← wgConj keep])
      else
        if ment it (cv t) || ment it fvs then return none
        pre := pre.push it
    PR := PR.push pre
    match cnt with
    | some (_, ws) =>
      UX := UX.push (SU[t]!.eraseIdx! ws[t]!.1)
      WE := WE.push ws[t]!.2.1
    | none =>
      UX := UX.push SU[t]!
      WE := WE.push one
  let unit := match cnt with
    | some (_, ws) => ws.all (·.2.2.1)
    | none => true
  let mut views : Array (Expr × Expr × Array Expr × Expr × Nat) := #[]
  for t in [0 : ns] do
    let preLam ← mkLambdaFVars (movX ++ UX[t]!) (starOf inst PR[t]!.toList)
    let nextLam ← mkLambdaFVars (movX ++ UX[t]!) (← wgTuple (mov.map (RA[t]![·]!)))
    let wLam ← mkLambdaFVars (movX ++ UX[t]!) WE[t]!
    views := views.push (preLam, nextLam, ← UX[t]!.mapM inferType, wLam, steps[t]!)
  let usX := UX[0]!
  let (preLam, nextLam, usTys, _, _) := views[0]!
  let cLam ← withLocalDeclD `s sty fun s => withLocalDeclD `s' sty fun s' =>
    withLocalDeclD `w arIntT fun w => do
      let comps ← (Array.range nm).mapM (wgProj s · nm)
      let comps' ← (Array.range nm).mapM (wgProj s' · nm)
      let sub := fun (e : Expr) => e.replaceFVars movX comps
      let mut ds : Array Expr := #[]
      for t in [0 : ns] do
        let mut eqs : Array Expr := #[]
        for j in [0 : nm] do eqs := eqs.push (← mkAppM ``Eq #[comps'[j]!, sub RA[t]![mov[j]!]!])
        eqs := eqs.push (← mkAppM ``Eq #[w, sub WE[t]!])
        let body := starOf inst ((PR[t]!.map sub).toList ++ [← mkAppOptM ``HProp.hpure #[inst, ← wgConj eqs]])
        ds := ds.push (← arExists inst UX[t]! body)
      let mut acc := ds[ds.size - 1]!
      for i in [0 : ds.size - 1] do acc ← mkAppM ``hdisj #[ds[ds.size - 2 - i]!, acc]
      mkLambdaFVars #[s, s', w] acc
  let guardSides := fun (c : Expr) => (match c.getAppFnArgs with
    | (``Ne, #[_, a, b]) => some (a, b)
    | (``Not, #[q]) => (q.eq?.map fun (_, a, b) => (a, b))
    | _ => none : Option (Expr × Expr))
  let mut GL : Array (Array (Nat × Nat)) := #[]
  let mut RL : Array (Array (Nat × Int × Int × Bool)) := #[]
  let mut AL : Array (Array (Nat × Nat)) := #[]
  let mut GP : Array (Array (Nat × Nat × Nat)) := #[]
  for t in [0 : ns] do
    let pre := PR[t]!
    let ux := UX[t]!
    let ra := RA[t]!
    let preConjs := pconj pre
    let addrs := pre.filterMap fun it =>
      if it.isAppOf ``HProp.hsingle then some it.getAppArgs[it.getAppNumArgs - 2]! else none
    let mut gloc : Array (Nat × Nat) := #[]
    for i in promo do
      let some pj := mov.idxOf? i | continue
      for c in preConjs do
        let some (a, b) := guardSides c | continue
        let o := if a == xs[i]! then some b else if b == xs[i]! then some a else none
        let some o := o | continue
        let some m := mov0.find? (xs[·]! == o) | continue
        unless addrs.contains o do continue
        let some pm := mov.idxOf? m | continue
        unless gloc.any (·.1 == pj) do gloc := gloc.push (pj, pm)
    GL := GL.push gloc
    let mut rels : Array (Nat × Int × Int × Bool) := #[]
    for j in [0 : nm] do
      unless ← isDefEq tys[mov[j]!]! arIntT do continue
      let some ka := ux.findIdx? (· == ra[mov[j]!]!) | continue
      let a := ux[ka]!
      let n := movX[j]!
      for c in preConjs do
        if (c.find? (fun e => e.isFVar && e != n && e != a)).isSome then continue
        if let some (sg, b, isEq) := wgRel? n a c then rels := rels.push (j, sg, b, isEq)
    RL := RL.push rels
    let mut acarP : Array (Nat × Nat) := #[]
    let mut gprev : Array (Nat × Nat × Nat) := #[]
    for j in [0 : nm] do
      unless ← isDefEq tys[mov[j]!]! (mkConst ``Nat) do continue
      let some a := movX.idxOf? ra[mov[j]!]! | continue
      if a == j || !addrs.contains movX[a]! then continue
      let nz := preConjs.any fun c => match guardSides c with
        | some (u, v) => (u == movX[a]! && v.nat? == some 0) || (v == movX[a]! && u.nat? == some 0)
        | none => false
      let guarded := preConjs.any fun c => match guardSides c with
        | some (u, v) => (u == movX[j]! && v.nat? != some 0) || (v == movX[j]! && u.nat? != some 0)
        | none => false
      if nz && guarded then
        acarP := acarP.push (j, a)
        for i in [0 : promo.size] do
          let c := i + mov0.size
          let hit := preConjs.any fun q => match guardSides q with
            | some (u, v) => (u == movX[c]! && v == movX[j]!) || (v == movX[c]! && u == movX[j]!)
            | none => false
          if hit then gprev := gprev.push (c, j, a)
    AL := AL.push acarP
    GP := GP.push gprev
  let gloc := wgCommon GL
  let rels := wgCommon RL
  let acarP := wgCommon AL
  let gprev := wgCommon GP
  let acar := acarP.map (·.1)
  let relE := fun (x y : Expr) (sg : Int) (isEq : Bool) (bk : Expr) => do
    let d ← if sg == 1 then arSub x y else arSub y x
    if isEq then mkAppM ``Eq #[d, bk] else arLe d bk
  let relLam ← withLocalDeclD `s sty fun s => withLocalDeclD `s' sty fun s' =>
    withLocalDeclD `w arIntT fun w => do
      let mut cs := #[← if unit then mkAppM ``Eq #[w, one] else arLe (← arIntLit 0) w]
      for (j, sg, b, isEq) in rels do
        cs := cs.push (← relE (← wgProj s j nm) (← wgProj s' j nm) sg isEq (← arIntLit b))
      for j in acar do
        cs := cs.push (← mkAppM ``Ne #[← wgProj s' j nm, mkNatLit 0])
      mkLambdaFVars #[s, s', w] (← wgConj cs)
  let invLam ← withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `s sty fun s =>
    withLocalDeclD `t sty fun t => withLocalDeclD `n arIntT fun n => do
      let ck ← arCast k
      let mut cs := #[← if unit then mkAppM ``Eq #[n, ck] else arLe (← arIntLit 0) n]
      let mut seen : Array Nat := #[]
      for (j, sg, b, isEq) in rels do
        let x ← wgProj s j nm
        let y ← wgProj t j nm
        let bk ← if b == 0 then arIntLit 0 else mkAppM ``HMul.hMul #[← arIntLit b, ck]
        cs := cs.push (← relE x y sg isEq bk)
        unless seen.contains j do
          seen := seen.push j
          cs := cs.push (← mkArrow (← mkAppM ``Eq #[k, mkNatLit 0]) (← mkAppM ``Eq #[x, y]))
      for j in acar do
        let x ← wgProj s j nm
        let y ← wgProj t j nm
        unless seen.contains j do
          cs := cs.push (← mkArrow (← mkAppM ``Eq #[k, mkNatLit 0]) (← mkAppM ``Eq #[x, y]))
        cs := cs.push (← mkAppM ``Or #[← mkAppM ``Eq #[k, mkNatLit 0], ← mkAppM ``Ne #[y, mkNatLit 0]])
      mkLambdaFVars #[k, s, t, n] (← wgConj cs)
  let eqPairs := bp.filterMap (fun c => match c.getAppFnArgs with
    | (``Eq, #[_, a, b]) => some (a, b)
    | _ => none)
  let partner := fun (e : Expr) => Id.run do
    if let some j := promo.find? (xs[·]! == e) then return some j
    for (a, b) in eqPairs do
      if a == e then if let some j := fixAll.find? (xs[·]! == b) then return some j
      if b == e then if let some j := fixAll.find? (xs[·]! == a) then return some j
    return none
  let lit := fun (e : Expr) => eqPairs.find? (fun (a, b) => (a == e && !b.hasFVar) || (b == e && !a.hasFVar))
    |>.map (fun (a, b) => if a == e then b else a)
  let hsB := bItems.filter (·.isAppOf ``HProp.hsingle)
  let absorbed ← (do
    if !bus.isEmpty && hsB.isEmpty then return none
    if hsB.isEmpty then
      let mut spec : Array (Option Nat × Option Expr) := #[]
      for j in mov do
        match partner xs[j]! with
        | some f => spec := spec.push (some f, none)
        | none => spec := spec.push (none, lit xs[j]!)
      return some (spec, 0, (#[] : Array Expr), (#[] : Array (Expr × Nat)))
    let canon := fun (e : Expr) => Id.run do
      let mut r := e
      for (a, b) in eqPairs do
        if let some _ := fixd.find? (xs[·]! == a) then
          if mov0.any (xs[·]! == b) then r := r.replaceFVar a b
        if let some _ := fixd.find? (xs[·]! == b) then
          if mov0.any (xs[·]! == a) then r := r.replaceFVar b a
      return r
    let mut left := (bItems.filter (!·.isAppOf ``HProp.hpure)).map canon
    let mut cur := movX
    let mut ncell := 0
    for _ in [0 : left.size] do
      let ms ← usX.mapM (fun u => do mkFreshExprMVar (some (← inferType u)))
      let pat := (flatStar (preLam.beta (cur ++ ms)) #[]).filter (!·.isAppOf ``HProp.hpure)
      if pat.isEmpty then break
      let s ← saveState
      let mut used : Array Nat := #[]
      let mut ok := true
      for pa in pat do
        let mut hit := false
        for k in [0 : left.size] do
          if used.contains k || left[k]!.getAppFn != pa.getAppFn then continue
          let s2 ← saveState
          if ← isDefEq pa left[k]! then
            used := used.push k
            hit := true
            break
          s2.restore
        unless hit do
          ok := false
          break
      unless ok do
        s.restore
        break
      let nx ← instantiateMVars (nextLam.beta (cur ++ ms))
      let nxs ← (Array.range nm).mapM fun j => do instantiateMVars (← wgNorm (← wgProj nx j nm))
      if nxs.any (·.hasExprMVar) && ncell > 0 then
        s.restore
        break
      left := (Array.range left.size).filter (!used.contains ·) |>.map (left[·]!)
      cur := nxs
      ncell := ncell + 1
    if ncell == 0 then return none
    let nxs := cur
    let mut spec : Array (Option Nat × Option Expr) := #[]
    let mut sub : Array (Expr × Nat) := #[]
    for j in [0 : nxs.size] do
      let e := nxs[j]!
      if e.hasExprMVar then spec := spec.push (none, none)
      else if let some f := fixAll.find? (xs[·]! == e) then spec := spec.push (some f, none)
      else if let some f := partner e then spec := spec.push (some f, none)
      else if !e.hasFVar then spec := spec.push (none, some e)
      else
        spec := spec.push (none, none)
        if e.isFVar then sub := sub.push (e, j)
    let mut tl := left
    for c in bp do
      let fs := (Lean.collectFVars {} c).fvarIds
      if fs.all (fun f => tl.any (fun it => (it.find? (· == mkFVar f)).isSome) &&
          !sub.any (·.1 == mkFVar f)) && !fs.isEmpty then
        tl := tl.push (← mkAppOptM ``HProp.hpure #[inst, c])
    return some (spec, ncell, tl, sub))
  let covered := fun (spec : Array (Option Nat × Option Expr)) =>
    fixd.all (fun f => spec.any (·.1 == some f))
  let mk := fun (spec : Array (Option Nat × Option Expr)) (kmin : Nat) (tail : Option Expr) =>
    some { pname := p, inst := inst, tys := tys, mov := mov, ai := ci, sty := sty,
           cLam := cLam, preLam := preLam, nextLam := nextLam, usTys := usTys, endSpec := spec,
           kmin := kmin, stepIdx := si, tailLam := tail, relLam := relLam, invLam := invLam,
           cst := (Array.range promo.size).map (· + mov0.size), gloc := gloc,
           rels := rels, gprev := gprev, prevAdr := acarP, unitW := unit,
           cellData := if ns > 1 then views else #[], baseIdx := bases[0]! : WgP }
  if let some (spec, kmin, tl, sub) := absorbed then
    if covered spec then
      if tl.isEmpty then return mk spec kmin none
      let missTys := (Array.range nm).filterMap (fun j =>
        if spec[j]!.1.isNone && spec[j]!.2.isNone then some tys[mov[j]!]! else none)
      let tailLam? ← withLocalDeclsD (wgDecls missTys "tm") fun miss => do
        let mut en : Array Expr := #[]
        let mut mi := 0
        for (pf, pc) in spec do
          match pf, pc with
          | some f, _ => en := en.push xs[f]!
          | none, some c => en := en.push c
          | none, none =>
            en := en.push miss[mi]!
            mi := mi + 1
        let body := (starOf inst tl.toList).replaceFVars (sub.map (·.1)) (sub.map (en[·.2]!))
        let bad := (bus ++ UX.flatten ++ movX).any (fun v => (body.find? (· == v)).isSome)
        if bad || body.hasExprMVar then return none
        return some (← mkLambdaFVars (xs ++ miss) body)
      if let some t := tailLam? then return mk spec kmin (some t)
      return none
  unless cnt.isNone && bus.isEmpty do return none
  let mut spec : Array (Option Nat × Option Expr) := #[]
  let mut used : Array Expr := #[]
  let fvsA := fixAll.map (xs[·]!)
  for j in mov do
    let e := xs[j]!
    if promo.contains j then
      spec := spec.push (some j, none)
      continue
    let hit := bp.find? (fun c => match c.getAppFnArgs with
      | (``Eq, #[_, a, b]) => (a == e && (fvsA.contains b || !b.hasFVar)) || (b == e && (fvsA.contains a || !a.hasFVar))
      | _ => false)
    match hit with
    | some c =>
      used := used.push c
      let o := if c.getAppArgs[1]! == e then c.getAppArgs[2]! else c.getAppArgs[1]!
      match fixAll.find? (xs[·]! == o) with
      | some f => spec := spec.push (some f, none)
      | none => spec := spec.push (none, some o)
    | none => spec := spec.push (none, none)
  let missTys := (Array.range nm).filterMap (fun j =>
    if spec[j]!.1.isNone && spec[j]!.2.isNone then some tys[mov[j]!]! else none)
  let tailLam ← withLocalDeclsD (wgDecls missTys "tm") fun miss => do
    let mut en : Array Expr := #[]
    let mut mi := 0
    for (pf, pc) in spec do
      match pf, pc with
      | some f, _ => en := en.push xs[f]!
      | none, some c => en := en.push c
      | none, none =>
        en := en.push miss[mi]!
        mi := mi + 1
    let mut tl : Array Expr := #[]
    for it in bItems do
      if let (``HProp.hpure, #[_, pr]) := it.getAppFnArgs then
        let keep := (pureConjs pr #[]).filter (!used.contains ·)
        unless keep.isEmpty do tl := tl.push (← mkAppOptM ``HProp.hpure #[inst, ← wgConj keep])
      else tl := tl.push it
    mkLambdaFVars (xs ++ miss) ((starOf inst tl.toList).replaceFVars movX en)
  return mk spec 0 (some tailLam)

def wgParseVia (rd : WgRd) : MetaM (Option WgP) := do
  let p := rd.p
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let info ← (do
    let xs := rd.xs
    unless xs.size == 1 || xs.size == 2 do return none
    unless ← isDefEq (← inferType xs[0]!) (mkConst ``Nat) do return none
    if xs.size == 2 then
      unless ← isDefEq (← inferType xs[1]!) arIntT do return none
    let brs := rd.brs
    let hasRec := fun (b : WgRB) => (b.raw.find? (·.isConstOf p)).isSome
    let bases := (Array.range brs.size).filter (!hasRec brs[·]!)
    unless bases.size == 1 && brs.size ≥ 2 do return none
    let bItems := brs[bases[0]!]!.items
    unless bItems.all (·.isAppOf ``HProp.hpure) do return none
    let bp := bItems.foldl (fun acc it => pureConjs it.appArg! acc) #[]
    let c := bp.findSome? (fun c => match c.getAppFnArgs with
      | (``Eq, #[_, a, b]) => if a == xs[0]! && !b.hasFVar then some b
          else if b == xs[0]! && !a.hasFVar then some a else none
      | _ => none)
    if c.isNone && bp.any (fun q => (q.find? (· == xs[0]!)).isSome) then return none
    return some (c, xs.size, bases[0]!) : MetaM (Option (Option Expr × Nat × Nat)))
  let some (cst, na, bi) := info | return none
  for e in entries do
    let q := e.headFn
    if q == p then continue
    let some P ← wgRead q wgCarrier | continue
    unless P.mov.size == 1 do continue
    unless P.cellData.any (fun cd => (cd.1.find? (·.isConstOf p)).isSome) do continue
    unless (na == 2) == P.ai.isSome do continue
    let tys := if na == 2 then #[mkConst ``Nat, arIntT] else #[mkConst ``Nat]
    return some { P with pname := p, tys := tys, mov := #[0], ai := if na == 2 then some 1 else none,
                         endSpec := #[(none, cst)], kmin := 0, via := true, baseIdx := bi }
  return none

def wgPOf (p : Name) : MetaM (Option WgP) := do
  match (← wgPCache.get).findSome? (fun e => if e.1 == p then some e.2 else none) with
  | some r => return r
  | none =>
    let r ← try (do
        match ← wgParseProf p with
        | some P => pure (some P)
        | none => wgRead p fun rd => do
          match ← wgCarrier rd with
          | some P => pure (some P)
          | none => wgParseVia rd) catch _ => pure none
    wgPCache.modify (·.push (p, r))
    return r

def wgValid (e : Expr) : MetaM Bool := do
  let env ← getEnv
  let used ← match (← wgUsedCache.get).find? (·.1 == e) with
    | some (_, u) => pure u
    | none =>
      let u := e.getUsedConstants
      wgUsedCache.modify (·.push (e, u))
      pure u
  return used.all env.contains

def wgLem (key : String) (build : TacticM Expr) : TacticM (Option Expr) := do
  if let some r := (← wgLCache.get).findSome? (fun e => if e.1 == key then some e.2 else none) then
    match r with
    | none => return none
    | some e =>
      if ← wgValid e then return r
      wgLCache.modify (·.filter (·.1 != key))
  let saved ← getGoals
  let st ← saveState
  let old ← lemBuilding.get
  lemBuilding.set true
  let r ← try withLCtx {} {} (some <$> build) catch _ => do st.restore; pure none
  lemBuilding.set old
  setGoals saved
  wgLCache.modify (·.push (key, r))
  return r

def wgSeg (P : WgP) (k n s t : Expr) : Expr :=
  mkAppN (mkConst ``Sep.wseg) #[P.inst, P.sty, P.cLam, k, n, s, t]

def wgIsSeg (e : Expr) : Bool := e.isAppOfArity ``Sep.wseg 7

def wgMovTys (P : WgP) : Array Expr := P.mov.map (P.tys[·]!)

def wgMissTys (P : WgP) : Array Expr := Id.run do
  let mut r : Array Expr := #[]
  for j in [0 : P.endSpec.size] do
    if P.endSpec[j]!.1.isNone && P.endSpec[j]!.2.isNone then r := r.push P.tys[P.mov[j]!]!
  return r

def wgEnC (P : WgP) (xs miss : Array Expr) : Array Expr := Id.run do
  let mut cs : Array Expr := #[]
  let mut mi := 0
  for (pf, pc) in P.endSpec do
    match pf, pc with
    | some f, _ => cs := cs.push xs[f]!
    | none, some c => cs := cs.push c
    | none, none =>
      cs := cs.push miss[mi]!
      mi := mi + 1
  return cs

def wgCond (P : WgP) (k : Expr) : MetaM Expr := do
  match P.profLam with
  | some f => pure (f.beta #[← arCast k])
  | none => mkAppM ``LE.le #[mkNatLit P.kmin, k]

def wgAbsTarget (P : WgP) (xs : Array Expr) : MetaM Expr :=
  withLocalDeclD `k (mkConst ``Nat) fun k =>
  withLocalDeclD `n arIntT fun n =>
  withLocalDeclsD (wgDecls (wgMissTys P) "wm") fun miss => do
    let st ← wgTuple (P.mov.map (xs[·]!))
    let en ← wgTuple (wgEnC P xs miss)
    let hk ← mkAppOptM ``HProp.hpure #[P.inst, ← wgCond P k]
    let (nE, vs) := match P.ai with
      | some i => (xs[i]!, #[k] ++ miss)
      | none => (n, #[k, n] ++ miss)
    let tl := match P.tailLam with
      | some t => [t.beta (xs ++ miss)]
      | none => []
    arExists P.inst vs (starOf P.inst ([wgSeg P k nE st en] ++ tl ++ [hk]))

def wgLhs : TacticM (Array Expr) := withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (lhs, _) := entailHead? t | throwError "wg: goal"
  return flatStar lhs #[]

def wgRhs : TacticM (Array Expr) := withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (_, rhs) := entailHead? t | throwError "wg: goal"
  return flatStar rhs #[]

partial def wgSubstNew (news : Array FVarId) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let some (_, a, b) := (← instantiateMVars d.type).eq? | continue
    let pick : Option Bool :=
      if a.isFVar && news.contains a.fvarId! && !(b.containsFVar a.fvarId!) then some false
      else if b.isFVar && news.contains b.fvarId! && !(a.containsFVar b.fvarId!) then some true
      else none
    let some symm := pick | continue
    let r ← try some <$> substCore g d.fvarId symm catch _ => pure none
    let some (_, g') := r | continue
    replaceMainGoal [g']
    return ← wgSubstNew news
  return

def wgSubstAll : TacticM Unit := withMainContext do
  replaceMainGoal [← fastSubstVars (← getMainGoal)]

partial def wgDestruct (v : Expr) : TacticM (Array Expr) := do
  let g ← getMainGoal
  let ty ← g.withContext do whnf (← inferType v)
  unless ty.isAppOf ``Prod do return #[v]
  let subs ← g.cases v.fvarId!
  let some sg := subs[0]? | throwError "wg: cases"
  replaceMainGoal [sg.mvarId]
  let fs := sg.fields
  let rest ← wgDestruct fs[1]!
  return #[fs[0]!] ++ rest

partial def puresProp (inst e : Expr) : MetaM (Option (Expr × Expr)) := do
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) =>
    let some (pa, ha) ← puresProp inst a | return none
    let some (pb, hb) ← puresProp inst b | return none
    return some (← mkAppM ``And #[pa, pb], mkAppN (mkConst ``pures_conj) #[inst, a, b, pa, pb, ha, hb])
  | (``HProp.hpure, #[_, p]) => return some (p, mkApp2 (mkConst ``HProp.himpl_refl) inst e)
  | (``HProp.hempty, _) => return some (mkConst ``True, mkApp (mkConst ``emp_pure_true) inst)
  | _ => return none

partial def puresBuild (inst : Expr) (e : Expr) : TacticM Expr := do
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) =>
    let pa ← puresBuild inst a
    let pb ← puresBuild inst b
    return mkAppN (mkConst ``emp_star_intro) #[inst, a, b, pa, pb]
  | (``HProp.hpure, #[_, q]) =>
    return mkApp3 (mkConst ``HProp.himpl_hempty_hpure) inst q (← wgSide q)
  | (``HProp.hempty, _) => return mkApp2 (mkConst ``HProp.himpl_refl) inst e
  | _ => throwError "pure: atom"

def pureEntDirect : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (lhs, rhs) := entailHead? t | return false
  if t.hasExprMVar then return false
  let inst := t.getAppArgs[0]!
  let some (P, hL) ← puresProp inst lhs | return false
  let s ← saveState
  try
    let body ← withLocalDeclD `hpe P fun hp => do
      mkLambdaFVars #[hp] (← puresBuild inst rhs)
    g.assign (mkAppN (mkConst ``HProp.himpl_trans) #[inst, lhs, mkApp2 (mkConst ``HProp.hpure) inst P, rhs, hL,
      mkAppN (mkConst ``pure_l_emp) #[inst, P, rhs, body]])
    replaceMainGoal []
    return true
  catch _ =>
    s.restore
    return false

def convEqs (rhs : Expr) (addrOnly : Bool := false) : MetaM Unit := do
  let rhs ← instantiateMVars rhs
  let adr := (flatStar rhs #[]).filterMap fun r =>
    if r.isAppOfArity ``HProp.hsingle 3 then some r.getAppArgs[1]! else none
  let ok := fun (m : Expr) => !addrOnly || adr.any (fun a => (a.find? (· == m)).isSome)
  for c in pureProps rhs #[] do
    for cc in pureConjs c #[] do
      if let some (_, a, b) := cc.eq? then
        let mut work := #[(a, b)]
        while !work.isEmpty do
          let (a, b) := work.back!
          work := work.pop
          let a ← instantiateMVars a
          let b ← instantiateMVars b
          if a.isAppOfArity ``Prod.mk 4 && b.isAppOfArity ``Prod.mk 4 then
            work := work.push (a.getAppArgs[2]!, b.getAppArgs[2]!) |>.push (a.getAppArgs[3]!, b.getAppArgs[3]!)
          else if a.isMVar && !b.hasExprMVar && ok a then let _ ← isDefEq a b
          else if b.isMVar && !a.hasExprMVar && ok b then let _ ← isDefEq b a

partial def wgSplitMVar (ty : Expr) : MetaM Expr := do
  let ty ← whnfR ty
  if ty.isAppOfArity ``Prod 2 then
    mkAppM ``Prod.mk #[← wgSplitMVar ty.appFn!.appArg!, ← wgSplitMVar ty.appArg!]
  else mkFreshExprMVar ty

def convClose : TacticM Unit := do
  let _ ← arIntroLhs
  wgSubstAll
  if ← wgUnfoldHelpers then wgSubstAll
  let nested ← withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (_, r) := entailHead? t | return false
    let (body, _) ← arOpen r
    return (body.find? (·.isAppOf ``HProp.hexists)).isSome
  let ws0 ← if nested then arOpenDeep else pure #[]
  if ← wgUnfoldHelpers then
    let _ ← arOpenDeep
  let ws ← arOpenGoal
  withMainContext do
    let mut split := false
    for w in ws0 ++ ws do
      if (← whnfR (← inferType w)).isAppOfArity ``Prod 2 then
        w.mvarId!.assign (← wgSplitMVar (← inferType w))
        split := true
    if split then
      let g ← getMainGoal
      replaceMainGoal [← g.replaceTargetDefEq (← wgNorm (← instantiateMVars (← g.getType)))]
  withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (lhs, rhs) := entailHead? t | throwError "dat: not an entailment"
    let L := (flatStar lhs #[]).filter (!·.isAppOf ``HProp.hpure)
    convEqs rhs true
    convEqs rhs true
    let R ← (flatStar rhs #[]).filterMapM fun r => do
      let r ← instantiateMVars r
      pure (if !r.isAppOf ``HProp.hpure && r.hasExprMVar then some r else none)
    unless ← (arAssign L R.toList #[]) do throwError "dat: match"
    convEqs rhs
    convEqs rhs
  for w in ws do
    if (← instantiateMVars w).hasExprMVar then throwError "dat: witness open"
  let s ← saveState
  if ← (try finishDirect catch _ => pure false) then return
  s.restore
  unless ← pureEntDirect do throwError "dat: no direct closure"
  for w in ws0 do
    if (← instantiateMVars w).hasExprMVar then throwError "conv: witness open"

partial def wgTupEq (cs ds : Array Expr) : TacticM Expr := withMainContext do
  let eqc := fun (a b : Expr) => do
    if (← instantiateMVars a) == (← instantiateMVars b) then mkEqRefl a
    else wgSide (← mkAppM ``Eq #[a, b])
  if cs.size == 1 then return ← eqc cs[0]! ds[0]!
  let h0 ← eqc cs[0]! ds[0]!
  let hr ← wgTupEq (cs.extract 1 cs.size) (ds.extract 1 ds.size)
  let f ← mkAppOptM ``Prod.mk #[← inferType cs[0]!, ← inferType (← wgTuple (cs.extract 1 cs.size))]
  mkCongr (← mkCongrArg f h0) hr

def wgCongPf (l : Expr) (k n s t : Expr) (nc : Nat) : TacticM Expr := withMainContext do
  let la := l.getAppArgs
  let k ← instantiateMVars k
  let n ← instantiateMVars n
  let s ← instantiateMVars s
  let t ← instantiateMVars t
  let tgt := mkAppN l.getAppFn #[la[0]!, la[1]!, la[2]!, k, n, s, t]
  let hk ← if la[3]! == k then mkEqRefl k else wgSide (← mkAppM ``Eq #[la[3]!, k])
  let hn ← if la[4]! == n then mkEqRefl n else wgSide (← mkAppM ``Eq #[la[4]!, n])
  let hs ← wgTupEq (← wgComps la[5]! nc) (← wgComps s nc)
  let ht ← wgTupEq (← wgComps la[6]! nc) (← wgComps t nc)
  let pf ← mkAppOptM ``Sep.wseg_cong #[la[0]!, la[1]!, la[2]!, none, none, none, none, none, none,
    none, none, hk, hn, hs, ht]
  mkExpectedTypeHint pf (← mkAppM ``HProp.himpl #[l, tgt])

def wgCongTo (l : Expr) (k n s t : Expr) (nc : Nat) : TacticM Expr := do
  let la := l.getAppArgs
  let k ← instantiateMVars k
  let n ← instantiateMVars n
  let s ← instantiateMVars s
  let t ← instantiateMVars t
  if la[3]! == k && la[4]! == n && la[5]! == s && la[6]! == t then return l
  let tgt := mkAppN l.getAppFn #[la[0]!, la[1]!, la[2]!, k, n, s, t]
  let lem ← withMainContext do
    let hk ← if la[3]! == k then mkEqRefl k else wgSide (← mkAppM ``Eq #[la[3]!, k])
    let hn ← if la[4]! == n then mkEqRefl n else wgSide (← mkAppM ``Eq #[la[4]!, n])
    let hs ← wgTupEq (← wgComps la[5]! nc) (← wgComps s nc)
    let ht ← wgTupEq (← wgComps la[6]! nc) (← wgComps t nc)
    let pf ← mkAppOptM ``Sep.wseg_cong #[la[0]!, la[1]!, la[2]!, none, none, none, none, none, none,
      none, none, hk, hn, hs, ht]
    mkExpectedTypeHint pf (← mkAppM ``HProp.himpl #[l, tgt])
  let _ ← arRwLhs [l] lem
  return tgt

def wgEqOk (a b : Expr) : TacticM Bool := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  if b.isMVar then return ← isDefEq b a
  if a == b then return true
  if b.hasExprMVar then return ← (try checkpointDefEq (isDefEq b a) catch _ => pure false)
  try (do let _ ← wgSide (← mkAppM ``Eq #[a, b]); pure true) catch _ => pure false

def wgUnify (l r : Expr) (nc : Nat) (cst : Array Nat := #[]) : TacticM Bool := withMainContext do
  let la := l.getAppArgs
  let ra := r.getAppArgs
  unless la[2]! == ra[2]! do return false
  let s ← saveState
  let ok ← (do
    let ls ← wgComps la[5]! nc
    let rs ← wgComps ra[5]! nc
    let le ← wgComps la[6]! nc
    let re ← wgComps ra[6]! nc
    for i in [0 : 2 * nc] do
      if cst.contains (i % nc) then continue
      unless ← wgEqOk (ls ++ le)[i]! (rs ++ re)[i]! do return false
    unless ← wgEqOk la[3]! ra[3]! do return false
    unless ← wgEqOk la[4]! ra[4]! do return false
    return true)
  unless ok do s.restore
  return ok

def wgTail (P : WgP) (xs miss : Array Expr) : Array Expr :=
  match P.tailLam with
  | some t => flatStar (t.beta (xs ++ miss)) #[]
  | none => #[]

def wgInvFact (P : WgP) (Inv x : Expr) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (lhs, rhs) := entailHead? t | return
  let inst := t.getAppArgs[0]!
  let xa := x.getAppArgs
  let q ← wgNorm (P.invLam.beta #[xa[3]!, xa[5]!, xa[6]!, xa[4]!])
  let known ← (← getLCtx).anyM fun dcl => do
    if dcl.isImplementationDetail then return false
    return (← instantiateMVars dcl.type) == q
  if known then return
  let some pf := holdsLift? inst q x (mkAppN Inv #[xa[3]!, xa[4]!, xa[5]!, xa[6]!]) lhs | return
  let mv ← mkFreshExprSyntheticOpaqueMVar (← mkArrow q t)
  g.assign (mkAppN (mkConst ``himpl_of_holds) #[inst, q, lhs, rhs, pf, mv])
  let (h, g2) ← mv.mvarId!.intro1P
  replaceMainGoal [← arSplitAnd g2 (mkFVar h)]

def wgInvAll (P : WgP) (Inv : Expr) : TacticM Unit := do
  for x in (← wgLhs) do
    if wgIsSeg x && x.getAppArgs[2]! == P.cLam then wgInvFact P Inv x

def wgPGIdx (I : WgPGI) (p : Name) : MetaM (Nat × Expr × Expr) := do
  let j := I.ms.idxOf p
  let (m, per, rs) := I.prof[j]!
  let tv : Nat × Nat × List Nat := (m, per, rs.toList)
  let hpr := mkApp2 (mkConst ``Eq.refl [1]) (ToExpr.toTypeExpr (α := Nat × Nat × List Nat)) (toExpr tv)
  return (j, toExpr tv, hpr)

def wgBuildAbsPG (P : WgP) : MetaM Expr := do
  let some I ← wgPGOf P.pname | throwError "pg: none"
  let (j, _, hpr) ← wgPGIdx I P.pname
  let (m, per, rs) := I.prof[j]!
  let pty := (← getConstInfo P.pname).type
  forallTelescope pty fun xs _ => do
    let x := xs[0]!
    let y := xs[1]!
    let atom := mkAppN (mkConst P.pname) xs
    let ph := if P.profLam.isSome then
        mkAppN (mkConst ``Sep.pAbsPhi) #[I.inst, I.C, I.B, I.profE, I.hA, mkNatLit j, mkNatLit m, mkNatLit per,
          toExpr rs.toList, hpr, x, y]
      else mkAppN (mkConst ``Sep.pAbsLe) #[I.inst, I.C, I.B, I.profE, I.hA, mkNatLit j, mkNatLit m, toExpr rs.toList,
          hpr, x, y]
    let some (_, _, rhs) := (← inferType ph).app3? ``HProp.himpl | throwError "pg: abs rhs"
    let mid := wgPGAt I.inst I.C I.B j x y
    let pf := mkAppN (mkConst ``HProp.himpl_trans) #[I.inst, atom, mid, rhs, mkApp2 I.absT[j]! x y, ph]
    let ty ← mkAppM ``HProp.himpl #[atom, ← wgAbsTarget P xs]
    unless ← isDefEq rhs (← wgAbsTarget P xs) do throwError "pg: abs type"
    mkLambdaFVars xs (← mkExpectedTypeHint pf ty)

def wgBuildConcPG (P : WgP) : MetaM Expr := do
  let some I ← wgPGOf P.pname | throwError "pg: none"
  let (j, _, hpr) ← wgPGIdx I P.pname
  let (m, per, rs) := I.prof[j]!
  let nat := wgPGNat
  withLocalDeclD `k nat fun k => withLocalDeclD `x nat fun x =>
  withLocalDeclD `y nat fun y => withLocalDeclD `n arIntT fun n => do
  let cond ← wgCond P k
  withLocalDeclD `hc cond fun hc => do
    let hj := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
    let cp := if P.profLam.isSome then
        mkAppN (mkConst ``Sep.pConcPhi) #[I.inst, I.C, I.B, I.profE, I.rkE, I.NE, I.spsE, I.certE, I.hC, mkNatLit j,
          mkNatLit m, mkNatLit per, toExpr rs.toList, hj, hpr, k, n, x, y, hc]
      else mkAppN (mkConst ``Sep.pConcLe) #[I.inst, I.C, I.B, I.profE, I.rkE, I.NE, I.spsE, I.certE, I.hC, mkNatLit j,
          mkNatLit m, toExpr rs.toList, hj, hpr, k, n, x, y, hc]
    let some (_, lhs, _) := (← inferType cp).app3? ``HProp.himpl | throwError "pg: conc lhs"
    let atom := mkApp2 (mkConst P.pname) x y
    let pf := mkAppN (mkConst ``HProp.himpl_trans) #[I.inst, lhs, wgPGAt I.inst I.C I.B j x y, atom, cp,
      mkApp3 I.concG (mkNatLit j) x y]
    let seg := wgSeg P k n x y
    unless ← isDefEq lhs seg do throwError "pg: conc type"
    let ty ← mkAppM ``HProp.himpl #[seg, atom]
    mkLambdaFVars #[k, x, y, n, hc] (← mkExpectedTypeHint pf ty)

def wgBuildInvPG (P : WgP) : MetaM Expr := do
  let some I ← wgPGOf P.pname | throwError "pg: none"
  let nat := wgPGNat
  withLocalDeclD `k nat fun k => withLocalDeclD `n arIntT fun n =>
  withLocalDeclD `s nat fun s => withLocalDeclD `t nat fun t => do
    let pf := mkAppN (mkConst ``Sep.pInv) #[I.inst, I.C, k, n, s, t]
    let ty ← mkAppM ``holdsP #[P.invLam.beta #[k, s, t, n], wgSeg P k n s t]
    unless ← isDefEq (← inferType pf) ty do throwError "pg: inv type"
    mkLambdaFVars #[k, n, s, t] (← mkExpectedTypeHint pf ty)

def wgBuildInv (P : WgP) : TacticM Expr := do
  let hc ← withLocalDeclD `s P.sty fun s => withLocalDeclD `s' P.sty fun s' =>
    withLocalDeclD `w arIntT fun w => do
      let q := P.relLam.beta #[s, s', w]
      let cell := P.cLam.beta #[s, s', w]
      let top ← mkAppM ``HProp.hstar #[← mkAppOptM ``HProp.hpure #[P.inst, q],
        mkApp (mkConst ``HProp.htop) P.inst]
      let m ← arGoal (← mkAppM ``HProp.himpl #[cell, top])
      for g in ← wgSplitDisj do
        setGoals [g]
        withMainContext do
          let g ← getMainGoal
          let some (lhs, _) := entailHead? (← instantiateMVars (← g.getType)) | throwError "wg: inv"
          let pq ← wgSide (← whnfR q)
          g.assign (← mkAppOptM ``himpl_pure_top #[P.inst, q, lhs, ← mkExpectedTypeHint pq q])
      let pf ← instantiateMVars m
      mkLambdaFVars #[s, s', w] (← mkAppOptM ``holdsP_of_top #[P.inst, q, cell, pf])
  let z ← arIntLit 0
  let h0 ← withLocalDeclD `s P.sty fun s => do
    let g ← wgNorm (P.invLam.beta #[mkNatLit 0, s, s, z])
    let pf ← wgSide g
    mkLambdaFVars #[s] (← mkExpectedTypeHint pf (P.invLam.beta #[mkNatLit 0, s, s, z]))
  let hs ← withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `s P.sty fun s =>
    withLocalDeclD `s' P.sty fun s' => withLocalDeclD `t P.sty fun t =>
    withLocalDeclD `w arIntT fun w => withLocalDeclD `m arIntT fun m => do
    withLocalDeclD `hr (P.relLam.beta #[s, s', w]) fun hr => do
    withLocalDeclD `hi (P.invLam.beta #[k, s', t, m]) fun hi => do
      let k1 ← mkAppM ``HAdd.hAdd #[k, mkNatLit 1]
      let tgt := P.invLam.beta #[k1, s, t, ← arAdd m w]
      let pf ← wgSide (← whnfR tgt)
      mkLambdaFVars #[k, s, s', t, w, m, hr, hi] (← mkExpectedTypeHint pf tgt)
  withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `n arIntT fun n =>
  withLocalDeclD `s P.sty fun s => withLocalDeclD `t P.sty fun t => do
    let pf := mkAppN (mkConst ``Sep.wseg_inv) #[P.inst, P.sty, P.cLam, P.relLam, P.invLam, hc, h0,
      hs, k, n, s, t]
    let ty ← mkAppM ``holdsP #[P.invLam.beta #[k, s, t, n], wgSeg P k n s t]
    unless ← isDefEq (← inferType pf) ty do throwError "wg: inv type"
    mkLambdaFVars #[k, n, s, t] (← mkExpectedTypeHint pf ty)

def wgInvOf (P : WgP) : TacticM (Option Expr) :=
  wgLem s!"inv:{P.cLam.hash}:{P.relLam.hash}:{P.invLam.hash}"
    (if P.pg then (try wgBuildInvPG P catch _ => wgBuildInv P) else wgBuildInv P)

def wgSelect (nb j : Nat) : TacticM Unit := do
  for _ in [0 : j] do applyConstT ``hdisj_right
  if j + 1 < nb then applyConstT ``hdisj_left

def wgViews (P : WgP) : Array WgP :=
  if P.cellData.isEmpty then #[P] else
  P.cellData.mapIdx fun d (pre, next, us, w, _) =>
    { P with preLam := pre, nextLam := next, usTys := us, wLam := some w, disj := (d, P.cellData.size) }

def wgBuildCI (P : WgP) : TacticM Expr := do
  withLocalDeclsD (wgDecls (wgMovTys P) "cs") fun S => withLocalDeclsD (wgDecls P.usTys "cu") fun us => do
    let pre := P.preLam.beta (S ++ us)
    let st ← wgTuple S
    let nx ← wgNorm (P.nextLam.beta (S ++ us))
    let one ← match P.wLam with
      | some f => pure (f.beta (S ++ us))
      | none => arIntLit 1
    let tgt := wgSeg P (mkNatLit 1) one st nx
    let cellE ← wgNorm (P.cLam.beta #[st, nx, one])
    let m ← arGoal (← mkAppM ``HProp.himpl #[pre, cellE])
    if P.disj.2 > 1 then wgSelect P.disj.2 P.disj.1
    convClose
    unless (← getUnsolvedGoals).isEmpty do throwError "wg: ci open"
    let pf ← instantiateMVars m
    let cl := mkAppN (mkConst ``Sep.wseg_cell) #[P.inst, P.sty, P.cLam, st, nx, one]
    let full ← mkAppOptM ``HProp.himpl_trans #[P.inst, pre, cellE, tgt, pf, cl]
    mkLambdaFVars (S ++ us) full

def wgCIOf (P : WgP) : TacticM (Option Expr) :=
  wgLem s!"ci:{P.cLam.hash}:{P.preLam.hash}:{P.nextLam.hash}"
    (wgBuildCI (((wgViews P).find? fun V => V.preLam == P.preLam && V.nextLam == P.nextLam).getD P))

def addrKey? (e : Expr) : Option (Option FVarId × Nat) :=
  if e.isFVar then some (some e.fvarId!, 0)
  else if let some n := e.nat? then some (none, n)
  else if e.isAppOfArity ``HAdd.hAdd 6 then
    match e.appFn!.appArg!.isFVar, e.appArg!.nat? with
    | true, some n => some (some e.appFn!.appArg!.fvarId!, n)
    | _, _ => none
  else none

def addrApart (a b : Expr) : Bool :=
  match addrKey? a, addrKey? b with
  | some ka, some kb => ka != kb
  | _, _ => false

partial def wgAssign (L : Array Expr) (rs : List Expr) (used : Array Nat) :
    MetaM (Option (Array Nat)) := do
  match rs with
  | [] => return some #[]
  | r :: rest =>
    let r ← instantiateMVars r
    let ra? := if r.isAppOfArity ``HProp.hsingle 3 then some r.appFn!.appArg! else none
    for j in [0 : L.size] do
      if used.contains j then continue
      unless L[j]!.getAppFn == r.getAppFn do continue
      if let some ra := ra? then
        if L[j]!.isAppOfArity ``HProp.hsingle 3 && addrApart ra L[j]!.appFn!.appArg! then continue
      let s ← saveState
      if ← (try checkpointDefEq (isDefEq r L[j]!) catch _ => pure false) then
        if let some js ← wgAssign L rest (used.push j) then return some (#[j] ++ js)
      s.restore
    return none

def wgCellAt (P : WgP) (L : Array Expr) (used : Array Nat) (cur : Option (Array Expr))
    (strict : Bool := true) (first : Option (Nat × Bool) := none) (hsOnly : Bool := false) :
    MetaM (Option (Array Expr × Array Expr × Array Nat)) := do
  let s0 ← saveState
  let S ← (wgMovTys P).mapM fun ty => mkFreshExprMVar (some ty)
  if let some c := cur then
    for i in [0 : S.size] do
      if P.cst.contains i then continue
      unless ← isDefEq S[i]! c[i]! do
        s0.restore
        return none
  let us ← P.usTys.mapM fun ty => mkFreshExprMVar (some ty)
  let items := flatStar (P.preLam.beta (S ++ us)) #[]
  let pat := items.filter (·.isAppOf ``HProp.hsingle) ++
    (if hsOnly then #[] else items.filter (fun e => !e.isAppOf ``HProp.hsingle && !e.isAppOf ``HProp.hpure))
  if pat.isEmpty then
    s0.restore
    return none
  let r ← match first with
    | none => wgAssign L pat.toList used
    | some (j, exact) => do
      let p0 ← instantiateMVars pat[0]!
      let l0 ← instantiateMVars L[j]!
      let pa := p0.getAppArgs
      let la := l0.getAppArgs
      unless l0.isAppOf ``HProp.hsingle && la.size == pa.size do return none
      if exact && pa[pa.size - 2]! != la[la.size - 2]! then return none
      if addrApart pa[pa.size - 2]! la[la.size - 2]! then return none
      unless ← (try checkpointDefEq (isDefEq p0 l0) catch _ => pure false) do return none
      let some js ← wgAssign L (pat.toList.drop 1) (used.push j) | return none
      pure (some (#[j] ++ js))
  let some js := r | do s0.restore; return none
  let S ← S.mapM instantiateMVars
  let us ← us.mapM instantiateMVars
  if strict && (S ++ us).any (·.hasExprMVar) then
    s0.restore
    return none
  return some (S, us, js)

def wgCellNext (P : WgP) (S us : Array Expr) : MetaM (Array Expr) := do
  wgComps (← wgNorm (P.nextLam.beta (S ++ us))) P.mov.size

def wgUnifyStA (cst : Array Nat) (a b : Array Expr) : TacticM Bool := do
  if a.size != b.size then return false
  let s ← saveState
  for i in [0 : a.size] do
    if cst.contains i then continue
    if ← (try checkpointDefEq (isDefEq a[i]! b[i]!) catch _ => pure false) then continue
    let x ← instantiateMVars a[i]!
    let y ← instantiateMVars b[i]!
    if !x.hasExprMVar && !y.hasExprMVar && (← inferType x) == arIntT then
      if ← withMainContext (wgEqOk x y) then continue
    s.restore
    return false
  return true

def wgNil (P : WgP) (r : Expr) : TacticM Unit := do
  let lem ← withMainContext do
    let ra ← r.getAppArgs.mapM instantiateMVars
    let nc := P.mov.size
    unless ← isDefEq ra[3]! (mkNatLit 0) do throwError "wg: nil k"
    if (← instantiateMVars ra[4]!).isMVar then
      unless ← isDefEq ra[4]! (← arIntLit 0) do throwError "wg: nil n"
    let sc ← wgComps ra[5]! nc
    let ec ← wgComps ra[6]! nc
    for (a, b) in sc.zip ec do
      let a ← instantiateMVars a
      let b ← instantiateMVars b
      if b.isMVar || a.isMVar then let _ ← isDefEq b a
    let ra ← r.getAppArgs.mapM instantiateMVars
    let h ← wgTupEq (← wgComps ra[5]! nc) (← wgComps ra[6]! nc)
    let hn ← wgSide (← mkAppM ``Eq #[ra[4]!, ← arIntLit 0])
    pure (mkAppN (mkConst ``Sep.wseg_nil) #[P.inst, P.sty, ra[2]!, ra[4]!, ra[5]!, ra[6]!, h, hn])
  let _ ← arRwLhs [] lem

def wgOpen (v : Array Expr) : MetaM Bool := do
  return (← v.mapM instantiateMVars).any (·.hasExprMVar)

def wgFill (v : Array Expr) (cands : Array (Array Expr)) : MetaM Bool := do
  if !(← wgOpen v) then return true
  for c in cands do
    if ← wgUnifySt v c then
      if !(← wgOpen v) then return true
  return false

def wgCellMatch (P : WgP) (CI : Expr) (hst hen : Option (Array Expr)) (avoid : Array Expr) :
    TacticM (Option (Array Expr × Expr)) := withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (lhs, rhs) := entailHead? t | return none
  let Ls := flatStar lhs #[]
  let used := (Array.range Ls.size).filter (avoid.contains Ls[·]!)
  let mut cands : Array (Array Expr) := #[]
  for e in Ls ++ #[rhs] do
    if let some a := e.find? (fun y => wgIsSeg y && !y.getAppArgs[5]!.hasLooseBVars) then
      cands := cands.push (← wgComps a.getAppArgs[5]! P.mov.size)
  for j in [0 : Ls.size] do
    unless Ls[j]!.isAppOf ``HProp.hsingle && !used.contains j do continue
    let s0 ← saveState
    if let some (S, us, js) ← wgCellAt P Ls used hst false (some (j, false)) then
      let mut cok := true
      if let some h := hst then
        for i in P.cst do
          unless ← isDefEq S[i]! h[i]! do cok := false
      let nx ← wgComps (← wgNorm (P.nextLam.beta (S ++ us))) P.mov.size
      let ok ← if !cok then pure false else match hen with
        | some e => do pure ((← wgFill S cands) && (← wgUnifySt nx e) && !(← wgOpen (S ++ us)))
        | none => do pure ((← wgFill S cands) && (← wgFill nx cands) && !(← wgOpen (S ++ us)))
      if ok then
        let S ← S.mapM instantiateMVars
        let us ← us.mapM instantiateMVars
        return some (js.map (Ls[·]!), mkAppN CI (S ++ us))
    s0.restore
  return none

def wgConcLhs (P : WgP) (k nE : Expr) (xs miss : Array Expr) : MetaM Expr := do
  let seg := wgSeg P k nE (← wgTuple (P.mov.map (xs[·]!))) (← wgTuple (wgEnC P xs miss))
  match P.tailLam with
  | some t => mkAppM ``HProp.hstar #[seg, t.beta (xs ++ miss)]
  | none => pure seg

structure WgGen where
  aty : Expr
  F : Expr
  nX : Nat
  stL : Expr
  enL : Expr
  mTy : Option Expr
  nEL : Option Expr
  PL : Expr
  TL : Option Expr

def wgGenData (P : WgP) (xs : Array Expr) : MetaM WgGen := do
  let atom := mkAppN (mkConst P.pname) xs
  let some (F, ta) ← functionalOf? atom | throwError "wg: gen functional"
  let aty ← inferType ta
  if aty.isAppOf ``Sum then throwError "wg: gen mutual"
  let nX := xs.size
  unless ← isDefEq ta (← wgTuple xs) do throwError "wg: gen tuple"
  let mTy := (wgMissTys P)[0]?
  if P.tailLam.isSome && mTy.isNone then throwError "wg: gen tail"
  withLocalDeclD `a aty fun a => withLocalDeclD `m (mTy.getD (mkConst ``Nat)) fun m => do
    let ps ← (Array.range nX).mapM (wgProj a · nX)
    let st ← wgTuple (P.mov.map (ps[·]!))
    let en ← wgTuple (P.endSpec.map fun (f, c) => match f, c with
      | some f, _ => ps[f]!
      | none, some c => c
      | none, none => m)
    let nE := P.ai.map (ps[·]!)
    let pa := mkAppN (mkConst P.pname) ps
    let enL ← mkLambdaFVars (if mTy.isSome then #[a, m] else #[a]) en
    let TL ← P.tailLam.mapM fun t => mkLambdaFVars #[a, m] (t.beta (ps.push m))
    return { aty, F, nX, stL := ← mkLambdaFVars #[a] st, enL, mTy,
             nEL := ← nE.mapM (mkLambdaFVars #[a] ·), PL := ← mkLambdaFVars #[a] pa, TL }

def wgGenEn (G : WgGen) (a : Expr) (m : Option Expr) : Expr :=
  match m with
  | some m => G.enL.beta #[a, m]
  | none => G.enL.beta #[a]

def wgBranchTo (P : WgP) (xs : Array Expr) (L : Expr) (bi : Nat) : TacticM (Expr × MVarId) := do
  let entries ← arEntries
  let some ent := entries.find? (·.headFn == P.pname) | throwError "wg: gen unfold"
  let eqPf := mkAppN (mkConst ent.lemmaName) xs
  let some (_, lhsE, body) := (← inferType eqPf).eq? | throwError "wg: gen unfold eq"
  let some br := (wgBranches body #[])[bi]? | throwError "wg: gen branch"
  let m ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``HProp.himpl) P.inst L br)
  let toBody := wgPGSel P.inst L body bi m
  let back ← mkEqSymm eqPf
  let pf := mkAppN (mkConst ``HProp.himpl_trans) #[P.inst, L, body, lhsE, toBody,
    mkAppN (mkConst ``himpl_of_eq) #[P.inst, body, lhsE, back]]
  return (pf, m.mvarId!)

def wgGenRel (G : WgGen) (a a' w : Expr) : MetaM Expr := do
  let ee ← match G.mTy with
    | some ty => withLocalDeclD `m ty fun m => do
        mkForallFVars #[m] (← mkEq (wgGenEn G a' (some m)) (wgGenEn G a (some m)))
    | none => mkEq (wgGenEn G a' none) (wgGenEn G a none)
  let ee ← match G.TL, G.mTy with
    | some tl, some ty => mkAppM ``And #[ee, ← withLocalDeclD `m ty fun m => do
        mkForallFVars #[m] (← mkEq (tl.beta #[a', m]) (tl.beta #[a, m]))]
    | _, _ => pure ee
  match G.nEL with
  | some nl => mkAppM ``And #[ee, ← mkEq (nl.beta #[a]) (← arAdd (nl.beta #[a']) w)]
  | none => pure ee

partial def wgCellViews (e : Expr) : Array Expr :=
  if e.isAppOfArity ``hdisj 3 then #[e.getAppArgs[1]!] ++ wgCellViews e.getAppArgs[2]! else #[e]

partial def wgCellSel (inst V e : Expr) (d : Nat) : Expr :=
  if e.isAppOfArity ``hdisj 3 then
    let a := e.getAppArgs
    if d == 0 then mkAppN (mkConst ``hdisj_left) #[inst, V, a[1]!, a[2]!, mkApp2 (mkConst ``HProp.himpl_refl) inst V]
    else mkAppN (mkConst ``hdisj_right) #[inst, V, a[1]!, a[2]!, wgCellSel inst V a[2]! (d - 1)]
  else mkApp2 (mkConst ``HProp.himpl_refl) inst V

partial def wgCellElim (inst K H e : Expr) (pfs : Array Expr) (d : Nat) : Expr :=
  if e.isAppOfArity ``hdisj 3 then
    let a := e.getAppArgs
    mkAppN (mkConst ``hdisj_star_elim) #[inst, a[1]!, a[2]!, K, H, pfs[d]!, wgCellElim inst K H a[2]! pfs (d + 1)]
  else pfs[d]!

def wgViewIdx (P : WgP) (j : Nat) : Option Nat :=
  if P.cellData.isEmpty then none else P.cellData.findIdx? (·.2.2.2.2 == j)

def wgBaseLem (P : WgP) (G : WgGen) (a : Expr) : MetaM Expr := do
  let st := G.stL.beta #[a]
  let cnt := G.nEL.isSome
  let nE := (G.nEL.map (·.beta #[a])).toArray
  let (thm, args) ← match G.mTy, G.TL with
    | none, _ => do
      let thm ← match P.kmin, cnt with
        | 0, true => pure ``Sep.wseg_base0_cnt
        | 0, false => pure ``Sep.wseg_base0_free
        | 1, true => pure ``Sep.wseg_base1_cnt
        | 1, false => pure ``Sep.wseg_base1_free
        | 2, false => pure ``Sep.wseg_base2_free
        | _, _ => throwError "wg: gen base"
      pure (thm, #[P.cLam, st, wgGenEn G a none] ++ nE)
    | some ty, tl => do
      let enF ← withLocalDeclD `m ty fun m => do mkLambdaFVars #[m] (wgGenEn G a (some m))
      match tl with
      | none =>
        let thm ← match P.kmin, cnt with
          | 0, true => pure ``Sep.wseg_base0_cnt_m
          | 0, false => pure ``Sep.wseg_base0_free_m
          | 1, true => pure ``Sep.wseg_base1_cnt_m
          | 1, false => pure ``Sep.wseg_base1_free_m
          | _, _ => throwError "wg: gen base"
        pure (thm, #[ty, P.cLam, st, enF] ++ nE)
      | some tl =>
        let thm ← match P.kmin, cnt with
          | 0, false => pure ``Sep.wseg_base0_free_mt
          | 1, false => pure ``Sep.wseg_base1_free_mt
          | _, _ => throwError "wg: gen base"
        let tF ← withLocalDeclD `m ty fun m => do mkLambdaFVars #[m] (tl.beta #[a, m])
        pure (thm, #[ty, P.cLam, st, enF, tF])
  return mkAppN (mkConst thm) (#[P.inst, P.sty] ++ args)

def wgViaPick (P : WgP) (st : Expr) : TacticM Nat := do
  let (d, pay) ← withMainContext do
    let L ← wgLhs
    let hw := L.filter (·.isAppOf ``hwith)
    let some h0 := hw[0]? | throwError "wg: via pick"
    let c0 := P.mov.map (h0.getAppArgs[1]!.getAppArgs[·]!)
    let cs ← wgComps st P.mov.size
    let mut found := none
    for d in [0 : P.cellData.size] do
      let (pre, next, usT, _, _) := P.cellData[d]!
      let s ← saveState
      let us ← usT.mapM fun t => mkFreshExprMVar (some t)
      let mut ok := true
      for r in flatStar (← wgNorm (pre.beta (cs ++ us))) #[] do
        unless r.isAppOfArity ``HProp.hsingle 3 do continue
        let l? ← L.findM? (fun l => do
          if l.isAppOfArity ``HProp.hsingle 3 then isDefEq l.getAppArgs[1]! r.getAppArgs[1]! else pure false)
        unless ← (match l? with | some l => isDefEq l r | none => pure false) do ok := false
      let nx ← wgComps (← instantiateMVars (← wgNorm (next.beta (cs ++ us)))) P.mov.size
      s.restore
      if ok && nx == c0 then
        found := some d
        break
    let some d := found | throwError "wg: via pick"
    pure (d, hw.extract 1 hw.size)
  for h in pay do
    let a := h.getAppArgs
    let _ ← arRwLhs [h] (mkAppN (mkConst ``hwith_l) #[a[0]!, a[1]!, a[2]!])
  return d

def wgBuildAbsGen (P : WgP) : TacticM Expr := do
  let pty := (← getConstInfo P.pname).type
  forallTelescope pty fun xs _ => do
  let G ← wgGenData P xs
  let inst := P.inst
  let QL ← withLocalDeclD `a G.aty fun a => do
    mkLambdaFVars #[a] (← wgAbsTarget P (← (Array.range G.nX).mapM (wgProj a · G.nX)))
  let (BL, hbase) ← withLocalDeclD `a G.aty fun a => do
    let lem ← wgBaseLem P G a
    let some (b, _) := entailHead? (← inferType lem) | throwError "wg: gen base"
    pure (← mkLambdaFVars #[a] (← Core.betaReduce b), ← mkLambdaFVars #[a] lem)
  let relL ← withLocalDeclD `a G.aty fun a => withLocalDeclD `a' G.aty fun a' =>
    withLocalDeclD `w arIntT fun w => do mkLambdaFVars #[a, a', w] (← wgGenRel G a a' w)
  let (cons, cargs) ← match G.nEL.isSome, G.mTy, G.TL with
    | true, none, none => pure (``Sep.wseg_cons_cnt, #[G.aty, P.sty, P.cLam, G.stL, G.enL] ++ G.nEL.toArray)
    | false, none, none => pure (``Sep.wseg_cons_free, #[G.aty, P.sty, P.cLam, G.stL, G.enL])
    | true, some ty, none => pure (``Sep.wseg_cons_cnt_m, #[G.aty, P.sty, ty, P.cLam, G.stL, G.enL] ++ G.nEL.toArray)
    | false, some ty, none => pure (``Sep.wseg_cons_free_m, #[G.aty, P.sty, ty, P.cLam, G.stL, G.enL])
    | false, some ty, some tl => pure (``Sep.wseg_cons_free_mt, #[G.aty, P.sty, ty, P.cLam, G.stL, G.enL, tl])
    | _, _, _ => throwError "wg: gen cons"
  let hcons := mkAppN (mkConst cons) (#[inst] ++ cargs ++ #[mkNatLit P.kmin])
  let WL ← withLocalDeclD `b G.aty fun b => do
    mkLambdaFVars #[b] (← mkAppM ``hwith #[G.PL.beta #[b], QL.beta #[b]])
  let hstep ← withLocalDeclD `X (← mkArrow G.aty (mkApp (mkConst ``HProp) inst)) fun X =>
    withLocalDeclsD (wgDecls P.tys "gx") fun ys => do
      let Xe := if P.via then WL else X
      let tup ← wgTuple ys
      let st := G.stL.beta #[tup]
      let some fx ← unfoldDefinition? (mkApp2 G.F Xe tup) | throwError "wg: gen F"
      let body ← wgNorm (← whnfCore fx)
      let brs := wgBranches body #[]
      let isRec := fun (e : Expr) => if P.via then e.isAppOf ``hwith else e.getAppFn == X
      let Bt ← wgNorm (BL.beta #[tup])
      let stepL ← withLocalDeclD `a' G.aty fun a' => withLocalDeclD `w arIntT fun w => do
        let inner ← mkAppM ``HProp.hstar #[← mkAppOptM ``HProp.hpure #[inst, ← wgGenRel G tup a' w],
          ← mkAppM ``HProp.hstar #[mkApp3 P.cLam st (G.stL.beta #[a']) w, mkApp Xe a']]
        let lw ← mkAppM ``HProp.hexists #[← mkLambdaFVars #[w] inner]
        mkAppM ``HProp.hexists #[← mkLambdaFVars #[a'] lw]
      let tgt ← mkAppM ``Sep.wor #[Bt, stepL]
      let mut pfs : Array Expr := #[]
      for j in [0 : brs.size] do
        let br := brs[j]!
        if (br.find? isRec).isNone then
          let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[br, Bt])
          setGoals [m.mvarId!]
          convClose
          pfs := pfs.push (← mkAppOptM ``Sep.wor_l #[none, br, Bt, stepL, ← instantiateMVars m])
          continue
        let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[br, stepL])
        setGoals [m.mvarId!]
        let _ ← arIntroLhs
        let vd ← if P.via then some <$> wgViaPick P st else pure (wgViewIdx P j)
        let g ← getMainGoal
        g.withContext do
          let some (lhs, _) := entailHead? (← instantiateMVars (← g.getType)) | throwError "wg: gen step"
          let some xa := (flatStar lhs #[]).find? isRec | throwError "wg: gen rec"
          let ta ← if P.via then wgTuple xa.getAppArgs[1]!.getAppArgs else pure xa.appArg!
          let (RL, VL, CL, hv, inner) ← withLocalDeclD `w arIntT fun w => do
            let cellN ← wgNorm (mkApp3 P.cLam st (G.stL.beta #[ta]) w)
            let (V, hv) := match vd with
              | some d => let V := (wgCellViews cellN)[d]!; (V, wgCellSel inst V cellN d)
              | none => (cellN, mkApp2 (mkConst ``HProp.himpl_refl) inst cellN)
            let r ← mkAppOptM ``HProp.hpure #[inst, ← wgGenRel G tup ta w]
            let lam := fun e => mkLambdaFVars #[w] e
            pure (← lam r, ← lam V, ← lam cellN, ← lam hv,
              ← mkAppM ``HProp.hexists #[← lam (← mkAppM ``HProp.hstar #[r, ← mkAppM ``HProp.hstar #[V, xa]])])
          let m2 ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[lhs, ← wgNorm inner])
          setGoals [m2.mvarId!]
          convClose
          let pfV := mkAppN (mkConst ``view_hexists) #[inst, lhs, xa, RL, VL, CL, ← instantiateMVars m2, hv]
          let pf2 ← mkAppOptM ``HProp.himpl_hexists_r #[none, none, ta, lhs, stepL.appArg!, pfV]
          unless ← isDefEq (← g.getType) (← inferType pf2) do throwError "wg: gen step type"
          g.assign pf2
        pfs := pfs.push (← mkAppOptM ``Sep.wor_r #[none, br, Bt, stepL, ← instantiateMVars m])
      let (pf, _) := wgPGElim inst tgt body pfs 0
      withLocalDeclD `a G.aty fun a => do
        let ps ← (Array.range G.nX).mapM (wgProj a · G.nX)
        let bd := (← mkLambdaFVars ys pf).beta ps
        mkLambdaFVars (if P.via then #[a] else #[X, a]) bd
  let tup ← wgTuple xs
  let pf ← if P.via then do
      let entries ← arEntries
      let some ent := entries.find? (·.headFn == P.pname) | throwError "wg: via unfold"
      let some val := (← getConstInfo ent.lemmaName).value? (allowOpaque := true) | throwError "wg: via value"
      let some un := val.find? (fun e => e.isAppOf `Bench.lfp_unfold) | throwError "wg: via lfp"
      let hmono := un.getAppArgs.back!
      let hfold ← withLocalDeclD `a G.aty fun a => do
        mkLambdaFVars #[a] (mkAppN (mkConst `Bench.lfp_pre) #[inst, G.aty, G.F, hmono, a])
      pure (mkAppN (mkConst ``wseg_abs_with) #[inst, G.aty, P.sty, G.F, hmono, hfold, P.cLam, G.stL, relL,
        QL, BL, hstep, hbase, hcons, tup])
    else do
      let hind ← withLocalDeclD `X (← mkArrow G.aty (mkApp (mkConst ``HProp) inst)) fun X => do
        let hxT ← withLocalDeclD `b G.aty fun b => do
          mkForallFVars #[b] (← mkAppM ``HProp.himpl #[mkApp2 G.F X b, mkApp X b])
        withLocalDeclD `hX hxT fun hX => withLocalDeclD `a G.aty fun a => do
          mkLambdaFVars #[X, hX, a] (← mkAppM ``lfpG_induct #[G.F, X, hX, a])
      pure (mkAppN (mkConst ``Sep.wseg_abs_core) #[inst, G.aty, P.sty, G.PL, G.F, hind, P.cLam, G.stL, relL,
        QL, BL, hstep, hbase, hcons, tup])
  let ty ← mkAppM ``HProp.himpl #[mkAppN (mkConst P.pname) xs, ← wgAbsTarget P xs]
  unless ← isDefEq (← inferType pf) ty do throwError "wg: gen abs type"
  mkLambdaFVars xs (← mkExpectedTypeHint pf ty)

def wgLoFact (lo x : Expr) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (lhs, rhs) := entailHead? t | return
  let inst := t.getAppArgs[0]!
  let pfx := mkAppN lo x.getAppArgs
  let hty ← whnfR (← inferType pfx)
  unless hty.isAppOf ``holdsP do return
  let q := hty.getAppArgs[1]!
  let some pf := holdsLift? inst q x pfx lhs | return
  let mv ← mkFreshExprSyntheticOpaqueMVar (← mkArrow q t)
  g.assign (mkAppN (mkConst ``himpl_of_holds) #[inst, q, lhs, rhs, pf, mv])
  let (_, g2) ← mv.mvarId!.intro1P
  replaceMainGoal [g2]

def wgRflEq (a b : Expr) : MetaM Expr := do
  unless ← isDefEq a b do throwError "wg: gen rfl"
  mkExpectedTypeHint (← mkEqRefl a) (← mkEq a b)

def wgBuildConcGen (P : WgP) (lo : Option Expr) : TacticM Expr := do
  let pty := (← getConstInfo P.pname).type
  forallTelescope pty fun xs0 _ => do
  let G ← wgGenData P xs0
  let inst := P.inst
  let nA := P.mov.size
  let cnt := G.nEL.isSome
  let mTy := G.mTy.getD (mkConst ``Nat)
  let JTy ← match cnt, G.mTy with
    | true, none => pure (mkConst ``Unit)
    | false, none => pure arIntT
    | true, some ty => pure ty
    | false, some ty => wgTupleTy #[ty, arIntT]
  let jM := fun (j : Expr) => do
    match cnt, G.mTy with
    | true, some _ => pure (some j)
    | false, some _ => some <$> wgProj j 0 2
    | _, _ => pure none
  let jN := fun (a j : Expr) => do
    match G.nEL, G.mTy with
    | some nl, _ => pure (nl.beta #[a])
    | none, some _ => wgProj j 1 2
    | none, none => pure j
  let empE := mkApp (mkConst ``HProp.hempty) inst
  let jT := fun (a j : Expr) => do
    match G.TL with
    | some tl => pure (tl.beta #[a, (← jM j).getD j])
    | none => pure empE
  let lam2 := fun (f : Expr → Expr → MetaM Expr) => withLocalDeclD `a G.aty fun a =>
    withLocalDeclD `j JTy fun j => do mkLambdaFVars #[a, j] (← f a j)
  let NL ← lam2 jN
  let EL ← lam2 fun a j => do pure (wgGenEn G a (← jM j))
  let TLL ← lam2 jT
  let jxL ← withLocalDeclD `j JTy fun j => withLocalDeclD `w arIntT fun w => do
    let r ← match cnt, G.mTy with
      | true, _ => pure j
      | false, none => arSub j w
      | false, some _ => wgTuple #[← wgProj j 0 2, ← arSub (← wgProj j 1 2) w]
    mkLambdaFVars #[j, w] r
  let nxL ← withLocalDeclD `a G.aty fun a => withLocalDeclD `s' P.sty fun s' =>
    withLocalDeclD `w arIntT fun w => do
      let ps ← (Array.range G.nX).mapM (wgProj a · G.nX)
      let cs ← (Array.range nA).mapM (wgProj s' · nA)
      let mut args : Array Expr := #[]
      for i in [0 : G.nX] do
        match P.mov.idxOf? i with
        | some j => args := args.push (if P.cst.contains j then ps[i]! else cs[j]!)
        | none => args := args.push (← if P.ai == some i then arSub ps[i]! w else pure ps[i]!)
      mkLambdaFVars #[a, s', w] (← wgTuple args)
  let useInv := P.tailLam.isSome || !P.cellData.isEmpty
  let (IL, hI) ← if useInv then do
      let some Inv ← wgInvOf P | throwError "wg: gen inv"
      pure (P.invLam, Inv)
    else
      withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `n arIntT fun n =>
      withLocalDeclD `s P.sty fun s => withLocalDeclD `t P.sty fun t => do
        let IL ← mkLambdaFVars #[k, s, t, n] (mkConst ``True)
        let hI ← mkLambdaFVars #[k, n, s, t] (mkAppN (mkConst ``holdsP_true) #[inst, wgSeg P k n s t])
        pure (IL, hI)
  let hst ← withLocalDeclD `a G.aty fun a => withLocalDeclD `s' P.sty fun s' =>
    withLocalDeclD `w arIntT fun w => do
      let nxa := nxL.beta #[a, s', w]
      let q ← mkEq (G.stL.beta #[nxa]) s'
      let cell := mkApp3 P.cLam (G.stL.beta #[a]) s' w
      let pf ← if P.cst.isEmpty then
          pure (mkAppN (mkConst ``holdsP_of) #[inst, q, cell, ← wgRflEq (G.stL.beta #[nxa]) s'])
        else do
          let top ← mkAppM ``HProp.hstar #[← mkAppOptM ``HProp.hpure #[inst, q], mkApp (mkConst ``HProp.htop) inst]
          let m ← arGoal (← mkAppM ``HProp.himpl #[cell, top])
          for g in ← wgSplitDisj do
            setGoals [g]
            withMainContext do
              let g ← getMainGoal
              let some (lhs, _) := entailHead? (← instantiateMVars (← g.getType)) | throwError "wg: gen hst"
              let e ← wgTupEq (← wgComps (← wgNorm (G.stL.beta #[nxa])) nA) (← wgComps s' nA)
              g.assign (← mkAppOptM ``himpl_pure_top #[inst, q, lhs, ← mkExpectedTypeHint e q])
          mkAppOptM ``holdsP_of_top #[inst, q, cell, ← instantiateMVars m]
      mkLambdaFVars #[a, s', w] pf
  let (hN, hE, hT) ← withLocalDeclD `a G.aty fun a => withLocalDeclD `j JTy fun j =>
    withLocalDeclD `s' P.sty fun s' => withLocalDeclD `w arIntT fun w => do
      let nxa := nxL.beta #[a, s', w]
      let jx := jxL.beta #[j, w]
      let vs := #[a, j, s', w]
      let hN ← mkLambdaFVars vs (← wgRflEq (NL.beta #[nxa, jx]) (← arSub (NL.beta #[a, j]) w))
      let hE ← mkLambdaFVars vs (← wgRflEq (EL.beta #[nxa, jx]) (EL.beta #[a, j]))
      let hT ← mkLambdaFVars vs (← wgRflEq (TLL.beta #[nxa, jx]) (TLL.beta #[a, j]))
      pure (hN, hE, hT)
  let bi := P.baseIdx
  let hb ← withLocalDeclsD (wgDecls P.tys "gy") fun ys => withLocalDeclD `j JTy fun j => do
    let tup ← wgTuple ys
    let st := G.stL.beta #[tup]
    let en := EL.beta #[tup, j]
    let nE := NL.beta #[tup, j]
    let T := TLL.beta #[tup, j]
    let seg := wgSeg P (mkNatLit P.kmin) nE st en
    let lem ← match P.kmin with
      | 0 => pure (mkAppN (mkConst ``Sep.wseg_zero_elim) #[inst, P.sty, P.cLam, nE, st, en])
      | 1 => pure (mkAppN (mkConst ``Sep.wseg_uncell) #[inst, P.sty, P.cLam, st, en, nE])
      | 2 => pure (mkAppN (mkConst ``Sep.wseg_two_elim) #[inst, P.sty, P.cLam, nE, st, en])
      | _ => throwError "wg: gen kmin"
    let some (_, Lz) := entailHead? (← inferType lem) | throwError "wg: gen hb"
    let (lemF, L) ← if G.TL.isSome then do
        pure (mkAppN (mkConst ``HProp.himpl_frame_l) #[inst, seg, Lz, T, lem], ← mkAppM ``HProp.hstar #[Lz, T])
      else do
        pure (← mkAppM ``HProp.himpl_trans #[mkAppN (mkConst ``star_emp_elim) #[inst, seg], lem], Lz)
    let L' ← wgNorm L
    let (pf, g) ← wgBranchTo P ys L' bi
    setGoals [g]
    convClose
    let full := mkAppN (mkConst ``HProp.himpl_trans) #[inst, ← mkAppM ``HProp.hstar #[seg, T], L,
      mkAppN (mkConst P.pname) ys, lemF, ← instantiateMVars pf]
    withLocalDeclD `a G.aty fun a => do
      let ps ← (Array.range G.nX).mapM (wgProj a · G.nX)
      mkLambdaFVars #[a, j] ((← mkLambdaFVars ys full).beta ps)
  let h1 ← withLocalDeclsD (wgDecls P.tys "gy") fun ys =>
    withLocalDeclsD (wgDecls (wgMovTys P) "gc") fun cs => withLocalDeclD `w arIntT fun w =>
    withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `j JTy fun j => do
      let tup ← wgTuple ys
      let ct ← wgTuple cs
      let st := G.stL.beta #[tup]
      let nw ← arSub (NL.beta #[tup, j]) w
      withLocalDeclD `hi (← wgNorm (IL.beta #[k, ct, EL.beta #[tup, j], nw])) fun hi => do
      let pnx ← wgNorm (G.PL.beta #[← wgNorm (nxL.beta #[tup, ct, w])])
      let cell ← wgNorm (mkApp3 P.cLam st ct w)
      let PA := mkAppN (mkConst P.pname) ys
      let views := if P.cellData.isEmpty then #[(cell, P.stepIdx)] else
        (wgCellViews cell).mapIdx fun d V => (V, if P.via then P.stepIdx else (P.cellData[d]!).2.2.2.2)
      let mut pfs : Array Expr := #[]
      for (V, b) in views do
        let (pf, g) ← wgBranchTo P ys (← mkAppM ``HProp.hstar #[V, pnx]) b
        setGoals [g]
        if let some lo := lo then wgLoFact lo pnx
        convClose
        pfs := pfs.push (← instantiateMVars pf)
      let pf := wgCellElim inst pnx PA cell pfs 0
      withLocalDeclD `a G.aty fun a => withLocalDeclD `s' P.sty fun s' => do
        let ps ← (Array.range G.nX).mapM (wgProj a · G.nX)
        let qs ← (Array.range nA).mapM (wgProj s' · nA)
        mkLambdaFVars #[a, s'] ((← mkLambdaFVars (ys ++ cs ++ #[w, k, j, hi]) pf).beta (ps ++ qs))
  let core := mkAppN (mkConst ``wseg_conc_core) #[inst, G.aty, P.sty, JTy, G.PL, P.cLam, G.stL, NL, EL, TLL,
    nxL, jxL, mkNatLit P.kmin, IL, hI, hst, hN, hE, hT, hb, h1]
  withLocalDeclD `k (mkConst ``Nat) fun k =>
  withLocalDeclsD (wgDecls P.tys "cx") fun xs =>
  withLocalDeclD `cm mTy fun m =>
  withLocalDeclD `cn arIntT fun n => do
    let nE := match P.ai with
      | some i => xs[i]!
      | none => n
    let mv := if G.mTy.isSome then #[m] else #[]
    let jv ← match cnt, G.mTy with
      | true, none => pure (mkConst ``Unit.unit)
      | false, none => pure n
      | true, some _ => pure m
      | false, some _ => wgTuple #[m, n]
    withLocalDeclD `hk (← wgCond P k) fun hk => do
      let tup ← wgTuple xs
      let pf0 := mkAppN core #[k, tup, jv, hk]
      let lhs ← wgConcLhs P k nE xs mv
      let pf ← if G.TL.isSome then pure pf0 else
        mkAppM ``HProp.himpl_trans #[mkAppN (mkConst ``star_emp_r) #[inst, lhs], pf0]
      let ty ← mkAppM ``HProp.himpl #[lhs, mkAppN (mkConst P.pname) xs]
      unless ← isDefEq (← inferType pf) ty do throwError "wg: gen conc type"
      let vs := #[k] ++ xs ++ mv ++ (if cnt then #[] else #[n]) ++ #[hk]
      mkLambdaFVars vs (← mkExpectedTypeHint pf ty)

mutual

partial def wgAbsOf (P : WgP) : TacticM (Option Expr) := do
  wgLem s!"abs:{P.pname}" (if P.pg then wgBuildAbsPG P else wgBuildAbsGen P)

partial def wgBuildLo (P : WgP) (Abs Inv : Expr) : TacticM Expr := do
  let pty := (← getConstInfo P.pname).type
  forallTelescope pty fun xs _ => do
    let some i := P.ai | throwError "wg: lo"
    let atom := mkAppN (mkConst P.pname) xs
    let q ← arLe (← arIntLit P.kmin) xs[i]!
    let top ← mkAppM ``HProp.hstar #[← mkAppOptM ``HProp.hpure #[P.inst, q],
      mkApp (mkConst ``HProp.htop) P.inst]
    let m ← arGoal (← mkAppM ``HProp.himpl #[atom, top])
    let _ ← arRwLhs [atom] (mkAppN Abs xs)
    let _ ← arIntroLhs
    wgInvAll P Inv
    withMainContext do
      let g ← getMainGoal
      let some (lhs, _) := entailHead? (← instantiateMVars (← g.getType)) | throwError "wg: lo"
      g.assign (← mkAppOptM ``himpl_pure_top #[P.inst, q, lhs, ← wgSide q])
    let pf ← instantiateMVars m
    mkLambdaFVars xs (← mkAppOptM ``holdsP_of_top #[P.inst, q, atom, pf])

partial def wgFactProp (P : WgP) (xs : Array Expr) : MetaM Expr :=
  withLocalDeclD `k (mkConst ``Nat) fun k =>
  withLocalDeclD `n arIntT fun n =>
  withLocalDeclsD (wgDecls (wgMissTys P) "wm") fun miss => do
    let st ← wgTuple (P.mov.map (xs[·]!))
    let en ← wgTuple (wgEnC P xs miss)
    let nE := match P.ai with
      | some i => xs[i]!
      | none => n
    let vs := if P.ai.isSome then #[k] ++ miss else #[k, n] ++ miss
    let cs := (pureConjs (← wgNorm (P.invLam.beta #[k, st, en, nE])) #[]).filter (!·.isForall)
    let body ← wgConj (cs.push (← wgCond P k))
    let mut acc := body
    for v in vs.reverse do
      acc ← mkAppM ``Exists #[← mkLambdaFVars #[v] acc]
    return acc

partial def wgBuildFact (P : WgP) (Abs Inv : Expr) : TacticM Expr := do
  let pty := (← getConstInfo P.pname).type
  forallTelescope pty fun xs _ => do
    let atom := mkAppN (mkConst P.pname) xs
    let q ← wgFactProp P xs
    let top ← mkAppM ``HProp.hstar #[← mkAppOptM ``HProp.hpure #[P.inst, q],
      mkApp (mkConst ``HProp.htop) P.inst]
    let m ← arGoal (← mkAppM ``HProp.himpl #[atom, top])
    let vs ← arRwLhs [atom] (mkAppN Abs xs)
    let _ ← arIntroLhs
    wgInvAll P Inv
    arIntroFacts
    withMainContext do
      let g ← getMainGoal
      let some (lhs, _) := entailHead? (← instantiateMVars (← g.getType)) | throwError "wg: fact"
      let mut cur : Expr := q
      let mut lams : Array Expr := #[]
      for v in vs do
        let lam ← match cur.getAppFnArgs with
          | (``Exists, #[_, l]) => pure l
          | _ => throwError "wg: fact shape"
        lams := lams.push lam
        cur := lam.beta #[v]
      let bm ← mkFreshExprSyntheticOpaqueMVar cur
      let saved ← getGoals
      wgCloseGoal bm.mvarId!
      setGoals saved
      let mut pf ← instantiateMVars bm
      for i' in [0 : vs.size] do
        let i := vs.size - 1 - i'
        pf ← mkAppOptM ``Exists.intro #[none, lams[i]!, vs[i]!, pf]
      g.assign (← mkAppOptM ``himpl_pure_top #[P.inst, q, lhs, pf])
    let pf ← instantiateMVars m
    mkLambdaFVars xs (← mkAppOptM ``holdsP_of_top #[P.inst, q, atom, pf])

partial def wgFactOf (P : WgP) : TacticM (Option Expr) := do
  let some A ← wgAbsOf P | return none
  let some Inv ← wgInvOf P | return none
  wgLem s!"fact:{P.pname}" (wgBuildFact P A Inv)

partial def wgLoOf (P : WgP) : TacticM (Option Expr) := do
  let some A ← wgAbsOf P | return none
  let some Inv ← wgInvOf P | return none
  wgLem s!"lo:{P.pname}" ((wgBuildLo P A Inv))

partial def wgConcOf (P : WgP) : TacticM (Option Expr) := do
  wgLem s!"conc:{P.pname}" (if P.pg then wgBuildConcPG P else do
    let lo ← if P.ai.isSome then wgLoOf P else pure none
    wgBuildConcGen P lo)

end

def wgBuildMap (A B : WgP) (idx : Array Nat) (rev : Bool) : TacticM Expr := do
  let nA := A.mov.size
  let F := fun (cs : Array Expr) => wgTuple (idx.map (cs[·]!))
  let hpf ← withLocalDeclsD (wgDecls (wgMovTys A) "ma") fun a =>
    withLocalDeclsD (wgDecls (wgMovTys A) "mb") fun b => withLocalDeclD `w arIntT fun w => do
      let lhs ← wgNorm (A.cLam.beta #[← wgTuple a, ← wgTuple b, w])
      let (x, y) := if rev then (b, a) else (a, b)
      let rhs ← wgNorm (B.cLam.beta #[← F x, ← F y, w])
      let m ← arGoal (← mkAppM ``HProp.himpl #[lhs, rhs])
      let _ ← arIntroLhs
      wgSubstAll
      let ok ← withMainContext do
        let t ← instantiateMVars (← (← getMainGoal).getType)
        let some (l, r) := entailHead? t | return false
        let Lc := (flatStar l #[]).filter (·.isAppOf ``HProp.hsingle)
        let (rb, _) ← arOpen r
        let Rc := (flatStar rb #[]).filter (·.isAppOf ``HProp.hsingle)
        let s ← saveState
        let r ← wgAssign Lc Rc.toList #[]
        s.restore
        return r.isSome && Lc.size == Rc.size
      unless ok do throwError "wg: map cells"
      convClose
      unless (← getUnsolvedGoals).isEmpty do throwError "wg: map open"
      mkLambdaFVars (a ++ b ++ #[w]) (← instantiateMVars m)
  let fLam ← withLocalDeclD `s A.sty fun s => do
    mkLambdaFVars #[s] (← F (← (Array.range nA).mapM (wgProj s · nA)))
  let h ← withLocalDeclD `s A.sty fun s => withLocalDeclD `s' A.sty fun s' =>
    withLocalDeclD `w arIntT fun w => do
      let ps ← (Array.range nA).mapM (wgProj s · nA)
      let ps' ← (Array.range nA).mapM (wgProj s' · nA)
      let body := hpf.beta (ps ++ ps' ++ #[w])
      let (x, y) := if rev then (s', s) else (s, s')
      let ty ← mkAppM ``HProp.himpl #[mkApp3 A.cLam s s' w, mkApp3 B.cLam (mkApp fLam x) (mkApp fLam y) w]
      unless ← isDefEq (← inferType body) ty do throwError "wg: map h"
      mkLambdaFVars #[s, s', w] (← mkExpectedTypeHint body ty)
  let thm := if rev then ``Sep.wseg_rev else ``Sep.wseg_map
  withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `n arIntT fun n =>
  withLocalDeclD `s A.sty fun s => withLocalDeclD `t A.sty fun t => do
    mkLambdaFVars #[k, n, s, t] (mkAppN (mkConst thm) #[A.inst, A.sty, B.sty, A.cLam, B.cLam, fLam, h, k, n, s, t])

def wgBuildRet (P : WgP) (j l : Nat) : TacticM Expr := do
  let nA := P.mov.size
  let tys := wgMovTys P
  withLocalDeclD `e tys[j]! fun e => do
  let cellAt := fun (a b : Array Expr) (w : Expr) => do wgNorm (P.cLam.beta #[← wgTuple a, ← wgTuple b, w])
  let hgp ← withLocalDeclsD (wgDecls tys "ra") fun a =>
    withLocalDeclsD (wgDecls tys "rb") fun b => withLocalDeclD `w arIntT fun w => do
      withLocalDeclD `hne (← mkAppM ``Ne #[a[l]!, e]) fun hne => do
        let lhs ← cellAt a b w
        let rhs ← cellAt (a.set! j e) (b.set! j e) w
        let m ← arGoal (← mkAppM ``HProp.himpl #[lhs, rhs])
        let _ ← arIntroLhs
        wgSubstAll
        convClose
        unless (← getUnsolvedGoals).isEmpty do throwError "wg: ret open"
        mkLambdaFVars (a ++ b ++ #[w, hne]) (← instantiateMVars m)
  let hcp ← withLocalDeclsD (wgDecls tys "ra") fun a =>
    withLocalDeclsD (wgDecls tys "rb") fun b => withLocalDeclD `w arIntT fun w => do
      let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``hasLoc #[a[l]!, ← cellAt a b w])
      unless ← wgAllocGoal m.mvarId! do throwError "wg: ret loc"
      mkLambdaFVars (a ++ b ++ #[w]) (← instantiateMVars m)
  let hzp ← withLocalDeclsD (wgDecls tys "ra") fun a =>
    withLocalDeclsD (wgDecls tys "rb") fun b => withLocalDeclD `w arIntT fun w => do
      let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``neLocs #[a[l]!, mkNatLit 0, ← cellAt a b w])
      setGoals [m.mvarId!]
      unless ← wgAllocGoal m.mvarId! do throwError "wg: srcne"
      unless (← getUnsolvedGoals).isEmpty do throwError "wg: ret nz"
      mkLambdaFVars (a ++ b ++ #[w]) (← instantiateMVars m)
  let fLam ← withLocalDeclD `s P.sty fun s => do
    mkLambdaFVars #[s] (← wgTuple ((← (Array.range nA).mapM (wgProj s · nA)).set! j e))
  let locLam ← withLocalDeclD `s P.sty fun s => do mkLambdaFVars #[s] (← wgProj s l nA)
  let lift := fun (pf : Expr) (extra : Bool) => withLocalDeclD `s P.sty fun s => withLocalDeclD `s' P.sty fun s' =>
    withLocalDeclD `w arIntT fun w => do
      let ps ← (Array.range nA).mapM (wgProj s · nA)
      let ps' ← (Array.range nA).mapM (wgProj s' · nA)
      if extra then
        withLocalDeclD `hne (← mkAppM ``Ne #[← wgProj s l nA, e]) fun hne => do
          mkLambdaFVars #[s, s', w, hne] (pf.beta (ps ++ ps' ++ #[w, hne]))
      else mkLambdaFVars #[s, s', w] (pf.beta (ps ++ ps' ++ #[w]))
  let hg ← lift hgp true
  let hc ← lift hcp false
  let hz ← lift hzp false
  withLocalDeclD `F (mkApp (mkConst ``HProp) P.inst) fun F => do
  withLocalDeclD `hF (← mkAppM ``safeFar #[e, F]) fun hF =>
  withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `n arIntT fun n =>
  withLocalDeclD `s P.sty fun s => withLocalDeclD `t P.sty fun t => do
    let pf ← mkAppM ``wseg_retarget #[P.cLam, fLam, locLam, e, F, hF, hc, hz, hg, k, n, s, t]
    mkLambdaFVars #[e, F, hF, k, n, s, t] pf

def wgBuildRetPrev (P : WgP) (j pv ad : Nat) : TacticM Expr := do
  let nA := P.mov.size
  let tys := wgMovTys P
  withLocalDeclD `e tys[j]! fun e => do
  let cellAt := fun (a b : Array Expr) (w : Expr) => do wgNorm (P.cLam.beta #[← wgTuple a, ← wgTuple b, w])
  let hgp ← withLocalDeclsD (wgDecls tys "ra") fun a =>
    withLocalDeclsD (wgDecls tys "rb") fun b => withLocalDeclD `w arIntT fun w => do
      withLocalDeclD `hne (← mkAppM ``Ne #[a[pv]!, e]) fun hne => do
        let lhs ← cellAt a b w
        let rhs ← cellAt (a.set! j e) (b.set! j e) w
        let m ← arGoal (← mkAppM ``HProp.himpl #[lhs, rhs])
        let _ ← arIntroLhs
        wgSubstAll
        convClose
        unless (← getUnsolvedGoals).isEmpty do throwError "wg: retp open"
        mkLambdaFVars (a ++ b ++ #[w, hne]) (← instantiateMVars m)
  let hcp ← withLocalDeclsD (wgDecls tys "ra") fun a =>
    withLocalDeclsD (wgDecls tys "rb") fun b => withLocalDeclD `w arIntT fun w => do
      let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``hasLoc #[a[ad]!, ← cellAt a b w])
      unless ← wgAllocGoal m.mvarId! do throwError "wg: retp loc"
      mkLambdaFVars (a ++ b ++ #[w]) (← instantiateMVars m)
  let hzp ← withLocalDeclsD (wgDecls tys "ra") fun a =>
    withLocalDeclsD (wgDecls tys "rb") fun b => withLocalDeclD `w arIntT fun w => do
      let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``neLocs #[a[ad]!, mkNatLit 0, ← cellAt a b w])
      setGoals [m.mvarId!]
      unless ← wgAllocGoal m.mvarId! do throwError "wg: srcne"
      unless (← getUnsolvedGoals).isEmpty do throwError "wg: retp nz"
      mkLambdaFVars (a ++ b ++ #[w]) (← instantiateMVars m)
  let hpp ← withLocalDeclsD (wgDecls tys "ra") fun a =>
    withLocalDeclsD (wgDecls tys "rb") fun b => withLocalDeclD `w arIntT fun w => do
      let q ← mkAppM ``Eq #[b[pv]!, a[ad]!]
      let cell ← cellAt a b w
      let top ← mkAppM ``HProp.hstar #[← mkAppOptM ``HProp.hpure #[P.inst, q], mkApp (mkConst ``HProp.htop) P.inst]
      let m ← arGoal (← mkAppM ``HProp.himpl #[cell, top])
      for g in ← wgSplitDisj do
        setGoals [g]
        withMainContext do
          let g ← getMainGoal
          let some (lhs, _) := entailHead? (← instantiateMVars (← g.getType)) | throwError "wg: retp prev"
          g.assign (← mkAppOptM ``himpl_pure_top #[P.inst, q, lhs, ← wgSide q])
      let pf ← instantiateMVars m
      mkLambdaFVars (a ++ b ++ #[w]) (← mkAppOptM ``holdsP_of_top #[P.inst, q, cell, pf])
  let fLam ← withLocalDeclD `s P.sty fun s => do
    mkLambdaFVars #[s] (← wgTuple ((← (Array.range nA).mapM (wgProj s · nA)).set! j e))
  let adrLam ← withLocalDeclD `s P.sty fun s => do mkLambdaFVars #[s] (← wgProj s ad nA)
  let prvLam ← withLocalDeclD `s P.sty fun s => do mkLambdaFVars #[s] (← wgProj s pv nA)
  let lift := fun (pf : Expr) (extra : Bool) => withLocalDeclD `s P.sty fun s => withLocalDeclD `s' P.sty fun s' =>
    withLocalDeclD `w arIntT fun w => do
      let ps ← (Array.range nA).mapM (wgProj s · nA)
      let ps' ← (Array.range nA).mapM (wgProj s' · nA)
      if extra then
        withLocalDeclD `hne (← mkAppM ``Ne #[← wgProj s pv nA, e]) fun hne => do
          mkLambdaFVars #[s, s', w, hne] (pf.beta (ps ++ ps' ++ #[w, hne]))
      else mkLambdaFVars #[s, s', w] (pf.beta (ps ++ ps' ++ #[w]))
  let hg ← lift hgp true
  let hc ← lift hcp false
  let hz ← lift hzp false
  let hp ← lift hpp false
  withLocalDeclD `F (mkApp (mkConst ``HProp) P.inst) fun F => do
  withLocalDeclD `hF (← mkAppM ``safeFar #[e, F]) fun hF =>
  withLocalDeclD `k (mkConst ``Nat) fun k => do
    let pf ← mkAppM ``wseg_retarget_prev #[P.cLam, fLam, adrLam, prvLam, e, F, hF, hc, hz, hp, hg, k]
    mkLambdaFVars #[e, F, hF, k] pf

def wgRetPrevOf (P : WgP) (j pv ad : Nat) : TacticM (Option Expr) :=
  wgLem s!"retp:{P.cLam.hash}:{j}:{pv}:{ad}" (wgBuildRetPrev P j pv ad)

def wgBuildBk (P : WgP) (pv ad : Nat) : TacticM Expr := do
  let nA := P.mov.size
  let tys := wgMovTys P
  let cellAt := fun (a b : Array Expr) (w : Expr) => do wgNorm (P.cLam.beta #[← wgTuple a, ← wgTuple b, w])
  let hcp ← withLocalDeclsD (wgDecls tys "ra") fun a =>
    withLocalDeclsD (wgDecls tys "rb") fun b => withLocalDeclD `w arIntT fun w => do
      let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``hasLoc #[a[ad]!, ← cellAt a b w])
      unless ← wgAllocGoal m.mvarId! do throwError "wg: bk loc"
      mkLambdaFVars (a ++ b ++ #[w]) (← instantiateMVars m)
  let hpp ← withLocalDeclsD (wgDecls tys "ra") fun a =>
    withLocalDeclsD (wgDecls tys "rb") fun b => withLocalDeclD `w arIntT fun w => do
      let q ← mkAppM ``Eq #[b[pv]!, a[ad]!]
      let cell ← cellAt a b w
      let top ← mkAppM ``HProp.hstar #[← mkAppOptM ``HProp.hpure #[P.inst, q], mkApp (mkConst ``HProp.htop) P.inst]
      let m ← arGoal (← mkAppM ``HProp.himpl #[cell, top])
      for g in ← wgSplitDisj do
        setGoals [g]
        withMainContext do
          let g ← getMainGoal
          let some (lhs, _) := entailHead? (← instantiateMVars (← g.getType)) | throwError "wg: bk prev"
          g.assign (← mkAppOptM ``himpl_pure_top #[P.inst, q, lhs, ← wgSide q])
      let pf ← instantiateMVars m
      mkLambdaFVars (a ++ b ++ #[w]) (← mkAppOptM ``holdsP_of_top #[P.inst, q, cell, pf])
  let adrLam ← withLocalDeclD `s P.sty fun s => do mkLambdaFVars #[s] (← wgProj s ad nA)
  let prvLam ← withLocalDeclD `s P.sty fun s => do mkLambdaFVars #[s] (← wgProj s pv nA)
  let lift := fun (pf : Expr) => withLocalDeclD `s P.sty fun s => withLocalDeclD `s' P.sty fun s' =>
    withLocalDeclD `w arIntT fun w => do
      let ps ← (Array.range nA).mapM (wgProj s · nA)
      let ps' ← (Array.range nA).mapM (wgProj s' · nA)
      mkLambdaFVars #[s, s', w] (pf.beta (ps ++ ps' ++ #[w]))
  let hc ← lift hcp
  let hp ← lift hpp
  mkAppM ``wseg_bk_zero #[P.cLam, adrLam, prvLam, hc, hp]

def wgBkOf (P : WgP) (pv ad : Nat) : TacticM (Option Expr) :=
  wgLem s!"bk:{P.cLam.hash}:{pv}:{ad}" (wgBuildBk P pv ad)

def wgRetOf (P : WgP) (j l : Nat) : TacticM (Option Expr) :=
  wgLem s!"ret:{P.cLam.hash}:{j}:{l}" (wgBuildRet P j l)

def wgBuildHc (P : WgP) (l : Nat) : TacticM Expr := do
  let nA := P.mov.size
  let tys := wgMovTys P
  let hcp ← withLocalDeclsD (wgDecls tys "ra") fun a =>
    withLocalDeclsD (wgDecls tys "rb") fun b => withLocalDeclD `w arIntT fun w => do
      let cell ← wgNorm (P.cLam.beta #[← wgTuple a, ← wgTuple b, w])
      let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``hasLoc #[a[l]!, cell])
      unless ← wgAllocGoal m.mvarId! do throwError "wg: hc"
      mkLambdaFVars (a ++ b ++ #[w]) (← instantiateMVars m)
  withLocalDeclD `s P.sty fun s => withLocalDeclD `s' P.sty fun s' =>
    withLocalDeclD `w arIntT fun w => do
      let ps ← (Array.range nA).mapM (wgProj s · nA)
      let ps' ← (Array.range nA).mapM (wgProj s' · nA)
      mkLambdaFVars #[s, s', w] (hcp.beta (ps ++ ps' ++ #[w]))

def wgHcOf (P : WgP) (l : Nat) : TacticM (Option Expr) :=
  wgLem s!"hc:{P.cLam.hash}:{l}" (wgBuildHc P l)

def wgSegEnd (e a : Expr) : TacticM (Option (WgP × Nat × Expr)) := do
  let a ← instantiateMVars a
  if wgIsSeg a then
    for P in (← wgPCache.get).filterMap (·.2) do
      unless P.cLam == a.getAppArgs[2]! do continue
      let nA := P.mov.size
      for (_, l) in P.gloc do
        let sc ← wgComps a.getAppArgs[5]! nA
        let tc ← wgComps a.getAppArgs[6]! nA
        if sc[l]! == e && tc[l]! != e then return some (P, l, tc[l]!)
    return none
  let some q := a.getAppFn.constName? | return none
  let some Q ← wgPOf q | return none
  unless a.getAppNumArgs == Q.tys.size && Q.tailLam.isNone do return none
  let xs := a.getAppArgs
  for (_, l) in Q.gloc do
    if xs[Q.mov[l]!]! != e then continue
    let (f, c) := Q.endSpec[l]!
    let b := match f, c with
      | some f, _ => some xs[f]!
      | none, some c => some c
      | none, none => none
    if let some b := b then
      if b != e then return some (Q, l, b)
  return none

partial def wgLocAtom (e F : Expr) : TacticM (Option Expr) := do
  let some (Q, l, b) ← wgSegEnd e F | return none
  if wgIsSeg F then
    let fa := F.getAppArgs
    let pos ← mkAppM ``LE.le #[mkNatLit 1, fa[3]!]
    if let some hk ← (try some <$> wgSide pos catch _ => pure none) then
      let some hc ← wgHcOf Q l | return none
      let locLam ← withLocalDeclD `s Q.sty fun s => do mkLambdaFVars #[s] (← wgProj s l Q.mov.size)
      let pf ← mkAppM ``hasLoc_wseg_pos #[Q.cLam, locLam, hc, fa[3]!, fa[4]!, fa[5]!, fa[6]!, hk]
      return some (← mkExpectedTypeHint pf (← mkAppM ``hasLoc #[e, F]))
  let ne ← mkAppM ``Ne #[e, b]
  let some hne ← (try some <$> wgSide ne catch _ => pure none) | return none
  let some hc ← wgHcOf Q l | return none
  if wgIsSeg F then
    let fa := F.getAppArgs
    let locLam ← withLocalDeclD `s Q.sty fun s => do mkLambdaFVars #[s] (← wgProj s l Q.mov.size)
    let pf ← mkAppM ``hasLoc_wseg_ne #[Q.cLam, locLam, hc, fa[3]!, fa[4]!, fa[5]!, fa[6]!, hne]
    return some (← mkExpectedTypeHint pf (← mkAppM ``hasLoc #[e, F]))
  let some A ← wgAbsOf Q | return none
  let xs := F.getAppArgs
  let tgt ← instantiateMVars ((← inferType (mkAppN A xs)).appArg!)
  let some p ← wgAlloc e tgt | return none
  return some (← mkAppM ``hasLoc_mono #[mkAppN A xs, p])

initialize wgLocHook.set wgLocAtom

partial def wgSafeFar (e F : Expr) (seen : Array Expr := #[]) : TacticM (Option Expr) := do
  let e ← instantiateMVars e
  if let some v ← getNatValue? e then
    if v == 0 then return some (← mkAppOptM ``safeFar_nil #[none, e, F, ← mkEqRefl e])
  let direct := (flatStar F #[]).any fun a =>
    a.isAppOf ``HProp.hsingle && a.getAppNumArgs ≥ 2 && a.getAppArgs[a.getAppNumArgs - 2]! == e
  if direct then
    if let some p ← wgAlloc e F then
      return some (← mkAppOptM ``safeFar_loc #[none, e, F, p])
  if seen.contains e then return none
  for a in flatStar F #[] do
    let some (_, _, b) ← wgSegEnd e a | continue
    if (← (try some <$> wgSide (← mkAppM ``Ne #[e, b]) catch _ => pure none)).isSome then
      if let some p ← wgAlloc e F then
        return some (← mkAppOptM ``safeFar_loc #[none, e, F, p])
    let s ← saveState
    let r ← (try (do
        let h1 ← withLocalDeclD `hne (← mkAppM ``Ne #[e, b]) fun hne => do
          let some p ← wgAlloc e F | throwError "wg: far loc"
          mkLambdaFVars #[hne] p
        let some h2p ← wgSafeFar b F (seen.push e) | throwError "wg: far step"
        let h2 ← withLocalDeclD `heq (← mkAppM ``Eq #[e, b]) fun heq => mkLambdaFVars #[heq] h2p
        pure (some (← mkAppM ``safeFar_step #[h1, h2]))) catch _ => pure none)
    if r.isSome then return r
    s.restore
  let z ← mkAppM ``Eq #[e, mkNatLit 0]
  if let some hz ← (try some <$> wgSide z catch _ => pure none) then
    return some (← mkAppOptM ``safeFar_nil #[none, e, F, hz])
  return none

initialize wgFarHook.set (fun e F => wgSafeFar e F)

def wgRetargetPrev (P : WgP) (a : Expr) (j : Nat) (e : Expr) : TacticM Expr := do
  let some (_, pv, ad) := P.gprev.find? (·.1 == j) | throwError "wg: no guard"
  let some core ← wgRetPrevOf P j pv ad | throwError "wg: retp lemma"
  let nA := P.mov.size
  let (lem, others, na) ← withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (lhs, _) := entailHead? t | throwError "wg: goal"
    let inst := t.getAppArgs[0]!
    let L := flatStar lhs #[]
    let some i := L.idxOf? a | throwError "wg: ret atom"
    let others := L.eraseIdx! i
    let F := starOf inst others.toList
    let some hF ← (wgSafeFar e F) | throwError "wg: ret safe"
    let aa := a.getAppArgs
    let sc ← wgComps aa[5]! nA
    let h0 ← wgSide (← mkAppM ``Ne #[sc[pv]!, e])
    let s' ← wgTuple (sc.set! j e)
    let t' ← wgTuple ((← wgComps aa[6]! nA).set! j e)
    let na := mkAppN a.getAppFn #[aa[0]!, aa[1]!, aa[2]!, aa[3]!, aa[4]!, s', t']
    let ty ← mkAppM ``HProp.himpl #[← mkAppM ``HProp.hstar #[a, F], ← mkAppM ``HProp.hstar #[na, F]]
    let pf := mkAppN core #[e, F, hF, aa[3]!, aa[4]!, aa[5]!, aa[6]!, h0]
    pure (← mkExpectedTypeHint pf ty, others, na)
  let _ ← arRwLhs (a :: others.toList) lem
  return na

def wgRetarget (P : WgP) (a : Expr) (j : Nat) (e : Expr) : TacticM Expr := do
  let some (_, l) := P.gloc.find? (·.1 == j) | wgRetargetPrev P a j e
  let some core ← wgRetOf P j l | throwError "wg: ret lemma"
  let nA := P.mov.size
  let (lem, others, na) ← withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (lhs, _) := entailHead? t | throwError "wg: goal"
    let inst := t.getAppArgs[0]!
    let L := flatStar lhs #[]
    let some i := L.idxOf? a | throwError "wg: ret atom"
    let others := L.eraseIdx! i
    let F := starOf inst others.toList
    let some hF ← (wgSafeFar e F) | throwError "wg: ret safe"
    let aa := a.getAppArgs
    let s' ← wgTuple ((← wgComps aa[5]! nA).set! j e)
    let t' ← wgTuple ((← wgComps aa[6]! nA).set! j e)
    let na := mkAppN a.getAppFn #[aa[0]!, aa[1]!, aa[2]!, aa[3]!, aa[4]!, s', t']
    let ty ← mkAppM ``HProp.himpl #[← mkAppM ``HProp.hstar #[a, F], ← mkAppM ``HProp.hstar #[na, F]]
    let pf := mkAppN core #[e, F, hF, aa[3]!, aa[4]!, aa[5]!, aa[6]!]
    pure (← mkExpectedTypeHint pf ty, others, na)
  let _ ← arRwLhs (a :: others.toList) lem
  return na

partial def wgIdxs (nA nB : Nat) : List (Array Nat) :=
  if nB == 0 then [#[]] else
  (wgIdxs nA (nB - 1)).flatMap fun pre =>
    ((List.range nA).filter (fun i => !pre.contains i)).map fun i => pre.push i

partial def wgCellFields (e : Expr) (acc : Array (Nat × Option Nat)) : Array (Nat × Option Nat) :=
  if e.isAppOfArity ``HProp.hsingle 3 then
    let a := e.appFn!.appArg!
    let v := e.appArg!
    let off := if a.isAppOfArity ``HAdd.hAdd 6 then (a.appArg!.nat?).getD 0 else 0
    let lit := if v.isAppOfArity ``Nat.cast 3 then v.appArg!.nat? else v.nat?
    acc.push (off, lit)
  else match e with
    | .app f a => wgCellFields a (wgCellFields f acc)
    | .lam _ t b _ => wgCellFields b (wgCellFields t acc)
    | .forallE _ t b _ => wgCellFields b (wgCellFields t acc)
    | .letE _ t v b _ => wgCellFields b (wgCellFields v (wgCellFields t acc))
    | .mdata _ b => wgCellFields b acc
    | _ => acc

def wgCellSig (c : Expr) : Array (Nat × Option Nat) :=
  (wgCellFields c #[]).qsort (fun x y => x.1 < y.1 || (x.1 == y.1 && x.2.getD 0 < y.2.getD 0))

def wgMapOf (A B : WgP) : TacticM (Option (Array Nat × Bool × Option Expr)) := do
  if A.cLam == B.cLam then return some (Array.range A.mov.size, false, none)
  let key := (A.pname, B.pname)
  if let some r := (← wgMCache.get).findSome? (fun e => if e.1 == key then some e.2 else none) then
    match r with
    | some (_, _, some e) =>
      if ← wgValid e then return r
      wgMCache.modify (·.filter (·.1 != key))
    | _ => return r
  let mut res : Option (Array Nat × Bool × Option Expr) := none
  if B.mov.size ≤ A.mov.size && wgCellSig A.cLam == wgCellSig B.cLam then
    for idx in wgIdxs A.mov.size B.mov.size do
      if res.isSome then break
      for rev in [false, true] do
        let saved ← getGoals
        let st ← saveState
        let r ← try withLCtx {} {} (some <$> (wgBuildMap A B idx rev)) catch _ => do st.restore; pure none
        setGoals saved
        if let some lem := r then
          res := some (idx, rev, some lem)
          break
  wgMCache.modify (·.push (key, res))
  return res

def wgMapInst (B : WgP) (mp : Array Nat × Bool × Option Expr) (atom : Expr) :
    TacticM (Expr × Expr) := do
  let some lem := mp.2.2 | return (atom, default)
  withMainContext do
    let aa := atom.getAppArgs
    let pf := mkAppN lem #[aa[3]!, aa[4]!, aa[5]!, aa[6]!]
    let ty ← instantiateMVars (← inferType pf)
    let some (_, r) := entailHead? ty | throwError "wg: map inst"
    let ra := r.getAppArgs
    let s ← wgTuple (← wgComps (← wgNorm ra[5]!) B.mov.size)
    let t ← wgTuple (← wgComps (← wgNorm ra[6]!) B.mov.size)
    let out := wgSeg B aa[3]! aa[4]! s t
    return (out, ← mkExpectedTypeHint pf (← mkAppM ``HProp.himpl #[atom, out]))

partial def wgRepl (e A B pf : Expr) : MetaM (Option (Expr × Expr)) := do
  if e == A then return some (B, pf)
  match e.getAppFnArgs with
  | (``HProp.hstar, #[inst, a, b]) =>
    if let some (a', pa) ← wgRepl a A B pf then
      return some (mkApp3 (mkConst ``HProp.hstar) inst a' b,
        mkAppN (mkConst ``HProp.himpl_frame_l) #[inst, a', a, b, pa])
    if let some (b', pb) ← wgRepl b A B pf then
      return some (mkApp3 (mkConst ``HProp.hstar) inst a b',
        mkAppN (mkConst ``HProp.himpl_frame_r) #[inst, a, b', b, pb])
    return none
  | _ => return none

def wgRwRhs (A B pf : Expr) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (lhs, rhs) := entailHead? t | throwError "wg: goal"
  let some (rhs', p) ← wgRepl rhs A B pf | throwError "wg: rhs atom"
  let inst := t.getAppArgs[0]!
  let m ← mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``HProp.himpl) inst lhs rhs')
  g.assign (mkAppN (mkConst ``HProp.himpl_trans) #[inst, lhs, rhs', rhs, m, p])
  replaceMainGoal [m.mvarId!]

structure WgPc where
  cell : Bool
  pred : Name := .anonymous
  atom : Expr := default
  idx : Option Nat := none
  st : Array Expr := #[]
  en : Array Expr := #[]
  len : Expr := default
  lo : Int := 0
  phs : Array Expr := #[]
  req : Option Expr := none
  deriving Inhabited

structure WgPlan where
  car : WgP
  lp : Array WgPc
  rp : Array WgPc
  rl : Array Expr
  deriving Inhabited

def wgLhsPieces {α : Type} [Inhabited α] (P : WgP) (L : Array Expr)
    (k : Array WgPc → Array Expr → TacticM α) : TacticM α := do
  let mut segs : Array (Expr × WgP × (Array Nat × Bool × Option Expr)) := #[]
  for x in L do
    let some q := x.getAppFn.constName? | continue
    let some Q ← wgPOf q | continue
    unless x.getAppNumArgs == Q.tys.size do continue
    let some mp ← wgMapOf Q P | continue
    segs := segs.push (x, Q, mp)
  let tys := segs.foldl (fun acc (_, Q, _) => acc ++ #[mkConst ``Nat] ++ wgMissTys Q) #[]
  withLocalDeclsD (wgDecls tys "wph") fun phs => do
    let mut out : Array WgPc := #[]
    let mut hyps : Array Expr := #[]
    let mut tails : Array Expr := #[]
    let mut off := 0
    for (x, Q, (idx, rev, _)) in segs do
      let nm := (wgMissTys Q).size
      let kp := phs[off]!
      let miss := phs.extract (off + 1) (off + 1 + nm)
      let ph := phs.extract off (off + 1 + nm)
      off := off + 1 + nm
      let xs := x.getAppArgs
      let sQ := Q.mov.map (xs[·]!)
      let eQ := wgEnC Q xs miss
      let wi ← match Q.ai with
        | some i => pure xs[i]!
        | none => arCast kp
      let w ← if Q.unitW then pure wi else arCast kp
      hyps := hyps.push (← wgCond Q kp)
      hyps := hyps.push (← wgNorm (Q.invLam.beta #[kp, ← wgTuple sQ, ← wgTuple eQ, wi]))
      tails := tails ++ wgTail Q xs miss
      let (a, b) := if rev then (eQ, sQ) else (sQ, eQ)
      out := out.push { cell := false, pred := Q.pname, atom := x, st := idx.map (a[·]!),
                        en := idx.map (b[·]!), len := w, lo := Q.kmin, phs := ph }
    withLocalDeclsD (wgDecls hyps "wh") fun _ => k out tails

def wgWalkL (P : WgP) (Lc : Array Expr) (segs : Array WgPc) (s0 : Array Expr) :
    MetaM (Array WgPc) := do
  let mut cur := s0
  let mut usedS : Array Nat := #[]
  let mut usedC : Array Nat := #[]
  let mut out : Array WgPc := #[]
  let one ← arIntLit 1
  for _ in [0 : segs.size + Lc.size + 1] do
    let mut nxt : Option (Nat × WgPc) := none
    for i in [0 : segs.size] do
      if usedS.contains i then continue
      if ← wgUnifyStC P.cst segs[i]!.st cur then
        nxt := some (i, segs[i]!)
        break
    match nxt with
    | some (i, pc) =>
      usedS := usedS.push i
      out := out.push pc
      cur := pc.en
    | none =>
      let some (S, us, js) ← wgCellAt P Lc usedC (some cur) false | break
      let nx ← wgCellNext P S us
      usedC := usedC ++ js
      out := out.push { cell := true, st := S, en := nx, len := one, lo := 1 }
      cur := nx
  return out

def wgRhsSt (P : WgP) (mp : Array Nat × Bool × Option Expr) (sQ eQ : Array Expr) :
    MetaM (Array Expr × Array Expr) := do
  let inv := fun (v : Array Expr) => do
    let mut out ← (wgMovTys P).mapM (fun ty => mkFreshExprMVar (some ty))
    for j in [0 : mp.1.size] do out := out.set! mp.1[j]! v[j]!
    return out
  if mp.2.1 then return (← inv eQ, ← inv sQ) else return (← inv sQ, ← inv eQ)

def wgMerged (ws : Array Expr) : MetaM Bool := do
  let mut seen : Array Expr := #[]
  for w in ws do
    let v ← instantiateMVars w
    if v.isMVar then
      if seen.contains v then return true
      seen := seen.push v
  return false

def wgBack (s : Tactic.SavedState) : TacticM Unit := do
  let env ← getEnv
  s.restore
  setEnv env

initialize wgWalkBudget : IO.Ref Nat ← IO.mkRef 0

partial def wgWalkR (P : WgP) (R ws : Array Expr) (cur tgt : Array Expr) (usedR : Array Nat)
    (acc : Array WgPc) (fuel : Nat) (okEnd : Array WgPc → TacticM Bool)
    (hints : Array (Array Expr) := #[]) : TacticM (Option (Array WgPc)) := do
  let left ← wgWalkBudget.get
  if left == 0 || (← pastGlobal) then return none
  wgWalkBudget.set (left - 1)
  let Rc := R.mapIdx fun i e => if usedR.contains i then mkConst ``True else e
  let one ← arIntLit 1
  for pass in [0 : (if fuel == 0 then 0 else 2)] do
    for j in [0 : R.size] do
      if usedR.contains j then continue
      let r := R[j]!
      if r.isAppOf ``HProp.hsingle then
        let s ← saveState
        if let some (S, us, js) ← wgCellAt P Rc #[] (some cur) false (some (j, pass == 0)) then
          unless ← wgMerged ws do
            let nx ← wgCellNext P S us
            let pc : WgPc := { cell := true, en := nx, len := one, lo := 1 }
            if let some res ← wgWalkR P R ws nx tgt (usedR ++ js) (acc.push pc) (fuel - 1) okEnd hints then
              return some res
        wgBack s
        continue
      let some q := r.getAppFn.constName? | continue
      let some Q ← wgPOf q | continue
      unless r.getAppNumArgs == Q.tys.size do continue
      let some mp ← wgMapOf P Q | continue
      let xs ← r.getAppArgs.mapM instantiateMVars
      let sQ := Q.mov.map (xs[·]!)
      if !mp.2.1 then
        let curI ← cur.mapM instantiateMVars
        if (Array.range mp.1.size).any (fun j => !P.cst.contains mp.1[j]! &&
            addrApart sQ[j]! curI[mp.1[j]!]!) then continue
      let s ← saveState
      let miss ← (wgMissTys Q).mapM fun ty => mkFreshExprMVar (some ty)
      let eQ := wgEnC Q xs miss
      let (st, en) ← wgRhsSt P mp sQ eQ
      let mut exact := true
      for i in mp.1 do
        unless (← instantiateMVars st[i]!) == (← instantiateMVars cur[i]!) do exact := false
      if (pass == 0) != exact then
        wgBack s
        continue
      if (← wgUnifyStC P.cst st cur) && !(← wgMerged ws) then
        let enI ← en.mapM instantiateMVars
        let enOpen ← (Array.range R.size).anyM fun j' => do
          if j' == j || usedR.contains j' then return false
          let o ← instantiateMVars R[j']!
          return enI.any fun e => e.isMVar && (o.find? (· == e)).isSome
        let curI ← cur.mapM instantiateMVars
        let after := match hints.idxOf? curI with
          | some i => hints.extract (i + 1) hints.size
          | none => hints.filter (· != curI)
        let alts : Array (Option (Array Expr)) :=
          if enOpen then (after.map some).push none else #[none]
        for h? in alts do
          let s2 ← saveState
          let okh ← match h? with
            | some h => wgUnifyStC P.cst en h
            | none => pure true
          if okh then
            let len ← match Q.ai with
              | some i => if Q.unitW then pure xs[i]! else mkFreshExprMVar (some arIntT)
              | none => mkFreshExprMVar (some arIntT)
            let pc : WgPc := { cell := false, pred := q, idx := some j, atom := r, en := en, len := len,
                               lo := Q.kmin, req := Q.profLam }
            let tl := (wgTail Q xs miss).filter (·.isAppOf ``HProp.hsingle)
            let nxt ← if tl.isEmpty || (mp.2.1 && mp.2.2.isSome) then pure (some (en, #[pc])) else do
              match ← wgCellAt P tl #[] (some en) false (some (0, false)) with
              | some (S, us, js) =>
                if js.size == tl.size then
                  let nx ← wgCellNext P S us
                  pure (some (nx, #[pc, { cell := true, en := nx, len := one, lo := 1 }]))
                else pure none
              | none => pure (if mp.2.2.isSome then some (en, #[pc]) else none)
            if let some (nx, pcs) := nxt then
              if let some res ← wgWalkR P R ws nx tgt (usedR.push j) (acc ++ pcs) (fuel - 1) okEnd hints then
                return some res
          wgBack s2
      wgBack s
  if !acc.isEmpty then
    let s ← saveState
    if ← wgUnifyStA P.cst cur tgt then
      if ← okEnd acc then return some acc
    wgBack s
  return none

def wgTrim (l r : Array WgPc) : Array WgPc × Array WgPc := Id.run do
  let mut l := l
  let mut r := r
  while l.size ≥ 1 && r.size ≥ 1 && l.back!.cell && r.back!.cell do
    l := l.pop
    r := r.pop
  return (l, r)

def wgRelLink (P : WgP) (cells : Array WgPc) : TacticM Bool := do
  for pc in cells do
    for (j, sg, b, isEq) in P.rels do
      unless isEq do continue
      let some s := pc.st[j]? | continue
      let some e := pc.en[j]? | continue
      let s ← instantiateMVars s
      let e ← instantiateMVars e
      if s.hasExprMVar then continue
      let bk ← arIntLit b
      let v ← if sg == 1 then arSub s bk else arAdd s bk
      if e.isMVar then
        let _ ← isDefEq e v
      else if !e.hasExprMVar then
        unless ← withMainContext (wgEqOk v e) do return false
  return true

def wgPlanFor (P : WgP) (onPlan : WgPlan → TacticM Bool) : TacticM Bool := withMainContext do
  let stop ← IO.mkRef false
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (lhs, rhs) := entailHead? t | return false
  let L := (flatStar lhs #[]).filter (!·.isAppOf ``HProp.hpure)
  wgLhsPieces P L fun segs tails => do
    let Lc := L ++ tails
    let (body, ws) ← arOpen rhs
    let R := flatStar body #[]
    let rpures := pureProps body #[]
    let rAll ← do
      let sv ← saveState
      let mut out : Array (Array Expr × Array Expr) := #[]
      for r in R do
        let some q := r.getAppFn.constName? | continue
        let some Q ← wgPOf q | continue
        unless r.getAppNumArgs == Q.tys.size do continue
        let some mp ← wgMapOf P Q | continue
        let xs ← r.getAppArgs.mapM instantiateMVars
        let miss ← (wgMissTys Q).mapM fun ty => mkFreshExprMVar (some ty)
        let (st, en) ← wgRhsSt P mp (Q.mov.map (xs[·]!)) (wgEnC Q xs miss)
        out := out.push (← st.mapM instantiateMVars, ← en.mapM instantiateMVars)
      wgBack sv
      pure out
    let rSE := if R.any (·.isAppOf ``HProp.hsingle) then none else some rAll
    let rLocs : Option (Array Expr) :=
      let cs := rAll.foldl (fun acc (st, _) =>
        acc ++ ((Array.range st.size).filter (!P.cst.contains ·)).map (st[·]!)) #[]
      let cells := (R.filter (·.isAppOfArity ``HProp.hsingle 3)).map (·.appFn!.appArg!)
      if cs.any (·.hasExprMVar) then none else some (cs ++ cells)
    let mut starts : Array (Array Expr) := segs.map (·.st)
    for x in Lc do
      if x.isAppOf ``HProp.hsingle then
        if let some cs := rLocs then
          unless cs.contains x.appFn!.appArg! do continue
        let s ← saveState
        if let some (S, _, _) ← (wgCellAt P (#[x] ++ Lc.erase x) #[] none false (some (0, false))) then
          let S ← S.mapIdxM fun i e => do
            let e ← instantiateMVars e
            return if (P.cst.contains i || P.rels.any (·.1 == i)) && e.isMVar then default else e
          if !S.any (·.hasExprMVar) && !starts.any (· == S) then starts := starts.push S
        wgBack s
    let tys := wgMovTys P
    let open0 := fun (s0 : Array Expr) => s0.mapIdxM fun i e =>
      if (P.cst.contains i || P.rels.any (·.1 == i)) && e == default then mkFreshExprMVar (some tys[i]!) else pure e
    let fits := fun (a b : Array Expr) => do
      if a.size != b.size then return false
      for i in [0 : a.size] do
        if P.cst.contains i then continue
        let x ← instantiateMVars a[i]!
        let y ← instantiateMVars b[i]!
        unless x.hasExprMVar || y.hasExprMVar || x == y || x == default || y == default do return false
      return true
    let mut sized : Array (Nat × Array Expr) := #[]
    for s0 in starts do
      if let some se := rSE then
        unless ← se.anyM (fun (st, _) => fits st s0) do continue
      if let some cs := rLocs then
        unless (Array.range s0.size).any (fun i => !P.cst.contains i && cs.contains s0[i]!) do continue
      let s1 ← saveState
      let n := (← (wgWalkL P Lc segs (← open0 s0))).size
      s1.restore
      sized := sized.push (n, s0)
    starts := (sized.qsort (fun a b => a.1 > b.1)).map (·.2)
    for s00 in starts do
      if ← pastGlobal then return false
      if let some se := rSE then
        unless ← se.anyM (fun (st, _) => fits st s00) do continue
      let s1 ← saveState
      let s0 ← open0 s00
      let lp ← (wgWalkL P Lc segs s0)
      for j' in [0 : lp.size] do
        let j := lp.size - j'
        let lpj := lp.extract 0 j
        if let some se := rSE then
          unless ← se.anyM (fun (_, en) => fits en lpj[j - 1]!.en) do continue
        let s2 ← saveState
        let found ← IO.mkRef (#[] : Array WgPlan)
        let okEnd := fun (rpc : Array WgPc) => do
          let (l, r) := wgTrim lpj rpc
          if l.isEmpty || r.isEmpty then return false
          unless ← wgUnifyStA P.cst l.back!.en r.back!.en do return false
          let mut tc : Array (Option Expr) := Array.replicate P.mov.size none
          for j in P.cst do
            for pc in r.reverse ++ l.reverse do
              if pc.cell then continue
              let v ← instantiateMVars pc.en[j]!
              if !v.hasExprMVar then
                tc := tc.set! j (some v)
                break
          for pc in l ++ r do
            unless pc.cell do continue
            for j in P.cst do
              for v in [pc.st[j]?, pc.en[j]?] do
                let some v := v | continue
                let v ← instantiateMVars v
                if v.isMVar then
                  if let some e := tc[j]! then let _ ← isDefEq v e
          for j in P.cst do
            let vs ← (r.filter (!·.cell)).mapM fun pc => instantiateMVars pc.en[j]!
            if vs.any (· != vs[0]!) then return false
          unless ← wgRelLink P (l.filter (·.cell)) do return false
          for pc in l do
            unless pc.cell do continue
            for (j, lc) in P.gloc do
              if (← instantiateMVars pc.st[lc]!) == (← instantiateMVars pc.st[j]!) then return false
          let nontriv := l.size ≥ 2 || r.size ≥ 2 ||
            (!l[0]!.cell && !r[0]!.cell && l[0]!.pred != r[0]!.pred) || l[0]!.cell != r[0]!.cell
          if !nontriv then return false
          let n0 ← arSum (l.map (·.len)).toList
          let aps := r.map fun pc => ({ cell := pc.cell, len := pc.len, lo := pc.lo } : ArPiece)
          let reqs := r.filterMap fun pc => pc.req.map (·.beta #[pc.len])
          if (← arSolve n0 aps (rpures ++ reqs)).isNone then return false
          let rl ← r.mapM fun pc => instantiateMVars pc.len
          let r ← r.mapM fun pc => do return { pc with en := ← pc.en.mapM instantiateMVars }
          let l ← l.mapM fun pc => do
            return { pc with st := ← pc.st.mapM instantiateMVars, en := ← pc.en.mapM instantiateMVars }
          let bad := rl.any (·.hasExprMVar) ||
            l.any (fun pc => pc.cell && (pc.st ++ pc.en).any (·.hasExprMVar))
          unless bad do
            let pl : WgPlan := { car := P, lp := l, rp := r, rl := rl }
            found.modify (·.push pl)
            if ← (onPlan pl) then
              stop.set true
              return true
          pastGlobal
        wgWalkBudget.set ((R.size + 1) * (R.size + 1))
        let hints ← lpj.mapM fun pc => pc.en.mapM instantiateMVars
        let hints := hints.filter fun h => !h.any (·.hasExprMVar)
        let _ ← (wgWalkR P R ws s0 lpj[j - 1]!.en #[] #[] (R.size + 2) okEnd hints)
        if ← stop.get then return true
        wgBack s2
      wgBack s1
    return false

def wgToNat (l : Expr) : MetaM Expr := do
  if let some v ← getIntValue? l then
    if v ≥ 0 then return mkNatLit v.toNat
  mkAppM ``Int.toNat #[l]

def wgExec (pl : WgPlan) (zr : Bool := false) (defer : Bool := true) : TacticM (Array Expr) := do
  let P := pl.car
  let nc := P.mov.size
  let some Inv ← wgInvOf P | throwError "wg: inv"
  let mut phs : Array Expr := #[]
  let mut acts : Array Expr := #[]
  let mut segAtoms : Array Expr := #[]
  for pc in pl.lp do
    if pc.cell then
      segAtoms := segAtoms.push default
      continue
    let some Q ← wgPOf pc.pred | throwError "wg: pred"
    let some A ← wgAbsOf Q | throwError "wg: abs"
    let some QI ← wgInvOf Q | throwError "wg: inv"
    let some mp ← wgMapOf Q P | throwError "wg: map"
    let before ← wgLhs
    let vs ← arRwLhs [pc.atom] (mkAppN A pc.atom.getAppArgs)
    let some a := (← wgLhs).find? (fun e => wgIsSeg e && !before.contains e) | throwError "wg: abs atom"
    let off := if Q.ai.isSome then 1 else 2
    phs := phs ++ pc.phs
    acts := acts ++ #[vs[0]!] ++ vs.extract off vs.size
    wgInvFact Q QI a
    if mp.2.2.isSome then
      let (out, lem) ← wgMapInst P mp a
      let _ ← arRwLhs [a] lem
      segAtoms := segAtoms.push out
    else
      segAtoms := segAtoms.push a
  unless phs.size == acts.size do throwError "wg: placeholders"
  arIntroFacts
  let sub := fun (e : Expr) => e.replaceFVars phs acts
  let mut late : Array (Nat × Expr) := #[]
  let mut cellC : Array (Nat × Expr) := #[]
  for j in P.cst do
    let mut tv : Option Expr := none
    for pc in pl.rp.reverse ++ pl.lp.reverse do
      if pc.cell then continue
      let v ← instantiateMVars (sub pc.en[j]!)
      unless v.hasExprMVar do
        tv := some v
        break
    let some e := tv | continue
    let mut need := false
    for i in [0 : pl.lp.size] do
      if pl.lp[i]!.cell then continue
      let a ← instantiateMVars segAtoms[i]!
      if (← wgComps a.getAppArgs[5]! nc)[j]! != e then need := true
    let z := mkNatLit 0
    let tgt := if (need || zr) && P.gloc.any (·.1 == j) && e != z then z else e
    unless tgt == e do
      late := late.push (j, e)
      cellC := cellC.push (j, tgt)
    for i in [0 : pl.lp.size] do
      if pl.lp[i]!.cell then continue
      let a ← instantiateMVars segAtoms[i]!
      let cj := (← wgComps a.getAppArgs[5]! nc)[j]!
      if cj == tgt then continue
      let a2 ← wgRetarget P a j tgt
      segAtoms := segAtoms.set! i a2
  let setC := fun (v : Array Expr) => cellC.foldl (fun acc (j, e) => acc.set! j e) v
  let mut parts : Array (Array Expr × Expr × Expr) := #[]
  let mut usedA : Array Expr := #[]
  for i in [0 : pl.lp.size] do
    let pc := pl.lp[i]!
    if pc.cell then
      let some CI ← wgCIOf P | throwError "wg: ci"
      let some (as, lem) ← wgCellMatch P CI (some (setC (pc.st.map sub))) (some (setC (pc.en.map sub))) usedA
        | throwError "wg: cell"
      let some (_, out) := entailHead? (← withMainContext do instantiateMVars (← inferType lem))
        | throwError "wg: cell"
      usedA := usedA ++ as
      parts := parts.push (as, lem, out)
    else
      let a := segAtoms[i]!
      wgInvFact P Inv a
      parts := parts.push (#[a], ← withMainContext do mkAppM ``HProp.himpl_refl #[a], a)
  let m := pl.rp.size
  let ks ← withMainContext do (Array.range m).mapM fun i => do
    if pl.rp[i]!.cell then pure (mkNatLit 1) else wgToNat (sub pl.rl[i]!)
  let zero := ks.map (· == mkNatLit 0)
  let lpEn ← pl.lp.mapM fun pc => pc.en.mapM fun e => instantiateMVars (sub e)
  let rpEn ← pl.rp.mapM fun pc => pc.en.mapM fun e => instantiateMVars (sub e)
  let mut groups : Array (Nat × Nat × Nat × Nat) := #[]
  let mut l0 := 0
  let mut r0 := 0
  for i in [0 : pl.lp.size - 1] do
    let e := lpEn[i]!
    if e.isEmpty || e.any (·.hasExprMVar) then continue
    let mut cut : Option Nat := none
    for j in [r0 : m - 1] do
      if rpEn[j]! == e then
        cut := some j
        break
    let some j := cut | continue
    groups := groups.push (l0, i + 1, r0, j + 1)
    l0 := i + 1
    r0 := j + 1
  groups := groups.push (l0, pl.lp.size, r0, m)
  let hasLive := fun (g : Nat × Nat × Nat × Nat) =>
    (Array.range (g.2.2.2 - g.2.2.1)).any fun i => !zero[i + g.2.2.1]!
  let mut merged : Array (Nat × Nat × Nat × Nat) := #[]
  let mut pend : Option (Nat × Nat) := none
  for g in groups do
    let (gl0, gl1, gr0, gr1) := g
    let (gl0, gr0) := match pend with
      | some (a, b) => (a, b)
      | none => (gl0, gr0)
    if hasLive (gl0, gl1, gr0, gr1) then
      merged := merged.push (gl0, gl1, gr0, gr1)
      pend := none
    else if let some (ml0, _, mr0, _) := merged.back? then
      merged := merged.pop.push (ml0, gl1, mr0, gr1)
      pend := none
    else pend := some (gl0, gr0)
  if let some (a, b) := pend then
    if let some (ml0, _, mr0, _) := merged.back? then
      merged := merged.pop.push (ml0, pl.lp.size, mr0, m)
    else merged := merged.push (a, pl.lp.size, b, m)
  groups := merged
  let cellBad := groups.any fun (gl0, gl1, gr0, gr1) =>
    let gl := (Array.range (gr1 - gr0)).map (· + gr0) |>.filter (!zero[·]!)
    gl.size == 1 && pl.rp[gl[0]!]!.cell && !(gl1 == gl0 + 1 && pl.lp[gl0]!.cell)
  if cellBad then groups := #[(0, pl.lp.size, 0, m)]
  let mut pieces : Array Expr := Array.replicate m default
  let mut news : Array FVarId := #[]
  let mut live : Array Nat := #[]
  let mut deferred : Array (Nat × Array Expr) := #[]
  for (gl0, gl1, gr0, gr1) in groups do
    let gparts := parts.extract gl0 gl1
    let glive := (Array.range (gr1 - gr0)).map (· + gr0) |>.filter (!zero[·]!)
    if defer && glive.size == 1 && gparts.size ≥ 2 && !pl.rp[glive[0]!]!.cell && pl.rp[glive[0]!]!.idx.isSome then
      let mut outs : Array Expr := #[]
      for (as, lem, out) in gparts do
        unless as.size == 1 && as[0]! == out do
          let _ ← arRwLhs as.toList lem
        outs := outs.push out
      for (j, e) in late do
        outs ← outs.mapM fun o => do wgRetarget P (← instantiateMVars o) j e
      for o in outs do wgInvFact P Inv (← instantiateMVars o)
      deferred := deferred.push (glive[0]!, outs)
      continue
    let (allA, chain, accJ) ← withMainContext do
      let (a0, p0, j0) := gparts[gparts.size - 1]!
      let mut as := a0
      let mut pf := p0
      let mut J := j0
      for i' in [0 : gparts.size - 1] do
        let (ai, pi, oi) := gparts[gparts.size - 2 - i']!
        let oa := oi.getAppArgs
        let ja := J.getAppArgs
        unless oa[6]! == ja[5]! do throwError "wg: chain"
        let join := mkAppN (mkConst ``Sep.wseg_join) #[P.inst, P.sty, P.cLam, oa[3]!, ja[3]!, oa[4]!,
          ja[4]!, oa[5]!, oa[6]!, ja[6]!]
        let fr ← mkAppM ``HProp.himpl_frame_lr #[pi, pf]
        pf ← mkAppM ``HProp.himpl_trans #[fr, join]
        as := ai ++ as
        let some (_, j') := entailHead? (← instantiateMVars (← inferType join)) | throwError "wg: join"
        J := j'
      pure (as, pf, J)
    if gparts.size ≥ 2 || pl.lp[gl0]!.cell then
      let _ ← arRwLhs allA.toList chain
    let mut acc := accJ
    for (j, e) in late do
      acc ← wgRetarget P (← instantiateMVars acc) j e
    live := live ++ glive
    if glive.size ≤ 1 then
      for i in glive do pieces := pieces.set! i acc
    else
      let kl := glive.map (ks[·]!)
      let ml := kl.size
      let sums ← withMainContext do
        let mut sums : Array Expr := Array.replicate ml (mkNatLit 0)
        sums := sums.set! (ml - 1) kl[ml - 1]!
        for i' in [0 : ml - 1] do
          let i := ml - 2 - i'
          sums := sums.set! i (← mkAppM ``HAdd.hAdd #[kl[i]!, sums[i + 1]!])
        pure sums
      let aa := acc.getAppArgs
      acc ← wgCongTo acc sums[0]! aa[4]! aa[5]! aa[6]! nc
      for i in [0 : ml - 1] do
        let ca := acc.getAppArgs
        let lem := mkAppN (mkConst ``Sep.wseg_split) #[P.inst, P.sty, P.cLam, kl[i]!, sums[i + 1]!,
          ca[4]!, ca[5]!, ca[6]!]
        let vs ← arRwLhs [acc] lem
        unless vs.size == 2 do throwError "wg: split"
        let tc ← wgDestruct vs[0]!
        news := news ++ tc.map (·.fvarId!) ++ #[vs[1]!.fvarId!]
        let tt ← withMainContext do wgTuple tc
        let L ← wgLhs
        let some pa := L.find? (fun e => wgIsSeg e && e.getAppArgs[6]! == tt && e.getAppArgs[5]! == ca[5]!)
          | throwError "wg: split piece"
        let some na := L.find? (fun e => wgIsSeg e && e.getAppArgs[5]! == tt) | throwError "wg: split rest"
        pieces := pieces.set! glive[i]! pa
        acc := na
      pieces := pieces.set! glive[ml - 1]! acc
  for i in live do wgInvFact P Inv pieces[i]!
  for i in [0 : m] do
    unless pl.rp[i]!.cell do continue
    let x := pieces[i]!
    let xa := x.getAppArgs
    let lem ← withMainContext do
      let pf := mkAppN (mkConst ``Sep.wseg_uncell) #[P.inst, P.sty, P.cLam, xa[5]!, xa[6]!, xa[4]!]
      let r ← wgNorm (P.cLam.beta #[xa[5]!, xa[6]!, xa[4]!])
      mkExpectedTypeHint pf (← mkAppM ``HProp.himpl #[x, r])
    let vs ← arRwLhs [x] lem
    news := news ++ vs.map (·.fvarId!)
    arIntroFacts
  wgSubstNew news
  wgNormAll
  let ws ← arOpenGoal
  let R ← wgRhs
  let mut rsegs : Array (Expr × Bool) := #[]
  for ri in [0 : m] do
    let pc := pl.rp[ri]!
    let z := zero[ri]!
    let some j := pc.idx | continue
    let want ← instantiateMVars pc.atom
    let mut r ← instantiateMVars R[j]!
    for e in R do
      if (← instantiateMVars e) == want then
        r := ← instantiateMVars e
        break
    let some Q ← wgPOf pc.pred | throwError "wg: rpred"
    let some C ← wgConcOf Q | throwError "wg: conc"
    let some mp ← wgMapOf P Q | throwError "wg: rmap"
    let (segQ, b1, lem1, sQ, eQ, kM, nE) ← withMainContext do
      let xs := r.getAppArgs
      let miss ← (wgMissTys Q).mapM fun ty => mkFreshExprMVar (some ty)
      let nM ← mkFreshExprMVar (some arIntT)
      let kM ← mkFreshExprMVar (some (mkConst ``Nat))
      let nE := match Q.ai with
        | some i => xs[i]!
        | none => nM
      let sQ := Q.mov.map (xs[·]!)
      let eQ := wgEnC Q xs miss
      let segQ := wgSeg Q kM nE (← wgTuple sQ) (← wgTuple eQ)
      let lhsQ ← wgConcLhs Q kM nE xs miss
      let hkT ← wgCond Q kM
      let body := mkAppN C (#[kM] ++ xs ++ miss ++ (if Q.ai.isSome then #[] else #[nM]))
      let lam ← withLocalDeclD `hk hkT fun hk => do mkLambdaFVars #[hk] (mkApp body hk)
      let pq ← mkAppOptM ``HProp.hpure #[Q.inst, hkT]
      let lem1 ← mkAppOptM ``HProp.himpl_hstar_hpure_l #[Q.inst, hkT, lhsQ, r, lam]
      pure (segQ, ← mkAppM ``HProp.hstar #[pq, lhsQ], lem1, sQ, eQ, kM, nE)
    wgRwRhs r b1 lem1
    if mp.2.2.isSome then
      let (seg2, lem2) ← withMainContext do
        let (st, en) ← wgRhsSt P mp sQ eQ
        let segP := wgSeg P kM nE (← wgTuple st) (← wgTuple en)
        let some lem := mp.2.2 | throwError "wg: rmap"
        let pf := mkAppN lem #[kM, nE, ← wgTuple st, ← wgTuple en]
        pure (segP, ← mkExpectedTypeHint pf (← mkAppM ``HProp.himpl #[segP, segQ]))
      wgRwRhs segQ seg2 lem2
      rsegs := rsegs.push (seg2, z)
    else
      rsegs := rsegs.push (segQ, z)
    if let some (_, outs) := deferred.find? (·.1 == ri) then
      let (rseg, _) := rsegs.back!
      rsegs := rsegs.pop
      let (pf, src) ← withMainContext do
        let outs ← outs.mapM instantiateMVars
        let o0 := outs[outs.size - 1]!
        let mut pf ← mkAppM ``HProp.himpl_refl #[o0]
        let mut J := o0
        for i' in [0 : outs.size - 1] do
          let oi := outs[outs.size - 2 - i']!
          let oa := oi.getAppArgs
          let ja := J.getAppArgs
          unless oa[6]! == ja[5]! do throwError "wg: chain"
          let join := mkAppN (mkConst ``Sep.wseg_join) #[P.inst, P.sty, P.cLam, oa[3]!, ja[3]!, oa[4]!,
            ja[4]!, oa[5]!, oa[6]!, ja[6]!]
          let fr ← mkAppM ``HProp.himpl_frame_lr #[← mkAppM ``HProp.himpl_refl #[oi], pf]
          pf ← mkAppM ``HProp.himpl_trans #[fr, join]
          let some (_, j') := entailHead? (← instantiateMVars (← inferType join)) | throwError "wg: join"
          J := j'
        let ra ← (← instantiateMVars rseg).getAppArgs.mapM instantiateMVars
        let ja := J.getAppArgs
        if ra[3]!.isMVar then
          let _ ← isDefEq ra[3]! ja[3]!
        if ra[4]!.isMVar then
          let _ ← isDefEq ra[4]! ja[4]!
        unless ← isDefEq ra[5]! ja[5]! do throwError "wg: deferred start"
        unless ← isDefEq ra[6]! ja[6]! do throwError "wg: deferred end"
        let ra ← ra.mapM instantiateMVars
        let cong ← wgCongPf J ra[3]! ra[4]! ra[5]! ra[6]! nc
        let inst := P.inst
        pure (← mkAppM ``HProp.himpl_trans #[pf, cong], starOf inst outs.toList)
      wgRwRhs (← instantiateMVars rseg) src pf
  for (r, z) in rsegs do
    if z then continue
    let ls := (← wgLhs).filter (fun e => wgIsSeg e && e.getAppArgs[2]! == P.cLam)
    let mut done := false
    for l in ls do
      if ← wgUnify l r nc then
        let ra ← r.getAppArgs.mapM instantiateMVars
        let _ ← wgCongTo l ra[3]! ra[4]! ra[5]! ra[6]! nc
        done := true
        break
    unless done || P.cst.isEmpty do
      for l in ls do
        let s ← saveState
        if ← wgUnify l r nc P.cst then
          try
            let ra ← r.getAppArgs.mapM instantiateMVars
            let rs ← wgComps ra[5]! nc
            let mut l2 := l
            for j in P.cst do
              let cj := (← wgComps (← instantiateMVars l2).getAppArgs[5]! nc)[j]!
              unless cj == rs[j]! do l2 ← wgRetarget P (← instantiateMVars l2) j rs[j]!
            let _ ← wgCongTo l2 ra[3]! ra[4]! ra[5]! ra[6]! nc
            done := true
            break
          catch _ => wgBack s
        else wgBack s
    unless done do throwError "wg: rhs seg"
  for (r, z) in rsegs do
    if z then wgNil P r
  return ws

def wgFinish (ws : Array Expr) : TacticM Unit := do
  withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (lhs, rhs) := entailHead? t | throwError "wg: goal"
    let L := (flatStar lhs #[]).filter (!·.isAppOf ``HProp.hpure)
    let R := (flatStar rhs #[]).filter (fun r => !r.isAppOf ``HProp.hpure && r.hasExprMVar)
    unless ← arAssign L R.toList #[] do throwError "wg: witness"
    for w in ws do
      if (← instantiateMVars w).hasExprMVar then throwError "wg: witness open"
  let s ← saveState
  if ← (try finishDirect catch _ => pure false) then return
  s.restore
  Sep.Xsimpl.xsimplDriver none
  cleanAll
  wgCloseAll
  unless (← getUnsolvedGoals).isEmpty do throwError "wg: open"

def wgLowFacts : TacticM Unit := do
  for x in (← wgLhs) do
    let some p := x.getAppFn.constName? | continue
    let some P ← wgPOf p | continue
    unless P.ai.isSome && x.getAppNumArgs == P.tys.size do continue
    let some lo ← wgLoOf P | continue
    withMainContext do
      let g ← getMainGoal
      let t ← instantiateMVars (← g.getType)
      let some (lhs, rhs) := entailHead? t | return
      let inst := t.getAppArgs[0]!
      let xa := x.getAppArgs
      let q ← arLe (← arIntLit P.kmin) xa[P.ai.get!]!
      let known ← (← getLCtx).anyM fun dcl => do
        if dcl.isImplementationDetail then return false
        return (← instantiateMVars dcl.type) == q
      if known then return
      let some pf := holdsLift? inst q x (mkAppN lo xa) lhs | return
      let mv ← mkFreshExprSyntheticOpaqueMVar (← mkArrow q t)
      g.assign (mkAppN (mkConst ``himpl_of_holds) #[inst, q, lhs, rhs, pf, mv])
      let (_, g2) ← mv.mvarId!.intro1P
      replaceMainGoal [g2]

def wgPrebuild (pl : WgPlan) : TacticM Unit := do
  let P := pl.car
  let _ ← wgInvOf P
  if pl.lp.any (·.cell) then
    let _ ← wgCIOf P
  for pc in pl.lp do
    if pc.cell then continue
    if let some Q ← wgPOf pc.pred then
      let _ ← wgAbsOf Q
      let _ ← wgInvOf Q
  for pc in pl.rp do
    if pc.cell then continue
    if let some Q ← wgPOf pc.pred then
      let _ ← wgConcOf Q

partial def witTuples (L Rs ms : Array Expr) (base : Array (Array Expr)) (bound cap i : Nat)
    (acc : Array Expr) (out : Array (Array Expr)) : MetaM (Array (Array Expr)) := do
  if out.size ≥ bound then return out
  if i == ms.size then return out.push acc
  let sub := fun (e : Expr) => e.replace (fun t => match ms.idxOf? t with
    | some j => if j < acc.size then some acc[j]! else none
    | none => none)
  let free := fun (e : Expr) => (e.find? (ms.contains ·)).isSome
  let m := ms[i]!
  let mut sc : Array (Nat × Expr) := #[]
  for r in Rs do
    let r' := sub r
    let ra := r'.getAppArgs
    for pos in [0 : ra.size] do
      unless ra[pos]! == m do continue
      for (s, l) in witPairs L r' free do
        if s > 0 then sc := sc.push (s, l.getAppArgs[pos]!)
  let sorted := (sc.insertionSort (fun a b => a.1 > b.1)).map (·.2)
  let mut cands : Array Expr := #[]
  for c in sorted ++ base[i]! do
    if !cands.contains c && cands.size < cap then cands := cands.push c
  let mut o := out
  for c in cands do
    o ← witTuples L Rs ms base bound cap (i + 1) (acc.push c) o
    if o.size ≥ bound then break
  return o

def witInst (vals : Array Expr) : TacticM Unit := do
  for v in vals do
    withMainContext do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some (lhs, rhs) := entailHead? t | throwError "wit: goal"
    unless rhs.isAppOf ``HProp.hexists do throwError "wit: binder"
    let lam := rhs.appArg!
    let inst := t.getAppArgs[0]!
    let body := (lam.bindingBody!.instantiate1 v)
    let m ← g.withContext do mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[lhs, body])
    g.assign (← mkAppOptM ``HProp.himpl_hexists_r #[inst, lam.bindingDomain!, v, lhs, lam, m])
    replaceMainGoal [m.mvarId!]

def witEnum (k : TacticM Unit) : TacticM Unit := do
  let _ ← tryTactic (evalTactic (← `(tactic| conv_rhs => simp only
    [Sep.Xsearch.hstar_hexists_rr, HProp.hstar_hexists, HProp.hstar_assoc])))
  let tuples ← withMainContext do
    let s ← saveState
    let t ← instantiateMVars (← (← getMainGoal).getType)
    if t.hasExprMVar then throwError "wit: mvars"
    let some (lhs, rhs) := entailHead? t | throwError "wit: goal"
    let (body, ms) ← arOpen rhs
    if ms.isEmpty then throwError "wit: no binder"
    let heads := (xsearchUnfoldExt.getState (← getEnv)).map (·.headFn)
    let isPred := fun (e : Expr) => match e.getAppFn.constName? with
      | some n => heads.contains n
      | none => false
    let Rs := (flatStar body #[]).filter (!·.isAppOf ``HProp.hpure)
    let Ls := (flatStar lhs #[]).filter (!·.isAppOf ``HProp.hpure)
    let ok := fun (e : Expr) => isPred e || e.isAppOf ``HProp.hsingle
    unless Rs.all ok && !Ls.isEmpty && Ls.all ok && (Rs ++ Ls).any isPred do
      throwError "wit: shape"
    let mut roots : Array Expr := #[]
    let mut holes : Array Expr := #[]
    for x in Ls do
      let xa := x.getAppArgs
      for i in [0 : xa.size] do
        unless ← isDefEq (← inferType xa[i]!) (mkConst ``Nat) do continue
        if i == 0 then
          unless roots.contains xa[i]! do roots := roots.push xa[i]!
        else unless holes.contains xa[i]! do holes := holes.push xa[i]!
    let nil := mkNatLit 0
    let mut base : Array (Array Expr) := #[]
    for m in ms do
      unless ← isDefEq (← inferType m) (mkConst ``Nat) do throwError "wit: type"
      unless Rs.any (fun r => r.getAppArgs.contains m) do throwError "wit: unused"
      let atRoot := Rs.any (fun r => r.getAppArgs[0]? == some m)
      base := base.push (if atRoot then roots ++ holes ++ #[nil] else holes ++ #[nil] ++ roots)
    let terms := (roots ++ holes).foldl (fun acc e => if acc.contains e then acc else acc.push e) #[nil]
    let out ← witTuples Ls Rs ms base (terms.size * ms.size + 1) terms.size 0 #[] #[]
    s.restore
    pure out
  let gd ← globalDeadline.get
  let saved ← getGoals
  for i in [0 : tuples.size] do
    let now ← vclock
    if now ≥ gd then break
    let s ← saveState
    let ok ← try (do
        witInst tuples[i]!
        if ← goalRefuted then throwError "wit: refuted"
        globalDeadline.set (if i + 1 == tuples.size then gd else now + (gd - now) / 2)
        k
        unless (← getUnsolvedGoals).isEmpty do throwError "wit: open"
        pure true) catch _ => pure false
    globalDeadline.set gd
    if ok then return
    s.restore
    setGoals saved
  throwError "wit: no witness"

def wgCands (L : Array Expr) : MetaM (Array WgP) := do
  let mut cands : Array WgP := #[]
  for x in L do
    if let some p := x.getAppFn.constName? then
      if let some P ← wgPOf p then
        if !cands.any (·.cLam == P.cLam) then cands := cands.push P
  return cands

def wgFinishable : TacticM Bool := withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (lhs, rhs) := entailHead? t | return false
  let (body, _) ← arOpen rhs
  let L := flatStar lhs #[]
  return (flatStar body #[]).all fun r =>
    r.isAppOf ``HProp.hpure || wgIsSeg r || r.hasExprMVar || L.contains r

def wgRhsSize : TacticM Nat := withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (_, rhs) := entailHead? t | return 0
  let (body, _) ← arOpen rhs
  return ((flatStar body #[]).filter (fun e => !e.isAppOf ``HProp.hpure && !wgIsSeg e)).size

def wgStateKey (base : Array FVarId) : TacticM (Array Expr) := withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (lhs, rhs) := entailHead? t | return #[]
  let (body, _) ← arOpen rhs
  let norm := fun (e : Expr) => if wgIsSeg e then
      mkApp3 (mkConst `wgSegKey) e.getAppArgs[2]! e.getAppArgs[5]! e.getAppArgs[6]! else e
  let keep := fun (e : Expr) => !e.isAppOf ``HProp.hpure &&
    (Lean.collectFVars {} e).fvarIds.all base.contains
  let ls := ((flatStar lhs #[]).map norm).filter keep
  let rs := ((flatStar body #[]).map norm).filter keep
  return ls ++ #[mkConst `wgSep] ++ rs

partial def wgRound (cands : Array WgP) (wsAcc : Array Expr) (resid : Bool := false)
    (memo : Option (IO.Ref (Array (Array Expr))) := none) (base : Array FVarId := #[]) :
    TacticM Unit := do
  let s ← saveState
  let base ← if resid then pure base else withMainContext do return (← getLCtx).getFVarIds
  let memo ← match memo with
    | some m => pure m
    | none => IO.mkRef #[]
  let key ← wgStateKey base
  let sameKey := fun (k : Array Expr) =>
    k.size == key.size && k.all (fun e => key.count e == k.count e)
  if resid then
    if (← memo.get).any sameKey then throwError "wg: failed state"
  let won ← IO.mkRef (none : Option Tactic.SavedState)
  let n0 ← wgRhsSize
  let carriers := cands.flatMap fun P =>
    if P.cellData.size ≤ 1 then #[P] else #[P] ++ (wgViews P).extract 1 P.cellData.size
  for P in carriers do
    if ← pastGlobal then break
    let onPlan := fun (pl : WgPlan) => do
      if ← pastGlobal then return false
      let sw ← saveState
      wgBack s
      try
        wgPrebuild pl
        let s2 ← saveState
        let defer := (pl.rp.filter (·.idx.isSome)).size < n0
        let ws ← try wgExec pl (defer := defer) catch e => do
          if pl.car.gloc.isEmpty then throw e
          wgBack s2
          wgExec pl true defer
        let allWs := wsAcc ++ ws
        let st' ← saveState
        try
          unless ← wgFinishable do throwError "wg: unmatched"
          wgFinish allWs
        catch _ =>
          wgBack st'
          let n1 ← wgRhsSize
          unless n1 < n0 do throwError "wg: no progress"
          let rest ← withMainContext do
            let t ← instantiateMVars (← (← getMainGoal).getType)
            let some (lhs, rhs) := entailHead? t | throwError "wg: goal"
            wgCands (flatStar lhs #[] ++ flatStar rhs #[])
          let gd ← globalDeadline.get
          let now ← vclock
          if gd > now then globalDeadline.set (now + (gd - now) * n1 / (n0 + 1))
          try wgRound rest allWs true memo base finally globalDeadline.set gd
        won.set (some (← saveState))
        return true
      catch _ =>
        wgBack sw
        return false
    let _ ← (try wgPlanFor P onPlan catch _ => pure false)
    if (← won.get).isSome then break
  if let some w := ← won.get then
    w.restore
    return
  wgBack s
  if resid && !(← pastGlobal) then memo.modify (·.push key)
  throwError "wg: no plan"

partial def wgSplitHyp (g : MVarId) (h : FVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← h.getType)
  if ty.isAppOfArity ``And 2 then
    let gs ← g.cases h
    let some sg := gs[0]? | throwError "wg: split"
    let fs := sg.fields
    let g1 ← wgSplitHyp sg.mvarId fs[0]!.fvarId!
    let f1 := (sg.subst.get fs[1]!.fvarId!)
    wgSplitHyp g1 f1.fvarId!
  else return g

partial def wgUnpackEx (g : MVarId) (h : FVarId) (acc : Array FVarId) :
    MetaM (MVarId × Array FVarId) := g.withContext do
  let ty ← instantiateMVars (← h.getType)
  if ty.isAppOfArity ``Exists 2 then
    let gs ← g.cases h
    let some sg := gs[0]? | throwError "wg: unpack"
    let fs := sg.fields
    let w := fs[0]!.fvarId!
    let hp := fs[1]!.fvarId!
    wgUnpackEx sg.mvarId hp (acc.push w)
  else
    return (← wgSplitHyp g h, acc)

def wgEntryFacts : TacticM (Array (Expr × Expr)) := do
  let mut out : Array (Expr × Expr) := #[]
  for x in (← wgLhs) do
    let some p := x.getAppFn.constName? | continue
    let some P ← wgPOf p | continue
    unless x.getAppNumArgs == P.tys.size do continue
    let some fct ← wgFactOf P | continue
    let r ← withMainContext do
      let g ← getMainGoal
      let t ← instantiateMVars (← g.getType)
      let some (lhs, rhs) := entailHead? t | return none
      let inst := t.getAppArgs[0]!
      let pfx := mkAppN fct x.getAppArgs
      let hty ← whnfR (← inferType pfx)
      unless hty.isAppOf ``holdsP do return none
      let q := hty.getAppArgs[1]!
      let some pf := holdsLift? inst q x pfx lhs | return none
      let mv ← mkFreshExprSyntheticOpaqueMVar (← mkArrow q t)
      g.assign (mkAppN (mkConst ``himpl_of_holds) #[inst, q, lhs, rhs, pf, mv])
      let (h, g2) ← mv.mvarId!.intro1P
      let (g3, ws) ← wgUnpackEx g2 h #[]
      pure (some (g3, ws))
    let some (g3, ws) := r | continue
    replaceMainGoal [g3]
    if let some k := ws[0]? then out := out.push (x, mkFVar k)
  return out

def wgFalseClose : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let s ← saveState
  try
    g.assign (← mkAppOptM ``False.elim #[← g.getType, ← wgSide (mkConst ``False)])
    replaceMainGoal []
    return true
  catch _ =>
    s.restore
    return false

def wgDropEmpty (ks : Array (Expr × Expr)) : TacticM Unit := do
  let mut dropped := false
  for (x, k) in ks do
    let s ← saveState
    try
      let isZero ← withMainContext do
        try (do
            let _ ← wgSide (← mkAppM ``Eq #[k, mkNatLit 0])
            pure true) catch _ => pure false
      unless isZero do continue
      let some p := x.getAppFn.constName? | continue
      let some P ← wgPOf p | continue
      let some A ← wgAbsOf P | continue
      let some Inv ← wgInvOf P | continue
      let before ← wgLhs
      unless before.contains x do continue
      let _ ← arRwLhs [x] (mkAppN A x.getAppArgs)
      let some a := (← wgLhs).find? (fun e => wgIsSeg e && !before.contains e) | throwError "wg: drop"
      wgInvFact P Inv a
      let aa := a.getAppArgs
      let a0 ← wgCongTo a (mkNatLit 0) aa[4]! aa[5]! aa[6]! P.mov.size
      let a0a := a0.getAppArgs
      let lem := mkAppN (mkConst ``Sep.wseg_zero_elim) #[P.inst, P.sty, P.cLam, a0a[4]!, a0a[5]!, a0a[6]!]
      let _ ← arRwLhs [a0] lem
      let _ ← arIntroLhs
      arIntroFacts
      dropped := true
    catch _ => s.restore
  if dropped then wgSubstAll

def wgAddHyp (q pf : Expr) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (lhs, rhs) := entailHead? t | throwError "wg: hyp goal"
  let inst := t.getAppArgs[0]!
  let mv ← mkFreshExprSyntheticOpaqueMVar (← mkArrow q t)
  g.assign (mkAppN (mkConst ``himpl_of_holds) #[inst, q, lhs, rhs, pf, mv])
  let (_, g2) ← mv.mvarId!.intro1P
  replaceMainGoal [g2]

def wgBkNe (P : WgP) (x : Expr) (pv ad : Nat) (e : Expr) : TacticM Unit := do
  let some A ← wgAbsOf P | return
  let some bk ← wgBkOf P pv ad | return
  let ba := bk.getAppArgs
  let base := ba.extract (ba.size - 5) ba.size
  let xs := x.getAppArgs
  let st := P.mov.map (xs[·]!)
  let p0 := st[pv]!
  let en := wgEnC P xs #[]
  let L ← wgLhs
  let inst := P.inst
  let rest := L.erase x
  for a in ptoLocsOf (starOf inst rest.toList) #[] do
    if a == e then continue
    let known ← withMainContext do
      return (← arByHyp (← mkAppM ``Ne #[a, e])).isSome || (← arByHyp (← mkAppM ``Ne #[e, a])).isSome
    if known then continue
    let s ← saveState
    try
      let h0 ← withMainContext do
        let q ← mkAppM ``Ne #[p0, a]
        if let some h := ← arByHyp q then return h
        let t ← instantiateMVars (← (← getMainGoal).getType)
        let some (lhs, _) := entailHead? t | throwError "wg: bkne goal"
        let some hl ← wgNeHeap lhs p0 a | throwError "wg: bkne sep"
        pure hl
      let h0 ← withMainContext do
        if (← inferType h0).isAppOf ``holdsP then
          wgAddHyp (← mkAppM ``Ne #[p0, a]) h0
          withMainContext do
            let some h ← arByHyp (← mkAppM ``Ne #[p0, a]) | throwError "wg: bkne hyp"
            pure h
        else pure h0
      withMainContext do
        let t ← instantiateMVars (← (← getMainGoal).getType)
        let some (lhs, _) := entailHead? t | throwError "wg: bkne goal"
        let L2 := flatStar lhs #[]
        let F := starOf inst (L2.erase x).toList
        let some hF ← wgCellLoc? a F | throwError "wg: bkne loc"
        let cond ← withLocalDeclD `k (mkConst ``Nat) fun k => do mkLambdaFVars #[k] (← wgCond P k)
        let pf := mkAppN (mkConst ``holdsP_abs_prev) (#[inst, P.sty] ++ base ++
          #[x, F, ← wgTuple st, ← wgTuple en, cond, a, mkAppN A xs, hF, h0])
        let some pm ← provePerm lhs (mkApp3 (mkConst ``HProp.hstar) inst x F) | throwError "wg: bkne perm"
        let q ← mkAppM ``Ne #[a, e]
        let hp ← mkAppM ``holdsP_mono_imp #[pm, pf]
        let hp ← mkExpectedTypeHint hp (← mkAppM ``holdsP #[q, lhs])
        wgAddHyp q hp
    catch _ => s.restore

def wgBkDrop : TacticM Unit := do
  let mut dropped := false
  for x in ← wgLhs do
    let some p := x.getAppFn.constName? | continue
    let some P ← wgPOf p | continue
    unless x.getAppNumArgs == P.tys.size && !P.prevAdr.isEmpty && (wgMissTys P).isEmpty do continue
    let xs := x.getAppArgs
    let en := wgEnC P xs #[]
    for (pv, ad) in P.prevAdr do
      let before ← wgLhs
      unless before.contains x do break
      let some e := en[pv]? | continue
      let ok ← wgCellLoc? e (starOf P.inst (before.erase x).toList)
      unless ok.isSome do
        wgBkNe P x pv ad e
        continue
      let s ← saveState
      try
        let some A ← wgAbsOf P | throwError "wg: bk abs"
        let some Inv ← wgInvOf P | throwError "wg: bk inv"
        let some bk ← wgBkOf P pv ad | throwError "wg: bk lemma"
        let _ ← arRwLhs [x] (mkAppN A xs)
        let some a := (← wgLhs).find? (fun e => wgIsSeg e && !before.contains e) | throwError "wg: bk atom"
        wgInvFact P Inv a
        withMainContext do
          let g ← getMainGoal
          let t ← instantiateMVars (← g.getType)
          let some (lhs, rhs) := entailHead? t | throwError "wg: bk goal"
          let a ← instantiateMVars a
          let aa := a.getAppArgs
          let F := starOf P.inst ((flatStar lhs #[]).erase a).toList
          let e' := (← wgComps aa[6]! P.mov.size)[pv]!
          let some hl ← wgCellLoc? e' F | throwError "wg: bk loc"
          let pf := mkAppN bk #[F, aa[3]!, aa[4]!, aa[5]!, aa[6]!, hl]
          let some pm ← provePerm lhs (mkApp3 (mkConst ``HProp.hstar) P.inst a F) | throwError "wg: bk perm"
          let q ← mkAppM ``Eq #[aa[3]!, mkNatLit 0]
          let hp ← mkAppM ``holdsP_mono_imp #[pm, pf]
          let mv ← mkFreshExprSyntheticOpaqueMVar (← mkArrow q t)
          g.assign (mkAppN (mkConst ``himpl_of_holds) #[P.inst, q, lhs, rhs, hp, mv])
          let (_, g2) ← mv.mvarId!.intro1P
          replaceMainGoal [g2]
        let aa := (← instantiateMVars a).getAppArgs
        let a0 ← wgCongTo a (mkNatLit 0) aa[4]! aa[5]! aa[6]! P.mov.size
        let a0a := a0.getAppArgs
        let lem := mkAppN (mkConst ``Sep.wseg_zero_elim) #[P.inst, P.sty, P.cLam, a0a[4]!, a0a[5]!, a0a[6]!]
        let _ ← arRwLhs [a0] lem
        let _ ← arIntroLhs
        arIntroFacts
        dropped := true
        break
      catch _ => s.restore
  if dropped then wgSubstAll

def wgDupAlloc : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (lhs, rhs) := entailHead? t | return false
  let inst := t.getAppArgs[0]!
  let L := flatStar lhs #[]
  let cells := L.filter (·.isAppOfArity ``HProp.hsingle 3)
  for i in [0 : cells.size] do
    for j in [i + 1 : cells.size] do
      let a := cells[i]!
      let b := cells[j]!
      unless a.appFn!.appArg! == b.appFn!.appArg! do continue
      let rest := (L.erase a).erase b
      let ab := mkApp3 (mkConst ``HProp.hstar) inst a b
      let tgt := if rest.isEmpty then ab else mkApp3 (mkConst ``HProp.hstar) inst ab (starOf inst rest.toList)
      let some pm ← provePerm lhs tgt | continue
      let fl ← mkAppM ``hstar_hsingle_same_loc #[a.appFn!.appArg!, a.appArg!, b.appArg!]
      let fal ← mkAppOptM ``HProp.hpure #[inst, mkConst ``False]
      let pf ← if rest.isEmpty then
          mkAppM ``HProp.himpl_trans #[fl, ← mkAppM ``HProp.himpl_trans
            #[← mkAppM ``HProp.himpl_hempty_hpure #[mkConst ``True.intro],
              ← mkAppOptM ``HProp.himpl_hstar_hpure_l #[none, mkConst ``False, ← mkAppOptM ``HProp.hempty #[inst], rhs,
                ← withLocalDeclD `f (mkConst ``False) fun f => do mkLambdaFVars #[f] (← mkAppOptM ``False.elim #[← mkAppM ``HProp.himpl #[← mkAppOptM ``HProp.hempty #[inst], rhs], f])]]]
        else do
          let restE := starOf inst rest.toList
          let fr := mkAppN (mkConst ``HProp.himpl_frame_l) #[inst, ab, fal, restE, fl]
          let el ← mkAppOptM ``HProp.himpl_hstar_hpure_l #[none, mkConst ``False, restE, rhs,
            ← withLocalDeclD `f (mkConst ``False) fun f => do
              mkLambdaFVars #[f] (← mkAppOptM ``False.elim #[← mkAppM ``HProp.himpl #[restE, rhs], f])]
          mkAppM ``HProp.himpl_trans #[fr, el]
      let full ← mkAppM ``HProp.himpl_trans #[pm, pf]
      unless ← isDefEq (← inferType full) t do continue
      g.assign full
      replaceMainGoal []
      return true
  return false

def wgSegCycle : TacticM Bool := do
  let mut edges : Array (Expr × Expr) := #[]
  for x in (← wgLhs) do
    let some p := x.getAppFn.constName? | continue
    let some P ← wgPOf p | continue
    unless x.getAppNumArgs == P.tys.size do continue
    let xs := x.getAppArgs
    let some i0 := P.mov[0]? | continue
    let some (some f, _) := P.endSpec[0]? | continue
    edges := edges.push (← instantiateMVars xs[i0]!, ← instantiateMVars xs[f]!)
  let mut reach : Array (Expr × Expr) := edges
  let mut grew := true
  while grew do
    grew := false
    for (a, b) in reach do
      for (c, d) in edges do
        if b == c && !reach.contains (a, d) then
          reach := reach.push (a, d)
          grew := true
  return reach.any (fun (a, b) => a == b)

def wgEntry : TacticM Bool := do
  arIntroFacts
  wgLowFacts
  wgBkDrop
  if ← (try wgDupAlloc catch _ => pure false) then return true
  unless ← wgSegCycle do return false
  let ks ← wgEntryFacts
  if ← wgFalseClose then return true
  wgDropEmpty ks
  return false

def wgPayPreds (P : WgP) : MetaM (Array Name) := do
  let mut out : Array Name := #[]
  for V in wgViews P do
    let r ← lambdaTelescope V.preLam fun _ body => do
      return (flatStar body #[]).filterMap fun it =>
        if it.isAppOf ``HProp.hsingle || it.isAppOf ``HProp.hpure then none else it.getAppFn.constName?
    for q in r do
      unless out.contains q || q == P.pname do out := out.push q
  return out

def wgPayChain (Q : WgP) (L : Array Expr) (a : Expr) : TacticM (Option (Array Expr)) := withMainContext do
  let xs ← a.getAppArgs.mapM instantiateMVars
  unless xs.size == Q.tys.size do return none
  let s ← saveState
  let miss ← (wgMissTys Q).mapM fun ty => mkFreshExprMVar (some ty)
  let tgt ← (wgEnC Q xs miss).mapM instantiateMVars
  if tgt.any (·.hasExprMVar) then
    s.restore
    return none
  let mut cur := Q.mov.map (xs[·]!)
  let mut used : Array Nat := #[]
  let same := fun (a b : Array Expr) => (Array.range a.size).all fun i => Q.cst.contains i || a[i]! == b[i]!
  let keepC := fun (c e : Array Expr) => (Array.range e.size).map fun i => if Q.cst.contains i then c[i]! else e[i]!
  for _ in [0 : L.size + 1] do
    if same cur tgt then
      s.restore
      return some (used.map (L[·]!))
    let mut stepped := false
    for i in [0 : L.size] do
      if used.contains i then continue
      let y := L[i]!
      unless y.getAppFn.constName? == some Q.pname && y.getAppNumArgs == Q.tys.size do continue
      let ya ← y.getAppArgs.mapM instantiateMVars
      unless same (Q.mov.map (ya[·]!)) cur do continue
      let m2 ← (wgMissTys Q).mapM fun ty => mkFreshExprMVar (some ty)
      let en ← (wgEnC Q ya m2).mapM instantiateMVars
      if (keepC cur en).any (·.hasExprMVar) then continue
      used := used.push i
      cur := keepC cur en
      stepped := true
      break
    unless stepped do
      let some (S, us, js) ← wgCellAt Q L used (some cur) false | break
      for j in Q.cst do
        let _ ← isDefEq S[j]! cur[j]!
      let S ← S.mapM instantiateMVars
      let nx := keepC cur (← (← wgCellNext Q S us).mapM instantiateMVars)
      if nx.any (·.hasExprMVar) then break
      used := used ++ js
      cur := nx
  s.restore
  return none

def wgPayApply (Q : WgP) (C : Array Expr) (a : Expr) : TacticM Bool := do
  let saved ← getGoals
  let s ← saveState
  let g ← getMainGoal
  let (m, m2) ← withMainContext do
    let t ← instantiateMVars (← g.getType)
    let some (lhs, rhs) := entailHead? t | throwError "wg: goal"
    let inst := t.getAppArgs[0]!
    let mut rest := flatStar lhs #[]
    for c in C do
      match rest.idxOf? c with
      | some i => rest := rest.eraseIdx! i
      | none => throwError "wg: pay atom"
    let mid ← mkAppM ``HProp.hstar #[a, starOf inst rest.toList]
    let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[lhs, mid])
    let m2 ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[mid, rhs])
    pure (m, m2)
  setGoals [m.mvarId!]
  try
    wgRound #[Q] #[]
    unless (← getUnsolvedGoals).isEmpty do throwError "wg: pay open"
    let pf ← instantiateMVars m
    if pf.hasExprMVar then throwError "wg: pay mvar"
    g.assign (← g.withContext do mkAppM ``HProp.himpl_trans #[pf, m2])
    setGoals [m2.mvarId!]
    let _ ← arIntroLhs
    return true
  catch _ =>
    wgBack s
    setGoals saved
    return false

def wgPayEmpty (Q : WgP) (a : Expr) : TacticM Bool := do
  let saved ← getGoals
  let s ← saveState
  try
    let bi := Q.baseIdx
    let pf ← withMainContext do
      let (pf, g) ← wgBranchTo Q a.getAppArgs (starOf Q.inst []) bi
      setGoals [g]
      convClose
      unless (← getUnsolvedGoals).isEmpty do throwError "wg: pay empty"
      instantiateMVars pf
    if pf.hasExprMVar then throwError "wg: pay mvar"
    setGoals saved
    let _ ← arRwLhs [] pf
    return true
  catch _ =>
    wgBack s
    setGoals saved
    return false

def wgLhsAtoms : TacticM (Array Expr) := do
  return (← wgLhs).filter (!·.isAppOf ``HProp.hpure)

partial def wgFoldPath (P : WgP) (st tgt : Array Expr) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then return
  let same := fun (a b : Array Expr) => (Array.range a.size).all fun i => P.cst.contains i || a[i]! == b[i]!
  let keepC := fun (c e : Array Expr) => (Array.range e.size).map fun i => if P.cst.contains i then c[i]! else e[i]!
  let mut cur := st
  let mut used : Array Expr := #[]
  for _ in [0 : (← wgLhsAtoms).size + 1] do
    if same cur tgt then return
    if ← pastGlobal then return
    let L ← wgLhsAtoms
    let segStep ← withMainContext do
      for y in L do
        if used.contains y then continue
        unless y.getAppFn.constName? == some P.pname && y.getAppNumArgs == P.tys.size do continue
        let ya ← y.getAppArgs.mapM instantiateMVars
        unless same (P.mov.map (ya[·]!)) cur do continue
        let s ← saveState
        let m2 ← (wgMissTys P).mapM fun ty => mkFreshExprMVar (some ty)
        let en ← (keepC cur (wgEnC P ya m2)).mapM instantiateMVars
        s.restore
        if en.any (·.hasExprMVar) then continue
        return some (y, en)
      return none
    if let some (y, en) := segStep then
      used := used.push y
      cur := en
      continue
    let cellStep ← withMainContext do
      let s ← saveState
      let usedIdx := (Array.range L.size).filter fun i => used.contains L[i]!
      let some (S, us, js) ← wgCellAt P L usedIdx (some cur) false none true | return none
      for j in P.cst do
        let _ ← isDefEq S[j]! cur[j]!
      let S ← S.mapM instantiateMVars
      let us ← us.mapM instantiateMVars
      let nx := keepC cur (← (← wgCellNext P S us).mapM instantiateMVars)
      let items := (flatStar (P.preLam.beta (S ++ us)) #[]).filter fun it =>
        !it.isAppOf ``HProp.hsingle && !it.isAppOf ``HProp.hpure
      let items ← items.mapM instantiateMVars
      let cells := js.map (L[·]!)
      s.restore
      if nx.any (·.hasExprMVar) then return none
      return some (cells, items, nx)
    let some (cells, items, nx) := cellStep | return
    used := used ++ cells
    for a in items do
      if a.hasExprMVar then continue
      if (← wgLhsAtoms).contains a then
        used := used.push a
        continue
      let some q := a.getAppFn.constName? | continue
      if q == P.pname then continue
      let some Q ← wgPOf q | continue
      let xs := a.getAppArgs
      unless xs.size == Q.tys.size do continue
      let tq ← withMainContext do
        let s ← saveState
        let miss ← (wgMissTys Q).mapM fun ty => mkFreshExprMVar (some ty)
        let r ← (wgEnC Q xs miss).mapM instantiateMVars
        s.restore
        pure r
      if tq.any (·.hasExprMVar) then continue
      wgFoldPath Q (Q.mov.map (xs[·]!)) tq (fuel - 1)
      let L2 ← wgLhsAtoms
      let some C ← wgPayChain Q L2 a | continue
      let ok ← if C.isEmpty then wgPayEmpty Q a else wgPayApply Q C a
      if ok then used := used.push a
    cur := nx

def wgFoldPayloads (cands : Array WgP) : TacticM Bool := do
  let before ← wgLhs
  unless before.any (·.isAppOf ``HProp.hsingle) do return false
  unless ← cands.anyM (fun P => do return !(← wgPayPreds P).isEmpty) do return false
  let R ← withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (_, rhs) := entailHead? t | throwError "wg: goal"
    let (body, _) ← arOpen rhs
    pure (flatStar body #[])
  let n := before.size
  for r in R do
    let some q := r.getAppFn.constName? | continue
    let some P := cands.find? (·.pname == q) | continue
    if (← wgPayPreds P).isEmpty then continue
    let xs ← r.getAppArgs.mapM instantiateMVars
    unless xs.size == P.tys.size do continue
    let tq ← withMainContext do
      let s ← saveState
      let miss ← (wgMissTys P).mapM fun ty => mkFreshExprMVar (some ty)
      let t ← (wgEnC P xs miss).mapM instantiateMVars
      s.restore
      pure t
    if tq.any (·.hasExprMVar) || xs.any (·.hasExprMVar) then continue
    wgFoldPath P (P.mov.map (xs[·]!)) tq n
  return (← wgLhs) != before

def wgPassBody (cands : Array WgP) : TacticM Unit := do
  try wgRound cands #[]
  catch e =>
    let s ← saveState
    let folded ← try wgFoldPayloads cands catch _ => do
      wgBack s
      pure false
    if folded then
      try
        let rest ← withMainContext do
          let t ← instantiateMVars (← (← getMainGoal).getType)
          let some (lhs, rhs) := entailHead? t | throwError "wg: goal"
          wgCands (flatStar lhs #[] ++ flatStar rhs #[])
        wgRound rest #[]
        return
      catch _ => wgBack s
    let s2 ← saveState
    if ← (try wgUnfoldHelpers catch _ => pure false) then
      try
        let rest ← withMainContext do
          let t ← instantiateMVars (← (← getMainGoal).getType)
          let some (lhs, rhs) := entailHead? t | throwError "wg: goal"
          let (body, _) ← arOpen rhs
          wgCands (flatStar lhs #[] ++ flatStar body #[])
        wgRound rest #[]
        return
      catch _ => wgBack s2
    throw e

def wgPass : TacticM Unit := do
  unless ← wgUnfoldHelpers true do
    let exL ← withMainContext do
      let t ← instantiateMVars (← (← getMainGoal).getType)
      let some (lhs, _) := entailHead? t | return false
      return (flatStar lhs #[]).any (·.isAppOf ``HProp.hexists)
    if exL then
      let _ ← arIntroLhs
  let (L, R) ← withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    if t.hasExprMVar then throwError "wg: mvars"
    let some (lhs, rhs) := entailHead? t | throwError "wg: not an entailment"
    let (body, _) ← arOpen rhs
    pure (flatStar lhs #[], flatStar body #[])
  let cands ← wgCands (L ++ R)
  if cands.isEmpty then throwError "wg: no predicate"
  if ← wgEntry then return
  let gd ← globalDeadline.get
  let now ← vclock
  globalDeadline.set (now + (gd - now) * cands.size / (cands.size + 1))
  try wgPassBody cands finally globalDeadline.set gd

elab "xsearch_wseg" : tactic => wgPass

partial def rhsVars (heads : Array Name) (e : Expr) (acc : Array Expr) :
    Array Expr :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) => rhsVars heads b (rhsVars heads a acc)
  | (``HProp.hexists, args) =>
      match args.back? with
      | some (.lam _ _ b _) => rhsVars heads b acc
      | _ => acc
  | (``HProp.hsingle, args) =>
      if args.size < 2 then acc else
      let l := args[args.size-2]!
      if l.isFVar then acc.push l else acc
  | _ =>
      match e.getAppFn.constName? with
      | some n =>
          if heads.contains n then
            let xs := e.getAppArgs
            if xs.any (fun y => y != xs[0]!) then
              xs.foldl (fun a y => if y.isFVar then a.push y else a) acc
            else acc
          else acc
      | none => acc

elab "xsearch_macros" : tactic => withMainContext do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let heads := entries.map (·.headFn)
  let mut ms : Array Name := #[]
  let mut ls : Array Name := #[]
  let mut rs : Array Name := #[]
  for e in entries do
    let ty := (← getConstInfo e.lemmaName).type
    let k ← forallTelescopeReducing ty fun _ concl => do
      match concl.eq? with
      | some (_, _, body) =>
          if isHorConst body then pure 0
          else if (collectOccs heads body #[]).isEmpty then pure 2
          else if ← isRecPred e.headFn then pure 0
          else pure 1
      | none => pure 0
    let det ← forallTelescopeReducing ty fun _ concl => do
      match concl.eq? with
      | some (_, _, body) =>
          let (bd, n) := exPeel body
          pure ((List.range n).all (fun i => bvarDetermined bd i))
      | none => pure false
    if k == 2 && !ms.contains e.headFn then ms := ms.push e.headFn
    if k == 1 && !ls.contains e.headFn then ls := ls.push e.headFn
    if det && !rs.contains e.headFn then rs := rs.push e.headFn
  for _ in [0 : 24] do
    if ← pastGlobal then return ()
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let mut occ : Option Expr := (collectOccs ms t #[])[0]?
    if occ.isNone then
      match entailHead? t with
      | some (lhs, rhs) =>
          let lsOk := ls.filter (fun n => (collectOccs #[n] rhs #[]).isEmpty)
          occ := (collectOccs lsOk lhs #[])[0]?
          if occ.isNone then
            let rsOk := ls.filter (fun n =>
              (collectOccs #[n] lhs #[]).isEmpty && rs.contains n)
            occ := (collectOccs rsOk rhs #[])[0]?
      | none => pure ()
    match occ with
    | none => return ()
    | some o =>
      unless ← tryTactic (rewriteOcc entries o) do return ()

elab "xsearch_refute" : tactic => withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  match entailHead? t with
  | none => pure ()
  | some (lhs, rhs) =>
    let heads := (xsearchUnfoldExt.getState (← getEnv)).map (·.headFn)
    for v in rhsVars heads rhs #[] do
      if (lhs.find? (· == v)).isNone then
        throwError "xsearch: unconstrained rhs variable"

elab "xsearch_start" : tactic => do
  globalDeadline.set ((← vclock) + 6000)
  bodySigCache.set #[]
  unfoldBudget.set 8
  failMemo.set {}
  forcedDepth.set 0
  lemBuilding.set false
  invCache.set #[]
  cmPending.set false
  flatPredCache.set #[]
  invDCache.set #[]
  minCellCache.set #[]
  recPredCache.set #[]
  wgPCache.set #[]
  wgPGCache.set #[]
  wgLCache.set #[]
  wgUsedCache.set #[]
  wgMCache.set #[]

elab "xsearch_backtrack" : tactic => do
  searchDeadline.set (← globalDeadline.get)
  searchNodes.set 20000
  searchSolve 40

elab "xsearch_cmodel" : tactic => do
  if ← (try cmFind catch _ => pure false) then
    throwError "xsearch: countermodel"

def fastHopeless : TacticM Bool := withMainContext do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let allFns := entries.map (·.headFn)
  let t ← instantiateMVars (← (← getMainGoal).getType)
  if t.hasMVar then return false
  let some (lhs, rhs) := entailHead? t | return false
  let L0 := Sep.Xsimpl.parseHstar lhs
  let R0 := Sep.Xsimpl.parseHstar rhs
  if L0.length + R0.length < 8 then return false
  unless (L0 ++ R0).all (fun e => match e.getAppFn.constName? with
      | some n => allFns.contains n
      | none => false) do return false
  let mut L := L0
  let mut R : List Expr := []
  for r in R0 do
    if L.contains r then L := L.erase r else R := R ++ [r]
  if R.isEmpty || L.isEmpty then return false
  for (mine, other) in [(L, R), (R, L)] do
    for x in mine do
      let some hd := x.getAppFn.constName? | return false
      let (bh, sg) ← bodySig entries hd
      unless bh do return false
      if ← other.anyM (fun r => liftM (horPartner entries sg r)) then return false
  return true

elab "xsearch_fastgate" : tactic => do
  if ← fastHopeless then throwError "xsearch: fast path hopeless"

def hasPredAtom : TacticM Bool := withMainContext do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let allFns := entries.map (·.headFn)
  let t ← instantiateMVars (← (← getMainGoal).getType)
  return (t.find? fun e => match e with
    | .const n _ => allFns.contains n
    | _ => false).isSome

syntax "xsearch_scope " tactic : tactic
elab_rules : tactic
  | `(tactic| xsearch_scope $t) => do
    simpOnlyCache.set #[]
    let cheap ← hasPredAtom
    withEnableInfoTree false
      (if cheap then Sep.Xsimpl.withCheapCancel (evalTactic t) else evalTactic t)

elab "xsearch_witness" : tactic => do
  witEnum (do evalTactic (← `(tactic| first
    | (xsearch_fastgate
       xsimpl_core_with xsearch_unfold_step
       all_goals (try xsimpl_clean)
       xsearch_pure
       done)
    | (xsearch_wseg
       first
       | done
       | xsearch_backtrack)
    | xsearch_backtrack)))

def witResidual : TacticM (Array Expr) := do
  let _ ← arOpenGoal
  withMainContext do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some (lhs, rhs) := entailHead? t | return #[]
    let L := (flatStar lhs #[]).filter (!·.isAppOf ``HProp.hpure)
    let R := (flatStar rhs #[]).filter (fun r => !r.isAppOf ``HProp.hpure && r.hasExprMVar)
    let mut used : Array Nat := #[]
    for r in R do
      for j in [0 : L.size] do
        if used.contains j || L[j]!.getAppFn != r.getAppFn then continue
        let s ← saveState
        if ← (try checkpointDefEq (isDefEq r L[j]!) catch _ => pure false) then
          used := used.push j
          break
        s.restore
    let mut res : Array Expr := #[]
    for c0 in pureProps (← instantiateMVars rhs) #[] do
      for c in pureConjs c0 #[] do
        let c ← instantiateMVars c
        if c.hasExprMVar then continue
        let m ← mkFreshExprSyntheticOpaqueMVar c
        let s ← saveState
        let closed ← (try (do wgCloseGoal m.mvarId!; pure true) catch _ => pure false)
        s.restore
        unless closed || res.contains c do res := res.push c
    return res

def witCaseTuples : TacticM (Array (Array Expr)) := withMainContext do
  let s ← saveState
  let t ← instantiateMVars (← (← getMainGoal).getType)
  if t.hasExprMVar then throwError "wit: mvars"
  let some (lhs, rhs) := entailHead? t | throwError "wit: goal"
  let (body, ms) ← arOpen rhs
  if ms.isEmpty then throwError "wit: no binder"
  let Rs := (flatStar body #[]).filter (!·.isAppOf ``HProp.hpure)
  let Ls := (flatStar lhs #[]).filter (!·.isAppOf ``HProp.hpure)
  let mut roots : Array Expr := #[]
  for x in Ls do
    if let some r := x.getAppArgs[0]? then
      if (← isDefEq (← inferType r) (mkConst ``Nat)) && !roots.contains r then roots := roots.push r
  let cands := roots.push (mkNatLit 0)
  let mut out : Array (Array Expr) := #[#[]]
  for m in ms do
    unless (← isDefEq (← inferType m) (mkConst ``Nat)) && Rs.any (fun r => r.getAppArgs.contains m) do break
    let mut nxt : Array (Array Expr) := #[]
    for pre in out do
      for c in cands do nxt := nxt.push (pre.push c)
    out := nxt
  s.restore
  if out.all (·.isEmpty) then throwError "wit: no location binder"
  return out

def witCaseEngine : TacticM Unit := do
  evalTactic (← `(tactic| first
    | (xsearch_fastgate
       xsimpl_core_with xsearch_unfold_step
       all_goals (try xsimpl_clean)
       xsearch_pure
       done)
    | (xsearch_wseg
       first
       | done
       | xsearch_backtrack)
    | xsearch_backtrack))
  unless (← getUnsolvedGoals).isEmpty do throwError "wit: case open"

partial def witCaseRun (tuples : Array (Array Expr)) : TacticM Unit := do
  let g ← getMainGoal
  let mut res : Array (Array Expr × Array Expr) := #[]
  for tp in tuples do
    if ← pastGlobal then break
    let s ← saveState
    let rs ← try (do witInst tp; witResidual) catch _ => pure #[]
    s.restore
    unless rs.isEmpty do res := res.push (tp, rs)
  if res.isEmpty then throwError "wit: no case"
  let disj ← withMainContext do
    let cs ← res.mapM fun (_, rs) => wgConj rs
    let mut d := cs.back!
    for i' in [0 : cs.size - 1] do
      d ← mkAppM ``Or #[cs[cs.size - 2 - i']!, d]
    pure d
  let _ ← withMainContext (wgSide disj)
  let mut cur := g
  let gd ← globalDeadline.get
  for i in [0 : res.size] do
    let (tp, rs) := res[i]!
    let now ← vclock
    globalDeadline.set (now + (gd - now) / (res.size - i))
    if i + 1 == res.size then
      setGoals [cur]
      witInst tp
      try witCaseEngine finally globalDeadline.set gd
      return
    let c ← cur.withContext (wgConj rs)
    let (yes, no) ← cur.byCases c
    setGoals [yes.mvarId]
    witInst tp
    try witCaseEngine finally globalDeadline.set gd
    cur := no.mvarId
  throwError "wit: case end"

elab "xsearch_witcase" : tactic => do
  let entries ← arEntries
  let heads := entries.map (·.headFn)
  let occs := (← wgLhs).filter fun x => match x.getAppFn.constName? with
    | some n => heads.contains n
    | none => false
  for o in occs do
    if ← pastGlobal then break
    let s ← saveState
    try
      rewriteOcc entries o
      let leaves ← wgSplitDisj
      for leaf in leaves do
        setGoals [leaf]
        if ← wgFalseClose then continue
        let tuples ← witCaseTuples
        witCaseRun tuples
      if (← getUnsolvedGoals).isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "wit: no case split"

syntax "xsearch" : tactic
macro_rules
  | `(tactic| xsearch) => `(tactic| xsearch_scope (
      xsearch_refute
      xsearch_cmodel
      xsearch_start
      first
      | (xsearch_fastgate
         xsimpl_core_with xsearch_unfold_step
         all_goals (try xsimpl_clean)
         xsearch_pure
         done)
      | (try xsearch_eqsubst
         try xsearch_trivpure
         try xsearch_macros
         try xsearch_trivpure
         try xsearch_exwit
         try xsearch_pfacts
         try xsearch_facts
         first
         | done
         | (xsearch_wseg
            first
            | done
            | xsearch_backtrack)
         | xsearch_witness
         | xsearch_backtrack
         | xsearch_witcase)))

-- # EVOLVE-BLOCK-END

end Sep.Xsearch
