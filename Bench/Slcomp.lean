import Bench.Encode
import Bench.SmtLib.Parser

open Lean Elab Command

namespace Bench.Slcomp

open Bench.SmtLib Bench.Encode

initialize genCounter : IO.Ref Nat ← IO.mkRef 0

def freshNamespace (path : System.FilePath) : CommandElabM Name := do
  let n ← genCounter.modifyGet (fun n => (n, n + 1))
  let base := sanitize (path.fileName.getD "prob")
  return `Bench.Slcomp.Gen ++ Name.mkSimple s!"g{n}_{base}"

def buildCtx (ns : Name) (p : Problem) : CommandElabM Ctx := do
  let mut ctors : Std.HashMap String (Array Field) := {}
  for d in p.datatypes do
    for c in d.constructors do
      ctors := ctors.insert c.name c.fields
  let mut preds : Std.HashMap String (Array Binder) := {}
  for d in p.funDefs do
    preds := preds.insert d.name d.params
  return { ctors, preds, ns }

def predArgIdents (d : FunDef) : Array Ident :=
  d.params.map (fun b => varIdent b.name)

open Meta in
partial def monoPf (inst X Y hXY : Expr) (e : Expr) : MetaM Expr := do
  if !e.containsFVar X.fvarId! then return mkApp2 (mkConst ``HProp.himpl_refl) inst e
  if e.getAppFn == X && e.getAppNumArgs == 1 then return mkApp hXY e.appArg!
  let sub := fun (t : Expr) => t.replaceFVar X Y
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) =>
      return mkApp7 (mkConst ``HProp.himpl_frame_lr) inst a (sub a) b (sub b)
        (← monoPf inst X Y hXY a) (← monoPf inst X Y hXY b)
  | (``Bench.hor, #[_, a, b]) =>
      return mkApp7 (mkConst ``Bench.hor_mono) inst a b (sub a) (sub b)
        (← monoPf inst X Y hXY a) (← monoPf inst X Y hXY b)
  | (``HProp.hexists, #[_, A, lam]) =>
      if let .lam n t b bi := lam then
        let pf ← withLocalDecl n bi t fun v => do
          mkLambdaFVars #[v] (← monoPf inst X Y hXY (b.instantiate1 v))
        return mkApp5 (mkConst ``HProp.himpl_hexists e.getAppFn.constLevels!) inst A lam (sub lam) pf
      else throwError "mono: exists"
  | _ => throwError "mono: shape"

open Meta in
partial def monoArm (inst X Y hXY : Expr) (e : Expr) : MetaM Expr := do
  match e.getAppFnArgs with
  | (``Sum.elim, #[α, β, _, f, g]) =>
      return mkApp9 (mkConst ``Bench.sumElim_mono) inst α β f (f.replaceFVar X Y) g
        (g.replaceFVar X Y) (← monoArm inst X Y hXY f) (← monoArm inst X Y hXY g)
  | _ =>
    if let .lam n t b bi := e then
      withLocalDecl n bi t fun v => do
        mkLambdaFVars #[v] (← monoPf inst X Y hXY (b.instantiate1 v))
    else throwError "mono: arm"

open Meta in
def monoTerm (F : Expr) : MetaM Expr := do
  let fty ← inferType F
  let xty := fty.bindingDomain!
  let aty := xty.bindingDomain!
  withLocalDeclD `X xty fun X =>
  withLocalDeclD `Y xty fun Y => do
    let hty ← withLocalDeclD `a aty fun a => do
      mkForallFVars #[a] (← mkAppM ``HProp.himpl #[mkApp X a, mkApp Y a])
    withLocalDeclD `hXY hty fun hXY => do
      let body ← whnfCore (mkApp F X)
      let pf ← monoArm xty.bindingBody!.appArg! X Y hXY body
      let pf ← instantiateMVars pf
      mkLambdaFVars #[X, Y, hXY] pf

partial def sumPick (e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``Sum.elim, #[_, _, _, f, g, x]) =>
      match x.getAppFnArgs with
      | (``Sum.inl, #[_, _, y]) => sumPick (f.beta #[y])
      | (``Sum.inr, #[_, _, y]) => sumPick (g.beta #[y])
      | _ => none
  | _ => some e

partial def tupleArgs (n : Nat) (t : Expr) : Array Expr :=
  if n ≤ 1 then #[t] else
  match t.getAppFnArgs with
  | (``Prod.mk, #[_, _, a, b]) => #[a] ++ tupleArgs (n - 1) b
  | _ => #[t]

partial def injIdx (k : Nat) (i : Nat) (t : Expr) : Option (Nat × Expr) :=
  if k ≤ 1 then some (i, t) else
  match t.getAppFnArgs with
  | (``Sum.inl, #[_, _, y]) => some (i, y)
  | (``Sum.inr, #[_, _, y]) => injIdx (k - 1) (i + 1) y
  | _ => none

partial def eqBody (X : Expr) (preds : Array (Name × Nat)) (e : Expr) : Option Expr :=
  match e with
  | .app .. =>
    if e.getAppFn == X then
      match injIdx preds.size 0 (eqBodyD X preds e.appArg!) with
      | some (c, tup) =>
          let (nm, n) := preds[c]!
          let args := tupleArgs n tup
          if args.size == n then some (mkAppN (mkConst nm) args) else none
      | none => none
    else
      match e.getAppFnArgs with
      | (``Prod.fst, #[_, _, t]) =>
          match (eqBodyD X preds t).getAppFnArgs with
          | (``Prod.mk, #[_, _, a, _]) => some a
          | _ => none
      | (``Prod.snd, #[_, _, t]) =>
          match (eqBodyD X preds t).getAppFnArgs with
          | (``Prod.mk, #[_, _, _, b]) => some b
          | _ => none
      | _ =>
        let f := eqBodyD X preds e.getAppFn
        some (mkAppN f (e.getAppArgs.map (eqBodyD X preds)))
  | .lam n t b bi => some (.lam n (eqBodyD X preds t) (eqBodyD X preds b) bi)
  | .forallE n t b bi => some (.forallE n (eqBodyD X preds t) (eqBodyD X preds b) bi)
  | .mdata m b => some (.mdata m (eqBodyD X preds b))
  | .proj s i b =>
      match (eqBodyD X preds b).getAppFnArgs, i with
      | (``Prod.mk, #[_, _, a, _]), 0 => some a
      | (``Prod.mk, #[_, _, _, c]), 1 => some c
      | _, _ => some (.proj s i (eqBodyD X preds b))
  | _ => some e
where
  eqBodyD (X : Expr) (preds : Array (Name × Nat)) (e : Expr) : Expr :=
    (eqBody X preds e).getD e

open Meta in
def deriveEq (F M : Name) (preds : Array (Name × Nat)) (i : Nat) :
    MetaM (Option (Expr × Expr)) := do
  let (pn, _) := preds[i]!
  let pv := (← getConstInfo pn).value!
  let pty := (← getConstInfo pn).type
  let fv := (← getConstInfo F).value!
  forallTelescope pty fun ids _ => do
    let body := pv.beta ids
    unless body.isAppOfArity ``Bench.lfp 4 do return none
    let t := body.appArg!
    let fty ← inferType (mkConst F)
    withLocalDeclD `X fty.bindingDomain! fun X => do
      let some arm := sumPick (fv.beta #[X, t]) | return none
      let rhs := (eqBody X preds arm).getD arm
      if rhs.containsFVar X.fvarId! then return none
      let lhs := mkAppN (mkConst pn) ids
      let ty ← mkForallFVars ids (← mkEq lhs rhs)
      let un ← mkAppM ``Bench.lfp_unfold #[mkConst F, mkConst M]
      let pf ← mkLambdaFVars ids (← mkAppM ``congrFun #[un, t])
      return some (ty, pf)

def elabClosed (stx : Syn) (ty? : Option Expr) : TermElabM Expr := do
  let e ← Term.withoutErrToSorry (Term.elabTermEnsuringType stx ty?)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasMVar then throwError "emit: unassigned metavariables"
  return e

def addDefn (n : Name) (ty val : Expr) : TermElabM Unit := do
  let h := getMaxHeight (← getEnv) val + 1
  let dv : DefinitionVal :=
    { name := n, levelParams := [], type := ty, value := val,
      hints := ReducibilityHints.regular h, safety := DefinitionSafety.safe }
  addDecl (Declaration.defnDecl dv)

def addThm (n : Name) (ty val : Expr) : TermElabM Unit := do
  let tv : TheoremVal := { name := n, levelParams := [], type := ty, value := val }
  addDecl (Declaration.thmDecl tv)

structure SynParts where
  fTy : Syn
  fBody : Syn
  preds : Array (Ident × Syn × Syn)
  eqs : Array (Ident × Syn × Syn)

def synParts (c : Ctx) (ds : Array FunDef) (group : Std.HashMap String Nat) :
    CommandElabM SynParts := do
  let k := ds.size
  let mut argTys := #[]
  for d in ds do
    argTys := argTys.push (← argsType c d.params)
  let mut argsT := argTys[k - 1]!
  for i in [0 : k - 1] do
    argsT ← `($(argTys[k - 2 - i]!) ⊕ $argsT)
  let X := mkIdent (Name.mkSimple "X_slcomp")
  let pv := mkIdent (Name.mkSimple "p_slcomp")
  let mut arms := #[]
  for i in [0 : k] do
    let d := ds[i]!
    let n := d.params.size
    let mut projSubst : Std.HashMap String Syn := {}
    for j in [0 : n] do
      projSubst := projSubst.insert d.params[j]!.name (← projTerm pv j n)
    let cF := { c with group, groupSize := k, subst := projSubst }
    arms := arms.push (← spatial cF (some X) d.body)
  let mut fBody ← `(fun $pv:ident => $(arms[k - 1]!))
  for i in [0 : k - 1] do
    let arm ← `(fun $pv:ident => $(arms[k - 2 - i]!))
    fBody ← `(Sum.elim $arm $fBody)
  fBody ← `(fun $X:ident => $fBody)
  let fId := funIdent c ds[0]!.name
  let mId := monoIdent c ds[0]!.name
  let fTy ← `(($argsT → HProp) → $argsT → HProp)
  let mut tups := #[]
  let mut idss := #[]
  let mut sortss := #[]
  for i in [0 : k] do
    let d := ds[i]!
    let n := d.params.size
    let mut sorts := #[]
    for b in d.params do
      sorts := sorts.push (← sortTerm b.sort)
    sortss := sortss.push sorts
    let ids := predArgIdents d
    idss := idss.push ids
    let mut tup : Syn := ids[n - 1]!
    for j in [0 : n - 1] do
      tup ← `(($(ids[n - 2 - j]!), $tup))
    tups := tups.push (← injTerm i k tup)
  let mut preds := #[]
  for i in [0 : k] do
    let d := ds[i]!
    let n := d.params.size
    let sorts := sortss[i]!
    let ids := idss[i]!
    let mut predTy ← `(HProp)
    for s in sorts.reverse do
      predTy ← `($s → $predTy)
    let mut lam ← `(Bench.lfp $fId $(tups[i]!))
    for j in [0 : n] do
      lam ← `(fun $(ids[n - 1 - j]!):ident => $lam)
    preds := preds.push (predIdent c d.name, predTy, lam)
  let cB := { c with emitted := ds.foldl (fun e d => e.insert d.name) c.emitted, subst := {} }
  let mut eqs := #[]
  for i in [0 : k] do
    let d := ds[i]!
    let n := d.params.size
    let sorts := sortss[i]!
    let ids := idss[i]!
    let bodyB ← spatial cB none d.body
    let mut eqTy ← `($(Syntax.mkApp (predIdent c d.name) ids) = $bodyB)
    let mut eqPf ← `(congrFun (Bench.lfp_unfold $fId $mId) $(tups[i]!))
    for j in [0 : n] do
      let l := n - 1 - j
      eqTy ← `(∀ $(ids[l]!):ident : $(sorts[l]!), $eqTy)
      eqPf ← `(fun ($(ids[l]!):ident : $(sorts[l]!)) => $eqPf)
    eqs := eqs.push (eqIdent c d.name, eqTy, eqPf)
  return { fTy, fBody, preds, eqs }

def arrowName : TermElabM Name := do
  return (← elabClosed (← `(Nat → Nat)) none).bindingName!

def emitComponent (c : Ctx) (ds : Array FunDef) : CommandElabM Ctx := do
  for d in ds do
    if d.params.size == 0 then unsupported s!"nullary predicate {d.name}"
  let k := ds.size
  let mut group : Std.HashMap String Nat := {}
  for i in [0 : k] do
    group := group.insert ds[i]!.name i
  let fId := funIdent c ds[0]!.name
  let mId := monoIdent c ds[0]!.name
  let cB := { c with emitted := ds.foldl (fun e d => e.insert d.name) c.emitted, subst := {} }
  let pnames : Array (Name × Nat) :=
    ds.map (fun d => ((predIdent c d.name).getId, d.params.size))
  let mut syn : Option SynParts := none
  let directOk ← liftTermElabM do
    match directF c ds group (← arrowName) with
    | some (fT, fV) => addDefn fId.getId fT fV; pure true
    | none => pure false
  unless directOk do
    let sp ← synParts c ds group
    syn := some sp
    liftTermElabM do
      let fT ← elabClosed sp.fTy none
      addDefn fId.getId fT (← elabClosed sp.fBody (some fT))
  let monoOk ← liftTermElabM do
    let F := mkConst fId.getId
    try
      addThm mId.getId (← Meta.mkAppM ``Bench.Mono #[F])
        (← monoTerm (← getConstInfo fId.getId).value!)
      pure true
    catch _ => pure false
  unless monoOk do
    elabCommand (← `(command| theorem $mId : Bench.Mono $fId := by unfold $fId:ident; hmono))
  let predsOk ← liftTermElabM do
    let an ← arrowName
    let ps := (List.range k).toArray.map (fun i => directPred ds i fId.getId an)
    unless ps.all Option.isSome do return false
    for i in [0 : k] do
      let some (pT, pV) := ps[i]! | return false
      addDefn pnames[i]!.1 pT pV
    return true
  unless predsOk do
    let sp ← match syn with
      | some sp => pure sp
      | none => synParts c ds group
    syn := some sp
    liftTermElabM do
      for (nm, ty, lam) in sp.preds do
        let pT ← elabClosed ty none
        addDefn nm.getId pT (← elabClosed lam (some pT))
  let eqsOk ← liftTermElabM do
    let mut out := #[]
    for i in [0 : k] do
      match ← deriveEq fId.getId mId.getId pnames i with
      | some r => out := out.push r
      | none => return false
    for i in [0 : k] do
      let nm := (eqIdent c ds[i]!.name).getId
      addThm nm out[i]!.1 out[i]!.2
      Attribute.add nm `xsearch_unfold Syntax.missing
    return true
  unless eqsOk do
    let sp ← match syn with
      | some sp => pure sp
      | none => synParts c ds group
    liftTermElabM do
      let mut i := 0
      for (nm, ty, pf) in sp.eqs do
        match ← deriveEq fId.getId mId.getId pnames i with
        | some (dTy, dPf) => addThm nm.getId dTy dPf
        | none =>
          let eT ← elabClosed ty none
          addThm nm.getId eT (← elabClosed pf none)
        Attribute.add nm.getId `xsearch_unfold Syntax.missing
        i := i + 1
  return cB

def components (ds : Array FunDef) (preds : Std.HashMap String (Array Binder)) :
    Array (Array FunDef) := Id.run do
  let n := ds.size
  let mut reach : Array (Array Bool) := Array.replicate n (Array.replicate n false)
  for i in [0 : n] do
    let refs := predRefs preds ds[i]!.body {}
    for j in [0 : n] do
      if refs.contains ds[j]!.name then
        reach := reach.set! i (reach[i]!.set! j true)
  for m in [0 : n] do
    for i in [0 : n] do
      if reach[i]![m]! then
        for j in [0 : n] do
          if reach[m]![j]! then
            reach := reach.set! i (reach[i]!.set! j true)
  let mut comp : Array Nat := Array.replicate n 0
  let mut assigned : Array Bool := Array.replicate n false
  let mut comps : Array (Array Nat) := #[]
  for i in [0 : n] do
    if !assigned[i]! then
      let mut mem := #[i]
      assigned := assigned.set! i true
      comp := comp.set! i comps.size
      for j in [i + 1 : n] do
        if !assigned[j]! && reach[i]![j]! && reach[j]![i]! then
          mem := mem.push j
          assigned := assigned.set! j true
          comp := comp.set! j comps.size
      comps := comps.push mem
  let mut done : Array Bool := Array.replicate comps.size false
  let mut out : Array (Array FunDef) := #[]
  for _ in [0 : comps.size] do
    let mut chosen : Option Nat := none
    for ci in [0 : comps.size] do
      if chosen.isNone && !done[ci]! then
        let mut ready := true
        for i in comps[ci]! do
          for j in [0 : n] do
            if reach[i]![j]! && comp[j]! != ci && !done[comp[j]!]! then
              ready := false
        if ready then chosen := some ci
    match chosen with
    | none =>
        for ci in [0 : comps.size] do
          if !done[ci]! then
            done := done.set! ci true
            out := out.push (comps[ci]!.map (ds[·]!))
    | some ci =>
        done := done.set! ci true
        out := out.push (comps[ci]!.map (ds[·]!))
  return out

def goalType (c : Ctx) (p : Problem) : CommandElabM (Syn × Array Ident) := do
  let some (lhsT, rhsT) := p.entailment
    | unsupported "problem is not a two-assert entailment"
  let lhs ← spatial c none lhsT
  let rhs ← spatial c none rhsT
  let mut ty ← `(HProp.himpl $lhs $rhs)
  let consts := p.consts
  let mut ids := #[]
  for b in consts do
    ids := ids.push (varIdent b.name)
  for i in [0 : consts.size] do
    let j := consts.size - 1 - i
    ty ← `(∀ $(ids[j]!):ident : $(← sortTerm consts[j]!.sort), $ty)
  return (ty, ids)

def goalCommand (c : Ctx) (p : Problem) (name : Ident) : CommandElabM (TSyntax `command) := do
  let (ty, ids) ← goalType c p
  if ids.isEmpty then
    `(command| theorem $name : $ty := by xsearch)
  else
    `(command| theorem $name : $ty := by intro $[$ids:ident]*; xsearch)

def proveGoal (c : Ctx) (p : Problem) (name : Ident) : CommandElabM Unit := do
  let ids := p.consts.map (fun b => varIdent b.name)
  let direct := match p.entailment with
    | some (l, r) => directGoal c l r p.consts
    | none => none
  let tyS? ← match direct with
    | some _ => pure none
    | none => pure (some (← goalType c p).1)
  let tac ← if ids.isEmpty then `(tactic| xsearch)
    else `(tactic| (intros $[$ids:ident]*; xsearch))
  liftTermElabM do
    let ty ← match direct, tyS? with
      | some ty, _ => pure ty
      | none, some tyS => elabClosed tyS none
      | none, none => throwError "emit: goal"
    let pf := ShareCommon.shareCommon' (← elabClosed (← `(by $tac:tactic)) (some ty))
    if pf.hasSorry then throwError "xsearch: proof contains sorry"
    addThm name.getId ty pf

def oneLine (s : String) : String :=
  let s := s.replace "\n" " " |>.replace "\t" " "
  let s := s.trimAscii.toString
  if s.length > 240 then String.ofList (s.toList.take 240) else s

def hasSub (hay needle : String) : Bool := (hay.splitOn needle).length > 1

def stripPrefix (s : String) : String :=
  match (s.splitOn unsupportedPrefix) with
  | _ :: rest => oneLine (String.intercalate unsupportedPrefix rest)
  | [] => s

def isTimeoutMsg (s : String) : Bool :=
  hasSub s "deterministic) timeout" ||
  hasSub s "maximum number of heartbeats"

def newErrorTexts (before : MessageLog) : CommandElabM (Array String) := do
  let after := (← get).messages
  let old := before.toList.length
  let fresh := after.toList.drop old
  let mut out := #[]
  for m in fresh do
    if m.severity == .error then
      out := out.push (oneLine (← m.data.toString))
  modify fun st => { st with messages := before }
  return out

def runDecls (cmds : CommandElabM Unit) : CommandElabM (Array String) := do
  let before := (← get).messages
  try
    cmds
  catch e =>
    let txt := oneLine (← e.toMessageData.toString)
    let _ ← newErrorTexts before
    return #[txt]
  newErrorTexts before

def runProblem (path : System.FilePath) (timeoutMs : Nat) :
    CommandElabM (String × Nat × String) := do
  let t0 ← IO.monoMsNow
  let result ← try
      pure (← Parser.parseFile path)
    catch e => pure (.error (oneLine (← e.toMessageData.toString)))
  match result with
  | .error err => return ("parse-error", (← IO.monoMsNow) - t0, oneLine err)
  | .ok prob =>
    let hb := max 1 (timeoutMs * 200)
    let run : CommandElabM (String × String) :=
      withScope (fun sc => { sc with opts := ((sc.opts.insert `maxHeartbeats (.ofNat hb)).insert `Elab.async (.ofBool false)).insert `maxRecDepth (.ofNat 4000) }) do
        let ns ← freshNamespace path
        let ctx0 ← buildCtx ns prob
        let goalId := mkIdent (ns ++ `goal)
        let declErrs ← runDecls do
          let mut c := ctx0
          for comp in components prob.funDefs ctx0.preds do
            c := ← emitComponent c comp
          proveGoal c prob goalId
        if declErrs.isEmpty then
          return ("proved", "")
        else
          let msg := declErrs[0]!
          if isTimeoutMsg msg then
            return ("timeout", msg)
          else if hasSub msg unsupportedPrefix then
            return ("unsupported", stripPrefix msg)
          else if msg.startsWith "unsolved goals" || hasSub msg "xsimpl"
              || hasSub msg "xsearch" || hasSub msg "unsolved goals" then
            return ("failed", msg)
          else
            return ("failed", msg)
    let (outcome, reason) ← try run catch e => do
      let txt := oneLine (← e.toMessageData.toString)
      if isTimeoutMsg txt then pure ("timeout", txt)
      else if hasSub txt unsupportedPrefix then pure ("unsupported", stripPrefix txt)
      else pure ("failed", txt)
    return (outcome, (← IO.monoMsNow) - t0, reason)

syntax (name := slcompCmd) "#slcomp_run " str ("(" &"timeout" " := " num ")")? : command

@[command_elab slcompCmd]
def elabSlcomp : CommandElab := fun stx => do
  let path := stx[1].isStrLit?.getD ""
  let timeoutMs :=
    if stx[2].isNone then 10000 else (stx[2][3].isNatLit?.getD 10000)
  let (outcome, ms, reason) ← runProblem path timeoutMs
  logInfo s!"slcomp: {outcome} {ms} {reason}"

def prepare (path : String) : CommandElabM (Ctx × Problem) := do
  let prob ← match ← Parser.parseFile path with
    | .error err => throwError err
    | .ok prob => pure prob
  let ns := `Bench.Slcomp.Gen ++ Name.mkSimple (sanitize ((path : System.FilePath).fileName.getD "prob"))
  let ctx0 ← buildCtx ns prob
  let mut c := ctx0
  let env ← getEnv
  for comp in components prob.funDefs ctx0.preds do
    if comp.all (fun d => env.contains (predIdent c d.name).getId) then
      c := { c with emitted := comp.foldl (fun e d => e.insert d.name) c.emitted }
    else
      c := ← emitComponent c comp
  return (c, prob)

syntax (name := slcompShowCmd) "#slcomp_show " str : command

@[command_elab slcompShowCmd]
def elabSlcompShow : CommandElab := fun stx => do
  let path := stx[1].isStrLit?.getD ""
  let (c, prob) ← prepare path
  logInfo m!"namespace {c.ns}"
  for d in prob.funDefs do
    let eq := eqIdent c d.name
    let info ← liftCoreM <| getConstInfo eq.getId
    let ty ← liftTermElabM <| Meta.ppExpr info.type
    logInfo m!"{d.name}: {ty}"
  let cmd ← goalCommand c prob (mkIdent `goal)
  logInfo m!"{cmd}"

syntax (name := slcompTryCmd) "#slcomp_try " str " by " tacticSeq : command

@[command_elab slcompTryCmd]
def elabSlcompTry : CommandElab := fun stx => do
  let path := stx[1].isStrLit?.getD ""
  let tacs : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨stx[3]⟩
  let (c, prob) ← prepare path
  let (ty, _) ← goalType c prob
  let name := mkIdent (c.ns ++ `goal)
  elabCommand (← `(command| theorem $name : $ty := by $tacs))

end Bench.Slcomp
