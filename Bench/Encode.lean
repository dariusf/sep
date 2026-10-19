import Bench.Fixpoint
import Bench.SmtLib.Ast

open Lean Elab Command

namespace Bench.Encode

open Bench.SmtLib

abbrev Syn := Lean.Term

instance slcompParams : Params where val := Int

def unsupportedPrefix : String := "SLCOMP-UNSUPPORTED: "

def unsupported {α : Type} (msg : String) : CommandElabM α :=
  throwError "{unsupportedPrefix}{msg}"

def sanitize (s : String) : String :=
  String.ofList (s.toList.map fun c =>
    if c.isAlphanum then c else '_')

def varIdent (s : String) : Ident := mkIdent (Name.mkSimple ("v_" ++ sanitize s))

def natLit (n : Nat) : Syn := Syntax.mkNumLit (toString n)

structure Ctx where
  ctors : Std.HashMap String (Array Field) := {}
  preds : Std.HashMap String (Array Binder) := {}
  emitted : Std.HashSet String := {}
  subst : Std.HashMap String Syn := {}
  ns    : Name := Name.anonymous
  group : Std.HashMap String Nat := {}
  groupSize : Nat := 0

def sortTerm : Sort' → CommandElabM Syn
  | .int => `(Int)
  | .named _ => `(Nat)
  | .bool => unsupported "Bool-sorted variable"

def isIntSort : Sort' → Bool
  | .int => true
  | _ => false

def predIdent (c : Ctx) (name : String) : Ident :=
  mkIdent (c.ns ++ Name.mkSimple ("p_" ++ sanitize name))

def funIdent (c : Ctx) (name : String) : Ident :=
  mkIdent (c.ns ++ Name.mkSimple ("f_" ++ sanitize name))

def monoIdent (c : Ctx) (name : String) : Ident :=
  mkIdent (c.ns ++ Name.mkSimple ("m_" ++ sanitize name))

def eqIdent (c : Ctx) (name : String) : Ident :=
  mkIdent (c.ns ++ Name.mkSimple ("e_" ++ sanitize name))

def injTerm (i n : Nat) (t : Syn) : CommandElabM Syn := do
  if n <= 1 then return t
  let mut acc := t
  if i + 1 != n then acc ← `(Sum.inl $acc)
  for _ in [0 : i] do
    acc ← `(Sum.inr $acc)
  return acc

partial def predRefs (preds : Std.HashMap String (Array Binder)) :
    SmtLib.Term → Std.HashSet String → Std.HashSet String
  | .app p args, acc =>
      let acc := if preds.contains p then acc.insert p else acc
      args.foldl (fun a t => predRefs preds t a) acc
  | .pto l _ args, acc => args.foldl (fun a t => predRefs preds t a) (predRefs preds l acc)
  | .sep args, acc | .and args, acc | .or args, acc
  | .eq args, acc | .distinct args, acc
  | .add args, acc | .sub args, acc | .mul args, acc =>
      args.foldl (fun a t => predRefs preds t a) acc
  | .wand l r, acc | .implies l r, acc
  | .lt l r, acc | .le l r, acc | .gt l r, acc | .ge l r, acc =>
      predRefs preds r (predRefs preds l acc)
  | .not t, acc | .neg t, acc => predRefs preds t acc
  | .exists _ b, acc | .forall _ b, acc => predRefs preds b acc
  | .ite a b d, acc => predRefs preds d (predRefs preds b (predRefs preds a acc))
  | .letIn bs b, acc => bs.foldl (fun a (_, t) => predRefs preds t a) (predRefs preds b acc)
  | _, acc => acc

partial def isSpatial (c : Ctx) : SmtLib.Term → Bool
  | .emp | .pto .. | .sep .. | .wand .. => true
  | .app p _ => c.preds.contains p
  | .and args | .or args => args.any (isSpatial c)
  | .exists _ b => isSpatial c b
  | .not t => isSpatial c t
  | _ => false

partial def pureTerm (c : Ctx) (t : SmtLib.Term) : CommandElabM Syn := do
  match t with
  | .var n => return c.subst[n]?.getD (varIdent n)
  | .nil _ => `((0 : Nat))
  | .intLit n =>
      if n < 0 then `((-$(natLit n.natAbs) : Int)) else `(($(natLit n.natAbs) : Int))
  | .true => `(True)
  | .false => `(False)
  | .eq args => do
      if args.size < 2 then `(True) else
      let mut parts := #[]
      for i in [0 : args.size - 1] do
        parts := parts.push (← `($(← pureTerm c args[i]!) = $(← pureTerm c args[i+1]!)))
      conj parts
  | .distinct args => do
      let mut parts := #[]
      for i in [0 : args.size] do
        for j in [i+1 : args.size] do
          parts := parts.push (← `($(← pureTerm c args[i]!) ≠ $(← pureTerm c args[j]!)))
      conj parts
  | .and args => do conj (← args.mapM (pureTerm c))
  | .or args => do disj (← args.mapM (pureTerm c))
  | .not t => do `(¬ $(← pureTerm c t))
  | .implies l r => do `($(← pureTerm c l) → $(← pureTerm c r))
  | .add args => do chain (← args.mapM (pureTerm c)) (fun a b => `($a + $b))
  | .sub args => do
      if args.size == 1 then `(-$(← pureTerm c args[0]!))
      else chain (← args.mapM (pureTerm c)) (fun a b => `($a - $b))
  | .mul args => do chain (← args.mapM (pureTerm c)) (fun a b => `($a * $b))
  | .neg t => do `(-$(← pureTerm c t))
  | .lt l r => do `($(← pureTerm c l) < $(← pureTerm c r))
  | .le l r => do `($(← pureTerm c l) ≤ $(← pureTerm c r))
  | .gt l r => do `($(← pureTerm c l) > $(← pureTerm c r))
  | .ge l r => do `($(← pureTerm c l) ≥ $(← pureTerm c r))
  | .ite a b d => do
      let sa ← pureTerm c a
      let sb ← pureTerm c b
      let sd ← pureTerm c d
      `(if $sa then $sb else $sd)
  | .forall bs b => do
      let mut body ← pureTerm c b
      for bd in bs.reverse do
        body ← `(∀ $(varIdent bd.name):ident : $(← sortTerm bd.sort), $body)
      return body
  | .exists bs b => do
      let mut body ← pureTerm c b
      for bd in bs.reverse do
        body ← `(∃ $(varIdent bd.name):ident : $(← sortTerm bd.sort), $body)
      return body
  | _ => unsupported "non-pure term in pure position"
where
  conj (parts : Array Syn) : CommandElabM Syn := do
    if parts.size == 0 then `(True) else
    let mut acc := parts[parts.size - 1]!
    for i in [0 : parts.size - 1] do
      acc ← `($(parts[parts.size - 2 - i]!) ∧ $acc)
    return acc
  disj (parts : Array Syn) : CommandElabM Syn := do
    if parts.size == 0 then `(False) else
    let mut acc := parts[parts.size - 1]!
    for i in [0 : parts.size - 1] do
      acc ← `($(parts[parts.size - 2 - i]!) ∨ $acc)
    return acc
  chain (parts : Array Syn) (f : Syn → Syn → CommandElabM Syn) : CommandElabM Syn := do
    if parts.size == 0 then unsupported "empty arithmetic application" else
    let mut acc := parts[0]!
    for i in [1 : parts.size] do
      acc ← f acc parts[i]!
    return acc

def valTerm (c : Ctx) (fieldSort : Sort') (t : SmtLib.Term) : CommandElabM Syn := do
  let e ← pureTerm c t
  if isIntSort fieldSort then return e else `((($e : Nat) : Int))

partial def spatial (c : Ctx) (self : Option Ident) (t : SmtLib.Term) :
    CommandElabM Syn := do
  match t with
  | .emp => `(HProp.hempty)
  | .true => `(HProp.hempty)
  | .pto loc ctor args => do
      let some fields := c.ctors[ctor]? | unsupported s!"unknown constructor {ctor}"
      if fields.size != args.size then unsupported s!"arity mismatch for {ctor}"
      let l ← pureTerm c loc
      let mut parts := #[← `(HProp.hpure ($l ≠ 0))]
      for i in [0 : args.size] do
        let v ← valTerm c fields[i]!.sort args[i]!
        let addr ← if i == 0 then pure l else `($l + $(natLit i))
        parts := parts.push (← `(HProp.hsingle $addr $v))
      star parts
  | .sep args => do star (← args.mapM (spatial c self))
  | .and args => do
      let mut parts := #[]
      for a in args do
        if isSpatial c a then parts := parts.push (← spatial c self a)
        else parts := parts.push (← `(HProp.hpure $(← pureTerm c a)))
      star parts
  | .or args => do
      let parts ← args.mapM (spatial c self)
      if parts.size == 0 then `(HProp.hpure False) else
      let mut acc := parts[parts.size - 1]!
      for i in [0 : parts.size - 1] do
        acc ← `(Bench.hor $(parts[parts.size - 2 - i]!) $acc)
      return acc
  | .wand l r => do `(HProp.hwand $(← spatial c self l) $(← spatial c self r))
  | .exists bs b => do
      let mut body ← spatial c self b
      for bd in bs.reverse do
        body ← `(HProp.hexists (fun $(varIdent bd.name):ident : $(← sortTerm bd.sort) => $body))
      return body
  | .app p args => do
      let some params := c.preds[p]? | unsupported s!"unknown predicate {p}"
      if params.size != args.size then unsupported s!"arity mismatch for {p}"
      let argSyns ← (Array.zip params args).mapM fun (b, a) => do
        let e ← pureTerm c a
        if isIntSort b.sort then return e else `(($e : Nat))
      if let some i := c.group[p]? then
        match self with
        | some X => do `($X $(← injTerm i c.groupSize (← tuple argSyns)))
        | none => unsupported s!"self reference to {p} outside its definition"
      else if c.emitted.contains p then
        return Syntax.mkApp (predIdent c p) argSyns
      else
        unsupported s!"mutually recursive or forward-referenced predicate {p}"
  | t => do `(HProp.hpure $(← pureTerm c t))
where
  star (parts : Array Syn) : CommandElabM Syn := do
    if parts.size == 0 then `(HProp.hempty) else
    let mut acc := parts[parts.size - 1]!
    for i in [0 : parts.size - 1] do
      acc ← `(HProp.hstar $(parts[parts.size - 2 - i]!) $acc)
    return acc
  tuple (xs : Array Syn) : CommandElabM Syn := do
    if xs.size == 0 then `(())
    else if xs.size == 1 then return xs[0]!
    else
      let mut acc := xs[xs.size - 1]!
      for i in [0 : xs.size - 1] do
        acc ← `(($(xs[xs.size - 2 - i]!), $acc))
      return acc

section Direct

def instE : Expr := mkConst ``slcompParams

def hpropE : Expr := mkApp (mkConst ``HProp) instE

def natE : Expr := mkConst ``Nat

def sortE? : Sort' → Option Expr
  | .named _ => some natE
  | _ => none

def natLitE (ty : Expr) (n : Nat) : Expr :=
  mkApp3 (mkConst ``OfNat.ofNat [0]) ty (mkRawNatLit n) (mkApp (mkConst ``instOfNatNat) (mkRawNatLit n))

def prodE (a b : Expr) : Expr := mkApp2 (mkConst ``Prod [0, 0]) a b

def sumE (a b : Expr) : Expr := mkApp2 (mkConst ``Sum [0, 0]) a b

def tupleTyE (ts : Array Expr) : Expr := Id.run do
  let mut acc := ts[ts.size - 1]!
  for i in [0 : ts.size - 1] do
    acc := prodE ts[ts.size - 2 - i]! acc
  return acc

def tupleE (ts xs : Array Expr) : Expr := Id.run do
  let n := xs.size
  let mut acc := xs[n - 1]!
  let mut accTy := ts[n - 1]!
  for i in [0 : n - 1] do
    let j := n - 2 - i
    acc := mkApp4 (mkConst ``Prod.mk [0, 0]) ts[j]! accTy xs[j]! acc
    accTy := prodE ts[j]! accTy
  return acc

def sumTyE (tys : Array Expr) (i : Nat) : Expr := Id.run do
  let k := tys.size
  let mut acc := tys[k - 1]!
  for j in [0 : k - 1 - i] do
    acc := sumE tys[k - 2 - j]! acc
  return acc

def injE (tys : Array Expr) (i : Nat) (t : Expr) : Expr := Id.run do
  let k := tys.size
  if k <= 1 then return t
  let mut acc := t
  if i + 1 != k then acc := mkApp3 (mkConst ``Sum.inl [0, 0]) tys[i]! (sumTyE tys (i + 1)) acc
  for m in [0 : i] do
    let j := i - 1 - m
    acc := mkApp3 (mkConst ``Sum.inr [0, 0]) tys[j]! (sumTyE tys (j + 1)) acc
  return acc

def projE (ts : Array Expr) (p : Expr) (i : Nat) : Expr := Id.run do
  let n := ts.size
  if n == 1 then return p
  let tl := fun (m : Nat) => tupleTyE (ts.extract m n)
  let mut acc := p
  for m in [0 : i] do
    acc := mkApp3 (mkConst ``Prod.snd [0, 0]) ts[m]! (tl (m + 1)) acc
  if i + 1 == n then return acc
  return mkApp3 (mkConst ``Prod.fst [0, 0]) ts[i]! (tl (i + 1)) acc

def starE (parts : Array Expr) : Expr := Id.run do
  if parts.size == 0 then return mkApp (mkConst ``HProp.hempty) instE
  let mut acc := parts[parts.size - 1]!
  for i in [0 : parts.size - 1] do
    acc := mkApp3 (mkConst ``HProp.hstar) instE parts[parts.size - 2 - i]! acc
  return acc

def hpureE (p : Expr) : Expr := mkApp2 (mkConst ``HProp.hpure) instE p

structure DCtx where
  c : Ctx
  subst : Std.HashMap String Expr := {}
  bound : Std.HashMap String Expr := {}
  self : Option Expr := none
  groupTys : Array Expr := #[]
  depth : Nat := 0

def DCtx.var? (d : DCtx) (n : String) : Option Expr :=
  match d.subst[n]? with
  | some e => some e
  | none => d.bound[n]?

def valE (d : DCtx) : SmtLib.Term → Option Expr
  | .var n => d.var? n
  | .nil _ => some (natLitE natE 0)
  | _ => none

def conjE (parts : Array Expr) : Expr := Id.run do
  if parts.size == 0 then return mkConst ``True
  let mut acc := parts[parts.size - 1]!
  for i in [0 : parts.size - 1] do
    acc := mkApp2 (mkConst ``And) parts[parts.size - 2 - i]! acc
  return acc

def disjE (parts : Array Expr) : Expr := Id.run do
  if parts.size == 0 then return mkConst ``False
  let mut acc := parts[parts.size - 1]!
  for i in [0 : parts.size - 1] do
    acc := mkApp2 (mkConst ``Or) parts[parts.size - 2 - i]! acc
  return acc

partial def propE (d : DCtx) : SmtLib.Term → Option Expr
  | .true => some (mkConst ``True)
  | .false => some (mkConst ``False)
  | .eq args => do
      if args.size < 2 then return mkConst ``True
      let vs ← args.mapM (valE d)
      let mut parts := #[]
      for i in [0 : vs.size - 1] do
        parts := parts.push (mkApp3 (mkConst ``Eq [1]) natE vs[i]! vs[i+1]!)
      return conjE parts
  | .distinct args => do
      let vs ← args.mapM (valE d)
      let mut parts := #[]
      for i in [0 : vs.size] do
        for j in [i+1 : vs.size] do
          parts := parts.push (mkApp3 (mkConst ``Ne [1]) natE vs[i]! vs[j]!)
      return conjE parts
  | .and args => do return conjE (← args.mapM (propE d))
  | .or args => do return disjE (← args.mapM (propE d))
  | .not t => do return mkApp (mkConst ``Not) (← propE d t)
  | _ => none

partial def spatialE (d : DCtx) : SmtLib.Term → Option Expr
  | .emp => some (mkApp (mkConst ``HProp.hempty) instE)
  | .true => some (mkApp (mkConst ``HProp.hempty) instE)
  | .pto loc ctor args => do
      let fields ← d.c.ctors[ctor]?
      if fields.size != args.size then failure
      let l ← valE d loc
      let mut parts := #[hpureE (mkApp3 (mkConst ``Ne [1]) natE l (natLitE natE 0))]
      for i in [0 : args.size] do
        if isIntSort fields[i]!.sort then failure
        let v := mkApp3 (mkConst ``Nat.cast [0]) (mkConst ``Int) (mkConst ``instNatCastInt)
          (← valE d args[i]!)
        let addr := if i == 0 then l else
          mkApp6 (mkConst ``HAdd.hAdd [0, 0, 0]) natE (mkConst ``Loc) natE
            (mkApp2 (mkConst ``instHAdd [0]) natE (mkConst ``instAddNat)) l
            (natLitE (mkConst ``Loc) i)
        parts := parts.push (mkApp3 (mkConst ``HProp.hsingle) instE addr v)
      return starE parts
  | .sep args => do return starE (← args.mapM (spatialE d))
  | .and args => do
      let mut parts := #[]
      for a in args do
        if isSpatial d.c a then parts := parts.push (← spatialE d a)
        else parts := parts.push (hpureE (← propE d a))
      return starE parts
  | .or args => do
      let parts ← args.mapM (spatialE d)
      if parts.size == 0 then return hpureE (mkConst ``False)
      let mut acc := parts[parts.size - 1]!
      for i in [0 : parts.size - 1] do
        acc := mkApp3 (mkConst ``Bench.hor) instE parts[parts.size - 2 - i]! acc
      return acc
  | .wand l r => do
      return mkApp3 (mkConst ``HProp.hwand) instE (← spatialE d l) (← spatialE d r)
  | .exists bs b => do
      for bd in bs do
        let _ ← sortE? bd.sort
      let fvs := (List.range bs.size).toArray.map (fun i => mkFVar ⟨.num (.num `_encv d.depth) i⟩)
      let mut bound := d.bound
      for i in [0 : bs.size] do
        bound := bound.insert bs[i]!.name fvs[i]!
      let mut body ← spatialE { d with bound, depth := d.depth + 1 } b
      for m in [0 : bs.size] do
        let i := bs.size - 1 - m
        let lam := Expr.lam (Name.mkSimple ("v_" ++ sanitize bs[i]!.name)) natE
          (body.abstract #[fvs[i]!]) .default
        body := mkApp3 (mkConst ``HProp.hexists [1]) instE natE lam
      return body
  | .app p args => do
      let params ← d.c.preds[p]?
      if params.size != args.size then failure
      let mut xs := #[]
      for (b, a) in Array.zip params args do
        if isIntSort b.sort then failure
        xs := xs.push (← valE d a)
      if let some i := d.c.group[p]? then
        let X ← d.self
        let tys := d.groupTys
        let ts := xs.map (fun _ => natE)
        return mkApp X (injE tys i (if xs.size == 1 then xs[0]! else tupleE ts xs))
      else if d.c.emitted.contains p then
        return mkAppN (mkConst (predIdent d.c p).getId) xs
      else none
  | t => do return hpureE (← propE d t)


def arrowE (an : Name) (a b : Expr) : Expr := .forallE an a b .default

def directF (c : Ctx) (ds : Array FunDef) (group : Std.HashMap String Nat) (an : Name) :
    Option (Expr × Expr) := do
  let k := ds.size
  let mut argTys := #[]
  for dd in ds do
    argTys := argTys.push (tupleTyE (← dd.params.mapM (fun b => sortE? b.sort)))
  let argsT := sumTyE argTys 0
  let xTy := arrowE an argsT hpropE
  let fTy := arrowE an xTy (arrowE an argsT hpropE)
  let X := mkFVar ⟨`_encX⟩
  let mut lams := #[]
  for j in [0 : k] do
    let dd := ds[j]!
    let ts := dd.params.map (fun _ => natE)
    let p := mkFVar ⟨.num `_encP j⟩
    let mut subst : Std.HashMap String Expr := {}
    for i in [0 : dd.params.size] do
      subst := subst.insert dd.params[i]!.name (projE ts p i)
    let cF := { c with group, groupSize := k }
    let arm ← spatialE { c := cF, subst, self := some X, groupTys := argTys } dd.body
    lams := lams.push (Expr.lam `p_slcomp argTys[j]! (arm.abstract #[p]) .default)
  let mut fB := lams[k - 1]!
  for m in [0 : k - 1] do
    let j := k - 2 - m
    fB := mkApp5 (mkConst ``Sum.elim [0, 0, 1]) argTys[j]! (sumTyE argTys (j + 1)) hpropE lams[j]! fB
  return (fTy, .lam `X_slcomp xTy (fB.abstract #[X]) .default)

def directPred (ds : Array FunDef) (i : Nat) (fName : Name) (an : Name) :
    Option (Expr × Expr) := do
  let mut argTys := #[]
  for dd in ds do
    argTys := argTys.push (tupleTyE (← dd.params.mapM (fun b => sortE? b.sort)))
  let argsT := sumTyE argTys 0
  let dd := ds[i]!
  let n := dd.params.size
  let ts := dd.params.map (fun _ => natE)
  let xs := (List.range n).toArray.map (fun j => mkFVar ⟨.num `_encA j⟩)
  let tup := injE argTys i (if n == 1 then xs[0]! else tupleE ts xs)
  let mut body := mkApp4 (mkConst ``Bench.lfp) instE argsT (mkConst fName) tup
  let mut ty := hpropE
  for m in [0 : n] do
    let j := n - 1 - m
    body := .lam (Name.mkSimple ("v_" ++ sanitize dd.params[j]!.name)) natE (body.abstract #[xs[j]!]) .default
    ty := arrowE an natE ty
  return (ty, body)

def directGoal (c : Ctx) (lhsT rhsT : SmtLib.Term) (consts : Array Binder) : Option Expr := do
  let xs := (List.range consts.size).toArray.map (fun j => mkFVar ⟨.num `_encG j⟩)
  let mut bound : Std.HashMap String Expr := {}
  for j in [0 : consts.size] do
    let _ ← sortE? consts[j]!.sort
    bound := bound.insert consts[j]!.name xs[j]!
  let d : DCtx := { c, bound }
  let mut ty := mkApp3 (mkConst ``HProp.himpl) instE (← spatialE d lhsT) (← spatialE d rhsT)
  for m in [0 : consts.size] do
    let j := consts.size - 1 - m
    ty := .forallE (Name.mkSimple ("v_" ++ sanitize consts[j]!.name)) natE (ty.abstract #[xs[j]!]) .default
  return ty

end Direct

def argsType (_c : Ctx) (params : Array Binder) : CommandElabM Syn := do
  if params.size == 0 then `(Unit) else
  let mut acc ← sortTerm params[params.size - 1]!.sort
  for i in [0 : params.size - 1] do
    acc ← `($(← sortTerm params[params.size - 2 - i]!.sort) × $acc)
  return acc

def projTerm (p : Ident) (i n : Nat) : CommandElabM Syn := do
  if n == 1 then return p
  let mut acc : Syn := p
  for _ in [0 : i] do
    acc ← `($acc |>.2)
  if i + 1 == n then return acc else `($acc |>.1)

end Bench.Encode
