module

public import Sep.FindLaws
public import Batteries.Data.List.Perm
public meta import Lean

public section

open Lean Meta Elab Tactic

universe u v

namespace Sep.Xsimpl

initialize registerTraceClass `xsimpl

meta initialize cheapCancel : IO.Ref Bool ← IO.mkRef false

meta def withCheapCancel {α : Type} (x : TacticM α) : TacticM α := do
  let old ← cheapCancel.get
  cheapCancel.set true
  try x finally cheapCancel.set old

meta def cheapDefEq (a b : Expr) : MetaM Bool := do
  if a == b then return true
  if !(← cheapCancel.get) || a.hasMVar || b.hasMVar then isDefEq a b
  else withReducible (isDefEq a b)

meta def headMayMatch (h t : Expr) : MetaM Bool := do
  if h.hasMVar || t.hasMVar then return true
  let .const c2 _ := t.getAppFn | return true
  if ← isReducible c2 then return true
  let h' ← whnfR h
  match h'.getAppFn with
  | .const c1 _ => return c1 == c2
  | .fvar _ => return true
  | .mvar _ => return true
  | _ => return false

meta def cheapAssumptionCore (g : MVarId) : MetaM Bool := do
  unless ← cheapCancel.get do return ← g.assumptionCore
  let t ← instantiateMVars (← g.getType)
  let r ← (← getLCtx).findDeclRevM? fun d => do
    if d.isImplementationDetail then return none
    unless ← headMayMatch d.type t do return none
    if ← cheapDefEq d.type t then return some d.toExpr else return none
  match r with
  | some e => g.assign e; return true
  | none => return false

inductive PTree.{w} (α : Type w) where
  | leaf : PTree α
  | node : PTree α → α → PTree α → PTree α

@[expose] noncomputable def ptGet.{w} {α : Type w} (d : α) (t : PTree α) : Nat → α :=
  PTree.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun _ x _ il ir i => cond (Nat.beq i 0) x (cond (Nat.beq (i % 2) 1) (il (i / 2)) (ir (i / 2 - 1)))) t

@[expose] noncomputable def bitMask (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun i _ ih => (1 <<< i) ||| ih) l

@[expose] noncomputable def permChk (l r : List Nat) : Bool :=
  Nat.beq l.length r.length && Nat.beq (bitMask l) (2 ^ l.length - 1) && Nat.beq (bitMask r) (2 ^ l.length - 1)

theorem testBit_bitMask (l : List Nat) (i : Nat) : (bitMask l).testBit i = true ↔ i ∈ l := by
  induction l with
  | nil => simp [bitMask]
  | cons j t ih =>
    show ((1 <<< j) ||| bitMask t).testBit i = true ↔ i ∈ j :: t
    rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, Bool.or_eq_true, ih]
    simp [eq_comm]

theorem perm_range_of_mask (l : List Nat) (n : Nat) (hl : l.length = n) (hm : bitMask l = 2 ^ n - 1) :
    (List.range n).Perm l := by
  refine (List.subperm_of_subset List.nodup_range (fun i hi => ?_)).perm_of_length_le (by simp [hl])
  exact (testBit_bitMask l i).1 (by rw [hm, Nat.testBit_two_pow_sub_one]; simpa using List.mem_range.1 hi)

theorem permChk_perm {l r : List Nat} (h : permChk l r = true) : l.Perm r := by
  simp only [permChk, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact (perm_range_of_mask l _ rfl (Nat.eq_of_beq_eq_true h2)).symm.trans
    (perm_range_of_mask r _ (Nat.eq_of_beq_eq_true h1).symm (Nat.eq_of_beq_eq_true h3))

@[expose] noncomputable def listStar {α : Type u} {entails : α → α → Prop} {star : α → α → α} {emp : α}
    {pure : Prop → α} {ex : {A : Sort v} → (A → α) → α} {wand : α → α → α}
    [SepLaws α entails star emp pure ex wand] (xs : List α) : α :=
  List.rec (motive := fun _ => α) emp
    (fun x r ih => List.rec (motive := fun _ => α) x (fun _ _ _ => star x ih) r) xs

@[expose] noncomputable def starI {α : Type u} {entails : α → α → Prop} {star : α → α → α} {emp : α}
    {pure : Prop → α} {ex : {A : Sort v} → (A → α) → α} {wand : α → α → α}
    [SepLaws α entails star emp pure ex wand] (env : PTree α) (l : List Nat) : α :=
  listStar (l.map (ptGet emp env))

section NativeLemmas

variable {α : Type u} {entails : α → α → Prop} {star : α → α → α} {emp : α} {pure : Prop → α}
  {ex : {A : Sort v} → (A → α) → α} {wand : α → α → α}
  [inst : SepLaws α entails star emp pure ex wand]

local infixr:61 " ∗ " => star
local infixr:60 " -∗ " => wand
local infixr:25 " ==> " => entails
local notation:max "⌜" P "⌝" => pure P

include inst

theorem nt_trans {a b c : α} (h1 : a ==> b) (h2 : b ==> c) : a ==> c :=
  inst.entails_trans h1 h2

theorem nt_refl (a : α) : a ==> a :=
  inst.entails_refl a

theorem nt_of_eq {a b : α} (h : a = b) : a ==> b := by
  subst h; exact inst.entails_refl _

theorem nt_frame (c : α) {a b : α} (h : a ==> b) : c ∗ a ==> c ∗ b :=
  inst.frame_r h

theorem nt_comm (a b : α) : a ∗ b ==> b ∗ a := by
  rw [inst.star_comm]; exact inst.entails_refl _

theorem nt_swap (a b c : α) : a ∗ (b ∗ c) ==> b ∗ (a ∗ c) := by
  rw [hstar_left_comm (inst := inst)]; exact inst.entails_refl _

theorem nt_assoc (a b c : α) : (a ∗ b) ∗ c = a ∗ (b ∗ c) :=
  inst.star_assoc a b c

theorem nt_pushl (a b c : α) : a ∗ (b ∗ c) ==> (b ∗ a) ∗ c :=
  nt_trans (nt_swap a b c) (nt_of_eq (nt_assoc b a c).symm)

theorem nt_empl (a : α) : emp ∗ a = a :=
  inst.star_emp_l a

theorem nt_empr (a : α) : a ∗ emp = a :=
  inst.star_emp_r a

theorem nt_exl_base {A : Sort v} (J : A → α) (q : α) :
    ex J ∗ q ==> ex (fun x => J x ∗ q) := by
  rw [inst.star_ex]; exact inst.entails_refl _

theorem nt_exl_layer {A : Sort v} {K : A → α} {x : α} (s : α) (h : x ==> ex K) :
    s ∗ x ==> ex (fun y => s ∗ K y) :=
  inst.entails_trans (inst.frame_r h)
    (by rw [hstar_hexists_r (inst := inst)]; exact inst.entails_refl _)

theorem nt_exr_base {A : Sort v} (J : A → α) (q : α) :
    ex (fun x => J x ∗ q) ==> ex J ∗ q := by
  rw [inst.star_ex]; exact inst.entails_refl _

theorem nt_exr_layer {A : Sort v} {K : A → α} {x : α} (s : α) (h : ex K ==> x) :
    ex (fun y => s ∗ K y) ==> s ∗ x :=
  inst.entails_trans (by rw [← hstar_hexists_r (inst := inst)]; exact inst.entails_refl _)
    (inst.frame_r h)

theorem nt_exl {A : Sort v} {J : A → α} {r : α} (k : ∀ x, J x ==> r) : ex J ==> r :=
  inst.ex_l k

theorem nt_exr {A : Sort v} (x : A) {J : A → α} {l : α} (h : l ==> J x) : l ==> ex J :=
  inst.ex_r x h

theorem nt_purel {P : Prop} {q r : α} (k : P → q ==> r) : ⌜P⌝ ∗ q ==> r :=
  inst.pure_l k

theorem nt_purel1 {P : Prop} {r : α} (k : P → emp ==> r) : ⌜P⌝ ==> r :=
  himpl_hpure_l (inst := inst) k

theorem nt_purer {P : Prop} {l q : α} (p : P) (h : l ==> q) : l ==> ⌜P⌝ ∗ q :=
  inst.pure_r p h

theorem nt_purer1 {P : Prop} {l : α} (p : P) (h : l ==> emp) : l ==> ⌜P⌝ :=
  himpl_hpure_r (inst := inst) p h

theorem nt_eq_exl {A : Sort v} (J : A → α) (q : α) : ex J ∗ q = ex (fun x => J x ∗ q) :=
  inst.star_ex J q

theorem nt_eq_exr {A : Sort v} (q : α) (J : A → α) : q ∗ ex J = ex (fun x => q ∗ J x) :=
  hstar_hexists_r (inst := inst) q J

theorem nt_curry (a b c : α) : (a ∗ b) -∗ c = a -∗ (b -∗ c) :=
  inst.wand_curry a b c

theorem nt_wand_l (a b : α) {l r : α} (h : b ∗ l ==> r) : a ∗ ((a -∗ b) ∗ l) ==> r :=
  himpl_wand_apply_lhs (inst := inst) h

theorem nt_wand_l1 (a b : α) {r : α} (h : b ==> r) : a ∗ (a -∗ b) ==> r :=
  himpl_wand_apply_lhs_emp (inst := inst) h

theorem nt_wand_r {l a b : α} (h : l ∗ a ==> b) : l ==> a -∗ b :=
  inst.wand_intro h

theorem nt_wand_same (a : α) {l r : α} (h : l ==> r) : l ==> (a -∗ a) ∗ r :=
  inst.entails_trans h (inst.entails_trans (nt_of_eq (inst.star_emp_l r).symm)
    (inst.frame_l (inst.wand_intro (nt_of_eq (inst.star_emp_l a)))))

theorem nt_wand_same1 (a : α) {l : α} (h : l ==> emp) : l ==> a -∗ a :=
  inst.entails_trans h (inst.wand_intro (nt_of_eq (inst.star_emp_l a)))

theorem listStar_cons (x : α) (xs : List α) :
    listStar (x :: xs) = x ∗ listStar xs := by
  cases xs with
  | nil => exact (inst.star_emp_r x).symm
  | cons y ys => rfl

theorem listStar_perm {xs ys : List α} (h : xs.Perm ys) :
    listStar xs = listStar ys := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [listStar_cons, listStar_cons, ih]
  | swap x y l =>
    rw [listStar_cons, listStar_cons, listStar_cons, listStar_cons, ← inst.star_assoc,
      ← inst.star_assoc, inst.star_comm x y]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem listStar_append (xs ys : List α) :
    listStar (xs ++ ys) = listStar xs ∗ listStar ys := by
  induction xs with
  | nil => exact (inst.star_emp_l _).symm
  | cons x xs ih => rw [List.cons_append, listStar_cons, listStar_cons, ih, inst.star_assoc]

theorem nt_perm_idx (env : PTree α) (l r : List Nat) (h : permChk l r = true) :
    starI env l ==> starI env r := by
  rw [starI, starI, listStar_perm ((permChk_perm h).map _)]
  exact inst.entails_refl _

theorem nt_frame_list (cs : List α) {xs ys : List α}
    (h : listStar xs ==> listStar ys) :
    listStar (cs ++ xs) ==> listStar (cs ++ ys) := by
  rw [listStar_append, listStar_append]
  exact inst.frame_r h

end NativeLemmas

meta structure NCtx where
  carrier : Expr
  u : Level
  entOp : NOp
  starOp : NOp
  empOp : NOp
  pureOp : NOp
  exOp : NOp
  wandOp : Option NOp
  starFn : Expr
  starArgs : Array Expr
  empE : Expr
  entFn : Expr
  entArgs : Array Expr
  lv0 : Level
  ops0 : Array Expr
  inst0 : Expr
  deriving Inhabited

meta def lawsNCtx (carrier : Expr) : MetaM (Option NCtx) := do
  let some (u, laws) ← sepLaws? carrier | return none
  let ops := laws.ops
  unless ops.size == 6 do return none
  withLocalDeclD `x carrier fun x => withLocalDeclD `y carrier fun y =>
  withLocalDeclD `P (mkSort Level.zero) fun p => withLocalDeclD `A (mkSort laws.lv) fun a => do
  withLocalDeclD `J (← mkArrow a carrier) fun j => do
    let some (entOp, entFn, entArgs) := opTemplate ops[0]! #[x, y] | return none
    let some (starOp, starFn, starArgs) := opTemplate ops[1]! #[x, y] | return none
    let some (empOp, empFn, empArgs) := opTemplate ops[2]! #[] | return none
    let some (pureOp, _, _) := opTemplate ops[3]! #[p] | return none
    let some (exOp, _, _) := opTemplate ops[4]! #[a, j] | return none
    let wandOp := (opTemplate ops[5]! #[x, y]).map (·.1)
    return some {
      carrier := carrier,
      u := u,
      entOp := entOp,
      starOp := starOp,
      empOp := empOp,
      pureOp := pureOp,
      exOp := exOp,
      wandOp := wandOp,
      starFn := starFn,
      starArgs := starArgs,
      empE := mkAppN empFn empArgs,
      entFn := entFn,
      entArgs := entArgs,
      lv0 := laws.lv,
      ops0 := ops,
      inst0 := laws.inst }

meta initialize nctxCache : IO.Ref (Name × Array (Expr × Option NCtx)) ←
  IO.mkRef (.anonymous, #[])

meta def nctxOf? (carrier : Expr) : MetaM (Option NCtx) := do
  let m := (← getEnv).mainModule
  let (m0, cache) ← nctxCache.get
  let cache := if m0 == m then cache else #[]
  match cache.find? (·.1 == carrier) with
  | some (_, r) => return r
  | none =>
    let r ← try lawsNCtx carrier catch _ => pure none
    nctxCache.set (m, cache.push (carrier, r))
    return r

meta def nctxFor? (t : Expr) : MetaM (Option (NCtx × Expr × Expr)) := do
  let t := t.consumeMData
  unless t.getAppFn.isConst && t.getAppNumArgs ≥ 2 do return none
  let l := t.appFn!.appArg!
  let r := t.appArg!
  let some carrier ← (try some <$> (instantiateMVars (← inferType l)) catch _ => pure none)
    | return none
  if carrier.hasMVar || carrier.hasLooseBVars then return none
  let some rt ← (try some <$> (instantiateMVars (← inferType r)) catch _ => pure none)
    | return none
  unless rt == carrier || (← withReducible (isDefEq rt carrier)) do return none
  let some c ← nctxOf? carrier | return none
  unless t.isAppOfArity c.entOp.name c.entOp.arity do return none
  return some (c, t.getArg! c.entOp.pos[0]!, t.getArg! c.entOp.pos[1]!)

meta def sepGoal? (g : MVarId) : MetaM (Option (MVarId × NCtx × Expr × Expr)) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  return (← nctxFor? t).map fun (c, l, r) => (g, c, l, r)

namespace NCtx

meta def isOp (op : NOp) (e : Expr) : Bool := e.isAppOfArity op.name op.arity

meta def arg (op : NOp) (e : Expr) (i : Nat) : Expr := e.getArg! op.pos[i]!

meta def mkStar (c : NCtx) (a b : Expr) : Expr :=
  mkAppN c.starFn ((c.starArgs.set! c.starOp.pos[0]! a).set! c.starOp.pos[1]! b)

meta def mkEnt (c : NCtx) (a b : Expr) : Expr :=
  mkAppN c.entFn ((c.entArgs.set! c.entOp.pos[0]! a).set! c.entOp.pos[1]! b)

meta def starL (c : NCtx) : List Expr → Expr
  | [] => c.empE
  | [a] => a
  | a :: r => c.mkStar a (c.starL r)

meta def starLeft (c : NCtx) (xs : Array Expr) : Expr := Id.run do
  let mut acc := xs[0]!
  for i in [1 : xs.size] do
    acc := c.mkStar acc xs[i]!
  return acc

meta def lem (c : NCtx) (n : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst n [c.u, c.lv0]) (#[c.carrier] ++ c.ops0 ++ #[c.inst0] ++ args)

meta def lemAt (c : NCtx) (l : LawsAt) (n : Name) (args : Array Expr) : Expr :=
  mkAppN (mkConst n [c.u, l.lv]) (#[c.carrier] ++ l.ops ++ #[l.inst] ++ args)

meta def lawsAtLv? (c : NCtx) (lv : Level) : MetaM (Option LawsAt) :=
  if lv == c.lv0 then return some { lv, ops := c.ops0, inst := c.inst0 }
  else lawsAt? ``SepLaws c.carrier c.u lv

meta def trans (c : NCtx) (a b d p q : Expr) : Expr := c.lem ``nt_trans #[a, b, d, p, q]

meta def transO (c : NCtx) (a b d : Expr) (p : Option Expr) (q : Expr) : Expr :=
  match p with
  | none => q
  | some p => c.trans a b d p q

meta def transO' (c : NCtx) (a b d : Expr) (p : Expr) (q : Option Expr) : Expr :=
  match q with
  | none => p
  | some q => c.trans a b d p q

meta def eqTrans (c : NCtx) (a b d p q : Expr) : Expr :=
  mkAppN (mkConst ``Eq.trans [c.u.succ]) #[c.carrier, a, b, d, p, q]

meta def eqSymm (c : NCtx) (a b p : Expr) : Expr :=
  mkAppN (mkConst ``Eq.symm [c.u.succ]) #[c.carrier, a, b, p]

meta def starFnOf (c : NCtx) (a : Expr) : Expr :=
  let n := c.starOp.arity
  if c.starOp.pos[0]! + 2 == n && c.starOp.pos[1]! + 1 == n then
    mkAppN c.starFn ((c.starArgs.set! c.starOp.pos[0]! a).extract 0 (n - 1))
  else .lam `x c.carrier (c.mkStar a (.bvar 0)) .default

meta def congrStar (c : NCtx) (a b1 b2 p : Expr) : Expr :=
  mkAppN (mkConst ``congrArg [c.u.succ, c.u.succ]) #[c.carrier, c.carrier, b1, b2, c.starFnOf a, p]

meta partial def flat (c : NCtx) (e : Expr) : List Expr × Option Expr :=
  if isOp c.starOp e then
    let a := arg c.starOp e 0
    let b := arg c.starOp e 1
    if isOp c.starOp a then
      let a1 := arg c.starOp a 0
      let a2 := arg c.starOp a 1
      let e' := c.mkStar a1 (c.mkStar a2 b)
      let p1 := c.lem ``nt_assoc #[a1, a2, b]
      let (l, p2) := c.flat e'
      (l, some (match p2 with
        | none => p1
        | some p2 => c.eqTrans e e' (c.starL l) p1 p2))
    else if isOp c.empOp a then
      let p1 := c.lem ``nt_empl #[b]
      let (l, p2) := c.flat b
      (l, some (match p2 with
        | none => p1
        | some p2 => c.eqTrans e b (c.starL l) p1 p2))
    else
      let (lb, pb) := c.flat b
      if lb.isEmpty then
        let p2 := c.lem ``nt_empr #[a]
        match pb with
        | none => ([a], some p2)
        | some q =>
          let mid := c.mkStar a c.empE
          ([a], some (c.eqTrans e mid a (c.congrStar a b c.empE q) p2))
      else
        (a :: lb, pb.map (c.congrStar a b (c.starL lb)))
  else if isOp c.empOp e then ([], none)
  else ([e], none)

meta partial def pullL (c : NCtx) (s : List Expr) (k : Nat) : Expr :=
  match s with
  | s0 :: s1 =>
    if k == 0 then c.lem ``nt_refl #[c.starL s]
    else
      let t0 := s1[k-1]!
      let s1' := s1.eraseIdx (k-1)
      if s1'.isEmpty then c.lem ``nt_comm #[s0, t0]
      else
        let r := c.starL s1'
        let p1 := c.pullL s1 (k-1)
        let fr := c.lem ``nt_frame #[s0, c.starL s1, c.mkStar t0 r, p1]
        let sw := c.lem ``nt_swap #[s0, t0, r]
        c.trans (c.starL s) (c.mkStar s0 (c.mkStar t0 r)) (c.mkStar t0 (c.mkStar s0 r)) fr sw
  | [] => c.lem ``nt_refl #[c.empE]

meta partial def pullR (c : NCtx) (s : List Expr) (k : Nat) : Expr :=
  match s with
  | s0 :: s1 =>
    if k == 0 then c.lem ``nt_refl #[c.starL s]
    else
      let t0 := s1[k-1]!
      let s1' := s1.eraseIdx (k-1)
      if s1'.isEmpty then c.lem ``nt_comm #[t0, s0]
      else
        let r := c.starL s1'
        let p1 := c.pullR s1 (k-1)
        let sw := c.lem ``nt_swap #[t0, s0, r]
        let fr := c.lem ``nt_frame #[s0, c.mkStar t0 r, c.starL s1, p1]
        c.trans (c.mkStar t0 (c.mkStar s0 r)) (c.mkStar s0 (c.mkStar t0 r)) (c.starL s) sw fr
  | [] => c.lem ``nt_refl #[c.empE]

meta partial def perm (c : NCtx) (s : List Expr) (idx : List Nat) : Option Expr :=
  match s, idx with
  | _ :: _ :: _, k :: rest =>
    let t := s[k]!
    let s' := s.eraseIdx k
    let rest' := rest.map (fun j => if j > k then j - 1 else j)
    let t' := rest'.map (s'[·]!)
    let fr := (c.perm s' rest').map (fun sub =>
      c.lem ``nt_frame #[t, c.starL s', c.starL t', sub])
    let pl := if k == 0 then none else some (c.pullL s k)
    match pl, fr with
    | none, none => none
    | some p, none => some p
    | none, some f => some f
    | some p, some f => some (c.trans (c.starL s) (c.mkStar t (c.starL s')) (c.mkStar t (c.starL t')) p f)
  | _, _ => none

meta def natList (xs : List Nat) : Expr :=
  xs.foldr (fun i acc => mkApp3 (mkConst ``List.cons [0]) (mkConst ``Nat) (mkRawNatLit i) acc)
    (mkApp (mkConst ``List.nil [0]) (mkConst ``Nat))

meta def atomList (c : NCtx) (xs : List Expr) : Expr :=
  xs.foldr (fun a acc => mkApp3 (mkConst ``List.cons [c.u]) c.carrier a acc) (mkApp (mkConst ``List.nil [c.u]) c.carrier)

meta partial def ptree (c : NCtx) (xs : Array Expr) (f : Nat → Nat) (n : Nat) : Expr :=
  if n == 0 then mkApp (mkConst ``PTree.leaf [c.u]) c.carrier
  else mkApp4 (mkConst ``PTree.node [c.u]) c.carrier (c.ptree xs (fun j => f (2 * j + 1)) (n / 2)) xs[f 0]!
    (c.ptree xs (fun j => f (2 * j + 2)) ((n - 1) / 2))

meta def permIdx (c : NCtx) (s : Array Expr) (r : List Nat) : Option Expr :=
  if r == List.range s.size then none else
  some (c.lem ``nt_perm_idx #[c.ptree s id s.size, natList (List.range s.size), natList r,
    mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)])

meta def selfEq (s : Expr) : Bool :=
  match s.getAppFnArgs with
  | (``Eq, #[_, a, b]) => a == b
  | (``Iff, #[a, b]) => a == b
  | _ => false

meta def bad (c : NCtx) (e : Expr) : Bool :=
  (e.find? (fun s =>
    match s with
    | .const n _ =>
      n == c.starOp.name || n == c.empOp.name || n == c.pureOp.name ||
        n == c.exOp.name || n == c.entOp.name ||
        (match c.wandOp with
         | some w => n == w.name
         | none => false)
    | .mdata .. => true
    | _ => selfEq s)).isSome

meta structure SpineAcc where
  lvs : Array Level := #[]
  hasEx : Bool := false
  nestedTypeEx : Bool := false

meta def exLevel (c : NCtx) (a : Expr) (acc : SpineAcc) (nested : Bool) : MetaM (Option SpineAcc) := do
  if a.hasLooseBVars || c.bad a || a == c.carrier then return none
  let lv ← try (some <$> getLevel a) catch _ => pure none
  let some lv := lv | return none
  let lv := (← instantiateLevelMVars lv).normalize
  if lv.hasMVar then return none
  let lvs := if acc.lvs.contains lv then acc.lvs else acc.lvs.push lv
  return some { acc with lvs, nestedTypeEx := acc.nestedTypeEx || (nested && lv != Level.zero) }

mutual

meta partial def nestedSide (c : NCtx) (x : Expr) (acc : SpineAcc) : MetaM (Option SpineAcc) := do
  if x.isLambda then
    return ← lambdaTelescope x fun _ b => nestedSide c b acc
  let (items, _) := c.flat x
  let mut acc := acc
  for it in items do
    if isOp c.exOp it then
      let some acc' ← exLevel c (arg c.exOp it 0) acc true | return none
      let j := arg c.exOp it 1
      unless j.isLambda do return none
      let some acc' ← nestedSide c j acc' | return none
      acc := acc'
    else if isOp c.pureOp it then
      continue
    else
      let some acc' ← atomCheck c it acc | return none
      acc := acc'
  return some acc

meta partial def atomCheck (c : NCtx) (e : Expr) (acc : SpineAcc) : MetaM (Option SpineAcc) := do
  if !c.bad e then return some acc
  if let some w := c.wandOp then
    if isOp w e then
      let some acc ← nestedSide c (arg w e 0) acc | return none
      return ← nestedSide c (arg w e 1) acc
  let fn := e.getAppFn
  if e.getAppNumArgs == 0 || c.bad fn then return none
  let mut acc := acc
  for x in e.getAppArgs do
    if !c.bad x then continue
    let some acc' ← nestedSide c x acc | return none
    acc := acc'
  return some acc

end

meta partial def spine (c : NCtx) (e : Expr) (acc : SpineAcc) : MetaM (Option SpineAcc) := do
  if isOp c.starOp e then
    match ← c.spine (arg c.starOp e 0) acc with
    | none => return none
    | some acc => c.spine (arg c.starOp e 1) acc
  else if isOp c.empOp e then return some acc
  else if isOp c.pureOp e then return some acc
  else if isOp c.exOp e then
    let some acc ← exLevel c (arg c.exOp e 0) acc false | return none
    let acc := { acc with hasEx := true }
    let j := arg c.exOp e 1
    if j.isLambda then lambdaTelescope j fun _ b => c.spine b acc
    else if c.bad j || j.hasLooseBVars then return none
    else return some acc
  else if e.isMVar then return some acc
  else atomCheck c e acc

meta inductive Item where
  | atom
  | ex (a j : Expr)
  | pure (p : Expr)

meta def item (c : NCtx) (e : Expr) : Item :=
  if isOp c.exOp e then .ex (arg c.exOp e 0) (arg c.exOp e 1)
  else if isOp c.pureOp e then .pure (arg c.pureOp e 0)
  else .atom

meta def pick (c : NCtx) (s : List Expr) (typeEx leftPure : Bool) : Option Nat := Id.run do
  let n := s.length
  let arr := s.toArray
  if typeEx then
    let mut i := n
    while i > 0 do
      i := i - 1
      if isOp c.exOp arr[i]! then return some i
    if leftPure then
      for k in [0 : n] do
        if isOp c.pureOp arr[k]! then return some k
      return none
  let mut i := n
  while i > 0 do
    i := i - 1
    if isOp c.exOp arr[i]! || isOp c.pureOp arr[i]! then return some i
  return none

meta def pickEx (c : NCtx) (s : List Expr) : Option Nat := Id.run do
  let arr := s.toArray
  let mut i := arr.size
  while i > 0 do
    i := i - 1
    if isOp c.exOp arr[i]! then return some i
  return none

meta def exBody (j : Expr) : Name × Expr :=
  if j.isLambda then (j.bindingName!, j.bindingBody!) else (`x, mkApp j (.bvar 0))

end NCtx

-- ============================================================
-- MetaM: star chain manipulation
-- ============================================================

meta def affineLaws? (c : NCtx) : MetaM (Option LawsAt) :=
  lawsAt? ``AffineSepLaws c.carrier c.u c.lv0

/-- Recognise an entailment of a registered logic. -/
meta def matchEntails? (e : Expr) : MetaM (Option (NCtx × Expr × Expr)) := do
  nctxFor? (← instantiateMVars e)

/-- Recognise `H1 ∗ H2`. -/
meta def matchStar? (c : NCtx) (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if NCtx.isOp c.starOp e then some (NCtx.arg c.starOp e 0, NCtx.arg c.starOp e 1) else none

meta def isEmp (c : NCtx) (e : Expr) : Bool := NCtx.isOp c.empOp e.consumeMData

meta def isSpure (c : NCtx) (e : Expr) : Bool := NCtx.isOp c.pureOp e.consumeMData

/-- Parse `H1 ∗ H2 ∗ ... ∗ emp` into `[H1, H2, ...]` (not including trailing `emp`). -/
meta partial def parseStar (c : NCtx) (e : Expr) : List Expr :=
  match matchStar? c e with
  | some (H1, H2) => H1 :: parseStar c H2
  | none => if isEmp c e then [] else [e]

meta def NCtx.lhsEq (c : NCtx) (proof g : Expr) : MetaM Expr :=
  mkAppOptM ``Sep.Xsimpl.himpl_lhs_eq #[some c.carrier, some c.ops0[0]!, none, none, none,
    some proof, some g]

meta def NCtx.rhsEq (c : NCtx) (proof g : Expr) : MetaM Expr :=
  mkAppOptM ``Sep.Xsimpl.himpl_rhs_eq #[some c.carrier, some c.ops0[0]!, none, none, none,
    some proof, some g]

/-- Move `atom` to the front of a star chain `tree`, returning `(newTree, proof : tree = newTree)`.
    `newTree` starts with `atom`. Fails if `atom` is not in the chain. -/
meta partial def starMoveToFront (c : NCtx) (atom : Expr) (tree : Expr) : MetaM (Expr × Expr) := do
  let tree := tree.consumeMData
  match matchStar? c tree with
  | some (H1, H2) =>
    if ← cheapDefEq atom H1 then
      return (tree, ← mkEqRefl tree)
    else
      -- Recursively move atom to front of H2 (the tail)
      let (newTail, tailProof) ← starMoveToFront c atom H2
      match matchStar? c newTail with
      | some (atomExpr, H2rest) =>
        -- Build f = fun x => H1 ∗ x  (to apply congrArg)
        let f ← withLocalDecl `x .default c.carrier fun xVar => do
          mkLambdaFVars #[xVar] (c.mkStar H1 xVar)
        -- step1 : H1 ∗ H2 = H1 ∗ (atom ∗ H2rest)
        let step1 ← mkCongrArg f tailProof
        -- leftComm : atom ∗ (H1 ∗ H2rest) = H1 ∗ (atom ∗ H2rest)
        let leftComm := c.lem ``Sep.Xsimpl.hstar_left_comm #[atomExpr, H1, H2rest]
        let step2 ← mkEqSymm leftComm
        let total ← mkEqTrans step1 step2
        return (c.mkStar atomExpr (c.mkStar H1 H2rest), total)
      | none =>
        -- newTail is just the atom
        let f ← withLocalDecl `x .default c.carrier fun xVar => do
          mkLambdaFVars #[xVar] (c.mkStar H1 xVar)
        let step1 ← mkCongrArg f tailProof
        let comm := c.lem ``SepLaws.star_comm #[H1, newTail]
        let total ← mkEqTrans step1 comm
        return (c.mkStar newTail H1, total)
  | none =>
    if ← cheapDefEq atom tree then
      return (tree, ← mkEqRefl tree)
    else
      throwError "starMoveToFront: {← ppExpr atom} not found in chain {← ppExpr tree}"

/-- Rewrite the LHS of the current entailment goal to `newLhs`, given `lhs = newLhs`. -/
meta def replaceLhs (goal : MVarId) (c : NCtx) (newLhs rhs proof : Expr) : MetaM MVarId := do
  let newGoalMVar ← mkFreshExprMVar (c.mkEnt newLhs rhs)
  goal.assign (← c.lhsEq proof newGoalMVar)
  return newGoalMVar.mvarId!

meta def applyLem (e : Expr) : TacticM Unit := do
  replaceMainGoal (← (← getMainGoal).apply e)

meta def firstOf (ts : List (TacticM Unit)) (msg : MessageData) : TacticM Unit :=
  ts.foldr (· <|> ·) (throwError msg)

-- ============================================================
-- Cancellation
-- ============================================================

/-- Try to cancel matching items between LHS and RHS of an entailment goal. -/
meta def xsimplCancelAllCore : TacticM Unit := withMainContext do
  let mut progress := false
  let mut cont := true
  while cont do
    cont := false
    let goals ← getUnsolvedGoals
    if goals.isEmpty then break
    let goal ← getMainGoal
    let goalType ← goal.getType >>= instantiateMVars
    let some (c, lhs, rhs) ← matchEntails? goalType | break
    let rhsItems := parseStar c rhs
    if rhsItems.isEmpty then break
    let lhsItems := parseStar c lhs
    if lhsItems.isEmpty then break

    let mut found : Option Expr := none
    for r in [:rhsItems.length] do
      let rhsItem ← instantiateMVars rhsItems[r]!
      if rhsItem.isMVar then continue
      for l in [:lhsItems.length] do
        let lhsItem ← instantiateMVars lhsItems[l]!
        if lhsItem.isMVar then continue
        if ← cheapDefEq lhsItem rhsItem then
          found := some rhsItems[r]!
          break
      if found.isSome then break

    let some atom := found | break
    cont := true
    progress := true
    trace[xsimpl] m!"Cancelling {atom}"

    let (newLhs, lhsProof) ← starMoveToFront c atom lhs
    let (newRhs, rhsProof) ← starMoveToFront c atom rhs

    let newGoalMVar ← mkFreshExprMVar (c.mkEnt newLhs newRhs)

    -- goal : lhs ==> rhs, via (newLhs ==> rhs) via (newLhs ==> newRhs)
    let goalMVar1 ← mkFreshExprMVar (c.mkEnt newLhs rhs)
    goal.assign (← c.lhsEq lhsProof goalMVar1)
    goalMVar1.mvarId!.assign (← c.rhsEq (← mkEqSymm rhsProof) newGoalMVar)

    replaceMainGoal [newGoalMVar.mvarId!]

    let newLhsIsStar := (matchStar? c newLhs).isSome
    let newRhsIsStar := (matchStar? c newRhs).isSome

    if newLhsIsStar && newRhsIsStar then
      applyLem (c.lem ``SepLaws.frame_r #[])
    else if newLhsIsStar && not newRhsIsStar then
      applyLem (c.lem ``Sep.Xsimpl.himpl_cancel_lhs #[])
    else if not newLhsIsStar && newRhsIsStar then
      applyLem (c.lem ``Sep.Xsimpl.himpl_cancel_rhs #[])
    else
      applyLem (c.lem ``SepLaws.entails_refl #[])
  if not progress then
    throwError "xsimpl_cancel_all: no items to cancel"

elab "xsimpl_cancel_all_core" : tactic => xsimplCancelAllCore

meta def xsimplCancelWandCore : TacticM Unit := withMainContext do
  let mut progress := false
  let mut cont := true
  while cont do
    cont := false
    let goals ← getUnsolvedGoals
    if goals.isEmpty then break
    let goal ← getMainGoal
    let goalType ← goal.getType >>= instantiateMVars
    let some (c, lhs, rhs) ← matchEntails? goalType | break
    let some w := c.wandOp | break
    let lhsItems := parseStar c lhs
    if lhsItems.isEmpty then break

    -- Find an (H1 -∗ H2) and an H1 matching its premise
    let mut found : Option (Expr × Expr) := none
    for l in [:lhsItems.length] do
      let itemWand := lhsItems[l]!.consumeMData
      if NCtx.isOp w itemWand then
        let wandLhs := NCtx.arg w itemWand 0
        for l2 in [:lhsItems.length] do
          if l != l2 then
            let itemPremise := lhsItems[l2]!
            if ← cheapDefEq wandLhs itemPremise then
              found := some (itemPremise, itemWand)
              break
        if found.isSome then break

    let some (premise, wand) := found | break
    cont := true
    progress := true

    -- Move wand to front, then premise to front so we get `premise ∗ wand`
    let (newLhs1, lhsProof1) ← starMoveToFront c wand lhs
    let (newLhs2, lhsProof2) ← starMoveToFront c premise newLhs1
    let transProof ← mkEqTrans lhsProof1 lhsProof2

    let newGoal ← replaceLhs goal c newLhs2 rhs transProof
    replaceMainGoal [newGoal]

    if (matchStar? c newLhs2).isSome then
      firstOf [applyLem (c.lem ``Sep.Xsimpl.himpl_wand_apply_lhs #[]),
        applyLem (c.lem ``Sep.Xsimpl.himpl_wand_apply_lhs_emp #[])] "xsimpl_cancel_wand: failed"
    else
      applyLem (c.lem ``Sep.Xsimpl.himpl_wand_apply_lhs_emp #[])
  if not progress then
    throwError "xsimpl_cancel_wand: no wands to cancel"

elab "xsimpl_cancel_wand_core" : tactic => xsimplCancelWandCore

-- ============================================================
-- Tactic phases
-- ============================================================

meta def exLevels (c : NCtx) (es : List Expr) : MetaM (Array Level) := do
  let mut out := #[]
  for e in es do
    for s in collect e #[] do
      let a := NCtx.arg c.exOp s 0
      if a.hasLooseBVars then continue
      let some lv ← (try some <$> getLevel a catch _ => pure none) | continue
      let lv := (← instantiateLevelMVars lv).normalize
      unless lv.hasMVar || out.contains lv do out := out.push lv
  return out
where
  collect (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := if NCtx.isOp c.exOp e then acc.push e else acc
    match e with
    | .app f a => collect a (collect f acc)
    | .lam _ t b _ => collect b (collect t acc)
    | .forallE _ t b _ => collect b (collect t acc)
    | .mdata _ b => collect b acc
    | _ => acc

meta def lawsFor (c : NCtx) (es : List Expr) : MetaM (Array LawsAt) := do
  let mut out : Array LawsAt := #[{ lv := c.lv0, ops := c.ops0, inst := c.inst0 }]
  for lv in ← exLevels c es do
    if out.any (·.lv == lv) then continue
    if let some l ← c.lawsAtLv? lv then out := out.push l
  return out

meta def xsimplNormalize : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let some (_, c, l, r) ← sepGoal? g | return
  let mut thms : SimpTheorems := {}
  let add := fun (thms : SimpTheorems) (n : Name) (e : Expr) => thms.add (.other n) #[] e
  for n in [``SepLaws.star_emp_l, ``SepLaws.star_emp_r, ``SepLaws.star_assoc,
      ``SepLaws.wand_curry] do
    thms ← add thms n (c.lem n #[])
  for laws in ← lawsFor c [l, r] do
    thms ← add thms ``SepLaws.star_ex (c.lemAt laws ``SepLaws.star_ex #[])
    thms ← add thms ``Sep.Xsimpl.hstar_hexists_r (c.lemAt laws ``Sep.Xsimpl.hstar_hexists_r #[])
  if let some l0 ← c.lawsAtLv? Level.zero then
    for n in [``Sep.Xsimpl.hstar_hpure_eq_hexists, ``Sep.Xsimpl.hstar_hpure_r_eq_hexists] do
      thms ← add thms n (mkAppN (mkConst n [c.u]) (#[c.carrier] ++ l0.ops ++ #[l0.inst]))
  let ctx ← Simp.mkContext (config := {}) (simpTheorems := #[thms])
    (congrTheorems := ← getSimpCongrTheorems)
  let (res, _) ← simpTarget g ctx
  replaceMainGoal res.toList

syntax "xsimpl_normalize" : tactic
elab_rules : tactic
  | `(tactic| xsimpl_normalize) => do
    try xsimplNormalize catch _ => pure ()

meta def hasExHead (c : NCtx) (items : List Expr) : Bool :=
  items.any fun i =>
    let i := i.consumeMData
    NCtx.isOp c.exOp i || NCtx.isOp c.pureOp i

meta def movePureToFront (onLhs : Bool) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (c, lhs, rhs) ← matchEntails? goalType | throwError "not an entailment"
  let side := if onLhs then lhs else rhs
  let items := parseStar c side
  if items.length ≤ 1 then throwError "no pure conjunct to move"
  if isSpure c items[0]! then throwError "pure conjunct already at the front"
  let some pureItem := items.find? (isSpure c) | throwError "no pure conjunct to move"
  let (newSide, proof) ← starMoveToFront c pureItem side
  if onLhs then
    replaceMainGoal [← replaceLhs goal c newSide rhs proof]
  else
    let newGoalMVar ← mkFreshExprMVar (c.mkEnt lhs newSide)
    goal.assign (← c.rhsEq (← mkEqSymm proof) newGoalMVar)
    replaceMainGoal [newGoalMVar.mvarId!]

elab "xsimpl_pure_front_lhs" : tactic => movePureToFront true
elab "xsimpl_pure_front_rhs" : tactic => movePureToFront false

meta def xsimplInstantiateStepCore : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (c, _, rhs) ← matchEntails? goalType | throwError "not an entailment"

  -- If RHS is an MVar, applying ex_r will infinite loop by unifying it with ex
  let rhsItems := parseStar c rhs
  for item in rhsItems do
    if item.isMVar then throwError "RHS contains MVar, skipping instantiate to prevent looping"
  unless hasExHead c rhsItems do throwError "RHS has no existential"

  let lawss ← lawsFor c rhsItems
  firstOf (lawss.toList.map (fun l => applyLem (c.lemAt l ``Sep.Xsimpl.himpl_hexists_r_star #[])) ++
    lawss.toList.map (fun l => applyLem (c.lemAt l ``SepLaws.ex_r #[])) ++
    [applyLem (c.lem ``SepLaws.pure_r #[]),
     applyLem (c.lem ``Sep.Xsimpl.himpl_hpure_r #[]),
     (do movePureToFront false; applyLem (c.lem ``SepLaws.pure_r #[]))])
    "xsimpl_instantiate_step: no step applies"

elab "xsimpl_instantiate_step_core" : tactic => xsimplInstantiateStepCore

meta def xsimplExtractStepCore : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (c, lhs, _) ← matchEntails? goalType | throwError "not an entailment"

  let lhsItems := parseStar c lhs
  for item in lhsItems do
    if item.isMVar then
      throwError "LHS contains MVar, skipping extract to prevent looping"
  unless hasExHead c lhsItems do throwError "LHS has no existential"

  let intro : TacticM Unit := evalTactic (← `(tactic| intro))
  let lawss ← lawsFor c lhsItems
  firstOf (lawss.toList.map (fun l => do
      applyLem (c.lemAt l ``Sep.Xsimpl.himpl_hexists_l_star #[]); intro) ++
    lawss.toList.map (fun l => do applyLem (c.lemAt l ``SepLaws.ex_l #[]); intro) ++
    [(do applyLem (c.lem ``SepLaws.pure_l #[]); intro),
     (do applyLem (c.lem ``Sep.Xsimpl.himpl_hpure_l #[]); intro),
     (do movePureToFront true; applyLem (c.lem ``SepLaws.pure_l #[]); intro)])
    "xsimpl_extract_step: no step applies"

elab "xsimpl_extract_step_core" : tactic => xsimplExtractStepCore

/-- **Wand introduction** (the adjunction, hence safe and invertible).
    Fires only when the whole RHS is a wand, i.e. the RHS star chain has a single
    remaining item and that item is `P1 -∗ P2`: then `H ==> P1 -∗ P2` becomes
    `H ∗ P1 ==> P2`. It cannot loop, since each step strips one wand. -/
meta def xsimplWandIntroCore : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let goalType ← goal.getType >>= instantiateMVars
  let some (c, _, rhs) ← matchEntails? goalType | throwError "not an entailment"
  let rhsItems := parseStar c rhs
  let [item] := rhsItems | throwError "RHS is not a single wand"
  if item.isMVar then throwError "RHS is a metavariable"
  let some w := c.wandOp | throwError "RHS is not a wand"
  unless NCtx.isOp w item.consumeMData do throwError "RHS is not a wand"
  applyLem (c.lem ``SepLaws.wand_intro #[])

elab "xsimpl_wand_intro_core" : tactic => xsimplWandIntroCore

syntax "xsimpl_cancel_all" : tactic
macro_rules
  | `(tactic| xsimpl_cancel_all) => `(tactic| xsimpl_cancel_all_core)

syntax "xsimpl_cancel_wand" : tactic
macro_rules
  | `(tactic| xsimpl_cancel_wand) => `(tactic| xsimpl_cancel_wand_core)

syntax "xsimpl_instantiate_step" : tactic
macro_rules
  | `(tactic| xsimpl_instantiate_step) => `(tactic| xsimpl_instantiate_step_core)

syntax "xsimpl_extract_step" : tactic
macro_rules
  | `(tactic| xsimpl_extract_step) => `(tactic| xsimpl_extract_step_core)

syntax "xsimpl_wand_intro" : tactic
macro_rules
  | `(tactic| xsimpl_wand_intro) => `(tactic| xsimpl_wand_intro_core)

/-- Run `t`, and fail unless it changed the goals.  `xsimpl_core` drives its
steps with `repeat`, which stops only on failure, so a step that succeeds without
progress would not terminate. -/
meta def withProgress (t : TacticM Unit) : TacticM Unit := do
  let before ← (← getGoals).mapM fun g => do instantiateMVars (← g.getType)
  t
  let after ← (← getGoals).mapM fun g => do instantiateMVars (← g.getType)
  if before.length == after.length && (before.zip after).all (fun (x, y) => x == y) then
    throwError "xsimpl: step made no progress"

syntax "xsimpl_with_progress " tacticSeq : tactic
elab_rules : tactic
  | `(tactic| xsimpl_with_progress $t) => withProgress (evalTactic t)

/-- One rewriting step. -/
syntax "xsimpl_step" : tactic
macro_rules
  | `(tactic| xsimpl_step) => `(tactic| (
      xsimpl_with_progress (
        first
        | xsimpl_cancel_all_core
        | xsimpl_extract_step_core
        | xsimpl_wand_intro_core
        | xsimpl_instantiate_step_core
        | xsimpl_cancel_wand_core
      )
    ))



meta def newGoal (cur : MVarId) (ty : Expr) (mk : Expr → Expr) : MetaM MVarId := cur.withContext do
  let m ← mkFreshExprMVar ty
  cur.assign (mk m)
  return m.mvarId!

meta def normLevel (a : Expr) : MetaM Level := do
  return (← instantiateLevelMVars (← getLevel a)).normalize

mutual

meta partial def itemsNorm (c : NCtx) (x : Expr) (items : List Expr) (p : Option Expr) :
    MetaM (List Expr × Option Expr) := do
  let mut cur := items
  let mut pf := p
  let mut lhs := c.starL items
  for k in [0 : items.length] do
    let it := cur[k]!
    let (it', q) ← itemNorm c it
    let some q := q | continue
    let next := cur.set k it'
    let f ← withLocalDeclD `y (← inferType it) fun y =>
      mkLambdaFVars #[y] (c.starL (cur.set k y))
    let step ← mkCongrArg f q
    let rhs := c.starL next
    pf := some (match pf with
      | none => step
      | some p0 => c.eqTrans x lhs rhs p0 step)
    lhs := rhs
    cur := next
  return (cur, pf)

meta partial def nestNorm (c : NCtx) (x : Expr) : MetaM (Expr × Option Expr) := do
  let (items0, p0) := c.flat x
  let (items, p1) ← itemsNorm c x items0 p0
  let flatE := c.starL items
  unless items.any (NCtx.isOp c.exOp) do return (flatE, p1)
  let arr := items.toArray
  let n := arr.size
  let mut acc := arr[n-1]!
  let mut accPf : Option Expr := none
  let mut k := n - 1
  while k > 0 do
    k := k - 1
    let orig := c.starL (items.drop (k+1))
    let start := c.mkStar arr[k]! orig
    let mid := c.mkStar arr[k]! acc
    let (acc', q) ← combine c arr[k]! acc
    let pa := accPf.map (c.congrStar arr[k]! orig acc)
    accPf := match pa, q with
      | none, none => none
      | some pa, none => some pa
      | none, some q => some q
      | some pa, some q => some (c.eqTrans start mid acc' pa q)
    acc := acc'
  let pf := match p1, accPf with
    | none, none => none
    | some p, none => some p
    | none, some q => some q
    | some p, some q => some (c.eqTrans x flatE acc p q)
  return (acc, pf)

meta partial def combine (c : NCtx) (a b : Expr) : MetaM (Expr × Option Expr) := do
  let e := c.mkStar a b
  let exLam := fun (x : Expr) => NCtx.isOp c.exOp x && (NCtx.arg c.exOp x 1).isLambda
  if exLam b || exLam a then
    let right := exLam b
    let x := if right then b else a
    let ax := NCtx.arg c.exOp x 0
    let jx := NCtx.arg c.exOp x 1
    let lv ← normLevel ax
    let some ins ← c.lawsAtLv? lv | throwError "xsimpl: no instance"
    let eq1 := if right then c.lemAt ins ``nt_eq_exr #[ax, a, jx]
      else c.lemAt ins ``nt_eq_exl #[ax, jx, b]
    let body1 := if right then c.mkStar a jx.bindingBody! else c.mkStar jx.bindingBody! b
    let mkEx := fun (j : Expr) => mkAppN x.getAppFn (x.getAppArgs.set! c.exOp.pos[1]! j)
    let e1 := mkEx (.lam jx.bindingName! ax body1 jx.bindingInfo!)
    let r ← withLocalDeclD jx.bindingName! ax fun y => do
      let inner := jx.bindingBody!.instantiate1 y
      let (bd', pb) ← if right then combine c a inner else combine c inner b
      match pb with
      | none => return none
      | some pb => return some (← mkLambdaFVars #[y] bd', ← mkFunExt (← mkLambdaFVars #[y] pb))
    match r with
    | none => return (e1, some eq1)
    | some (j', pj) =>
      let f ← withLocalDeclD `k (← inferType jx) fun k => mkLambdaFVars #[k] (mkEx k)
      return (mkEx j', some (c.eqTrans e e1 (mkEx j') eq1 (← mkCongrArg f pj)))
  else
    let (l, p) := c.flat e
    return (c.starL l, p)

meta partial def wandNorm (c : NCtx) (w : NOp) (e : Expr) : MetaM (Expr × Option Expr) := do
  let mkW := fun (a b : Expr) =>
    mkAppN e.getAppFn ((e.getAppArgs.set! w.pos[0]! a).set! w.pos[1]! b)
  let a := NCtx.arg w e 0
  let b := NCtx.arg w e 1
  let (a', pa) ← nestNorm c a
  let (b', pb) ← nestNorm c b
  let mut cur := e
  let mut pf : Option Expr := none
  let step := fun (pf : Option Expr) (lhs mid rhs q : Expr) =>
    match pf with
    | none => q
    | some p => c.eqTrans lhs mid rhs p q
  if let some pa := pa then
    let f ← withLocalDeclD `y c.carrier fun y => mkLambdaFVars #[y] (mkW y b)
    let nxt := mkW a' b
    pf := some (step pf e cur nxt (← mkCongrArg f pa))
    cur := nxt
  if let some pb := pb then
    let f ← withLocalDeclD `y c.carrier fun y => mkLambdaFVars #[y] (mkW a' y)
    let nxt := mkW a' b'
    pf := some (step pf e cur nxt (← mkCongrArg f pb))
    cur := nxt
  if NCtx.isOp c.starOp a' then
    let x := NCtx.arg c.starOp a' 0
    let y := NCtx.arg c.starOp a' 1
    let inner := mkW y b'
    let (inner', pi) ← itemNorm c inner
    let nxt := mkW x inner
    let q := c.lem ``nt_curry #[x, y, b']
    pf := some (step pf e cur nxt q)
    cur := nxt
    if let some pi := pi then
      let f ← withLocalDeclD `y c.carrier fun z => mkLambdaFVars #[z] (mkW x z)
      let nxt2 := mkW x inner'
      pf := some (step pf e cur nxt2 (← mkCongrArg f pi))
      cur := nxt2
  return (cur, pf)

meta partial def argNorm (c : NCtx) (x : Expr) : MetaM (Expr × Option Expr) := do
  let .lam n ty b bi := x | nestNorm c x
  withLocalDecl n bi ty fun v => do
    let (b', pb) ← argNorm c (b.instantiate1 v)
    match pb with
    | none => return (x, none)
    | some pb => return (← mkLambdaFVars #[v] b', some (← mkFunExt (← mkLambdaFVars #[v] pb)))

meta partial def itemNorm (c : NCtx) (e : Expr) : MetaM (Expr × Option Expr) := do
  if NCtx.isOp c.exOp e then
    let j := NCtx.arg c.exOp e 1
    unless j.isLambda do return (e, none)
    let a := NCtx.arg c.exOp e 0
    let r ← withLocalDeclD j.bindingName! a fun v => do
      let (b', pb) ← nestNorm c (j.bindingBody!.instantiate1 v)
      match pb with
      | none => return none
      | some pb => return some (← mkLambdaFVars #[v] b', ← mkFunExt (← mkLambdaFVars #[v] pb))
    let some (j', pj) := r | return (e, none)
    let e' := mkAppN e.getAppFn (e.getAppArgs.set! c.exOp.pos[1]! j')
    let f ← withLocalDeclD `y (← inferType j) fun y =>
      mkLambdaFVars #[y] (mkAppN e.getAppFn (e.getAppArgs.set! c.exOp.pos[1]! y))
    return (e', some (← mkCongrArg f pj))
  if NCtx.isOp c.pureOp e then
    let pr := NCtx.arg c.pureOp e 0
    unless NCtx.selfEq pr do return (e, none)
    let q ← if pr.isAppOf ``Eq then mkAppM ``eq_self #[pr.appArg!] else mkAppM ``iff_self #[pr.appArg!]
    let args := e.getAppArgs
    let e' := mkAppN e.getAppFn (args.set! c.pureOp.pos[0]! (mkConst ``True))
    let f ← withLocalDeclD `y (mkSort Level.zero) fun y =>
      mkLambdaFVars #[y] (mkAppN e.getAppFn (args.set! c.pureOp.pos[0]! y))
    return (e', some (← mkCongrArg f q))
  if !c.bad e then return (e, none)
  if let some w := c.wandOp then
    if NCtx.isOp w e then return ← wandNorm c w e
  let args := e.getAppArgs
  let mut cur := args
  let mut pf : Option Expr := none
  for i in [0 : args.size] do
    if !c.bad args[i]! then continue
    let (a', q) ← argNorm c args[i]!
    let some q := q | continue
    let next := cur.set! i a'
    let f ← withLocalDeclD `y (← inferType args[i]!) fun y =>
      mkLambdaFVars #[y] (mkAppN e.getAppFn (cur.set! i y))
    let step ← mkCongrArg f q
    pf := some (← match pf with
      | none => pure step
      | some p0 => mkEqTrans p0 step)
    cur := next
  return (mkAppN e.getAppFn cur, pf)

end

meta def flatN (c : NCtx) (e : Expr) : MetaM (List Expr × Option Expr) := do
  let (s, p) := c.flat e
  let needs := fun (it : Expr) =>
    if NCtx.isOp c.pureOp it then NCtx.selfEq (NCtx.arg c.pureOp it 0)
    else !NCtx.isOp c.exOp it && c.bad it
  if !s.any needs then return (s, p)
  let (s', q) ← itemsNorm c e s p
  return (s', q)

meta def flatGoalL (c : NCtx) (cur : MVarId) (l r : Expr) : MetaM (MVarId × List Expr) :=
    cur.withContext do
  let (s, p) ← flatN c l
  match p with
  | none => return (cur, s)
  | some p =>
    let ls := c.starL s
    let g ← newGoal cur (c.mkEnt ls r) fun m => c.trans l ls r (c.lem ``nt_of_eq #[l, ls, p]) m
    return (g, s)

meta def flatGoalR (c : NCtx) (cur : MVarId) (l r : Expr) : MetaM (MVarId × List Expr) :=
    cur.withContext do
  let (t, p) ← flatN c r
  match p with
  | none => return (cur, t)
  | some p =>
    let lt := c.starL t
    let g ← newGoal cur (c.mkEnt l lt) fun m =>
      c.trans l lt r m (c.lem ``nt_of_eq #[lt, r, c.eqSymm r lt p])
    return (g, t)

meta def pureBlockPf (c : NCtx) (s : List Expr) : Option Expr × Expr × List Expr × List Expr := Id.run do
  let arr := s.toArray
  let n := arr.size
  let last := arr[n - 1]!
  let isP := fun (e : Expr) => NCtx.isOp c.pureOp e
  let mut P : Option Expr := if isP last then some last else none
  let mut R : Option Expr := if isP last then none else some last
  let mut ps : Array Expr := if isP last then #[last] else #[]
  let mut cs : List Expr := if isP last then [] else [last]
  let mut tail := last
  let mut pf : Option Expr := none
  let assemble := fun (P R : Option Expr) => match P, R with
    | some p, some r => c.mkStar p r
    | some p, none => p
    | none, some r => r
    | none, none => c.empE
  let mut j := n - 1
  while j > 0 do
    j := j - 1
    let x := arr[j]!
    let A := assemble P R
    let src := c.mkStar x tail
    let framed := pf.map (fun q => c.lem ``nt_frame #[x, tail, A, q])
    let (P', R', step) : Option Expr × Option Expr × Option Expr :=
      if isP x then
        match P, R with
        | none, some r => (some x, some r, none)
        | some p, none => (some (c.mkStar p x), none, some (c.lem ``nt_comm #[x, p]))
        | some p, some r => (some (c.mkStar p x), some r, some (c.lem ``nt_pushl #[x, p, r]))
        | none, none => (some x, none, none)
      else
        match P, R with
        | none, some r => (none, some (c.mkStar x r), none)
        | some p, none => (some p, some x, some (c.lem ``nt_comm #[x, p]))
        | some p, some r => (some p, some (c.mkStar x r), some (c.lem ``nt_swap #[x, p, r]))
        | none, none => (none, some x, none)
    let A' := assemble P' R'
    pf := match framed, step with
      | none, none => none
      | some f, none => some f
      | none, some st => some st
      | some f, some st => some (c.trans src (c.mkStar x A) A' f st)
    if isP x then ps := ps.push x else cs := x :: cs
    P := P'
    R := R'
    tail := src
  let k := ps.size
  let mut m := k
  while m > 1 do
    m := m - 1
    let y := ps[m]!
    let L := c.starLeft (ps.extract 0 m)
    match R with
    | none => R := some y
    | some r =>
      let A := c.mkStar (c.mkStar L y) r
      let A' := c.mkStar L (c.mkStar y r)
      let st := c.lem ``nt_of_eq #[A, A', c.lem ``nt_assoc #[L, y, r]]
      pf := some (match pf with
        | none => st
        | some q => c.trans (c.starL s) A A' q st)
      R := some (c.mkStar y r)
    P := some L
  let mid := c.starL (ps.toList ++ cs)
  return (pf, mid, ps.toList, cs)

mutual

meta partial def peelPures (c : NCtx) (inst : Level → MetaM LawsAt) (lctx0 : LocalContext)
    (li0 : LocalInstances) (rr : Expr) (typeEx leftPure : Bool) (xs : Array Expr)
    (ps cs : List Expr) : MetaM (Expr × Array Expr × List Expr × Expr) := do
  match ps with
  | [] => lhsRec c inst lctx0 li0 rr typeEx leftPure xs cs
  | it :: rest =>
    let p := NCtx.arg c.pureOp it 0
    let pA := p.abstract xs
    let restL := rest ++ cs
    withLocalDecl `a .default p fun h => do
      let (m, xsF, sF, inner) ← peelPures c inst lctx0 li0 rr typeEx leftPure (xs.push h) rest cs
      let lam := Expr.lam `a pA inner .default
      if restL.isEmpty then
        return (m, xsF, sF, c.lem ``nt_purel1 #[pA, rr, lam])
      else
        return (m, xsF, sF, c.lem ``nt_purel #[pA, (c.starL restL).abstract xs, rr, lam])

meta partial def lhsRec (c : NCtx) (inst : Level → MetaM LawsAt) (lctx0 : LocalContext)
    (li0 : LocalInstances) (rr : Expr) (typeEx leftPure : Bool) (xs : Array Expr)
    (s : List Expr) : MetaM (Expr × Array Expr × List Expr × Expr) := do
  let abs := fun (e : Expr) => e.abstract xs
  if !typeEx && !s.any (NCtx.isOp c.exOp) && (s.filter (NCtx.isOp c.pureOp)).length ≥ 2 then
    let (pf, mid, ps, cs) := pureBlockPf c s
    let (m, xsF, sF, inner) ← peelPures c inst lctx0 li0 rr typeEx leftPure xs ps cs
    return (m, xsF, sF, c.transO (abs (c.starL s)) (abs mid) rr (pf.map abs) inner)
  match c.pick s typeEx leftPure with
  | none =>
    let ty ← mkForallFVars xs (c.mkEnt (c.starL s) rr)
    let m ← mkFreshExprMVarAt lctx0 li0 ty
    let k := xs.size
    return (m, xs, s, mkAppN m ((List.range k).toArray.map (fun i => .bvar (k - 1 - i))))
  | some i =>
    let n := s.length
    let arr := s.toArray
    let ls := c.starL s
    match c.item arr[i]! with
    | .ex a j =>
      let lv ← normLevel a
      let ins ← inst lv
      let (bn, jb) := NCtx.exBody j
      let mut pf : Option Expr := none
      let mut body := jb
      if i + 1 < n then
        let q := c.starL (s.drop (i+1))
        pf := some (c.lemAt ins ``nt_exl_base #[a, j, q])
        body := c.mkStar jb q
      let mut k := i
      while k > 0 do
        k := k - 1
        let x := c.starL (s.drop (k+1))
        let kl := Expr.lam bn a body .default
        let h := pf.getD (c.lemAt ins ``nt_refl #[x])
        pf := some (c.lemAt ins ``nt_exl_layer #[a, kl, x, arr[k]!, h])
        body := c.mkStar arr[k]! body
      let kl := Expr.lam bn a body .default
      let exK := mkOp ins.ops[4]! #[a, kl]
      let aA := abs a
      let klA := abs kl
      let head := c.transO (abs ls) (abs exK) rr (pf.map abs)
      withLocalDecl bn .default a fun x => do
        let xs2 := xs.push x
        let bx := body.instantiate1 x
        let (s2, p) ← flatN c bx
        let (m, xsF, sF, inner) ← lhsRec c inst lctx0 li0 rr typeEx leftPure xs2 s2
        let inner := match p with
          | none => inner
          | some p =>
            let bxA := bx.abstract xs2
            let ls2A := (c.starL s2).abstract xs2
            c.trans bxA ls2A rr (c.lem ``nt_of_eq #[bxA, ls2A, p.abstract xs2]) inner
        return (m, xsF, sF, head (c.lemAt ins ``nt_exl #[aA, klA, rr, .lam bn aA inner .default]))
    | .pure p =>
      let pA := abs p
      if n == 1 then
        withLocalDecl `a .default p fun h => do
          let (m, xsF, sF, inner) ← lhsRec c inst lctx0 li0 rr typeEx leftPure (xs.push h) []
          return (m, xsF, sF, c.lem ``nt_purel1 #[pA, rr, .lam `a pA inner .default])
      else
        let rest := s.eraseIdx i
        let lr := c.starL rest
        let pl := if i == 0 then none else some (c.pullL s i)
        let lrA := abs lr
        let head := c.transO (abs ls) (abs (c.mkStar arr[i]! lr)) rr (pl.map abs)
        withLocalDecl `a .default p fun h => do
          let (m, xsF, sF, inner) ← lhsRec c inst lctx0 li0 rr typeEx leftPure (xs.push h) rest
          return (m, xsF, sF, head (c.lem ``nt_purel #[pA, lrA, rr, .lam `a pA inner .default]))
    | .atom => throwError "xsimpl: native step on an atom"

end

meta def lhsBatch (c : NCtx) (inst : Level → MetaM LawsAt) (cur : MVarId) (s : List Expr) (rr : Expr)
    (typeEx leftPure : Bool) : MetaM (MVarId × List Expr × Nat) := cur.withContext do
  let (m, xsF, sF, pf) ← lhsRec c inst (← getLCtx) (← getLocalInstances) rr typeEx leftPure #[] s
  cur.assign pf
  let (fvs, g2) ← m.mvarId!.introN xsF.size
  return (g2, sF.map (·.replaceFVars xsF (fvs.map mkFVar)), xsF.size)

meta def rhsStep (c : NCtx) (inst : Level → MetaM LawsAt) (cur : MVarId) (ls : Expr) (tt : List Expr)
    (jx : Nat) : MetaM (MVarId × List Expr × Expr) := cur.withContext do
  let n := tt.length
  let arr := tt.toArray
  let lt := c.starL tt
  match c.item arr[jx]! with
  | .ex a j =>
    let lv ← normLevel a
    let ins ← inst lv
    let (bn, jb) := NCtx.exBody j
    let mut pf : Option Expr := none
    let mut body := jb
    if jx + 1 < n then
      let q := c.starL (tt.drop (jx+1))
      pf := some (c.lemAt ins ``nt_exr_base #[a, j, q])
      body := c.mkStar jb q
    let mut k := jx
    while k > 0 do
      k := k - 1
      let x := c.starL (tt.drop (k+1))
      let kl := Expr.lam bn a body .default
      let h := pf.getD (c.lemAt ins ``nt_refl #[x])
      pf := some (c.lemAt ins ``nt_exr_layer #[a, kl, x, arr[k]!, h])
      body := c.mkStar arr[k]! body
    let kl := Expr.lam bn a body .default
    let exK := mkOp ins.ops[4]! #[a, kl]
    let y ← mkFreshExprMVar a (userName := bn)
    let nr := body.instantiate1 y
    let m ← newGoal cur (c.mkEnt ls nr) fun m =>
      c.transO' ls exK lt (c.lemAt ins ``nt_exr #[a, y, kl, ls, m]) pf
    let (g2, t') ← flatGoalR c m ls nr
    return (g2, t', y)
  | .pure p =>
    let q ← mkFreshExprMVar p (userName := `x)
    if p.isConstOf ``True then q.mvarId!.assign (mkConst ``True.intro)
    if n == 1 then
      let g2 ← newGoal cur (c.mkEnt ls c.empE) fun m => c.lem ``nt_purer1 #[p, ls, q, m]
      return (g2, [], q)
    else
      let rest := tt.eraseIdx jx
      let lr := c.starL rest
      let pl := if jx == 0 then none else some (c.pullR tt jx)
      let g2 ← newGoal cur (c.mkEnt ls lr) fun m =>
        c.transO' ls (c.mkStar arr[jx]! lr) lt (c.lem ``nt_purer #[p, ls, lr, q, m]) pl
      return (g2, rest, q)
  | .atom => throwError "xsimpl: native step on an atom"

meta def cancelScan (sa ta : Array Expr) : MetaM (Array (Nat × Nat) × Array Bool × Array Nat) := do
  let cheap ← cheapCancel.get
  let mut lAlive : Array Bool := sa.map (fun _ => true)
  let mut pairs : Array (Nat × Nat) := #[]
  let mut tIdx : Array Nat := (List.range ta.size).toArray
  let sI ← sa.mapM instantiateMVars
  let tI ← ta.mapM instantiateMVars
  if !sI.any (·.hasMVar) && !tI.any (·.hasMVar) then
    let mut at_ : Std.HashMap Expr (List Nat) := {}
    for li in (List.range sI.size).reverse do
      at_ := at_.insert sI[li]! (li :: at_.getD sI[li]! [])
    let mut rest : Array Nat := #[]
    for ri in [0 : tI.size] do
      match at_.getD tI[ri]! [] with
      | li :: more =>
        at_ := at_.insert tI[ri]! more
        pairs := pairs.push (li, ri)
        lAlive := lAlive.set! li false
      | [] => rest := rest.push ri
    tIdx := rest
  let mut rStart := 0
  let mut cont := true
  while cont do
    cont := false
    let mut found : Option (Nat × Nat) := none
    for r in [rStart : tIdx.size] do
      let ri ← instantiateMVars ta[tIdx[r]!]!
      if ri.isMVar then continue
      for li in [0 : sa.size] do
        unless lAlive[li]! do continue
        let le ← instantiateMVars sa[li]!
        if le.isMVar then continue
        let mv := le.hasMVar || ri.hasMVar
        if cheap && !mv && le != ri then
          match le.getAppFn, ri.getAppFn with
          | .const a _, .const b _ =>
            if a != b && !(← isReducible a) && !(← isReducible b) then continue
          | _, _ => pure ()
        if ← cheapDefEq le ri then
          found := some (li, r)
          rStart := if mv then 0 else r
          break
      if found.isSome then break
    if let some (li, r) := found then
      pairs := pairs.push (li, tIdx[r]!)
      lAlive := lAlive.set! li false
      tIdx := tIdx.eraseIdx! r
      cont := true
  return (pairs, lAlive, tIdx)

meta def cancelStep (c : NCtx) (cur : MVarId) (s tt : List Expr) :
    MetaM (Option (Option MVarId × List Expr × List Expr)) :=
  cur.withContext do
  let (pairs, lAlive, tIdx) ← cancelScan s.toArray tt.toArray
  if pairs.isEmpty then return none
  let ta ← tt.toArray.mapM instantiateMVars
  let sa ← s.toArray.mapM instantiateMVars
  let cl := pairs.toList.map (fun (li, _) => sa[li]!)
  let cr : List Expr := pairs.toList.map (fun (_, ri) => ta[ri]!)
  for x in cr do trace[xsimpl] m!"Cancelling {x}"
  let lRestIdx := (List.range sa.size).filter (fun i => lAlive[i]!)
  let sr := lRestIdx.map (sa[·]!)
  let tr := tIdx.toList.map (ta[·]!)
  let pl := c.permIdx sa (pairs.toList.map (·.1) ++ lRestIdx)
  let u := cr ++ tr
  let pos := (List.range ta.size).map (fun k =>
    match pairs.findIdx? (·.2 == k) with
    | some p => p
    | none => cr.length + tIdx.toList.idxOf k)
  let pr := c.permIdx u.toArray pos
  let ls := c.starL sa.toList
  let lcl := c.starL (cl ++ sr)
  let lcr := c.starL (cl ++ tr)
  let lt := c.starL ta.toList
  let body := fun (mv : Expr) =>
    c.transO ls lcl lt pl (c.transO' lcl lcr lt
      (c.lem ``nt_frame_list #[c.atomList cl, c.atomList sr, c.atomList tr, mv]) pr)
  if sr.isEmpty && tr.isEmpty then
    cur.assign (body (c.lem ``nt_refl #[c.empE]))
    return some (none, [], [])
  let g2 ← newGoal cur (c.mkEnt (c.starL sr) (c.starL tr)) body
  return some (some g2, sr, tr)

meta def closeRefl (c : NCtx) (g : MVarId) (l r : Expr) : MetaM Bool := g.withContext do
  unless ← cheapDefEq l r do return false
  g.assign (c.lem ``nt_refl #[l])
  return true

meta def wholeEq (c : NCtx) (g : MVarId) (l r : Expr) : MetaM Bool := do
  if l.hasExprMVar || r.hasExprMVar then return false
  closeRefl c g l r

meta def residualEq (c : NCtx) (g : MVarId) (created : Array Expr) (l r : Expr) : MetaM Bool := do
  let l ← instantiateMVars l
  let r ← instantiateMVars r
  let ok := fun (e : Expr) => (e.find? fun x => x.isMVar && !created.contains x).isNone
  unless ok l && ok r do return false
  closeRefl c g l r

meta def permClose (c : NCtx) (g : MVarId) (s : List Expr) (r : Expr) : MetaM Bool := g.withContext do
  let binder := fun (e : Expr) => NCtx.isOp c.exOp e || NCtx.isOp c.pureOp e
  unless s.any binder || (r.find? binder).isSome do return false
  let (t, _) ← flatN c r
  unless s.length == t.length do return false
  if s.any (·.hasExprMVar) || t.any (·.hasExprMVar) then return false
  let (pairs, _, _) ← cancelScan s.toArray t.toArray
  unless pairs.size == s.length do return false
  let (g2, t2) ← flatGoalR c g (c.starL s) r
  let some (none, _, _) ← cancelStep c g2 s t2 | return false
  return true

meta def appTag (t n : Name) : Name := if t.isAnonymous then n else appendTag t n

meta partial def nativeGoal (g : MVarId) : MetaM (Option (List MVarId)) := g.withContext do
  let some (g, c, l0, r0) ← sepGoal? g | return none
  let some accL ← c.spine l0 {} | return none
  let some accR ← c.spine r0 { accL with hasEx := false } | return none
  let lvs := accR.lvs
  let rHasEx := accR.hasEx
  let foreverA := accR.nestedTypeEx
  let typeEx := lvs.any (· != Level.zero)
  let mut insts : Array (Level × LawsAt) := #[(c.lv0, { lv := c.lv0, ops := c.ops0, inst := c.inst0 })]
  for lv in lvs do
    if insts.any (·.1 == lv) then continue
    let some i ← c.lawsAtLv? lv | return none
    insts := insts.push (lv, i)
  let inst : Level → MetaM LawsAt := fun lv => do
    match insts.find? (·.1 == lv) with
    | some (_, i) => return i
    | none =>
      let some i ← c.lawsAtLv? lv | throwError "xsimpl: no instance"
      return i
  if ← wholeEq c g l0 r0 then return some []
  let mut tag ← g.getTag
  let (g1, s1) ← flatGoalL c g l0 r0
  if ← permClose c g1 s1 r0 then return some []
  let mut changed := g1 != g
  let mut cur := g1
  let mut s := s1
  let leftPure := typeEx && (rHasEx || foreverA)
  if (c.pick s typeEx leftPure).isSome then
    changed := true
    let (g2, s2, k) ← lhsBatch c inst cur s r0 typeEx leftPure
    for _ in [0 : k] do
      tag := appTag tag `a
    g2.setTag tag
    cur := g2
    s := s2
  let ls := c.starL s
  let (g3, t3) ← flatGoalR c cur ls r0
  if g3 != cur then changed := true
  cur := g3
  let mut tt := t3
  let mut created : Array Expr := #[]
  repeat
    let some j := (if foreverA then c.pickEx tt else c.pick tt typeEx false) | break
    changed := true
    let (g4, t4, y) ← rhsStep c inst cur ls tt j
    y.mvarId!.setTag (appTag tag `x)
    tag := appTag tag `a
    g4.setTag tag
    cur := g4
    tt := t4
    created := created.push y
  let (res, sr, tr) ← match ← cancelStep c cur s tt with
    | none => pure (some cur, s, tt)
    | some (r, sr, tr) =>
      changed := true
      if let some r := r then r.setTag `a
      pure (r, sr, tr)
  let mut res := res
  let mut tr := tr
  let mut pures : List MVarId := []
  if foreverA then
    if let some r0 := res then
      let mut r := r0
      let lsr := c.starL sr
      repeat
        let some j := (List.range tr.length).find? (fun k => NCtx.isOp c.pureOp tr[k]!) | break
        changed := true
        let (r2, tr2, q) ← rhsStep c inst r lsr tr j
        r := r2
        tr := tr2
        pures := pures ++ [q.mvarId!]
      res := some r
  if let some r := res then
    if ← residualEq c r created (c.starL sr) (c.starL tr) then
      changed := true
      res := none
  if let (some w, some r0) := (c.wandOp, res) then
    let mut r := r0
    repeat
      let tra ← r.withContext (tr.toArray.mapM instantiateMVars)
      let mut hit : Option Nat := none
      for j in [0 : tra.size] do
        let t := tra[j]!
        unless NCtx.isOp w t do continue
        let a := NCtx.arg w t 0
        let b := NCtx.arg w t 1
        if a.hasExprMVar || b.hasExprMVar then continue
        if ← r.withContext (cheapDefEq a b) then
          hit := some j
          break
      let some j := hit | break
      changed := true
      let rest := (List.range tra.size).filter (· != j)
      let restE := rest.map (tra[·]!)
      let a := NCtx.arg w tra[j]! 0
      let inv := (List.range tra.size).map (fun k => if k == j then 0 else if k < j then k + 1 else k)
      let mid := c.starL (tra[j]! :: restE)
      let rt := c.starL tra.toList
      let lsr := c.starL sr
      let ty := c.mkEnt lsr (c.starL restE)
      r ← newGoal r ty fun m =>
        c.transO' lsr mid rt (if restE.isEmpty then c.lem ``nt_wand_same1 #[a, lsr, m]
          else c.lem ``nt_wand_same #[a, lsr, c.starL restE, m]) (c.perm (tra[j]! :: restE) inv)
      tr := restE
    res := some r
    if tr.isEmpty then
      if ← closeRefl c r (c.starL sr) c.empE then res := none
  let mut sub : Option (List MVarId) := none
  if let (some w, some r) := (c.wandOp, res) then
    let sr ← r.withContext (sr.mapM instantiateMVars)
    if tr.length == 1 && NCtx.isOp w tr[0]! then
      let a := NCtx.arg w tr[0]! 0
      let b := NCtx.arg w tr[0]! 1
      let lsr := c.starL sr
      let g' ← newGoal r (c.mkEnt (c.mkStar lsr a) b) fun m => c.lem ``nt_wand_r #[lsr, a, b, m]
      sub := some ((← nativeGoal g').getD [g'])
    else
      let arr := sr.toArray
      let mut hit : Option (Nat × Nat) := none
      for l in [0 : arr.size] do
        if hit.isSome then break
        unless NCtx.isOp w arr[l]! do continue
        let prem := NCtx.arg w arr[l]! 0
        for l2 in [0 : arr.size] do
          if l2 == l then continue
          if ← r.withContext (cheapDefEq prem arr[l2]!) then
            hit := some (l, l2)
            break
      if let some (l, l2) := hit then
        let rest := (List.range arr.size).filter (fun k => k != l && k != l2)
        let order := [l2, l] ++ rest
        let pm := c.perm sr order
        let a := NCtx.arg w arr[l]! 0
        let b := NCtx.arg w arr[l]! 1
        let restE := rest.map (arr[·]!)
        let rt := c.starL tr
        let src := c.starL sr
        let mid := c.starL (order.map (arr[·]!))
        let lr := c.starL restE
        let ty := if restE.isEmpty then c.mkEnt b rt else c.mkEnt (c.mkStar b lr) rt
        let g' ← newGoal r ty fun m =>
          c.transO src mid rt pm (if restE.isEmpty then c.lem ``nt_wand_l1 #[a, b, rt, m]
            else c.lem ``nt_wand_l #[a, b, lr, rt, m])
        sub := some ((← nativeGoal g').getD [g'])
  if sub.isSome then changed := true
  unless changed do return some [g]
  let mut out : List MVarId := pures
  match sub with
  | some o => out := out ++ o
  | none => if let some r := res then out := out ++ [r]
  for y in created.reverse do
    if let .mvar id ← instantiateMVars y then
      unless ← id.isAssigned do out := out ++ [id]
  return some out

meta def nativeOrNone (g : MVarId) : MetaM (Option (List MVarId)) := do
  let s ← saveState
  try
    let r ← nativeGoal g
    if r.isNone then s.restore
    return r
  catch _ =>
    s.restore
    return none

mutual

meta partial def driveOne (extra : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) (g : MVarId) :
    TacticM (List MVarId) := do
  if ← g.isAssigned then return []
  withExtra extra ((← nativeOrNone g).getD [g])

meta partial def withExtra (extra : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
    (hs : List MVarId) : TacticM (List MVarId) := do
  match extra with
  | none => return hs
  | some e =>
    let mut out : List MVarId := []
    for h in hs do
      if ← h.isAssigned then continue
      setGoals [h]
      if ← tryTactic (evalTactic e) then
        for h2 in ← getUnsolvedGoals do
          out := out ++ (← driveOne extra h2)
      else
        out := out ++ [h]
    return out

end

meta def xsimplDriver (extra : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq)) : TacticM Unit := do
  let mut out : List MVarId := []
  for g in ← getGoals do
    out := out ++ (← driveOne extra g)
  setGoals out

syntax "xsimpl_core_with " tacticSeq : tactic
elab_rules : tactic
  | `(tactic| xsimpl_core_with $extra) => xsimplDriver (some extra)

syntax "xsimpl_core" : tactic
elab_rules : tactic
  | `(tactic| xsimpl_core) => xsimplDriver none

meta def affineEmpProof? (c : NCtx) (l : Expr) : MetaM (Option Expr) := do
  let some aff ← affineLaws? c | return none
  return some (c.lemAt aff ``AffineSepLaws.entails_emp #[l])

meta def isEmpRhs (c : NCtx) (r : Expr) : MetaM Bool := do
  if NCtx.isOp c.empOp r || NCtx.isOp c.empOp (← whnfR r) then return true
  if r.hasExprMVar then return false
  isDefEq r c.empE

meta def affineEmp (c : NCtx) (g : MVarId) (l r : Expr) : MetaM Bool := do
  unless ← isEmpRhs c r do return false
  let some pf ← affineEmpProof? c l | return false
  unless ← isDefEq (← inferType pf) (← g.getType) do return false
  g.assign pf
  return true

meta def closeEqRefl (g : MVarId) : MetaM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let some (_, a, b) := t.eq? | return false
  if a.hasExprMVar || b.hasExprMVar then return false
  unless ← withReducibleAndInstances (isDefEq a b) do return false
  g.assign (← mkEqRefl a)
  return true

meta def xsimplClean : TacticM Unit := do
  let g ← getMainGoal
  let (g, done) ← g.withContext do
    match ← sepGoal? g with
    | some (g, c, l, r) => g.withContext do
      if ← closeRefl c g l r then return (g, true)
      if ← cheapAssumptionCore g then return (g, true)
      return (g, ← affineEmp c g l r)
    | none =>
      if ← cheapAssumptionCore g then return (g, true)
      return (g, ← closeEqRefl g)
  replaceMainGoal (if done then [] else [g])

syntax "xsimpl_clean" : tactic
elab_rules : tactic
  | `(tactic| xsimpl_clean) => xsimplClean

syntax "xsimpl" : tactic
macro_rules
  | `(tactic| xsimpl) => `(tactic| (
      xsimpl_core
      all_goals (
        try xsimpl_clean
      )
    ))

end Sep.Xsimpl
