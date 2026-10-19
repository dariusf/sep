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

theorem hpure_true {P : Prop} (hp : P) : (⌈P⌉ : HProp) = HProp.hempty := by
  funext h
  exact propext ⟨fun hh => (HProp.hpure_elim_hempty hh).2,
    fun hh => HProp.hpure_intro_hempty hh hp⟩

theorem hstar_hexists_rr {A : Sort _} (H : HProp) (J : A → HProp) :
    H ✶ (HProp.hexists J) = ∃✶ x, H ✶ J x := by
  rw [HProp.hstar_comm, HProp.hstar_hexists]
  exact congrArg _ (funext fun x => HProp.hstar_comm _ _)

def hdisj (H1 H2 : HProp) : HProp := fun h => H1 h ∨ H2 h

theorem contra_pure {P : Prop} {H R : HProp} (h1 : ∀ h, H h → P)
    (h2 : ∀ h, H h → ¬P) : H ==> R := fun h hh => absurd (h1 h hh) (h2 h hh)

theorem contra_ne_self {α : Sort _} {a : α} {H R : HProp}
    (h : ∀ h, H h → a ≠ a) : H ==> R := fun hh hx => absurd rfl (h hh hx)

theorem hdisj_star_l (H1 H2 K : HProp) :
    hdisj H1 H2 ✶ K = hdisj (H1 ✶ K) (H2 ✶ K) := by
  funext h
  apply propext
  constructor
  · intro hh
    obtain ⟨h1, h2, ha, hb, hd, he⟩ := HProp.hstar_elim hh
    rcases ha with ha | ha
    · exact Or.inl (he ▸ HProp.hstar_intro ha hb hd)
    · exact Or.inr (he ▸ HProp.hstar_intro ha hb hd)
  · intro hh
    rcases hh with hh | hh
    · obtain ⟨h1, h2, ha, hb, hd, he⟩ := HProp.hstar_elim hh
      exact he ▸ HProp.hstar_intro (show hdisj H1 H2 h1 from Or.inl ha) hb hd
    · obtain ⟨h1, h2, ha, hb, hd, he⟩ := HProp.hstar_elim hh
      exact he ▸ HProp.hstar_intro (show hdisj H1 H2 h1 from Or.inr ha) hb hd

theorem hdisj_star_r (K H1 H2 : HProp) :
    K ✶ hdisj H1 H2 = hdisj (K ✶ H1) (K ✶ H2) := by
  rw [HProp.hstar_comm, hdisj_star_l, HProp.hstar_comm K H1, HProp.hstar_comm K H2]

theorem hdisj_hexists {A : Sort _} (J K : A → HProp) :
    HProp.hexists (fun x => hdisj (J x) (K x))
      = hdisj (HProp.hexists J) (HProp.hexists K) := by
  funext h
  simp only [HProp.hexists, hdisj]
  exact propext exists_or

theorem hdisj_elim {H1 H2 H : HProp} (h1 : H1 ==> H) (h2 : H2 ==> H) :
    hdisj H1 H2 ==> H := by
  intro h hh
  rcases hh with hh | hh
  · exact h1 h hh
  · exact h2 h hh

theorem hdisj_left {H H1 H2 : HProp} (h : H ==> H1) : H ==> hdisj H1 H2 :=
  fun h' hh => Or.inl (h h' hh)

theorem hdisj_right {H H1 H2 : HProp} (h : H ==> H2) : H ==> hdisj H1 H2 :=
  fun h' hh => Or.inr (h h' hh)

def hasLoc (p : Loc) (H : HProp) : Prop := ∀ h, H h → p ∈ h

def neLocs (p q : Loc) (H : HProp) : Prop := ∀ h, H h → p ≠ q

theorem hasLoc_single (p : Loc) (v : val) : hasLoc p (HProp.hsingle p v) := by
  intro h hh
  simp only [HProp.hsingle] at hh
  rw [hh]
  exact (Finmap.mem_singleton p p v).2 rfl

theorem hasLoc_star_l {p : Loc} {H1 H2 : HProp} (h1 : hasLoc p H1) :
    hasLoc p (H1 ✶ H2) := by
  intro h hh
  obtain ⟨a, b, ha, hb, hd, he⟩ := HProp.hstar_elim hh
  rw [he]
  exact Finmap.mem_union.2 (Or.inl (h1 a ha))

theorem hasLoc_star_r {p : Loc} {H1 H2 : HProp} (h2 : hasLoc p H2) :
    hasLoc p (H1 ✶ H2) := by
  intro h hh
  obtain ⟨a, b, ha, hb, hd, he⟩ := HProp.hstar_elim hh
  rw [he]
  exact Finmap.mem_union.2 (Or.inr (h2 b hb))

theorem hasLoc_hexists {A : Sort _} {p : Loc} {J : A → HProp}
    (h : ∀ a, hasLoc p (J a)) : hasLoc p (HProp.hexists J) := by
  intro hh hj
  simp only [HProp.hexists] at hj
  obtain ⟨a, ha⟩ := hj
  exact h a hh ha

theorem hasLoc_disj {p : Loc} {H1 H2 : HProp} (h1 : hasLoc p H1)
    (h2 : hasLoc p H2) : hasLoc p (hdisj H1 H2) := by
  intro h hh
  rcases hh with hh | hh
  · exact h1 h hh
  · exact h2 h hh

theorem hasLoc_pure_star {p : Loc} {P : Prop} {H : HProp}
    (h : P → hasLoc p H) : hasLoc p (⌈P⌉ ✶ H) := by
  intro hh hj
  rcases (HProp.hstar_hpure_l P H hh).1 hj with ⟨hP, hH⟩
  exact h hP hh hH

theorem hasLoc_mono {p : Loc} {F G : HProp} (h : F ==> G) (hg : hasLoc p G) :
    hasLoc p F := fun hh hf => hg hh (h hh hf)

theorem pure_add {P : Prop} {H R : HProp} (hp : P) (h : H ==> R) :
    H ==> ⌈P⌉ ✶ R := by
  intro k hk
  exact (HProp.hstar_hpure_l P R k).2 ⟨hp, h k hk⟩

theorem pure_emp {P : Prop} (hp : P) : (HProp.hempty : HProp) ==> ⌈P⌉ :=
  fun k hk => HProp.hpure_intro_hempty hk hp

def safeFar (f : Loc) (F : HProp) : Prop := f = 0 ∨ hasLoc f F

theorem safeFar_nil {f : Loc} {F : HProp} (h : f = 0) : safeFar f F := Or.inl h

theorem safeFar_loc {f : Loc} {F : HProp} (h : hasLoc f F) : safeFar f F :=
  Or.inr h

theorem safeFar_step {a b : Loc} {F : HProp} (h1 : a ≠ b → hasLoc a F)
    (h2 : a = b → safeFar b F) : safeFar a F := by
  by_cases h : a = b
  · rcases h2 h with hb | hb
    · exact Or.inl (h ▸ hb)
    · exact Or.inr (h ▸ hb)
  · exact Or.inr (h1 h)

theorem safeFar_elim {f : Loc} {F : HProp} {M : Loc → Prop}
    (h : safeFar f F) (h0 : M 0) (h1 : hasLoc f F → M f) : M f := by
  rcases h with h | h
  · subst h
    exact h0
  · exact h1 h

def hexact (h0 : Heap) : HProp := fun h => h = h0

theorem hasLoc_exact {c : Loc} {h0 : Heap} (hc : c ∈ h0) : hasLoc c (hexact h0) := by
  intro k hk
  simp only [hexact] at hk
  exact hk ▸ hc

theorem frameOut {c : Loc} {S T : HProp}
    (A : ∀ G : HProp, hasLoc c G → S ✶ G ==> T ✶ G)
    {h hg : Heap} (hs : S h) (hd : Finmap.Disjoint h hg) (hc : c ∈ hg) : T h := by
  have hst : (S ✶ hexact hg) (h ∪ hg) :=
    HProp.hstar_intro hs (show (hexact hg) hg from rfl) hd
  obtain ⟨k1, k2, hT, hk2, hdk, heq⟩ :=
    HProp.hstar_elim (A (hexact hg) (hasLoc_exact hc) _ hst)
  simp only [hexact] at hk2
  subst hk2
  have : h = k1 := Finmap.union_cancel_right hd hdk heq
  exact this ▸ hT

theorem combine2 {c1 c2 : Loc} {S1 T1 S2 T2 : HProp}
    (A : ∀ G : HProp, hasLoc c1 G → S1 ✶ G ==> T1 ✶ G)
    (B : ∀ G : HProp, hasLoc c2 G → S2 ✶ G ==> T2 ✶ G)
    (w1 : hasLoc c1 S2) (w2 : hasLoc c2 S1) : S1 ✶ S2 ==> T1 ✶ T2 := by
  intro h hh
  obtain ⟨h1, h2, hs1, hs2, hd, he⟩ := HProp.hstar_elim hh
  refine he ▸ HProp.hstar_intro (frameOut A hs1 hd (w1 h2 hs2))
    (frameOut B hs2 (Finmap.Disjoint.symm _ _ hd) (w2 h1 hs1)) hd

theorem neLocs_star {p q : Loc} {H1 H2 : HProp}
    (h1 : hasLoc p H1) (h2 : hasLoc q H2) : neLocs p q (H1 ✶ H2) := by
  intro h hh
  obtain ⟨a, b, ha, hb, hd, _⟩ := HProp.hstar_elim hh
  intro hpq
  exact hd p (h1 a ha) (hpq ▸ h2 b hb)

theorem neLocs_star' {p q : Loc} {H1 H2 : HProp}
    (h1 : hasLoc q H1) (h2 : hasLoc p H2) : neLocs p q (H1 ✶ H2) := by
  intro h hh
  obtain ⟨a, b, ha, hb, hd, _⟩ := HProp.hstar_elim hh
  intro hpq
  exact hd q (h1 a ha) (hpq ▸ h2 b hb)

theorem neLocs_star_l {p q : Loc} {H1 H2 : HProp} (h : neLocs p q H1) :
    neLocs p q (H1 ✶ H2) := by
  intro h' hh
  obtain ⟨a, b, ha, _, _, _⟩ := HProp.hstar_elim hh
  exact h a ha

theorem neLocs_star_r {p q : Loc} {H1 H2 : HProp} (h : neLocs p q H2) :
    neLocs p q (H1 ✶ H2) := by
  intro h' hh
  obtain ⟨a, b, _, hb, _, _⟩ := HProp.hstar_elim hh
  exact h b hb

theorem neLocs_const {p q : Loc} {H : HProp} (h : p ≠ q) : neLocs p q H :=
  fun _ _ => h

theorem neLocs_mono {p q : Loc} {F G : HProp} (h : F ==> G) (hg : neLocs p q G) :
    neLocs p q F := fun hh hf => hg hh (h hh hf)

theorem neLocs_disj {p q : Loc} {H1 H2 : HProp} (h1 : neLocs p q H1)
    (h2 : neLocs p q H2) : neLocs p q (hdisj H1 H2) := by
  intro h hh
  rcases hh with hh | hh
  · exact h1 h hh
  · exact h2 h hh

theorem neLocs_pure_star {p q : Loc} {P : Prop} {H : HProp}
    (h : P → neLocs p q H) : neLocs p q (⌈P⌉ ✶ H) := by
  intro hh hj
  rcases (HProp.hstar_hpure_l P H hh).1 hj with ⟨hP, hH⟩
  exact h hP hh hH

theorem neLocs_hexists {A : Sort _} {p q : Loc} {J : A → HProp}
    (h : ∀ a, neLocs p q (J a)) : neLocs p q (HProp.hexists J) := by
  intro hh hj
  simp only [HProp.hexists] at hj
  obtain ⟨a, ha⟩ := hj
  exact h a hh ha

theorem himpl_of_neLocs {p q : Loc} {H R : HProp} (hn : neLocs p q H)
    (k : p ≠ q → H ==> R) : H ==> R := fun h hh => k (hn h hh) h hh

def tryAlt (k : MetaM Bool) : MetaM Bool := do
  let s ← saveState
  let r ← try k catch _ => pure false
  unless r do s.restore
  return r

def applyConstT (n : Name) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  replaceMainGoal (← g.apply (← mkConstWithFreshMVarLevels n))

def applyC (g : MVarId) (n : Name) : MetaM (List MVarId) := do
  let gs ← g.apply (← mkConstWithFreshMVarLevels n)
  gs.filterM fun m => do return !(← m.isAssigned)

def hFam (e : Expr) : Nat :=
  if e.isFVar then 4
  else if e.isAppOfArity ``hdisj 3 then 1
  else if e.isAppOfArity ``HProp.hstar 3 || e.isAppOfArity ``HProp.hexists 3
      || e.isAppOfArity ``HProp.hpure 2 || e.isAppOfArity ``HProp.hwand 3 then 2
  else if e.isAppOfArity ``HProp.hempty 1 || e.isAppOfArity ``HProp.hsingle 3 then 3
  else 0

partial def hasLocSolve (g : MVarId) : MetaM Bool := do
  let all := fun (gs : List MVarId) => gs.allM hasLocSolve
  let t ← instantiateMVars (← g.getType)
  let H := t.appArg!
  let conn := !H.hasMVar && [``HProp.hstar, ``HProp.hpure, ``HProp.hexists, ``HProp.hempty,
    ``hdisj].any (H.isAppOf ·)
  if !conn then
    if ← tryAlt (do return (← applyC g ``hasLoc_single).isEmpty) then return true
  if ← tryAlt (g.withContext (Sep.Xsimpl.cheapAssumptionCore g)) then return true
  let fam := hFam H
  let notEx := fam == 1 || fam == 3 || fam == 4
  if !(fam == 2 || fam == 3 || fam == 4) then
    if ← tryAlt (do all (← applyC g ``hasLoc_disj)) then return true
  let pureOk := !notEx && !(H.isAppOfArity ``HProp.hstar 3 &&
    (let f := hFam H.appFn!.appArg!; f == 1 || f == 3 || f == 4))
  if ← tryAlt (do
      unless pureOk do return false
      let gs ← applyC g ``hasLoc_pure_star
      let [g1] := gs | return false
      let (hp, g2) ← g1.intro `hxpe
      if ← tryAlt (do
          let g3 ← (try fastSubstVars g2 catch _ => pure g2)
          hasLocSolve g3) then return true
      g2.withContext do
        let np ← mkAppM ``Not #[← hp.getType]
        for d in ← getLCtx do
          if d.isImplementationDetail then continue
          if ← isDefEq d.type np then
            g2.assign (← mkAppOptM ``absurd #[none, ← g2.getType, mkFVar hp, d.toExpr])
            return true
        return false) then return true
  if !notEx then
    if ← tryAlt (do all (← applyC g ``hasLoc_star_l)) then return true
    if ← tryAlt (do all (← applyC g ``hasLoc_star_r)) then return true
  if ← tryAlt (do
      let r ← g.rewrite (← g.getType) (← mkConstWithFreshMVarLevels ``HProp.hstar_hexists)
      let g' ← g.replaceTargetEq r.eNew r.eqProof
      all (g' :: r.mvarIds)) then return true
  if ← tryAlt (do
      if notEx then return false
      let gs ← applyC g ``hasLoc_hexists
      gs.allM fun g1 => do
        let (_, g2) ← g1.intro1
        hasLocSolve g2) then return true
  return false

syntax "xsearch_hasloc" : tactic
elab_rules : tactic
  | `(tactic| xsearch_hasloc) => do
    let g ← getMainGoal
    unless ← hasLocSolve g do throwError "xsearch_hasloc: failed"
    replaceMainGoal []

syntax "xsearch_nelocs" : tactic
macro_rules
  | `(tactic| xsearch_nelocs) => `(tactic| (
      first
      | (refine Sep.Xsearch.neLocs_star ?_ ?_ <;> xsearch_hasloc)
      | (refine Sep.Xsearch.neLocs_star' ?_ ?_ <;> xsearch_hasloc)
      | (apply Sep.Xsearch.neLocs_star_l; xsearch_nelocs)
      | (apply Sep.Xsearch.neLocs_star_r; xsearch_nelocs)))

syntax "xsearch_srcne" : tactic
macro_rules
  | `(tactic| xsearch_srcne) => `(tactic| (
      first
      | exact Sep.Xsearch.neLocs_const (by assumption)
      | exact Sep.Xsearch.neLocs_const (Ne.symm (by assumption))
      | (refine Sep.Xsearch.neLocs_star ?_ ?_ <;> xsearch_hasloc)
      | (refine Sep.Xsearch.neLocs_star' ?_ ?_ <;> xsearch_hasloc)
      | (refine Sep.Xsearch.neLocs_disj ?_ ?_ <;> xsearch_srcne)
      | (apply Sep.Xsearch.neLocs_pure_star
         intro hxse
         first
         | ((try xsearch_subst) <;> xsearch_srcne)
         | exact absurd hxse (by assumption))
      | (rw [HProp.hstar_hexists] <;> xsearch_srcne)
      | (apply Sep.Xsearch.neLocs_hexists <;> intro _ <;> xsearch_srcne)
      | (apply Sep.Xsearch.neLocs_star_l; xsearch_srcne)
      | (apply Sep.Xsearch.neLocs_star_r; xsearch_srcne)))

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

def arithAtom? (e : Expr) : Option Expr :=
  match e with
  | .fvar _ => some e
  | .lit (.natVal n) => some (mkRawNatLit n)
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.appFn!.appArg! with
      | .lit (.natVal n) => some (mkRawNatLit n)
      | _ => none
    else none

def eqAtoms? (t : Expr) : Option (Bool × (Bool × Expr) × (Bool × Expr)) :=
  let t' := if t.isAppOfArity ``Not 1 then t.appArg! else t
  let neg := t.isAppOfArity ``Not 1
  if (t'.isAppOfArity ``Eq 3 || (!neg && t'.isAppOfArity ``Ne 3)) then
    let ty := t'.appFn!.appFn!.appArg!
    if !(ty.isConstOf ``Nat || ty.isConstOf ``Int) then none else
    let isInt := ty.isConstOf ``Int
    match arithAtom? t'.appFn!.appArg!, arithAtom? t'.appArg! with
    | some a, some b => some (t'.isAppOfArity ``Eq 3 && !neg, (isInt, a), (isInt, b))
    | _, _ => none
  else none

def omegaHeads : List Name :=
  [``Eq, ``Ne, ``Not, ``LT.lt, ``LE.le, ``GT.gt, ``GE.ge, ``Dvd.dvd, ``And, ``Or, ``Iff,
   ``False, ``True, ``Exists]

def omegaHopeless (g : MVarId) : MetaM Bool := g.withContext do
  let gt ← instantiateMVars (← g.getType)
  let some (gEq, ga, gb) := eqAtoms? gt | return false
  let mut parent : Std.HashMap (Bool × Expr) (Bool × Expr) := {}
  let mut diseqs : Array ((Bool × Expr) × (Bool × Expr)) := #[]
  let find := fun (m : Std.HashMap (Bool × Expr) (Bool × Expr))
      (x : Bool × Expr) => Id.run do
    let mut y := x
    for _ in [0 : 10000] do
      match m[y]? with
      | some z => if z == y then break else y := z
      | none => break
    return y
  let mut eqs : Array ((Bool × Expr) × (Bool × Expr)) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    match eqAtoms? t with
    | some (true, a, b) => eqs := eqs.push (a, b)
    | some (false, a, b) => diseqs := diseqs.push (a, b)
    | none =>
      match t.getAppFn with
      | .const n _ =>
        if omegaHeads.contains n then
          if t.isAppOfArity ``Eq 3 || t.isAppOfArity ``Ne 3 then
            let ty := t.appFn!.appFn!.appArg!
            if ty.isConstOf ``Nat || ty.isConstOf ``Int then return false
            if (← instantiateMVars ty).isConstOf ``Nat then return false
          else return false
      | .forallE .. => if ← isProp t then return false
      | .mvar _ => return false
      | _ => pure ()
  for (a, b) in eqs do
    let ra := find parent a
    let rb := find parent b
    if ra != rb then parent := parent.insert ra rb
  let lit := fun (m : Std.HashMap (Bool × Expr) (Bool × Expr))
      (r : Bool × Expr) (all : Array (Bool × Expr)) =>
    all.filterMap (fun x => match x.2 with
      | .lit (.natVal n) => if find m x == r then some n else none
      | _ => none)
  let mut atoms : Array (Bool × Expr) := #[ga, gb]
  for (a, b) in eqs ++ diseqs do atoms := atoms.push a |>.push b
  for x in atoms do
    let ls := lit parent (find parent x) atoms
    if ls.any (· != ls[0]!) then return false
  for (a, b) in diseqs do
    if find parent a == find parent b then return false
  let ra := find parent ga
  let rb := find parent gb
  if gEq then return ra != rb
  if ra == rb then return true
  let la := lit parent ra atoms
  let lb := lit parent rb atoms
  if !la.isEmpty && !lb.isEmpty && la[0]! != lb[0]! then return false
  for (a, b) in diseqs do
    let x := find parent a
    let y := find parent b
    if (x == ra && y == rb) || (x == rb && y == ra) then return false
  return true

elab "xsearch_omega" : tactic => do
  if ← omegaHopeless (← getMainGoal) then throwError "xsearch_omega: not entailed"
  evalTactic (← `(tactic| omega))

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

partial def hasLocPf? (inst p e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``HProp.hsingle, args) =>
      if args.size == 3 && args[1]! == p then
        some (mkAppN (mkConst ``hasLoc_single) #[inst, p, args[2]!])
      else none
  | (``HProp.hstar, #[_, a, b]) =>
      match hasLocPf? inst p a with
      | some h => some (mkAppN (mkConst ``hasLoc_star_l) #[inst, p, a, b, h])
      | none =>
        match hasLocPf? inst p b with
        | some h => some (mkAppN (mkConst ``hasLoc_star_r) #[inst, p, a, b, h])
        | none => none
  | _ => none

partial def nePf? (inst p q e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) =>
      match hasLocPf? inst p a, hasLocPf? inst q b with
      | some h1, some h2 =>
          some (mkAppN (mkConst ``neLocs_star) #[inst, p, q, a, b, h1, h2])
      | _, _ =>
        match hasLocPf? inst q a, hasLocPf? inst p b with
        | some h1, some h2 =>
            some (mkAppN (mkConst ``neLocs_star') #[inst, p, q, a, b, h1, h2])
        | _, _ =>
          match nePf? inst p q a with
          | some h =>
              some (mkAppN (mkConst ``neLocs_star_l) #[inst, p, q, a, b, h])
          | none =>
            match nePf? inst p q b with
            | some h =>
                some (mkAppN (mkConst ``neLocs_star_r) #[inst, p, q, a, b, h])
            | none => none
  | _ => none

def fastNeLocs (g : MVarId) : MetaM Bool := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let args := t.getAppArgs
  unless t.getAppFn.constName? == some ``neLocs && args.size == 4 do
    return false
  match nePf? args[0]! args[1]! args[2]! args[3]! with
  | none => return false
  | some pf =>
      if pf.hasExprMVar then return false
      unless ← isDefEq (← inferType pf) t do return false
      g.assign pf
      return true

def addNeFast (p q : Expr) (nm : Name) : TacticM Bool := withMainContext do
  if p == q then return false
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  match t.getAppFnArgs with
  | (``HProp.himpl, #[inst, lhs, rhs]) =>
    if t.hasExprMVar then return false
    let some npf := nePf? inst p q lhs | return false
    let ne ← mkAppM ``Ne #[p, q]
    let mv ← mkFreshExprSyntheticOpaqueMVar (← mkArrow ne t)
    goal.assign (mkAppN (mkConst ``himpl_of_neLocs)
      #[inst, p, q, lhs, rhs, npf, mv])
    let (_, g2) ← mv.mvarId!.intro nm
    replaceMainGoal [g2]
    return true
  | _ => return false

def factsCore : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  match t.getAppFnArgs with
  | (``HProp.himpl, #[inst, lhs, rhs]) =>
    if t.hasExprMVar then return ()
    let locs := ptoLocsOf lhs #[]
    if locs.size > 32 then return ()
    let mut facts : Array (Name × Expr × Expr × Expr × Expr) := #[]
    for i in [0 : locs.size] do
      for j in [i+1 : locs.size] do
        if ← pastGlobal then break
        let p := locs[i]!
        let q := locs[j]!
        if p == q then continue
        match nePf? inst p q lhs with
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
    (key : κ) (ms : Nat) (clamp : Bool) (k : TacticM Expr) (nm : String := "lem") : TacticM (Option Expr) := do
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

def lfpG {α : Type} (F : (α → HProp) → α → HProp) : α → HProp :=
  fun a h => ∀ X : α → HProp, (∀ b, F X b ==> X b) → X a h

theorem lfpG_induct {α : Type} (F : (α → HProp) → α → HProp) (X : α → HProp)
    (hX : ∀ b, F X b ==> X b) (a : α) : lfpG F a ==> X a := fun _ hh => hh X hX

def hguard (P : Prop) (H : HProp) : HProp := fun h => P → H h

theorem hguard_intro {P : Prop} {H R : HProp} (k : P → H ==> R) :
    H ==> hguard P R := fun h hh hp => k hp h hh

theorem hguard_rfl {α : Sort _} (a : α) (H : HProp) : hguard (a = a) H = H := by
  funext h
  exact propext ⟨fun k => k rfl, fun k _ => k⟩

theorem hguard_true (H : HProp) : hguard True H = H := by
  funext h
  exact propext ⟨fun k => k trivial, fun k _ => k⟩

theorem himpl_hguard_rfl {α : Sort _} {a : α} {H R : HProp}
    (h : H ==> hguard (a = a) R) : H ==> R := fun hh hx => h hh hx rfl

theorem wand_consume {P Q1 Q2 : HProp} (h : P ==> Q1 -✶ Q2) : P ✶ Q1 ==> Q2 := by
  rw [HProp.hstar_comm]
  exact HProp.himpl_hwand_r_elim h

theorem frame_l_of (H3 : HProp) {H1 H2 : HProp} (h : H1 ==> H2) :
    H1 ✶ H3 ==> H2 ✶ H3 := HProp.himpl_frame_l h

theorem frame_r_of (H1 : HProp) {H2 H3 : HProp} (h : H2 ==> H3) :
    H1 ✶ H2 ==> H1 ✶ H3 := HProp.himpl_frame_r h

theorem seg_consume {A B C D R : HProp} (hc : A ✶ B ==> C) (h : D ==> B ✶ R) :
    A ✶ D ==> C ✶ R := by
  refine HProp.himpl_trans (HProp.himpl_frame_r h) ?_
  rw [← HProp.hstar_assoc]
  exact HProp.himpl_frame_l hc

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

def predOrient (entries : Array UnfoldEntry) (q : Name) : MetaM (Bool × Bool) := do
  let heads := entries.map (·.headFn)
  let mut lft := false
  let mut rgt := false
  for e in entries do
    if e.headFn == q then
      let ty := (← getConstInfo e.lemmaName).type
      let r ← forallTelescopeReducing ty fun args concl => do
        if args.size != 2 then return (false, false)
        match concl.eq? with
        | some (_, _, body) =>
          let occs := collectOccs heads body #[]
          let mut l := false
          let mut r := false
          for o in occs do
            if o.getAppNumArgs == 2 then
              let oa := o.getAppArgs
              if oa[1]! == args[1]! then l := true
              if oa[0]! == args[0]! then r := true
          return (l, r)
        | none => return (false, false)
      lft := lft || r.1
      rgt := rgt || r.2
  return (lft, rgt)

initialize indCache :
    IO.Ref (Array (Name × Name × Nat × Array Nat × Array (Nat × Expr) × Name ×
      Array (Nat × Expr) × Option Expr)) ←
  IO.mkRef #[]

initialize indSpent : IO.Ref Nat ← IO.mkRef 0

initialize composeChanged : IO.Ref Bool ← IO.mkRef false

initialize composeTries : IO.Ref Nat ← IO.mkRef 0

initialize witnessMissed : IO.Ref Bool ← IO.mkRef false

initialize composeDepth : IO.Ref Nat ← IO.mkRef 0

initialize composeAltSpent : IO.Ref Nat ← IO.mkRef 0

initialize subTopFuel : IO.Ref Nat ← IO.mkRef 0

initialize forcedDepth : IO.Ref Nat ← IO.mkRef 0

def starOf (inst : Expr) : List Expr → Expr
  | [] => mkApp (mkConst ``HProp.hempty) inst
  | [a] => a
  | a :: rest => mkApp3 (mkConst ``HProp.hstar) inst a (starOf inst rest)

def mkStarOf (inst : Expr) (l : List Expr) : MetaM Expr := pure (starOf inst l)

def provePermCore (src tgt : Expr) : TacticM (Option Expr) := do
  if ← pastGlobal then return none
  let ty ← mkAppM ``HProp.himpl #[src, tgt]
  let mv ← mkFreshExprSyntheticOpaqueMVar ty
  let saved ← getGoals
  let st ← saveState
  try
    setGoals [mv.mvarId!]
    evalTactic (← `(tactic| (xsimpl_core
                             all_goals (try xsimpl_clean)
                             all_goals (try xsearch_subst)
                             all_goals (try xsimpl_core)
                             all_goals (try xsimpl_clean)
                             all_goals (try (first | rfl | assumption | trivial
                                                   | (apply Ne.symm; assumption)
                                                   | xsearch_omega)))))
    unless (← getUnsolvedGoals).isEmpty do throwError "perm: open"
    setGoals saved
    let r ← instantiateMVars mv
    if r.hasMVar then return none
    return some r
  catch _ =>
    st.restore
    setGoals saved
    return none

theorem perm_comm (A B : HProp) : A ✶ B ==> B ✶ A := by
  rw [HProp.hstar_comm]
  exact HProp.himpl_refl _

theorem perm_swap (A B C : HProp) : A ✶ (B ✶ C) ==> B ✶ (A ✶ C) := by
  rw [← HProp.hstar_assoc, HProp.hstar_comm A B, HProp.hstar_assoc]
  exact HProp.himpl_refl _

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

def provePermFast (src tgt : Expr) : MetaM (Option Expr) := do
  unless src.getAppFn.constName? == some ``HProp.hstar
      && src.getAppNumArgs == 3 do return none
  let inst := src.getAppArgs[0]!
  let S := Sep.Xsimpl.parseHstar src
  let T := Sep.Xsimpl.parseHstar tgt
  if S.length != T.length || S.length > 48 then return none
  unless (← mkStarOf inst S) == src do return none
  unless (← mkStarOf inst T) == tgt do return none
  let some pf := permListPfS inst S src T tgt | return none
  if pf.hasExprMVar then return none
  let ty ← mkAppM ``HProp.himpl #[src, tgt]
  unless ← isDefEq (← inferType pf) ty do return none
  return some pf

theorem himpl_of_eq {A B : HProp} (h : A = B) : A ==> B := h ▸ HProp.himpl_refl A

partial def flatEq (e : Expr) : MetaM (List Expr × Expr) := do
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

def provePermFlat (src tgt : Expr) : MetaM (Option Expr) := do
  let inst? := if src.isAppOfArity ``HProp.hstar 3 then src.getAppArgs[0]?
    else if tgt.isAppOfArity ``HProp.hstar 3 then tgt.getAppArgs[0]? else none
  let some inst := inst? | return none
  let (S, ps) ← flatEq src
  let (T, pt) ← flatEq tgt
  if S.length != T.length || S.length > 48 || S.isEmpty then return none
  let hty := mkApp (mkConst ``HProp) inst
  let sS := starOf inst S
  let sT := starOf inst T
  let some pm := permListPfS inst S sS T sT | return none
  let tr := fun (x y z p q : Expr) => mkAppN (mkConst ``HProp.himpl_trans) #[inst, x, y, z, p, q]
  let oe := fun (x y h : Expr) => mkAppN (mkConst ``himpl_of_eq) #[inst, x, y, h]
  let back := oe sT tgt (mkAppN (mkConst ``Eq.symm [1]) #[hty, tgt, sT, pt])
  let pf := tr src sS tgt (oe src sS ps) (tr sS sT tgt pm back)
  if pf.hasExprMVar then return none
  let ty ← mkAppM ``HProp.himpl #[src, tgt]
  unless ← isDefEq (← inferType pf) ty do return none
  return some pf

initialize permCache : IO.Ref (Array (Expr × Expr × Option Expr)) ← IO.mkRef #[]

def provePerm (src tgt : Expr) : TacticM (Option Expr) := do
  match (← permCache.get).findSome? (fun e =>
      if e.1 == src && e.2.1 == tgt then some e.2.2 else none) with
  | some (some pf) =>
      let lctx ← getLCtx
      let bad := pf.find? (fun e =>
        match e with
        | .fvar f => (lctx.find? f).isNone
        | _ => false)
      if bad.isNone then return some pf else return none
  | some none => return none
  | none =>
    let fast ← (try provePermFast src tgt catch _ => pure none)
    let fast ← match fast with
      | some pf => pure (some pf)
      | none => (try provePermFlat src tgt catch _ => pure none)
    let r ← match fast with
      | some pf => pure (some pf)
      | none => (provePermCore src tgt)
    if (← permCache.get).size < 256 then
      permCache.modify (·.push (src, tgt, r))
    return r

theorem wand_use {A B D C : HProp} (h1 : D ==> A) (h2 : B ==> C) :
    (A -✶ B) ✶ D ==> C := by
  rw [HProp.hstar_comm]
  exact HProp.himpl_trans (HProp.himpl_frame_l h1)
    (HProp.himpl_trans (HProp.hwand_cancel A B) h2)

theorem wand_use2 {A B E F C : HProp} (h1 : E ==> A) (h2 : B ✶ F ==> C) :
    (A -✶ B) ✶ (E ✶ F) ==> C := by
  refine HProp.himpl_trans (HProp.himpl_frame_r (HProp.himpl_frame_l h1)) ?_
  rw [← HProp.hstar_assoc, HProp.hstar_comm (A -✶ B) A]
  exact HProp.himpl_trans (HProp.himpl_frame_l (HProp.hwand_cancel A B)) h2

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

def segArgs? (heads : Array Name) (e : Expr) : Option (Name × Expr × Expr) :=
  match e.getAppFn.constName? with
  | some n =>
      if heads.contains n && e.getAppNumArgs == 2 then
        let args := e.getAppArgs
        some (n, args[0]!, args[1]!)
      else none
  | none => none

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

def indSetup (F X aty : Expr) (post : Nat := 0) : TacticM Expr := do
  let hXType ← withLocalDeclD `indb aty fun b => do
    mkForallFVars #[b] (← mkAppM ``HProp.himpl #[mkApp2 F X b, mkApp X b])
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

partial def mkXFun (tup templ aty : Expr) : MetaM Expr := do
  match aty.getAppFnArgs with
  | (``Sum, #[a, b]) =>
      mkAppM ``Sum.elim #[← mkXFun tup templ a, ← mkXFun tup templ b]
  | _ =>
      withLocalDeclD `xit aty fun t => do
        let pm ← projMap tup t
        mkLambdaFVars #[t] (templ.replaceFVars (pm.map (·.1)) (pm.map (·.2)))

partial def leafCount (aty : Expr) : Nat :=
  match aty.getAppFnArgs with
  | (``Sum, #[a, b]) => leafCount a + leafCount b
  | _ => 1

partial def mkXFunN (tup : Expr) (templs : Array Expr) (off : Nat) (aty : Expr) :
    MetaM Expr := do
  match aty.getAppFnArgs with
  | (``Sum, #[a, b]) =>
      mkAppM ``Sum.elim
        #[← mkXFunN tup templs off a,
          ← mkXFunN tup templs (off + leafCount a) b]
  | _ =>
      withLocalDeclD `xit aty fun t => do
        let pm ← projMap tup t
        let templ := templs[min off (templs.size - 1)]!
        mkLambdaFVars #[t] (templ.replaceFVars (pm.map (·.1)) (pm.map (·.2)))

partial def injIndex (e : Expr) : Nat :=
  match e.getAppFnArgs with
  | (``Sum.inr, args) => if args.size == 3 then 1 + injIndex args[2]! else 0
  | _ => 0

initialize groupCache : IO.Ref (Array (Name × Array Name)) ← IO.mkRef #[]

def groupMembers (p : Name) : MetaM (Array Name) := do
  match (← groupCache.get).findSome? (fun e =>
      if e.1 == p then some e.2 else none) with
  | some r => return r
  | none =>
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let mut heads : Array Name := #[]
  for e in entries do
    if !heads.contains e.headFn then heads := heads.push e.headFn
  let res ← try (do
      let pty := (← getConstInfo p).type
      forallTelescope pty fun xs _ => do
        if xs.isEmpty then return #[]
        let some (F, ta) ← functionalOf? (mkAppN (mkConst p) xs) | return #[]
        let k := leafCount (← inferType ta)
        if k == 0 || k > 8 then return #[]
        if k == 1 then return #[p]
        let mut ms : Array Name := Array.replicate k p
        let mut got : Array Bool := Array.replicate k false
        for n in heads do
          let nty := (← getConstInfo n).type
          let r2 ← forallTelescope nty fun ys _ => do
            if ys.isEmpty then return none
            match ← functionalOf? (mkAppN (mkConst n) ys) with
            | some (F2, ta2) => if F2 == F then return some (injIndex ta2)
                                else return none
            | none => return none
          match r2 with
          | some i =>
              if i < k && !got[i]! then
                ms := ms.set! i n
                got := got.set! i true
          | none => pure ()
        if got.any (fun b => !b) then return #[]
        return ms)
    catch _ => pure #[]
  groupCache.modify (·.push (p, res))
  return res

def stepSucc (members : Array Name) (m : Name) : MetaM Name := do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  for e in entries do
    if e.headFn != m then continue
    let ty := (← getConstInfo e.lemmaName).type
    let r ← forallTelescopeReducing ty fun _ concl => do
      match concl.eq? with
      | some (_, _, body) =>
          pure ((collectOccs members body #[]).findSome? (·.getAppFn.constName?))
      | none => pure none
    match r with
    | some n => return n
    | none => pure ()
  return m

def assignHeads (pm : Array Name) (p rn : Name) : MetaM (Array Name) := do
  let fallback := Array.replicate pm.size rn
  let rm ← groupMembers rn
  if rm.isEmpty then return fallback
  let some pi := pm.findIdx? (· == p) | return fallback
  let mut A : Array (Option Name) := Array.replicate pm.size none
  A := A.set! pi (some rn)
  for _ in [0 : pm.size] do
    for i in [0 : pm.size] do
      match A[i]! with
      | none => pure ()
      | some a =>
        let s ← stepSucc pm pm[i]!
        let sa ← stepSucc rm a
        match pm.findIdx? (· == s) with
        | some si => if (A[si]!).isNone then A := A.set! si (some sa)
        | none => pure ()
  if A.any (·.isNone) then return fallback
  return A.map (·.getD rn)

def hpack (H1 H2 : HProp) : HProp := H1 ✶ H2

theorem hpack_eq (H1 H2 : HProp) : hpack H1 H2 = H1 ✶ H2 := rfl

theorem base_frame (F : HProp) {A : HProp} (h : HProp.hempty ==> A) :
    F ==> A ✶ F := by
  have hb := frame_l_of F h
  rw [HProp.hstar_hempty_l] at hb
  exact hb

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

partial def hasLocPfH? (hy : Array (Expr × Expr × Expr)) (inst p e : Expr) : Option Expr :=
  match hy.find? (fun (l, H, _) => l == p && H == e) with
  | some (_, _, pf) => some pf
  | none =>
  match e.getAppFnArgs with
  | (``HProp.hsingle, args) =>
      if args.size == 3 && args[1]! == p then
        some (mkAppN (mkConst ``hasLoc_single) #[inst, p, args[2]!])
      else none
  | (``HProp.hstar, #[_, a, b]) =>
      match hasLocPfH? hy inst p a with
      | some h => some (mkAppN (mkConst ``hasLoc_star_l) #[inst, p, a, b, h])
      | none =>
        match hasLocPfH? hy inst p b with
        | some h => some (mkAppN (mkConst ``hasLoc_star_r) #[inst, p, a, b, h])
        | none => none
  | _ => none

partial def nePfH? (hy : Array (Expr × Expr × Expr)) (inst p q e : Expr) : Option Expr :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) =>
      match hasLocPfH? hy inst p a, hasLocPfH? hy inst q b with
      | some h1, some h2 =>
          some (mkAppN (mkConst ``neLocs_star) #[inst, p, q, a, b, h1, h2])
      | _, _ =>
        match hasLocPfH? hy inst q a, hasLocPfH? hy inst p b with
        | some h1, some h2 =>
            some (mkAppN (mkConst ``neLocs_star') #[inst, p, q, a, b, h1, h2])
        | _, _ =>
          match nePfH? hy inst p q a with
          | some h =>
              some (mkAppN (mkConst ``neLocs_star_l) #[inst, p, q, a, b, h])
          | none =>
            match nePfH? hy inst p q b with
            | some h =>
                some (mkAppN (mkConst ``neLocs_star_r) #[inst, p, q, a, b, h])
            | none => none
  | _ => none

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

elab "xsearch_hlchk" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  match t.getAppFnArgs with
  | (``hasLoc, #[_, p, H]) =>
      unless ← mayHasLoc (← ctxLocs g) p H do throwError "hasloc: impossible"
  | _ => pure ()

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
      let fast ← g1.withContext do
        let t ← instantiateMVars (← g1.getType)
        let args := t.getAppArgs
        unless t.getAppFn.constName? == some ``neLocs && args.size == 4 do
          return false
        match nePfH? hy args[0]! args[1]! args[2]! args[3]! with
        | none => return false
        | some pf =>
            if pf.hasExprMVar then return false
            unless ← isDefEq (← inferType pf) t do return false
            g1.assign pf
            return true
      unless fast do
        setGoals [g1]
        evalTactic (← `(tactic| xsearch_nelocs))
        unless (← getUnsolvedGoals).isEmpty do throwError "ne: open"
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

def holdsP (P : Prop) (H : HProp) : Prop := ∀ h, H h → P

theorem holdsP_pure (P : Prop) : holdsP P (⌈P⌉ : HProp) :=
  fun _ hh => (HProp.hpure_elim hh).1

theorem holdsP_star_l {P : Prop} {H1 H2 : HProp} (h : holdsP P H1) :
    holdsP P (H1 ✶ H2) := by
  intro h' hh
  obtain ⟨a, _, ha, _, _, _⟩ := HProp.hstar_elim hh
  exact h a ha

theorem holdsP_star_r {P : Prop} {H1 H2 : HProp} (h : holdsP P H2) :
    holdsP P (H1 ✶ H2) := by
  intro h' hh
  obtain ⟨_, b, _, hb, _, _⟩ := HProp.hstar_elim hh
  exact h b hb

theorem himpl_of_holds {P : Prop} {H R : HProp} (hn : holdsP P H)
    (k : P → H ==> R) : H ==> R := fun h hh => k (hn h hh) h hh

theorem holdsP_of {P : Prop} {H : HProp} (h : H ==> ⌈P⌉ ✶ H) : holdsP P H := by
  intro hh hx
  exact ((HProp.hstar_hpure_l P H hh).1 (h hh hx)).1

theorem holdsP_of_top {P : Prop} {H : HProp} (h : H ==> ⌈P⌉ ✶ HProp.htop) : holdsP P H :=
  fun hh hx => ((HProp.hstar_hpure_l P _ hh).1 (h hh hx)).1

theorem himpl_pure_top {P : Prop} {H : HProp} (hp : P) : H ==> ⌈P⌉ ✶ HProp.htop :=
  fun hh _ => (HProp.hstar_hpure_l P _ hh).2 ⟨hp, HProp.htop_intro hh⟩

theorem himpl_add_pure {P : Prop} {H : HProp} (hp : P) : H ==> ⌈P⌉ ✶ H :=
  fun hh hx => (HProp.hstar_hpure_l P H hh).2 ⟨hp, hx⟩

theorem pure_pre {P : Prop} {A K R : HProp} (hp : P) (h : A ✶ (⌈P⌉ ✶ K) ==> R) :
    A ✶ K ==> R := by
  refine HProp.himpl_trans ?_ h
  apply HProp.himpl_frame_r
  intro hh hk
  exact (HProp.hstar_hpure_l P K hh).2 ⟨hp, hk⟩

theorem snoc_frame (F : HProp) {P : Prop} {A B C : HProp} (hp : P)
    (h : A ✶ (⌈P⌉ ✶ B) ==> C) : A ✶ (B ✶ F) ==> C ✶ F := by
  rw [← HProp.hstar_assoc]
  apply HProp.himpl_frame_l
  refine HProp.himpl_trans ?_ h
  apply HProp.himpl_frame_r
  intro hh hk
  exact (HProp.hstar_hpure_l P B hh).2 ⟨hp, hk⟩

def hOrIn (P : Prop) (c : Loc) : HProp := fun h => P ∨ c ∈ h

theorem hOrIn_triv {P : Prop} {c : Loc} {H : HProp} (hp : P) : H ==> hOrIn P c :=
  fun _ _ => Or.inl hp

theorem hOrIn_of_loc {P : Prop} {c : Loc} {H : HProp} (h : hasLoc c H) :
    H ==> hOrIn P c := fun k hk => Or.inr (h k hk)

theorem hOrIn_star_r {P Q : Prop} {c : Loc} {K H : HProp}
    (h1 : H ==> hOrIn Q c) (h2 : Q → hasLoc c K) : K ✶ H ==> hOrIn P c := by
  intro k hk
  obtain ⟨a, b, ha, hb, hd, he⟩ := HProp.hstar_elim hk
  show P ∨ c ∈ k
  rw [he]
  rcases h1 b hb with hq | hq
  · exact Or.inr (Finmap.mem_union.2 (Or.inl (h2 hq a ha)))
  · exact Or.inr (Finmap.mem_union.2 (Or.inr hq))

theorem holdsP_mono {P : Prop} {F G : HProp} (h : F ==> G) (hg : holdsP P G) :
    holdsP P F := fun k hk => hg k (h k hk)

theorem holds_of_orIn {P : Prop} {c : Loc} {A B : HProp}
    (h1 : A ==> hOrIn P c) (h2 : hasLoc c B) : holdsP P (A ✶ B) := by
  intro k hk
  obtain ⟨a, b, ha, hb, hd, _⟩ := HProp.hstar_elim hk
  rcases h1 a ha with hp | hp
  · exact hp
  · exact absurd (h2 b hb) (hd c hp)

theorem neLocs_orIn {P : Prop} {a c : Loc} {A B : HProp}
    (h1 : A ==> hOrIn P c) (h2 : hasLoc a B) (h3 : P → a ≠ c) :
    neLocs a c (A ✶ B) := by
  intro k hk
  obtain ⟨x, y, hx, hy, hd, _⟩ := HProp.hstar_elim hk
  rcases h1 x hx with hp | hp
  · exact h3 hp
  · intro he
    exact hd c hp (he ▸ h2 y hy)

syntax "xsearch_pclose" : tactic
macro_rules
  | `(tactic| xsearch_pclose) => `(tactic| (
      first
      | rfl
      | assumption
      | (apply Eq.symm; assumption)
      | (apply Ne.symm; assumption)
      | (refine ⟨?_, ?_⟩ <;> xsearch_pclose)
      | xsearch_omega
      | trivial))

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

elab "xsearch_contra" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  match t.getAppFnArgs with
  | (``HProp.himpl, #[inst, lhs, rhs]) =>
    if t.hasExprMVar then return ()
    for q in pureProps lhs #[] do
      match q.getAppFnArgs with
      | (``Ne, #[_, a, b]) =>
        let some pfN := holdsPf? inst q lhs | continue
        let eqP ← mkAppM ``Eq #[a, b]
        let pf? ←
          if a == b then
            pure (some (← mkAppOptM ``contra_ne_self
              #[some inst, none, some a, some lhs, some rhs, some pfN]))
          else
            match holdsPf? inst eqP lhs with
            | none => pure none
            | some pfE => pure (some (← mkAppOptM ``contra_pure
                #[some inst, some eqP, some lhs, some rhs, some pfE,
                  some pfN]))
        match pf? with
        | none => pure ()
        | some pf =>
          if ← isDefEq (← inferType pf) t then
            g.assign pf
            replaceMainGoal []
            return ()
      | _ => pure ()
  | _ => pure ()

elab "xsearch_dsplit" : tactic => withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (lhs, rhs) := entailHead? t | return ()
  unless isDisj lhs do return ()
  unless (rhs.find? (fun e =>
      e.getAppFn.constName? == some ``HProp.hexists)).isSome do return ()
  evalTactic (← `(tactic| repeat (apply Sep.Xsearch.hdisj_elim)))

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
    let some (lhs, rhs) := entailHead? t | return ()
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

initialize compSpecCache :
    IO.Ref (Array ((Name × Array Expr × Array Expr) × Option Expr)) ←
  IO.mkRef #[]

structure SegLems where
  basePf   : Option Expr
  baseCell : Option Expr
  foldPf   : Expr
  foldNePf : Expr

initialize segLazyCache : IO.Ref (Array ((Name × Nat) × Option Expr)) ← IO.mkRef #[]

initialize segLemCache : IO.Ref (Array (Name × Option SegLems)) ←
  IO.mkRef #[]

initialize allocNeCache : IO.Ref (Array (Name × Option Expr)) ← IO.mkRef #[]

initialize srcNeCache : IO.Ref (Array (Name × Option Expr)) ← IO.mkRef #[]

initialize snocNilCache : IO.Ref (Array (Name × Option Expr)) ← IO.mkRef #[]

structure SegDesc where
  pname   : Name
  arity   : Nat
  nearIdx : Array Nat
  farIdx  : Array Nat
  fixIdx  : Array Nat
  usTypes : Array Expr
  nextU   : Nat
  cellLam : Expr
  payLams : Array Expr
  guards  : Array (Nat × Nat)
  headIdx : Nat
  baseCell : Bool
  deriving Inhabited

structure PStep where
  cellStep : Bool
  idxs : Array Nat
  nb   : Array Expr
  na   : Array Expr
  us   : Array Expr
  deriving Inhabited

initialize descCache : IO.Ref (Array (Name × Option SegDesc)) ← IO.mkRef #[]

partial def pureConjs (p : Expr) (acc : Array Expr) : Array Expr :=
  match p.getAppFnArgs with
  | (``And, #[a, b]) => pureConjs b (pureConjs a acc)
  | _ => acc.push p

def segArgsOf (d : SegDesc) (N FV C : Array Expr) : Array Expr := Id.run do
  let mut a : Array Expr := Array.replicate d.arity (mkConst ``Nat)
  for k in [0 : d.nearIdx.size] do
    if h : k < N.size then a := a.set! d.nearIdx[k]! N[k]
  for k in [0 : d.farIdx.size] do
    if h : k < FV.size then a := a.set! d.farIdx[k]! FV[k]
  for k in [0 : d.fixIdx.size] do
    if h : k < C.size then a := a.set! d.fixIdx[k]! C[k]
  return a

def pApp (d : SegDesc) (N FV C : Array Expr) : Expr :=
  mkAppN (mkConst d.pname) (segArgsOf d N FV C)

def segApp? (heads : Array Name) (e : Expr) : Option (Name × Array Expr) :=
  match e.getAppFn.constName? with
  | some n =>
      if heads.contains n && e.getAppNumArgs > 0 then some (n, e.getAppArgs)
      else none
  | none => none

def dropIdx (a : Array Nat) (i : Nat) : Array Nat :=
  (a.zipIdx.filterMap (fun (x, j) => if j == i then none else some x))

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

def canonIdx (n : Nat) (eqs : Array (Nat × Nat)) : Array Nat := Id.run do
  let mut c := Array.range n
  for _ in [0 : n] do
    for (i, j) in eqs do
      if i < n && j < n then
        let a := c[i]!
        let b := c[j]!
        if a != b then
          let m := min a b
          c := c.map (fun v => if v == a || v == b then m else v)
  return c

def mkSegDesc (p : Name) (dats : Array Nat := #[]) :
    MetaM (Option SegDesc) := do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  for ent in entries do
    if ent.headFn != p then continue
    let ty := (← getConstInfo ent.lemmaName).type
    let r ← forallTelescopeReducing ty fun xs concl => do
      let n := xs.size
      if n == 0 then return none
      let some (_, _, body) := concl.eq? | return none
      unless isHorConst body && body.getAppNumArgs ≥ 2 do return none
      let bargs := body.getAppArgs
      let baseB := bargs[bargs.size-2]!
      let stepB := bargs[bargs.size-1]!
      peelExG baseB #[] fun _bus bbody => do
      let mut eqs : Array (Nat × Nat) := #[]
      let baseItems := flatStar bbody #[]
      let baseCellE : Bool := baseItems.any (fun it =>
        it.getAppFn.constName? == some ``HProp.hsingle)
      for it in baseItems do
        match it.getAppFnArgs with
        | (``HProp.hpure, #[_, pr]) =>
          for c in pureConjs pr #[] do
            match c.getAppFnArgs with
            | (``Eq, #[_, a, b]) =>
              match xs.findIdx? (· == a), xs.findIdx? (· == b) with
              | some i, some j =>
                  if i != j && !eqs.any (fun e => e == (i, j) || e == (j, i)) then
                    eqs := eqs.push (i, j)
              | _, _ => pure ()
            | _ => pure ()
        | _ => pure ()
      if eqs.isEmpty && !baseCellE then return none
      peelExG stepB #[] fun us bd => do
        let items := if !dats.isEmpty then (flatStar bd #[]).toList else Sep.Xsimpl.parseHstar bd
        let mut recE : Option Expr := none
        for it in items do
          if it.getAppFn.constName? == some p then recE := some it
        let some rc := recE | return none
        let rargs := rc.getAppArgs
        if rargs.size != n then return none
        let some h := (Array.range n).find? (fun k =>
          !dats.contains k && (us.findIdx? (· == rargs[k]!)).isSome) | return none
        let some nextU := us.findIdx? (· == rargs[h]!) | return none
        let mut gAll : Array (Nat × Nat) := #[]
        let mut cellE : Option Expr := none
        let mut pays : Array Expr := #[]
        for it in items do
          if it.getAppFn.constName? == some p then continue
          match it.getAppFnArgs with
          | (``HProp.hpure, #[_, pr]) =>
            for c in pureConjs pr #[] do
              match c.getAppFnArgs with
              | (``Ne, #[_, a, b]) =>
                match xs.findIdx? (· == a), xs.findIdx? (· == b) with
                | some i, some j => gAll := gAll.push (i, j)
                | _, _ => pure ()
              | _ => pure ()
          | _ =>
            match cellGroup? it with
            | some (l, _) =>
                if cellE.isNone && l == xs[h]! then cellE := some it
                else pays := pays.push it
            | none => pays := pays.push it
        if !dats.isEmpty then
          let hs := items.filter (fun it => it.isAppOf ``HProp.hsingle
            && (it.getAppArgs[1]!.find? (· == xs[h]!)).isSome)
          if let some c0 := hs[0]? then
            let mut c := c0
            for it in hs.drop 1 do c ← mkAppM ``HProp.hstar #[c, it]
            cellE := some c
            pays := pays.filter (fun it => !hs.contains it)
        let some cell := cellE | return none
        let mut role : Array Nat := Array.replicate n 1
        role := role.set! h 0
        for k in [0 : n] do
          if k == h then continue
          if dats.contains k then
            role := role.set! k 2
            continue
          if rargs[k]! == xs[h]! then role := role.set! k 0
          else if rargs[k]! == xs[k]! then role := role.set! k 1
          else return none
        let mut nearIdx : Array Nat := #[]
        let mut farIdx : Array Nat := #[]
        if baseCellE then
          nearIdx := #[h]
          for k in [0 : n] do
            if k != h && role[k]! == 0 then nearIdx := nearIdx.push k
          let cvars := (canonIdx n eqs).map (fun i => xs[i]!)
          let mvs ← us.mapM fun u => do mkFreshExprMVar (some (← inferType u))
          let tmpl := (← mkLambdaFVars us cell).beta mvs
          let bItems := baseItems.map (fun e => e.replaceFVars xs cvars)
          let mut bUsed : Array Nat := #[]
          for t in flatStar (tmpl.replaceFVars xs cvars) #[] do
            if t.getAppFn.constName? == some ``HProp.hpure then continue
            let mut found := false
            for j in [0 : bItems.size] do
              if bUsed.contains j then continue
              let ok ← try checkpointDefEq (isDefEq t bItems[j]!)
                catch _ => pure false
              if ok then
                bUsed := bUsed.push j
                found := true
                break
            unless found do return none
          let uv ← instantiateMVars mvs[nextU]!
          if uv.hasExprMVar then return none
          let mut targets : Array Expr := #[uv]
          for _ in [1 : nearIdx.size] do targets := targets.push xs[h]!
          for t in targets do
            let tc := t.replaceFVars xs cvars
            match (Array.range n).find? (fun k =>
              role[k]! == 1 && !farIdx.contains k
                && (xs[k]!.replaceFVars xs cvars) == tc) with
            | some j => farIdx := farIdx.push j
            | none => return none
        else
          for (i, j) in eqs do
            if dats.contains i || dats.contains j then continue
            if i ≥ n || j ≥ n then return none
            if role[i]! == 0 && role[j]! == 1 then
              nearIdx := nearIdx.push i
              farIdx := farIdx.push j
            else if role[j]! == 0 && role[i]! == 1 then
              nearIdx := nearIdx.push j
              farIdx := farIdx.push i
            else return none
          let some h0 := nearIdx.findIdx? (· == h) | return none
          let far0 := farIdx[h0]!
          nearIdx := #[h] ++ dropIdx nearIdx h0
          farIdx := #[far0] ++ dropIdx farIdx h0
          for k in [0 : n] do
            if role[k]! == 0 && !nearIdx.contains k then return none
        let far0 := farIdx[0]?.getD n
        let mut fixIdx : Array Nat := #[]
        for k in [0 : n] do
          if role[k]! == 1 && !farIdx.contains k then fixIdx := fixIdx.push k
        let guards := gAll.filter (fun gd =>
          !(gd == (h, far0) || gd == (far0, h)))
        let usTypes ← us.mapM inferType
        let vars := xs ++ us
        return some {
          pname := p, arity := n, nearIdx := nearIdx, farIdx := farIdx,
          fixIdx := fixIdx, usTypes := usTypes, nextU := nextU,
          cellLam := ← mkLambdaFVars vars cell,
          payLams := ← pays.mapM (fun e => mkLambdaFVars vars e),
          guards := guards, headIdx := h, baseCell := baseCellE }
    match r with
    | some d => return some d
    | none => pure ()
  return none

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

initialize farImpCache : IO.Ref (Array ((Name × Nat) × Option Expr)) ←
  IO.mkRef #[]

initialize convCache :
    IO.Ref (Array (Name × Name × Array Nat × Expr × Array Expr ×
      Option Expr)) ← IO.mkRef #[]

def cellPureLam (d : SegDesc) : MetaM (Option Expr) := do
  lambdaTelescope d.cellLam fun vars body => do
    if h : d.headIdx < vars.size then
      let hv := vars[d.headIdx]
      let others := vars.filter (· != hv)
      let mut props : Array Expr := #[]
      for it in flatStar body #[] do
        match it.getAppFnArgs with
        | (``HProp.hpure, #[_, pr]) =>
            if (pr.find? (· == hv)).isSome
                && !others.any (fun o => (pr.find? (· == o)).isSome) then
              props := props.push pr
        | _ => pure ()
      if props.isEmpty then return none
      let mut conj := props[props.size-1]!
      for i in [0 : props.size-1] do
        conj ← mkAppM ``And #[props[props.size-2-i]!, conj]
      return some (← mkLambdaFVars #[hv] conj)
    else return none

def absOver (d : SegDesc) (a : Array Expr) (K : Expr) : MetaM (Option Expr) := do
  let pty := (← getConstInfo d.pname).type
  forallTelescope pty fun xs _ => do
    if xs.size != d.arity then return none
    if a.size != d.arity then return none
    let mut kfrom : Array Expr := #[]
    let mut kinto : Array Expr := #[]
    for m in d.farIdx ++ d.fixIdx do
      if m < d.arity && !kfrom.any (· == a[m]!) then
        kfrom := kfrom.push a[m]!
        kinto := kinto.push xs[m]!
    if kfrom.isEmpty then return none
    let K' := K.replace (fun t =>
      match kfrom.findIdx? (· == t) with
      | some ix => some kinto[ix]!
      | none => none)
    for m in d.nearIdx do
      if a[m]!.isFVar && (K'.find? (· == a[m]!)).isSome then return none
    if (K'.find? (fun t => xs.any (· == t))).isNone then return none
    return some (← mkLambdaFVars xs K')

structure SnocD where
  pname : Name
  nearI : Nat
  farI  : Nat
  usTys : Array Expr
  items : Array Expr
  deriving Inhabited

initialize snocDCache : IO.Ref (Array (Name × Option SnocD)) ← IO.mkRef #[]

initialize snocKCache : IO.Ref (Array (Name × Option Expr)) ← IO.mkRef #[]

initialize selfAllocCache : IO.Ref (Array ((Name × Nat) × Option Expr)) ←
  IO.mkRef #[]

def mkSnocD (p : Name) : MetaM (Option SnocD) := do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  for ent in entries do
    if ent.headFn != p then continue
    let ty := (← getConstInfo ent.lemmaName).type
    let r ← forallTelescopeReducing ty fun xs concl => do
      if xs.size != 2 then return none
      let some (_, _, body) := concl.eq? | return none
      unless isHorConst body && body.getAppNumArgs ≥ 2 do return none
      let bargs := body.getAppArgs
      let baseB := bargs[bargs.size-2]!
      let stepB := bargs[bargs.size-1]!
      unless (flatStar baseB #[]).any (fun it =>
          it.getAppFn.constName? == some ``HProp.hsingle) do return none
      peelExG stepB #[] fun us bd => do
        if us.size < 2 then return none
        let items0 := (Sep.Xsimpl.parseHstar bd).toArray
        let mut recE : Option Expr := none
        let mut rest : Array Expr := #[]
        for it in items0 do
          if it.getAppFn.constName? == some p && recE.isNone then recE := some it
          else rest := rest.push it
        let some rc := recE | return none
        let rargs := rc.getAppArgs
        if rargs.size != 2 then return none
        let some near := (Array.range 2).find? (fun k =>
          (us.findIdx? (· == rargs[k]!)).isSome) | return none
        let far := 1 - near
        unless rargs[far]! == xs[far]! do return none
        let some kk := us.findIdx? (· == rargs[near]!) | return none
        if rest.size < 2 then return none
        for it in rest do
          if (it.find? (· == xs[far]!)).isSome then return none
        let zv := us[kk]!
        let us' := us.zipIdx.filterMap (fun (u, j) =>
          if j == kk then none else some u)
        let usTys ← us'.mapM inferType
        let vars := #[xs[near]!, zv] ++ us'
        let its ← rest.mapM (fun e => mkLambdaFVars vars e)
        let sd : SnocD :=
          { pname := p, nearI := near, farI := far
            usTys := usTys, items := its }
        return some sd
    match r with
    | some d => return some d
    | none => pure ()
  return none

def snocDOf (p : Name) : MetaM (Option SnocD) := do
  match (← snocDCache.get).findSome? (fun e =>
      if e.1 == p then some e.2 else none) with
  | some r => return r
  | none =>
    let r ← try mkSnocD p catch _ => pure none
    snocDCache.modify (·.push (p, r))
    return r

def descOf (p : Name) : MetaM (Option SegDesc) := do
  match (← descCache.get).findSome? (fun e => if e.1 == p then some e.2 else none) with
  | some r => return r
  | none =>
    let r ← try mkSegDesc p catch _ => pure none
    descCache.modify (·.push (p, r))
    return r

def matchCell (d : SegDesc) (xsArgs : Array Expr) (L : Array Expr)
    (used : Array Nat) (i : Nat) : MetaM (Option (Array Nat × Array Expr)) := do
  let mvs ← d.usTypes.mapM fun t => mkFreshExprMVar (some t)
  let inst := d.cellLam.beta (xsArgs ++ mvs)
  let whole ← try checkpointDefEq (isDefEq inst L[i]!) catch _ => pure false
  let mut idxs : Array Nat := #[i]
  if !whole then
    idxs := #[]
    for t in Sep.Xsimpl.parseHstar inst do
      if t.getAppFn.constName? == some ``HProp.hpure then continue
      let mut found := false
      for j in [0 : L.size] do
        if used.contains j || idxs.contains j then continue
        let ok ← try checkpointDefEq (isDefEq t L[j]!) catch _ => pure false
        if ok then
          idxs := idxs.push j
          found := true
          break
      unless found do return none
    unless idxs.contains i do return none
  let vs ← mvs.mapM instantiateMVars
  if vs.any (·.hasExprMVar) then return none
  return some (idxs, vs)

def findCellStep (d : SegDesc) (L : Array Expr) (used : Array Nat)
    (xsArgs : Array Expr) : MetaM (Option (Array Nat × Array Expr)) := do
  let mut res : Option (Array Nat × Array Expr) := none
  for i in [0 : L.size] do
    if used.contains i then continue
    match cellGroup? L[i]! with
    | some (l, _) =>
      if l != xsArgs[d.headIdx]! then continue
      match ← matchCell d xsArgs L used i with
      | some r => if res.isSome then return none else res := some r
      | none => pure ()
    | none => pure ()
  return res

def findSegStep (d : SegDesc) (L : Array Expr) (used : Array Nat)
    (xsArgs : Array Expr) : Option (Nat × Array Expr) := Id.run do
  let mut res : Option (Nat × Array Expr) := none
  for i in [0 : L.size] do
    if used.contains i then continue
    let e := L[i]!
    if e.getAppFn.constName? != some d.pname then continue
    let b := e.getAppArgs
    if b.size != d.arity then continue
    if !(d.nearIdx.all (fun k => b[k]! == xsArgs[k]!)) then continue
    if !(d.fixIdx.all (fun k => b[k]! == xsArgs[k]!)) then continue
    if b[d.farIdx[0]!]! == xsArgs[d.headIdx]! then continue
    if res.isSome then return none else res := some (i, d.farIdx.map (fun k => b[k]!))
  return res

def planChain (d : SegDesc) (L : Array Expr) (FV C N0 : Array Expr) :
    MetaM (Option (Array PStep × Array Expr × Array Nat)) := do
  let mut used : Array Nat := #[]
  let mut steps : Array PStep := #[]
  let mut missing : Array Expr := #[]
  let mut N := N0
  for _ in [0 : 32] do
    if (Array.range d.nearIdx.size).all (fun k => N[k]! == FV[k]!) then
      return some (steps, missing, used)
    let xsArgs := segArgsOf d N FV C
    let cs ← findCellStep d L used xsArgs
    let ss := findSegStep d L used xsArgs
    if cs.isSome && ss.isSome then return none
    match cs with
    | some (cidxs, usv) =>
        used := used ++ cidxs
        let mut idxs : Array Nat := cidxs
        let full := xsArgs ++ usv
        for pl in d.payLams do
          let plv ← instantiateMVars (pl.beta full)
          match (Array.range L.size).find? (fun j => !used.contains j && L[j]! == plv) with
          | some j =>
              idxs := idxs.push j
              used := used.push j
          | none =>
              if !missing.any (· == plv) then missing := missing.push plv
        let mut Nn : Array Expr := #[usv[d.nextU]!]
        for _ in [1 : d.nearIdx.size] do Nn := Nn.push N[0]!
        steps := steps.push { cellStep := true, idxs := idxs, nb := N,
                              na := Nn, us := usv }
        N := Nn
    | none =>
      match ss with
      | some (i, M) =>
          used := used.push i
          steps := steps.push { cellStep := false, idxs := #[i], nb := N,
                                na := M, us := #[] }
          N := M
      | none => return none
  return none

def regroupAtoms (inst : Expr) (items : Array Expr) : MetaM (Array Expr) := do
  let isP := fun (e : Expr) => e.getAppFn.constName? == some ``HProp.hpure
  let isC := fun (e : Expr) => e.getAppFn.constName? == some ``HProp.hsingle
  let mut out : Array Expr := #[]
  let mut i := 0
  while i < items.size do
    if isP items[i]! && i + 1 < items.size && isC items[i+1]! then
      let mut j := i + 1
      while j < items.size && isC items[j]! do
        j := j + 1
      let grp := ((List.range (j - i)).map (fun k => items[i+k]!))
      out := out.push (← mkStarOf inst grp)
      i := j
    else
      out := out.push items[i]!
      i := i + 1
  return out

def projOf (t : Expr) (i n : Nat) : MetaM Expr := do
  if n ≤ 1 then return t
  let mut acc := t
  for _ in [0 : i] do acc ← mkAppM ``Prod.snd #[acc]
  if i + 1 == n then return acc else mkAppM ``Prod.fst #[acc]

def tupleOf (xs : Array Expr) : MetaM Expr := do
  if xs.size == 0 then return mkConst ``Unit.unit
  let mut acc := xs[xs.size-1]!
  for i in [0 : xs.size-1] do
    acc ← mkAppM ``Prod.mk #[xs[xs.size-2-i]!, acc]
  return acc

def withLocs {α : Type} [Inhabited α] (n : Nat) (nm : String) (ty : Expr)
    (k : Array Expr → TacticM α) : TacticM α :=
  withLocalDeclsD ((Array.range n).map fun i =>
    (Name.mkSimple (nm ++ toString i), fun _ => pure ty)) k

def withTys {α : Type} [Inhabited α] (tys : Array Expr) (nm : String)
    (k : Array Expr → TacticM α) : TacticM α :=
  withLocalDeclsD (tys.mapIdx fun i t =>
    (Name.mkSimple (nm ++ toString i), fun _ => pure t)) k

def knownNe (g : MVarId) (a b : Expr) : MetaM (Option Expr) := g.withContext do
  let t1 ← mkAppM ``Ne #[a, b]
  let t2 ← mkAppM ``Ne #[b, a]
  for dcl in ← getLCtx do
    if dcl.isImplementationDetail then continue
    let ty ← instantiateMVars dcl.type
    if ty == t1 then return some dcl.toExpr
    if ty == t2 then return some (← mkAppM ``Ne.symm #[dcl.toExpr])
  return none

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

partial def cmProp (env : Std.HashMap FVarId Int) (p : Expr) : Option Bool :=
  match p.getAppFnArgs with
  | (``Eq, #[_, a, b]) =>
      match cmVal env a, cmVal env b with
      | some x, some y => some (x == y)
      | _, _ => none
  | (``Ne, #[_, a, b]) =>
      match cmVal env a, cmVal env b with
      | some x, some y => some (x != y)
      | _, _ => none
  | (``Not, #[a]) => (cmProp env a).map (!·)
  | (``And, #[a, b]) =>
      match cmProp env a, cmProp env b with
      | some false, _ => some false
      | _, some false => some false
      | some true, some true => some true
      | _, _ => none
  | (``Or, #[a, b]) =>
      match cmProp env a, cmProp env b with
      | some true, _ => some true
      | _, some true => some true
      | some false, some false => some false
      | _, _ => none
  | (``True, #[]) => some true
  | (``False, #[]) => some false
  | _ =>
    match p with
    | .forallE _ a b _ =>
        if b.hasLooseBVars then none else
        match cmProp env a, cmProp env b with
        | some false, _ => some true
        | _, some true => some true
        | some true, some false => some false
        | _, _ => none
    | .mdata _ b => cmProp env b
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

partial def cmDisjs (e : Expr) : Array Expr :=
  if isHorConst e && e.getAppNumArgs ≥ 2 then
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
    if isHorConst e && e.getAppNumArgs ≥ 2 then
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
      let base := ds.filter (fun d => !cmHasPred tbl d)
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

def cmSolve (cls : CmCls) (st : CmSt) : Option (Std.HashMap FVarId Int × CmHeap) := Id.run do
  let mut env : Std.HashMap FVarId Int := {}
  let mut k := 0
  for c in cls do
    let lits := c.filterMap (fun a => match a with | .inr n => some n | .inl _ => none)
    let v ← match lits[0]? with
      | some n =>
          if lits.any (· != n) then return none
          pure n
      | none =>
          k := k + 1
          pure (Int.ofNat (100000 + 1000 * k))
    for a in c do
      match a with
      | .inl f => env := env.insert f v
      | .inr _ => pure ()
  for p in st.pures do
    unless cmProp env p == some true do return none
  let mut h : CmHeap := #[]
  for (a, v) in st.cells do
    match cmVal env a, cmVal env v with
    | some x, some y =>
        if h.any (·.1 == x) then return none
        h := h.push (x, y)
    | _, _ => return none
  return some (env, h.qsort (fun x y => x.1 < y.1))

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

structure CmPre where
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
  return some ⟨allV, ix, pures, cells, base⟩

def cmSameI (cls : CmClsI) (x y : Sum Nat Int) : Bool :=
  match cls.findIdx? (·.contains x) with
  | some i => cls[i]!.contains y
  | none => false

structure CmFb where
  clsOf : Std.HashMap Nat Nat := {}
  litOf : Array (Option Int) := #[]
  pairs : Std.HashSet (Nat × Nat) := {}
  lits : Std.HashSet (Nat × Int) := {}

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
  let mut byOff : Array (Int × Nat) := #[]
  for (a, _) in pre.cells do
    let r : Option (Nat × Int) := match a with
      | .var i => some (i, 0)
      | .add (.var i) (.lit k) => some (i, k)
      | _ => none
    match r with
    | some (i, k) =>
        match clsOf[i]? with
        | some ci =>
            for (k2, c2) in byOff do
              if k2 == k then pairs := pairs.insert (key ci c2)
            byOff := byOff.push (k, ci)
        | none => pure ()
    | none => pure ()
  return { clsOf, litOf, pairs, lits }

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
          fb.pairs.contains (key ci cj) || clash (fb.litOf[ci]?.join) (fb.litOf[cj]?.join)
      | _, _ => false
  | .inl i, .inr n | .inr n, .inl i =>
      match fb.clsOf[i]? with
      | some ci =>
          fb.lits.contains (ci, n) || clash (fb.litOf[ci]?.join) (some n) ||
            (match litCls n with
              | some cn => fb.pairs.contains (key ci cn)
              | none => false)
      | none => false
  | _, _ => false

def cmSolveM (pre : CmPre) (mi : Nat) (mj : Option Nat) (extra : Array (Sum Nat Int)) :
    Option (Array (Option Int) × CmHeap × Array Int) := Id.run do
  let mut env : Array (Option Int) := Array.replicate pre.allV.size none
  let mut k := 0
  let mut litVals : Array Int := #[]
  let nb := pre.base.size
  for ci in [0 : nb + 1] do
    if mj == some ci then continue
    if ci == nb && mi != nb then continue
    let c := if ci == nb then extra else if ci == mi then pre.base[ci]! ++ extra else pre.base[ci]!
    let mut lit : Option Int := none
    for a in c do
      match a with
      | .inr n => match lit with
        | none => lit := some n
        | some m => if m != n then return none
      | .inl _ => pure ()
    let v ← match lit with
      | some n => pure n
      | none =>
          k := k + 1
          pure (Int.ofNat (100000 + 1000 * k))
    let mut hasVar := false
    for a in c do
      match a with
      | .inl i =>
          env := env.set! i (some v)
          hasVar := true
      | .inr _ => pure ()
    if hasVar && lit.isSome then litVals := litVals.push v
  for p in pre.pures do
    unless p.eval env == some true do return none
  let mut h : CmHeap := #[]
  for (a, v) in pre.cells do
    match a.eval env, v.eval env with
    | some x, some y =>
        if h.any (·.1 == x) then return none
        h := h.push (x, y)
    | _, _ => return none
  let mut vals : Array Int := #[]
  for v in (litVals ++ (List.range k).toArray.map (fun i => Int.ofNat (100000 + 1000 * (i + 1)))).qsort (· < ·) do
    if vals.back? != some v then vals := vals.push v
  return some (env, h.qsort (fun x y => x.1 < y.1), vals)

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

structure CmRes where
  outs : Array CmHeap := #[]
  inc : Bool := false
  deriving Inhabited

def CmRes.join (a b : CmRes) : CmRes :=
  { outs := b.outs.foldl (fun acc o => if acc.contains o then acc else acc.push o) a.outs,
    inc := a.inc || b.inc }

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
  | ex (isNat : Bool) (pin : Option CmV) (body : CmN)
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
          .ex isNat ((cmPin x body).map (cmCV ix)) (cmCompile tbl ix' (next + 1) body)
      | _ => .unk
  | _ =>
    if isHorConst e && e.getAppNumArgs ≥ 2 then
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

def cmCandsI (ev : CmEv) (env : Array (Option Int)) (path : Array Int) (h : CmHeap)
    (isNat : Bool) (pin : Option CmV) : CmM (Array Int) := do
  let _ ← cmCount
  let mut cands : Array Int := #[]
  let mut pinned := false
  match pin.bind (·.eval env) with
  | some av =>
      pinned := true
      match h.find? (·.1 == av) with
      | some (_, v) => cands := #[v]
      | none => pure ()
  | none => pure ()
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

mutual

partial def cmConsI (ev : CmEv) (env : Array (Option Int)) (path : Array Int) (fuel : Nat)
    (e : CmN) (h : CmHeap) : CmM CmRes := do
  unless ← cmTick do return { inc := true }
  match e with
  | .star a b =>
      let r1 ← cmConsI ev env path fuel a h
      let mut acc : CmRes := { inc := r1.inc }
      for o in r1.outs do
        acc := acc.join (← cmConsI ev env path fuel b o)
      return acc
  | .emp => return { outs := #[h] }
  | .pure p =>
      match p.eval env with
      | some true => return { outs := #[h] }
      | some false => return {}
      | none => return { inc := true }
  | .cell a v =>
      match a.eval env, v.eval env with
      | some x, some y =>
          if h.contains (x, y) then return { outs := #[h.filter (·.1 != x)] }
          else return {}
      | _, _ => return { inc := true }
  | .ex isNat pin body =>
      let cands ← cmCandsI ev env path h isNat pin
      let mut acc : CmRes := {}
      for c in cands do
        acc := acc.join (← cmConsI ev (env.push (some c)) (path.push c) fuel body h)
      return acc
  | .or ds =>
      let mut acc : CmRes := {}
      for d in ds do
        acc := acc.join (← cmConsI ev env path fuel d h)
      return acc
  | .call k args =>
      if fuel == 0 then return { inc := true }
      cmConsI ev (args.map (·.eval env)) path (fuel - 1) ev.prog[k]! h
  | .unk => return { inc := true }

partial def cmConsKI (ev : CmEv) (env : Array (Option Int)) (path : Array Int) (fuel : Nat)
    (e : CmN) (h : CmHeap) : CmM (Bool × Bool) := do
  unless ← cmTick do return (false, true)
  match e with
  | .star a b =>
      let r1 ← cmConsI ev env path fuel a h
      let mut inc := r1.inc
      for o in r1.outs do
        let (f, i) ← cmConsKI ev env path fuel b o
        inc := inc || i
        if f then return (true, inc)
      return (false, inc)
  | .emp => return (h.isEmpty, false)
  | .pure p =>
      match p.eval env with
      | some true => return (h.isEmpty, false)
      | some false => return (false, false)
      | none => return (false, true)
  | .cell a v =>
      match a.eval env, v.eval env with
      | some x, some y =>
          if h.contains (x, y) then return ((h.filter (·.1 != x)).isEmpty, false)
          else return (false, false)
      | _, _ => return (false, true)
  | .ex isNat pin body =>
      let cands ← cmCandsI ev env path h isNat pin
      let mut inc := false
      for c in cands do
        let (f, i) ← cmConsKI ev (env.push (some c)) (path.push c) fuel body h
        inc := inc || i
        if f then return (true, inc)
      return (false, inc)
  | .or ds =>
      let mut inc := false
      for d in ds do
        let (f, i) ← cmConsKI ev env path fuel d h
        inc := inc || i
        if f then return (true, inc)
      return (false, inc)
  | .call k args =>
      if fuel == 0 then return (false, true)
      cmConsKI ev (args.map (·.eval env)) path (fuel - 1) ev.prog[k]! h
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

def cmAllocRefuted (occ loc : Expr) (esc : Option Expr) : MetaM Bool := do
  let hty ← whnfR (← inferType occ)
  unless hty.isAppOfArity ``HProp 1 do return false
  unless ← isDefEq (mkApp (mkConst ``Params.val) hty.appArg!) (mkConst ``Int) do
    return false
  let tbl ← cmTable
  let vars := cmFVars occ #[]
  for lv in [0 : 3] do
    match ← cmGen tbl lv 0 occ #[{}] with
    | none => pure ()
    | some sts =>
      for st in sts do
        match cmSolve (cmBase vars st) st with
        | none => pure ()
        | some (env, h) =>
          match cmVal env loc with
          | none => pure ()
          | some l =>
            if h.any (·.1 == l) then continue
            match esc with
            | none => return true
            | some p => if cmProp env p == some false then return true
  return false

partial def hasPureOrEx (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, a, b]) => hasPureOrEx a || hasPureOrEx b
  | (``HProp.hpure, _) => true
  | (``HProp.hexists, _) => true
  | _ => false

def closeBy (g : MVarId) (tac : TacticM Unit) : TacticM Bool := do
  let st ← saveState
  try
    setGoals [g]
    tac
    if (← getUnsolvedGoals).isEmpty then return true
    st.restore
    return false
  catch _ =>
    st.restore
    return false

partial def splitConjHyps (g : MVarId) : MetaM MVarId := g.withContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``And 2 then
      let rs ← g.cases d.fvarId
      if h : rs.size = 1 then return ← splitConjHyps rs[0].mvarId
      else return g
  return g

partial def orinRun (g : MVarId) (depth : Nat) : TacticM Bool := g.withContext do
  if depth > 16 then return false
  let t ← instantiateMVars (← g.getType)
  let some (lhs, rhs) := entailHead? t | return false
  unless rhs.isAppOfArity ``hOrIn 3 do return false
  if lhs.isAppOf ``hdisj then
    let gs ← g.apply (← mkConstWithFreshMVarLevels ``hdisj_elim)
    for g' in gs do
      unless ← orinRun g' (depth + 1) do return false
    return true
  if hasPureOrEx lhs then
    let st ← saveState
    setGoals [g]
    Sep.Xsimpl.xsimplDriver none
    let gs ← getUnsolvedGoals
    let mut ok := true
    for g' in gs do
      let g'' ← fastSubstVars (← splitConjHyps g')
      let t' ← instantiateMVars (← g''.getType)
      let some (l', _) := entailHead? t' | do ok := false; break
      if hasPureOrEx l' then
        ok := false
        break
      unless ← orinRun g'' (depth + 1) do
        ok := false
        break
    unless ok do st.restore
    return ok
  let c := rhs.appArg!
  if ← closeBy g (do
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``hOrIn_triv)
      setGoals gs
      evalTactic (← `(tactic| all_goals xsearch_pclose))) then return true
  if ← closeBy g (do
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``hOrIn_of_loc)
      setGoals gs
      evalTactic (← `(tactic| all_goals (xsearch_hlchk; xsearch_hasloc)))) then return true
  let L := Sep.Xsimpl.parseHstar lhs
  let inst := t.getAppArgs[0]!
  for i in [0 : L.length] do
    let a := L[i]!
    unless a.isAppOfArity ``hOrIn 3 && a.appArg! == c do continue
    let rest := (L.zipIdx.filter (fun (_, m) => m != i)).map (·.1)
    if rest.isEmpty then continue
    let K ← mkStarOf inst rest
    let tgt ← mkAppM ``HProp.hstar #[K, a]
    let some pm ← provePerm lhs tgt | continue
    if ← closeBy g (do
        let mv ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[tgt, rhs])
        g.assign (← mkAppM ``HProp.himpl_trans #[pm, mv])
        let gs ← mv.mvarId!.apply (← mkConstWithFreshMVarLevels ``hOrIn_star_r)
        let mut rem : List MVarId := []
        for g2 in gs do
          let ty ← instantiateMVars (← g2.getType)
          if ty.isAppOf ``HProp.himpl then
            let rf ← mkAppM ``HProp.himpl_refl #[a]
            unless ← isDefEq ty (← inferType rf) do throwError "orin: refl"
            g2.assign rf
        for g2 in gs do
          if ← g2.isAssigned then continue
          let ty ← instantiateMVars (← g2.getType)
          unless ty.isForall do throwError "orin: shape"
          let (_, g3) ← g2.intro `hxoq
          let g4 ← fastSubstVars (← splitConjHyps g3)
          rem := rem ++ [g4]
        setGoals rem
        evalTactic (← `(tactic| all_goals xsearch_hasloc))) then return true
  return false

initialize bkAllocCache : IO.Ref (Array ((Name × Nat) × Option Expr)) ←
  IO.mkRef #[]

def proveBkAlloc (d : SegDesc) (j : Nat) : TacticM (Option Expr) :=
  withLemCache (nm := "bkAlloc") bkAllocCache (d.pname, j) 900 true do
  let nr := d.nearIdx.size
  let nf := d.fixIdx.size
  if j == 0 || j ≥ nr then throwError "bk: index"
  let pty := (← getConstInfo d.pname).type
  unless pty.isForall do throwError "bk: arity"
  let A := pty.bindingDomain!
  let pf ←
    withLocs nr "bknv" A fun Nv =>
    withLocs nr "bkfv" A fun FVv =>
    withLocs nf "bkcv" A fun Cv => do
      let pnm := pApp d Nv FVv Cv
      let escP ← mkAppM ``And
        #[← mkAppM ``Eq #[Nv[0]!, FVv[0]!], ← mkAppM ``Eq #[Nv[j]!, FVv[j]!]]
      if ← cmAllocRefuted pnm FVv[j]! (some escP) then throwError "bk: refuted"
      let some (Ff, ta) ← functionalOf? pnm | throwError "bk: not lfp"
      let tup ← tupleOf (segArgsOf d Nv FVv Cv)
      unless ← isDefEq ta tup do throwError "bk: shape"
      let aty ← inferType tup
      let mkP : Array Expr → MetaM Expr := fun prj => do
        mkAppM ``And
          #[← mkAppM ``Eq #[prj[d.nearIdx[0]!]!, prj[d.farIdx[0]!]!],
            ← mkAppM ``Eq #[prj[d.nearIdx[j]!]!, prj[d.farIdx[j]!]!]]
      let X ← withLocalDeclD `bkt aty fun t => do
        let mut prj : Array Expr := #[]
        for i in [0 : d.arity] do prj := prj.push (← projOf t i d.arity)
        mkLambdaFVars #[t]
          (← mkAppM ``hOrIn #[← mkP prj, prj[d.farIdx[j]!]!])
      let hXMv ← indSetup Ff X aty
      evalTactic (← `(tactic| all_goals (try xsearch_distr)))
      for g in ← getGoals do
        unless ← orinRun g 0 do throwError "bk: open"
      setGoals []
      let key ← mkAppM ``lfpG_induct #[Ff, X, hXMv, tup]
      let stmt ← mkAppM ``HProp.himpl
        #[pnm, ← mkAppM ``hOrIn
            #[← mkP (segArgsOf d Nv FVv Cv), FVv[j]!]]
      unless ← isDefEq (← inferType key) stmt do throwError "bk: type"
      let key ← mkExpectedTypeHint key stmt
      let r ← instantiateMVars (← mkLambdaFVars ((Nv ++ FVv) ++ Cv) key)
      if r.hasMVar then throwError "bk: mvar"
      pure r
  pure pf

def provePropBy (ty : Expr) (tac : TacticM Unit) : TacticM (Option Expr) := do
  let sv ← getGoals
  let st ← saveState
  try
    let mv ← mkFreshExprSyntheticOpaqueMVar ty
    setGoals [mv.mvarId!]
    tac
    unless (← getUnsolvedGoals).isEmpty do throwError "pp: open"
    setGoals sv
    let r ← instantiateMVars mv
    if r.hasMVar then throwError "pp: mvar"
    pure (some r)
  catch _ =>
    st.restore
    setGoals sv
    pure none

def bkFactsCore : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  match t.getAppFnArgs with
  | (``HProp.himpl, #[inst, lhs, rhs]) =>
    if t.hasExprMVar then return ()
    let heads := (xsearchUnfoldExt.getState (← getEnv)).map (·.headFn)
    let L ← regroupAtoms inst (Sep.Xsimpl.parseHstar lhs).toArray
    if L.size > 16 then return ()
    let mut g := goal
    let mut k := 0
    let mut done := false
    for i in [0 : L.size] do
      if done then break
      if ← pastGlobal then break
      match segApp? heads L[i]! with
      | none => pure ()
      | some (pn, bargs) =>
        match ← descOf pn with
        | none => pure ()
        | some d =>
          if bargs.size != d.arity then continue
          if d.nearIdx.size < 2 then continue
          let Nv := d.nearIdx.map (fun m => bargs[m]!)
          let FVv := d.farIdx.map (fun m => bargs[m]!)
          let Cv := d.fixIdx.map (fun m => bargs[m]!)
          let others := (L.toList.zipIdx.filter (fun (_, m) => m != i)).map (·.1)
          if others.isEmpty then continue
          let B ← mkStarOf inst others
          let AB ← mkAppM ``HProp.hstar #[L[i]!, B]
          let mut pm? : Option Expr := none
          for jj in [1 : d.nearIdx.size] do
            if done then break
            if ← pastGlobal then break
            match ← proveBkAlloc d jj with
            | none => pure ()
            | some lem =>
              let c := FVv[jj]!
              let h1 := mkAppN lem ((Nv ++ FVv) ++ Cv)
              let ity ← instantiateMVars (← inferType h1)
              let P := ity.getAppArgs[2]!.getAppArgs[1]!
              if pm?.isNone then
                pm? ← provePerm lhs AB
              let some pm := pm? | continue
              match hasLocPf? inst c B with
              | some h2 =>
                  let stf ← saveState
                  try
                    let hp ← mkAppM ``holds_of_orIn #[h1, h2]
                    let hp ← mkAppM ``holdsP_mono #[pm, hp]
                    let hp ← mkExpectedTypeHint hp
                      (← mkAppM ``holdsP #[P, lhs])
                    let gt ← instantiateMVars (← g.getType)
                    let mv ← g.withContext do
                      mkFreshExprSyntheticOpaqueMVar (← mkArrow P gt)
                    g.assign (mkAppN (mkConst ``himpl_of_holds)
                      #[inst, P, lhs, gt.getAppArgs[2]!, hp, mv])
                    k := k + 1
                    g := mv.mvarId!
                    done := true
                  catch _ => stf.restore
              | none =>
                let locs := ptoLocsOf B #[]
                if locs.size > 10 then continue
                for a in locs do
                  if ← pastGlobal then break
                  if a == c then continue
                  if (← knownNe g a c).isSome then continue
                  let some h2 := hasLocPf? inst a B | continue
                  let stf ← saveState
                  try
                    let ne ← mkAppM ``Ne #[a, c]
                    let some h3 ← provePropBy (← mkArrow P ne)
                      (evalTactic (← `(tactic| (
                        intro hxbq
                        obtain ⟨hxbq1, hxbq2⟩ := hxbq
                        xsearch_subst
                        first
                        | assumption
                        | (apply Ne.symm; assumption)
                        | xsearch_omega))))
                      | throwError "bk: side"
                    let nl ← mkAppM ``neLocs_orIn #[h1, h2, h3]
                    let nl ← mkExpectedTypeHint nl
                      (← mkAppM ``neLocs #[a, c, AB])
                    let npf ← mkAppM ``neLocs_mono #[pm, nl]
                    let gt ← instantiateMVars (← g.getType)
                    let mv ← g.withContext do
                      mkFreshExprSyntheticOpaqueMVar (← mkArrow ne gt)
                    g.assign (mkAppN (mkConst ``himpl_of_neLocs)
                      #[inst, a, c, lhs, gt.getAppArgs[2]!, npf, mv])
                    let (_, g2) ← mv.mvarId!.intro (Name.mkSimple s!"hxbn{k}")
                    k := k + 1
                    g := g2
                  catch _ => stf.restore
    replaceMainGoal [g]
    if done then
      evalTactic (← `(tactic| (intro hxbkp
                               try (obtain ⟨_, _⟩ := hxbkp)
                               try xsearch_subst)))
  | _ => pure ()

elab "xsearch_bkfacts" : tactic => withMainContext do
  bkFactsCore

def exCellWits (heads : Array Name) (L : List Expr) (side : Expr) :
    Array (Nat × Expr) := Id.run do
  let (body, n) := exPeel side
  if n == 0 then return #[]
  let isCell := fun (e : Expr) => e.getAppFn.constName? == some ``HProp.hsingle
  let some cl := body.find? (fun e => isCell e && e.getAppNumArgs ≥ 2 &&
      (match e.getAppArgs[e.getAppNumArgs - 2]! with
       | .bvar k => k < n
       | _ => false)) | return #[]
  let k := match cl.getAppArgs[cl.getAppNumArgs - 2]! with
    | .bvar k => k
    | _ => 0
  let cells := Sep.Xsimpl.parseHstar body |>.filter (fun e => isCell e && e.getAppNumArgs ≥ 2)
  if cells.any (fun e => (e.getAppArgs.back!.find? (· == .bvar k)).isSome) then return #[]
  let fixedLocs := cells.filterMap (fun e =>
    let l := e.getAppArgs[e.getAppNumArgs - 2]!
    if l.hasLooseBVars then none else some l)
  let mut cands : Array Expr := #[]
  for a in L do
    if isCell a && a.getAppNumArgs ≥ 2 then
      let l := a.getAppArgs[a.getAppNumArgs - 2]!
      if l.isFVar && !cands.contains l && !fixedLocs.contains l then cands := cands.push l
  if cands.size < 2 then return #[]
  let mut scored : Array (Nat × Expr) := #[]
  for c in cands do
    let sb := body.replace (fun e => if e == .bvar k then some c else none)
    let mut sc := 0
    for it in Sep.Xsimpl.parseHstar sb do
      match it.getAppFn.constName? with
      | some pn =>
          if heads.contains pn then
            let ra := it.getAppArgs
            if L.any (fun l => l.getAppFn.constName? == some pn &&
                l.getAppNumArgs == ra.size &&
                (List.range ra.size).all (fun m =>
                  ra[m]!.hasLooseBVars || ra[m]! == l.getAppArgs[m]!)) then
              sc := sc + 1
      | none => pure ()
    scored := scored.push (sc, c)
  let sorted := scored.insertionSort (fun a b => a.1 > b.1)
  return sorted.map (fun (_, c) => (n - 1 - k, c))

def exWitAlt (j : Nat) (c : Expr) : TacticM Unit := do
  for i in [0 : j + 1] do
    let g ← getMainGoal
    g.withContext do
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``HProp.himpl_hexists_r)
      let mut rem : List MVarId := []
      for gg in gs do
        if ← gg.isAssigned then continue
        let ty ← instantiateMVars (← gg.getType)
        if ← isProp ty then rem := rem ++ [gg]
        else if i == j then
          unless ← isDefEq (mkMVar gg) c do throwError "exw: assign"
      replaceMainGoal rem
      evalTactic (← `(tactic| try beta_reduce))

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

def witAlts (b : TacticM Unit) (ws : Array (Nat × Expr)) :
    Array (Bool × TacticM Unit) :=
  (ws.map (fun (j, c) => (false, b *> exWitAlt j c))).push (false, b)

theorem fwand_use {α : Sort _} {J : α → HProp} {A B E F C : HProp} (v : α)
    (hj : J v = (A -✶ B)) (h1 : E ==> A) (h2 : B ✶ F ==> C) :
    HProp.hforall J ✶ (E ✶ F) ==> C := by
  have hw : HProp.hforall J ==> (A -✶ B) := hj ▸ HProp.hforall_specialize v J
  refine HProp.himpl_trans (HProp.himpl_frame_l hw) ?_
  refine HProp.himpl_trans (HProp.himpl_frame_r (HProp.himpl_frame_l h1)) ?_
  rw [← HProp.hstar_assoc, HProp.hstar_comm (A -✶ B) A]
  exact HProp.himpl_trans (HProp.himpl_frame_l (HProp.hwand_cancel A B)) h2

theorem par_use {α : Sort _} {J : α → HProp} {P L T C : HProp} (v : α)
    (h : P ==> HProp.hforall J) (hj : J v = ((L ✶ T) -✶ C)) : L ✶ (P ✶ T) ==> C := by
  have h2 : P ==> ((L ✶ T) -✶ C) :=
    hj ▸ HProp.himpl_trans h (HProp.hforall_specialize v J)
  refine HProp.himpl_trans ?_ (HProp.himpl_hwand_r_elim h2)
  rw [HProp.hstar_comm P T, ← HProp.hstar_assoc]
  exact HProp.himpl_refl _

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

structure ParD where
  pname : Name
  nearI : Nat
  wsTys : Array Expr
  lead  : Array Expr
  trail : Array Expr
  deriving Inhabited

initialize parDCache : IO.Ref (Array (Name × Option ParD)) ← IO.mkRef #[]

initialize parCache : IO.Ref (Array (Name × Option Expr)) ← IO.mkRef #[]

def mkParD (p : Name) : MetaM (Option ParD) := do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  for ent in entries do
    if ent.headFn != p then continue
    let ty := (← getConstInfo ent.lemmaName).type
    let r ← forallTelescopeReducing ty fun xs concl => do
      if xs.size != 2 then return none
      let some (_, _, body) := concl.eq? | return none
      unless isHorConst body && body.getAppNumArgs ≥ 2 do return none
      let bargs := body.getAppArgs
      let baseB := bargs[bargs.size-2]!
      let stepB := bargs[bargs.size-1]!
      if (flatStar baseB #[]).any (fun it =>
          it.getAppFn.constName? == some ``HProp.hsingle) then return none
      peelExG stepB #[] fun us bd => do
        let mut recE : Option Expr := none
        let mut rest : Array Expr := #[]
        for it in flatStar bd #[] do
          if it.getAppFn.constName? == some p && recE.isNone then recE := some it
          else rest := rest.push it
        let some rc := recE | return none
        let rargs := rc.getAppArgs
        if rargs.size != 2 then return none
        let some near := (Array.range 2).find? (fun k => us.contains rargs[k]!)
          | return none
        let far := 1 - near
        unless rargs[far]! == xs[far]! do return none
        let rv := rargs[near]!
        let inV := xs[near]!
        let ment := fun (e v : Expr) => (e.find? (· == v)).isSome
        if rest.any (ment · xs[far]!) then return none
        let lead := rest.filter (ment · inV)
        let trail := rest.filter (fun it => !ment it inV)
        let isCell := fun (it : Expr) => it.getAppFn.constName? == some ``HProp.hsingle
        unless lead.any isCell && trail.any isCell do return none
        let shared := us.filter (fun u => lead.any (ment · u) && trail.any (ment · u))
        unless shared.size == 1 do return none
        let a := shared[0]!
        if a == rv || lead.any (ment · rv) then return none
        if us.any (fun u => u != a && lead.any (ment · u)) then return none
        let ws := us.filter (fun u => u != a && u != rv)
        let pd : ParD :=
          { pname := p, nearI := near, wsTys := ← ws.mapM inferType
            lead := ← lead.mapM (mkLambdaFVars #[inV, a] ·)
            trail := ← trail.mapM (mkLambdaFVars (#[a, rv] ++ ws) ·) }
        return some pd
    match r with
    | some d => return some d
    | none => pure ()
  return none

def parDOf (p : Name) : MetaM (Option ParD) := do
  match (← parDCache.get).findSome? (fun e =>
      if e.1 == p then some e.2 else none) with
  | some r => return r
  | none =>
    let r ← try mkParD p catch _ => pure none
    parDCache.modify (·.push (p, r))
    return r

def parP (pd : ParD) (a b : Expr) : Expr :=
  mkAppN (mkConst pd.pname) (if pd.nearI == 0 then #[a, b] else #[b, a])

def parLead (pd : ParD) (inst c x : Expr) : MetaM Expr :=
  mkStarOf inst (pd.lead.map (·.beta #[c, x])).toList

def parTrail (pd : ParD) (inst q p : Expr) (ws : Array Expr) : MetaM Expr :=
  mkStarOf inst (pd.trail.map (·.beta (#[q, p] ++ ws))).toList

def proveParity (solve : Nat → TacticM Unit) (pd : ParD) :
    TacticM (Option Expr) :=
  withLemCache (nm := "par") parCache pd.pname 1560 true do
  let inst := (← instantiateMVars (← (← getMainGoal).getType)).getAppArgs[0]!
  let pty := (← getConstInfo pd.pname).type
  unless pty.isForall do throwError "par: arity"
  let A := pty.bindingDomain!
  let pf ←
    withLocs 4 "pqv" A fun V =>
    withTys pd.wsTys "pqw" fun Ws => do
      let c := V[0]!
      let x := V[1]!
      let q := V[2]!
      let p := V[3]!
      let pnm := parP pd x q
      let some (Ff, ta) ← functionalOf? pnm | throwError "par: not lfp"
      let tup ← tupleOf (if pd.nearI == 0 then #[x, q] else #[q, x])
      unless ← isDefEq ta tup do throwError "par: shape"
      let aty ← inferType tup
      let mkJ : Expr → Expr → MetaM Expr := fun tN tM =>
        withLocalDeclD `pqc A fun c' => do
          let w ← mkAppM ``HProp.hwand
            #[← mkAppM ``HProp.hstar
                #[← parLead pd inst c' tN, ← parTrail pd inst tM p Ws],
              parP pd c' p]
          mkLambdaFVars #[c'] w
      let X ← withLocalDeclD `pqt aty fun t => do
        let p0 ← projOf t 0 2
        let p1 ← projOf t 1 2
        let (tN, tM) := if pd.nearI == 0 then (p0, p1) else (p1, p0)
        mkLambdaFVars #[t] (← mkAppM ``HProp.hforall #[← mkJ tN tM])
      let hXMv ← indSetup Ff X aty
      evalTactic (← `(tactic| (all_goals apply HProp.himpl_hforall_r
                               all_goals intro pqc
                               all_goals apply HProp.himpl_hwand_r
                               all_goals (try xsearch_distr)
                               all_goals (try apply Sep.Xsearch.hdisj_elim))))
      solve 8
      unless (← getUnsolvedGoals).isEmpty do throwError "par: open"
      let J ← mkJ x q
      let key ← mkAppM ``lfpG_induct #[Ff, X, hXMv, tup]
      let key ← mkExpectedTypeHint key
        (← mkAppM ``HProp.himpl #[pnm, ← mkAppM ``HProp.hforall #[J]])
      let Le ← parLead pd inst c x
      let Te ← parTrail pd inst q p Ws
      let C := parP pd c p
      let hj ← mkExpectedTypeHint (← mkEqRefl (mkApp J c))
        (← mkEq (mkApp J c) (← mkAppM ``HProp.hwand
          #[← mkAppM ``HProp.hstar #[Le, Te], C]))
      let pf ← mkAppM ``par_use #[c, key, hj]
      let stmt ← mkAppM ``HProp.himpl
        #[← mkAppM ``HProp.hstar #[Le, ← mkAppM ``HProp.hstar #[pnm, Te]], C]
      unless ← isDefEq (← inferType pf) stmt do throwError "par: type"
      let pf ← mkExpectedTypeHint pf stmt
      let pf ← instantiateMVars (← mkLambdaFVars (V ++ Ws) pf)
      if pf.hasMVar then throwError "par: mvar"
      pure pf
  pure pf

def parityAlt (solve : Nat → TacticM Unit) (lhs rhs : Expr) (L : List Expr)
    (i : Nat) (pd : ParD) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let gt ← instantiateMVars (← g.getType)
  let inst := gt.getAppArgs[0]!
  let atom := L[i]!
  let aa := atom.getAppArgs
  let x := aa[pd.nearI]!
  let q := aa[1 - pd.nearI]!
  let ty ← inferType x
  let cm ← mkFreshExprMVar (some ty)
  let pm ← mkFreshExprMVar (some ty)
  let wms ← pd.wsTys.mapM fun t => mkFreshExprMVar (some t)
  let tmpl := (flatStar (← parLead pd inst cm x) #[]) ++
    flatStar (← parTrail pd inst q pm wms) #[]
  let mut used : Array Nat := #[i]
  for t in tmpl do
    if t.getAppFn.constName? == some ``HProp.hpure then continue
    let mut got := false
    for j in [0 : L.length] do
      if used.contains j then continue
      let ok ← try checkpointDefEq (isDefEq t L[j]!) catch _ => pure false
      if ok then
        used := used.push j
        got := true
        break
    unless got do throwError "par: match"
  let c ← instantiateMVars cm
  let p ← instantiateMVars pm
  let ws ← wms.mapM instantiateMVars
  if c.hasExprMVar || p.hasExprMVar || ws.any (·.hasExprMVar) then
    throwError "par: open"
  unless (rhs.find? (· == c)).isSome do throwError "par: rhs"
  let some lem ← proveParity solve pd | throwError "par: lemma"
  let lemI := mkAppN lem ((#[c, x, q, p] ++ ws))
  let B ← instantiateMVars (← inferType lemI)
  let some (Bs, Bt) := entailHead? B | throwError "par: shape"
  let D ← mkStarOf inst ((L.zipIdx.filter (fun (_, j) => !used.contains j)).map (·.1))
  let mv0 ← mkFreshExprSyntheticOpaqueMVar
    (← mkAppM ``HProp.himpl #[lhs, ← mkAppM ``HProp.hstar #[Bs, D]])
  setGoals [mv0.mvarId!]
  evalTactic (← `(tactic| (xsimpl_core
                           all_goals (try xsimpl_clean)
                           xsearch_pure)))
  unless (← getUnsolvedGoals).isEmpty do throwError "par: pre"
  let mv ← mkFreshExprSyntheticOpaqueMVar
    (← mkAppM ``HProp.himpl #[← mkAppM ``HProp.hstar #[Bt, D], gt.getAppArgs[2]!])
  let full ← mkAppM ``HProp.himpl_trans
    #[mv0, ← mkAppM ``HProp.himpl_trans #[← mkAppM ``frame_l_of #[D, lemI], mv]]
  unless ← isDefEq (← inferType full) gt do throwError "par: mismatch"
  g.assign full
  setGoals [mv.mvarId!]

def parityAlts (solve : Nat → TacticM Unit) (heads : Array Name) (lhs rhs : Expr)
    (L : List Expr) : TacticM (Array (Bool × TacticM Unit)) := do
  let mut out : Array (Bool × TacticM Unit) := #[]
  for i in [0 : L.length] do
    match L[i]!.getAppFn.constName? with
    | some pn =>
        if heads.contains pn && L[i]!.getAppNumArgs == 2 then
          match ← parDOf pn with
          | some pd => out := out.push (false, parityAlt solve lhs rhs L i pd)
          | none => pure ()
    | none => pure ()
  return out

def hwith (H1 H2 : HProp) : HProp := fun h => H1 h ∧ H2 h

theorem hwith_intro {H A B : HProp} (h1 : H ==> A) (h2 : H ==> B) :
    H ==> hwith A B := fun h hh => ⟨h1 h hh, h2 h hh⟩

theorem hwith_l (A B : HProp) : hwith A B ==> A := fun _ hh => hh.1

theorem hwith_r (A B : HProp) : hwith A B ==> B := fun _ hh => hh.2

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

def proveInv (solve : Nat → TacticM Unit) (p : Name) (inv : Expr) (strong : Bool) :
    TacticM (Option Expr) :=
  withLemCache (nm := "inv") invCache (p, inv, strong) 2600 true do
  let pty := (← getConstInfo p).type
  let pf ← forallTelescope pty fun xs _ => do
    let pxs := mkAppN (mkConst p) xs
    let some (Ff, ta) ← functionalOf? pxs | throwError "inv: lfp"
    unless stripInj ta == ta do throwError "inv: group"
    let aty ← inferType ta
    let W := inv.beta xs
    let templ ← if strong then mkAppM ``hwith #[pxs, W] else pure W
    let X ← mkXFunN ta #[templ] 0 aty
    let hXMv ← indSetup Ff X aty
    if strong then
      evalTactic (← `(tactic| all_goals apply Sep.Xsearch.hwith_intro))
    let mut gs : List MVarId := []
    for g in ← getGoals do
      gs := gs ++ (← invIntroGoal g)
    setGoals gs
    evalTactic (← `(tactic| (all_goals (try xsearch_distr)
                             all_goals (try apply Sep.Xsearch.hdisj_elim))))
    solve 8
    unless (← getUnsolvedGoals).isEmpty do throwError "inv: open"
    let key ← mkAppM ``lfpG_induct #[Ff, X, hXMv, ta]
    let key ← if strong then
        mkAppM ``HProp.himpl_trans #[key, ← mkAppM ``hwith_r #[pxs, W]]
      else pure key
    let stmt ← mkAppM ``HProp.himpl #[pxs, W]
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

def projPf (inst : Expr) (L : List Expr) (right : Nat) :
    MetaM (Expr × List Expr) := do
  match L with
  | [] => pure (← mkAppM ``HProp.himpl_refl #[mkApp (mkConst ``HProp.hempty) inst], [])
  | a :: rest =>
    let (pa, a') ←
      if isHwith a then
        let aa := a.getAppArgs
        if right == 0 then pure (← mkAppM ``hwith_r #[aa[1]!, aa[2]!], aa[2]!)
        else pure (← mkAppM ``hwith_l #[aa[1]!, aa[2]!], aa[1]!)
      else pure (← mkAppM ``HProp.himpl_refl #[a], a)
    if rest.isEmpty then return (pa, [a'])
    let (pr, rest') ← projPf inst rest (if right == 0 then L.length + 1 else right - 1)
    return (← mkAppM ``HProp.himpl_frame_lr #[pa, pr], a' :: rest')

def hwithAlt (lhs rhs : Expr) (L : List Expr) (right : Nat) : TacticM Unit :=
  withMainContext do
    let g ← getMainGoal
    let gt ← instantiateMVars (← g.getType)
    let inst := gt.getAppArgs[0]!
    let (pp, L') ← projPf inst L right
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
  if pref then rights ++ lefts else lefts ++ rights

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
  return some (t, fs, fuel, ← forcedDepth.get, (← subTopFuel.get) * 1000 + (← composeDepth.get))

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
  let nil := mkNatLit 0
  let t0 ← vclock
  cmSteps.set 400000
  let mut stCache : Array (Option (Array (Option CmPrepped))) := Array.replicate pols.size none
  let rvs := cmFVars rhs #[]
  let mut seen : Std.HashSet (CmHeap × Array (Option Int) × Array Int) := {}
  let mut stSeen : Std.HashSet (Array Expr) := {}
  let prog := cmCompileTbl tbl
  let rhsN := cmCompile tbl ((List.range vars.size).foldl (fun m i => m.insert vars[i]! i) {})
    vars.size rhs
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
          | some (envA, h, vals) =>
            let key := (h, sp.rvIdx.map (fun i? => i?.bind (fun i => envA[i]?.join)), vals)
            if seen.contains key then continue
            seen := seen.insert key
            let rem ← cmSteps.get
            let bud := min rem 5000
            let ev : CmEv := { prog, off, gvals := envA.filterMap id }
            let cnt0 ← cmCounter.get
            let ((found, inc), (left, cnt)) :=
              (cmConsKI ev (envA.extract 0 vars.size) #[] (2 * h.size + 8) rhsN h).run (bud, cnt0)
            cmCounter.set cnt
            cmSteps.set (rem - (bud - left))
            if !inc && !found then return true
  return false

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
  stmtRefuted vs L rhs

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

mutual

partial def proveInduct (p q : Name) (mode : Nat) (sel : Array Nat)
    (fix : Array (Nat × Expr) := #[]) (rn : Name := q)
    (csts : Array (Nat × Expr) := #[]) : TacticM (Option Expr) := do
  match (← indCache.get).findSome? (fun e =>
      if e.1 == p && e.2.1 == q && e.2.2.1 == mode && e.2.2.2.1 == sel
          && e.2.2.2.2.1 == fix && e.2.2.2.2.2.1 == rn
          && e.2.2.2.2.2.2.1 == csts then
        some e.2.2.2.2.2.2.2 else none) with
  | some r => return r
  | none =>
  if (← indSpent.get) > 3000 then return none
  indCache.modify (·.push (p, q, mode, sel, fix, rn, csts, none))
  let st ← saveState
  let saved ← getGoals
  let start ← vclock
  let oldDeadline ← searchDeadline.get
  let leash := if ← isRecPred p then 2100 else 1100
  searchDeadline.set (min oldDeadline (start + leash))
  let res : Option Expr ←
    try
      let pty := (← getConstInfo p).type
      unless pty.isForall do throwError "ind: arity"
      forallTelescope pty fun xs _ =>
      withLocalDeclD `indc pty.bindingDomain! fun c => do
        if mode != 0 && xs.size != 2 then throwError "ind: not a segment"
        let pxs := mkAppN (mkConst p) xs
        match ← functionalOf? pxs with
        | none => throwError "ind: not a fixpoint"
        | some (F, ta) =>
        let aty ← inferType ta
        let tup := stripInj ta
        let qc := mkConst q
        if sel.any (fun k => k ≥ xs.size) then throwError "ind: sel"
        if !csts.isEmpty && mode != 0 then throwError "ind: csts"
        let qArity := sel.size + csts.size
        if csts.any (fun e => e.1 ≥ qArity) then throwError "ind: cst idx"
        let resArgs : Array Expr := Id.run do
          let mut out : Array (Option Expr) := Array.replicate qArity none
          for (k, e) in csts do
            if k < qArity then out := out.set! k (some e)
          let mut si := 0
          for k in [0 : qArity] do
            if (out[k]!).isNone && si < sel.size then
              out := out.set! k (some xs[sel[si]!]!)
              si := si + 1
          return out.filterMap id
        if mode != 0 && !fix.isEmpty then throwError "ind: fix"
        if mode == 0 && fix.isEmpty && csts.isEmpty then
          if ← stmtRefuted xs pxs (mkAppN (mkConst rn) resArgs) then throwError "ind: cm"
        if fix.any (fun e => e.1 ≥ xs.size) then throwError "ind: fix idx"
        let mkGuards : Expr → MetaM Expr := fun body => do
          let mut r := body
          for (k, e) in fix.reverse do
            r ← mkAppM ``hguard #[← mkAppM ``Eq #[xs[k]!, e], r]
          pure r
        let pm ← groupMembers p
        let hds ←
          if pm.size ≤ 1 then pure #[rn] else assignHeads pm p rn
        let mkTempl : Name → MetaM Expr := fun hn => do
          let hc := mkConst hn
          if mode == 0 then mkGuards (mkAppN hc resArgs)
          else if mode == 1 then
            mkAppM ``HProp.hwand
              #[mkAppN qc #[xs[1]!, c], mkAppN hc #[xs[0]!, c]]
          else if mode == 3 then
            mkAppM ``HProp.hwand
              #[mkAppN qc #[xs[1]!], mkAppN hc #[xs[0]!]]
          else
            mkAppM ``HProp.hwand
              #[mkAppN qc #[c, xs[0]!], mkAppN hc #[c, xs[1]!]]
        let templs ← liftM (hds.mapM mkTempl)
        let X ← mkXFunN tup templs 0 aty
        let hXMv ← indSetup F X aty (if mode != 0 then 3 else 0)
        unless fix.isEmpty do
          evalTactic (← `(tactic| (
            all_goals (repeat (apply Sep.Xsearch.hguard_intro; intro hgfx))
            all_goals (try xsearch_subst)
            all_goals (try simp only [Sep.Xsearch.hguard_rfl,
              Sep.Xsearch.hguard_true]))))
        let oldTop ← subTopFuel.get
        subTopFuel.set (if mode == 0 then 8 else 0)
        try searchSolve 8
        finally subTopFuel.set oldTop
        unless (← getUnsolvedGoals).isEmpty do throwError "ind: open goals"
        setGoals saved
        let key ← mkAppM ``lfpG_induct #[F, X, hXMv, ta]
        let pf ← if mode == 0 then pure key else mkAppM ``wand_consume #[key]
        let rc := mkConst rn
        let stmt ←
          if mode == 0 then
            mkAppM ``HProp.himpl #[pxs, ← mkGuards (mkAppN rc resArgs)]
          else if mode == 1 then
            mkAppM ``HProp.himpl
              #[← mkAppM ``HProp.hstar #[pxs, mkAppN qc #[xs[1]!, c]],
                mkAppN rc #[xs[0]!, c]]
          else if mode == 3 then
            mkAppM ``HProp.himpl
              #[← mkAppM ``HProp.hstar #[pxs, mkAppN qc #[xs[1]!]],
                mkAppN rc #[xs[0]!]]
          else
            mkAppM ``HProp.himpl
              #[← mkAppM ``HProp.hstar #[pxs, mkAppN qc #[c, xs[0]!]],
                mkAppN rc #[c, xs[1]!]]
        unless ← isDefEq (← inferType pf) stmt do throwError "ind: type"
        let pf ← mkExpectedTypeHint pf stmt
        let vars := if mode == 0 || mode == 3 then xs else #[c] ++ xs
        let pf ← instantiateMVars (← mkLambdaFVars vars pf)
        if pf.hasMVar then throwError "ind: mvars"
        pure (some pf)
    catch _ =>
      st.restore
      setGoals saved
      pure none
  searchDeadline.set oldDeadline
  indSpent.modify (· + ((← vclock) - start))
  indCache.modify (fun arr =>
    #[(p, q, mode, sel, fix, rn, csts, res)] ++
      arr.filter (fun e =>
        !(e.1 == p && e.2.1 == q && e.2.2.1 == mode && e.2.2.2.1 == sel
          && e.2.2.2.2.1 == fix && e.2.2.2.2.2.1 == rn
          && e.2.2.2.2.2.2.1 == csts)))
  return res

partial def implAlt (lhs : Expr) (L : List Expr) (i : Nat) (pn qn : Name)
    (sel : Array Nat) (fix : Array (Nat × Expr) := #[])
    (csts : Array (Nat × Expr) := #[]) : TacticM Unit := withMainContext do
  match ← proveInduct pn qn 0 sel fix qn csts with
  | none => throwError "impl: no lemma"
  | some lem0 =>
    let mut lem := mkAppN lem0 (L[i]!).getAppArgs
    for _ in fix do
      lem ← mkAppM ``himpl_hguard_rfl #[lem]
    let g ← getMainGoal
    let A := L[i]!
    let gt ← instantiateMVars (← g.getType)
    let inst := gt.getAppArgs[0]!
    let D ← mkStarOf inst (L.eraseIdx i)
    let aa := A.getAppArgs
    let qArity := sel.size + csts.size
    let bArgs : Array Expr := Id.run do
      let mut out : Array (Option Expr) := Array.replicate qArity none
      for (k, e) in csts do
        if k < qArity then out := out.set! k (some e)
      let mut si := 0
      for k in [0 : qArity] do
        if (out[k]!).isNone && si < sel.size then
          out := out.set! k (some aa[sel[si]!]!)
          si := si + 1
      return out.filterMap id
    let B := mkAppN (mkConst qn) bArgs
    match ← provePerm lhs (← mkAppM ``HProp.hstar #[A, D]) with
    | none => throwError "impl: perm"
    | some h1 =>
      let step ← mkAppM ``frame_l_of #[D, lem]
      let newTy ← mkAppM ``HProp.himpl
        #[← mkAppM ``HProp.hstar #[B, D], gt.getAppArgs[2]!]
      let mv ← mkFreshExprSyntheticOpaqueMVar newTy
      let full ← mkAppM ``HProp.himpl_trans
        #[h1, ← mkAppM ``HProp.himpl_trans #[step, mv]]
      unless ← isDefEq (← inferType full) gt do throwError "impl: mismatch"
      g.assign full
      replaceMainGoal [mv.mvarId!]

partial def implAllAlt (lhs rhs : Expr) (L Rs : List Expr) (idx : Array Nat) :
    TacticM Unit := withMainContext do
  let g ← getMainGoal
  let gt ← instantiateMVars (← g.getType)
  let n := L.length
  if n == 0 || idx.size != n then throwError "ia: shape"
  let mut lems : Array Expr := #[]
  for i in [0 : n] do
    let a := L[i]!
    let c := Rs[idx[i]!]!
    if a == c then lems := lems.push (← mkAppM ``HProp.himpl_refl #[a])
    else
      let some pn := a.getAppFn.constName? | throwError "ia: head"
      let some qn := c.getAppFn.constName? | throwError "ia: head"
      let aargs := a.getAppArgs
      unless aargs == c.getAppArgs && aargs.size > 0 do throwError "ia: args"
      match ← proveInduct pn qn 0 (Array.range aargs.size) #[] qn with
      | none => throwError "ia: lemma"
      | some lem => lems := lems.push (mkAppN lem aargs)
  let tgt := (Array.range n).map (fun i => Rs[idx[i]!]!)
  let mut acc := lems[n-1]!
  let mut srcTail := L[n-1]!
  let mut tgtTail := tgt[n-1]!
  let mut k := n - 1
  while k > 0 do
    k := k - 1
    let fr1 ← mkAppM ``frame_l_of #[srcTail, lems[k]!]
    let fr2 ← mkAppM ``frame_r_of #[tgt[k]!, acc]
    acc ← mkAppM ``HProp.himpl_trans #[fr1, fr2]
    srcTail ← mkAppM ``HProp.hstar #[L[k]!, srcTail]
    tgtTail ← mkAppM ``HProp.hstar #[tgt[k]!, tgtTail]
  let hL ←
    if lhs == srcTail then mkAppM ``HProp.himpl_refl #[lhs]
    else match ← provePerm lhs srcTail with
         | some h => pure h
         | none => throwError "ia: perm l"
  let hR ←
    if tgtTail == rhs then mkAppM ``HProp.himpl_refl #[rhs]
    else match ← provePerm tgtTail rhs with
         | some h => pure h
         | none => throwError "ia: perm r"
  let full ← mkAppM ``HProp.himpl_trans
    #[hL, ← mkAppM ``HProp.himpl_trans #[acc, hR]]
  unless ← isDefEq (← inferType full) gt do throwError "ia: mismatch"
  g.assign full
  replaceMainGoal []

partial def segAltU (lhs rhs : Expr) (L Rs : List Expr) (i j : Nat)
    (pn qn rn : Name) (a b : Expr) : TacticM Unit := withMainContext do
  match ← proveInduct pn qn 3 #[0, 1] #[] rn with
  | none => throwError "segu: no composition lemma"
  | some comp =>
    let g ← getMainGoal
    let A := L[i]!
    let C := Rs[j]!
    let inst := (← instantiateMVars (← g.getType)).getAppArgs[0]!
    let D ← mkStarOf inst (L.eraseIdx i)
    let R ← mkStarOf inst (Rs.eraseIdx j)
    let B := mkAppN (mkConst qn) #[b]
    let hc := mkAppN comp #[a, b]
    match ← provePerm lhs (← mkAppM ``HProp.hstar #[A, D]) with
    | none => throwError "segu: perm l"
    | some h1 =>
      match ← provePerm (← mkAppM ``HProp.hstar #[C, R]) rhs with
      | none => throwError "segu: perm r"
      | some h3 =>
        let newTy ← mkAppM ``HProp.himpl #[D, ← mkAppM ``HProp.hstar #[B, R]]
        let mv ← mkFreshExprSyntheticOpaqueMVar newTy
        let h2 ← mkAppM ``seg_consume #[hc, mv]
        let full ← mkAppM ``HProp.himpl_trans
          #[h1, ← mkAppM ``HProp.himpl_trans #[h2, h3]]
        unless ← isDefEq (← inferType full) (← g.getType) do
          throwError "segu: mismatch"
        g.assign full
        replaceMainGoal [mv.mvarId!]

partial def segAlt (lhs rhs : Expr) (L Rs : List Expr) (i j : Nat)
    (pn qn : Name) (a b c : Expr) (mode : Nat) (rn : Name := qn) :
    TacticM Unit := withMainContext do
  match ← proveInduct pn qn mode #[0, 1] #[] rn with
  | none => throwError "seg: no composition lemma"
  | some comp =>
    let g ← getMainGoal
    let A := L[i]!
    let C := Rs[j]!
    let inst := (← instantiateMVars (← g.getType)).getAppArgs[0]!
    let D ← mkStarOf inst (L.eraseIdx i)
    let R ← mkStarOf inst (Rs.eraseIdx j)
    let B := if mode == 2 then mkAppN (mkConst qn) #[c, a]
             else mkAppN (mkConst qn) #[b, c]
    let hc := mkAppN comp #[c, a, b]
    match ← provePerm lhs (← mkAppM ``HProp.hstar #[A, D]) with
    | none => throwError "seg: perm l"
    | some h1 =>
      match ← provePerm (← mkAppM ``HProp.hstar #[C, R]) rhs with
      | none => throwError "seg: perm r"
      | some h3 =>
        let newTy ← mkAppM ``HProp.himpl #[D, ← mkAppM ``HProp.hstar #[B, R]]
        let mv ← mkFreshExprSyntheticOpaqueMVar newTy
        let h2 ← mkAppM ``seg_consume #[hc, mv]
        let full ← mkAppM ``HProp.himpl_trans
          #[h1, ← mkAppM ``HProp.himpl_trans #[h2, h3]]
        unless ← isDefEq (← inferType full) (← g.getType) do
          throwError "seg: mismatch"
        g.assign full
        replaceMainGoal [mv.mvarId!]

partial def compCore (d : SegDesc) (A Fr : Expr) (FVv Cv : Array Expr) :
    TacticM Expr :=
  withLocs d.nearIdx.size "slnv" A fun Nv =>
  withLocs d.nearIdx.size "slmv" A fun Mv => do
    let pnm := pApp d Nv Mv Cv
    let some (Ff, ta) ← functionalOf? pnm | throwError "cs: not lfp"
    let tup ← tupleOf (segArgsOf d Nv Mv Cv)
    unless ← isDefEq ta tup do throwError "cs: shape"
    let aty ← inferType tup
    let X ← withLocalDeclD `slt aty fun t => do
      let mut prj : Array Expr := #[]
      for i in [0 : d.arity] do prj := prj.push (← projOf t i d.arity)
      let tN := d.nearIdx.map (fun k => prj[k]!)
      let tM := d.farIdx.map (fun k => prj[k]!)
      let tC := d.fixIdx.map (fun k => prj[k]!)
      mkLambdaFVars #[t] (← mkAppM ``HProp.hwand
        #[← mkAppM ``hpack #[pApp d tM FVv tC, Fr],
          ← mkAppM ``hpack #[pApp d tN FVv tC, Fr]])
    let hXMv ← indSetup Ff X aty 2
    searchSolve 6
    unless (← getUnsolvedGoals).isEmpty do throwError "cs: open"
    let key ← mkAppM ``lfpG_induct #[Ff, X, hXMv, tup]
    let pf ← mkAppM ``wand_consume #[key]
    let stmt ← mkAppM ``HProp.himpl
      #[← mkAppM ``HProp.hstar
          #[pnm, ← mkAppM ``HProp.hstar #[pApp d Mv FVv Cv, Fr]],
        ← mkAppM ``HProp.hstar #[pApp d Nv FVv Cv, Fr]]
    unless ← isDefEq (← inferType pf) stmt do throwError "cs: type"
    let pf ← mkExpectedTypeHint pf stmt
    let pf ← instantiateMVars (← mkLambdaFVars (Nv ++ Mv) pf)
    if pf.hasMVar then throwError "cs: mvar"
    pure pf

partial def segFoldBody (d : SegDesc) (inst A Fr : Expr) (FVv Cv : Array Expr)
    (fmode : Nat) : TacticM Expr :=
  let nr := d.nearIdx.size
  withLocs nr "slnv" A fun Nv =>
  withTys d.usTypes "slu" fun Uv => do
    let xsArgs := segArgsOf d Nv FVv Cv
    let mut gTys : Array Expr := #[]
    if fmode == 2 then
      gTys := gTys.push
        (← mkAppM ``Ne #[xsArgs[d.headIdx]!, xsArgs[d.farIdx[0]!]!])
    for (a, b) in d.guards do
      gTys := gTys.push (← mkAppM ``Ne #[xsArgs[a]!, xsArgs[b]!])
    withTys gTys "slg" fun Gv => do
      let full := xsArgs ++ Uv
      let cell := d.cellLam.beta full
      let pre ← mkStarOf inst (cell :: (d.payLams.map (·.beta full)).toList)
      let mut Nn : Array Expr := #[Uv[d.nextU]!]
      for _ in [1 : nr] do Nn := Nn.push Nv[0]!
      let stmt ← mkAppM ``HProp.himpl
        #[← mkAppM ``HProp.hstar
            #[pre, ← mkAppM ``HProp.hstar #[pApp d Nn FVv Cv, Fr]],
          ← mkAppM ``HProp.hstar #[pApp d Nv FVv Cv, Fr]]
      let mv ← mkFreshExprSyntheticOpaqueMVar stmt
      setGoals [mv.mvarId!]
      if fmode == 1 then evalTactic (← `(tactic| try xsearch_hfacts))
      searchSolve 5
      unless (← getUnsolvedGoals).isEmpty do throwError "sl: fold open"
      let r ← instantiateMVars mv
      if r.hasMVar then throwError "sl: fold mvar"
      mkLambdaFVars ((Nv ++ Uv) ++ Gv) r

partial def proveSegLemsG (d : SegDesc) : TacticM (Option SegLems) := do
  match (← segLemCache.get).findSome? (fun e =>
      if e.1 == d.pname then some e.2 else none) with
  | some r => return r
  | none =>
  segLemCache.modify (·.push (d.pname, none))
  let st ← saveState
  let saved ← getGoals
  let oldD ← searchDeadline.get
  searchDeadline.set (min oldD ((← vclock) + 2000))
  let inst := (← instantiateMVars (← (← getMainGoal).getType)).getAppArgs[0]!
  let nr := d.nearIdx.size
  let nf := d.fixIdx.size
  let optPart : TacticM Expr → TacticM (Option Expr) := fun k => do
    let s2 ← saveState
    searchDeadline.set (min oldD ((← vclock) + 2000))
    let r ← try (do
        let v ← k
        setGoals saved
        pure (some v))
      catch _ => do
        s2.restore
        setGoals saved
        pure none
    pure r
  let res : Option SegLems ←
    try
      let pty := (← getConstInfo d.pname).type
      unless pty.isForall do throwError "sl: arity"
      let A := pty.bindingDomain!
      let hpty := mkApp (mkConst ``HProp) inst
      let basePf ← do
        if d.baseCell then
          pure none
        else
          optPart <|
            withLocs nr "slfv" A fun FVv =>
            withLocs nf "slcv" A fun Cv => do
              let stmt ← mkAppM ``HProp.himpl
                #[mkApp (mkConst ``HProp.hempty) inst, pApp d FVv FVv Cv]
              let mv ← mkFreshExprSyntheticOpaqueMVar stmt
              setGoals [mv.mvarId!]
              searchSolve 4
              unless (← getUnsolvedGoals).isEmpty do throwError "sl: base open"
              let r ← instantiateMVars mv
              if r.hasMVar then throwError "sl: base mvar"
              mkLambdaFVars (FVv ++ Cv) r
      let foldPf ←
        withLocalDeclD `slF hpty fun Fr =>
        withLocs nr "slfv" A fun FVv =>
        withLocs nf "slcv" A fun Cv => do
          let hlTy ← mkAppM ``hasLoc #[FVv[0]!, Fr]
          withLocalDeclD `slh hlTy fun hh => do
            let b ← segFoldBody d inst A Fr FVv Cv 1
            mkLambdaFVars ((#[Fr] ++ FVv ++ Cv) ++ #[hh]) b
      let foldNePf ←
        withLocalDeclD `slF hpty fun Fr =>
        withLocs nr "slfv" A fun FVv =>
        withLocs nf "slcv" A fun Cv => do
          let b ← segFoldBody d inst A Fr FVv Cv 2
          mkLambdaFVars ((#[Fr] ++ FVv) ++ Cv) b
      let baseCellPf ← do
        if !d.baseCell then
          pure none
        else
          optPart <|
            withLocalDeclD `slF hpty fun Fr =>
            withLocs nf "slcv" A fun Cv =>
            withLocs nr "slnv" A fun Nv =>
            withTys d.usTypes "slu" fun Uv => do
              let mut Nn : Array Expr := #[Uv[d.nextU]!]
              for _ in [1 : nr] do Nn := Nn.push Nv[0]!
              let xsArgs := segArgsOf d Nv Nn Cv
              let mut gTys : Array Expr := #[]
              for (a, b) in d.guards do
                gTys := gTys.push (← mkAppM ``Ne #[xsArgs[a]!, xsArgs[b]!])
              withTys gTys "slg" fun Gv => do
                let full := xsArgs ++ Uv
                let cell := d.cellLam.beta full
                let pre ← mkStarOf inst (cell :: (d.payLams.map (·.beta full)).toList)
                let stmt ← mkAppM ``HProp.himpl
                  #[← mkAppM ``HProp.hstar #[pre, Fr],
                    ← mkAppM ``HProp.hstar #[pApp d Nv Nn Cv, Fr]]
                let mv ← mkFreshExprSyntheticOpaqueMVar stmt
                setGoals [mv.mvarId!]
                searchSolve 5
                unless (← getUnsolvedGoals).isEmpty do throwError "sl: bc open"
                let r ← instantiateMVars mv
                if r.hasMVar then throwError "sl: bc mvar"
                mkLambdaFVars ((((#[Fr] ++ Cv) ++ Nv) ++ Uv) ++ Gv) r
      setGoals saved
      unless basePf.isSome || baseCellPf.isSome do throwError "sl: no base"
      pure (some { basePf := basePf, baseCell := baseCellPf, foldPf := foldPf,
                   foldNePf := foldNePf })
    catch _ =>
      st.restore
      setGoals saved
      pure none
  searchDeadline.set oldD
  segLemCache.modify (fun arr =>
    #[(d.pname, res)] ++ arr.filter (fun e => e.1 != d.pname))
  return res

partial def segLazy (d : SegDesc) (k : Nat) : TacticM (Option Expr) :=
  withLemCache (nm := s!"segLazy{k}") segLazyCache (d.pname, k) 1560 true do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let inst := (← instantiateMVars (← (← getMainGoal).getType)).getAppArgs[0]!
  let nr := d.nearIdx.size
  let nf := d.fixIdx.size
  let pty := (← getConstInfo d.pname).type
  unless pty.isForall do throwError "sl: arity"
  let A := pty.bindingDomain!
  let hpty := mkApp (mkConst ``HProp) inst
  if k == 0 then
    unless d.baseCell do throwError "sl: no free fold"
    withLocalDeclD `slF hpty fun Fr =>
    withLocs nr "slfv" A fun FVv =>
    withLocs nf "slcv" A fun Cv => do
      let b ← segFoldBody d inst A Fr FVv Cv 0
      mkLambdaFVars ((#[Fr] ++ FVv) ++ Cv) b
  else if k == 1 then
    withLocalDeclD `slF hpty fun Fr =>
    withLocs nr "slfv" A fun FVv =>
    withLocs nf "slcv" A fun Cv => do
    withLocalDeclD `slh (← mkAppM ``hasLoc #[FVv[0]!, Fr]) fun hh => do
      mkLambdaFVars (((#[Fr] ++ FVv) ++ Cv) ++ #[hh]) (← compCore d A Fr FVv Cv)
  else if k == 2 then
    unless nr == 1 do throwError "sl: no nil fold"
    withLocalDeclD `slF hpty fun Fr =>
    withLocs nf "slcv" A fun Cv => do
      let b ← segFoldBody d inst A Fr #[mkNatLit 0] Cv 1
      mkLambdaFVars (#[Fr] ++ Cv) b
  else
    withLocalDeclD `slF hpty fun Fr =>
    withLocs nr "slfv" A fun FVv =>
    withLocs nf "slcv" A fun Cv =>
    withLocs nr "slnv" A fun Nv => do
    withLocalDeclD `slh (← mkAppM ``hasLoc #[FVv[0]!, Fr]) fun hh => do
      let stmt ← mkAppM ``hasLoc
        #[Nv[0]!, ← mkAppM ``HProp.hstar #[pApp d Nv FVv Cv, Fr]]
      let mv ← mkFreshExprSyntheticOpaqueMVar stmt
      setGoals [mv.mvarId!]
      rewriteOcc entries (pApp d Nv FVv Cv)
      evalTactic (← `(tactic| xsearch_hasloc))
      unless (← getUnsolvedGoals).isEmpty do throwError "sl: alloc open"
      let r ← instantiateMVars mv
      if r.hasMVar then throwError "sl: alloc mvar"
      mkLambdaFVars ((((#[Fr] ++ FVv) ++ Cv) ++ Nv) ++ #[hh]) r

partial def proveCompSpec (d : SegDesc) (FVv Cv : Array Expr) :
    TacticM (Option Expr) :=
  withLemCache (nm := "compSpec") compSpecCache (d.pname, FVv, Cv) 1560 true do
  let inst := (← instantiateMVars (← (← getMainGoal).getType)).getAppArgs[0]!
  let pty := (← getConstInfo d.pname).type
  unless pty.isForall do throwError "cs: arity"
  let A := pty.bindingDomain!
  let hpty := mkApp (mkConst ``HProp) inst
  let pf ← withLocalDeclD `slF hpty fun Fr => do
    mkLambdaFVars #[Fr] (← compCore d A Fr FVv Cv)
  pure pf

partial def segExtraLem (nm : Name) (cache : IO.Ref (Array (Name × Option Expr)))
    (d : SegDesc) (k : Expr → Expr → Nat → Nat → TacticM Expr) :
    TacticM (Option Expr) :=
  withLemCache (nm := s!"segExtra.{nm}") cache d.pname 1560 true do
  let inst := (← instantiateMVars (← (← getMainGoal).getType)).getAppArgs[0]!
  let pty := (← getConstInfo d.pname).type
  unless pty.isForall do throwError "{nm}: arity"
  let v ← k inst pty.bindingDomain! d.nearIdx.size d.fixIdx.size
  pure v

partial def proveAllocNe (d : SegDesc) : TacticM (Option Expr) :=
  segExtraLem `allocNe allocNeCache d fun inst A nr nf => do
    let entries := xsearchUnfoldExt.getState (← getEnv)
    let hpty := mkApp (mkConst ``HProp) inst
    withLocalDeclD `slF hpty fun Fr =>
    withLocs nr "slfv" A fun FVv =>
    withLocs nf "slcv" A fun Cv =>
    withLocs nr "slnv" A fun Nv => do
    withLocalDeclD `slne (← mkAppM ``Ne #[Nv[0]!, FVv[0]!]) fun hne => do
      let stmt ← mkAppM ``hasLoc
        #[Nv[0]!, ← mkAppM ``HProp.hstar #[pApp d Nv FVv Cv, Fr]]
      let mv ← mkFreshExprSyntheticOpaqueMVar stmt
      setGoals [mv.mvarId!]
      rewriteOcc entries (pApp d Nv FVv Cv)
      evalTactic (← `(tactic| xsearch_hasloc))
      unless (← getUnsolvedGoals).isEmpty do throwError "sl: allocNe open"
      let r ← instantiateMVars mv
      if r.hasMVar then throwError "sl: allocNe mvar"
      mkLambdaFVars ((((#[Fr] ++ FVv) ++ Cv) ++ Nv) ++ #[hne]) r

partial def proveSrcNe (d : SegDesc) : TacticM (Option Expr) :=
  segExtraLem `srcNe srcNeCache d fun inst A nr nf => do
    let entries := xsearchUnfoldExt.getState (← getEnv)
    let hpty := mkApp (mkConst ``HProp) inst
    withLocalDeclD `slF hpty fun Fr =>
    withLocs nr "slnv" A fun Nv =>
    withLocs nr "slfv" A fun FVv =>
    withLocs nf "slcv" A fun Cv =>
    withLocs 1 "slav" A fun Av => do
      let a := Av[0]!
      withLocalDeclD `slha (← mkAppM ``hasLoc #[a, Fr]) fun hha => do
      withLocalDeclD `slne (← mkAppM ``Ne #[a, FVv[0]!]) fun hne => do
        let stmt ← mkAppM ``neLocs
          #[a, Nv[0]!, ← mkAppM ``HProp.hstar #[pApp d Nv FVv Cv, Fr]]
        let mv ← mkFreshExprSyntheticOpaqueMVar stmt
        setGoals [mv.mvarId!]
        rewriteOcc entries (pApp d Nv FVv Cv)
        evalTactic (← `(tactic| xsearch_srcne))
        unless (← getUnsolvedGoals).isEmpty do throwError "sl: srcNe open"
        let r ← instantiateMVars mv
        if r.hasMVar then throwError "sl: srcNe mvar"
        mkLambdaFVars
          ((((#[Fr] ++ Nv) ++ FVv) ++ Cv) ++ #[a, hha, hne]) r

partial def snocNilParts (d : SegDesc) (inst : Expr) (us : Array Expr)
    (tN tM tC : Array Expr) : MetaM (Expr × Expr × Expr) := do
  let mut na : Array Expr := #[us[d.nextU]!]
  for _ in [1 : d.nearIdx.size] do na := na.push tM[0]!
  let cell := d.cellLam.beta (segArgsOf d tM na tC ++ us)
  let args := segArgsOf d tN na tC
  let mut gs : Array Expr := #[]
  for (a, b) in d.guards do gs := gs.push (← mkAppM ``Ne #[args[a]!, args[b]!])
  let g ← if gs.isEmpty then pure (mkConst ``True) else
    gs.pop.foldrM (fun x acc => mkAppM ``And #[x, acc]) gs.back!
  let pk ← mkAppM ``HProp.hstar #[mkAppN (mkConst ``HProp.hpure) #[inst, g], cell]
  return (pk, pApp d tN na tC, g)

partial def proveSnocNil (d : SegDesc) : TacticM (Option Expr) :=
  segExtraLem `snocNil snocNilCache d fun inst A nr nf => do
    unless !d.baseCell && d.payLams.isEmpty && d.nextU < d.usTypes.size
        && d.farIdx.size == nr do throwError "sn: shape"
    withLocs nr "sznv" A fun Nv =>
    withLocs nr "szmv" A fun Mv =>
    withLocs nf "szcv" A fun Cv =>
    withTys d.usTypes "szuv" fun Us => do
      let us := Us.set! d.nextU (mkNatLit 0)
      let pnm := pApp d Nv Mv Cv
      let some (Ff, ta) ← functionalOf? pnm | throwError "sn: not lfp"
      let tup ← tupleOf (segArgsOf d Nv Mv Cv)
      unless ← isDefEq ta tup do throwError "sn: tuple"
      let aty ← inferType tup
      let X ← withLocalDeclD `szt aty fun t => do
        let mut prj : Array Expr := #[]
        for i in [0 : d.arity] do prj := prj.push (← projOf t i d.arity)
        let (pk, rhs, _) ← snocNilParts d inst us (d.nearIdx.map (fun k => prj[k]!))
          (d.farIdx.map (fun k => prj[k]!)) (d.fixIdx.map (fun k => prj[k]!))
        mkLambdaFVars #[t] (← mkAppM ``HProp.hwand #[pk, rhs])
      let hXMv ← indSetup Ff X aty 2
      searchSolve 6
      unless (← getUnsolvedGoals).isEmpty do throwError "sn: open"
      let key ← mkAppM ``lfpG_induct #[Ff, X, hXMv, tup]
      let pf ← mkAppM ``wand_consume #[key]
      let (pk, rhs, _) ← snocNilParts d inst us Nv Mv Cv
      let stmt ← mkAppM ``HProp.himpl #[← mkAppM ``HProp.hstar #[pnm, pk], rhs]
      unless ← isDefEq (← inferType pf) stmt do throwError "sn: type"
      let pf ← mkExpectedTypeHint pf stmt
      let r ← instantiateMVars (← mkLambdaFVars (((Nv ++ Mv) ++ Cv) ++ Us) pf)
      if r.hasMVar then throwError "sn: mvar"
      pure r

partial def buildGuard (inst : Expr) (plain guarded : List Expr)
    (pp : Expr → TacticM Expr) : TacticM Expr := do
  match guarded with
  | [] => throwError "bg: empty"
  | [g] =>
      match g.getAppFnArgs with
      | (``HProp.hpure, #[_, pr]) =>
          if plain.isEmpty then
            mkAppOptM ``pure_emp #[some inst, some pr, some (← pp pr)]
          else throwError "bg: leftover"
      | _ =>
        match plain with
        | [pl] =>
            if pl == g then mkAppM ``HProp.himpl_refl #[pl]
            else throwError "bg: mismatch"
        | _ => throwError "bg: mismatch2"
  | g :: gs =>
      match g.getAppFnArgs with
      | (``HProp.hpure, #[_, pr]) =>
          mkAppM ``pure_add #[← pp pr, ← buildGuard inst plain gs pp]
      | _ =>
        match plain with
        | pl :: ps =>
            if pl != g then throwError "bg: mismatch3"
            if ps.isEmpty then throwError "bg: short"
            mkAppM ``frame_r_of #[pl, ← buildGuard inst ps gs pp]
        | [] => throwError "bg: short2"

partial def proveSnocK (sd : SnocD) : TacticM (Option Expr) :=
  withLemCache (nm := "snocK") snocKCache sd.pname 3000 false do
  let inst := (← instantiateMVars (← (← getMainGoal).getType)).getAppArgs[0]!
  let pty := (← getConstInfo sd.pname).type
  unless pty.isForall do throwError "sk: arity"
  let A := pty.bindingDomain!
  let hpty := mkApp (mkConst ``HProp) inst
  let mkP : Expr → Expr → Expr := fun a b =>
    mkAppN (mkConst sd.pname) (if sd.nearI == 0 then #[a, b] else #[b, a])
  let pf ←
    withLocalDeclD `skF hpty fun Fr =>
    withLocs 1 "skz" A fun Zv =>
    withTys sd.usTys "sku" fun Uv =>
    withLocs 1 "skx" A fun Xv =>
    withLocs 1 "sky" A fun Yv => do
      let z := Zv[0]!
      let cellsOf : Expr → MetaM Expr := fun y =>
        mkStarOf inst (sd.items.foldl (fun acc l =>
          flatStar (l.beta (#[y, z] ++ Uv)) acc) #[]).toList
      let pnm := mkP Xv[0]! Yv[0]!
      let some (Ff, ta) ← functionalOf? pnm | throwError "sk: not lfp"
      let tup ← tupleOf
        (if sd.nearI == 0 then #[Xv[0]!, Yv[0]!] else #[Yv[0]!, Xv[0]!])
      unless ← isDefEq ta tup do throwError "sk: shape"
      let aty ← inferType tup
      let X ← withLocalDeclD `skt aty fun t => do
        let p0 ← projOf t 0 2
        let p1 ← projOf t 1 2
        let tN := if sd.nearI == 0 then p0 else p1
        let tM := if sd.nearI == 0 then p1 else p0
        mkLambdaFVars #[t] (← mkAppM ``HProp.hwand
          #[← mkAppM ``hpack #[← cellsOf tM, Fr],
            ← mkAppM ``hpack #[mkP tN z, Fr]])
      let hXMv ← indSetup Ff X aty 2
      let mut gs2 : List MVarId := []
      for gg in ← getUnsolvedGoals do
        let ty ← instantiateMVars (← gg.getType)
        if (ty.find? (fun e =>
            e.getAppFn.constName? == some ``HProp.hwand)).isNone then
          setGoals [gg]
          let _ ← tryTactic (evalTactic (← `(tactic|
            simp only [Sep.Xsearch.hpack_eq])))
          gs2 := gs2 ++ (← getUnsolvedGoals)
        else gs2 := gs2 ++ [gg]
      setGoals gs2
      searchSolve 8
      unless (← getUnsolvedGoals).isEmpty do throwError "sk: open"
      let key ← mkAppM ``lfpG_induct #[Ff, X, hXMv, tup]
      let pf ← mkAppM ``wand_consume #[key]
      let stmt ← mkAppM ``HProp.himpl
        #[← mkAppM ``HProp.hstar
            #[pnm, ← mkAppM ``HProp.hstar #[← cellsOf Yv[0]!, Fr]],
          ← mkAppM ``HProp.hstar #[mkP Xv[0]! z, Fr]]
      unless ← isDefEq (← inferType pf) stmt do throwError "sk: type"
      let pf ← mkExpectedTypeHint pf stmt
      let pf ← instantiateMVars
        (← mkLambdaFVars ((((#[Fr] ++ Zv) ++ Uv) ++ Xv) ++ Yv) pf)
      if pf.hasMVar then throwError "sk: mvar"
      pure pf
  pure pf

partial def snocKAlt (lhs : Expr) (atom : Expr) (sd : SnocD) :
    TacticM Unit := withMainContext do
  let g ← getMainGoal
  let gt ← instantiateMVars (← g.getType)
  if gt.hasExprMVar then throwError "sk: mvar goal"
  let inst := gt.getAppArgs[0]!
  let LG ← regroupAtoms inst (Sep.Xsimpl.parseHstar lhs).toArray
  let some i := LG.findIdx? (· == atom) | throwError "sk: atom"
  let a := atom.getAppArgs
  if a.size != 2 then throwError "sk: args"
  let x := a[sd.nearI]!
  let y := a[sd.farI]!
  if x == y then throwError "sk: triv"
  let zmv ← mkFreshExprMVar (some (← inferType x))
  let umvs ← sd.usTys.mapM fun t => mkFreshExprMVar (some t)
  let mut idxs : Array Nat := #[]
  for l in sd.items do
    let t := l.beta (#[y, zmv] ++ umvs)
    let mut found := false
    for j in [0 : LG.size] do
      if j == i || idxs.contains j then continue
      let ok ← try checkpointDefEq (isDefEq t LG[j]!) catch _ => pure false
      if ok then
        idxs := idxs.push j
        found := true
        break
    unless found do
      for c in Sep.Xsimpl.parseHstar t do
        if c.getAppFn.constName? == some ``HProp.hpure then continue
        let mut got := false
        for j in [0 : LG.size] do
          if j == i || idxs.contains j then continue
          let ok ← try checkpointDefEq (isDefEq c LG[j]!) catch _ => pure false
          if ok then
            idxs := idxs.push j
            got := true
            break
        unless got do throwError "sk: match"
  let z ← instantiateMVars zmv
  let us ← umvs.mapM instantiateMVars
  if z.hasExprMVar || us.any (·.hasExprMVar) then throwError "sk: open mvar"
  let some lem ← proveSnocK sd | throwError "sk: lemma"
  let D ← mkStarOf inst ((LG.toList.zipIdx.filter (fun (_, j) =>
    j != i && !idxs.contains j)).map (·.1))
  let step0 := mkAppN lem ((((#[D] ++ #[z]) ++ us) ++ #[x]) ++ #[y])
  let B ← instantiateMVars (← inferType step0)
  let some (Bs, Bt) := entailHead? B | throwError "sk: shape2"
  let ba := Bs.getAppArgs
  if ba.size != 3 then throwError "sk: shape3"
  let bb := ba[2]!.getAppArgs
  if bb.size != 3 then throwError "sk: shape4"
  let cellsE := bb[1]!
  let guarded := (flatStar cellsE #[]).toList
  let plain := (idxs.toList.map (fun j => LG[j]!)).flatMap
    (fun e => (flatStar e #[]).toList)
  let pp : Expr → TacticM Expr := fun pr => do
    let mv ← mkFreshExprSyntheticOpaqueMVar pr
    let sv ← getGoals
    setGoals [mv.mvarId!]
    let ok ← tryTactic (evalTactic (← `(tactic|
      first | assumption | (apply Ne.symm; assumption) | xsearch_omega | trivial)))
    unless ok && (← getUnsolvedGoals).isEmpty do throwError "sk: pure"
    setGoals sv
    instantiateMVars mv
  let gpf ← buildGuard inst plain guarded pp
  let plainE ← mkStarOf inst plain
  let mid ← mkAppM ``HProp.hstar #[atom, ← mkAppM ``HProp.hstar #[plainE, D]]
  let lift ← mkAppM ``frame_r_of #[atom, ← mkAppM ``frame_l_of #[D, gpf]]
  match ← provePerm lhs mid with
  | none => throwError "sk: perm"
  | some h0 =>
    let h1 ← mkAppM ``HProp.himpl_trans #[h0, lift]
    unless ← isDefEq (← inferType h1)
        (← mkAppM ``HProp.himpl #[lhs, Bs]) do throwError "sk: lift"
    let h1 ← mkExpectedTypeHint h1 (← mkAppM ``HProp.himpl #[lhs, Bs])
    let newTy ← mkAppM ``HProp.himpl #[Bt, gt.getAppArgs[2]!]
    let mv ← mkFreshExprSyntheticOpaqueMVar newTy
    let full ← mkAppM ``HProp.himpl_trans
      #[h1, ← mkAppM ``HProp.himpl_trans #[step0, mv]]
    unless ← isDefEq (← inferType full) gt do throwError "sk: mismatch"
    g.assign full
    replaceMainGoal [mv.mvarId!]

partial def proveConvK (p q : Name) (sel : Array Nat) (kAbs : Expr)
    (pures : Array Expr) : TacticM (Option Expr) := do
  let ck : Expr := kAbs
  match (← convCache.get).findSome? (fun e =>
      if e.1 == p && e.2.1 == q && e.2.2.1 == sel && e.2.2.2.1 == ck
          && e.2.2.2.2.1 == pures then
        some e.2.2.2.2.2 else none) with
  | some r => return r
  | none =>
  if (← indSpent.get) > 3000 then return none
  convCache.modify (·.push (p, q, sel, ck, pures, none))
  let st ← saveState
  let saved ← getGoals
  let start ← vclock
  let oldDeadline ← searchDeadline.get
  searchDeadline.set (min oldDeadline (start + 1430))
  let res : Option Expr ←
    try
      let pty := (← getConstInfo p).type
      unless pty.isForall do throwError "conv: arity"
      forallTelescope pty fun xs _ => do
        if sel.any (fun k => k ≥ xs.size) then throwError "conv: sel"
        withTys (pures.map (fun pl => pl.beta xs)) "cvh" fun Hv => do
        let pxs := mkAppN (mkConst p) xs
        let some (F, ta) ← functionalOf? pxs | throwError "conv: not a fixpoint"
        let aty ← inferType ta
        let tup := stripInj ta
        let qargs := sel.map (fun k => xs[k]!)
        let instK := (← inferType (kAbs.beta xs)).getAppArgs[0]!
        let mut kfull := kAbs.beta xs
        for pl in pures.reverse do
          kfull ← mkAppM ``HProp.hstar
            #[mkAppN (mkConst ``HProp.hpure) #[instK, pl.beta xs], kfull]
        let templ ← mkAppM ``HProp.hwand
          #[kfull, mkAppN (mkConst q) qargs]
        let X ← mkXFunN tup #[templ] 0 aty
        let hXMv ← indSetup F X aty 3
        let oldTop ← subTopFuel.get
        let oldFD ← forcedDepth.get
        subTopFuel.set 8
        forcedDepth.set 0
        try searchSolve 16
        finally
          subTopFuel.set oldTop
          forcedDepth.set oldFD
        unless (← getUnsolvedGoals).isEmpty do throwError "conv: open goals"
        setGoals saved
        let key ← mkAppM ``lfpG_induct #[F, X, hXMv, ta]
        let pf ← mkAppM ``wand_consume #[key]
        let stmt ← mkAppM ``HProp.himpl
          #[← mkAppM ``HProp.hstar #[pxs, kfull],
            mkAppN (mkConst q) qargs]
        unless ← isDefEq (← inferType pf) stmt do throwError "conv: type"
        let mut pfa ← mkExpectedTypeHint pf stmt
        for hv in Hv do
          pfa ← mkAppM ``pure_pre #[hv, pfa]
        let pf ← instantiateMVars (← mkLambdaFVars (xs ++ Hv) pfa)
        if pf.hasMVar then throwError "conv: mvars"
        pure (some pf)
    catch _ =>
      st.restore
      setGoals saved
      pure none
  searchDeadline.set oldDeadline
  indSpent.modify (· + ((← vclock) - start))
  convCache.modify (fun arr =>
    #[(p, q, sel, ck, pures, res)] ++ arr.filter (fun e =>
      !(e.1 == p && e.2.1 == q && e.2.2.1 == sel && e.2.2.2.1 == ck
        && e.2.2.2.2.1 == pures)))
  return res

partial def convKAlt (lhs : Expr) (LG : List Expr) (i : Nat) (ks : List Nat)
    (pn qn : Name) (sel : Array Nat) (kAbs : Expr) (pures pfs : Array Expr) :
    TacticM Unit := withMainContext do
  match ← proveConvK pn qn sel kAbs pures with
  | none => throwError "conv: no lemma"
  | some lem =>
    let A := LG[i]!
    let g ← getMainGoal
    let gt ← instantiateMVars (← g.getType)
    let inst := gt.getAppArgs[0]!
    let K ← mkStarOf inst (ks.map (fun m => LG[m]!))
    let D ← mkStarOf inst ((List.range LG.length).filterMap
      (fun m => if m == i || ks.contains m then none else some LG[m]!))
    let hc := mkAppN lem (A.getAppArgs ++ pfs)
    let aa := A.getAppArgs
    let B := mkAppN (mkConst qn) (sel.map (fun m => aa[m]!))
    let KD ← mkAppM ``HProp.hstar #[K, D]
    match ← provePerm lhs (← mkAppM ``HProp.hstar #[A, KD]) with
    | none => throwError "conv: perm"
    | some h1 =>
      let h2 ← mkAppM ``seg_consume
        #[hc, ← mkAppM ``HProp.himpl_refl #[KD]]
      let newTy ← mkAppM ``HProp.himpl
        #[← mkAppM ``HProp.hstar #[B, D], gt.getAppArgs[2]!]
      let mv ← mkFreshExprSyntheticOpaqueMVar newTy
      let full ← mkAppM ``HProp.himpl_trans
        #[h1, ← mkAppM ``HProp.himpl_trans #[h2, mv]]
      unless ← isDefEq (← inferType full) gt do throwError "conv: mismatch"
      g.assign full
      replaceMainGoal [mv.mvarId!]

partial def proveFarImp (d : SegDesc) (j : Nat) : TacticM (Option Expr) :=
  withLemCache (nm := "farImp") farImpCache (d.pname, j) 900 true do
  let inst := (← instantiateMVars (← (← getMainGoal).getType)).getAppArgs[0]!
  let nr := d.nearIdx.size
  let nf := d.fixIdx.size
  let some qlam ← cellPureLam d | throwError "fi: no cell pure"
  if j == 0 || j ≥ nr then throwError "fi: index"
  let pty := (← getConstInfo d.pname).type
  unless pty.isForall do throwError "fi: arity"
  let A := pty.bindingDomain!
  let pf ←
    withLocs nr "finv" A fun Nv =>
    withLocs nr "fifv" A fun FVv =>
    withLocs nf "ficv" A fun Cv => do
      let pnm := pApp d Nv FVv Cv
      let some (Ff, ta) ← functionalOf? pnm | throwError "fi: not lfp"
      let tup ← tupleOf (segArgsOf d Nv FVv Cv)
      unless ← isDefEq ta tup do throwError "fi: shape"
      let aty ← inferType tup
      let X ← withLocalDeclD `fit aty fun t => do
        let mut prj : Array Expr := #[]
        for i in [0 : d.arity] do prj := prj.push (← projOf t i d.arity)
        let pn := mkAppN (mkConst d.pname) prj
        let imp ← mkArrow (qlam.beta #[prj[d.nearIdx[j]!]!])
          (qlam.beta #[prj[d.farIdx[j]!]!])
        mkLambdaFVars #[t] (← mkAppM ``HProp.hstar
          #[mkAppN (mkConst ``HProp.hpure) #[inst, imp], pn])
      let hXMv ← indSetup Ff X aty 1
      searchSolve 5
      unless (← getUnsolvedGoals).isEmpty do throwError "fi: open"
      let key ← mkAppM ``lfpG_induct #[Ff, X, hXMv, tup]
      let imp ← mkArrow (qlam.beta #[Nv[j]!]) (qlam.beta #[FVv[j]!])
      let ent ← mkAppM ``HProp.himpl
        #[pnm, ← mkAppM ``HProp.hstar
          #[mkAppN (mkConst ``HProp.hpure) #[inst, imp], pnm]]
      unless ← isDefEq (← inferType key) ent do throwError "fi: type"
      let key ← mkExpectedTypeHint key ent
      let r ← mkAppM ``holdsP_of #[key]
      let r ← instantiateMVars (← mkLambdaFVars ((Nv ++ FVv) ++ Cv) r)
      if r.hasMVar then throwError "fi: mvar"
      pure r
  pure pf

partial def farImpCore : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  match t.getAppFnArgs with
  | (``HProp.himpl, #[inst, lhs, rhs]) =>
    if t.hasExprMVar then return ()
    let heads := (xsearchUnfoldExt.getState (← getEnv)).map (·.headFn)
    let items := (Sep.Xsimpl.parseHstar lhs).toArray
    if items.size > 24 then return ()
    let mut g := goal
    let mut k := 0
    for i in [0 : items.size] do
      if ← pastGlobal then break
      match segApp? heads items[i]! with
      | none => pure ()
      | some (pn, bargs) =>
        match ← descOf pn with
        | none => pure ()
        | some d =>
          if bargs.size != d.arity then continue
          if d.nearIdx.size < 2 then continue
          for j in [1 : d.nearIdx.size] do
            if ← pastGlobal then break
            match ← proveFarImp d j with
            | none => pure ()
            | some lem =>
              let Nv := d.nearIdx.map (fun kk => bargs[kk]!)
              let FVv := d.farIdx.map (fun kk => bargs[kk]!)
              let Cv := d.fixIdx.map (fun kk => bargs[kk]!)
              let stf ← saveState
              try
                let hp := mkAppN lem ((Nv ++ FVv) ++ Cv)
                let ity ← instantiateMVars (← inferType hp)
                unless ity.getAppFn.constName? == some ``holdsP
                    && ity.getAppNumArgs == 3 do throwError "fi: shape2"
                let P := ity.getAppArgs[1]!
                let known ← g.withContext do
                  (← getLCtx).anyM fun dcl => do
                    if dcl.isImplementationDetail then return false
                    return (← instantiateMVars dcl.type) == P
                if known then throwError "fi: known"
                let some hl := holdsLift? inst P items[i]! hp lhs
                  | throwError "fi: lift"
                let gt ← instantiateMVars (← g.getType)
                let mv ← g.withContext do
                  mkFreshExprSyntheticOpaqueMVar (← mkArrow P gt)
                g.assign (mkAppN (mkConst ``himpl_of_holds)
                  #[inst, P, lhs, rhs, hl, mv])
                let (_, g2) ← mv.mvarId!.intro (Name.mkSimple s!"hxfi{k}")
                k := k + 1
                g := g2
              catch _ => stf.restore
    replaceMainGoal [g]
  | _ => pure ()

partial def composeBuild (d : SegDesc) (lems : SegLems) (inst : Expr)
    (FV C N0 : Array Expr) (steps : Array PStep) (F : Expr)
    (hl? : Option Expr) : TacticM (Expr × Expr × Expr) := do
    let foldPf := lems.foldPf
    let foldNePf := lems.foldNePf
    let startAtLast := !steps.isEmpty
      && (d.baseCell || !steps[steps.size-1]!.cellStep)
    let inner := if startAtLast then steps.extract 0 (steps.size-1) else steps
    let needComp := inner.any (fun e => !e.cellStep)
    let comp? ← if hl?.isSome && needComp then segLazy d 1 else pure none
    let compSpec? : Option Expr ←
      if (hl?.isNone || comp?.isNone) && needComp then proveCompSpec d FV C
      else pure none
    let snocLem? : Option Expr ←
      if needComp && compSpec?.isNone && (hl?.isNone || comp?.isNone)
          && !startAtLast && !d.baseCell && steps.size ≥ 2
          && steps[steps.size-1]!.cellStep && !steps[steps.size-2]!.cellStep
          && FV.size > 0 && FV[0]!.nat? == some 0
          && !((steps.extract 0 (steps.size-2)).any (fun e => !e.cellStep)) then
        proveSnocNil d
      else pure none
    if hl?.isNone && compSpec?.isNone && needComp && snocLem?.isNone then
      witnessMissed.set true
      throwError "cc: no witness"
    let proveNe : Expr → Expr → TacticM Expr := fun x y => do
      let nmv ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Ne #[x, y])
      let sv ← getGoals
      setGoals [nmv.mvarId!]
      let okn ← tryTactic (evalTactic (← `(tactic|
        first | assumption | (apply Ne.symm; assumption) | xsearch_omega)))
      unless okn && (← getUnsolvedGoals).isEmpty do
        witnessMissed.set true
        throwError "cc: ne"
      setGoals sv
      instantiateMVars nmv
    let baseN := if steps.isEmpty then N0 else steps[steps.size-1]!.na
    let mut i := steps.size
    let mut src := F
    let mut cur := F
    let mut acc := F
    if let some sl := snocLem? then
      i := steps.size - 2
      let e1 := steps[i]!
      let e2 := steps[i+1]!
      let pre1 := pApp d e1.nb e1.na C
      let pre2 := d.cellLam.beta (segArgsOf d e2.nb FV C ++ e2.us)
      src ← mkAppM ``HProp.hstar #[pre1, ← mkAppM ``HProp.hstar #[pre2, F]]
      cur ← mkAppM ``HProp.hstar #[pApp d e1.nb FV C, F]
      let args := segArgsOf d e1.nb FV C
      let mut gPfs : Array Expr := #[]
      for (a, b) in d.guards do
        gPfs := gPfs.push (← proveNe args[a]! args[b]!)
      let gp ← if gPfs.isEmpty then pure (mkConst ``True.intro) else
        gPfs.pop.foldrM (fun x acc => mkAppM ``And.intro #[x, acc]) gPfs.back!
      let lemI := mkAppN sl (((e1.nb ++ e1.na) ++ C) ++ e2.us)
      let pf ← mkAppM ``snoc_frame #[F, gp, lemI]
      let want ← mkAppM ``HProp.himpl #[src, cur]
      unless ← isDefEq (← inferType pf) want do throwError "cc: snoc type"
      acc ← mkExpectedTypeHint pf want
    else if startAtLast then
      i := steps.size - 1
      let e := steps[i]!
      let xsArgs := segArgsOf d e.nb FV C
      let pre ←
        if e.cellStep then
          let full := xsArgs ++ e.us
          mkStarOf inst ((d.cellLam.beta full)
            :: (d.payLams.map (·.beta full)).toList)
        else pure (pApp d e.nb e.na C)
      src ← mkAppM ``HProp.hstar #[pre, F]
      cur ← mkAppM ``HProp.hstar #[pApp d e.nb FV C, F]
      if e.cellStep then
        let some bcp := lems.baseCell | throwError "cc: no base cell"
        let mut gPfs : Array Expr := #[]
        for (a, b) in d.guards do
          gPfs := gPfs.push (← proveNe xsArgs[a]! xsArgs[b]!)
        acc ← mkExpectedTypeHint
          (mkAppN bcp ((((#[F] ++ C) ++ e.nb) ++ e.us) ++ gPfs))
          (← mkAppM ``HProp.himpl #[src, cur])
      else
        acc ← mkExpectedTypeHint (← mkAppM ``HProp.himpl_refl #[src])
          (← mkAppM ``HProp.himpl #[src, cur])
    else
      if d.baseCell then throwError "cc: empty chain"
      let some bpf := lems.basePf | throwError "cc: no base"
      cur ← mkAppM ``HProp.hstar #[pApp d baseN FV C, F]
      acc ← mkExpectedTypeHint
        (← mkAppM ``base_frame #[F, mkAppN bpf (FV ++ C)])
        (← mkAppM ``HProp.himpl #[src, cur])
    while i > 0 do
      i := i - 1
      let e := steps[i]!
      let xsArgs := segArgsOf d e.nb FV C
      let mut gPfs : Array Expr := #[]
      for (a, b) in d.guards do
        gPfs := gPfs.push (← proveNe xsArgs[a]! xsArgs[b]!)
      let pre ←
        if e.cellStep then
          let full := xsArgs ++ e.us
          mkStarOf inst ((d.cellLam.beta full)
            :: (d.payLams.map (·.beta full)).toList)
        else pure (pApp d e.nb e.na C)
      let step ←
        if e.cellStep then do
          let ffree ← if hl?.isNone && d.baseCell then segLazy d 0 else pure none
          match hl?, ffree with
          | some hl, _ =>
              pure (mkAppN foldPf
                ((((((#[F] ++ FV) ++ C) ++ #[hl]) ++ e.nb) ++ e.us) ++ gPfs))
          | none, some ff =>
              pure (mkAppN ff
                ((((#[F] ++ FV) ++ C) ++ e.nb) ++ e.us ++ gPfs))
          | none, none => do
              let fnil ← if FV.size == 1 && FV[0]!.nat? == some 0
                  && d.nearIdx.size == 1 then segLazy d 2 else pure none
              match fnil with
              | some fn =>
                  pure (mkAppN fn (((#[F] ++ C) ++ e.nb) ++ e.us ++ gPfs))
              | none => do
                let pg ← proveNe xsArgs[d.headIdx]! xsArgs[d.farIdx[0]!]!
                pure (mkAppN foldNePf
                  (((((#[F] ++ FV) ++ C) ++ e.nb) ++ e.us) ++ #[pg] ++ gPfs))
        else
          match hl?, comp? with
          | some hl, some compPf =>
              pure (mkAppN compPf
                (((((#[F] ++ FV) ++ C) ++ #[hl]) ++ e.nb) ++ e.na))
          | _, _ =>
            match compSpec? with
            | some cs => pure (mkAppN cs ((#[F] ++ e.nb) ++ e.na))
            | none =>
              witnessMissed.set true
              throwError "cc: no witness"
      let nsrc ← mkAppM ``HProp.hstar #[pre, src]
      let ncur ← mkAppM ``HProp.hstar #[pApp d e.nb FV C, F]
      let fr ← mkAppM ``frame_r_of #[pre, acc]
      acc ← mkExpectedTypeHint (← mkAppM ``HProp.himpl_trans #[fr, step])
        (← mkAppM ``HProp.himpl #[nsrc, ncur])
      src := nsrc
      cur := ncur
    return (src, cur, acc)

partial def findWitness (d : SegDesc) (_lems : SegLems) (inst : Expr)
    (w0 : Expr) (frame : List Expr) (F : Expr) : TacticM (Option Expr) := do
    let heads := (xsearchUnfoldExt.getState (← getEnv)).map (·.headFn)
    if ← pastGlobal then throwError "cc: time"
    let tryNeProof : Expr → Expr → TacticM (Option Expr) := fun x y => do
      if x == y then return none
      let sv ← getGoals
      let stn ← saveState
      try
        let nmv ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``Ne #[x, y])
        setGoals [nmv.mvarId!]
        evalTactic (← `(tactic|
          first | assumption | (apply Ne.symm; assumption) | xsearch_omega))
        unless (← getUnsolvedGoals).isEmpty do throwError "cc: ne?"
        setGoals sv
        let r ← instantiateMVars nmv
        if r.hasMVar then throwError "cc: ne? mvar"
        pure (some r)
      catch _ =>
        stn.restore
        setGoals sv
        pure none
    let segAt : Expr → Expr → TacticM (Option (SegDesc × Array Expr)) :=
      fun w atom => do
        match segApp? heads atom with
        | none => return none
        | some (qn, bs) =>
          match ← descOf qn with
          | none => return none
          | some dq =>
            if bs.size != dq.arity then return none
            unless dq.nearIdx.all (fun k => bs[k]! == w) do return none
            return some (dq, bs)
    let neSegBase : Expr → List Expr → TacticM (Option (Expr × List Expr)) :=
      fun w rs => do
        for (atom, i) in rs.zipIdx do
          match ← segAt w atom with
          | none => pure ()
          | some (dq, bs) =>
            let nN := dq.nearIdx.map (fun k => bs[k]!)
            let nF := dq.farIdx.map (fun k => bs[k]!)
            let nC := dq.fixIdx.map (fun k => bs[k]!)
            match ← proveAllocNe dq with
            | none => pure ()
            | some anp =>
              match ← tryNeProof w nF[0]! with
              | some nep =>
                  let rs' := rs.eraseIdx i
                  let pf ← mkExpectedTypeHint
                    (mkAppN anp
                      ((((#[← mkStarOf inst rs'] ++ nF) ++ nC) ++ nN) ++ #[nep]))
                    (← mkAppM ``hasLoc #[w, ← mkAppM ``HProp.hstar
                      #[atom, ← mkStarOf inst rs']])
                  return some (pf, atom :: rs')
              | none => pure ()
        return none
    let allocAt : Expr → List Expr →
        TacticM (Option (Nat × Expr × Array Expr × Array Expr × Array Expr × Expr)) :=
      fun w rs => do
        for (atom, i) in rs.zipIdx do
          match ← segAt w atom with
          | none => pure ()
          | some (dq, bs) =>
            let ap? ←
              if dq.pname == d.pname then segLazy d 3
              else match ← proveSegLemsG dq with
                   | some _ => segLazy dq 3
                   | none => pure none
            match ap? with
            | none => pure ()
            | some ap =>
                return some (i, atom, dq.nearIdx.map (fun k => bs[k]!),
                  dq.farIdx.map (fun k => bs[k]!),
                  dq.fixIdx.map (fun k => bs[k]!), ap)
        return none
    let mut chain :
        Array (Expr × Array Expr × Array Expr × Array Expr × Expr × Expr) := #[]
    let mut rest := frame
    let mut w := w0
    let mut base : Option Expr := none
    let mut stuck := false
    for _ in [0 : 24] do
      if base.isNone && !stuck then
        let direct ←
          if rest.any (fun atom => atomHead? atom == some w) then do
            pure (hasLocPf? inst w (← mkStarOf inst rest))
          else pure none
        match direct with
        | some hp => base := some hp
        | none =>
        match ← neSegBase w rest with
        | some (pf, rs) =>
            base := some pf
            rest := rs
        | none =>
          match ← allocAt w rest with
          | some (i, atom, nN, nF, nC, ap) =>
              chain := chain.push (w, nN, nF, nC, atom, ap)
              rest := rest.eraseIdx i
              w := nF[0]!
          | none => stuck := true
    let hl? : Option Expr ←
      match base with
      | none => pure none
      | some hp => do
        let mut hl := hp
        let mut cur := rest
        let mut k := chain.size
        while k > 0 do
          k := k - 1
          let (_, nN, nF, nC, atom, ap) := chain[k]!
          hl ← mkExpectedTypeHint
            (mkAppN ap ((((#[← mkStarOf inst cur] ++ nF) ++ nC) ++ nN) ++ #[hl]))
            (← mkAppM ``hasLoc #[nN[0]!, ← mkAppM ``HProp.hstar
              #[atom, ← mkStarOf inst cur]])
          cur := atom :: cur
        let hty ← instantiateMVars (← inferType hl)
        let some curE := hty.getAppArgs.back? | pure none
        if curE == F then pure (some hl)
        else
          match ← provePerm F curE with
          | none => pure none
          | some pm => pure (some (← mkAppM ``hasLoc_mono #[pm, hl]))
    return hl?

partial def findSafe (inst : Expr) (w0 : Expr) (frame : List Expr)
    (F : Expr) : TacticM (Option Expr) := do
  let heads := (xsearchUnfoldExt.getState (← getEnv)).map (·.headFn)
  let segAtIn : Expr → TacticM (Option (Nat × Expr × SegDesc × Array Expr)) :=
    fun w => do
      for (atom, i) in frame.zipIdx do
        match segApp? heads atom with
        | none => pure ()
        | some (qn, bs) =>
          match ← descOf qn with
          | none => pure ()
          | some dq =>
            if bs.size != dq.arity then continue
            if dq.farIdx.isEmpty then continue
            unless dq.nearIdx.all (fun k => bs[k]! == w) do continue
            if bs[dq.farIdx[0]!]! == w then continue
            return some (i, atom, dq, bs)
      return none
  let mut path : Array (Nat × Expr × SegDesc × Array Expr) := #[]
  let mut seen : Array Expr := #[]
  let mut w := w0
  let mut term : Option Expr := none
  for _ in [0 : 8] do
    if ← pastGlobal then break
    if w.nat? == some 0 then
      let h ← mkExpectedTypeHint (← mkEqRefl w)
        (← mkAppM ``Eq #[w, mkNatLit 0])
      term := some (← mkAppOptM ``safeFar_nil #[some inst, some w, some F,
        some h])
      break
    match hasLocPf? inst w F with
    | some hp =>
        term := some (← mkAppOptM ``safeFar_loc
          #[some inst, some w, some F, some hp])
        break
    | none => pure ()
    if seen.contains w then break
    seen := seen.push w
    match ← segAtIn w with
    | none => break
    | some (i, atom, dq, bs) =>
        path := path.push (i, atom, dq, bs)
        w := bs[dq.farIdx[0]!]!
  let some t0 := term | return none
  let mut acc := t0
  let mut k := path.size
  while k > 0 do
    k := k - 1
    let (i, atom, dq, bs) := path[k]!
    let wk := bs[dq.nearIdx[0]!]!
    let wn := bs[dq.farIdx[0]!]!
    let some anp ← proveAllocNe dq | return none
    let Frest ← mkStarOf inst (frame.eraseIdx i)
    let whole ← mkAppM ``HProp.hstar #[atom, Frest]
    let some pm ← provePerm F whole | return none
    let nN := dq.nearIdx.map (fun m => bs[m]!)
    let nF := dq.farIdx.map (fun m => bs[m]!)
    let nC := dq.fixIdx.map (fun m => bs[m]!)
    let h1 ← withLocalDeclD `sfne (← mkAppM ``Ne #[wk, wn]) fun hne => do
      let pf ← mkExpectedTypeHint
        (mkAppN anp ((((#[Frest] ++ nF) ++ nC) ++ nN) ++ #[hne]))
        (← mkAppM ``hasLoc #[wk, whole])
      mkLambdaFVars #[hne] (← mkAppM ``hasLoc_mono #[pm, pf])
    let h2 ← withLocalDeclD `sfeq (← mkAppM ``Eq #[wk, wn]) fun heq =>
      mkLambdaFVars #[heq] acc
    let st ← mkAppM ``safeFar #[wk, F]
    let cand ← mkAppOptM ``safeFar_step
      #[some inst, some wk, some wn, some F, some h1, some h2]
    unless ← isDefEq (← inferType cand) st do return none
    acc ← mkExpectedTypeHint cand st
  if acc.hasMVar then return none
  return some acc

partial def composeSafe (d : SegDesc) (lems : SegLems) (inst : Expr)
    (FV C N0 : Array Expr) (steps : Array PStep) (F : Expr) (sp : Expr) :
    TacticM (Expr × Expr × Expr) := do
  unless FV.size == 1 && FV[0]!.isFVar do throwError "cf: shape"
  let f := FV[0]!
  let nil := mkNatLit 0
  let sub : Expr → Expr := fun e =>
    e.replace (fun t => if t == f then some nil else none)
  let steps0 := steps.map (fun e =>
    { e with nb := e.nb.map sub, na := e.na.map sub, us := e.us.map sub })
  let (_, _, acc0) ← composeBuild d lems inst #[nil] (C.map sub) (N0.map sub)
    steps0 (sub F) none
  let (src, cur, lam) ←
    withLocalDeclD `cfh (← mkAppM ``hasLoc #[f, F]) fun hh => do
      let (src, cur, acc) ← composeBuild d lems inst FV C N0 steps F (some hh)
      pure (src, cur, ← mkLambdaFVars #[hh] acc)
  let M ← withLocalDeclD `cfx (← inferType f) fun x => do
    let sx : Expr → Expr := fun e =>
      e.replace (fun t => if t == f then some x else none)
    mkLambdaFVars #[x] (← mkAppM ``HProp.himpl #[sx src, sx cur])
  unless ← isDefEq (← inferType acc0) (M.beta #[nil]) do
    throwError "cf: nil type"
  let acc0 ← mkExpectedTypeHint acc0 (M.beta #[nil])
  let stmt ← mkAppM ``HProp.himpl #[src, cur]
  let pf ← mkAppOptM ``safeFar_elim
    #[some inst, some f, some F, some M, some sp, some acc0, some lam]
  unless ← isDefEq (← inferType pf) stmt do throwError "cf: type"
  let pf ← instantiateMVars (← mkExpectedTypeHint pf stmt)
  if pf.hasMVar then throwError "cf: mvar"
  return (src, cur, pf)

partial def composeChainG (d : SegDesc) (FV C N0 : Array Expr)
    (steps : Array PStep) (L : Array Expr) (used : Array Nat) :
    TacticM Unit := withMainContext do
  match ← proveSegLemsG d with
  | none => throwError "cc: no lemmas"
  | some lems =>
    let g ← getMainGoal
    let gt ← instantiateMVars (← g.getType)
    let inst := gt.getAppArgs[0]!
    let frame := (L.toList.zipIdx.filter (fun (_, i) => !used.contains i)).map (·.1)
    let F ← mkStarOf inst frame
    let hl? ← findWitness d lems inst FV[0]! frame F
    let (src, _cur, acc) ←
      if hl?.isSome then composeBuild d lems inst FV C N0 steps F hl?
      else
        match ← (try findSafe inst FV[0]! frame F catch _ => pure none) with
        | none => composeBuild d lems inst FV C N0 steps F none
        | some sp =>
          try composeSafe d lems inst FV C N0 steps F sp
          catch _ => composeBuild d lems inst FV C N0 steps F none
    match ← provePerm gt.getAppArgs[1]! src with
    | none => throwError "cc: perm"
    | some h1 =>
      let newTy ← mkAppM ``HProp.himpl
        #[← mkAppM ``HProp.hstar #[pApp d N0 FV C, F], gt.getAppArgs[2]!]
      let mv ← mkFreshExprSyntheticOpaqueMVar newTy
      let full ← mkAppM ``HProp.himpl_trans
        #[h1, ← mkAppM ``HProp.himpl_trans #[acc, mv]]
      unless ← isDefEq (← inferType full) gt do throwError "cc: mismatch"
      g.assign full
      replaceMainGoal [mv.mvarId!]

partial def composeAbs (d : SegDesc) (FV C N0 : Array Expr)
    (steps : Array PStep) (inst : Expr) :
    TacticM (Option (Expr × Expr × Expr)) := do
  if steps.isEmpty then return none
  match ← proveSegLemsG d with
  | none => return none
  | some lems =>
    let hpty := mkApp (mkConst ``HProp) inst
    let saved ← getGoals
    let st ← saveState
    try
      let r ← withLocalDeclD `cbG hpty fun G => do
        withLocalDeclD `cbH (← mkAppM ``hasLoc #[FV[0]!, G]) fun hh => do
          let (src, cur, acc) ← composeBuild d lems inst FV C N0 steps G (some hh)
          let items := (Sep.Xsimpl.parseHstar src).filter (fun e => e != G)
          if items.isEmpty then return none
          let S ← mkStarOf inst items
          let SG ← mkAppM ``HProp.hstar #[S, G]
          let tgt ← mkAppM ``HProp.himpl #[SG, cur]
          match ← provePerm SG src with
          | none => return none
          | some pm =>
            let full ← mkAppM ``HProp.himpl_trans #[pm, acc]
            unless ← isDefEq (← inferType full) tgt do return none
            let lam ← instantiateMVars
              (← mkLambdaFVars #[G, hh] (← mkExpectedTypeHint full tgt))
            if lam.hasMVar then return none
            return some (S, pApp d N0 FV C, lam)
      setGoals saved
      return r
    catch _ =>
      st.restore
      setGoals saved
      return none

partial def composePairG (d1 : SegDesc) (FV1 C1 N01 : Array Expr)
    (steps1 : Array PStep) (used1 : Array Nat)
    (d2 : SegDesc) (FV2 C2 N02 : Array Expr)
    (steps2 : Array PStep) (used2 : Array Nat)
    (L : Array Expr) : TacticM Unit := withMainContext do
  if used1.any (fun k => used2.contains k) then throwError "cp: overlap"
  let g ← getMainGoal
  let gt ← instantiateMVars (← g.getType)
  if gt.hasExprMVar then throwError "cp: mvar"
  let inst := gt.getAppArgs[0]!
  let some (S1, T1, A) ← composeAbs d1 FV1 C1 N01 steps1 inst
    | throwError "cp: abs1"
  let some (S2, T2, B) ← composeAbs d2 FV2 C2 N02 steps2 inst
    | throwError "cp: abs2"
  let some lems1 ← proveSegLemsG d1 | throwError "cp: lems1"
  let some lems2 ← proveSegLemsG d2 | throwError "cp: lems2"
  let hasLocOf : SegDesc → SegLems → Expr → Expr → TacticM Expr :=
    fun dd ll w G => do
      match hasLocPf? inst w G with
      | some p => pure p
      | none =>
        match ← findWitness dd ll inst w (Sep.Xsimpl.parseHstar G) G with
        | some p => pure p
        | none => throwError "cp: hasloc"
  let w1 ← hasLocOf d2 lems2 FV1[0]! S2
  let w2 ← hasLocOf d1 lems1 FV2[0]! S1
  let rest := (L.toList.zipIdx.filter (fun (_, i) =>
    !used1.contains i && !used2.contains i)).map (·.1)
  let F ← mkStarOf inst rest
  let comb ← mkAppM ``combine2 #[A, B, w1, w2]
  let srcAll ← mkAppM ``HProp.hstar #[← mkAppM ``HProp.hstar #[S1, S2], F]
  let framed ← mkAppM ``frame_l_of #[F, comb]
  match ← provePerm gt.getAppArgs[1]! srcAll with
  | none => throwError "cp: perm"
  | some pm =>
    let tgtAll ← mkAppM ``HProp.hstar #[← mkAppM ``HProp.hstar #[T1, T2], F]
    let newTy ← mkAppM ``HProp.himpl #[tgtAll, gt.getAppArgs[2]!]
    let mv ← mkFreshExprSyntheticOpaqueMVar newTy
    let full ← mkAppM ``HProp.himpl_trans
      #[pm, ← mkAppM ``HProp.himpl_trans #[framed, mv]]
    unless ← isDefEq (← inferType full) gt do throwError "cp: mismatch"
    g.assign full
    replaceMainGoal [mv.mvarId!]

partial def proveSelfAlloc (p : Name) (idx : Nat) : TacticM (Option Expr) :=
  withLemCache (nm := "selfAlloc") selfAllocCache (p, idx) 500 true do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let pty := (← getConstInfo p).type
  unless pty.isForall do throwError "sa: arity"
  let A := pty.bindingDomain!
  let n ← forallTelescope pty fun xs _ => pure xs.size
  if idx ≥ n then throwError "sa: idx"
  let pf ← withLocs n "sav" A fun Av => do
    let occ := mkAppN (mkConst p) Av
    if ← cmAllocRefuted occ Av[idx]! none then throwError "sa: refuted"
    let stmt ← mkAppM ``hasLoc #[Av[idx]!, occ]
    let mv ← mkFreshExprSyntheticOpaqueMVar stmt
    setGoals [mv.mvarId!]
    rewriteOcc entries occ
    evalTactic (← `(tactic| xsearch_hasloc))
    unless (← getUnsolvedGoals).isEmpty do throwError "sa: open"
    let r ← instantiateMVars mv
    if r.hasMVar then throwError "sa: mvar"
    mkLambdaFVars Av r
  pure pf

partial def dblAllocCore : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (lhs, rhs) := entailHead? t | return ()
  if t.hasExprMVar then return ()
  let inst := t.getAppArgs[0]!
  let heads := (xsearchUnfoldExt.getState (← getEnv)).map (·.headFn)
  let L ← regroupAtoms inst (Sep.Xsimpl.parseHstar lhs).toArray
  if L.size > 20 then return ()
  for i in [0 : L.size] do
    if ← pastGlobal then return ()
    for c in ptoLocsOf L[i]! #[] do
      for j in [i+1 : L.size] do
        match hasLocPf? inst c L[i]!, hasLocPf? inst c L[j]! with
        | some h1, some h2 =>
          let st ← saveState
          try
            let rest := (L.toList.zipIdx.filter (fun (_, m) =>
              m != i && m != j)).map (·.1)
            let Fr ← mkStarOf inst (L[j]! :: rest)
            let h2' ←
              if rest.isEmpty then pure h2
              else do
                let re ← mkStarOf inst rest
                mkAppOptM ``hasLoc_star_l
                  #[some inst, some c, some L[j]!, some re, some h2]
            let G ← mkAppM ``HProp.hstar #[L[i]!, Fr]
            let nl ← mkAppM ``neLocs_star #[h1, h2']
            let nl ← mkExpectedTypeHint nl (← mkAppM ``neLocs #[c, c, G])
            match ← provePerm lhs G with
            | none => throwError "da: perm2"
            | some pm =>
              let nl2 ← mkAppM ``neLocs_mono #[pm, nl]
              let pf ← mkAppOptM ``contra_ne_self
                #[some inst, none, some c, some lhs, some rhs, some nl2]
              unless ← isDefEq (← inferType pf) t do throwError "da: type2"
              g.assign pf
              replaceMainGoal []
              return ()
          catch _ => st.restore
        | _, _ => pure ()
  for i in [0 : L.size] do
    if ← pastGlobal then return ()
    match segApp? heads L[i]! with
    | none => pure ()
    | some (pn, bs) =>
      for k in [0 : bs.size] do
        let c := bs[k]!
        unless c.isFVar do continue
        for j in [0 : L.size] do
          if j == i then continue
          match hasLocPf? inst c L[j]! with
          | none => pure ()
          | some h2 =>
            match ← proveSelfAlloc pn k with
            | none => pure ()
            | some sa =>
              let st ← saveState
              try
                let h1 ← mkExpectedTypeHint (mkAppN sa bs)
                  (← mkAppM ``hasLoc #[c, L[i]!])
                let rest := (L.toList.zipIdx.filter (fun (_, m) =>
                  m != i && m != j)).map (·.1)
                let Fr ← mkStarOf inst (L[j]! :: rest)
                let h2' ←
                  if rest.isEmpty then pure h2
                  else do
                    let re ← mkStarOf inst rest
                    let lj := L[j]!
                    mkAppOptM ``hasLoc_star_l
                      #[some inst, some c, some lj, some re, some h2]
                let G ← mkAppM ``HProp.hstar #[L[i]!, Fr]
                let nl ← mkAppM ``neLocs_star #[h1, h2']
                let nl ← mkExpectedTypeHint nl
                  (← mkAppM ``neLocs #[c, c, G])
                match ← provePerm lhs G with
                | none => throwError "da: perm"
                | some pm =>
                  let nl2 ← mkAppM ``neLocs_mono #[pm, nl]
                  let pf ← mkAppOptM ``contra_ne_self
                    #[some inst, none, some c, some lhs, some rhs, some nl2]
                  unless ← isDefEq (← inferType pf) t do throwError "da: type"
                  g.assign pf
                  replaceMainGoal []
                  return ()
              catch _ => st.restore
  return ()

partial def snefactsCore : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let t ← instantiateMVars (← goal.getType)
  match t.getAppFnArgs with
  | (``HProp.himpl, #[inst, lhs, rhs]) =>
    if t.hasExprMVar then return ()
    let heads := (xsearchUnfoldExt.getState (← getEnv)).map (·.headFn)
    let items := (Sep.Xsimpl.parseHstar lhs).toArray
    if items.size > 24 then return ()
    let plocs := ptoLocsOf lhs #[]
    if plocs.size > 16 then return ()
    let mut g := goal
    let mut k := 0
    for i in [0 : items.size] do
      if ← pastGlobal then break
      match segApp? heads items[i]! with
      | none => pure ()
      | some (pn, bargs) =>
        match ← descOf pn with
        | none => pure ()
        | some d =>
          if bargs.size != d.arity then continue
          let Nv := d.nearIdx.map (fun kk => bargs[kk]!)
          let FVv := d.farIdx.map (fun kk => bargs[kk]!)
          let Cv := d.fixIdx.map (fun kk => bargs[kk]!)
          let v := Nv[0]!
          if plocs.any (· == v) then continue
          let mut cands : Array (Expr × Expr) := #[]
          for a in plocs do
            if a == v then continue
            if (← knownNe g a v).isSome then continue
            match ← knownNe g a FVv[0]! with
            | some nep => cands := cands.push (a, nep)
            | none => pure ()
          if cands.isEmpty then continue
          match ← proveSegLemsG d with
          | none => continue
          | some _ =>
            match ← proveSrcNe d with
            | none => continue
            | some srcNe =>
              let others := (items.toList.zipIdx.filter
                (fun (_, j) => j != i)).map (·.1)
              let F ← mkStarOf inst others
              match ← provePerm lhs
                  (← mkAppM ``HProp.hstar #[items[i]!, F]) with
              | none => continue
              | some pm =>
                for (a, nep) in cands do
                  if ← pastGlobal then break
                  let some hla := hasLocPf? inst a F | continue
                  let st ← saveState
                  try
                    let nl := mkAppN srcNe
                      ((((#[F] ++ Nv) ++ FVv) ++ Cv) ++ #[a, hla, nep])
                    let nl ← mkExpectedTypeHint nl
                      (← mkAppM ``neLocs #[a, v,
                        ← mkAppM ``HProp.hstar #[items[i]!, F]])
                    let npf ← mkAppM ``neLocs_mono #[pm, nl]
                    let gt ← instantiateMVars (← g.getType)
                    let ne ← mkAppM ``Ne #[a, v]
                    let mv ← g.withContext do
                      mkFreshExprSyntheticOpaqueMVar (← mkArrow ne gt)
                    g.assign (mkAppN (mkConst ``himpl_of_neLocs)
                      #[inst, a, v, lhs, rhs, npf, mv])
                    let (_, g2) ← mv.mvarId!.intro
                      (Name.mkSimple s!"hxsn{k}")
                    k := k + 1
                    g := g2
                  catch _ => st.restore
    replaceMainGoal [g]
  | _ => pure ()

partial def composePass (strict : Bool) (fuel : Nat) : TacticM Bool :=
    withMainContext do
  if fuel == 0 then return false
  if ← pastGlobal then return false
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (lhs, rhs) := entailHead? t | return false
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let heads := entries.map (·.headFn)
  let L ← regroupAtoms (t.getAppArgs[0]!) (Sep.Xsimpl.parseHstar lhs).toArray
  let mut queue : Array (Expr × Bool) := #[]
  for r in Sep.Xsimpl.parseHstar rhs do
    match segApp? heads r with
    | some _ =>
        if !L.any (· == r) && !queue.any (fun q => q.1 == r) then
          queue := queue.push (r, false)
    | none => pure ()
  let mut ready :
      Array (Bool × SegDesc × Array Expr × Array Expr × Array Expr ×
             Array PStep × Array Nat) := #[]
  let mut qi := 0
  while qi < queue.size && qi < 24 do
    let (tgt, isSub) := queue[qi]!
    qi := qi + 1
    match segApp? heads tgt with
    | none => pure ()
    | some (pn, targs) =>
      match ← descOf pn with
      | none => pure ()
      | some d =>
        if targs.size != d.arity then continue
        let N0 := d.nearIdx.map (fun k => targs[k]!)
        let FV := d.farIdx.map (fun k => targs[k]!)
        let C := d.fixIdx.map (fun k => targs[k]!)
        match ← (try planChain d L FV C N0 catch _ => pure none) with
        | none => pure ()
        | some (steps, missing, used) =>
          if missing.isEmpty then
            if (steps.size > 0 || isSub) && !(d.baseCell && steps.isEmpty) then
              ready := ready.push (isSub, d, FV, C, N0, steps, used)
            match (Array.range steps.size).find? (fun k => !steps[k]!.cellStep) with
            | some j =>
                if j > 0 then
                  let sub := pApp d steps[j]!.nb FV C
                  if !queue.any (fun q => q.1 == sub) && !L.any (· == sub) then
                    queue := queue.push (sub, true)
            | none => pure ()
          else
            for m in missing do
              if !queue.any (fun q => q.1 == m) && !L.any (· == m) then
                queue := queue.push (m, true)
  let rkey : (Bool × SegDesc × Array Expr × Array Expr × Array Expr ×
      Array PStep × Array Nat) → Nat := fun c =>
    if c.1 then 0
    else if c.2.2.2.2.2.1.any (fun e => !e.cellStep) then 1 else 2
  let nr := ready.size
  let mut deps : Array (Array Nat) := Array.replicate nr #[]
  for i in [0 : nr] do
    let ci := ready[i]!
    let di := ci.2.1
    let w := ci.2.2.1[0]!
    for k in [0 : L.size] do
      let isWit :=
        atomHead? L[k]! == some w
          || (match segApp? heads L[k]! with
              | some (qn, bs) =>
                  qn == di.pname && bs.size == di.arity
                    && bs[di.nearIdx[0]!]! == w
              | none => false)
      if isWit then
        for j in [0 : nr] do
          if j != i && ready[j]!.2.2.2.2.2.2.contains k
              && !deps[j]!.contains i then
            deps := deps.set! j (deps[j]!.push i)
  let mut ordered := #[]
  let mut taken : Array Bool := Array.replicate nr false
  for _ in [0 : nr] do
    let mut pick : Option Nat := none
    for i in [0 : nr] do
      if taken[i]! then continue
      unless deps[i]!.all (fun j => taken[j]!) do continue
      match pick with
      | none => pick := some i
      | some q => if rkey ready[i]! < rkey ready[q]! then pick := some i
    if pick.isNone then
      for i in [0 : nr] do
        if taken[i]! then continue
        match pick with
        | none => pick := some i
        | some q => if rkey ready[i]! < rkey ready[q]! then pick := some i
    match pick with
    | none => pure ()
    | some i =>
        taken := taken.set! i true
        ordered := ordered.push ready[i]!
  if ordered.isEmpty then return strict
  for (_, d, FV, C, N0, steps, used) in ordered do
    if ← pastGlobal then return false
    if (← composeTries.get) == 0 then return false
    composeTries.modify (· - 1)
    let st ← saveState
    let got ←
      try
        composeChainG d FV C N0 steps L used
        pure true
      catch _ =>
        st.restore
        pure false
    if got then
      composeChanged.set true
      let ok ← composePass strict (fuel - 1)
      if strict && !ok then
        st.restore
      else
        return true
  for i in [0 : nr] do
    for j in [i+1 : nr] do
      if ← pastGlobal then return false
      if (← composeTries.get) == 0 then return false
      if deps[i]!.contains j && deps[j]!.contains i then
        let ci := ready[i]!
        let cj := ready[j]!
        composeTries.modify (· - 1)
        let st ← saveState
        let got ←
          try
            composePairG ci.2.1 ci.2.2.1 ci.2.2.2.1 ci.2.2.2.2.1
              ci.2.2.2.2.2.1 ci.2.2.2.2.2.2
              cj.2.1 cj.2.2.1 cj.2.2.2.1 cj.2.2.2.2.1
              cj.2.2.2.2.2.1 cj.2.2.2.2.2.2 L
            pure true
          catch _ =>
            st.restore
            pure false
        if got then
          composeChanged.set true
          let ok ← composePass strict (fuel - 1)
          if strict && !ok then
            st.restore
          else
            return true
  return false

partial def composeAlt : TacticM Unit := do
  if (← composeAltSpent.get) > 1500 then throwError "xsearch: compose alt budget"
  let t0 ← vclock
  let savedTries ← composeTries.get
  let savedChanged ← composeChanged.get
  composeDepth.modify (· + 1)
  composeTries.set 8
  composeChanged.set false
  let r ← try composePass true 8 catch _ => pure false
  let ch ← composeChanged.get
  composeDepth.modify (fun k => k - 1)
  composeTries.set savedTries
  composeChanged.set (savedChanged || ch)
  composeAltSpent.modify (· + ((← vclock) - t0))
  unless r && ch do throwError "xsearch: compose alt failed"

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
    let la := witAlts l (exCellWits heads atoms args[n-2]!)
    let ra := witAlts r (exCellWits heads atoms args[n-1]!)
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
        | some nm =>
            match ← descOf nm with
            | some dd => pure dd.headIdx
            | none => pure 0
        | none => pure 0
      match o.getAppArgs[hi]? with
      | some a => if ptoLocs.any (· == a) then forced := forced.push o
      | none => pure ()
    let ivs ← if fuel ≥ 36 && !t.hasExprMVar then invAlts searchSolve heads lhs rhs L Rs
      else pure #[]
    let mut exact : Array (Bool × TacticM Unit) := #[]
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
    if L.length ≥ 3 && L.length == Rs.length && !t.hasExprMVar then
      let mut idx : Array Nat := #[]
      let mut okAll := true
      let mut diff := false
      for a in L do
        unless okAll do break
        match a.getAppFn.constName? with
        | some pn =>
            if !heads.contains pn || a.getAppNumArgs == 0 then okAll := false
            else
              let aargs := a.getAppArgs
              match (List.range Rs.length).find? (fun m =>
                  !idx.contains m &&
                    (match Rs[m]!.getAppFn.constName? with
                     | some qn => heads.contains qn && Rs[m]!.getAppArgs == aargs
                     | none => false)) with
              | some m =>
                  idx := idx.push m
                  if Rs[m]! != a then diff := true
              | none => okAll := false
        | none => okAll := false
      if okAll && diff && idx.size == L.length then
        if ivs.isEmpty then alts := alts.push (false, implAllAlt lhs rhs L Rs idx)
        else exact := exact.push (false, implAllAlt lhs rhs L Rs idx)
    let fdeep := (← forcedDepth.get) ≥ 6
    for o in forced do
      unless fdeep do alts := alts.push (true, rewriteOcc entries o)
    let lhsOccs := collectOccs heads lhs #[]
    for o in lhsOccs do
      match o.getAppFn.constName? with
      | some nm =>
          if ← isFlatPred nm then alts := alts.push (false, rewriteOcc entries o)
      | none => pure ()
    if (← composeDepth.get) == 0 && !t.hasExprMVar then
      let mut cand := false
      for r in Rs do
        match segApp? heads r with
        | some (rn, _) =>
            if !L.any (· == r) then
              match ← descOf rn with
              | some dd => if dd.baseCell then cand := true
              | none => pure ()
        | none => pure ()
      if cand then alts := alts.push (false, composeAlt)
    for i in [0 : L.length] do
      for j in [0 : Rs.length] do
        match segArgs? heads L[i]!, segArgs? heads Rs[j]! with
        | some (pn, a1, b1), some (rn, a2, c2) =>
            let same := a1 == a2 && b1 == c2 && pn == rn
            let grp ← groupMembers rn
            let others : Expr → Expr → TacticM (Array Name) := fun u v => do
              let mut acc : Array Name := #[]
              for k in [0 : L.length] do
                if k == i then continue
                match segArgs? heads L[k]! with
                | some (qn, u', v') =>
                    if u' == u && v' == v && qn != rn && !acc.contains qn then
                      acc := acc.push qn
                | none => pure ()
              if grp.size ≥ 2
                  && (List.range L.length).any (fun k => atomHead? L[k]! == some u)
              then
                for m in grp do
                  if m != rn && !acc.contains m then acc := acc.push m
              return acc
            if !same && a1 == a2 && (← predOrient entries rn).1 then
              alts := alts.push (false, segAlt lhs rhs L Rs i j pn rn a1 b1 c2 1)
              for qn in ← others b1 c2 do
                alts := alts.push (false, segAlt lhs rhs L Rs i j pn qn a1 b1 c2 1 rn)
            if !same && b1 == c2 && (← predOrient entries rn).2 then
              alts := alts.push (false, segAlt lhs rhs L Rs i j pn rn a1 b1 a2 2)
        | _, _ => pure ()
    for i in [0 : L.length] do
      for j in [0 : Rs.length] do
        match segArgs? heads L[i]!, Rs[j]!.getAppFn.constName? with
        | some (pn, a1, b1), some rn =>
            if heads.contains rn && Rs[j]!.getAppNumArgs == 1
                && Rs[j]!.getAppArgs[0]! == a1 then
              let mut qs : Array Name := #[]
              for k in [0 : L.length] do
                if k == i then continue
                match L[k]!.getAppFn.constName? with
                | some qn =>
                    if heads.contains qn && L[k]!.getAppNumArgs == 1
                        && L[k]!.getAppArgs[0]! == b1 && !qs.contains qn then
                      qs := qs.push qn
                | none => pure ()
              for qn in qs do
                alts := alts.push (false, segAltU lhs rhs L Rs i j pn qn rn a1 b1)
        | _, _ => pure ()
    let mut late : Array (Bool × TacticM Unit) := #[]
    let mut nrImpl : Array (Bool × TacticM Unit) := #[]
    if fuel ≥ 30 then
      let instG := t.getAppArgs[0]!
      let LG ← regroupAtoms instG L.toArray
      let ctxHyps : Array (Expr × Expr) ← g.withContext do
        let mut acc : Array (Expr × Expr) := #[]
        for dcl in ← getLCtx do
          if dcl.isImplementationDetail then continue
          if acc.size ≥ 12 then break
          let dty ← instantiateMVars dcl.type
          if ← isProp dty then acc := acc.push (dty, dcl.toExpr)
        pure acc
      for i in [0 : LG.size] do
        match segApp? heads LG[i]! with
        | none => pure ()
        | some (pn, a) =>
          match ← descOf pn with
          | none => pure ()
          | some d =>
            if a.size == d.arity && !d.farIdx.isEmpty then
              let fv0 := a[d.farIdx[0]!]!
              for rj in Rs do
                match rj.getAppFn.constName? with
                | none => pure ()
                | some qn =>
                  let b := rj.getAppArgs
                  if qn != pn && heads.contains qn && !b.isEmpty
                      && !LG.any (· == rj) then
                    let idx := b.map (fun x =>
                      (Array.range a.size).find? (fun m =>
                        a[m]! == x && d.nearIdx.contains m))
                    if idx.all (·.isSome) then
                      let sel := idx.filterMap id
                      let kks := (List.range LG.size).filter (fun m =>
                        m != i && (LG[m]!.find? (· == fv0)).isSome)
                      if !kks.isEmpty && kks.length ≤ 4 then
                        let Kx ← mkStarOf instG (kks.map (fun m => LG[m]!))
                        match ← absOver d a Kx with
                        | none => pure ()
                        | some kAbs =>
                            let mut pAbs : Array Expr := #[]
                            let mut pFv : Array Expr := #[]
                            for (dty, dfv) in ctxHyps do
                              if pAbs.size ≥ 4 then break
                              unless (dty.find? (· == fv0)).isSome do continue
                              match ← absOver d a dty with
                              | some pl =>
                                  pAbs := pAbs.push pl
                                  pFv := pFv.push dfv
                              | none => pure ()
                            late := late.push (false,
                              convKAlt lhs LG.toList i kks pn qn sel kAbs
                                pAbs pFv)
    for i in [0 : L.length] do
      for j in [0 : Rs.length] do
        match L[i]!.getAppFn.constName?, Rs[j]!.getAppFn.constName? with
        | some pn, some qn =>
            if pn != qn && heads.contains pn && heads.contains qn then
              let aargs := L[i]!.getAppArgs
              let cargs := Rs[j]!.getAppArgs
              if aargs == cargs && cargs.size > 0 then
                if !(← isRecPred pn) then
                  nrImpl := nrImpl.push (false, implAlt lhs L i pn qn (Array.range cargs.size))
                else if ivs.isEmpty then
                  alts := alts.push (false, implAlt lhs L i pn qn (Array.range cargs.size))
                else exact := exact.push (false, implAlt lhs L i pn qn (Array.range cargs.size))
              else if fuel ≥ 30 || fuel ≤ (← subTopFuel.get) then
                let idx := cargs.map (fun c => aargs.findIdx? (· == c))
                if cargs.size > 0 && idx.all (·.isSome) then
                  let sel := idx.filterMap id
                  let mut fx : Array (Nat × Expr) := #[]
                  for k in [0 : aargs.size] do
                    unless sel.contains k || aargs[k]!.isFVar do
                      fx := fx.push (k, aargs[k]!)
                  late := late.push (false, implAlt lhs L i pn qn sel fx)
                else if cargs.size > 0 && cargs.size == aargs.size then
                  if ivs.isEmpty || aargs[0]! != cargs[0]! then
                    late := late.push (false, implAlt lhs L i pn qn (Array.range aargs.size))
                  else exact := exact.push (false, implAlt lhs L i pn qn (Array.range aargs.size))
                else
                  let vsel := (Array.range aargs.size).filter
                    (fun k => aargs[k]!.isFVar)
                  let fx2 := ((Array.range aargs.size).filter
                    (fun k => !aargs[k]!.isFVar)).map (fun k => (k, aargs[k]!))
                  let cc := ((Array.range cargs.size).filter
                    (fun k => !cargs[k]!.isFVar)).map (fun k => (k, cargs[k]!))
                  if cargs.size > 0 && vsel.size > 0
                      && vsel.size + cc.size == cargs.size then
                    late := late.push (false, implAlt lhs L i pn qn vsel fx2 cc)
        | _, _ => pure ()
    for o in lhsOccs do
      match o.getAppFn.constName? with
      | some nm =>
          if !(← isFlatPred nm) && !(← isRecPred nm) then
            late := late.push (false, rewriteOcc entries o)
      | none => pure ()
    for i in [0 : L.length] do
      match L[i]!.getAppFn.constName? with
      | some pn =>
          if heads.contains pn && L[i]!.getAppNumArgs == 2
              && (← descOf pn).isNone then
            match ← snocDOf pn with
            | some sd => late := late.push (false, snocKAlt lhs L[i]! sd)
            | none => pure ()
      | none => pure ()
    let rwEarly := forced.isEmpty && !ptoLocs.isEmpty
    alts := alts ++ (if rwEarly then occsR.map (fun o => (false, rewriteOcc entries o))
      else #[]) ++ late ++ nrImpl
    alts := (← forallAlts lhs rhs L) ++ (← parityAlts searchSolve heads lhs rhs L)
      ++ hwithAlts lhs rhs L Rs ++ specAlts lhs rhs L Rs ++ exact ++ ivs ++ alts
    let early ← if t.hasExprMVar then pure #[] else earlyLhsOccs entries heads lhs rhs
    alts := (early.map (fun o => (false, rewriteOcc entries o))) ++ alts
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
  | _ => false

structure ArPiece where
  cell : Bool
  len : Expr
  lo : Int := 0
  deriving Inhabited

partial def arLin (n k : Expr) (e : Expr) : Option (Int × Int × Int) :=
  if e == n then some (1, 0, 0) else if e == k then some (0, 1, 0) else
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
      let (x1, y1, c1) ← arLin n k a
      let (x2, y2, c2) ← arLin n k b
      pure (x1 + x2, y1 + y2, c1 + c2)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do
      let (x1, y1, c1) ← arLin n k a
      let (x2, y2, c2) ← arLin n k b
      pure (x1 - x2, y1 - y2, c1 - c2)
  | (``Neg.neg, #[_, _, a]) => do
      let (x1, y1, c1) ← arLin n k a
      pure (-x1, -y1, -c1)
  | (``OfNat.ofNat, #[_, l, _]) =>
      match l with
      | .lit (.natVal v) => some (0, 0, v)
      | _ => none
  | _ => none

def arLinEq? (n k c : Expr) : Option (Int × Int × Int) :=
  match c.getAppFnArgs with
  | (``Eq, #[_, a, b]) => do
      let (x1, y1, c1) ← arLin n k a
      let (x2, y2, c2) ← arLin n k b
      pure (x1 - x2, y1 - y2, c1 - c2)
  | _ => none

def arStepDec? (n k c : Expr) : Option Int :=
  match arLinEq? n k c with
  | some (cn, ck, cc) =>
      if ck == 1 && cn == -1 then some cc
      else if ck == -1 && cn == 1 then some (-cc)
      else none
  | none => none

def arIntLit (v : Int) : MetaM Expr := do
  let e ← mkAppOptM ``OfNat.ofNat #[arIntT, mkRawNatLit v.natAbs, none]
  if v < 0 then mkAppM ``Neg.neg #[e] else pure e

def arAdd (a b : Expr) : MetaM Expr := mkAppM ``HAdd.hAdd #[a, b]
def arSub (a b : Expr) : MetaM Expr := mkAppM ``HSub.hSub #[a, b]
def arEq (a b : Expr) : MetaM Expr := mkAppM ``Eq #[a, b]
def arLe (a b : Expr) : MetaM Expr := mkAppM ``LE.le #[a, b]

def arExists (inst : Expr) (vs : Array Expr) (body : Expr) : MetaM Expr := do
  let mut acc := body
  for i in [0 : vs.size] do
    let v := vs[vs.size - 1 - i]!
    let lam ← mkLambdaFVars #[v] acc
    acc ← mkAppOptM ``HProp.hexists #[inst, ← inferType v, lam]
  return acc

def arOmega (p : Expr) : TacticM Expr := do
  let m ← mkFreshExprSyntheticOpaqueMVar p
  let saved ← getGoals
  setGoals [m.mvarId!]
  try
    evalTactic (← `(tactic| omega))
  catch e =>
    setGoals saved
    throw e
  setGoals saved
  instantiateMVars m

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
  for q in pureProps lhs #[] do
    let known ← g.withContext do
      (← getLCtx).anyM fun dcl => do
        if dcl.isImplementationDetail then return false
        return (← instantiateMVars dcl.type) == q
    if known then continue
    let some pf := holdsPf? inst q lhs | continue
    let tcur ← instantiateMVars (← g.getType)
    let mv ← g.withContext do mkFreshExprSyntheticOpaqueMVar (← mkArrow q tcur)
    g.assign (mkAppN (mkConst ``himpl_of_holds) #[inst, q, lhs, rhs, pf, mv])
    let (h, g2) ← mv.mvarId!.intro1P
    g ← arSplitAnd g2 (mkFVar h)
  replaceMainGoal [g]

partial def arIntroLhs : TacticM (Array Expr) := do
  let mut out : Array Expr := #[]
  for _ in [0 : 24] do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some (lhs, _) := entailHead? t | break
    if lhs.isAppOf ``HProp.hexists then
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``HProp.himpl_hexists_l)
      let gs ← gs.filterM fun m => do return !(← m.isAssigned)
      let [g1] := gs | throwError "ar: hexists_l"
      let (x, g2) ← g1.intro1P
      let g3 ← g2.withContext do
        g2.change (← Core.betaReduce (← instantiateMVars (← g2.getType)))
      replaceMainGoal [g3]
      out := out.push (mkFVar x)
    else if (lhs.find? (·.isAppOf ``HProp.hexists)).isSome then
      let ok ← tryTactic (evalTactic (← `(tactic| conv_lhs => simp only
        [HProp.hstar_hexists, Sep.Xsearch.hstar_hexists_rr, HProp.hstar_assoc])))
      unless ok do break
      let t2 ← instantiateMVars (← (← getMainGoal).getType)
      if t2 == t then break
    else break
  arIntroFacts
  return out

def arCloseProps : TacticM Unit := do
  let gs ← getUnsolvedGoals
  for g in gs do
    if ← g.isAssigned then continue
    setGoals [g]
    let t ← instantiateMVars (← g.getType)
    if (entailHead? t).isSome then throwError "ar: open entailment"
    evalTactic (← `(tactic| first | xsearch_pclose | omega | (exfalso; omega)))
  setGoals []

def arRwLhs (As : List Expr) (lem : Expr) : TacticM (Array Expr) := do
  withMainContext do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some (lhs, rhs) := entailHead? t | throwError "ar: not an entailment"
    let inst := t.getAppArgs[0]!
    let lty ← instantiateMVars (← inferType lem)
    let some (lemL, lemR) := entailHead? lty | throwError "ar: lemma shape"
    let mut rest := flatStar lhs #[]
    for x in As do
      match rest.idxOf? x with
      | some i => rest := rest.eraseIdx! i
      | none => throwError "ar: atom not found"
    let restE := starOf inst rest.toList
    let m1 ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``HProp.himpl #[lhs, ← mkAppM ``HProp.hstar #[lemL, restE]])
    setGoals [m1.mvarId!]
    Sep.Xsimpl.xsimplDriver none
    cleanAll
    arCloseProps
    let m2 ← mkFreshExprSyntheticOpaqueMVar
      (← mkAppM ``HProp.himpl #[← mkAppM ``HProp.hstar #[lemR, restE], rhs])
    let fr ← mkAppOptM ``HProp.himpl_frame_l #[inst, lemL, lemR, restE, lem]
    let pf2 ← mkAppOptM ``HProp.himpl_trans #[inst, none, none, none, fr, m2]
    g.assign (← mkAppOptM ``HProp.himpl_trans #[inst, none, none, none, m1, pf2])
    setGoals [m2.mvarId!]
  let mut out : Array Expr := #[]
  for _ in [0 : 16] do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some (lhs, _) := entailHead? t | break
    match lhs.getAppFnArgs with
    | (``HProp.hstar, #[_, ex, rest]) =>
      unless ex.isAppOf ``HProp.hexists do break
      let J := ex.appArg!
      let eq ← mkAppM ``HProp.hstar_hexists #[J, rest]
      let g' ← g.withContext do
        let r ← g.rewrite t eq
        g.replaceTargetEq r.eNew r.eqProof
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
  for _ in [0 : 32] do
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

def arFinish (m : Expr) (vs : Array Expr) : TacticM Expr := do
  unless (← getUnsolvedGoals).isEmpty do throwError "ar: lemma open"
  let pf ← instantiateMVars m
  if pf.hasExprMVar then throwError "ar: lemma mvar"
  mkLambdaFVars vs pf

def arGoal (ty : Expr) : TacticM Expr := do
  let m ← mkFreshExprSyntheticOpaqueMVar ty
  setGoals [m.mvarId!]
  return m

def arEntries : MetaM (Array UnfoldEntry) := return xsearchUnfoldExt.getState (← getEnv)

def arCast (k : Expr) : MetaM Expr := mkAppOptM ``Nat.cast #[arIntT, none, k]

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
  for _ in [0 : 32] do
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
        let _ ← arOmega (← arConj ps)
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

def arWitness : TacticM Unit := do
  arIntroFacts
  withMainContext do
    let g ← getMainGoal
    replaceMainGoal [← fastSubstVars g]
  let ws ← arOpenGoal
  if ws.isEmpty then return
  withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (lhs, rhs) := entailHead? t | throwError "ar: not an entailment"
    let L := (flatStar lhs #[]).filter (!·.isAppOf ``HProp.hpure)
    let R := (flatStar rhs #[]).filter (fun r => !r.isAppOf ``HProp.hpure && r.hasExprMVar)
    unless ← arAssign L R.toList #[] do throwError "ar: no witness"
  for w in ws do
    if (← instantiateMVars w).hasExprMVar then throwError "ar: witness open"

def datConj (l : Array Expr) : MetaM Expr := do
  if l.isEmpty then return mkConst ``True
  let mut acc := l[l.size - 1]!
  for i in [0 : l.size - 1] do acc ← mkAppM ``And #[l[l.size - 2 - i]!, acc]
  return acc

def datMatchClose : TacticM Unit := do
  let ws ← arOpenGoal
  withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (lhs, rhs) := entailHead? t | throwError "dat: not an entailment"
    let L := (flatStar lhs #[]).filter (!·.isAppOf ``HProp.hpure)
    let R := (flatStar rhs #[]).filter (fun r => !r.isAppOf ``HProp.hpure && r.hasExprMVar)
    unless ← arAssign L R.toList #[] do throwError "dat: match"
    for _ in [0 : 2] do
      for c in pureProps (← instantiateMVars rhs) #[] do
        for cc in pureConjs c #[] do
          if let some (_, a, b) := cc.eq? then
            let a ← instantiateMVars a
            let b ← instantiateMVars b
            if a.isMVar && !b.hasExprMVar then let _ ← isDefEq a b
            else if b.isMVar && !a.hasExprMVar then let _ ← isDefEq b a
  for w in ws do
    if (← instantiateMVars w).hasExprMVar then throwError "dat: witness open"
  Sep.Xsimpl.xsimplDriver none
  cleanAll
  arCloseProps

partial def datSplitDisj (fuel : Nat := 6) : TacticM (List MVarId) := do
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
    out := out ++ (← datSplitDisj (fuel - 1))
  return out

structure LenP where
  pname : Name
  inst : Expr
  c : Expr
  phiLam : Expr
  lo : Nat
  branches : Array (Array (Bool × Name))
  members : Array Name
  recursive : Bool
  deriving Inhabited

partial def lenHorBranches (e : Expr) (acc : Array Expr) : Array Expr :=
  if isHorConst e && e.getAppNumArgs ≥ 2 then
    let a := e.getAppArgs
    lenHorBranches a[a.size - 1]! (lenHorBranches a[a.size - 2]! acc)
  else acc.push e

def lenInfo (p : Name) : MetaM (Option (Expr × Expr × Array (Array (Bool × Name)))) := do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let some ent := entries.find? (·.headFn == p) | return none
  let ty := (← getConstInfo ent.lemmaName).type
  forallTelescopeReducing ty fun xs concl => do
    unless xs.size == 2 do return none
    let some (eqT, _, body) := concl.eq? | return none
    let inst := eqT.appArg!
    let mut cLam : Option Expr := none
    let mut brs : Array (Array (Bool × Name)) := #[]
    for br in lenHorBranches body #[] do
      let r ← peelExG br #[] fun _ bd => do
        let items := flatStar bd #[]
        let mut cells : Array (Expr × Expr × Expr) := #[]
        let mut atoms : Array (Name × Expr × Expr) := #[]
        let mut pures : Array Expr := #[]
        for it in items do
          match it.getAppFnArgs with
          | (``HProp.hpure, #[_, pr]) => pures := pureConjs pr pures
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
          let guard := pures.find? (fun q => match q.getAppFnArgs with
            | (``Ne, #[_, x, _]) => x == a
            | _ => false)
          let ta ← inferType a
          let tn ← inferType nx
          let lam ← withLocalDeclD `la ta fun la => withLocalDeclD `lb tn fun lb => do
            let hs := (h.replaceFVar a la).replaceFVar nx lb
            let body ← match guard with
              | some g => mkAppM ``HProp.hstar #[← mkAppOptM ``HProp.hpure #[inst, g.replaceFVar a la], hs]
              | none => pure hs
            mkLambdaFVars #[la, lb] body
          if let some c0 := cl then
            unless c0 == lam do return none
          else cl := some lam
        for q in pures do
          match q.getAppFnArgs with
          | (``Ne, #[_, x, _]) => unless cells.any (·.1 == x) do return none
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
        return some (cl, ps)
      let some (cl, ps) := r | return none
      if let some l := cl then
        if let some c0 := cLam then
          unless c0 == l do return none
        else cLam := some l
      brs := brs.push ps
    let some c := cLam | return some (inst, mkConst ``Unit, brs)
    return some (inst, c, brs)

def lenW : Nat := 16

def lenPhi (S : Array Bool) : Option (Nat × Nat × Array Nat) := do
  let m ← (Array.range S.size).find? (fun i => S[i]!)
  let p ← [1, 2, 3, 4].find? (fun p => (List.range S.size).all (fun n =>
    n < m || n + p ≥ S.size || S[n]! == S[n + p]!))
  let rs := (List.range p).filter (fun r => m + r < S.size && S[m + r]!)
  some (m, p, rs.toArray)

def lenPhiExpr (m p : Nat) (rs : Array Nat) (n : Expr) : MetaM Expr := do
  let lit := fun (v : Nat) => arIntLit v
  let ge ← mkAppM ``LE.le #[← lit m, n]
  if p == 1 then return ge
  let d ← mkAppM ``HMod.hMod #[← mkAppM ``HSub.hSub #[n, ← lit m], ← lit p]
  let mut alts : Array Expr := #[]
  for r in rs do alts := alts.push (← mkAppM ``Eq #[d, ← lit r])
  let mut disj := alts[alts.size - 1]!
  for i in [0 : alts.size - 1] do disj ← mkAppM ``Or #[alts[alts.size - 2 - i]!, disj]
  mkAppM ``And #[ge, disj]

initialize lenPCache : IO.Ref (Array (Name × Option LenP)) ← IO.mkRef #[]

def lenPOf (p : Name) : MetaM (Option LenP) := do
  if let some r := (← lenPCache.get).findSome? (fun e => if e.1 == p then some e.2 else none) then
    return r
  let r ← try (do
      let mut todo : Array Name := #[p]
      let mut infos : Array (Name × Expr × Expr × Array (Array (Bool × Name))) := #[]
      let mut guard := 0
      while !todo.isEmpty && guard < 16 do
        guard := guard + 1
        let q := todo.back!
        todo := todo.pop
        if infos.any (·.1 == q) then continue
        let some (inst, c, brs) ← lenInfo q | throwError "len: info"
        infos := infos.push (q, inst, c, brs)
        for br in brs do
          for (isC, nm) in br do
            if !isC && !infos.any (·.1 == nm) && !todo.contains nm then todo := todo.push nm
      unless todo.isEmpty do throwError "len: closure"
      let cs := (infos.map (·.2.2.1)).filter (· != mkConst ``Unit)
      let some c := cs[0]? | throwError "len: no cell"
      unless cs.all (· == c) do throwError "len: cells"
      let mut S : Array (Name × Array Bool) := infos.map (fun i => (i.1, Array.replicate (lenW + 1) false))
      for _ in [0 : lenW + 2] do
        let mut S2 := S
        for (q, _, _, brs) in infos do
          let mut acc := Array.replicate (lenW + 1) false
          for br in brs do
            let mut cur := Array.replicate (lenW + 1) false
            let nc := (br.filter (·.1)).size
            if nc ≤ lenW then cur := cur.set! nc true
            for (isC, nm) in br do
              if isC then continue
              let some (_, sq) := S.find? (·.1 == nm) | throwError "len: set"
              let mut nxt := Array.replicate (lenW + 1) false
              for a in [0 : lenW + 1] do
                if cur[a]! then
                  for b in [0 : lenW + 1 - a] do
                    if sq[b]! then nxt := nxt.set! (a + b) true
              cur := nxt
            for n in [0 : lenW + 1] do
              if cur[n]! then acc := acc.set! n true
          S2 := S2.map (fun e => if e.1 == q then (q, acc) else e)
        S := S2
      let some (_, sp) := S.find? (·.1 == p) | throwError "len: no set"
      let some (m, per, rs) := lenPhi sp | throwError "len: profile"
      let some (_, inst, _, brs) := infos.find? (·.1 == p) | throwError "len: info"
      let phiLam ← withLocalDeclD `n arIntT fun n => do mkLambdaFVars #[n] (← lenPhiExpr m per rs n)
      let rec_ ← isRecPred p
      let ms ← if rec_ then groupMembers p else pure #[p]
      let ms := if ms.isEmpty then #[p] else ms
      pure (some { pname := p, inst := inst, c := c, phiLam := phiLam, lo := m,
                   branches := brs, members := ms, recursive := rec_ : LenP }))
    catch _ => pure none
  lenPCache.modify (·.push (p, r))
  return r

def lenSeg (P : LenP) (n x y : Expr) : Expr := mkAppN (mkConst ``Sep.segI) #[P.inst, P.c, n, x, y]

def lenAbsTarget (P : LenP) (x y : Expr) : MetaM Expr := do
  withLocalDeclD `ln arIntT fun n => do
    let body ← mkAppM ``HProp.hstar #[lenSeg P n x y, ← mkAppOptM ``HProp.hpure #[P.inst, P.phiLam.beta #[n]]]
    arExists P.inst #[n] body

def lenBeta (e : Expr) : MetaM Expr := do
  let ty ← instantiateMVars (← inferType e)
  mkExpectedTypeHint e (← Core.betaReduce ty)

def lenIsSeg (e : Expr) : Bool := e.isAppOf ``Sep.segI && e.getAppNumArgs == 5

def lenCells (P : LenP) : TacticM Unit := do
  for _ in [0 : 64] do
    let found ← withMainContext do
      let t ← instantiateMVars (← (← getMainGoal).getType)
      let some (lhs, _) := entailHead? t | return none
      let Ls := flatStar lhs #[]
      for h in Ls do
        unless h.isAppOf ``HProp.hsingle do continue
        let a := h.getAppArgs[1]!
        let v := h.getAppArgs[2]!
        let fvs := (Lean.collectFVars {} v).fvarIds
        for f in fvs do
          let cell := (P.c.beta #[a, mkFVar f]).headBeta
          let parts := flatStar cell #[]
          if parts.all (Ls.contains ·) then
            return some (parts, a, mkFVar f)
        if fvs.isEmpty then
          if let some b := v.find? (fun e => e.isFVar || e.isAppOf ``OfNat.ofNat) then
            let cell := (P.c.beta #[a, b]).headBeta
            let parts := flatStar cell #[]
            if parts.all (Ls.contains ·) then return some (parts, a, b)
      return none
    match found with
    | none => return
    | some (parts, a, b) =>
      let lem ← withMainContext do lenBeta (← mkAppOptM ``Sep.segI_cell #[P.inst, P.c, a, b])
      let _ ← arRwLhs parts.toList lem

def lenJoinAll (P : LenP) : TacticM (Option Expr) := do
  for _ in [0 : 64] do
    let r ← withMainContext do
      let t ← instantiateMVars (← (← getMainGoal).getType)
      let some (lhs, _) := entailHead? t | throwError "len: goal"
      let Ss := (flatStar lhs #[]).filter lenIsSeg
      if Ss.size ≤ 1 then return (Ss[0]?, none)
      for A in Ss do
        for B in Ss do
          if A == B then continue
          let aa := A.getAppArgs
          let ba := B.getAppArgs
          if aa[4]! == ba[3]! then
            let lem ← mkAppOptM ``Sep.segI_join #[P.inst, P.c, aa[2]!, ba[2]!, aa[3]!, aa[4]!, ba[4]!]
            return (none, some (A, B, lem))
      throwError "len: no join"
    match r with
    | (res, none) => return res
    | (_, some (A, B, lem)) => let _ ← arRwLhs [A, B] lem
  throwError "len: join fuel"

initialize lenAbsCache : IO.Ref (Array (Name × Option Expr)) ← IO.mkRef #[]
initialize lenConcCache : IO.Ref (Array (Name × Option Expr)) ← IO.mkRef #[]

mutual

partial def lenAbsOf (p : Name) : TacticM (Option Expr) := do
  if let some r := (← lenAbsCache.get).findSome? (fun e => if e.1 == p then some e.2 else none) then
    return r
  lenAbsCache.modify (·.push (p, none))
  let saved ← getGoals
  let st ← saveState
  let r ← try (do
      let some P ← lenPOf p | throwError "len: no profile"
      pure (some (← lenBuildAbs P)))
    catch _ => do st.restore; pure none
  setGoals saved
  lenAbsCache.modify (fun a => #[(p, r)] ++ a.filter (·.1 != p))
  return r

partial def lenAbsLeaf (P : LenP) (grp : Array Name) : TacticM Unit := do
  let _ ← arIntroLhs
  for _ in [0 : 16] do
    let nxt ← withMainContext do
      let t ← instantiateMVars (← (← getMainGoal).getType)
      let some (lhs, _) := entailHead? t | throwError "len: goal"
      pure ((flatStar lhs #[]).find? (fun x => match x.getAppFn.constName? with
        | some q => q != ``Sep.segI && q != ``HProp.hpure && q != ``HProp.hsingle && !grp.contains q
            && x.getAppNumArgs == 2
        | none => false))
    match nxt with
    | none => break
    | some x =>
      let some q := x.getAppFn.constName? | throwError "len: atom"
      let some lem ← lenAbsOf q | throwError "len: no abs"
      let inst ← withMainContext do lenBeta (mkAppN lem x.getAppArgs)
      let _ ← arRwLhs [x] inst
      let _ ← arIntroLhs
  lenCells P
  arIntroFacts
  let res ← lenJoinAll P
  if res.isNone then
    withMainContext do
      let t ← instantiateMVars (← (← getMainGoal).getType)
      let some (_, rhs) := entailHead? t | throwError "len: goal"
      let (body, _) ← arOpen rhs
      let some s := (flatStar body #[]).find? lenIsSeg | throwError "len: rhs"
      let a := s.getAppArgs[3]!
      let b := s.getAppArgs[4]!
      let a ← instantiateMVars a
      let b ← instantiateMVars b
      let h ← arOmega (← mkAppM ``Eq #[a, b])
      let lem ← mkAppOptM ``Sep.segI_zero_intro #[P.inst, P.c, a, b, h]
      let _ ← arRwLhs [] lem
  datMatchClose

partial def lenBuildAbs (P : LenP) : TacticM Expr := do
  let pty := (← getConstInfo P.pname).type
  forallTelescope pty fun xs _ => do
    unless xs.size == 2 do throwError "len: arity"
    let atom := mkAppN (mkConst P.pname) xs
    let tgt ← lenAbsTarget P xs[0]! xs[1]!
    if P.recursive then
      let some (F, ta) ← functionalOf? atom | throwError "len: lfp"
      let aty ← inferType ta
      let tup := stripInj ta
      let mut templs : Array Expr := #[]
      for q in P.members do
        let some Q ← lenPOf q | throwError "len: member"
        templs := templs.push (← lenAbsTarget Q xs[0]! xs[1]!)
      let X ← mkXFunN tup templs 0 aty
      let hX ← indSetup F X aty 1
      let mut leaves : List MVarId := []
      for g in ← getGoals do
        setGoals [g]
        leaves := leaves ++ (← datSplitDisj)
      for g in leaves do
        setGoals [g]
        lenAbsLeaf P P.members
      setGoals []
      let key ← instantiateMVars (← mkAppM ``lfpG_induct #[F, X, hX, ta])
      let ty ← mkAppM ``HProp.himpl #[atom, tgt]
      unless ← isDefEq (← inferType key) ty do throwError "len: abs type"
      let pf ← instantiateMVars (← mkExpectedTypeHint key ty)
      if pf.hasExprMVar then throwError "len: abs mvar"
      mkLambdaFVars xs pf
    else
      let m ← arGoal (← mkAppM ``HProp.himpl #[atom, tgt])
      rewriteOcc (← arEntries) atom
      let leaves ← datSplitDisj
      for g in leaves do
        setGoals [g]
        lenAbsLeaf P #[]
      arFinish m xs

partial def lenConcOf (p : Name) : TacticM (Option Expr) := do
  if let some r := (← lenConcCache.get).findSome? (fun e => if e.1 == p then some e.2 else none) then
    return r
  lenConcCache.modify (·.push (p, none))
  let saved ← getGoals
  let st ← saveState
  let r ← try (do
      let some P ← lenPOf p | throwError "len: no profile"
      pure (some (← lenBuildConc P)))
    catch _ => do st.restore; pure none
  setGoals saved
  lenConcCache.modify (fun a => #[(p, r)] ++ a.filter (·.1 != p))
  return r

partial def lenConcBody (P : LenP) (ms : Array LenP) (k : Expr) : MetaM Expr := do
  withLocalDeclD `n arIntT fun n => withLocalDeclD `x (mkConst ``Nat) fun x =>
  withLocalDeclD `y (mkConst ``Nat) fun y => do
  withLocalDeclD `hk (← mkAppM ``Eq #[n, ← mkAppOptM ``Nat.cast #[arIntT, none, k]]) fun hk => do
    let mut parts : Array Expr := #[]
    for Q in ms do
      let st ← mkAppM ``HProp.himpl #[lenSeg P n x y, mkAppN (mkConst Q.pname) #[x, y]]
      parts := parts.push (← mkArrow (Q.phiLam.beta #[n]) st)
    let conj ← datConj parts
    mkForallFVars #[n, x, y, hk] conj

partial def lenCond (Q : LenP) (j : Nat) (n : Expr) : TacticM Expr := do
  let br := Q.branches[j]!
  let nc := (br.filter (·.1)).size
  let atoms := br.filter (!·.1)
  if atoms.isEmpty then return ← mkAppM ``Eq #[n, ← arIntLit nc]
  let some A ← lenPOf atoms[0]!.2 | throwError "len: atom"
  let l ← arSub n (← arIntLit nc)
  mkAppM ``And #[← arLe (← arIntLit nc) n, A.phiLam.beta #[l]]

partial def lenConcOne (P : LenP) (ms : Array LenP) (Q : LenP) (j : Nat) (k ih goalTy : Expr) :
    TacticM Expr := do
  let m ← arGoal goalTy
  lenConcBranch P ms Q j k ih
  unless (← getUnsolvedGoals).isEmpty do throwError "len: open"
  let pf ← instantiateMVars m
  if pf.hasExprMVar then throwError "len: branch mvar"
  return pf

partial def lenConcTry (P : LenP) (ms : Array LenP) (Q : LenP) (k ih n goalTy : Expr)
    (js : List Nat) : TacticM Expr := do
  match js with
  | [] => throwError "len: no branch"
  | j :: rest =>
    if rest.isEmpty then return ← lenConcOne P ms Q j k ih goalTy
    let cond ← lenCond Q j n
    let proves := fun (p : Expr) => do
      try (do let _ ← arOmega p; pure true) catch _ => pure false
    if ← proves (← mkAppM ``Not #[cond]) then return ← lenConcTry P ms Q k ih n goalTy rest
    let st ← saveState
    let p1 ← try some <$> withLocalDeclD `hc cond (fun hc => do
        mkLambdaFVars #[hc] (← lenConcOne P ms Q j k ih goalTy)) catch _ => pure none
    let some p1 := p1 | do st.restore; throwError "len: branch"
    let p2 ← withLocalDeclD `hnc (← mkAppM ``Not #[cond]) fun hn => do
      mkLambdaFVars #[hn] (← lenConcTry P ms Q k ih n goalTy rest)
    mkAppOptM ``Classical.byCases #[cond, goalTy, p1, p2]

partial def lenConcCase (P : LenP) (ms : Array LenP) (i : Nat) (k ih n x y : Expr) :
    TacticM Expr := do
  let Q := ms[i]!
  withLocalDeclD `hphi (Q.phiLam.beta #[n]) fun hphi => do
    let goalTy ← mkAppM ``HProp.himpl #[lenSeg P n x y, mkAppN (mkConst Q.pname) #[x, y]]
    let saved ← getGoals
    let pf ← lenConcTry P ms Q k ih n goalTy (List.range Q.branches.size)
    setGoals saved
    mkLambdaFVars #[hphi] pf

partial def lenConcBranch (P : LenP) (ms : Array LenP) (Q : LenP) (j : Nat) (k ih : Expr) :
    TacticM Unit := withMainContext do
  let br := Q.branches[j]!
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (lhs, rhs) := entailHead? t | throwError "len: goal"
  let la := lhs.getAppArgs
  let n := la[2]!
  let x := la[3]!
  let y := la[4]!
  let nc := (br.filter (·.1)).size
  let atoms := br.filter (!·.1)
  let one ← arIntLit 1
  if atoms.size == 0 then
    let _ ← arOmega (← mkAppM ``Eq #[n, ← arIntLit nc])
  else if atoms.size > 1 then throwError "len: two atoms"
  let l ← arSub n (← arIntLit nc)
  let lens ← br.mapM fun (c, _) => if c then pure one else pure l
  if atoms.size == 1 then
    let some A ← lenPOf atoms[0]!.2 | throwError "len: atom"
    let _ ← arOmega (← mkAppM ``And #[← arLe (← arIntLit 0) l, A.phiLam.beta #[l]])
  if br.isEmpty then
    let h ← arOmega (← mkAppM ``Eq #[n, ← arIntLit 0])
    let _ ← arRwLhs [lhs] (← mkAppOptM ``Sep.segI_zero_elim #[P.inst, P.c, n, x, y, h])
    arIntroFacts
  else
    let mut cur := lhs
    let mut pieces : Array Expr := #[]
    for i in [0 : br.size] do
      if i + 1 == br.size then
        let ca := cur.getAppArgs
        if ca[2]! != lens[i]! then
          let h ← withMainContext do arOmega (← mkAppM ``Eq #[ca[2]!, lens[i]!])
          let lem ← withMainContext do
            mkAppOptM ``Sep.segI_cong #[P.inst, P.c, ca[2]!, lens[i]!, ca[3]!, ca[4]!, h]
          let _ ← arRwLhs [cur] lem
          cur := lenSeg P lens[i]! ca[3]! ca[4]!
        pieces := pieces.push cur
      else
        let ca := cur.getAppArgs
        let rest ← arSum (lens.extract (i + 1) br.size).toList
        let lem ← withMainContext do
          let hn ← arOmega (← mkAppM ``Eq #[ca[2]!, ← arAdd lens[i]! rest])
          let ha ← arOmega (← arLe (← arIntLit 0) lens[i]!)
          let hb ← arOmega (← arLe (← arIntLit 0) rest)
          mkAppOptM ``Sep.segI_split #[P.inst, P.c, ca[2]!, lens[i]!, rest, ca[3]!, ca[4]!, hn, ha, hb]
        let vs ← arRwLhs [cur] lem
        let some v := vs[0]? | throwError "len: split"
        pieces := pieces.push (lenSeg P lens[i]! ca[3]! v)
        cur := lenSeg P rest v ca[4]!
    for (pc, (isC, nm)) in pieces.zip br do
      let pa := pc.getAppArgs
      if isC then
        let _ ← arRwLhs [pc] (← withMainContext do
          lenBeta (← mkAppOptM ``Sep.segI_uncell #[P.inst, P.c, pa[3]!, pa[4]!]))
      else
        let some A ← lenPOf nm | throwError "len: atom"
        let lem ← withMainContext do
          let kk ← mkAppM ``Int.toNat #[pa[2]!]
          let hk ← arOmega (← mkAppM ``Eq #[pa[2]!, ← mkAppOptM ``Nat.cast #[arIntT, none, kk]])
          let hphi ← arOmega (A.phiLam.beta #[pa[2]!])
          match ms.findIdx? (·.pname == nm) with
          | some idx =>
            let hlt ← arOmega (← mkAppM ``LT.lt #[kk, k])
            let c ← pure (mkAppN ih #[kk, hlt, pa[2]!, pa[3]!, pa[4]!, hk])
            let mut proj := c
            for _ in [0 : idx] do proj ← mkAppM ``And.right #[proj]
            if idx + 1 < ms.size then proj ← mkAppM ``And.left #[proj]
            pure (mkApp proj hphi)
          | none =>
            let some cl ← lenConcOf nm | throwError "len: conc"
            pure (mkAppN cl #[kk, pa[2]!, pa[3]!, pa[4]!, hk, hphi])
        let _ ← arRwLhs [pc] lem
  let _ := rhs
  withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (_, r) := entailHead? t | throwError "len: goal"
    rewriteOcc (← arEntries) r
  for i in [0 : j] do
    let _ := i
    applyConstT ``hdisj_right
  if j + 1 < Q.branches.size then applyConstT ``hdisj_left
  datMatchClose

partial def lenBuildConc (P : LenP) : TacticM Expr := do
  let ms ← if P.recursive then P.members.mapM (fun q => do
      let some Q ← lenPOf q | throwError "len: member"
      pure Q) else pure #[P]
  let some i := ms.findIdx? (·.pname == P.pname) | throwError "len: self"
  let motive ← withLocalDeclD `k (mkConst ``Nat) fun k => do
    mkLambdaFVars #[k] (← lenConcBody P ms k)
  let step ← withLocalDeclD `k (mkConst ``Nat) fun k => do
    let ihTy ← withLocalDeclD `m (mkConst ``Nat) fun mm => do
      mkForallFVars #[mm] (← mkArrow (← mkAppM ``LT.lt #[mm, k]) (motive.beta #[mm]))
    withLocalDeclD `ih ihTy fun ih =>
    withLocalDeclD `n arIntT fun n => withLocalDeclD `x (mkConst ``Nat) fun x =>
    withLocalDeclD `y (mkConst ``Nat) fun y => do
    withLocalDeclD `hk (← mkAppM ``Eq #[n, ← mkAppOptM ``Nat.cast #[arIntT, none, k]]) fun hk => do
      let mut parts : Array Expr := #[]
      for idx in [0 : ms.size] do
        parts := parts.push (← lenConcCase P ms idx k ih n x y)
      let mut acc := parts[parts.size - 1]!
      for t in [0 : parts.size - 1] do
        acc ← mkAppM ``And.intro #[parts[parts.size - 2 - t]!, acc]
      mkLambdaFVars #[k, ih, n, x, y, hk] acc
  let rec_ ← withLocalDeclD `k (mkConst ``Nat) fun k => do
    let t ← mkAppOptM ``Nat.strongRecOn #[motive, k, step]
    mkLambdaFVars #[k] t
  withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `n arIntT fun n =>
  withLocalDeclD `x (mkConst ``Nat) fun x => withLocalDeclD `y (mkConst ``Nat) fun y => do
  withLocalDeclD `hk (← mkAppM ``Eq #[n, ← mkAppOptM ``Nat.cast #[arIntT, none, k]]) fun hk => do
  withLocalDeclD `hphi (P.phiLam.beta #[n]) fun hphi => do
    let mut c := mkAppN (rec_.beta #[k]) #[n, x, y, hk]
    for _ in [0 : i] do c ← mkAppM ``And.right #[c]
    if i + 1 < ms.size then c ← mkAppM ``And.left #[c]
    let pf ← instantiateMVars (mkApp c hphi)
    if pf.hasExprMVar then throwError "len: conc mvar"
    let _ ← inferType pf
    mkLambdaFVars #[k, n, x, y, hk, hphi] pf

end

def lenStarProof (inst : Expr) (pfs : List (Expr × Expr × Expr)) : MetaM Expr := do
  match pfs with
  | [] => mkAppOptM ``HProp.himpl_refl #[inst, mkApp (mkConst ``HProp.hempty) inst]
  | [(_, _, p)] => pure p
  | (a, b, p) :: rest => do
    let q ← lenStarProof inst rest
    mkAppOptM ``HProp.himpl_frame_lr #[inst, a, b, starOf inst (rest.map (·.1)),
      starOf inst (rest.map (·.2.1)), p, q]

partial def lenRhsBody {α : Type} [Inhabited α] (P : LenP) (inst : Expr) (atoms : List Expr)
    (acc : Array Expr) (k : Array Expr → Array Expr → TacticM α) : TacticM α := do
  match atoms with
  | [] => k acc #[]
  | a :: rest =>
    match a.getAppFn.constName? with
    | some q =>
      if q == ``HProp.hpure || q == ``HProp.hsingle || q == ``Sep.segI then
        lenRhsBody P inst rest (acc.push a) k
      else
        let some Q ← lenPOf q | throwError "len: rhs atom"
        withLocalDeclD `rm arIntT fun m => do
          let a' ← mkAppM ``HProp.hstar #[← mkAppOptM ``HProp.hpure #[inst, Q.phiLam.beta #[m]],
            lenSeg P m a.getAppArgs[0]! a.getAppArgs[1]!]
          lenRhsBody P inst rest (acc.push a') fun acc2 ms => k acc2 (#[m] ++ ms)
    | none => throwError "len: rhs atom"

partial def lenRhsGo (P : LenP) (inst : Expr) (r : Expr) : TacticM (Expr × Expr) := do
  if r.isAppOf ``HProp.hexists then
    let lam := r.appArg!
    if lam.isLambda then
      return ← withLocalDeclD lam.bindingName! lam.bindingDomain! fun w => do
        let (r', pf) ← lenRhsGo P inst (lam.bindingBody!.instantiate1 w)
        let lam' ← mkLambdaFVars #[w] r'
        let ex' ← mkAppOptM ``HProp.hexists #[inst, lam.bindingDomain!, lam']
        let pfl ← mkLambdaFVars #[w] (← instantiateMVars pf)
        let pfE ← mkAppOptM ``HProp.himpl_hexists #[inst, lam.bindingDomain!, lam', lam, pfl]
        pure (ex', pfE)
  let Rs0 := flatStar r #[]
  let mut guards : Array Expr := #[]
  for h in Rs0 do
    if h.isAppOf ``HProp.hsingle then
      let addr := h.getAppArgs[1]!
      for g in flatStar ((P.c.beta #[addr, addr]).headBeta) #[] do
        if g.isAppOf ``HProp.hpure then guards := guards.push g
  let Rs := Rs0.filter (fun a => !guards.contains a)
  let mut items : Array Expr := #[]
  let mut tgts : Array Expr := #[]
  for a in Rs do
    if a.isAppOf ``HProp.hsingle then
      let addr := a.getAppArgs[1]!
      let fvs := (Lean.collectFVars {} a.getAppArgs[2]!).fvarIds
      let b ← match fvs[0]? with
        | some f => pure (mkFVar f)
        | none => match a.getAppArgs[2]!.find? (·.isAppOf ``OfNat.ofNat) with
          | some b => pure b
          | none => throwError "len: rhs cell"
      items := items.push (lenSeg P (← arIntLit 1) addr b)
      tgts := tgts.push ((P.c.beta #[addr, b]).headBeta)
    else
      items := items.push a
      tgts := tgts.push a
  lenRhsBody P inst items.toList #[] fun acc ms => do
    let body' := starOf inst acc.toList
    let mut pfs : Array (Expr × Expr × Expr) := #[]
    for (a', tg) in acc.zip tgts do
      if lenIsSeg a' then
        let aa := a'.getAppArgs
        pfs := pfs.push (a', tg, ← lenBeta (← mkAppOptM ``Sep.segI_uncell #[P.inst, P.c, aa[3]!, aa[4]!]))
      else if a'.isAppOf ``HProp.hstar then
        let seg := a'.getAppArgs[2]!
        let sa := seg.getAppArgs
        let some q := tg.getAppFn.constName? | throwError "len: rhs"
        let some Q ← lenPOf q | throwError "len: rhs"
        let some cl ← lenConcOf q | throwError "len: conc"
        let phi := Q.phiLam.beta #[sa[2]!]
        let pf ← withLocalDeclD `hp phi fun hp => do
          let kk ← mkAppM ``Int.toNat #[sa[2]!]
          let hk ← arOmega (← mkAppM ``Eq #[sa[2]!, ← mkAppOptM ``Nat.cast #[arIntT, none, kk]])
          mkLambdaFVars #[hp] (mkAppN cl #[kk, sa[2]!, sa[3]!, sa[4]!, hk, hp])
        pfs := pfs.push (a', tg, ← mkAppOptM ``HProp.himpl_hstar_hpure_l #[inst, phi, seg, tg, pf])
      else
        pfs := pfs.push (a', tg, ← mkAppOptM ``HProp.himpl_refl #[inst, a'])
    let step1 ← lenStarProof inst pfs.toList
    let mid := starOf inst tgts.toList
    let m2 ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[mid, r])
    let saved ← getGoals
    setGoals [m2.mvarId!]
    Sep.Xsimpl.xsimplDriver none
    cleanAll
    arCloseProps
    setGoals saved
    let pfBody ← instantiateMVars (← mkAppM ``HProp.himpl_trans #[step1, m2])
    let ex ← arExists inst ms body'
    let mut pf := pfBody
    for i in [0 : ms.size] do
      let mv := ms[ms.size - 1 - i]!
      pf ← mkAppM ``HProp.himpl_hexists_l #[← mkLambdaFVars #[mv] pf]
    pure (ex, pf)

def lenRhsTransform (P : LenP) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (lhs, rhs) := entailHead? t | throwError "len: goal"
  let inst := t.getAppArgs[0]!
  let (r', pf) ← lenRhsGo P inst rhs
  let ng ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[lhs, r'])
  g.assign (← mkAppM ``HProp.himpl_trans #[ng, pf])
  replaceMainGoal [ng.mvarId!]

partial def lenWalk (atoms : Array Expr) (cur tgt : Expr) (used : Array Nat) (acc : Array Expr)
    (okF : Array Expr → TacticM Bool) : TacticM (Option (Array Expr)) := do
  let cu ← instantiateMVars cur
  let mut order : Array Nat := #[]
  for j in [0 : atoms.size] do
    if (← instantiateMVars atoms[j]!.getAppArgs[3]!) == cu then order := order.push j
  for j in [0 : atoms.size] do
    if !order.contains j then order := order.push j
  for j in order do
    if used.contains j then continue
    let a := atoms[j]!
    let aa := a.getAppArgs
    let s ← saveState
    let hd ← instantiateMVars aa[3]!
    let ok ← if hd == cu then pure true
      else if hd.isMVar then (try checkpointDefEq (isDefEq hd cu) catch _ => pure false)
      else pure false
    if ok then
      if let some r ← lenWalk atoms aa[4]! tgt (used.push j) (acc.push a) okF then return some r
    s.restore
  if acc.isEmpty then return none
  let s ← saveState
  if ← (try checkpointDefEq (isDefEq cur tgt) catch _ => pure false) then
    if used.size == atoms.size then
      let s3 ← saveState
      let good ← okF acc
      s3.restore
      if good then return some acc
  s.restore
  return none

def lenCut (P : LenP) (A : Expr) (lens : Array Expr) : TacticM Unit := do
  let k := lens.size
  let mut cur := A
  for i in [0 : k] do
    let ca := cur.getAppArgs
    if i + 1 == k then
      if ca[2]! != lens[i]! then
        let lem ← withMainContext do
          let h ← arOmega (← mkAppM ``Eq #[ca[2]!, lens[i]!])
          mkAppOptM ``Sep.segI_cong #[P.inst, P.c, ca[2]!, lens[i]!, ca[3]!, ca[4]!, h]
        let _ ← arRwLhs [cur] lem
    else
      let rest ← withMainContext do arSum (lens.extract (i + 1) k).toList
      let lem ← withMainContext do
        let hn ← arOmega (← mkAppM ``Eq #[ca[2]!, ← arAdd lens[i]! rest])
        let ha ← arOmega (← arLe (← arIntLit 0) lens[i]!)
        let hb ← arOmega (← arLe (← arIntLit 0) rest)
        mkAppOptM ``Sep.segI_split #[P.inst, P.c, ca[2]!, lens[i]!, rest, ca[3]!, ca[4]!, hn, ha, hb]
      let vs ← arRwLhs [cur] lem
      let some v := vs[0]? | throwError "len: split"
      cur := lenSeg P rest v ca[4]!

def lenPass : TacticM Unit := do
  let (L, R, hasEx) ← withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    if t.hasExprMVar then throwError "len: mvars"
    let some (lhs, rhs) := entailHead? t | throwError "len: goal"
    let (body, ws) ← arOpen rhs
    let mut ex := false
    for w in ws do
      if ← isDefEq (← inferType w) (mkConst ``Nat) then ex := true
    pure (flatStar lhs #[], flatStar body #[], ex)
  let mut P? : Option LenP := none
  for x in L ++ R do
    match x.getAppFn.constName? with
    | some q =>
      if q == ``HProp.hpure || q == ``HProp.hsingle then continue
      unless x.getAppNumArgs == 2 do throwError "len: atom"
      let some Q ← lenPOf q | throwError "len: no profile"
      if let some P0 := P? then
        unless P0.c == Q.c do throwError "len: cells"
      else P? := some Q
    | none => throwError "len: atom"
  let some P := P? | throwError "len: none"
  unless hasEx do throwError "len: gate"
  lenRhsTransform P
  arIntroFacts
  for x in L do
    match x.getAppFn.constName? with
    | some q =>
      if q == ``HProp.hpure || q == ``HProp.hsingle then continue
      let some lem ← lenAbsOf q | throwError "len: abs"
      let inst ← withMainContext do lenBeta (mkAppN lem x.getAppArgs)
      let _ ← arRwLhs [x] inst
    | none => pure ()
  let _ ← arIntroLhs
  lenCells P
  arIntroFacts
  let some A ← lenJoinAll P | throwError "len: empty"
  let s0 ← saveState
  let lens? ← withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    let some (_, rhs) := entailHead? t | throwError "len: goal"
    let (body, _) ← arOpen rhs
    let Rs := (flatStar body #[]).filter lenIsSeg
    let rp := pureProps body #[]
    let aa := A.getAppArgs
    let mkPc := fun (a : Expr) => ArPiece.mk false a.getAppArgs[2]! 0
    let okF := fun (acc : Array Expr) => do
      return (← arSolve aa[2]! (acc.map mkPc) rp).isSome
    let some acc ← lenWalk Rs aa[3]! aa[4]! #[] #[] okF | return none
    arSolve aa[2]! (acc.map mkPc) rp
  s0.restore
  let some lens := lens? | throwError "len: no plan"
  lenCut P A lens
  arWitness
  Sep.Xsimpl.xsimplDriver none
  cleanAll
  arCloseProps

elab "xsearch_lenabs" : tactic => lenPass

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
  arith : Bool := false
  relLam : Expr
  invLam : Expr
  deriving Inhabited

def wgTupleTy (tys : Array Expr) : MetaM Expr := do
  let mut acc := tys[tys.size - 1]!
  for i in [0 : tys.size - 1] do acc ← mkAppM ``Prod #[tys[tys.size - 2 - i]!, acc]
  return acc

def wgTuple (cs : Array Expr) : MetaM Expr := do
  let mut acc := cs[cs.size - 1]!
  for i in [0 : cs.size - 1] do acc ← mkAppM ``Prod.mk #[cs[cs.size - 2 - i]!, acc]
  return acc

def wgProj (s : Expr) (j n : Nat) : MetaM Expr := do
  if n == 1 then return s
  let mut acc := s
  for _ in [0 : j] do acc ← mkAppM ``Prod.snd #[acc]
  if j + 1 < n then acc ← mkAppM ``Prod.fst #[acc]
  return acc

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

def wgRel? (n a c : Expr) : Option (Int × Int × Bool) :=
  let lf := fun (x y : Expr) => do
    let (x1, y1, c1) ← arLin n a x
    let (x2, y2, c2) ← arLin n a y
    let cn := x1 - x2
    if y1 - y2 == -cn && (cn == 1 || cn == -1) then some (cn, -(c1 - c2)) else none
  match c.getAppFnArgs with
  | (``Eq, #[_, x, y]) => (lf x y).map fun (s, b) => (s, b, true)
  | (``LE.le, #[_, _, x, y]) => (lf x y).map fun (s, b) => (s, b, false)
  | (``LT.lt, #[_, _, x, y]) => (lf x y).map fun (s, b) => (s, b - 1, false)
  | (``GE.ge, #[_, _, x, y]) => (lf y x).map fun (s, b) => (s, b, false)
  | (``GT.gt, #[_, _, x, y]) => (lf y x).map fun (s, b) => (s, b - 1, false)
  | _ => none

def wgParse (p : Name) : MetaM (Option WgP) := do
  let entries := xsearchUnfoldExt.getState (← getEnv)
  let some ent := entries.find? (·.headFn == p) | return none
  let ty := (← getConstInfo ent.lemmaName).type
  forallTelescopeReducing ty fun xs concl => do
    let some (eqT, _, body) := concl.eq? | return none
    let inst := eqT.appArg!
    let brs := lenHorBranches body #[]
    unless brs.size == 2 do return none
    let hasRec := fun (e : Expr) => (e.find? (·.isConstOf p)).isSome
    let si := if hasRec brs[1]! then 1 else 0
    if hasRec brs[1 - si]! || !hasRec brs[si]! then return none
    let tys ← xs.mapM inferType
    peelExG brs[si]! #[] fun us bd => peelExG brs[1 - si]! #[] fun bus bb => do
      let items := flatStar bd #[]
      let bItems := flatStar bb #[]
      let mut bp : Array Expr := #[]
      for it in bItems do
        if let (``HProp.hpure, #[_, pr]) := it.getAppFnArgs then bp := pureConjs pr bp
      let recs := items.filter (·.getAppFn.constName? == some p)
      unless recs.size == 1 do return none
      let rargs := recs[0]!.getAppArgs
      unless rargs.size == xs.size do return none
      let mut cnt : Option (Nat × Nat) := none
      for i in [0 : xs.size] do
        unless ← isDefEq tys[i]! arIntT do continue
        let some ki := us.findIdx? (· == rargs[i]!) | continue
        let onlyI := fun (c : Expr) => (c.find? (· == xs[i]!)).isSome &&
          (c.find? (fun e => e.isFVar && e != xs[i]!)).isNone
        unless bp.any onlyI do continue
        for it in items do
          if let (``HProp.hpure, #[_, pr]) := it.getAppFnArgs then
            for c in pureConjs pr #[] do
              if arStepDec? xs[i]! us[ki]! c == some 1 then cnt := some (i, ki)
      let mov := (Array.range xs.size).filter (fun i => cnt.map (·.1) != some i && rargs[i]! != xs[i]!)
      if mov.isEmpty then return none
      for i in mov do
        unless (← isDefEq tys[i]! (mkConst ``Nat)) || (← isDefEq tys[i]! arIntT) do return none
      let fixd := (Array.range xs.size).filter (fun i => cnt.map (·.1) != some i && !mov.contains i)
      let cvars := match cnt with
        | some (i, k) => #[xs[i]!, us[k]!]
        | none => #[]
      let ment := fun (e : Expr) (vs : Array Expr) => vs.any (fun v => (e.find? (· == v)).isSome)
      let fvs := fixd.map (xs[·]!)
      let mut pre : Array Expr := #[]
      for it in items do
        if it.getAppFn.constName? == some p then continue
        if let (``HProp.hpure, #[_, pr]) := it.getAppFnArgs then
          let cs := pureConjs pr #[]
          for c in cs do
            if ment c fvs && !ment c cvars then
              for v in (xs ++ us).filter (fun v => (c.find? (· == v)).isSome) do
                unless ← isDefEq (← inferType v) arIntT do return none
          let keep := cs.filter (fun c => !ment c cvars && !ment c fvs)
          unless keep.isEmpty do pre := pre.push (← mkAppOptM ``HProp.hpure #[inst, ← datConj keep])
        else
          if ment it cvars || ment it fvs then return none
          pre := pre.push it
      let nm := mov.size
      let movX := mov.map (xs[·]!)
      let sty ← wgTupleTy (mov.map (tys[·]!))
      let usX := match cnt with
        | some (_, k) => us.eraseIdx! k
        | none => us
      let usTys ← usX.mapM inferType
      let preLam ← mkLambdaFVars (movX ++ usX) (starOf inst pre.toList)
      let nextLam ← mkLambdaFVars (movX ++ usX) (← wgTuple (mov.map (rargs[·]!)))
      let one ← arIntLit 1
      let cLam ← withLocalDeclD `s sty fun s => withLocalDeclD `s' sty fun s' =>
        withLocalDeclD `w arIntT fun w => do
          let comps ← (Array.range nm).mapM (wgProj s · nm)
          let comps' ← (Array.range nm).mapM (wgProj s' · nm)
          let sub := fun (e : Expr) => e.replaceFVars movX comps
          let mut eqs : Array Expr := #[]
          for j in [0 : nm] do eqs := eqs.push (← mkAppM ``Eq #[comps'[j]!, sub rargs[mov[j]!]!])
          eqs := eqs.push (← mkAppM ``Eq #[w, one])
          let body := starOf inst ((pre.map sub).toList ++
            [← mkAppOptM ``HProp.hpure #[inst, ← datConj eqs]])
          mkLambdaFVars #[s, s', w] (← arExists inst usX body)
      let mut rels : Array (Nat × Int × Int × Bool) := #[]
      for j in [0 : nm] do
        unless ← isDefEq tys[mov[j]!]! arIntT do continue
        let some ka := usX.findIdx? (· == rargs[mov[j]!]!) | continue
        let a := usX[ka]!
        let n := movX[j]!
        for it in pre do
          if let (``HProp.hpure, #[_, pr]) := it.getAppFnArgs then
            for c in pureConjs pr #[] do
              if (c.find? (fun e => e.isFVar && e != n && e != a)).isSome then continue
              if let some (sg, b, isEq) := wgRel? n a c then rels := rels.push (j, sg, b, isEq)
      let relE := fun (x y : Expr) (sg : Int) (isEq : Bool) (bk : Expr) => do
        let d ← if sg == 1 then arSub x y else arSub y x
        if isEq then mkAppM ``Eq #[d, bk] else arLe d bk
      let relLam ← withLocalDeclD `s sty fun s => withLocalDeclD `s' sty fun s' =>
        withLocalDeclD `w arIntT fun w => do
          let mut cs := #[← mkAppM ``Eq #[w, one]]
          for (j, sg, b, isEq) in rels do
            cs := cs.push (← relE (← wgProj s j nm) (← wgProj s' j nm) sg isEq (← arIntLit b))
          mkLambdaFVars #[s, s', w] (← datConj cs)
      let invLam ← withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `s sty fun s =>
        withLocalDeclD `t sty fun t => withLocalDeclD `n arIntT fun n => do
          let ck ← arCast k
          let mut cs := #[← mkAppM ``Eq #[n, ck]]
          let mut seen : Array Nat := #[]
          for (j, sg, b, isEq) in rels do
            let x ← wgProj s j nm
            let y ← wgProj t j nm
            let bk ← if b == 0 then arIntLit 0 else mkAppM ``HMul.hMul #[← arIntLit b, ck]
            cs := cs.push (← relE x y sg isEq bk)
            unless seen.contains j do
              seen := seen.push j
              cs := cs.push (← mkArrow (← mkAppM ``Eq #[k, mkNatLit 0]) (← mkAppM ``Eq #[x, y]))
          mkLambdaFVars #[k, s, t, n] (← datConj cs)
      let arith := cnt.isSome || (← mov.anyM (fun i => isDefEq tys[i]! arIntT)) || pre.any (fun it =>
        it.isAppOf ``HProp.hpure && (pureConjs it.appArg! #[]).any (fun c => ment c movX && ment c usX))
      let eqPairs := bp.filterMap (fun c => match c.getAppFnArgs with
        | (``Eq, #[_, a, b]) => some (a, b)
        | _ => none)
      let partner := fun (e : Expr) => Id.run do
        for (a, b) in eqPairs do
          if a == e then if let some j := fixd.find? (xs[·]! == b) then return some j
          if b == e then if let some j := fixd.find? (xs[·]! == a) then return some j
        return none
      let lit := fun (e : Expr) => eqPairs.find? (fun (a, b) => (a == e && !b.hasFVar) || (b == e && !a.hasFVar))
        |>.map (fun (a, b) => if a == e then b else a)
      let hsB := bItems.filter (·.isAppOf ``HProp.hsingle)
      let absorbed ← (do
        if !bus.isEmpty then return none
        if hsB.isEmpty then
          let mut spec : Array (Option Nat × Option Expr) := #[]
          for j in mov do
            match partner xs[j]! with
            | some f => spec := spec.push (some f, none)
            | none => spec := spec.push (none, lit xs[j]!)
          return some (spec, 0)
        let canon := fun (e : Expr) => Id.run do
          let mut r := e
          for (a, b) in eqPairs do
            if let some _ := fixd.find? (xs[·]! == a) then
              if mov.any (xs[·]! == b) then r := r.replaceFVar a b
            if let some _ := fixd.find? (xs[·]! == b) then
              if mov.any (xs[·]! == a) then r := r.replaceFVar b a
          return r
        let ms ← usX.mapM (fun u => do mkFreshExprMVar (some (← inferType u)))
        let pat := (flatStar (preLam.beta (movX ++ ms)) #[]).filter (·.isAppOf ``HProp.hsingle)
        unless ← arAssign (hsB.map canon) pat.toList #[] do return none
        let nx ← instantiateMVars (nextLam.beta (movX ++ ms))
        let nxs ← (Array.range nm).mapM fun j => do wgNorm (← wgProj nx j nm)
        let mut spec : Array (Option Nat × Option Expr) := #[]
        for e in nxs do
          if e.hasExprMVar then spec := spec.push (none, none)
          else if let some f := fixd.find? (xs[·]! == e) then spec := spec.push (some f, none)
          else if let some f := partner e then spec := spec.push (some f, none)
          else if !e.hasFVar then spec := spec.push (none, some e)
          else spec := spec.push (none, none)
        return some (spec, 1))
      let covered := fun (spec : Array (Option Nat × Option Expr)) =>
        fixd.all (fun f => spec.any (·.1 == some f))
      let mk := fun (spec : Array (Option Nat × Option Expr)) (kmin : Nat) (tail : Option Expr) =>
        some { pname := p, inst := inst, tys := tys, mov := mov, ai := cnt.map (·.1), sty := sty,
               cLam := cLam, preLam := preLam, nextLam := nextLam, usTys := usTys, endSpec := spec,
               kmin := kmin, stepIdx := si, tailLam := tail, relLam := relLam, invLam := invLam,
               arith := arith : WgP }
      if let some (spec, kmin) := absorbed then
        if covered spec then return mk spec kmin none
      unless cnt.isNone && bus.isEmpty do return none
      let mut spec : Array (Option Nat × Option Expr) := #[]
      let mut used : Array Expr := #[]
      for j in mov do
        let e := xs[j]!
        let hit := bp.find? (fun c => match c.getAppFnArgs with
          | (``Eq, #[_, a, b]) => (a == e && (fvs.contains b || !b.hasFVar)) || (b == e && (fvs.contains a || !a.hasFVar))
          | _ => false)
        match hit with
        | some c =>
          used := used.push c
          let o := if c.getAppArgs[1]! == e then c.getAppArgs[2]! else c.getAppArgs[1]!
          match fixd.find? (xs[·]! == o) with
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
            unless keep.isEmpty do tl := tl.push (← mkAppOptM ``HProp.hpure #[inst, ← datConj keep])
          else tl := tl.push it
        mkLambdaFVars (xs ++ miss) ((starOf inst tl.toList).replaceFVars movX en)
      return mk spec 0 (some tailLam)

initialize wgPCache : IO.Ref (Array (Name × Option WgP)) ← IO.mkRef #[]
initialize wgLCache : IO.Ref (Array (String × Option Expr)) ← IO.mkRef #[]
initialize wgMCache : IO.Ref (Array ((Name × Name) × Option (Array Nat × Bool × Option Expr))) ←
  IO.mkRef #[]

def wgPOf (p : Name) : MetaM (Option WgP) := do
  match (← wgPCache.get).findSome? (fun e => if e.1 == p then some e.2 else none) with
  | some r => return r
  | none =>
    let r ← try wgParse p catch _ => pure none
    wgPCache.modify (·.push (p, r))
    return r

def wgLem (key : String) (build : TacticM Expr) : TacticM (Option Expr) := do
  if let some r := (← wgLCache.get).findSome? (fun e => if e.1 == key then some e.2 else none) then
    return r
  let saved ← getGoals
  let st ← saveState
  let r ← try withLCtx {} {} (do
      let e ← build
      pure (some e)) catch _ => do st.restore; pure none
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

def wgAbsTarget (P : WgP) (xs : Array Expr) : MetaM Expr :=
  withLocalDeclD `k (mkConst ``Nat) fun k =>
  withLocalDeclD `n arIntT fun n =>
  withLocalDeclsD (wgDecls (wgMissTys P) "wm") fun miss => do
    let st ← wgTuple (P.mov.map (xs[·]!))
    let en ← wgTuple (wgEnC P xs miss)
    let hk ← mkAppOptM ``HProp.hpure #[P.inst, ← mkAppM ``LE.le #[mkNatLit P.kmin, k]]
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

partial def wgTupEq (cs ds : Array Expr) : TacticM Expr := withMainContext do
  let eqc := fun (a b : Expr) => do
    if (← instantiateMVars a) == (← instantiateMVars b) then mkEqRefl a
    else arOmega (← mkAppM ``Eq #[a, b])
  if cs.size == 1 then return ← eqc cs[0]! ds[0]!
  let h0 ← eqc cs[0]! ds[0]!
  let hr ← wgTupEq (cs.extract 1 cs.size) (ds.extract 1 ds.size)
  let f ← mkAppOptM ``Prod.mk #[← inferType cs[0]!, ← inferType (← wgTuple (cs.extract 1 cs.size))]
  mkCongr (← mkCongrArg f h0) hr

def wgCongTo (l : Expr) (k n s t : Expr) (nc : Nat) : TacticM Expr := do
  let la := l.getAppArgs
  let k ← instantiateMVars k
  let n ← instantiateMVars n
  let s ← instantiateMVars s
  let t ← instantiateMVars t
  if la[3]! == k && la[4]! == n && la[5]! == s && la[6]! == t then return l
  let tgt := mkAppN l.getAppFn #[la[0]!, la[1]!, la[2]!, k, n, s, t]
  let lem ← withMainContext do
    let hk ← if la[3]! == k then mkEqRefl k else arOmega (← mkAppM ``Eq #[la[3]!, k])
    let hn ← if la[4]! == n then mkEqRefl n else arOmega (← mkAppM ``Eq #[la[4]!, n])
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
  try (do let _ ← arOmega (← mkAppM ``Eq #[a, b]); pure true) catch _ => pure false

def wgUnify (l r : Expr) (nc : Nat) : TacticM Bool := withMainContext do
  let la := l.getAppArgs
  let ra := r.getAppArgs
  unless la[2]! == ra[2]! do return false
  let s ← saveState
  let ok ← (do
    let ls ← wgComps la[5]! nc
    let rs ← wgComps ra[5]! nc
    let le ← wgComps la[6]! nc
    let re ← wgComps ra[6]! nc
    for (a, b) in (ls ++ le).zip (rs ++ re) do
      unless ← wgEqOk a b do return false
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

def wgBuildInv (P : WgP) : TacticM Expr := do
  let hc ← withLocalDeclD `s P.sty fun s => withLocalDeclD `s' P.sty fun s' =>
    withLocalDeclD `w arIntT fun w => do
      let q := P.relLam.beta #[s, s', w]
      let cell := P.cLam.beta #[s, s', w]
      let top ← mkAppM ``HProp.hstar #[← mkAppOptM ``HProp.hpure #[P.inst, q],
        mkApp (mkConst ``HProp.htop) P.inst]
      let m ← arGoal (← mkAppM ``HProp.himpl #[cell, top])
      let _ ← arIntroLhs
      withMainContext do
        let g ← getMainGoal
        let some (lhs, _) := entailHead? (← instantiateMVars (← g.getType)) | throwError "wg: inv"
        g.assign (← mkAppOptM ``himpl_pure_top #[P.inst, q, lhs, ← arOmega q])
      let pf ← instantiateMVars m
      mkLambdaFVars #[s, s', w] (← mkAppOptM ``holdsP_of_top #[P.inst, q, cell, pf])
  let z ← arIntLit 0
  let h0 ← withLocalDeclD `s P.sty fun s => do
    mkLambdaFVars #[s] (← arOmega (P.invLam.beta #[mkNatLit 0, s, s, z]))
  let hs ← withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `s P.sty fun s =>
    withLocalDeclD `s' P.sty fun s' => withLocalDeclD `t P.sty fun t =>
    withLocalDeclD `w arIntT fun w => withLocalDeclD `m arIntT fun m => do
    withLocalDeclD `hr (P.relLam.beta #[s, s', w]) fun hr => do
    withLocalDeclD `hi (P.invLam.beta #[k, s', t, m]) fun hi => do
      let k1 ← mkAppM ``HAdd.hAdd #[k, mkNatLit 1]
      let pf ← arOmega (P.invLam.beta #[k1, s, t, ← arAdd m w])
      mkLambdaFVars #[k, s, s', t, w, m, hr, hi] pf
  withLocalDeclD `k (mkConst ``Nat) fun k => withLocalDeclD `n arIntT fun n =>
  withLocalDeclD `s P.sty fun s => withLocalDeclD `t P.sty fun t => do
    let pf := mkAppN (mkConst ``Sep.wseg_inv) #[P.inst, P.sty, P.cLam, P.relLam, P.invLam, hc, h0,
      hs, k, n, s, t]
    let ty ← mkAppM ``holdsP #[P.invLam.beta #[k, s, t, n], wgSeg P k n s t]
    unless ← isDefEq (← inferType pf) ty do throwError "wg: inv type"
    mkLambdaFVars #[k, n, s, t] (← mkExpectedTypeHint pf ty)

def wgInvOf (P : WgP) : TacticM (Option Expr) := wgLem s!"inv:{P.pname}" (wgBuildInv P)

def wgBuildCI (P : WgP) : TacticM Expr := do
  withLocalDeclsD (wgDecls (wgMovTys P) "cs") fun S => withLocalDeclsD (wgDecls P.usTys "cu") fun us => do
    let pre := P.preLam.beta (S ++ us)
    let st ← wgTuple S
    let nx ← wgNorm (P.nextLam.beta (S ++ us))
    let one ← arIntLit 1
    let tgt := wgSeg P (mkNatLit 1) one st nx
    let cellE ← wgNorm (P.cLam.beta #[st, nx, one])
    let m ← arGoal (← mkAppM ``HProp.himpl #[pre, cellE])
    datMatchClose
    unless (← getUnsolvedGoals).isEmpty do throwError "wg: ci open"
    let pf ← instantiateMVars m
    let cl := mkAppN (mkConst ``Sep.wseg_cell) #[P.inst, P.sty, P.cLam, st, nx, one]
    let full ← mkAppOptM ``HProp.himpl_trans #[P.inst, pre, cellE, tgt, pf, cl]
    mkLambdaFVars (S ++ us) full

def wgCIOf (P : WgP) : TacticM (Option Expr) := wgLem s!"ci:{P.pname}" (wgBuildCI P)

partial def wgAssign (L : Array Expr) (rs : List Expr) (used : Array Nat) :
    MetaM (Option (Array Nat)) := do
  match rs with
  | [] => return some #[]
  | r :: rest =>
    for j in [0 : L.size] do
      if used.contains j then continue
      unless L[j]!.getAppFn == r.getAppFn do continue
      let s ← saveState
      if ← (try checkpointDefEq (isDefEq r L[j]!) catch _ => pure false) then
        if let some js ← wgAssign L rest (used.push j) then return some (#[j] ++ js)
      s.restore
    return none

def wgCellAt (P : WgP) (L : Array Expr) (used : Array Nat) (cur : Option (Array Expr))
    (strict : Bool := true) (first : Option (Nat × Bool) := none) :
    MetaM (Option (Array Expr × Array Expr × Array Nat)) := do
  let s0 ← saveState
  let S ← (wgMovTys P).mapM fun ty => mkFreshExprMVar (some ty)
  if let some c := cur then
    for (a, b) in S.zip c do
      unless ← isDefEq a b do
        s0.restore
        return none
  let us ← P.usTys.mapM fun ty => mkFreshExprMVar (some ty)
  let pat := (flatStar (P.preLam.beta (S ++ us)) #[]).filter (·.isAppOf ``HProp.hsingle)
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

def wgJoinAll (P : WgP) : TacticM Unit := do
  for _ in [0 : 16] do
    let pr ← withMainContext do
      let S := (← wgLhs).filter (fun e => wgIsSeg e && e.getAppArgs[2]! == P.cLam)
      for i in [0 : S.size] do
        for j in [0 : S.size] do
          if i == j then continue
          if S[i]!.getAppArgs[6]! == S[j]!.getAppArgs[5]! then return some (S[i]!, S[j]!)
      return none
    let some (a, b) := pr | return
    let aa := a.getAppArgs
    let ba := b.getAppArgs
    let lem := mkAppN (mkConst ``Sep.wseg_join) #[P.inst, P.sty, P.cLam, aa[3]!, ba[3]!, aa[4]!,
      ba[4]!, aa[5]!, aa[6]!, ba[6]!]
    let _ ← arRwLhs [a, b] lem

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
      let b ← instantiateMVars b
      if b.isMVar then let _ ← isDefEq b a
    let ra ← r.getAppArgs.mapM instantiateMVars
    let h ← wgTupEq (← wgComps ra[5]! nc) (← wgComps ra[6]! nc)
    let hn ← arOmega (← mkAppM ``Eq #[ra[4]!, ← arIntLit 0])
    pure (mkAppN (mkConst ``Sep.wseg_nil) #[P.inst, P.sty, ra[2]!, ra[4]!, ra[5]!, ra[6]!, h, hn])
  let _ ← arRwLhs [] lem

def wgCloseSegs (P : WgP) : TacticM Unit := do
  let ws ← arOpenGoal
  let nc := P.mov.size
  let rs := (← wgRhs).filter wgIsSeg
  for r in rs do
    let ls := (← wgLhs).filter wgIsSeg
    let mut done := false
    for l in ls do
      if ← wgUnify l r nc then
        let ra ← r.getAppArgs.mapM instantiateMVars
        let _ ← wgCongTo l ra[3]! ra[4]! ra[5]! ra[6]! nc
        done := true
        break
    unless done do wgNil P r
  for w in ws do
    if (← instantiateMVars w).hasExprMVar then throwError "wg: witness open"
  Sep.Xsimpl.xsimplDriver none
  cleanAll
  arCloseProps

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
      let nx ← wgComps (← wgNorm (P.nextLam.beta (S ++ us))) P.mov.size
      let ok ← match hen with
        | some e => do pure ((← wgFill S cands) && (← wgUnifySt nx e) && !(← wgOpen (S ++ us)))
        | none => do pure ((← wgFill S cands) && (← wgFill nx cands) && !(← wgOpen (S ++ us)))
      if ok then
        let S ← S.mapM instantiateMVars
        let us ← us.mapM instantiateMVars
        return some (js.map (Ls[·]!), mkAppN CI (S ++ us))
    s0.restore
  return none

def wgCellToSeg (P : WgP) (CI : Expr) (hst hen : Option (Array Expr)) : TacticM (Option Expr) := do
  let some (atoms, lem) ← wgCellMatch P CI hst hen #[] | return none
  let some (_, out) := entailHead? (← withMainContext do instantiateMVars (← inferType lem)) | return none
  let _ ← arRwLhs atoms.toList lem
  return some out

def wgAbsLeaf (P : WgP) (CI : Expr) : TacticM Unit := do
  let _ ← arIntroLhs
  wgSubstAll
  wgNormAll
  for _ in [0 : 4] do
    if (← wgCellToSeg P CI none none).isNone then break
  wgJoinAll P
  wgCloseSegs P

def wgBuildAbs (P : WgP) (CI : Expr) : TacticM Expr := do
  let pty := (← getConstInfo P.pname).type
  forallTelescope pty fun xs _ => do
    let atom := mkAppN (mkConst P.pname) xs
    let tgt ← wgAbsTarget P xs
    let some (F, ta) ← functionalOf? atom | throwError "wg: lfp"
    let aty ← inferType ta
    if aty.isAppOf ``Sum then throwError "wg: mutual"
    let tup := stripInj ta
    let X ← mkXFunN tup #[tgt] 0 aty
    let hX ← indSetup F X aty 1
    let mut leaves : List MVarId := []
    for g in ← getGoals do
      setGoals [g]
      leaves := leaves ++ (← datSplitDisj)
    for g in leaves do
      setGoals [g]
      wgAbsLeaf P CI
    setGoals []
    let key ← instantiateMVars (← mkAppM ``lfpG_induct #[F, X, hX, ta])
    let ty ← mkAppM ``HProp.himpl #[atom, tgt]
    unless ← isDefEq (← inferType key) ty do throwError "wg: abs type"
    let pf ← instantiateMVars (← mkExpectedTypeHint key ty)
    if pf.hasExprMVar then throwError "wg: abs mvar"
    mkLambdaFVars xs pf

def wgAbsOf (P : WgP) : TacticM (Option Expr) := do
  let some CI ← wgCIOf P | return none
  wgLem s!"abs:{P.pname}" (wgBuildAbs P CI)

def wgConcLhs (P : WgP) (k nE : Expr) (xs miss : Array Expr) : MetaM Expr := do
  let seg := wgSeg P k nE (← wgTuple (P.mov.map (xs[·]!))) (← wgTuple (wgEnC P xs miss))
  match P.tailLam with
  | some t => mkAppM ``HProp.hstar #[seg, t.beta (xs ++ miss)]
  | none => pure seg

def wgConcMotive (P : WgP) (k : Expr) : MetaM Expr := do
  withLocalDeclsD (wgDecls P.tys "cx") fun xs =>
  withLocalDeclsD (wgDecls (wgMissTys P) "cm") fun miss =>
  withLocalDeclD `cn arIntT fun n => do
    let nE := match P.ai with
      | some i => xs[i]!
      | none => n
    let hk ← mkAppM ``LE.le #[mkNatLit P.kmin, k]
    let body ← mkArrow hk (← mkAppM ``HProp.himpl #[← wgConcLhs P k nE xs miss,
      mkAppN (mkConst P.pname) xs])
    let vs := if P.ai.isSome then xs ++ miss else xs ++ miss ++ #[n]
    mkForallFVars vs body

def wgUnfoldRhs (P : WgP) (base : Bool) : TacticM Unit := do
  let some a := (← wgRhs).find? (·.isAppOf P.pname) | throwError "wg: rhs pred"
  rewriteOcc (← arEntries) a
  let j := if base then 1 - P.stepIdx else P.stepIdx
  if j == 0 then applyConstT ``hdisj_left else applyConstT ``hdisj_right

def wgLhsSeg (P : WgP) : TacticM Expr := do
  let some a := (← wgLhs).find? (fun e => wgIsSeg e && e.getAppArgs[2]! == P.cLam)
    | throwError "wg: lhs seg"
  return a

def wgConcZeroElim (P : WgP) (atom : Expr) : TacticM Unit := do
  let aa := atom.getAppArgs
  let _ ← arRwLhs [atom] (mkAppN (mkConst ``Sep.wseg_zero_elim) #[P.inst, P.sty, P.cLam, aa[4]!, aa[5]!,
    aa[6]!])
  arIntroFacts
  wgSubstAll
  wgNormAll
  wgUnfoldRhs P true
  datMatchClose

def wgConcIH (P : WgP) (Inv k ih : Expr) (xs miss : Array Expr) : TacticM Unit := do
  wgInvAll P Inv
  let atom ← wgLhsSeg P
  let (lem, tl) ← withMainContext do
    let aa := atom.getAppArgs
    let sc ← wgComps aa[5]! P.mov.size
    let mut xs' := xs
    for j in [0 : P.mov.size] do xs' := xs'.set! P.mov[j]! sc[j]!
    if let some i := P.ai then xs' := xs'.set! i aa[4]!
    let hk' ← arOmega (← mkAppM ``LE.le #[mkNatLit P.kmin, k])
    let extra := if P.ai.isSome then #[] else #[aa[4]!]
    let pf := mkAppN ih (xs' ++ miss ++ extra ++ #[hk'])
    let tl := wgTail P xs' miss
    let ty ← mkAppM ``HProp.himpl #[← wgConcLhs P k aa[4]! xs' miss, mkAppN (mkConst P.pname) xs']
    unless ← isDefEq (← inferType pf) ty do throwError "wg: ih type"
    pure (← mkExpectedTypeHint pf ty, tl)
  let _ ← arRwLhs ([atom] ++ tl.toList) lem
  wgUnfoldRhs P false
  datMatchClose

def wgConcStep (P : WgP) (Inv k ih : Expr) (xs miss : Array Expr) : TacticM Unit := do
  let old ← withMainContext do return (← getLCtx).getFVarIds
  let atom ← wgLhsSeg P
  let aa := atom.getAppArgs
  let vs ← arRwLhs [atom] (mkAppN (mkConst ``Sep.wseg_succ_elim) #[P.inst, P.sty, P.cLam, k, aa[4]!,
    aa[5]!, aa[6]!])
  let _ ← arIntroLhs
  let some s' := vs[0]? | throwError "wg: succ"
  let _ ← wgDestruct s'
  wgNormAll
  let news ← withMainContext do return (← getLCtx).getFVarIds.filter (!old.contains ·)
  wgSubstNew news
  if P.kmin == 0 then
    wgConcIH P Inv k ih xs miss
    return
  let (g1, g2) ← withMainContext do
    let g ← getMainGoal
    let cond ← mkAppM ``LE.le #[mkNatLit P.kmin, k]
    let gt ← g.getType
    let m1 ← mkFreshExprSyntheticOpaqueMVar (← mkArrow cond gt)
    let m2 ← mkFreshExprSyntheticOpaqueMVar (← mkArrow (← mkAppM ``Not #[cond]) gt)
    g.assign (← mkAppOptM ``Classical.byCases #[cond, gt, m1, m2])
    let (_, g1) ← m1.mvarId!.intro1P
    let (_, g2) ← m2.mvarId!.intro1P
    pure (g1, g2)
  setGoals [g1]
  wgConcIH P Inv k ih xs miss
  setGoals [g2]
  let atom ← wgLhsSeg P
  let aa := atom.getAppArgs
  let atom' ← wgCongTo atom (mkNatLit 0) aa[4]! aa[5]! aa[6]! P.mov.size
  wgConcZeroElim P atom'

def wgBuildConc (P : WgP) (Inv : Expr) : TacticM Expr := do
  let motive ← withLocalDeclD `k (mkConst ``Nat) fun k => do mkLambdaFVars #[k] (← wgConcMotive P k)
  let nx := P.tys.size
  let nm := (wgMissTys P).size
  let nv := nx + nm + (if P.ai.isSome then 0 else 1)
  let mb ← arGoal (motive.beta #[mkNatLit 0])
  let (_, gb) ← (← getMainGoal).introNP (nv + 1)
  setGoals [gb]
  if P.kmin ≥ 1 then
    withMainContext do
      let g ← getMainGoal
      let pf ← arOmega (mkConst ``False)
      g.assign (← mkAppOptM ``False.elim #[← g.getType, pf])
  else
    wgConcZeroElim P (← wgLhsSeg P)
  unless (← getUnsolvedGoals).isEmpty do throwError "wg: conc base"
  let base ← instantiateMVars mb
  let sty ← withLocalDeclD `k (mkConst ``Nat) fun k => do
    mkForallFVars #[k] (← mkArrow (motive.beta #[k]) (motive.beta #[← mkAppM ``HAdd.hAdd #[k, mkNatLit 1]]))
  let ms ← arGoal sty
  let (fvs, gs) ← (← getMainGoal).introNP (2 + nv + 1)
  setGoals [gs]
  let xs := (fvs.extract 2 (2 + nx)).map mkFVar
  let miss := (fvs.extract (2 + nx) (2 + nx + nm)).map mkFVar
  wgConcStep P Inv (mkFVar fvs[0]!) (mkFVar fvs[1]!) xs miss
  unless (← getUnsolvedGoals).isEmpty do throwError "wg: conc step"
  let step ← instantiateMVars ms
  withLocalDeclD `k (mkConst ``Nat) fun k => do
    let r ← instantiateMVars (← mkAppOptM ``Nat.rec #[motive, base, step, k])
    if r.hasExprMVar then throwError "wg: conc mvar"
    mkLambdaFVars #[k] r

def wgConcOf (P : WgP) : TacticM (Option Expr) := do
  let some Inv ← wgInvOf P | return none
  wgLem s!"conc:{P.pname}" (wgBuildConc P Inv)

def wgBuildLo (P : WgP) (Abs Inv : Expr) : TacticM Expr := do
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
      g.assign (← mkAppOptM ``himpl_pure_top #[P.inst, q, lhs, ← arOmega q])
    let pf ← instantiateMVars m
    mkLambdaFVars xs (← mkAppOptM ``holdsP_of_top #[P.inst, q, atom, pf])

def wgLoOf (P : WgP) : TacticM (Option Expr) := do
  let some A ← wgAbsOf P | return none
  let some Inv ← wgInvOf P | return none
  wgLem s!"lo:{P.pname}" (wgBuildLo P A Inv)

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
      datMatchClose
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

partial def wgIdxs (nA nB : Nat) : List (Array Nat) :=
  if nB == 0 then [#[]] else
  (wgIdxs nA (nB - 1)).flatMap fun pre =>
    ((List.range nA).filter (fun i => !pre.contains i)).map fun i => pre.push i

def wgMapOf (A B : WgP) : TacticM (Option (Array Nat × Bool × Option Expr)) := do
  if A.cLam == B.cLam then return some (Array.range A.mov.size, false, none)
  let key := (A.pname, B.pname)
  if let some r := (← wgMCache.get).findSome? (fun e => if e.1 == key then some e.2 else none) then
    return r
  let mut res : Option (Array Nat × Bool × Option Expr) := none
  if B.mov.size ≤ A.mov.size then
    for idx in wgIdxs A.mov.size B.mov.size do
      if res.isSome then break
      for rev in [false, true] do
        let saved ← getGoals
        let st ← saveState
        let r ← try withLCtx {} {} (some <$> wgBuildMap A B idx rev) catch _ => do st.restore; pure none
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
  | (``HProp.hstar, #[_, a, b]) =>
    if let some (a', pa) ← wgRepl a A B pf then
      return some (← mkAppM ``HProp.hstar #[a', b],
        ← mkAppM ``HProp.himpl_frame_lr #[pa, ← mkAppM ``HProp.himpl_refl #[b]])
    if let some (b', pb) ← wgRepl b A B pf then
      return some (← mkAppM ``HProp.hstar #[a, b'],
        ← mkAppM ``HProp.himpl_frame_lr #[← mkAppM ``HProp.himpl_refl #[a], pb])
    return none
  | _ => return none

def wgRwRhs (A B pf : Expr) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some (lhs, rhs) := entailHead? t | throwError "wg: goal"
  let some (rhs', p) ← wgRepl rhs A B pf | throwError "wg: rhs atom"
  let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[lhs, rhs'])
  g.assign (← mkAppM ``HProp.himpl_trans #[m, p])
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
    if Q.tailLam.isSome && mp.2.2.isSome then continue
    if (← wgAbsOf Q).isNone then continue
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
      let w ← match Q.ai with
        | some i => pure xs[i]!
        | none => arCast kp
      hyps := hyps.push (← mkAppM ``LE.le #[mkNatLit Q.kmin, kp])
      hyps := hyps.push (← wgNorm (Q.invLam.beta #[kp, ← wgTuple sQ, ← wgTuple eQ, w]))
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
      if ← wgUnifySt segs[i]!.st cur then
        nxt := some (i, segs[i]!)
        break
    match nxt with
    | some (i, pc) =>
      usedS := usedS.push i
      out := out.push pc
      cur := pc.en
    | none =>
      let some (S, us, js) ← wgCellAt P Lc usedC (some cur) false | break
      let nx ← wgComps (← wgNorm (P.nextLam.beta (S ++ us))) P.mov.size
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

partial def wgWalkR (P : WgP) (R ws : Array Expr) (cur tgt : Array Expr) (usedR : Array Nat)
    (acc : Array WgPc) (fuel : Nat) (okEnd : Array WgPc → TacticM Bool) :
    TacticM (Option (Array WgPc)) := do
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
            let nx ← wgComps (← wgNorm (P.nextLam.beta (S ++ us))) P.mov.size
            let pc : WgPc := { cell := true, en := nx, len := one, lo := 1 }
            if let some res ← wgWalkR P R ws nx tgt (usedR ++ js) (acc.push pc) (fuel - 1) okEnd then
              return some res
        wgBack s
        continue
      let some q := r.getAppFn.constName? | continue
      let some Q ← wgPOf q | continue
      unless r.getAppNumArgs == Q.tys.size do continue
      let some mp ← wgMapOf P Q | continue
      if Q.tailLam.isSome && mp.2.2.isSome then continue
      if (← wgConcOf Q).isNone then continue
      let xs ← r.getAppArgs.mapM instantiateMVars
      let sQ := Q.mov.map (xs[·]!)
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
      if (← wgUnifySt st cur) && !(← wgMerged ws) then
        let len ← match Q.ai with
          | some i => pure xs[i]!
          | none => mkFreshExprMVar (some arIntT)
        let pc : WgPc := { cell := false, pred := q, idx := some j, en := en, len := len, lo := Q.kmin }
        let tl := (wgTail Q xs miss).filter (·.isAppOf ``HProp.hsingle)
        let nxt ← if tl.isEmpty then pure (some (en, #[pc])) else do
          match ← wgCellAt P tl #[] (some en) false (some (0, false)) with
          | some (S, us, js) =>
            if js.size == tl.size then
              let nx ← wgComps (← wgNorm (P.nextLam.beta (S ++ us))) P.mov.size
              pure (some (nx, #[pc, { cell := true, en := nx, len := one, lo := 1 }]))
            else pure none
          | none => pure none
        if let some (nx, pcs) := nxt then
          if let some res ← wgWalkR P R ws nx tgt (usedR.push j) (acc ++ pcs) (fuel - 1) okEnd then
            return some res
      wgBack s
  if !acc.isEmpty then
    let s ← saveState
    if ← wgUnifySt cur tgt then
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

def wgPlanFor (P : WgP) : TacticM (Array WgPlan) := withMainContext do
  let t ← instantiateMVars (← (← getMainGoal).getType)
  let some (lhs, rhs) := entailHead? t | return #[]
  let L := (flatStar lhs #[]).filter (!·.isAppOf ``HProp.hpure)
  wgLhsPieces P L fun segs tails => do
    let Lc := L ++ tails
    let (body, ws) ← arOpen rhs
    let R := flatStar body #[]
    let rpures := pureProps body #[]
    let mut starts : Array (Array Expr) := segs.map (·.st)
    for x in Lc do
      if x.isAppOf ``HProp.hsingle then
        let s ← saveState
        if let some (S, _, _) ← wgCellAt P (#[x] ++ Lc.erase x) #[] none false (some (0, false)) then
          let S ← S.mapM instantiateMVars
          if !S.any (·.hasExprMVar) && !starts.any (· == S) then starts := starts.push S
        wgBack s
    let isEnd := fun (s : Array Expr) => segs.any (·.en == s)
    starts := starts.filter (!isEnd ·) ++ starts.filter isEnd
    let mut out : Array WgPlan := #[]
    for s0 in starts do
      let s1 ← saveState
      let lp ← wgWalkL P Lc segs s0
      for j in [1 : lp.size + 1] do
        let lpj := lp.extract 0 j
        let s2 ← saveState
        let okEnd := fun (rpc : Array WgPc) => do
          let (l, r) := wgTrim lpj rpc
          if l.isEmpty || r.isEmpty then return false
          unless ← wgUnifySt l.back!.en r.back!.en do return false
          let nontriv := l.size ≥ 2 || r.size ≥ 2 ||
            (!l[0]!.cell && !r[0]!.cell && l[0]!.pred != r[0]!.pred) || l[0]!.cell != r[0]!.cell
          if !nontriv then return false
          let n0 ← arSum (l.map (·.len)).toList
          let aps := r.map fun pc => ({ cell := pc.cell, len := pc.len, lo := pc.lo } : ArPiece)
          return (← arSolve n0 aps rpures).isSome
        if let some rpc ← wgWalkR P R ws s0 lpj[j - 1]!.en #[] #[] (R.size + 2) okEnd then
          let (l, r) := wgTrim lpj rpc
          let rl ← r.mapM fun pc => instantiateMVars pc.len
          let l ← l.mapM fun pc => do
            return { pc with st := ← pc.st.mapM instantiateMVars, en := ← pc.en.mapM instantiateMVars }
          let bad := rl.any (·.hasExprMVar) ||
            l.any (fun pc => pc.cell && (pc.st ++ pc.en).any (·.hasExprMVar))
          wgBack s2
          unless bad do
            out := out.push { car := P, lp := l, rp := r, rl := rl }
            if out.size ≥ 6 then return out
        else
          wgBack s2
      wgBack s1
    return out

def wgToNat (l : Expr) : MetaM Expr := do
  if let some v ← getIntValue? l then
    if v ≥ 0 then return mkNatLit v.toNat
  mkAppM ``Int.toNat #[l]

def wgExec (pl : WgPlan) : TacticM (Array Expr) := do
  let P := pl.car
  let nc := P.mov.size
  let some Inv ← wgInvOf P | throwError "wg: inv"
  let some CI ← wgCIOf P | throwError "wg: ci"
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
  let sub := fun (e : Expr) => e.replaceFVars phs acts
  let mut parts : Array (Array Expr × Expr × Expr) := #[]
  let mut usedA : Array Expr := #[]
  for i in [0 : pl.lp.size] do
    let pc := pl.lp[i]!
    if pc.cell then
      let some (as, lem) ← wgCellMatch P CI (some (pc.st.map sub)) (some (pc.en.map sub)) usedA
        | throwError "wg: cell"
      let some (_, out) := entailHead? (← withMainContext do instantiateMVars (← inferType lem))
        | throwError "wg: cell"
      usedA := usedA ++ as
      parts := parts.push (as, lem, out)
    else
      let a := segAtoms[i]!
      wgInvFact P Inv a
      parts := parts.push (#[a], ← withMainContext do mkAppM ``HProp.himpl_refl #[a], a)
  let (allA, chain, accJ) ← withMainContext do
    let (a0, p0, j0) := parts[parts.size - 1]!
    let mut as := a0
    let mut pf := p0
    let mut J := j0
    for i' in [0 : parts.size - 1] do
      let (ai, pi, oi) := parts[parts.size - 2 - i']!
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
  if parts.size ≥ 2 || pl.lp[0]!.cell then
    let _ ← arRwLhs allA.toList chain
  let mut acc := accJ
  let m := pl.rp.size
  let mut pieces : Array Expr := #[]
  let mut news : Array FVarId := #[]
  if m == 1 then pieces := #[acc] else
    let (ks, sums) ← withMainContext do
      let ks ← (Array.range m).mapM fun i => do
        if pl.rp[i]!.cell then pure (mkNatLit 1) else wgToNat (sub pl.rl[i]!)
      let mut sums : Array Expr := Array.replicate m (mkNatLit 0)
      sums := sums.set! (m - 1) ks[m - 1]!
      for i' in [0 : m - 1] do
        let i := m - 2 - i'
        sums := sums.set! i (← mkAppM ``HAdd.hAdd #[ks[i]!, sums[i + 1]!])
      pure (ks, sums)
    let aa := acc.getAppArgs
    acc ← wgCongTo acc sums[0]! aa[4]! aa[5]! aa[6]! nc
    for i in [0 : m - 1] do
      let ca := acc.getAppArgs
      let lem := mkAppN (mkConst ``Sep.wseg_split) #[P.inst, P.sty, P.cLam, ks[i]!, sums[i + 1]!,
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
      pieces := pieces.push pa
      acc := na
    pieces := pieces.push acc
  for x in pieces do wgInvFact P Inv x
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
  let mut rsegs : Array Expr := #[]
  for pc in pl.rp do
    let some j := pc.idx | continue
    let r ← instantiateMVars R[j]!
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
      let hkT ← mkAppM ``LE.le #[mkNatLit Q.kmin, kM]
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
      rsegs := rsegs.push seg2
    else
      rsegs := rsegs.push segQ
  for r in rsegs do
    let ls := (← wgLhs).filter (fun e => wgIsSeg e && e.getAppArgs[2]! == P.cLam)
    let mut done := false
    for l in ls do
      if ← wgUnify l r nc then
        let ra ← r.getAppArgs.mapM instantiateMVars
        let _ ← wgCongTo l ra[3]! ra[4]! ra[5]! ra[6]! nc
        done := true
        break
    unless done do throwError "wg: rhs seg"
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
  Sep.Xsimpl.xsimplDriver none
  cleanAll
  arCloseProps
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

def wgPass : TacticM Unit := do
  let (L, R) ← withMainContext do
    let t ← instantiateMVars (← (← getMainGoal).getType)
    if t.hasExprMVar then throwError "wg: mvars"
    let some (lhs, rhs) := entailHead? t | throwError "wg: not an entailment"
    let (body, _) ← arOpen rhs
    pure (flatStar lhs #[], flatStar body #[])
  let mut cands : Array WgP := #[]
  for x in L ++ R do
    if let some p := x.getAppFn.constName? then
      if let some P ← wgPOf p then
        if !cands.any (·.cLam == P.cLam) then cands := cands.push P
  unless cands.any (·.arith) do throwError "wg: no predicate"
  arIntroFacts
  wgLowFacts
  let s ← saveState
  for P in cands do
    if ← pastGlobal then break
    let pls ← try wgPlanFor P catch _ => pure #[]
    wgBack s
    for pl in pls do
      if ← pastGlobal then break
      let ok ← try (do
          let ws ← wgExec pl
          wgFinish ws
          pure true) catch _ => pure false
      if ok then return
      wgBack s
  throwError "wg: no plan"

elab "xsearch_wseg" : tactic => wgPass

elab "xsearch_snefacts" : tactic => withMainContext do
  snefactsCore

elab "xsearch_qfacts" : tactic => withMainContext do
  farImpCore

elab "xsearch_dblalloc" : tactic => withMainContext do
  dblAllocCore

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
  indCache.set #[]
  segLemCache.set #[]
  segLazyCache.set #[]
  failMemo.set {}
  allocNeCache.set #[]
  srcNeCache.set #[]
  farImpCache.set #[]
  convCache.set #[]
  compSpecCache.set #[]
  indSpent.set 0
  composeAltSpent.set 0
  witnessMissed.set false
  forcedDepth.set 0
  composeDepth.set 0
  subTopFuel.set 0
  permCache.set #[]
  snocNilCache.set #[]
  snocKCache.set #[]
  parCache.set #[]
  invCache.set #[]
  selfAllocCache.set #[]
  cmPending.set false
  bkAllocCache.set #[]
  descCache.set #[]
  flatPredCache.set #[]
  groupCache.set #[]
  invDCache.set #[]
  minCellCache.set #[]
  parDCache.set #[]
  recPredCache.set #[]
  snocDCache.set #[]
  lenPCache.set #[]
  lenAbsCache.set #[]
  wgPCache.set #[]
  wgLCache.set #[]
  wgMCache.set #[]
  lenConcCache.set #[]

elab "xsearch_backtrack" : tactic => do
  let reset : Nat → TacticM Unit := fun tries => do
    searchDeadline.set (← globalDeadline.get)
    searchNodes.set 20000
    composeChanged.set false
    composeTries.set tries
  reset 16
  let st ← saveState
  let gs ← getGoals
  let ok1 ← try composePass true 16 catch _ => pure false
  unless ok1 do
    st.restore
    setGoals gs
    reset 16
    let ok2 ←
      if ← witnessMissed.get then do
        let _ ← tryTactic (evalTactic (← `(tactic| xsearch_snefacts)))
        let _ ← tryTactic (evalTactic (← `(tactic| xsearch_qfacts)))
        let st2 ← saveState
        let gs2 ← getGoals
        reset 64
        let r ← try composePass true 16 catch _ => pure false
        unless r do
          st2.restore
          setGoals gs2
        pure r
      else pure false
    unless ok2 do
      st.restore
      setGoals gs
      reset 48
  searchSolve 40

partial def rootCombos (cs : List (Array Expr)) (acc : Array Expr) (out : Array (Array Expr))
    (cap : Nat) : Array (Array Expr) :=
  if out.size ≥ cap then out else
  match cs with
  | [] => out.push acc
  | c :: rest => c.foldl (fun o v => rootCombos rest (acc.push v) o cap) out

def rootInst (vals : Array Expr) : TacticM Unit := do
  for v in vals do
    withMainContext do
    let g ← getMainGoal
    let t ← instantiateMVars (← g.getType)
    let some (lhs, rhs) := entailHead? t | throwError "root: goal"
    unless rhs.isAppOf ``HProp.hexists do throwError "root: binder"
    let lam := rhs.appArg!
    let inst := t.getAppArgs[0]!
    let body := (lam.bindingBody!.instantiate1 v)
    let m ← g.withContext do mkFreshExprSyntheticOpaqueMVar (← mkAppM ``HProp.himpl #[lhs, body])
    g.assign (← mkAppOptM ``HProp.himpl_hexists_r #[inst, lam.bindingDomain!, v, lhs, lam, m])
    replaceMainGoal [m.mvarId!]

elab "xsearch_rootwit" : tactic => do
  let cands ← withMainContext do
    let s ← saveState
    let t ← instantiateMVars (← (← getMainGoal).getType)
    if t.hasExprMVar then throwError "root: mvars"
    let some (lhs, rhs) := entailHead? t | throwError "root: goal"
    let (body, ms) ← arOpen rhs
    if ms.isEmpty then throwError "root: no binder"
    let entries := xsearchUnfoldExt.getState (← getEnv)
    let heads := entries.map (·.headFn)
    let isPred := fun (e : Expr) => match e.getAppFn.constName? with
      | some n => heads.contains n
      | none => false
    let Rs := (flatStar body #[]).filter (!·.isAppOf ``HProp.hpure)
    let Ls := (flatStar lhs #[]).filter (!·.isAppOf ``HProp.hpure)
    unless Rs.all isPred && !Ls.isEmpty && Ls.all isPred do throwError "root: shape"
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
    let mut out : Array (Array Expr) := #[]
    for m in ms do
      unless ← isDefEq (← inferType m) (mkConst ``Nat) do throwError "root: type"
      let atRoot := Rs.any (fun r => r.getAppArgs[0]? == some m)
      unless Rs.any (fun r => r.getAppArgs.contains m) do throwError "root: unused"
      let base := if atRoot then roots ++ holes ++ #[nil] else holes ++ #[nil] ++ roots
      let mut c : Array Expr := #[]
      for v in base do
        if !c.contains v && c.size < 5 then c := c.push v
      out := out.push c
    s.restore
    pure out
  let combos := rootCombos cands.toList #[] #[] 40
  let gd ← globalDeadline.get
  let saved ← getGoals
  for combo in combos do
    if (← vclock) + 300 > gd then break
    let s ← saveState
    let ok ← try (do
        rootInst combo
        if ← goalRefuted then throwError "root: refuted"
        globalDeadline.set (min gd ((← vclock) + 900))
        evalTactic (← `(tactic| xsearch_backtrack))
        unless (← getUnsolvedGoals).isEmpty do throwError "root: open"
        pure true) catch _ => pure false
    globalDeadline.set gd
    if ok then return
    s.restore
    setGoals saved
  throwError "root: no witness"

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
         try xsearch_bkfacts
         try xsearch_dblalloc
         first
         | (xsearch_wseg
            first
            | done
            | xsearch_backtrack)
         | (xsearch_lenabs
            first
            | done
            | xsearch_backtrack)
         | xsearch_rootwit
         | xsearch_backtrack)))

-- # EVOLVE-BLOCK-END

end Sep.Xsearch
