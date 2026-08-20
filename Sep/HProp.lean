import Sep.FmapTactics
open Lean

class Params where
  val : Type

variable [Params]

abbrev val : Type := Params.val
abbrev Loc : Type := Nat
abbrev null : Loc := 0

abbrev Heap : Type := Finmap fun _ : Loc => val
def Heap.empty : Heap := ∅

def HProp : Type := Heap → Prop

namespace HProp

/-- Heap entailment -/
def himpl (H1 H2 : HProp) : Prop :=
  ∀ h, H1 h → H2 h

def qimpl {A : Sort _} (Q1 Q2 : A → HProp) : Prop :=
  ∀ v, himpl (Q1 v) (Q2 v)

def hempty : HProp :=
  fun h => h = ∅

def hsingle (p : Loc) (v : val) : HProp :=
  fun h => h = Finmap.singleton p v

def hstar (H1 H2 : HProp) : HProp :=
  fun h => ∃ h1 h2, H1 h1 ∧ H2 h2 ∧ Finmap.Disjoint h1 h2 ∧ h = h1 ∪ h2

def hexists {A : Sort _} (J : A → HProp) : HProp :=
  fun h => ∃ x, J x h

def hforall {A : Sort _} (J : A → HProp) : HProp :=
  fun h => ∀ x, J x h

def hpure (P : Prop) : HProp :=
  hexists (A := P) (fun _ => hempty)

def htop : HProp :=
  fun _ => True

-- https://softwarefoundations.cis.upenn.edu/slf-current/LibSepReference.html#SepSimplArgs.hwand
def hwand (H1 H2 : HProp) : HProp :=
  hexists (fun H0 : HProp =>
    hstar H0 (hpure (himpl (hstar H1 H0) H2)))

def qwand {A : Sort _} (Q1 Q2 : A → HProp) : HProp :=
  hforall (fun x => hwand (Q1 x) (Q2 x))

/-- Septraction, aka separating subtraction, the existential dual of `hwand`. The heap `h` satisfying `H1 -⊛ H2` can be extended by some disjoint `h1` satisfying `H1` so that the combined heap satisfies `H2`. -/
def hsept (H1 H2 : HProp) : HProp :=
  fun h => ∃ h1, H1 h1 ∧ Finmap.Disjoint h h1 ∧ H2 (h ∪ h1)

/-- Heap-pointwise conjunction -/
def hand (H1 H2 : HProp) : HProp :=
  fun h => H1 h ∧ H2 h

/-- `H` is precise if it determines its heap uniquely. -/
def Precise (H : HProp) : Prop :=
  ∀ h1 h2, H h1 → H h2 → h1 = h2

/-- `H` is satisfiable / inhabited: it has at least one witness heap. -/
def Sat (H : HProp) : Prop := ∃ p, H p

/-- This is a meta-assertion, returning Prop. It universally quantifies over all satisfying heaps, whereas separating conjunction is existential -/
def Separated (H1 H2 : HProp) : Prop :=
  ∀ p q, H1 p → H2 q → Finmap.Disjoint p q

class IsSeparated (H1 H2 : HProp) : Prop where
  sep : Separated H1 H2

namespace Notation

@[inherit_doc] scoped infixr:25 " ==> " => himpl
scoped infixr:25 " ==>+ " => qimpl

scoped notation:max "emp" => hempty
scoped notation "⌈" P "⌉" => hpure P
-- scoped notation "\\Top" => htop

scoped infixr:61 " ✶ " => hstar
scoped notation Q " ✶+ " H => fun x => hstar (Q x) H
scoped infixr:63 " -✶ " => hwand
scoped infixr:63 " -✶+ " => qwand
scoped notation p:70 " ↦ " v:71 => hsingle p v

@[inherit_doc] scoped infixr:63 " -⊛ " => hsept

@[inherit_doc] scoped infixr:62 " ⊓ " => hand

syntax:max (name := heapExists) "∃✶ " explicitBinders ", " term : term
syntax:max (name := heapForall) "∀✶ " explicitBinders ", " term : term

macro_rules
  | `(heapExists| ∃✶ $xs:explicitBinders, $b:term) =>
      expandExplicitBinders ``hexists xs b
  | `(heapForall| ∀✶ $xs:explicitBinders, $b:term) =>
      expandExplicitBinders ``hforall xs b

@[app_unexpander hexists] def unexpandHexists : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => $body) => `(∃✶ $x:ident, $body)
  | `($(_) fun ($x:ident : $_) => $body) => `(∃✶ $x:ident, $body)
  | _ => throw ()

@[app_unexpander hforall] def unexpandHforall : Lean.PrettyPrinter.Unexpander
  | `($(_) fun $x:ident => $body) => `(∀✶ $x:ident, $body)
  | `($(_) fun ($x:ident : $_) => $body) => `(∀✶ $x:ident, $body)
  | _ => throw ()

end Notation

open Notation

theorem himpl_refl (H : HProp) : H ==> H := by
  intro _ h
  exact h

theorem himpl_trans {H1 H2 H3 : HProp} :
    (H1 ==> H2) → (H2 ==> H3) → (H1 ==> H3) := by
  intro h12 h23 h hh
  exact h23 h (h12 h hh)

theorem himpl_trans_r {H1 H2 H3 : HProp} :
    (H2 ==> H3) → (H1 ==> H2) → (H1 ==> H3) := by
  intro h23 h12
  exact himpl_trans h12 h23

theorem himpl_antisym {H1 H2 : HProp} :
    (H1 ==> H2) → (H2 ==> H1) → H1 = H2 := by
  intro h12 h21
  funext h
  exact propext ⟨h12 h, h21 h⟩

theorem hprop_op_comm (op : HProp → HProp → HProp) :
    (∀ H1 H2, op H1 H2 ==> op H2 H1) →
      ∀ H1 H2, op H1 H2 = op H2 H1 := by
  intro hop H1 H2
  exact himpl_antisym (hop H1 H2) (hop H2 H1)

theorem qimpl_refl {A : Sort _} (Q : A → HProp) : Q ==>+ Q := by
  intro _
  exact himpl_refl _

theorem hempty_intro : (emp : HProp) ∅ := by
  rfl

theorem hempty_elim {h : Heap} : (emp : HProp) h → h = ∅ := by
  intro hh
  exact hh

theorem hstar_intro {H1 H2 : HProp} {h1 h2 : Heap} :
    H1 h1 → H2 h2 → Finmap.Disjoint h1 h2 → (H1 ✶ H2) (h1 ∪ h2) := by
  intro hh1 hh2 hd
  exact ⟨h1, h2, hh1, hh2, hd, rfl⟩

theorem hstar_elim {H1 H2 : HProp} {h : Heap} :
    (H1 ✶ H2) h →
      ∃ h1 h2, H1 h1 ∧ H2 h2 ∧ Finmap.Disjoint h1 h2 ∧ h = h1 ∪ h2 := by
  intro hh
  exact hh

theorem hstar_comm (H1 H2 : HProp) :
    H1 ✶ H2 = H2 ✶ H1 := by
  funext h
  apply propext
  constructor
  · intro hh
    rcases hh with ⟨h1, h2, hh1, hh2, hd, hu⟩
    refine ⟨h2, h1, hh2, hh1, hd.symm, ?_⟩
    rw [hu]
    exact Finmap.union_comm_of_disjoint hd
  · intro hh
    rcases hh with ⟨h2, h1, hh2, hh1, hd, hu⟩
    refine ⟨h1, h2, hh1, hh2, hd.symm, ?_⟩
    rw [hu]
    exact Finmap.union_comm_of_disjoint hd

theorem hstar_assoc (H1 H2 H3 : HProp) :
    (H1 ✶ H2) ✶ H3 = H1 ✶ (H2 ✶ H3) := by
  funext h
  apply propext
  constructor
  · intro hh
    rcases hh with ⟨h12, h3, hh12, hh3, hd123, hu123⟩
    rcases hh12 with ⟨h1, h2, hh1, hh2, hd12, hu12⟩
    subst hu12
    exact ⟨h1, h2 ∪ h3, hh1, ⟨h2, h3, hh2, hh3, by fmap_disjoint, rfl⟩,
      by fmap_disjoint, by fmap_eq⟩
  · intro hh
    rcases hh with ⟨h1, h23, hh1, hh23, hd123, hu123⟩
    rcases hh23 with ⟨h2, h3, hh2, hh3, hd23, hu23⟩
    subst hu23
    exact ⟨h1 ∪ h2, h3, ⟨h1, h2, hh1, hh2, by fmap_disjoint, rfl⟩, hh3,
      by fmap_disjoint, by fmap_eq⟩

instance : Std.Associative hstar := ⟨hstar_assoc⟩
instance : Std.Commutative hstar := ⟨hstar_comm⟩

theorem hstar_hempty_l (H : HProp) :
    emp ✶ H = H := by
  funext h
  apply propext
  constructor
  · intro hh
    rcases hh with ⟨h1, h2, hh1, hh2, _, hu⟩
    have he : h1 = ∅ := hh1
    subst h1
    rw [Finmap.empty_union] at hu
    simpa [hu] using hh2
  · intro hh
    refine ⟨∅, h, hempty_intro, hh, Finmap.disjoint_empty _, ?_⟩
    exact Finmap.empty_union.symm

theorem hstar_hempty_r (H : HProp) :
    H ✶ emp = H := by
  rw [hstar_comm, hstar_hempty_l]

theorem hstar_hexists {A : Sort _} (J : A → HProp) (H : HProp) :
    (hexists J) ✶ H = ∃✶ x, J x ✶ H := by
  funext h
  apply propext
  constructor
  · intro hh
    rcases hh with ⟨h1, h2, ⟨x, hx⟩, hH, hd, hu⟩
    exact ⟨x, h1, h2, hx, hH, hd, hu⟩
  · intro hh
    rcases hh with ⟨x, h1, h2, hx, hH, hd, hu⟩
    exact ⟨h1, h2, ⟨x, hx⟩, hH, hd, hu⟩

theorem hstar_hforall {A : Sort _} (H : HProp) (J : A → HProp) :
    (hforall J) ✶ H ==> ∀✶ x, J x ✶ H := by
  intro h hh x
  rcases hh with ⟨h1, h2, hJ, hH, hd, hu⟩
  exact ⟨h1, h2, hJ x, hH, hd, hu⟩

theorem himpl_frame_l {H1 H2 H3 : HProp} :
    (H1 ==> H2) → (H1 ✶ H3 ==> H2 ✶ H3) := by
  intro hi h hh
  rcases hh with ⟨h1, h2, hh1, hh2, hd, hu⟩
  exact ⟨h1, h2, hi h1 hh1, hh2, hd, hu⟩

theorem himpl_frame_r {H1 H2 H3 : HProp} :
    (H2 ==> H3) → (H1 ✶ H2 ==> H1 ✶ H3) := by
  intro hi h hh
  rcases hh with ⟨h1, h2, hh1, hh2, hd, hu⟩
  exact ⟨h1, h2, hh1, hi h2 hh2, hd, hu⟩

theorem himpl_frame_lr {H1 H2 H3 H4 : HProp} :
    (H1 ==> H2) → (H3 ==> H4) → (H1 ✶ H3 ==> H2 ✶ H4) := by
  intro h12 h34
  exact himpl_trans (himpl_frame_l h12) (himpl_frame_r h34)

theorem himpl_hstar_trans_l {H1 H2 H3 H4 : HProp} :
    (H1 ==> H2) → (H2 ✶ H3 ==> H4) → (H1 ✶ H3 ==> H4) := by
  intro h12 h234
  exact himpl_trans (himpl_frame_l h12) h234

theorem himpl_hstar_trans_r {H1 H2 H3 H4 : HProp} :
    (H1 ==> H2) → (H3 ✶ H2 ==> H4) → (H3 ✶ H1 ==> H4) := by
  intro h12 h324
  exact himpl_trans (himpl_frame_r h12) h324

theorem hexists_intro {A : Sort _} (x : A) (J : A → HProp) {h : Heap} :
    J x h → (∃✶ y, J y) h := by
  intro hx
  exact ⟨x, hx⟩

theorem hexists_elim {A : Sort _} {J : A → HProp} {h : Heap} :
    (∃✶ x, J x) h → ∃ x, J x h := by
  intro hx
  exact hx

theorem hpure_intro (P : Prop) (hP : P) : ⌈P⌉ ∅ := by
  exact ⟨hP, rfl⟩

theorem hpure_elim {P : Prop} {h : Heap} :
    ⌈P⌉ h → P ∧ h = ∅ := by
  intro hp
  rcases hp with ⟨hP, hh⟩
  exact ⟨hP, hh⟩

theorem hstar_hpure_l (P : Prop) (H : HProp) (h : Heap) :
    (⌈P⌉ ✶ H) h ↔ P ∧ H h := by
  constructor
  · intro hh
    rcases hh with ⟨h1, h2, hp, hH, _, hu⟩
    rcases hpure_elim hp with ⟨hP, he⟩
    subst h1
    rw [Finmap.empty_union] at hu
    exact ⟨hP, hu ▸ hH⟩
  · intro hh
    rcases hh with ⟨hP, hH⟩
    refine ⟨∅, h, hpure_intro P hP, hH, Finmap.disjoint_empty _, ?_⟩
    exact Finmap.empty_union.symm

theorem hstar_hpure_r (P : Prop) (H : HProp) (h : Heap) :
    (H ✶ ⌈P⌉) h ↔ H h ∧ P := by
  rw [hstar_comm, hstar_hpure_l]
  constructor
  · intro hh
    exact ⟨hh.2, hh.1⟩
  · intro hh
    exact ⟨hh.2, hh.1⟩

theorem himpl_hstar_hpure_r {P : Prop} {H1 H2 : HProp} :
    P → (H1 ==> H2) → (H1 ==> ⌈P⌉ ✶ H2) := by
  intro hP hH h hh
  exact (hstar_hpure_l P H2 h).2 ⟨hP, hH h hh⟩

theorem hpure_elim_hempty {P : Prop} {h : Heap} :
    ⌈P⌉ h → P ∧ emp h := by
  intro hp
  rcases hpure_elim hp with ⟨hP, hh⟩
  exact ⟨hP, hh⟩

theorem hpure_intro_hempty {P : Prop} {h : Heap} :
    emp h → P → ⌈P⌉ h := by
  intro hh hP
  exact hh ▸ hpure_intro P hP

theorem himpl_hempty_hpure {P : Prop} :
    P → (emp ==> ⌈P⌉) := by
  intro hP h hh
  exact hpure_intro_hempty hh hP

theorem himpl_hstar_hpure_l {P : Prop} {H1 H2 : HProp} :
    (P → (H1 ==> H2)) → (⌈P⌉ ✶ H1 ==> H2) := by
  intro hPH h hh
  rcases (hstar_hpure_l P H1 h).1 hh with ⟨hP, hH⟩
  exact hPH hP h hH

theorem hempty_eq_hpure_true :
    (emp : HProp) = ⌈True⌉ := by
  apply himpl_antisym
  · exact himpl_hempty_hpure True.intro
  · intro h hh
    exact (hpure_elim_hempty hh).2

theorem hfalse_hstar_any (H : HProp) :
    ⌈False⌉ ✶ H = ⌈False⌉ := by
  apply himpl_antisym
  · intro h hh
    exact False.elim ((hstar_hpure_l False H h).1 hh).1
  · intro h hh
    rcases hpure_elim_hempty hh with ⟨hF, _⟩
    exact False.elim hF

theorem himpl_hexists_l {A : Sort _} {H : HProp} {J : A → HProp} :
    (∀ x, J x ==> H) → ((∃✶ x, J x) ==> H) := by
  intro hJ h hh
  rcases hh with ⟨x, hx⟩
  exact hJ x h hx

theorem himpl_hexists_r {A : Sort _} (x : A) {H : HProp} {J : A → HProp} :
    (H ==> J x) → (H ==> ∃✶ y, J y) := by
  intro hJ h hh
  exact ⟨x, hJ h hh⟩

theorem himpl_hexists {A : Sort _} {J1 J2 : A → HProp} :
    (J1 ==>+ J2) → ((∃✶ x, J1 x) ==> ∃✶ x, J2 x) := by
  intro hJ
  exact himpl_hexists_l (H := ∃✶ x, J2 x) (fun x => himpl_hexists_r x (hJ x))

theorem hforall_intro {A : Sort _} {J : A → HProp} {h : Heap} :
    (∀ x, J x h) → (∀✶ x, J x) h := by
  intro hJ
  exact hJ

theorem hforall_elim {A : Sort _} {J : A → HProp} {h : Heap} :
    (∀✶ x, J x) h → ∀ x, J x h := by
  intro hJ
  exact hJ

theorem himpl_hforall_r {A : Sort _} {J : A → HProp} {H : HProp} :
    (∀ x, H ==> J x) → (H ==> ∀✶ x, J x) := by
  intro hJ h hh x
  exact hJ x h hh

theorem himpl_hforall_l {A : Sort _} (x : A) {J : A → HProp} {H : HProp} :
    (J x ==> H) → ((∀✶ y, J y) ==> H) := by
  intro hJ h hh
  exact hJ h (hh x)

theorem hforall_specialize {A : Sort _} (x : A) (J : A → HProp) :
    (∀✶ y, J y) ==> J x := by
  exact himpl_hforall_l x (himpl_refl _)

theorem himpl_hforall {A : Sort _} {J1 J2 : A → HProp} :
    (J1 ==>+ J2) → ((∀✶ x, J1 x) ==> ∀✶ x, J2 x) := by
  intro hJ
  exact himpl_hforall_r (fun x => himpl_hforall_l x (hJ x))

theorem htop_intro (h : Heap) : htop h := by
  trivial

theorem himpl_htop_r (H : HProp) : H ==> htop := by
  intro _ _
  trivial

theorem hwand_equiv (H1 H2 H3 : HProp) :
    (H1 ==> (H2 -✶ H3)) ↔ (H2 ✶ H1 ==> H3) := by
  constructor
  · intro hW h hh
    rcases hh with ⟨h2, h0, hh2, hh0, hd, hu⟩
    rcases hW h0 hh0 with ⟨W, hhw⟩
    rcases hhw with ⟨hw, hp, hWw, hpW, hdW, huW⟩
    rcases hpure_elim hpW with ⟨himplW, _⟩
    subst hp
    rw [Finmap.union_empty] at huW
    simpa [hu] using himplW (h2 ∪ h0) ⟨h2, h0, hh2, huW ▸ hWw, hd, rfl⟩
  · intro hS h hh
    refine ⟨H1, ?_⟩
    refine ⟨h, ∅, hh, hpure_intro _ hS, ?_, ?_⟩
    · exact (Finmap.disjoint_empty h).symm
    · rw [Finmap.union_empty]

theorem himpl_hwand_r {H1 H2 H3 : HProp} :
    (H2 ✶ H1 ==> H3) → (H1 ==> H2 -✶ H3) := by
  intro hS
  exact (hwand_equiv H1 H2 H3).2 hS

theorem himpl_hwand_r_elim {H1 H2 H3 : HProp} :
    (H1 ==> H2 -✶ H3) → (H2 ✶ H1 ==> H3) := by
  intro hW
  exact (hwand_equiv H1 H2 H3).1 hW

theorem hwand_cancel (H1 H2 : HProp) :
    H1 ✶ (H1 -✶ H2) ==> H2 := by
  exact himpl_hwand_r_elim (himpl_refl _)

theorem himpl_hempty_hwand_same (H : HProp) :
    emp ==> (H -✶ H) := by
  apply himpl_hwand_r
  intro h hh
  simpa [hstar_hempty_r H] using hh

theorem hwand_hempty_l (H : HProp) :
    (emp -✶ H) = H := by
  apply himpl_antisym
  · intro h hh
    have hs : (emp ✶ (emp -✶ H)) h := by
      simpa [hstar_hempty_l (emp -✶ H)] using hh
    exact hwand_cancel emp H h hs
  · exact (hwand_equiv H emp H).2 <| by
      simpa [hstar_hempty_l H] using (himpl_refl H)

theorem hwand_hpure_l {P : Prop} (H : HProp) :
    P → (⌈P⌉ -✶ H) = H := by
  intro hP
  apply himpl_antisym
  · intro h hh
    have h1 : (⌈P⌉ -✶ H) ==> ⌈P⌉ ✶ (⌈P⌉ -✶ H) :=
      himpl_hstar_hpure_r hP (himpl_refl _)
    exact hwand_cancel ⌈P⌉ H h (h1 h hh)
  · exact (hwand_equiv H ⌈P⌉ H).2 <| by
      exact himpl_hstar_hpure_l (fun _ => himpl_refl H)

theorem hwand_curry (H1 H2 H3 : HProp) :
    ((H1 ✶ H2) -✶ H3) ==> (H1 -✶ H2 -✶ H3) := by
  apply himpl_hwand_r
  apply himpl_hwand_r
  intro h hh
  have hh' : ((H1 ✶ H2) ✶ ((H1 ✶ H2) -✶ H3)) h := by
    simpa [← hstar_assoc, hstar_comm H1 H2] using hh
  exact hwand_cancel (H1 ✶ H2) H3 h hh'

theorem hwand_uncurry (H1 H2 H3 : HProp) :
    (H1 -✶ H2 -✶ H3) ==> ((H1 ✶ H2) -✶ H3) := by
  exact (hwand_equiv (H1 -✶ H2 -✶ H3) (H1 ✶ H2) H3).2 <| by
    simpa [hstar_comm H1 H2, hstar_assoc] using
      (himpl_hstar_trans_r
        (H1 := H1 ✶ (H1 -✶ H2 -✶ H3))
        (H2 := H2 -✶ H3)
        (H3 := H2)
        (H4 := H3)
        (hwand_cancel H1 (H2 -✶ H3))
        (hwand_cancel H2 H3))

theorem hwand_curry_eq (H1 H2 H3 : HProp) :
    ((H1 ✶ H2) -✶ H3) = (H1 -✶ H2 -✶ H3) := by
  exact himpl_antisym (hwand_curry H1 H2 H3) (hwand_uncurry H1 H2 H3)

theorem hwand_elim {h1 h2 : Heap} {H1 H2 : HProp} :
    (H1 -✶ H2) h2 →
      H1 h1 →
      Finmap.Disjoint h1 h2 →
      H2 (h1 ∪ h2) := by
  intro hw hh1 hd
  rcases hw with ⟨H0, hH0⟩
  rcases hH0 with ⟨h0, hp, hh0, hp0, _, hu0⟩
  rcases hpure_elim hp0 with ⟨himpl0, _⟩
  subst hp
  rw [Finmap.union_empty] at hu0
  exact himpl0 _ ⟨h1, h2, hh1, hu0 ▸ hh0, hd, rfl⟩

theorem qwand_equiv {A : Sort _} (H : HProp) (Q1 Q2 : A → HProp) :
    (H ==> (Q1 -✶+ Q2)) ↔ ((Q1 ✶+ H) ==>+ Q2) := by
  constructor
  · intro hQ x
    exact (hwand_equiv H (Q1 x) (Q2 x)).1 <| by
      intro h hh
      exact hQ h hh x
  · intro hQ h hh x
    exact (hwand_equiv H (Q1 x) (Q2 x)).2 (hQ x) h hh

theorem qwand_cancel {A : Sort _} (Q1 Q2 : A → HProp) :
    (Q1 ✶+ (Q1 -✶+ Q2)) ==>+ Q2 := by
  exact (qwand_equiv (Q1 -✶+ Q2) Q1 Q2).1 (himpl_refl _)

theorem himpl_qwand_r {A : Sort _} {Q1 Q2 : A → HProp} {H : HProp} :
    ((Q1 ✶+ H) ==>+ Q2) → (H ==> Q1 -✶+ Q2) := by
  intro hQ
  exact (qwand_equiv H Q1 Q2).2 hQ

theorem qwand_specialize {A : Sort _} (x : A) (Q1 Q2 : A → HProp) :
    (Q1 -✶+ Q2) ==> (Q1 x -✶ Q2 x) := by
  exact himpl_hforall_l x (himpl_refl _)

theorem htop_eq_hexists_self :
    htop = ∃✶ H : HProp, H := by
  funext h
  apply propext
  constructor
  · intro _
    exact ⟨htop, trivial⟩
  · intro _
    trivial

theorem hstar_htop_htop :
    htop ✶ htop = htop := by
  apply himpl_antisym
  · exact himpl_htop_r _
  · intro h _
    refine ⟨∅, h, trivial, trivial, Finmap.disjoint_empty _, ?_⟩
    exact Finmap.empty_union.symm

theorem hsingle_intro (p : Loc) (v : val) : (p ↦ v) (Finmap.singleton p v) := by
  rfl

theorem hsingle_elim {p : Loc} {v : val} {h : Heap} :
    (p ↦ v) h → h = Finmap.singleton p v := by
  intro hh
  exact hh

theorem hstar_hsingle_same_loc (p : Loc) (w1 w2 : val) :
    ((p ↦ w1) ✶ (p ↦ w2)) ==> ⌈False⌉ := by
  intro h hh
  rcases hh with ⟨h1, h2, hh1, hh2, hd, _⟩
  have he1 : h1 = Finmap.singleton p w1 := hh1
  have he2 : h2 = Finmap.singleton p w2 := hh2
  subst h1 h2
  exfalso
  exact Finmap.not_disjoint_singleton_singleton hd

theorem hstar_hpure_conj (P1 P2 : Prop) :
    ⌈P1⌉ ✶ ⌈P2⌉ = ⌈P1 ∧ P2⌉ := by
  funext h
  apply propext
  constructor
  · intro hh
    rcases (hstar_hpure_l P1 ⌈P2⌉ h).1 hh with ⟨hP1, hh2⟩
    rcases hpure_elim hh2 with ⟨hP2, _⟩
    subst h
    exact hpure_intro (P1 ∧ P2) ⟨hP1, hP2⟩
  · intro hh
    rcases hpure_elim hh with ⟨hand, _⟩
    rcases hand with ⟨hP1, hP2⟩
    subst h
    exact (hstar_hpure_l P1 ⌈P2⌉ ∅).2 ⟨hP1, hpure_intro P2 hP2⟩

theorem hstar_pure_post_pure (P : val → Prop) (P1 : Prop) :
    (fun r => ⌈P r⌉ ✶ ⌈P1⌉) = (fun r => ⌈P r ∧ P1⌉) := by
  funext r
  exact hstar_hpure_conj (P r) P1

/-- Clean elimination form of `Precise`: any two heaps satisfying a precise `H`
    are equal. (Aliasing the definition with a friendlier name for `obtain`-
    style use.) -/
theorem Precise.unique {H : HProp} (hprec : Precise H)
    {h1 h2 : Heap} (hh1 : H h1) (hh2 : H h2) : h1 = h2 :=
  hprec h1 h2 hh1 hh2

theorem hempty_precise :
    Precise emp := by
  intro h1 h2 hh1 hh2
  rw [HProp.hempty_elim hh1, HProp.hempty_elim hh2]

/-- `⌈P⌉` only holds at empty heaps -/
theorem precise_hpure (P : Prop) : Precise ⌈P⌉ := by
  intro h1 h2 hh1 hh2
  rw [(HProp.hpure_elim hh1).2, (HProp.hpure_elim hh2).2]

theorem precise_hsingle (l : Loc) (v : val) :
    Precise (l ↦ v) := by
  intro h1 h2 hh1 hh2
  rw [HProp.hsingle_elim hh1, HProp.hsingle_elim hh2]

theorem precise_hstar {H1 H2 : HProp}
    (hp1 : Precise H1) (hp2 : Precise H2) :
    Precise (H1 ✶ H2) := by
  intro h h' hh hh'
  obtain ⟨a1, a2, hA1, hA2, hda, rfl⟩ := HProp.hstar_elim hh
  obtain ⟨b1, b2, hB1, hB2, hdb, rfl⟩ := HProp.hstar_elim hh'
  have he1 : a1 = b1 := hp1 _ _ hA1 hB1
  have he2 : a2 = b2 := hp2 _ _ hA2 hB2
  rw [he1, he2]

/-- Precision is downward-closed under entailment: anything implying a precise
    predicate is itself precise. Useful for transferring precision across
    rewrites or strengthenings. -/
theorem precise_of_himpl {H1 H2 : HProp}
    (hi : H1 ==> H2) (hp : Precise H2) : Precise H1 :=
  fun h1 h2 hh1 hh2 => hp h1 h2 (hi h1 hh1) (hi h2 hh2)

/-! Septraction -/

theorem hsept_intro {H1 H2 : HProp} {h h1 : Heap} (hH1 : H1 h1)
    (hd : Finmap.Disjoint h h1) (hH2 : H2 (h ∪ h1)) :
    (H1 -⊛ H2) h :=
  ⟨h1, hH1, hd, hH2⟩

/-- Septraction is monotone (covariant) in both arguments, unlike `-✶`, which is contravariant in its left argument. -/
theorem hsept_mono {H1 H1' H2 H2' : HProp}
    (hi1 : H1 ==> H1') (hi2 : H2 ==> H2') :
    H1 -⊛ H2 ==> H1' -⊛ H2' := by
  intro h ⟨p, hH1, hd, hH2⟩
  exact ⟨p, hi1 p hH1, hd, hi2 _ hH2⟩

/-- `hempty` is the left identity of septraction. -/
theorem hsept_hempty_l (H : HProp) : HProp.hempty -⊛ H = H := by
  funext h
  apply propext
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hpe, _, hH⟩
    have hp : p = ∅ := HProp.hempty_elim hpe
    subst hp
    rw [Finmap.union_empty] at hH
    exact hH
  · intro hH
    refine ⟨∅, HProp.hempty_intro, (Finmap.disjoint_empty _).symm, ?_⟩
    rw [Finmap.union_empty]; exact hH

theorem hsept_hexists_l {A : Sort _} (J : A → HProp) (H : HProp) :
    (∃✶ a, J a) -⊛ H = (∃✶ a, J a -⊛ H) := by
  funext h
  apply propext
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hex, hd, hH⟩
    obtain ⟨x, hJx⟩ := HProp.hexists_elim hex
    exact HProp.hexists_intro x _ ⟨p, hJx, hd, hH⟩
  · intro hh
    obtain ⟨x, p, hJx, hd, hH⟩ := HProp.hexists_elim hh
    exact ⟨p, HProp.hexists_intro x _ hJx, hd, hH⟩

/-- Dual of `hsept_hexists_l` -/
theorem hsept_hexists_r {A : Sort _} (H : HProp) (J : A → HProp) :
    H -⊛ (∃✶ a, J a) = (∃✶ a, H -⊛ J a) := by
  funext h
  apply propext
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hHp, hd, hex⟩
    obtain ⟨x, hJx⟩ := HProp.hexists_elim hex
    exact HProp.hexists_intro x _ ⟨p, hHp, hd, hJx⟩
  · intro hh
    obtain ⟨x, p, hHp, hd, hJx⟩ := HProp.hexists_elim hh
    exact ⟨p, hHp, hd, HProp.hexists_intro x _ hJx⟩

/-- Currying: subtracting `H1 ✶ H2` is the same as subtracting them in
    sequence. The dual of `hwand_curry_eq`. -/
theorem hsept_hstar_l (H1 H2 H3 : HProp) :
    (H1 ✶ H2) -⊛ H3 = H1 -⊛ (H2 -⊛ H3) := by
  funext h
  apply propext
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hstar, hd, hH3⟩
    obtain ⟨p1, p2, hH1, hH2, hd12, rfl⟩ := HProp.hstar_elim hstar
    refine ⟨p1, hH1, by fmap_disjoint, p2, hH2, by fmap_disjoint, ?_⟩
    · exact (Finmap.union_assoc (s₁ := h) (s₂ := p1) (s₃ := p2)).symm ▸ hH3
  · rintro ⟨p1, hH1, hd1, p2, hH2, hd2, hH3⟩
    refine ⟨p1 ∪ p2, HProp.hstar_intro hH1 hH2 (by fmap_disjoint), by fmap_disjoint, ?_⟩
    · exact Finmap.union_assoc (s₁ := h) (s₂ := p1) (s₃ := p2) ▸ hH3

/-- Cancellation: `(H1 -⊛ H2) ✶ H1 ==> H2`, when `H1` is precise.
    Without precision, the witness piece in the septraction need not equal
    the actual `H1` piece, so the joined heap may differ. The dual of
    `hwand_cancel : H1 ✶ (H1 -✶ H2) ==> H2`, which holds unconditionally. -/
theorem hsept_cancel {H1 H2 : HProp} (hprec : Precise H1) :
    (H1 -⊛ H2) ✶ H1 ==> H2 := by
  intro h hh
  obtain ⟨k1, k2, hsept, hH1k2, _, heq⟩ := HProp.hstar_elim hh
  obtain ⟨p, hH1p, hdp, hH2⟩ := hsept
  have hpe : p = k2 := hprec p k2 hH1p hH1k2
  subst hpe
  rw [heq]; exact hH2

/-- `H -⊛ emp` reduces to "the heap absorbs an `H`-witness whose result is empty",
    which forces both sides to be empty. -/
theorem hsept_hempty_r (H : HProp) :
    H -⊛ hempty = fun h => h = ∅ ∧ H ∅ := by
  funext h
  apply propext
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hHp, hd, hH⟩
    have hu : h ∪ p = ∅ := HProp.hempty_elim hH
    have hh : h = ∅ := by
      apply Finmap.ext_lookup
      intro a
      show Finmap.lookup a h = Finmap.lookup a (∅ : Heap)
      rw [Finmap.lookup_empty]
      have hpt : Finmap.lookup a (h ∪ p) = Finmap.lookup a (∅ : Heap) := by rw [hu]
      rw [Finmap.lookup_empty] at hpt
      by_cases hap : a ∈ p
      · exact Finmap.lookup_eq_none.mpr (fun ha => (hd a ha) hap)
      · rw [← Finmap.lookup_union_left_of_not_in (s₂ := p) hap]; exact hpt
    have hp : p = ∅ := by
      apply Finmap.ext_lookup
      intro a
      show Finmap.lookup a p = Finmap.lookup a (∅ : Heap)
      rw [Finmap.lookup_empty]
      have hpt : Finmap.lookup a (h ∪ p) = Finmap.lookup a (∅ : Heap) := by rw [hu]
      rw [Finmap.lookup_empty] at hpt
      subst hh
      rw [Finmap.empty_union] at hpt; exact hpt
    exact ⟨hh, hp ▸ hHp⟩
  · rintro ⟨rfl, hHe⟩
    refine ⟨∅, hHe, (Finmap.disjoint_empty _).symm, ?_⟩
    rw [Finmap.union_empty]; exact HProp.hempty_intro

/-- Subtracting a pure proposition is the same as conjoining it. The witness must
    be empty (only `∅` satisfies `⌜P⌝`), so `-⊛` collapses to `✶`. -/
theorem hsept_hpure_l (P : Prop) (H : HProp) :
    HProp.hpure P -⊛ H = HProp.hpure P ✶ H := by
  funext h
  apply propext
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hPp, hd, hH⟩
    obtain ⟨hP, hpe⟩ := HProp.hpure_elim hPp
    subst p
    rw [Finmap.union_empty] at hH
    exact (HProp.hstar_hpure_l P H h).2 ⟨hP, hH⟩
  · intro hh
    obtain ⟨hP, hH⟩ := (HProp.hstar_hpure_l P H h).1 hh
    refine ⟨∅, HProp.hpure_intro P hP, (Finmap.disjoint_empty _).symm, ?_⟩
    rw [Finmap.union_empty]; exact hH

/-- Subtracting *to* a pure proposition: only achievable from the empty heap with
    a witness in `H` whose union with `∅` is empty (i.e. only `H emp ∧ P`). -/
theorem hsept_hpure_r (H : HProp) (P : Prop) :
    H -⊛ HProp.hpure P =
      fun h => h = ∅ ∧ H ∅ ∧ P := by
  funext h
  apply propext
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hHp, hd, hPp⟩
    obtain ⟨hP, hue⟩ := HProp.hpure_elim hPp
    have hh : h = ∅ := by
      apply Finmap.ext_lookup
      intro a
      show Finmap.lookup a h = Finmap.lookup a (∅ : Heap)
      rw [Finmap.lookup_empty]
      have hpt : Finmap.lookup a (h ∪ p) = Finmap.lookup a (∅ : Heap) := by rw [hue]
      rw [Finmap.lookup_empty] at hpt
      by_cases hap : a ∈ p
      · exact Finmap.lookup_eq_none.mpr (fun ha => (hd a ha) hap)
      · rw [← Finmap.lookup_union_left_of_not_in (s₂ := p) hap]; exact hpt
    have hp : p = ∅ := by
      subst hh
      rw [Finmap.empty_union] at hue; exact hue
    exact ⟨hh, hp ▸ hHp, hP⟩
  · rintro ⟨rfl, hHe, hP⟩
    refine ⟨∅, hHe, (Finmap.disjoint_empty _).symm, ?_⟩
    rw [Finmap.union_empty]; exact HProp.hpure_intro P hP

/-- One direction of the septraction/`✶` adjunction, with precision: if `H2` always
    splits as `H3 ✶ H1`, then subtracting `H1` from `H2` lands in `H3`. The reverse
    direction does not hold without further structure (an arbitrary `H2`-heap need
    not contain an `H1`-piece to extract). -/
theorem hsept_himpl_of_hstar {H1 H2 H3 : HProp} (hprec : Precise H1)
    (himp : H2 ==> H3 ✶ H1) :
    H1 -⊛ H2 ==> H3 := by
  intro h ⟨p, hH1p, hdhp, hH2⟩
  obtain ⟨k1, k2, hH3, hH1k2, hd12, heq⟩ := HProp.hstar_elim (himp _ hH2)
  have hpe : k2 = p := (hprec p k2 hH1p hH1k2).symm
  subst hpe
  have hk1 : k1 = h := Finmap.union_cancel_right hd12 hdhp heq.symm
  exact hk1 ▸ hH3

/-- Round-trip law: subtracting a precise `H1` from `H1 ✶ H2` recovers `H2`.
    The dual of `hwand_cancel` in the "produce-then-consume" direction; the
    converse `H2 ==> H1 -⊛ (H1 ✶ H2)` does not hold (it requires the existence
    of a witness for `H1` disjoint from the current heap). Specialization of
    `hsept_himpl_of_hstar`. -/
theorem hsept_hstar_himpl {H1 H2 : HProp} (hprec : Precise H1) :
    (H1 -⊛ (H1 ✶ H2)) ==> H2 :=
  hsept_himpl_of_hstar hprec (HProp.hstar_comm H1 H2 ▸ HProp.himpl_refl _)

/-- A satisfiable `H` self-cancels: `emp ==> H -⊛ H` provided `H` holds of *some*
    heap. (The witness for the septraction is that heap.) -/
theorem hempty_himpl_hsept_self {H : HProp} (hsat : ∃ p, H p) :
    hempty ==> H -⊛ H := by
  intro h hh
  obtain ⟨p, hHp⟩ := hsat
  have hhe : h = ∅ := HProp.hempty_elim hh
  subst hhe
  refine ⟨p, hHp, Finmap.disjoint_empty p, ?_⟩
  rw [Finmap.empty_union]; exact hHp

/-- Reusable extractor witnessing the heap split that drives the reverse
    direction of `hsept_hstar_r`. Given `h ⊕ p = q1 ⊕ q2` with `disjoint p q2`,
    the residue `h \ q2` separates an `H`-piece from an `H1`-piece: it satisfies
    `(H -⊛ H1)`, is disjoint from `q2`, and reunites with `q2` to yield `h`. -/
theorem hsept_intro_split {H H1 : HProp}
    {h p q1 q2 : Heap}
    (hHp : H p)
    (hH1 : H1 q1)
    (hdhp : Finmap.Disjoint h p)
    (hd12 : Finmap.Disjoint q1 q2)
    (hdpq2 : Finmap.Disjoint p q2)
    (heq : h ∪ p = q1 ∪ q2) :
    (H -⊛ H1) (h \ q2) ∧
    Finmap.Disjoint (h \ q2) q2 ∧
    (h \ q2) ∪ q2 = h := by
  have hd_sd_q2 : Finmap.Disjoint (h \ q2) q2 := Finmap.disjoint_sdiff_self h q2
  have hd_sd_p : Finmap.Disjoint (h \ q2) p := Finmap.disjoint_sdiff_of_disjoint hdhp
  have hsplit : (h \ q2) ∪ p = q1 :=
    Finmap.union_sdiff_eq_of_union_eq hd12 hdpq2 heq
  have hh : (h \ q2) ∪ q2 = h := by
    apply Finmap.ext_lookup
    intro a
    show Finmap.lookup a ((h \ q2) ∪ q2) = Finmap.lookup a h
    by_cases ha2 : a ∈ q2
    · have hsd : a ∉ (h \ q2) := fun h' => hd_sd_q2 a h' ha2
      have hap : a ∉ p := fun hp => hdpq2 a hp ha2
      have ha1 : a ∉ q1 := fun h' => hd12 a h' ha2
      have hpoint : Finmap.lookup a (h ∪ p) = Finmap.lookup a (q1 ∪ q2) := by
        rw [heq]
      rw [Finmap.lookup_union_right hsd,
          ← Finmap.lookup_union_right ha1, ← hpoint,
          Finmap.lookup_union_left_of_not_in hap]
    · rw [Finmap.lookup_union_left_of_not_in ha2]
      exact Finmap.lookup_sdiff_of_notMem ha2
  exact ⟨⟨p, hHp, hd_sd_p, hsplit ▸ hH1⟩, hd_sd_q2, hh⟩

/-- Forward direction of right-distribution for septraction.
    The frame `H2` may be absorbed *into* a septraction by `H` provided `H` and `H2`
    operate on disjoint footprints (so the `H`-witness from the septraction stays
    disjoint from the `H2` piece). Without `Separated H H2` this fails: the witness
    `p : H p` from the septraction could collide with the framed `H2`-piece. -/
theorem hstar_himpl_hsept_hstar_r {H H1 H2 : HProp} (hsep : Separated H H2) :
    (H -⊛ H1) ✶ H2 ==> H -⊛ (H1 ✶ H2) := by
  intro h hh
  obtain ⟨k1, k2, ⟨p, hHp, hdk1p, hH1⟩, hH2k2, hdk1k2, rfl⟩ := HProp.hstar_elim hh
  have hdk2p : Finmap.Disjoint k2 p := (hsep p k2 hHp hH2k2).symm
  refine ⟨p, hHp, by fmap_disjoint, ?_⟩
  have heq : (k1 ∪ k2) ∪ p = (k1 ∪ p) ∪ k2 := by fmap_eq
  rw [heq]
  exact HProp.hstar_intro hH1 hH2k2 (by fmap_disjoint)

/-- Right-distribution equality for septraction over `✶`, given the frame `H2`
is footprint-disjoint from `H`. The forward direction is
`hstar_himpl_hsept_hstar_r`; the reverse splits `h` as `(h \ q2) ⊕ q2`. -/
theorem hsept_hstar_r {H H1 H2 : HProp} (hsep : Separated H H2) :
    H -⊛ (H1 ✶ H2) = (H -⊛ H1) ✶ H2 := by
  funext h; apply propext
  refine ⟨?_, hstar_himpl_hsept_hstar_r hsep h⟩
  rintro ⟨p, hHp, hdhp, hstar⟩
  obtain ⟨q1, q2, hH1, hH2, hd12, heq⟩ := HProp.hstar_elim hstar
  have hdpq2 : Finmap.Disjoint p q2 := hsep p q2 hHp hH2
  obtain ⟨hH1sd, hd_sd_q2, hh⟩ :=
    hsept_intro_split hHp hH1 hdhp hd12 hdpq2 heq
  exact hh ▸ HProp.hstar_intro hH1sd hH2 hd_sd_q2

/-! Other -/

def haffine (_H : HProp) : Prop := True

def hgc : HProp := htop

theorem haffine_hany (H : HProp) : haffine H := by
  trivial

theorem haffine_hempty : haffine emp := by
  trivial

theorem haffine_hgc : haffine hgc := by
  trivial

theorem himpl_hgc_r (H : HProp) :
    haffine H → (H ==> hgc) := by
  intro _
  exact himpl_htop_r H

/-! Satisfiability -/

theorem sat_hempty : Sat emp := ⟨∅, hempty_intro⟩

theorem sat_hpure {P : Prop} : Sat ⌈P⌉ ↔ P :=
  ⟨fun ⟨_, hp⟩ => (hpure_elim hp).1, fun hP => ⟨∅, hpure_intro P hP⟩⟩

theorem sat_htop : Sat htop := ⟨∅, htop_intro _⟩

theorem sat_hsingle (l : Loc) (v : val) : Sat (l ↦ v) :=
  ⟨Finmap.singleton l v, hsingle_intro l v⟩

theorem sat_hexists {A : Sort _} {J : A → HProp} :
    Sat (∃✶ x, J x) ↔ ∃ x, Sat (J x) :=
  ⟨fun ⟨p, x, hx⟩ => ⟨x, p, hx⟩, fun ⟨x, p, hx⟩ => ⟨p, x, hx⟩⟩

theorem sat_himpl {H1 H2 : HProp} (hi : H1 ==> H2) : Sat H1 → Sat H2
  | ⟨p, hp⟩ => ⟨p, hi p hp⟩

theorem sat_hstar_left {H1 H2 : HProp} : Sat (H1 ✶ H2) → Sat H1
  | ⟨_, h1, _, hh1, _, _, _⟩ => ⟨h1, hh1⟩

theorem sat_hstar_right {H1 H2 : HProp} : Sat (H1 ✶ H2) → Sat H2
  | ⟨_, _, h2, _, hh2, _, _⟩ => ⟨h2, hh2⟩

theorem sat_hstar_of_separated {H1 H2 : HProp}
    (hsep : Separated H1 H2) : Sat H1 → Sat H2 → Sat (H1 ✶ H2)
  | ⟨h1, hh1⟩, ⟨h2, hh2⟩ =>
      ⟨h1 ∪ h2, hstar_intro hh1 hh2 (hsep h1 h2 hh1 hh2)⟩

/-! `_eq` API: canonical unfolding lemmas, mathlib-style. Prefer these over
    the `_intro` / `_elim` pairs when both directions are needed at once.
    Not tagged `@[simp]`: the unfolded form is more complex, and these
    primitives are the canonical form. -/

theorem hempty_eq (h : Heap) : (emp : HProp) h ↔ h = ∅ := Iff.rfl

theorem hsingle_eq (p : Loc) (v : val) (h : Heap) :
    (p ↦ v) h ↔ h = Finmap.singleton p v := Iff.rfl

theorem hstar_eq (H1 H2 : HProp) (h : Heap) :
    (H1 ✶ H2) h ↔
      ∃ h1 h2, H1 h1 ∧ H2 h2 ∧ Finmap.Disjoint h1 h2 ∧ h = h1 ∪ h2 :=
  Iff.rfl

theorem hexists_eq {A : Sort _} (J : A → HProp) (h : Heap) :
    (∃✶ x, J x) h ↔ ∃ x, J x h := Iff.rfl

theorem hforall_eq {A : Sort _} (J : A → HProp) (h : Heap) :
    (∀✶ x, J x) h ↔ ∀ x, J x h := Iff.rfl

theorem hpure_eq (P : Prop) (h : Heap) :
    ⌈P⌉ h ↔ P ∧ h = ∅ :=
  ⟨hpure_elim, fun ⟨hP, hh⟩ => hh ▸ hpure_intro P hP⟩

theorem htop_eq (h : Heap) : htop h ↔ True := Iff.rfl

theorem hand_eq (H1 H2 : HProp) (h : Heap) :
    (H1 ⊓ H2) h ↔ H1 h ∧ H2 h := Iff.rfl

attribute [irreducible] hempty hsingle hstar hexists hforall hpure htop hwand qwand hand
