import Sep.HProp

instance : Params where
  val := Nat

open HProp Notation

-- abbrev HProp : Type := HProp
abbrev Q : Type := Nat → HProp

def H : HProp := fun _ => True
def H1 : HProp := fun _ => True
def H2 : HProp := fun _ => False
def Pst : Q := fun _ => H
def Pst1 : Q := fun x => fun _ => x = x
def Pst2 : Q := fun x => fun _ => x = x
def v : val := (2 : Nat)

/-- info: emp : HProp -/
#guard_msgs in
#check (emp : HProp)

/-- info: ⌈True⌉ : HProp -/
#guard_msgs in
#check (⌈True⌉ : HProp)

-- /-- info: \Top : HProp -/
-- #guard_msgs in
-- #check (\Top : HProp)

/-- info: 1 ↦ v : HProp -/
#guard_msgs in
#check (1 ↦ v : HProp)

/-- info: H1 ✶ H2 : HProp -/
#guard_msgs in
#check (H1 ✶ H2 : HProp)

/-- info: H1 ==> H2 : Prop -/
#guard_msgs in
#check (H1 ==> H2 : Prop)

/-- info: Pst1 ==>+ Pst2 : Prop -/
#guard_msgs in
#check (Pst1 ==>+ Pst2 : Prop)

/-- info: fun x => Pst x ✶ H : ℕ → HProp -/
#guard_msgs in
#check (Pst ✶+ H : Nat → HProp)

/-- info: H1 -✶ H2 : HProp -/
#guard_msgs in
#check (H1 -✶ H2 : HProp)

/-- info: Pst1 -✶+ Pst2 : HProp -/
#guard_msgs in
#check (Pst1 -✶+ Pst2 : HProp)

/-- info: ∃✶ x, x ↦ x : HProp -/
#guard_msgs in
#check (∃✶ x, ((x ↦ x : HProp)) : HProp)

/-- info: ∀✶ x, x ↦ x : HProp -/
#guard_msgs in
#check (∀✶ x, ((x ↦ x : HProp)) : HProp)

/-- info: ∃✶ x, ∃✶ y, x ↦ y : HProp -/
#guard_msgs in
#check (∃✶ x y, ((x ↦ y : HProp)) : HProp)

/-- info: ∀✶ x, ∀✶ y, x ↦ y : HProp -/
#guard_msgs in
#check (∀✶ x y, ((x ↦ y : HProp)) : HProp)
