import Sep.Tests.Notation
import Sep.HProp.SepLogic

namespace SepLogicNotationTests

open Sep.Tests.Notation

local notation "α" => HProp

variable [Params] (H1 H2 H3 : α) (P : Prop) (J : Nat → α) (K : Nat → Nat → α)

/-- info: H1 ∗ H2 : α -/
#guard_msgs in
#check (H1 ∗ H2 : α)

/-- info: H1 ∗ H2 ∗ H3 : α -/
#guard_msgs in
#check (H1 ∗ H2 ∗ H3 : α)

/-- info: H1 -∗ H2 : α -/
#guard_msgs in
#check (H1 -∗ H2 : α)

/-- info: H1 ==> H2 : Prop -/
#guard_msgs in
#check (H1 ==> H2 : Prop)

/-- info: emp : α -/
#guard_msgs in
#check (emp : α)

/-- info: ⌜P⌝ : α -/
#guard_msgs in
#check (⌜P⌝ : α)

/-- info: ∃ₛ x, J x : α -/
#guard_msgs in
#check (∃ₛ x, J x : α)

/-- info: ∃ₛ x y, K x y : α -/
#guard_msgs in
#check (∃ₛ x y, K x y : α)

/-- info: ∃ₛ x, J x : α -/
#guard_msgs in
#check (∃ₛ (x : Nat), J x : α)

/-- info: ∀ₛ x, J x : α -/
#guard_msgs in
#check (∀ₛ x, J x : α)

/-- info: ∀ₛ x y, K x y : α -/
#guard_msgs in
#check (∀ₛ x y, K x y : α)

/-- info: ∀ₛ x, ∃ₛ y, K x y : α -/
#guard_msgs in
#check (∀ₛ x, ∃ₛ y, K x y : α)

/-- info: H1 ∗ (H1 -∗ H2) ==> H2 : Prop -/
#guard_msgs in
#check (H1 ∗ (H1 -∗ H2) ==> H2 : Prop)

/-- info: ⌜P⌝ ∗ emp ==> ∃ₛ x, J x : Prop -/
#guard_msgs in
#check (⌜P⌝ ∗ emp ==> ∃ₛ x, J x : Prop)

end SepLogicNotationTests
