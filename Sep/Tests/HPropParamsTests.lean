import Sep.HProp

open HProp

-- Instantiate with Nat:
instance natParams : Params where
  val := Nat

-- Now this just works, no explicit V anywhere:

/-- info: HProp.hempty [Params] : HProp -/
#guard_msgs in
#check hempty  -- instance is inferred

/-- info: hsingle 1 42 : HProp -/
#guard_msgs in
#check (hsingle 1 (42 : Nat))

example : val := (42 : Nat)
example : HProp := hempty

-- We can also instantiate with String:
namespace StringHeap

instance stringParams : Params where
  val := String

/-- info: hsingle 1 "hello" : HProp -/
#guard_msgs in
#check (hsingle 1 "hello")

example : val := "world"

end StringHeap
