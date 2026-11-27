module

public import Sep.HProp
public meta import Lean

public section

open Lean

namespace HProp

/-- Parse a star chain stated with the `HProp` constants. -/
meta partial def parseHstar (e : Expr) : List Expr :=
  match e.getAppFnArgs with
  | (``HProp.hstar, #[_, H1, H2]) => H1 :: parseHstar H2
  | (``HProp.hempty, _) => []
  | _ => [e]

end HProp
