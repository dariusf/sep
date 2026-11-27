module

public import Lean

public section

open Lean PrettyPrinter

/-!
# Pretty-printing quantifier binder notation

Makes a quantifier such as `hexists fun x => hexists fun y => P` print as
`∃ₛ x y, P`, with nested binders merged into one.
Useful for logics that declare their own `∃ₛ`- or `∀ₛ`-style notation.

For example:

```
-- Vanilla declaration
macro:max (name := sepExists) "∃ₛ " xs:explicitBinders ", " b:term : term =>
  return ⟨← expandExplicitBinders ``hexists xs b⟩

-- Use of this
@[app_unexpander hexists] def unexpandSepExists : Unexpander :=
  unexpandQuantifierBinder ``sepExists "∃ₛ "
```

The arguments to `unexpandQuantifierBinder` are the name given to the notation and its opening token.

mathlib's notation3 is an alternative.
-/

namespace Sep

meta def unexpandQuantifierBinder (kind : Name) (tk : String) : Unexpander := fun stx => do
  let (x, body) ← match stx with
    | `($(_) fun $x:ident => $body) => pure (x, body)
    | `($(_) fun ($x:ident : $_) => $body) => pure (x, body)
    | _ => throw ()
  let mut ids : Array (TSyntax ``binderIdent) := #[← `(binderIdent| $x:ident)]
  let mut body := body
  if body.raw.getKind == kind then
    if let `(explicitBinders| $ys:binderIdent*) := body.raw[1] then
      ids := ids ++ ys
      body := ⟨body.raw[3]⟩
  let bs ← `(explicitBinders| $ids:binderIdent*)
  return Syntax.node .none kind #[Syntax.atom .none tk, bs, Syntax.atom .none ", ", body]

end Sep
