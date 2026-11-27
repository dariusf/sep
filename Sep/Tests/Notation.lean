import Sep.HProp
import Sep.QuantifierUnexpander

open Lean PrettyPrinter

namespace Sep.Tests.Notation

scoped infixr:61 " ∗ " => HProp.hstar
scoped infixr:60 " -∗ " => HProp.hwand
scoped infixr:25 " ==> " => HProp.himpl
scoped notation:max "emp" => HProp.hempty
scoped notation:max "⌜" P "⌝" => HProp.hpure P

scoped macro:max (name := sepExists) "∃ₛ " xs:explicitBinders ", " b:term : term =>
  return ⟨← expandExplicitBinders ``HProp.hexists xs b⟩

scoped macro:max (name := sepForall) "∀ₛ " xs:explicitBinders ", " b:term : term =>
  return ⟨← expandExplicitBinders ``HProp.hforall xs b⟩

@[scoped app_unexpander HProp.hexists] def unexpandSepExists : Unexpander :=
  unexpandQuantifierBinder ``sepExists "∃ₛ "

@[scoped app_unexpander HProp.hforall] def unexpandSepForall : Unexpander :=
  unexpandQuantifierBinder ``sepForall "∀ₛ "

end Sep.Tests.Notation
