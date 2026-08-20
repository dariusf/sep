import Sep.GrwSepLogic
import Sep.Xsimpl

namespace Sep.Xsimpl

open scoped SepLogic

instance instSepLogicHPropType [Params] : SepLogic.{0, 1} HProp := instSepLogicHProp

variable [Params]

attribute [refl] HProp.himpl_refl

instance : Trans (SepLogic.Entails (α := HProp)) SepLogic.Entails SepLogic.Entails :=
  ⟨SepLogic.entails_trans⟩

@[gcongr]
theorem himpl_imp_himpl {H1 H1' H2 H2' : HProp} (h1 : H1' ==> H1) (h2 : H2 ==> H2') :
    (H1 ==> H2) → (H1' ==> H2') :=
  SepLogic.entails_imp_entails h1 h2

@[gcongr]
theorem hstar_mono {H1 H1' H2 H2' : HProp} (h1 : H1 ==> H1') (h2 : H2 ==> H2') :
    (H1 ∗ H2) ==> (H1' ∗ H2') :=
  SepLogic.star_mono h1 h2

end Sep.Xsimpl
