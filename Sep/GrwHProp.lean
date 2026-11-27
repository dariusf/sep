module

public import Sep.GrwSepLogic
public import Sep.HProp.SepLogic

public section

namespace Sep.Xsimpl

open HProp Notation

variable [Params]

attribute [refl] HProp.himpl_refl

instance : Trans HProp.himpl HProp.himpl HProp.himpl :=
  ⟨HProp.himpl_trans⟩

@[gcongr]
theorem himpl_imp_himpl {H1 H1' H2 H2' : HProp} (h1 : H1' ==> H1) (h2 : H2 ==> H2') :
    (H1 ==> H2) → (H1' ==> H2') :=
  SepLaws.entails_imp_entails h1 h2

@[gcongr]
theorem hstar_mono {H1 H1' H2 H2' : HProp} (h1 : H1 ==> H1') (h2 : H2 ==> H2') :
    (H1 ✶ H2) ==> (H1' ✶ H2') :=
  SepLaws.star_mono h1 h2

@[gcongr]
theorem hexists_mono {A : Sort _} {J K : A → HProp} (h : ∀ x, J x ==> K x) :
    hexists J ==> hexists K :=
  SepLaws.ex_mono h

@[gcongr]
theorem hwand_mono {H1 H1' H2 H2' : HProp} (h1 : H1' ==> H1) (h2 : H2 ==> H2') :
    (H1 -✶ H2) ==> (H1' -✶ H2') :=
  SepLaws.wand_mono h1 h2

end Sep.Xsimpl
