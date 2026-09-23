module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Diagonals of representable presheaves

This file transports the scheme-theoretic fact that every diagonal is an immersion
across a chosen representation of a presheaf.  It supplies the presheaf-level form
needed to rule out representability from a non-immersive diagonal.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits

universe u

namespace AlgebraicGeometry

/-- The diagonal of a presheaf represented by a scheme is representable by immersions. -/
theorem presheaf_isImmersion_diag_of_isRepresentable
    (X : Functor Scheme.{u}ᵒᵖ (Type u)) [X.IsRepresentable] :
    MorphismProperty.presheaf (@IsImmersion : MorphismProperty Scheme.{u})
      (Limits.diag X) := by
  let e : yoneda.obj X.reprX ≅ X := X.reprW
  let e₂ : yoneda.obj (X.reprX ⨯ X.reprX) ≅ X ⨯ X :=
    preservesLimitIso yoneda (pair X.reprX X.reprX) ≪≫
      HasLimit.isoOfNatIso (pairComp X.reprX X.reprX yoneda) ≪≫
      prod.mapIso e e
  have hdiag : MorphismProperty.presheaf
      (@IsImmersion : MorphismProperty Scheme.{u})
      (yoneda.map (prod.lift (𝟙 X.reprX) (𝟙 X.reprX))) :=
    MorphismProperty.relative_map (by infer_instance)
  refine (MorphismProperty.arrow_mk_iso_iff _
    (Arrow.isoMk e e₂ ?_)).1 hdiag
  apply prod.hom_ext <;> simp [e₂, e]
  all_goals
    change X.reprW.hom = 𝟙 _ ≫ X.reprW.hom
    simp

end AlgebraicGeometry
