module

public import StacksAndModuli.API.OverBasedYonedaEquivalence
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»

/-!
# Scheme models of fibers of representable morphisms

`BasedFunctor.RepresentableWith P F` states the property using every algebraic-space
realization of a fiber and every scheme atlas of that realization.  This file records
the useful special case in which the fiber is already represented by a scheme: use the
representable presheaf itself and its identity atlas, then cancel the based Yoneda
equivalence.

## Main result

* `BasedFunctor.RepresentableWith.property_of_scheme_representation`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor
open CategoryTheory.BasedCategory

universe v₁ u₁ v₂ u₂ u

namespace AlgebraicGeometry.BasedFunctor

/-- The structural morphism of any scheme representation of a fiber of a morphism
representable with `P` has property `P`. -/
theorem RepresentableWith.property_of_scheme_representation
    {Xcat : BasedCategory.{v₁, u₁} Scheme.{u}}
    {Ycat : BasedCategory.{v₂, u₂} Scheme.{u}}
    {P : MorphismProperty Scheme.{u}} {F : Xcat ⥤ᵇ Ycat}
    (hF : RepresentableWith P F)
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ Ycat)
    (U : Scheme.{u})
    (E : overBased U ⥤ᵇ fiberProduct F g)
    (hE : E.toFunctor.IsEquivalence) :
    P (E.comp (CategoryTheory.BasedCategory.fiberProductSnd F g)).overHom := by
  let I := ofPresheafYonedaToOverBased U
  let O := overBasedToOfPresheafYoneda U
  let E' := I.comp E
  have hE' : E'.toFunctor.IsEquivalence := by
    change (I.toFunctor ⋙ E.toFunctor).IsEquivalence
    exact Functor.isEquivalence_trans I.toFunctor E.toFunctor
  have hq : MorphismProperty.presheaf
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale :
        MorphismProperty Scheme.{u}) (𝟙 (yoneda.obj U)) :=
    (MorphismProperty.presheaf
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale :
        MorphismProperty Scheme.{u})).id_mem _
  have hP := hF.2 T g (yoneda.obj U) (by infer_instance)
    E' hE' U (𝟙 (yoneda.obj U)) hq
  let H := E.comp (CategoryTheory.BasedCategory.fiberProductSnd F g)
  have hmap : ofPresheaf.map (𝟙 (yoneda.obj U)) =
      CategoryTheory.BasedFunctor.id (ofPresheaf (yoneda.obj U)) := by
    apply CategoryTheory.BasedFunctor.ext_of_toFunctor_eq
    rfl
  have e : O.comp ((ofPresheaf.map (𝟙 (yoneda.obj U))).comp
      (E'.comp (CategoryTheory.BasedCategory.fiberProductSnd F g))) ≅ H := by
    rw [hmap]
    exact (eqToIso (CategoryTheory.BasedFunctor.comp_assoc O
      (CategoryTheory.BasedFunctor.id _) _)).trans
      ((isoWhiskerRight (overBasedYonedaCounitIso U) H).trans
        (eqToIso (CategoryTheory.BasedFunctor.id_comp H)))
  exact (CategoryTheory.BasedFunctor.overHom_eq_of_iso e) ▸ hP

end AlgebraicGeometry.BasedFunctor
