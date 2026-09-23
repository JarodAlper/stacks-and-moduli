module

public import StacksAndModuli.API.FiberProductPresentationRepresentable
public import StacksAndModuli.API.RepresentableWithEquivalence

/-!
# Properties of the canonical fiber-product presentation map

The canonical map induced by two presentation morphisms is a base change of their
product, up to an equivalence of source prestacks and a based natural isomorphism.
This file transfers a `RepresentableWith` statement across that comparison.
-/

@[expose] public section

open CategoryTheory Functor
open CategoryTheory.BasedCategory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅ u

namespace AlgebraicGeometry.BasedFunctor

variable {U : BasedCategory.{v₁, u₁} Scheme.{u}}
  {X : BasedCategory.{v₂, u₂} Scheme.{u}}
  {V : BasedCategory.{v₃, u₃} Scheme.{u}}
  {Y' : BasedCategory.{v₄, u₄} Scheme.{u}}
  {Y : BasedCategory.{v₅, u₅} Scheme.{u}}

/-- If the product of two presentation morphisms is representable with property
`P`, then so is the canonical morphism from the fiber product of their composites
to the fiber product of their targets. -/
theorem RepresentableWith.fiberProductPresentationMap_of_prodMap
    {𝒷 : MorphismProperty Scheme.{u}}
    [U.p.IsFiberedInGroupoids] [X.p.IsFiberedInGroupoids]
    [V.p.IsFiberedInGroupoids] [Y'.p.IsFiberedInGroupoids]
    [Y.p.IsFiberedInGroupoids]
    {F : X ⥤ᵇ Y} {G : Y' ⥤ᵇ Y}
    {P : U ⥤ᵇ X} {Q : V ⥤ᵇ Y'}
    (hprod : RepresentableWith 𝒷
      (CategoryTheory.BasedCategory.prodMap P Q)) :
    RepresentableWith 𝒷
      (CategoryTheory.BasedCategory.fiberProductPresentationMap F G P Q) := by
  let H := CategoryTheory.BasedCategory.fiberProductPairMap F G
  let π := CategoryTheory.BasedCategory.fiberProductSnd
    (CategoryTheory.BasedCategory.prodMap P Q) H
  have hπ : RepresentableWith 𝒷 π := hprod.fiberProductSnd H
  let E := CategoryTheory.BasedCategory.fiberProductPresentationBaseChangeComparison
    F G P Q
  let _ : E.toFunctor.IsEquivalence :=
    CategoryTheory.BasedCategory.isEquivalence_fiberProductPresentationBaseChangeComparison
      F G P Q
  let η := CategoryTheory.BasedCategory.fiberProductPresentationBaseChangeIso
    F G P Q
  have hcomp : RepresentableWith 𝒷
      (E.comp (CategoryTheory.BasedCategory.fiberProductPresentationMap F G P Q)) :=
    hπ.of_iso η.symm
  exact RepresentableWith.of_comp_isEquivalence E hcomp

end AlgebraicGeometry.BasedFunctor
