module

public import StacksAndModuli.API.AlgebraicSpaceAtlasComposition
public import StacksAndModuli.API.AlgebraicStackDiagonal
public import StacksAndModuli.API.FiberProductPresentationProperty

/-!
# Scheme presentations of fiber products of algebraic stacks

This file packages the presentation step in the proof that algebraic stacks are closed
under fiber products.  Given presentations of the two outer prestacks, the product of
their presentation maps first presents an algebraic-space fiber of the middle stack's
diagonal.  An étale scheme atlas of that algebraic space then gives a presentation of the
original fiber product.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe vX uX vY uY vY' uY' u

namespace AlgebraicGeometry

/-- If the product of two presentation morphisms has a property `P`, then those
presentations induce a scheme presentation with property `P` of the corresponding
fiber product.  The property need only be local on the source for surjective étale
morphisms. -/
theorem exists_fiberProduct_presentation
    {P : MorphismProperty Scheme.{u}}
    {X : BasedCategory.{vX, uX} Scheme.{u}}
    {Y : BasedCategory.{vY, uY} Scheme.{u}}
    {Y' : BasedCategory.{vY', uY'} Scheme.{u}}
    [IsAlgebraicStack Y]
    [X.p.IsFiberedInGroupoids] [Y'.p.IsFiberedInGroupoids]
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    {U V : Scheme.{u}}
    {pX : overBased U ⥤ᵇ X} {pY : overBased V ⥤ᵇ Y'}
    (hprod : BasedFunctor.RepresentableWith P (prodMap pX pY))
    (hlocal : ∀ ⦃S' S T : Scheme.{u}⦄ (p : S' ⟶ S) (f : S ⟶ T),
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p →
        (P f ↔ P (p ≫ f))) :
    ∃ (W : Scheme.{u}) (J : overBased W ⥤ᵇ fiberProduct F G),
      BasedFunctor.RepresentableWith P J := by
  have hΔ := IsAlgebraicStack.representable_diag_of_presentation Y
  obtain ⟨A, hA, hrep⟩ :=
    exists_isAlgebraicSpace_fiberProduct_of_representableDiagonal
      (pX.comp F) (pY.comp G) hΔ
  obtain ⟨E, hE⟩ := hrep
  let _ : IsAlgebraicSpace A := hA
  let _ : E.toFunctor.IsEquivalence := hE
  obtain ⟨W, q, hq⟩ := IsAlgebraicSpace.exists_presentation (X := A)
  have hcanonical :=
    BasedFunctor.RepresentableWith.fiberProductPresentationMap_of_prodMap
      (F := F) (G := G) (P := pX) (Q := pY) hprod
  have hcomparison := hcanonical.comp_source_isEquivalence E
  have hpresentation :=
    hcomparison.comp_algebraicSpacePresentation hq hlocal
  exact ⟨W, _, hpresentation⟩

end AlgebraicGeometry
