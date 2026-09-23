module

public import StacksAndModuli.API.RepresentableWithEquivalence

/-!
# Surjective étale presentations from equivalences

An equivalence of prestacks over schemes is a representable, surjective, and étale
morphism.  This supplies the presentation property for a scheme chart that represents a
fiber by an equivalence.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry.BasedFunctor

/-- The identity of a prestack is relatively representable, surjective, and étale. -/
lemma relativelyRepresentableWith_id_surjectiveEtale
    (X : BasedCategory.{v₁, u₁} Scheme.{u}) :
    (CategoryTheory.BasedFunctor.id X).RelativelyRepresentableWith
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) := by
  refine ⟨fun S g ↦ ⟨S, fiberProductIdInv g,
    isEquivalence_fiberProductIdInv g⟩, ?_⟩
  intro S g S' E hE
  have hSnd := isEquivalence_fiberProductSnd_id g
  have hcomp : Functor.IsEquivalence
      (E.comp (fiberProductSnd (CategoryTheory.BasedFunctor.id X) g)).toFunctor :=
    Functor.isEquivalence_trans E.toFunctor
      (fiberProductSnd (CategoryTheory.BasedFunctor.id X) g).toFunctor
  have hIso := CategoryTheory.BasedFunctor.isIso_overHom_of_isEquivalence _ hcomp
  exact ⟨inferInstance, inferInstance⟩

/-- An equivalence of prestacks over schemes is representable with the surjective
étale property. -/
theorem RepresentableWith.surjectiveEtale_of_isEquivalence
    {X : BasedCategory.{v₁, u₁} Scheme.{u}}
    {Y : BasedCategory.{v₂, u₂} Scheme.{u}}
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    (F : BasedFunctor X Y) [F.toFunctor.IsEquivalence] :
    RepresentableWith (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) F := by
  let _ : MorphismProperty.IsStableUnderComposition
      (@Surjective : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  let _ : MorphismProperty.IsStableUnderComposition
      (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  let _ : MorphismProperty.IsStableUnderComposition
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderComposition.inf
  have hId : RepresentableWith
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u})
      (CategoryTheory.BasedFunctor.id Y) :=
    RelativelyRepresentableWith.representableWith le_rfl
      (relativelyRepresentableWith_id_surjectiveEtale Y)
  have hcomp := RepresentableWith.comp_source_isEquivalence hId F
  exact RepresentableWith.of_iso hcomp
    (eqToIso (CategoryTheory.BasedFunctor.comp_id F))

end AlgebraicGeometry.BasedFunctor
