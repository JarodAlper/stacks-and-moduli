module

public import StacksAndModuli.API.BasedFunctorEquivalence
public import StacksAndModuli.API.FiberProductEquivalence
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»

/-!
# Relative representability under an equivalence of sources

Precomposing a morphism of prestacks by an equivalence does not change its base changes
up to equivalence.  This file packages that observation for relative representability,
including properties of the induced morphisms of representing objects.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedFunctor

open CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {𝒜 : BasedCategory.{v₂, u₂} C}
  {𝒜' : BasedCategory.{v₃, u₃} C}
  {𝒴 : BasedCategory.{v₄, u₄} C}

/-- Relative representability with a morphism property is invariant under replacing
the source by an equivalent prestack. -/
theorem RelativelyRepresentableWith.comp_of_isEquivalence
    {P : MorphismProperty C} {F : BasedFunctor 𝒜 𝒴}
    (hF : F.RelativelyRepresentableWith P) (E : BasedFunctor 𝒜' 𝒜)
    [𝒜'.p.IsFiberedInGroupoids] [𝒜.p.IsFiberedInGroupoids]
    [𝒴.p.IsFiberedInGroupoids] [E.toFunctor.IsEquivalence]
    : (E.comp F).RelativelyRepresentableWith P := by
  classical
  refine ⟨?_, ?_⟩
  · intro S g
    obtain ⟨S', R, hR⟩ := hF.1 S g
    let K := fiberProductLeftMap F g E
    have hK : K.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductLeftMap F g E
    let _ : K.toFunctor.IsEquivalence := hK
    obtain ⟨L, ⟨α⟩, ⟨β⟩⟩ :=
      CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor K
    have hL : L.toFunctor.IsEquivalence := by
      exact Functor.IsEquivalence.mk' K.toFunctor
        ((BasedNatTrans.forgetful _ _).mapIso β).symm
        ((BasedNatTrans.forgetful _ _).mapIso α)
    exact ⟨S', R.comp L, Functor.isEquivalence_trans R.toFunctor L.toFunctor⟩
  · intro S g S' R hR
    let K := fiberProductLeftMap F g E
    have hK : K.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductLeftMap F g E
    have hRK : (R.comp K).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans R.toFunctor K.toFunctor
    have hP := hF.2 S g S' (R.comp K) hRK
    simpa [K, CategoryTheory.BasedFunctor.comp_assoc,
      fiberProductLeftMap_comp_fiberProductSnd] using hP

end CategoryTheory.BasedFunctor
