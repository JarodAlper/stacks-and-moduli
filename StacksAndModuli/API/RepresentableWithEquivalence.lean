module

public import StacksAndModuli.API.BasedFunctorEquivalence
public import StacksAndModuli.API.FiberProductEquivalence
public import StacksAndModuli.API.FiberProductLegIso
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»

/-!
# Representability with properties under equivalences

This file shows that `RepresentableWith P` is unchanged by replacing the source
prestack by an equivalent one or by replacing the morphism by a 2-isomorphic morphism.
No locality hypothesis on `P` is needed: the comparison equivalences preserve the
projection from each base change to its test scheme.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor
open CategoryTheory.BasedCategory

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {X : BasedCategory.{v₁, u₁} Scheme.{u}}
  {X' : BasedCategory.{v₂, u₂} Scheme.{u}}
  {Y : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- Precomposing with an equivalence of source prestacks preserves representability
with every morphism property. -/
theorem RepresentableWith.comp_source_isEquivalence
    {P : MorphismProperty Scheme.{u}} {F : BasedFunctor X Y}
    (hF : RepresentableWith P F) (E : BasedFunctor X' X)
    [X'.p.IsFiberedInGroupoids] [X.p.IsFiberedInGroupoids]
    [Y.p.IsFiberedInGroupoids] [E.toFunctor.IsEquivalence] :
    RepresentableWith P (E.comp F) := by
  refine ⟨?_, ?_⟩
  · intro T g
    obtain ⟨Z, hZ, R, hR⟩ := hF.1 T g
    let K := fiberProductLeftMap F g E
    have hK : K.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductLeftMap F g E
    let _ : K.toFunctor.IsEquivalence := hK
    obtain ⟨J, ⟨α⟩, ⟨β⟩⟩ :=
      CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor K
    have hJ : J.toFunctor.IsEquivalence :=
      Functor.IsEquivalence.mk' K.toFunctor
        ((BasedNatTrans.forgetful _ _).mapIso β).symm
        ((BasedNatTrans.forgetful _ _).mapIso α)
    exact ⟨Z, hZ, R.comp J,
      Functor.isEquivalence_trans R.toFunctor J.toFunctor⟩
  · intro T g Z hZ R hR U q hq
    let K := fiberProductLeftMap F g E
    have hK : K.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductLeftMap F g E
    have hRK : (R.comp K).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans R.toFunctor K.toFunctor
    have hP := hF.2 T g Z hZ (R.comp K) hRK U q hq
    simpa [K, CategoryTheory.BasedFunctor.comp_assoc,
      fiberProductLeftMap_comp_fiberProductSnd] using hP

/-- Representability with a morphism property is invariant under a based natural
isomorphism. -/
theorem RepresentableWith.of_iso {P : MorphismProperty Scheme.{u}}
    {F G : BasedFunctor X Y} (hF : RepresentableWith P F) (e : F ≅ G)
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids] :
    RepresentableWith P G := by
  refine ⟨?_, ?_⟩
  · intro T g
    obtain ⟨Z, hZ, R, hR⟩ := hF.1 T g
    let K := fiberProductMapLeftIso e g
    have hK : K.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductMapLeftIso e g
    exact ⟨Z, hZ, R.comp K,
      Functor.isEquivalence_trans R.toFunctor K.toFunctor⟩
  · intro T g Z hZ R hR U q hq
    let K := fiberProductMapLeftIso e.symm g
    have hK : K.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductMapLeftIso e.symm g
    have hRK : (R.comp K).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans R.toFunctor K.toFunctor
    have hP := hF.2 T g Z hZ (R.comp K) hRK U q hq
    have hproj : K.comp (BasedCategory.fiberProductSnd F g) =
        BasedCategory.fiberProductSnd G g :=
      CategoryTheory.BasedFunctor.ext_of_toFunctor_eq rfl
    simpa [CategoryTheory.BasedFunctor.comp_assoc, hproj] using hP

/-- If precomposition by an equivalence is representable with a property, then the
original morphism is representable with that property. -/
theorem RepresentableWith.of_comp_isEquivalence
    {P : MorphismProperty Scheme.{u}} {F : BasedFunctor X Y}
    (E : BasedFunctor X' X)
    [X'.p.IsFiberedInGroupoids] [X.p.IsFiberedInGroupoids]
    [Y.p.IsFiberedInGroupoids] [E.toFunctor.IsEquivalence]
    (hEF : RepresentableWith P (E.comp F)) : RepresentableWith P F := by
  obtain ⟨J, ⟨α⟩, ⟨β⟩⟩ :=
    CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor E
  have hJ : J.toFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk' E.toFunctor
      ((BasedNatTrans.forgetful _ _).mapIso β).symm
      ((BasedNatTrans.forgetful _ _).mapIso α)
  let _ : J.toFunctor.IsEquivalence := hJ
  have hcomp := hEF.comp_source_isEquivalence J
  let e : J.comp (E.comp F) ≅ F :=
    (eqToIso (CategoryTheory.BasedFunctor.comp_assoc J E F).symm).trans
      ((BasedCategory.isoWhiskerRight β F).trans
        (eqToIso (CategoryTheory.BasedFunctor.id_comp F)))
  exact hcomp.of_iso e

end AlgebraicGeometry.BasedFunctor
