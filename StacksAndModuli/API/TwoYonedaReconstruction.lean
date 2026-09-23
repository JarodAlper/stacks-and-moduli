module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.4-two-yoneda-lemma»

/-!
# Reconstructing a morphism of prestacks from its value at the identity

The 2-Yoneda equivalence is packaged in the book files as an equivalence theorem for
the evaluation functor.  This file records the corresponding concrete reconstruction
isomorphism using the chosen cartesian-pullback quasi-inverse.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {X : BasedCategory.{v₂, u₂} C} [X.p.IsFiberedInGroupoids]

/-- A morphism out of a representable prestack is isomorphic to the morphism obtained
by evaluating it at the identity and then taking the chosen cartesian pullbacks. -/
noncomputable def twoYonedaPullbackEvalIso {S : C} (F : overBased S ⥤ᵇ X) :
    twoYonedaPullback S ((twoYonedaEval (𝒳 := X) S).obj F) ≅ F := by
  let E := twoYonedaEval (𝒳 := X) S
  let a := E.obj F
  let π := IsPreFibered.pullbackMap a.2 (𝟙 S)
  have hπ : IsHomLift X.p (𝟙 S) π := inferInstance
  let e : E.obj (twoYonedaPullback S a) ≅ E.obj F :=
    asIso (⟨π, hπ⟩ : E.obj (twoYonedaPullback S a) ⟶ E.obj F)
  letI : E.Full := (isEquivalence_twoYonedaEval (𝒳 := X) S).full
  letI : E.Faithful := (isEquivalence_twoYonedaEval (𝒳 := X) S).faithful
  let α : twoYonedaPullback S a ⟶ F := E.preimage e.hom
  let β : F ⟶ twoYonedaPullback S a := E.preimage e.inv
  exact
    { hom := α
      inv := β
      hom_inv_id := by
        apply E.map_injective
        rw [E.map_comp, E.map_preimage, E.map_preimage, e.hom_inv_id,
          E.map_id]
      inv_hom_id := by
        apply E.map_injective
        rw [E.map_comp, E.map_preimage, E.map_preimage, e.inv_hom_id,
          E.map_id] }

end CategoryTheory.BasedCategory
