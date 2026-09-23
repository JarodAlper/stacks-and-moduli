module

public import StacksAndModuli.API.TwoYonedaReconstruction
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»

/-!
# Cartesian lifts and the 2-Yoneda correspondence

A cartesian arrow between two objects of a prestack identifies the morphism represented
by its source with the pullback of the morphism represented by its target.  This file
records that concrete form of the 2-Yoneda correspondence.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {X : BasedCategory.{v₂, u₂} C} [X.p.IsFiberedInGroupoids]

/-- A cartesian arrow from `x` to `y` over `f : S ⟶ T` induces the expected
isomorphism between the morphism represented by `x` and the pullback along `f` of the
morphism represented by `y`. -/
noncomputable def twoYonedaPullbackIsoOfIsHomLift
    {S T : C} (f : S ⟶ T) (x : X.p.Fiber S) (y : X.p.Fiber T)
    (q : x.1 ⟶ y.1) [IsHomLift X.p f q] :
    twoYonedaPullback S x ≅
      (overBased.map f).comp (twoYonedaPullback T y) := by
  let L := twoYonedaPullback S x
  let R := (overBased.map f).comp (twoYonedaPullback T y)
  let E := twoYonedaEval (𝒳 := X) S
  let πx := IsPreFibered.pullbackMap x.2 (𝟙 S)
  let πy := IsPreFibered.pullbackMap y.2
    ((overBased.map f).obj (Over.mk (𝟙 S))).hom
  haveI hπx : IsHomLift X.p (𝟙 S) πx := inferInstance
  haveI hπxq : IsHomLift X.p f (πx ≫ q) := by
    simpa [πx] using IsHomLift.comp X.p (𝟙 S) f πx q
  haveI hπy : IsHomLift X.p
      ((overBased.map f).obj (Over.mk (𝟙 S))).hom πy := inferInstance
  let ε := IsStronglyCartesian.map X.p
    ((overBased.map f).obj (Over.mk (𝟙 S))).hom πy
    (show f = (𝟙 S) ≫ ((overBased.map f).obj (Over.mk (𝟙 S))).hom by
      simp [overBased.map]) (πx ≫ q)
  let e : E.obj L ≅ E.obj R :=
    asIso (Fiber.homMk X.p S ε)
  letI : E.Full := (isEquivalence_twoYonedaEval (𝒳 := X) S).full
  letI : E.Faithful := (isEquivalence_twoYonedaEval (𝒳 := X) S).faithful
  let α : L ⟶ R := E.preimage e.hom
  let β : R ⟶ L := E.preimage e.inv
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
