module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# Mapping module objects along monoidal functors

Mathlib maps monoid objects along lax monoidal functors but does not yet provide the
parallel construction for module objects.  This file supplies the object-level
construction.  For monoidal functors between cartesian monoidal categories it also
shows that the simply-transitive action map is preserved.
-/

@[expose] public section

open CategoryTheory MonoidalCategory MonObj
open scoped CategoryTheory.Obj ModObj MonoidalLeftAction

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  (F : Functor C D) [F.LaxMonoidal]
  (M X : C) [MonObj M] [ModObj M X]

/-- A lax monoidal functor maps an internal module object to a module over the
mapped monoid object. -/
abbrev mapModObj : ModObj (F.obj M) (F.obj X) where
  smul := LaxMonoidal.μ F M X ≫ F.map γ[M, X]
  one_smul := by
    simp [← F.map_comp]
  mul_smul := by
    change
      ((LaxMonoidal.μ F M M ≫ F.map μ[M]) ▷ F.obj X) ≫
          LaxMonoidal.μ F M X ≫ F.map γ[M, X] =
        (α_ (F.obj M) (F.obj M) (F.obj X)).hom ≫
          (F.obj M ◁ (LaxMonoidal.μ F M X ≫ F.map γ[M, X])) ≫
          LaxMonoidal.μ F M X ≫ F.map γ[M, X]
    simp_rw [comp_whiskerRight, Category.assoc,
      LaxMonoidal.μ_natural_left_assoc,
      MonoidalCategory.whiskerLeft_comp, Category.assoc,
      LaxMonoidal.μ_natural_right_assoc]
    slice_lhs 3 4 => rw [← F.map_comp, ModObj.mul_smul_self]
    simp

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [CartesianMonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [CartesianMonoidalCategory D]
  (F : Functor C D) [F.Monoidal]
  (M X : C) [MonObj M] [ModObj M X]

open CartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false in
/-- Under the mapped module structure, the action graph is the image of the
original action graph, conjugated by the product comparison isomorphisms. -/
lemma map_leftSMul :
    letI := F.mapModObj M X
    ModObj.leftSMul (F.obj M) (F.obj X) =
      LaxMonoidal.μ F M X ≫ F.map (ModObj.leftSMul M X) ≫
        CategoryTheory.inv (LaxMonoidal.μ F X X) := by
  letI := F.mapModObj M X
  ext
  · rw [← cancel_epi (prodComparisonIso F M X).hom]
    simp [ModObj.leftSMul, Monoidal.μ_of_cartesianMonoidalCategory,
      CartesianMonoidalCategory.prodComparison]
    rw [show lift (F.map (fst M X)) (F.map (snd M X)) =
      (prodComparisonIso F M X).hom by rfl, Iso.hom_inv_id_assoc]
    change prodComparison F M X ≫
      (LaxMonoidal.μ F M X ≫ F.map γ[M, X]) =
        F.map (ModObj.leftSMul M X) ≫ F.map (fst X X)
    rw [Monoidal.μ_of_cartesianMonoidalCategory,
      show prodComparison F M X = (prodComparisonIso F M X).hom by rfl,
      Iso.hom_inv_id_assoc, ← F.map_comp]
    simp [ModObj.leftSMul]
  · rw [← cancel_epi (prodComparisonIso F M X).hom]
    simp [ModObj.leftSMul, Monoidal.μ_of_cartesianMonoidalCategory,
      CartesianMonoidalCategory.prodComparison]
    rw [show lift (F.map (fst M X)) (F.map (snd M X)) =
      (prodComparisonIso F M X).hom by rfl, Iso.hom_inv_id_assoc,
      ← F.map_comp]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- A monoidal functor between cartesian monoidal categories preserves a
simply-transitive internal action. -/
lemma isIso_map_leftSMul [IsIso (ModObj.leftSMul M X)] :
    letI := F.mapModObj M X
    IsIso (ModObj.leftSMul (F.obj M) (F.obj X)) := by
  letI := F.mapModObj M X
  rw [map_leftSMul F M X]
  infer_instance

end CategoryTheory.Functor
