module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pullbacks of internal module objects

In a cartesian monoidal category with pullbacks, the pullback of two equivariant
maps carries the componentwise action.  This elementary construction is useful for
base-changing group actions while keeping the acting group fixed.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe v u

namespace CategoryTheory.ModObj

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  [HasPullbacks C]
variable (M : C) [MonObj M]
variable {X Y Z : C} [ModObj M X] [ModObj M Y] [ModObj M Z]

/-- The componentwise action on the pullback of two equivariant maps. -/
@[instance_reducible]
noncomputable def pullbackAction (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsModHom M f] [IsModHom M g] : ModObj M (pullback f g) where
  smul := pullback.lift
    ((M ◁ pullback.fst f g) ≫ γ[M, X])
    ((M ◁ pullback.snd f g) ≫ γ[M, Y])
    (by
      rw [Category.assoc, IsModHom.smul_hom,
        Category.assoc, IsModHom.smul_hom]
      change (M ◁ pullback.fst f g) ≫ (M ◁ f) ≫ γ[M, Z] =
        (M ◁ pullback.snd f g) ≫ (M ◁ g) ≫ γ[M, Z]
      slice_lhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp]
      slice_rhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp]
      rw [pullback.condition])
  one_smul := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      change (η[M] ▷ pullback f g) ≫ (M ◁ pullback.fst f g) ≫ γ[M, X] =
        (λ_ (pullback f g)).hom ≫ pullback.fst f g
      slice_lhs 1 2 => rw [← MonoidalCategory.whisker_exchange]
      simp
    · rw [Category.assoc, pullback.lift_snd]
      change (η[M] ▷ pullback f g) ≫ (M ◁ pullback.snd f g) ≫ γ[M, Y] =
        (λ_ (pullback f g)).hom ≫ pullback.snd f g
      slice_lhs 1 2 => rw [← MonoidalCategory.whisker_exchange]
      simp
  mul_smul := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst]
      change (μ[M] ▷ pullback f g) ≫ (M ◁ pullback.fst f g) ≫ γ[M, X] = _
      slice_lhs 1 2 => rw [← MonoidalCategory.whisker_exchange]
      simp
      slice_rhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp]
      rw [pullback.lift_fst, MonoidalCategory.whiskerLeft_comp_assoc]
    · rw [Category.assoc, pullback.lift_snd]
      change (μ[M] ▷ pullback f g) ≫ (M ◁ pullback.snd f g) ≫ γ[M, Y] = _
      slice_lhs 1 2 => rw [← MonoidalCategory.whisker_exchange]
      simp
      slice_rhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp]
      rw [pullback.lift_snd, MonoidalCategory.whiskerLeft_comp_assoc]

/-- Every morphism between objects with the trivial action is equivariant. -/
lemma isModHom_trivialAction {A B : C} (f : A ⟶ B) :
    @IsModHom C _ _ C _ (inferInstance : MonoidalLeftAction C C)
      M _ A B (ModObj.trivialAction M A) (ModObj.trivialAction M B) f := by
  exact @IsModHom.mk C _ _ C _ _ M _ A B
    (ModObj.trivialAction M A) (ModObj.trivialAction M B) f (by
      change snd M A ≫ f = (M ◁ f) ≫ snd M B
      simp)

/-- The first projection from an equivariant pullback is equivariant. -/
lemma isModHom_pullback_fst (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsModHom M f] [IsModHom M g] :
    letI := pullbackAction M f g
    IsModHom M (pullback.fst f g) := by
  letI := pullbackAction M f g
  constructor
  exact pullback.lift_fst _ _ _

/-- The second projection from an equivariant pullback is equivariant. -/
lemma isModHom_pullback_snd (f : X ⟶ Z) (g : Y ⟶ Z)
    [IsModHom M f] [IsModHom M g] :
    letI := pullbackAction M f g
    IsModHom M (pullback.snd f g) := by
  letI := pullbackAction M f g
  constructor
  exact pullback.lift_snd _ _ _

/-- A pair of equivariant maps with equal composites induces an equivariant map
to the equivariant pullback. -/
lemma isModHom_pullback_lift {W : C} [ModObj M W]
    (f : X ⟶ Z) (g : Y ⟶ Z) [IsModHom M f] [IsModHom M g]
    (a : W ⟶ X) (b : W ⟶ Y) (h : a ≫ f = b ≫ g)
    [IsModHom M a] [IsModHom M b] :
    letI := pullbackAction M f g
    IsModHom M (pullback.lift a b h) := by
  letI := pullbackAction M f g
  constructor
  change γ[M, W] ≫ pullback.lift a b h =
    (M ◁ pullback.lift a b h) ≫
      pullback.lift ((M ◁ pullback.fst f g) ≫ γ[M, X])
        ((M ◁ pullback.snd f g) ≫ γ[M, Y]) _
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst, IsModHom.smul_hom]
    slice_rhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp]
    rw [pullback.lift_fst]
    rfl
  · simp only [Category.assoc, pullback.lift_snd, IsModHom.smul_hom]
    slice_rhs 1 2 => rw [← MonoidalCategory.whiskerLeft_comp]
    rw [pullback.lift_snd]
    rfl

end CategoryTheory.ModObj
