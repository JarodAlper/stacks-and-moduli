module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.1-definition-of-a-prestack»
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The cartesian-arrow fibration

This file packages the category whose objects are arrows of a category and whose
morphisms are pullback squares.  It is kept in the API because the construction and
its fibered-in-groupoids proof are useful independently of the Zariski stack theorem.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe v u

variable {C : Type u} [Category.{v} C]

/-- The type of arrows of `C`, equipped below with cartesian squares as morphisms. -/
def CategoryTheory.ArrowCartesian (C : Type u) [Category.{v} C] := Arrow C

/-- A morphism between arrows whose defining square is a pullback. -/
@[ext]
structure CategoryTheory.CartesianArrowHom (a b : Arrow C) where
  /-- The morphism on total spaces. -/
  left : a.left ⟶ b.left
  /-- The morphism on bases. -/
  right : a.right ⟶ b.right
  /-- The square is cartesian. -/
  isPullback : IsPullback left a.hom b.hom right

namespace CategoryTheory.CartesianArrowHom

/-- The identity cartesian square. -/
@[simps]
def id (a : Arrow C) : CartesianArrowHom a a where
  left := 𝟙 a.left
  right := 𝟙 a.right
  isPullback := IsPullback.of_horiz_isIso ⟨by simp⟩

/-- Composition of cartesian squares. -/
@[simps]
def comp {a b c : Arrow C} (φ : CartesianArrowHom a b) (ψ : CartesianArrowHom b c) :
    CartesianArrowHom a c where
  left := φ.left ≫ ψ.left
  right := φ.right ≫ ψ.right
  isPullback := φ.isPullback.paste_horiz ψ.isPullback

end CategoryTheory.CartesianArrowHom

/-- The category structure whose morphisms are cartesian squares. -/
instance CategoryTheory.ArrowCartesian.instCategory :
    Category (ArrowCartesian C) where
  Hom a b := CartesianArrowHom a b
  id a := CartesianArrowHom.id a
  comp φ ψ := φ.comp ψ
  id_comp φ := by ext <;> simp [CartesianArrowHom.id, CartesianArrowHom.comp]
  comp_id φ := by ext <;> simp [CartesianArrowHom.id, CartesianArrowHom.comp]
  assoc φ ψ χ := by ext <;> simp [CartesianArrowHom.comp, Category.assoc]

/-- The object associated to a morphism of `C`. -/
def CategoryTheory.ArrowCartesian.mk {X S : C} (f : X ⟶ S) : ArrowCartesian C :=
  Arrow.mk f

/-- The cartesian-arrow category based over `C` by remembering the target. -/
def CategoryTheory.arrowCartesian (C : Type u) [Category.{v} C] : BasedCategory C where
  obj := ArrowCartesian C
  p :=
    { obj := fun a ↦ (a : Arrow C).right
      map := fun φ ↦ CartesianArrowHom.right φ
      map_id := fun a ↦ rfl
      map_comp := fun φ ψ ↦ rfl }

/-- With pullbacks, the cartesian-arrow projection is fibered in groupoids. -/
instance CategoryTheory.arrowCartesian_isFiberedInGroupoids [HasPullbacks C] :
    (arrowCartesian C).p.IsFiberedInGroupoids := by
  constructor
  · intro a R f
    let b : ArrowCartesian C :=
      ArrowCartesian.mk (pullback.snd (a : Arrow C).hom f)
    let φ : b ⟶ a :=
      { left := pullback.fst (a : Arrow C).hom f
        right := f
        isPullback := IsPullback.of_hasPullback (a : Arrow C).hom f }
    refine ⟨b, φ, ?_⟩
    have hf : f = (arrowCartesian C).p.map φ := by
      change f = φ.right
      rfl
    rw [hf]
    infer_instance
  · intro a b φ
    constructor
    intro c g ψ hψ
    have hg : g ≫ φ.right = ψ.right := by
      have hbase := IsHomLift.eq_of_isHomLift (arrowCartesian C).p
        (g ≫ (arrowCartesian C).p.map φ) ψ
      change g ≫ φ.right = ψ.right at hbase
      exact hbase
    have hw : ψ.left ≫ (b : Arrow C).hom =
        ((c : Arrow C).hom ≫ g) ≫ φ.right := by
      calc
        ψ.left ≫ (b : Arrow C).hom = (c : Arrow C).hom ≫ ψ.right :=
          ψ.isPullback.w
        _ = (c : Arrow C).hom ≫ (g ≫ φ.right) := by rw [hg]
        _ = ((c : Arrow C).hom ≫ g) ≫ φ.right := Category.assoc _ _ _ |>.symm
    let χleft : (c : Arrow C).left ⟶ (a : Arrow C).left :=
      φ.isPullback.lift ψ.left ((c : Arrow C).hom ≫ g) hw
    have hχleft : χleft ≫ φ.left = ψ.left := φ.isPullback.lift_fst _ _ _
    have hχright : χleft ≫ (a : Arrow C).hom = (c : Arrow C).hom ≫ g :=
      φ.isPullback.lift_snd _ _ _
    have hχpb : IsPullback χleft (c : Arrow C).hom (a : Arrow C).hom g := by
      have hout : IsPullback (χleft ≫ φ.left) (c : Arrow C).hom
          (b : Arrow C).hom (g ≫ φ.right) := by
        simpa only [hχleft, hg] using ψ.isPullback
      exact hout.of_right hχright φ.isPullback
    let χ : c ⟶ a :=
      { left := χleft
        right := g
        isPullback := hχpb }
    refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
    · have hgχ : g = (arrowCartesian C).p.map χ := by
        change g = χ.right
        rfl
      rw [hgχ]
      infer_instance
    · apply CartesianArrowHom.ext
      · exact hχleft
      · exact hg
    · intro χ' hχ'
      obtain ⟨hχ'lift, hχ'fac⟩ := hχ'
      have hright : χ'.right = g := by
        exact (IsHomLift.eq_of_isHomLift (arrowCartesian C).p g χ').symm
      apply CartesianArrowHom.ext
      · apply φ.isPullback.hom_ext
        · have h := congrArg CartesianArrowHom.left hχ'fac
          change χ'.left ≫ φ.left = ψ.left at h
          simpa [χ, χleft] using h
        · rw [χ'.isPullback.w, hright, hχright]
      · exact hright

end
