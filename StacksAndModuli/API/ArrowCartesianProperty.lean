module

public import StacksAndModuli.API.ArrowCartesian
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Pullback-stable full subfibrations of the cartesian-arrow fibration

For a morphism property `P` stable under base change, this file restricts the
cartesian-arrow fibration to arrows satisfying `P`.  Its objects are `P`-morphisms,
its morphisms are cartesian squares, and its projection remembers the target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe v u

variable {C : Type u} [Category.{v} C]

namespace CategoryTheory

/-- The object property on the cartesian-arrow category associated to a morphism
property on the underlying category. -/
def ArrowCartesian.property (P : MorphismProperty C) :
    ObjectProperty (ArrowCartesian C) :=
  fun f => P (f : Arrow C).hom

/-- The full based subcategory of the cartesian-arrow fibration consisting of
arrows satisfying `P`. -/
def arrowCartesianProperty (P : MorphismProperty C) : BasedCategory C where
  obj := (ArrowCartesian.property P).FullSubcategory
  p := (ArrowCartesian.property P).ι ⋙ (arrowCartesian C).p

namespace arrowCartesianProperty

variable (P : MorphismProperty C)

/-- A pullback-stable property of arrows defines a prestack: its cartesian
pullback along any base morphism still has the property. -/
instance [HasPullbacks C] [P.IsStableUnderBaseChange] :
    (arrowCartesianProperty P).p.IsFiberedInGroupoids := by
  constructor
  · intro a R f
    let b₀ : ArrowCartesian C :=
      ArrowCartesian.mk (pullback.snd (a.obj : Arrow C).hom f)
    let φ₀ : b₀ ⟶ a.obj :=
      { left := pullback.fst (a.obj : Arrow C).hom f
        right := f
        isPullback := IsPullback.of_hasPullback (a.obj : Arrow C).hom f }
    have hb₀ : ArrowCartesian.property P b₀ := by
      exact P.of_isPullback φ₀.isPullback a.property
    let b : (ArrowCartesian.property P).FullSubcategory := ⟨b₀, hb₀⟩
    let φ : b ⟶ a := ObjectProperty.homMk φ₀
    refine ⟨b, φ, ?_⟩
    change IsHomLift ((ArrowCartesian.property P).ι ⋙ (arrowCartesian C).p) f φ
    have hf : f = ((ArrowCartesian.property P).ι ⋙ (arrowCartesian C).p).map φ := by
      rfl
    rw [hf]
    infer_instance
  · intro a b φ
    let φ₀ : a.obj ⟶ b.obj := φ.hom
    letI hφlift : IsHomLift (arrowCartesian C).p φ₀.right φ₀ := by
      change IsHomLift (arrowCartesian C).p ((arrowCartesian C).p.map φ₀) φ₀
      infer_instance
    letI hφ₀ : IsStronglyCartesian (arrowCartesian C).p φ₀.right φ₀ :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift _ _ _
    constructor
    intro c g ψ hψ
    letI hψlift : IsHomLift
        ((ArrowCartesian.property P).ι ⋙ (arrowCartesian C).p)
        (g ≫ ((ArrowCartesian.property P).ι ⋙ (arrowCartesian C).p).map φ) ψ := hψ
    let ψ₀ : c.obj ⟶ b.obj := ψ.hom
    have hgfac : g ≫ φ₀.right = ψ₀.right := by
      have h := IsHomLift.eq_of_isHomLift
        ((ArrowCartesian.property P).ι ⋙ (arrowCartesian C).p)
        (g ≫ ((ArrowCartesian.property P).ι ⋙ (arrowCartesian C).p).map φ) ψ
      exact h
    haveI hψ₀ : IsHomLift (arrowCartesian C).p (g ≫ φ₀.right) ψ₀ := by
      rw [hgfac]
      change IsHomLift (arrowCartesian C).p ((arrowCartesian C).p.map ψ₀) ψ₀
      infer_instance
    obtain ⟨χ₀, hχ₀, huniq⟩ :=
      IsStronglyCartesian.universal_property' (p := (arrowCartesian C).p)
        (f := φ₀.right) (φ := φ₀) g ψ₀
    let χ : c ⟶ a := ObjectProperty.homMk χ₀
    letI hχ₀lift : IsHomLift (arrowCartesian C).p g χ₀ := hχ₀.1
    refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
    · change IsHomLift ((ArrowCartesian.property P).ι ⋙ (arrowCartesian C).p) g χ
      have hg : g = ((ArrowCartesian.property P).ι ⋙ (arrowCartesian C).p).map χ := by
        exact IsHomLift.eq_of_isHomLift (arrowCartesian C).p g χ₀
      rw [hg]
      infer_instance
    · apply ObjectProperty.hom_ext
      exact hχ₀.2
    · intro χ' hχ'
      apply ObjectProperty.hom_ext
      apply huniq χ'.hom
      refine ⟨?_, ?_⟩
      · have h := hχ'.1
        change IsHomLift ((ArrowCartesian.property P).ι ⋙ (arrowCartesian C).p) g χ' at h
        have hg : g = ((ArrowCartesian.property P).ι ⋙ (arrowCartesian C).p).map χ' :=
          @IsHomLift.eq_of_isHomLift _ _ _ _
            ((ArrowCartesian.property P).ι ⋙ (arrowCartesian C).p) _ _ g χ' h
        apply IsHomLift.of_fac (arrowCartesian C).p g χ'.hom rfl rfl
        simpa using hg
      · exact congrArg InducedCategory.Hom.hom hχ'.2

/-- A refinement `P ≤ Q` of morphism properties refines the corresponding object property
on the cartesian-arrow category. -/
lemma property_monotone {P Q : MorphismProperty C} (h : P ≤ Q) :
    ArrowCartesian.property P ≤ ArrowCartesian.property Q :=
  fun _ hf ↦ h _ hf

/-- A refinement `P ≤ Q` of morphism properties induces a based functor between the
corresponding full subfibrations of the cartesian-arrow fibration. -/
def ιOfLE {P Q : MorphismProperty C} (h : P ≤ Q) :
    arrowCartesianProperty P ⥤ᵇ arrowCartesianProperty Q where
  toFunctor := ObjectProperty.ιOfLE (property_monotone h)
  w := rfl

/-- The inclusion of a refinement is fully faithful: the smaller subfibration is a *full*
subcategory of the larger one. -/
def fullyFaithfulιOfLE {P Q : MorphismProperty C} (h : P ≤ Q) :
    (ιOfLE h).toFunctor.FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE (property_monotone h)

instance ιOfLE_full {P Q : MorphismProperty C} (h : P ≤ Q) :
    (ιOfLE h).toFunctor.Full :=
  (fullyFaithfulιOfLE h).full

instance ιOfLE_faithful {P Q : MorphismProperty C} (h : P ≤ Q) :
    (ιOfLE h).toFunctor.Faithful :=
  (fullyFaithfulιOfLE h).faithful

@[simp]
lemma ιOfLE_obj {P Q : MorphismProperty C} (h : P ≤ Q)
    (a : (ArrowCartesian.property P).FullSubcategory) :
    ((ιOfLE h).obj a).obj = a.obj := rfl

end arrowCartesianProperty

end CategoryTheory
