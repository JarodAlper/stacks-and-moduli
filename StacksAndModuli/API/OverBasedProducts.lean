module

public import StacksAndModuli.API.PrestackProducts
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»

/-!
# Products of representable prestacks

This file constructs the canonical comparison from the prestack represented by a
binary product to the product of the two representable prestacks.  The comparison is
an equivalence.  This is supporting API for the magic-square representability argument
of §4.2 of *Stacks and Moduli*.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits

universe v u

namespace CategoryTheory.BasedCategory

variable {C : Type u} [Category.{v} C]

/-- A morphism in an over-category lifts every base morphism lifted by its underlying
arrow. -/
lemma over_isHomLift_of_left {T R R' : C} {x y : Over T} (f : R ⟶ R') (q : x ⟶ y)
    (h : IsHomLift (Functor.id C) f q.left) : IsHomLift (Over.forget T) f q := by
  let _ : IsHomLift (Functor.id C) f q.left := h
  apply IsHomLift.of_fac' (Over.forget T) f q
    (IsHomLift.domain_eq (Functor.id C) f q.left)
    (IsHomLift.codomain_eq (Functor.id C) f q.left)
  exact IsHomLift.fac' (Functor.id C) f q.left

/-- The canonical comparison from the representable prestack of a binary product to
the product of the two representable prestacks. -/
noncomputable def overBasedProdComparison (S T : C) [HasBinaryProduct S T] :
    BasedFunctor (overBased (S ⨯ T)) (prod (overBased S) (overBased T)) where
  obj x :=
    { fst := Over.mk (x.hom ≫ Limits.prod.fst)
      snd := Over.mk (x.hom ≫ Limits.prod.snd)
      over_eq := by
        change x.left = x.left
        rfl
      iso := Iso.refl x.left
      isHomLift := IsHomLift.id rfl }
  map {x y} q := by
    let q₁ : Over.mk (x.hom ≫ Limits.prod.fst) ⟶
        Over.mk (y.hom ≫ Limits.prod.fst) := Over.homMk q.left (by
        change q.left ≫ (y.hom ≫ Limits.prod.fst) = x.hom ≫ Limits.prod.fst
        rw [← Category.assoc, Over.w])
    let q₂ : Over.mk (x.hom ≫ Limits.prod.snd) ⟶
        Over.mk (y.hom ≫ Limits.prod.snd) := Over.homMk q.left (by
        change q.left ≫ (y.hom ≫ Limits.prod.snd) = x.hom ≫ Limits.prod.snd
        rw [← Category.assoc, Over.w])
    exact
      { fst := q₁
        snd := q₂
        isHomLift := by
          have h₂ : IsHomLift (Functor.id C) q.left q₂.left := by
            simpa [q₂] using (IsHomLift.map (p := Functor.id C) q.left)
          simpa [q₁] using over_isHomLift_of_left q.left q₂ h₂
        w := by
          change q.left ≫ 𝟙 _ = 𝟙 _ ≫ q.left
          simp }
  map_id x := by
    apply FiberProductHom.ext
    · apply Over.OverMorphism.ext
      rfl
    · apply Over.OverMorphism.ext
      rfl
  map_comp q r := by
    apply FiberProductHom.ext
    · apply Over.OverMorphism.ext
      rfl
    · apply Over.OverMorphism.ext
      rfl
  w := rfl

/-- The comparison from the representable prestack of a product is faithful. -/
lemma overBasedProdComparison_faithful (S T : C) [HasBinaryProduct S T] :
    (overBasedProdComparison S T).toFunctor.Faithful := by
  constructor
  intro x y f g h
  apply Over.OverMorphism.ext
  exact congrArg (fun k ↦ k.fst.left) h

/-- The comparison from the representable prestack of a product is full. -/
lemma overBasedProdComparison_full (S T : C) [HasBinaryProduct S T] :
    (overBasedProdComparison S T).toFunctor.Full := by
  constructor
  intro x y q
  have hsnd : q.snd.left = q.fst.left := by
    have h := q.w
    change q.fst.left ≫ 𝟙 _ = 𝟙 _ ≫ q.snd.left at h
    simpa using h.symm
  let r : x ⟶ y := Over.homMk q.fst.left (by
    apply Limits.prod.hom_ext
    · have h := Over.w q.fst
      change q.fst.left ≫ (y.hom ≫ Limits.prod.fst) = x.hom ≫ Limits.prod.fst at h
      simpa only [Category.assoc] using h
    · have h := Over.w q.snd
      change q.snd.left ≫ (y.hom ≫ Limits.prod.snd) = x.hom ≫ Limits.prod.snd at h
      rw [hsnd] at h
      simpa only [Category.assoc] using h)
  refine ⟨r, ?_⟩
  apply FiberProductHom.ext
  · apply Over.OverMorphism.ext
    rfl
  · apply Over.OverMorphism.ext
    exact hsnd.symm

/-- The comparison from the representable prestack of a product is essentially
surjective. -/
lemma overBasedProdComparison_essSurj (S T : C) [HasBinaryProduct S T] :
    (overBasedProdComparison S T).toFunctor.EssSurj := by
  constructor
  intro x
  let z : Over (S ⨯ T) := Over.mk (Limits.prod.lift x.fst.hom (x.iso.hom ≫ x.snd.hom))
  refine ⟨z, ⟨?_⟩⟩
  let e₁ : ((overBasedProdComparison S T).obj z).fst ≅ x.fst :=
    Over.isoMk (Iso.refl _) (by
      dsimp [overBasedProdComparison, z]
      simp)
  let ex : x.fst.left ≅ x.snd.left := x.iso
  let e₂ : ((overBasedProdComparison S T).obj z).snd ≅ x.snd :=
    Over.isoMk ex (by
      dsimp [overBasedProdComparison, z]
      exact (Limits.prod.lift_snd x.fst.hom (x.iso.hom ≫ x.snd.hom)).symm)
  apply FiberProductObj.isoMk e₁ e₂
  · let R : C := x.fst.left
    have h₁left : IsHomLift (Functor.id C) (𝟙 R) e₁.hom.left := by
      dsimp [e₁]
      exact IsHomLift.id rfl
    have h₁ := over_isHomLift_of_left (𝟙 R) e₁.hom h₁left
    have h₂left : IsHomLift (Functor.id C) (𝟙 R) e₂.hom.left := by
      have hx := x.isHomLift
      change IsHomLift (Functor.id C) (𝟙 x.fst.left) x.iso.hom at hx
      simpa [e₂, ex, R, z, overBasedProdComparison] using hx
    have h₂ := over_isHomLift_of_left (𝟙 R) e₂.hom h₂left
    exact isHomLift_map_of_common_lift (𝟙 R) e₁.hom e₂.hom h₁ h₂
  · change e₁.hom.left ≫ x.iso.hom =
      ((overBasedProdComparison S T).obj z).iso.hom ≫ e₂.hom.left
    rw [show e₁.hom.left = 𝟙 z.left by rfl,
      show e₂.hom.left = x.iso.hom by rfl,
      show ((overBasedProdComparison S T).obj z).iso.hom = 𝟙 z.left by rfl]

/-- A binary product represents the product of the two corresponding representable
prestacks. -/
theorem isEquivalence_overBasedProdComparison (S T : C) [HasBinaryProduct S T] :
    (overBasedProdComparison S T).toFunctor.IsEquivalence := by
  let _ := overBasedProdComparison_faithful S T
  let _ := overBasedProdComparison_full S T
  let _ := overBasedProdComparison_essSurj S T
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

end CategoryTheory.BasedCategory
