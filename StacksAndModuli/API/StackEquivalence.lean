module

public import StacksAndModuli.API.BasedFunctorEquivalence
public import StacksAndModuli.«Section3.5-Stacks».«part3.5.1-the-definition»

/-!
# Transporting stacks across equivalences over the base

The stack condition is invariant under equivalence of the total categories over the
site.  This file proves the direction used by relative Yoneda: a prestack equivalent over
the base to a stack is itself a stack.

## Main declarations

* `CategoryTheory.BasedFunctor.morphismsGlue_of_isEquivalence_to_stack`: morphism descent
  is reflected by an equivalence into a stack;
* `CategoryTheory.BasedFunctor.exists_gluing_obj_of_isEquivalence_to_stack`: object
  descent is reflected by the same equivalence;
* `CategoryTheory.BasedCategory.IsStack.of_equivalence`: the resulting stack transport
  theorem.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.BasedFunctor

variable {C : Type u₁} [Category.{v₁} C]
  {X : BasedCategory.{v₂, u₂} C} {Y : BasedCategory.{v₃, u₃} C}
  {J : GrothendieckTopology C}

/-- A fully faithful based functor into a stack reflects the unique gluing of morphisms
specified on a cartesian cocone. -/
lemma existsUnique_gluing_hom_of_full_faithful_to_stack
    (E : BasedFunctor X Y) [Y.p.IsFiberedInGroupoids] [Y.p.IsStack J]
    [E.toFunctor.Full] [E.toFunctor.Faithful]
    {S : C} {R : Sieve S} (hR : R ∈ J S)
    (D : R.arrows.category ⥤ X.obj)
    {a b : X.obj} (ha : X.p.obj a = S) (hb : X.p.obj b = S)
    (η : ∀ q : R.arrows.category, D.obj q ⟶ a)
    (hηlift : ∀ q, IsHomLift X.p q.obj.hom (η q))
    (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift X.p k.hom.left (D.map k))
    (hηnat : ∀ {q r : R.arrows.category} (k : q ⟶ r), D.map k ≫ η r = η q)
    (θ : ∀ q : R.arrows.category, D.obj q ⟶ b)
    (hθlift : ∀ q, IsHomLift X.p q.obj.hom (θ q))
    (hθnat : ∀ {q r : R.arrows.category} (k : q ⟶ r), D.map k ≫ θ r = θ q) :
    ∃! Φ : a ⟶ b, IsHomLift X.p (𝟙 S) Φ ∧
      ∀ {T : C} {q : T ⟶ S} (hq : R q), θ (R.arrows.categoryMk q hq) =
        η (R.arrows.categoryMk q hq) ≫ Φ := by
  have hEDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift Y.p k.hom.left ((D ⋙ E.toFunctor).map k) := by
    intro q r k
    change IsHomLift Y.p k.hom.left (E.map (D.map k))
    exact E.preserves_isHomLift _ _
  have hEηlift : ∀ q : R.arrows.category,
      IsHomLift Y.p q.obj.hom (E.map (η q)) := by
    intro q
    exact E.preserves_isHomLift _ _
  have hEθlift : ∀ q : R.arrows.category,
      IsHomLift Y.p q.obj.hom (E.map (θ q)) := by
    intro q
    exact E.preserves_isHomLift _ _
  have hEηnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      (D ⋙ E.toFunctor).map k ≫ E.map (η r) = E.map (η q) := by
    intro q r k
    simpa only [Functor.comp_map, ← E.map_comp] using congrArg E.map (hηnat k)
  have hEθnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      (D ⋙ E.toFunctor).map k ≫ E.map (θ r) = E.map (θ q) := by
    intro q r k
    simpa only [Functor.comp_map, ← E.map_comp] using congrArg E.map (hθnat k)
  obtain ⟨Ψ, hΨ, huniq⟩ := Functor.IsStack.existsUnique_gluing_hom_of_cocone
    hR (D ⋙ E.toFunctor) ((E.w_obj a).trans ha) ((E.w_obj b).trans hb)
      (fun q ↦ E.map (η q)) hEηlift hEDmap hEηnat
      (fun q ↦ E.map (θ q)) hEθlift hEθnat
  obtain ⟨Φ, hΦmap⟩ := E.toFunctor.map_surjective Ψ
  have hΦlift : IsHomLift X.p (𝟙 S) Φ := by
    haveI hmap : IsHomLift Y.p (𝟙 S) (E.map Φ) := by
      rw [hΦmap]
      exact hΨ.1
    exact E.isHomLift_map (𝟙 S) Φ
  refine ⟨Φ, ⟨hΦlift, ?_⟩, ?_⟩
  · intro T q hq
    apply E.toFunctor.map_injective
    rw [E.toFunctor.map_comp, hΦmap]
    exact hΨ.2 hq
  · intro Φ' hΦ'
    apply E.toFunctor.map_injective
    rw [hΦmap]
    apply huniq (E.map Φ')
    have hmaplift : IsHomLift Y.p (𝟙 S) (E.map Φ') := by
      letI := hΦ'.1
      exact E.preserves_isHomLift (𝟙 S) Φ'
    refine ⟨hmaplift, ?_⟩
    intro T q hq
    simpa only [E.toFunctor.map_comp] using congrArg E.map (hΦ'.2 hq)

/-- A based equivalence into a stack reflects the morphism-gluing axiom. -/
theorem morphismsGlue_of_isEquivalence_to_stack
    (E : BasedFunctor X Y) [X.p.IsFiberedInGroupoids]
    [Y.p.IsFiberedInGroupoids] [Y.p.IsStack J]
    [E.toFunctor.IsEquivalence] : X.p.MorphismsGlue J := by
  intro S R hR a b ha hb φ hφlift hφnat
  subst S
  have φ_congr : ∀ {T : C} {g g' : T ⟶ X.p.obj a} (hgg : g = g')
      (hg : R g) (hg' : R g') {x : X.obj} (ξ ξ' : x ⟶ a)
      (hξ : IsHomLift X.p g ξ) (hξ' : IsHomLift X.p g' ξ')
      (hξeq : ξ = ξ'), φ hg ξ hξ = φ hg' ξ' hξ' := by
    intro T g g' hgg hg hg' x ξ ξ' hξ hξ' hξeq
    subst g'
    subst ξ'
    rfl
  obtain ⟨D, η, hηlift, hDmap, hηnat⟩ :=
    Functor.IsStack.exists_lift_cocone (p := X.p) (a := a) R
  let θ : ∀ q : R.arrows.category, D.obj q ⟶ b := fun q ↦
    φ q.property (η q) (hηlift q)
  have hθlift : ∀ q : R.arrows.category,
      IsHomLift X.p q.obj.hom (θ q) := by
    intro q
    exact hφlift q.property (η q) (hηlift q)
  have hθnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      D.map k ≫ θ r = θ q := by
    intro q r k
    have h := hφnat r.property (D.map k) (η r) (hηlift r) (hDmap k)
    have hcomp : IsHomLift X.p (k.hom.left ≫ r.obj.hom)
        (D.map k ≫ η r) := inferInstance
    have hleft := φ_congr k.hom.w
      (R.downward_closed r.property k.hom.left) q.property
      (D.map k ≫ η r) (η q) hcomp (hηlift q) (hηnat k)
    exact h.symm.trans hleft
  obtain ⟨Φ, hΦ, huniq⟩ :=
    E.existsUnique_gluing_hom_of_full_faithful_to_stack hR D rfl hb
      η hηlift hDmap hηnat θ hθlift hθnat
  let Q : ∀ {T : C} {q : T ⟶ X.p.obj a}, R q → R.arrows.category :=
    fun {_} {q} hq ↦ R.arrows.categoryMk q hq
  let κ : ∀ {T : C} {q : T ⟶ X.p.obj a} (hq : R q) {x : X.obj}
      (ξ : x ⟶ a) [IsHomLift X.p q ξ], x ⟶ D.obj (Q hq) :=
    fun {_} {q} hq {_} ξ hξ ↦ by
      letI := hξ
      letI : IsHomLift X.p q (η (Q hq)) := by
        simpa [Q] using hηlift (Q hq)
      letI : IsStronglyCartesian X.p q (η (Q hq)) :=
        Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift X.p q _
      exact IsStronglyCartesian.map X.p q (η (Q hq))
        (Category.id_comp q).symm ξ
  have hκlift : ∀ {T : C} {q : T ⟶ X.p.obj a} (hq : R q) {x : X.obj}
      (ξ : x ⟶ a) [IsHomLift X.p q ξ],
      IsHomLift X.p (𝟙 T) (κ hq ξ) := by
    intro T q hq x ξ hξ
    letI : IsHomLift X.p q (η (Q hq)) := by
      simpa [Q] using hηlift (Q hq)
    letI : IsStronglyCartesian X.p q (η (Q hq)) :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift X.p q _
    simpa [κ] using IsStronglyCartesian.map_isHomLift X.p q (η (Q hq))
      (Category.id_comp q).symm ξ
  have hκfac : ∀ {T : C} {q : T ⟶ X.p.obj a} (hq : R q) {x : X.obj}
      (ξ : x ⟶ a) [IsHomLift X.p q ξ], κ hq ξ ≫ η (Q hq) = ξ := by
    intro T q hq x ξ hξ
    letI : IsHomLift X.p q (η (Q hq)) := by
      simpa [Q] using hηlift (Q hq)
    letI : IsStronglyCartesian X.p q (η (Q hq)) :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift X.p q _
    simp [κ]
  refine ⟨Φ, ⟨hΦ.1, ?_⟩, ?_⟩
  · intro T q hq x ξ hξ
    letI := hξ
    letI : IsHomLift X.p (𝟙 T) (κ hq ξ) := hκlift hq ξ
    have hcompat := hφnat hq (κ hq ξ) (η (Q hq))
      (by simpa [Q] using hηlift (Q hq)) (hκlift hq ξ)
    calc
      φ hq ξ hξ = κ hq ξ ≫ θ (Q hq) := by
        simpa only [Q, θ, Category.id_comp, hκfac hq ξ] using hcompat
      _ = κ hq ξ ≫ (η (Q hq) ≫ Φ) := by rw [← hΦ.2 hq]
      _ = (κ hq ξ ≫ η (Q hq)) ≫ Φ := (Category.assoc _ _ _).symm
      _ = ξ ≫ Φ := by rw [hκfac hq ξ]
  · intro Φ' hΦ'
    apply huniq Φ'
    refine ⟨hΦ'.1, ?_⟩
    intro T q hq
    simpa only [Q, θ] using hΦ'.2 hq (η (Q hq))
      (by simpa [Q] using hηlift (Q hq))

/-- A based equivalence into a stack reflects effective descent of objects. -/
theorem exists_gluing_obj_of_isEquivalence_to_stack
    (E : BasedFunctor X Y) [X.p.IsFiberedInGroupoids]
    [Y.p.IsFiberedInGroupoids] [Y.p.IsStack J]
    [E.toFunctor.IsEquivalence]
    {S : C} {R : Sieve S} (hR : R ∈ J S)
    (D : R.arrows.category ⥤ X.obj)
    (hDobj : ∀ q : R.arrows.category, X.p.obj (D.obj q) = q.obj.left)
    (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift X.p k.hom.left (D.map k)) :
    ∃ (a : X.obj) (_ : X.p.obj a = S) (ε : ∀ q : R.arrows.category, D.obj q ⟶ a),
      (∀ q, IsHomLift X.p q.obj.hom (ε q)) ∧
      ∀ {q r : R.arrows.category} (k : q ⟶ r), D.map k ≫ ε r = ε q := by
  obtain ⟨b, hb, ε, hεlift, hεnat⟩ :=
    BasedFunctor.exists_gluing_obj_of_isStack E hR D hDobj hDmap
  let bFiber : Y.p.Fiber S := ⟨b, hb⟩
  let _ : (E.onFiber S).EssSurj :=
    BasedCategory.onFiber_essSurj_of_essSurj E S
  let a : X.p.Fiber S := (E.onFiber S).objPreimage bFiber
  let e : (E.onFiber S).obj a ≅ bFiber :=
    (E.onFiber S).objObjPreimageIso bFiber
  let δ : ∀ q : R.arrows.category, D.obj q ⟶ a.1 := fun q ↦
    E.toFunctor.preimage (ε q ≫ e.inv.1)
  have hEδ : ∀ q : R.arrows.category,
      E.map (δ q) = ε q ≫ e.inv.1 := fun q ↦ E.toFunctor.map_preimage _
  have hδlift : ∀ q : R.arrows.category,
      IsHomLift X.p q.obj.hom (δ q) := by
    intro q
    have hcomp : IsHomLift Y.p q.obj.hom (ε q ≫ e.inv.1) := by
      letI : IsHomLift Y.p (𝟙 S) e.inv.1 := e.inv.2
      exact IsHomLift.comp_lift_id_right' Y.p q.obj.hom (ε q) S e.inv.1
    haveI hmap : IsHomLift Y.p q.obj.hom (E.map (δ q)) := by
      rw [hEδ q]
      exact hcomp
    exact E.isHomLift_map q.obj.hom (δ q)
  have hδnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      D.map k ≫ δ r = δ q := by
    intro q r k
    apply E.toFunctor.map_injective
    calc
      E.map (D.map k ≫ δ r) = E.map (D.map k) ≫ (ε r ≫ e.inv.1) := by
        rw [E.toFunctor.map_comp, hEδ r]
      _ = (E.map (D.map k) ≫ ε r) ≫ e.inv.1 :=
        (Category.assoc _ _ _).symm
      _ = ε q ≫ e.inv.1 := by rw [hεnat k]
      _ = E.map (δ q) := (hEδ q).symm
  exact ⟨a.1, a.2, δ, hδlift, hδnat⟩

end CategoryTheory.BasedFunctor

namespace CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {X : BasedCategory.{v₂, u₂} C} {Y : BasedCategory.{v₃, u₃} C}
  {J : GrothendieckTopology C}

/-- The source of an equivalence over the base is a stack whenever the target is a
stack. -/
theorem IsStack.of_equivalence (E : BasedFunctor X Y)
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    [E.toFunctor.IsEquivalence] [BasedCategory.IsStack J Y] :
    BasedCategory.IsStack J X where
  isFiberedInGroupoids := inferInstance
  isStack := by
    constructor
    · exact E.morphismsGlue_of_isEquivalence_to_stack
    · exact E.exists_gluing_obj_of_isEquivalence_to_stack

end CategoryTheory.BasedCategory
