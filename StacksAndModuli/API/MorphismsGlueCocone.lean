module

public import StacksAndModuli.«Section3.5-Stacks».«part3.5.1-the-definition»

/-!
# Gluing morphisms from cocone data

This file refines the morphism half of the stack condition.  When morphisms
glue along a topology, it is enough to prescribe a natural local morphism on
one cartesian cocone over a covering sieve.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.MorphismsGlue

variable {Base : Type u₁} {Total : Type u₂} [Category.{v₁} Base]
  [Category.{v₂} Total] {p : Total ⥤ Base} [p.IsFiberedInGroupoids]
  {J : GrothendieckTopology Base}

/-- To glue a morphism in a prestack whose morphisms satisfy descent, it
suffices to give the morphism on one functorial choice of cartesian lifts over
the covering sieve. -/
lemma existsUnique_gluing_hom_of_cocone
    (hglue : p.MorphismsGlue J) {S : Base} {R : Sieve S} (hR : R ∈ J S)
    (D : R.arrows.category ⥤ Total)
    {a b : Total} (ha : p.obj a = S) (hb : p.obj b = S)
    (η : ∀ q : R.arrows.category, D.obj q ⟶ a)
    (hηlift : ∀ q, IsHomLift p q.obj.hom (η q))
    (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      IsHomLift p k.hom.left (D.map k))
    (hηnat : ∀ {q r : R.arrows.category} (k : q ⟶ r), D.map k ≫ η r = η q)
    (θ : ∀ q : R.arrows.category, D.obj q ⟶ b)
    (hθlift : ∀ q, IsHomLift p q.obj.hom (θ q))
    (hθnat : ∀ {q r : R.arrows.category} (k : q ⟶ r), D.map k ≫ θ r = θ q) :
    ∃! Φ : a ⟶ b, IsHomLift p (𝟙 S) Φ ∧
      ∀ {T : Base} {q : T ⟶ S} (hq : R q), θ (R.arrows.categoryMk q hq) =
        η (R.arrows.categoryMk q hq) ≫ Φ := by
  let Q : ∀ {T : Base} {q : T ⟶ S}, R q → R.arrows.category :=
    fun {_} {q} hq ↦ R.arrows.categoryMk q hq
  let κ : ∀ {T : Base} {q : T ⟶ S} (hq : R q) {x : Total}
      (ξ : x ⟶ a) [IsHomLift p q ξ], x ⟶ D.obj (Q hq) :=
    fun {_} {q} hq {_} ξ hξ ↦ by
      letI := hξ
      letI : IsHomLift p q (η (Q hq)) := by simpa [Q] using hηlift (Q hq)
      letI : IsStronglyCartesian p q (η (Q hq)) :=
        Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift p q _
      exact IsStronglyCartesian.map p q (η (Q hq)) (Category.id_comp q).symm ξ
  have hκ_fac : ∀ {T : Base} {q : T ⟶ S} (hq : R q) {x : Total}
      (ξ : x ⟶ a) [IsHomLift p q ξ], κ hq ξ ≫ η (Q hq) = ξ := by
    intro T q hq x ξ hξ
    letI : IsHomLift p q (η (Q hq)) := by simpa [Q] using hηlift (Q hq)
    letI : IsStronglyCartesian p q (η (Q hq)) :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift p q _
    simp [κ]
  obtain ⟨Φ, hΦ, huniq⟩ := hglue hR ha hb
    (fun {_} {_} hq {_} ξ hξ ↦ by
      letI := hξ
      exact κ hq ξ ≫ θ (Q hq))
    (fun {_} {q} hq {_} ξ hξ ↦ by
      letI := hξ
      letI : IsHomLift p q (η (Q hq)) := by simpa [Q] using hηlift (Q hq)
      letI : IsStronglyCartesian p q (η (Q hq)) :=
        Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift p q _
      letI := IsStronglyCartesian.map_isHomLift p q (η (Q hq))
        (Category.id_comp q).symm ξ
      letI : IsHomLift p q (θ (Q hq)) := by simpa [Q] using hθlift (Q hq)
      infer_instance)
    (fun {T'} {T} {q} hq {r} {x'} {x} χ ξ hξ hχ ↦ by
      letI := hξ
      letI := hχ
      let hq' := R.downward_closed hq r
      let k : Q hq' ⟶ Q hq := ObjectProperty.homMk (Over.homMk r rfl)
      have hkη : D.map k ≫ η (Q hq) = η (Q hq') := hηnat k
      have hkθ : D.map k ≫ θ (Q hq) = θ (Q hq') := hθnat k
      have hκ : κ hq' (χ ≫ ξ) ≫ D.map k = χ ≫ κ hq ξ := by
        letI : IsHomLift p q (η (Q hq)) := by simpa [Q] using hηlift (Q hq)
        letI : IsHomLift p (r ≫ q) (η (Q hq')) := by
          simpa [Q] using hηlift (Q hq')
        letI : IsHomLift p r (D.map k) := by simpa [k, Q] using hDmap k
        letI : IsStronglyCartesian p q (η (Q hq)) :=
          Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift p q _
        letI : IsStronglyCartesian p (r ≫ q) (η (Q hq')) :=
          Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift p (r ≫ q) _
        letI : IsHomLift p (𝟙 _) (κ hq ξ) := by
          simpa [κ] using IsStronglyCartesian.map_isHomLift p q (η (Q hq))
            (Category.id_comp q).symm ξ
        letI : IsHomLift p (𝟙 _) (κ hq' (χ ≫ ξ)) := by
          simpa [κ] using IsStronglyCartesian.map_isHomLift p (r ≫ q) (η (Q hq'))
            (Category.id_comp (r ≫ q)).symm (χ ≫ ξ)
        letI : IsHomLift p r (χ ≫ κ hq ξ) := inferInstance
        letI : IsHomLift p r (κ hq' (χ ≫ ξ) ≫ D.map k) :=
          IsHomLift.comp_lift_id_left' p T' _ r _
        apply IsStronglyCartesian.ext p q (η (Q hq)) r
        rw [Category.assoc, hkη, hκ_fac, Category.assoc, hκ_fac]
      calc
        κ hq' (χ ≫ ξ) ≫ θ (Q hq') =
            (κ hq' (χ ≫ ξ) ≫ D.map k) ≫ θ (Q hq) := by
          rw [Category.assoc, hkθ]
        _ = (χ ≫ κ hq ξ) ≫ θ (Q hq) := by rw [hκ]
        _ = χ ≫ κ hq ξ ≫ θ (Q hq) := Category.assoc _ _ _)
  refine ⟨Φ, ⟨hΦ.1, fun {T q} hq ↦ ?_⟩, ?_⟩
  · let q' := R.arrows.categoryMk q hq
    letI := hηlift q'
    have h := hΦ.2 hq (η q') (hηlift q')
    dsimp [q'] at h ⊢
    simpa [Q, κ] using h
  · intro Ψ hΨ
    apply huniq Ψ
    refine ⟨hΨ.1, ?_⟩
    intro T q hq x ξ hξ
    letI := hξ
    calc
      κ hq ξ ≫ θ (Q hq) = κ hq ξ ≫ (η (Q hq) ≫ Ψ) := by rw [← hΨ.2 hq]
      _ = (κ hq ξ ≫ η (Q hq)) ≫ Ψ := (Category.assoc _ _ _).symm
      _ = ξ ≫ Ψ := by rw [hκ_fac]

end CategoryTheory.Functor.MorphismsGlue
