module

public import StacksAndModuli.API.ActionQuotientFpqcObjects
public import StacksAndModuli.«Section3.5-Stacks».«part3.5.1-the-definition»

/-!
# Stack reductions for action quotient prestacks

This file reduces the fpqc and étale stack conditions for a principal-bundle
action quotient to effective cartesian gluing of the underlying total-space
arrows.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {G U : Over S} [GrpObj G] [ModObj G U]

/-- A reusable reduction of the fpqc stack condition for `[U/G]` to
cartesian gluing of the underlying total spaces. -/
theorem actionQuotient_isStack_fpqc_of_underlyingGluing
    (hglue : ∀ {T : Over S} {R : Sieve T},
      R ∈ Scheme.fpqcTopology.over S T →
      ∀ (D : R.arrows.category ⥤ ActionQuotientObj G U)
        (hDobj : ∀ q : R.arrows.category,
          (actionQuotientPrestack G U).p.obj (D.obj q) = q.obj.left)
        (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
          IsHomLift (actionQuotientPrestack G U).p k.hom.left (D.map k)),
        Nonempty (ClassifyingObj.UnderlyingGluing
          (ActionQuotientObjectDescent.carrierFunctor D)
          (ActionQuotientObjectDescent.carrierFunctor_obj D hDobj)
          (ActionQuotientObjectDescent.carrierFunctor_map D hDmap))) :
    BasedCategory.IsStack (Scheme.fpqcTopology.over S)
      (actionQuotientPrestack G U) := by
  refine ⟨inferInstance, ?_⟩
  constructor
  · exact ActionQuotientPrestackMorphisms.morphismsGlue_fpqc
  · intro T R hR D hDobj hDmap
    obtain ⟨A⟩ := hglue hR D hDobj (fun {_ _} k ↦ hDmap k)
    exact ActionQuotientObjectDescent.exists_gluing
      D hDobj (fun {_ _} k ↦ hDmap k) A hR

/-- A reusable reduction of the fpqc stack condition for `BG` to cartesian
gluing of the underlying total spaces. -/
theorem classifyingPrestack_isStack_fpqc_of_underlyingGluing
    (hglue : ∀ {T : Over S} {R : Sieve T},
      R ∈ Scheme.fpqcTopology.over S T →
      ∀ (D : R.arrows.category ⥤ ClassifyingObj G)
        (hDobj : ∀ q : R.arrows.category,
          (classifyingPrestack G).p.obj (D.obj q) = q.obj.left)
        (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
          IsHomLift (classifyingPrestack G).p k.hom.left (D.map k)),
        Nonempty (ClassifyingObj.UnderlyingGluing D hDobj hDmap)) :
    BasedCategory.IsStack (Scheme.fpqcTopology.over S)
      (classifyingPrestack G) := by
  refine ⟨inferInstance, ?_⟩
  constructor
  · exact ClassifyingPrestackMorphisms.morphismsGlue_fpqc
  · intro T R hR D hDobj hDmap
    obtain ⟨A⟩ := hglue hR D hDobj (fun {_ _} k ↦ hDmap k)
    exact ClassifyingObj.UnderlyingGluing.exists_gluing A hR

/-- The étale topology on `Scheme/S` is coarser than its fpqc topology. -/
lemma etaleTopology_over_le_fpqcTopology_over (S : Scheme.{u}) :
    Scheme.etaleTopology.over S ≤ Scheme.fpqcTopology.over S := by
  intro T R hR
  rw [Scheme.etaleTopology.mem_over_iff] at hR
  rw [Scheme.fpqcTopology.mem_over_iff]
  exact Scheme.etaleTopology_le_fpqcTopology _ hR

/-- The corresponding reduction of the étale stack condition. -/
theorem actionQuotient_isStack_etale_of_underlyingGluing
    (hglue : ∀ {T : Over S} {R : Sieve T},
      R ∈ Scheme.fpqcTopology.over S T →
      ∀ (D : R.arrows.category ⥤ ActionQuotientObj G U)
        (hDobj : ∀ q : R.arrows.category,
          (actionQuotientPrestack G U).p.obj (D.obj q) = q.obj.left)
        (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
          IsHomLift (actionQuotientPrestack G U).p k.hom.left (D.map k)),
        Nonempty (ClassifyingObj.UnderlyingGluing
          (ActionQuotientObjectDescent.carrierFunctor D)
          (ActionQuotientObjectDescent.carrierFunctor_obj D hDobj)
          (ActionQuotientObjectDescent.carrierFunctor_map D hDmap))) :
    BasedCategory.IsStack (Scheme.etaleTopology.over S)
      (actionQuotientPrestack G U) := by
  let hfpqc := actionQuotient_isStack_fpqc_of_underlyingGluing hglue
  letI : (actionQuotientPrestack G U).p.IsFiberedInGroupoids :=
    hfpqc.isFiberedInGroupoids
  let hstack : (actionQuotientPrestack G U).p.IsStack
      (Scheme.fpqcTopology.over S) := hfpqc.isStack
  refine ⟨inferInstance, ?_⟩
  constructor
  · intro T R hR
    exact hstack.existsUnique_gluing_hom
      (etaleTopology_over_le_fpqcTopology_over S T hR)
  · intro T R hR
    exact hstack.exists_gluing_obj
      (etaleTopology_over_le_fpqcTopology_over S T hR)

end AlgebraicGeometry.Scheme
