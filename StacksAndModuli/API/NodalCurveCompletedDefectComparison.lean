module

public import StacksAndModuli.API.NodalCurveDefectComparison
public import StacksAndModuli.API.SchemeModuleCompletedStalk
public import StacksAndModuli.API.SplitNodeAxisSequence

/-!
# Completed-local comparison for the nodal normalization defect

At a split node, the standard completed-local normalization sequence has quotient
defect

`(k[[x]] × k[[y]]) / (k[[x,y]]/(xy)) ≃ k`.

This file states the precise comparison datum needed to transfer that calculation to
the defect of the global relative normalization.  A
`NormalizationNodeCompletedAxisComparison` consists of a node functional together with
equivalences identifying the completed stalks of its source and target with the standard
axis defect and `k`, compatibly with the difference-of-constants map.

The compatibility immediately makes the completed component map bijective.  Since the
ordinary local ring is Noetherian and its completion is faithfully flat, bijectivity
descends to the ordinary stalk.  The finite point-support construction then gives the
global isomorphism.

This is deliberately a conditional interface.  Constructing the source equivalence
requires the geometric theorem that completion of the stalk of the global relative
normalization agrees with the integral closure of the completed nodal local ring.  The
existing node-ring calculation proves that the latter integral closure is the two-axis
ring, but Mathlib currently has no theorem that supplies the former comparison for
finite-type schemes over a field.

## Main definitions and results

* `AlgebraicGeometry.Scheme.IsNodalCurveOver.NormalizationNodeCompletedAxisComparison`:
  the exact completed-local comparison datum at one node.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.completedAxisComparison_component_isIso`:
  the descended component is an isomorphism on the node stalk.
* `normalizationDefectIsoNodeResidueSupportOfCompletedAxisComparisons`:
  a family of completed-axis comparisons gives the global defect isomorphism.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A comparison of the completed stalk of one global normalization-defect component
with the standard coordinate-axis defect at a split node.

The target equivalence also includes the canonical rationality comparison implicit at
a closed point over an algebraically closed field.  Plain equivalences suffice here:
their only role is to transfer bijectivity of the standard defect equivalence. -/
structure IsNodalCurveOver.NormalizationNodeCompletedAxisComparison
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (q : C.SplitNodePoints k) where
  /-- The functional whose adjoint transpose defines the component supported at `q`. -/
  functional : h.NormalizationNodeFunctional q
  /-- Identification of the completed global defect stalk with the quotient defect of
  the chosen completed-local coordinate axes. -/
  defectEquiv :
    Modules.completedStalkModule h.normalizationDefectModule q.1 ≃
      q.2.ChosenCompletedLocalAxisDefect
  /-- Identification of the completed stalk of the residue-point target with the ground
  field. -/
  residueEquiv :
    Modules.completedStalkModule (residuePointSupportModule C q.1) q.1 ≃ k
  /-- Under the two identifications, the completed component map is the standard
  difference-of-branch-constants equivalence. -/
  map_compatibility : ∀ z,
    residueEquiv
        (Modules.completedStalkLinearMap
          (h.normalizationDefectToNodeResidueComponent q functional) q.1 z) =
      q.2.chosenCompletedLocalAxisDefectLinearEquiv (defectEquiv z)

/-- A completed-axis comparison makes the completed component map bijective. -/
theorem IsNodalCurveOver.completedAxisComparison_component_bijective
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (q : C.SplitNodePoints k)
    (d : h.NormalizationNodeCompletedAxisComparison q) :
    Function.Bijective
      (Modules.completedStalkLinearMap
        (h.normalizationDefectToNodeResidueComponent q d.functional) q.1) := by
  constructor
  · intro a b hab
    apply d.defectEquiv.injective
    apply q.2.chosenCompletedLocalAxisDefectLinearEquiv.injective
    rw [← d.map_compatibility a, ← d.map_compatibility b, hab]
  · intro y
    let z := d.defectEquiv.symm
      (q.2.chosenCompletedLocalAxisDefectLinearEquiv.symm (d.residueEquiv y))
    refine ⟨z, d.residueEquiv.injective ?_⟩
    rw [d.map_compatibility]
    simp [z]

/-- A completed-axis comparison makes the corresponding defect-to-residue component an
isomorphism on the ordinary additive stalk at its node. -/
theorem IsNodalCurveOver.completedAxisComparison_component_isIso
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (q : C.SplitNodePoints k)
    (d : h.NormalizationNodeCompletedAxisComparison q) :
    IsIso ((Modules.toPresheaf C ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q.1).map
        (h.normalizationDefectToNodeResidueComponent q d.functional)) := by
  let _ : IsNoetherian C := h.isNoetherian
  exact Modules.isIso_stalkFunctor_map_of_completed_bijective
    (h.normalizationDefectToNodeResidueComponent q d.functional) q.1
    (h.completedAxisComparison_component_bijective q d)

/-- A family of completed-axis comparisons makes the assembled global comparison an
isomorphism. -/
theorem IsNodalCurveOver.isIso_normalizationDefectToNodeResidueSupport_ofCompletedAxisComparisons
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (d : ∀ q : C.SplitNodePoints k,
      h.NormalizationNodeCompletedAxisComparison q) :
    IsIso (h.normalizationDefectToNodeResidueSupport (fun q ↦ (d q).functional)) := by
  apply h.isIso_normalizationDefectToNodeResidueSupport
  intro q
  exact h.completedAxisComparison_component_isIso q (d q)

/-- Package a family of completed-axis comparisons as the global isomorphism from the
normalization defect to the finite node-residue module. -/
noncomputable def
    IsNodalCurveOver.normalizationDefectIsoNodeResidueSupportOfCompletedAxisComparisons
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (d : ∀ q : C.SplitNodePoints k,
      h.NormalizationNodeCompletedAxisComparison q) :
    h.normalizationDefectModule ≅ h.nodeResidueSupportModule := by
  let _ : IsIso
      (h.normalizationDefectToNodeResidueSupport (fun q ↦ (d q).functional)) :=
    h.isIso_normalizationDefectToNodeResidueSupport_ofCompletedAxisComparisons d
  exact asIso
    (h.normalizationDefectToNodeResidueSupport (fun q ↦ (d q).functional))

end AlgebraicGeometry.Scheme

end
