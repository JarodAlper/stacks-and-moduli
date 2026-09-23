module

public import StacksAndModuli.API.FinitePointSupportComparison
public import StacksAndModuli.API.NodalCurveDefectStalkwiseIso

/-!
# Constructing the nodal normalization-defect comparison

At each split node `q`, a morphism from the pullback of the normalization pushforward
to the structure module on `Spec κ(q)` gives, by adjunction, a morphism to the
residue-point module at `q`.  If the local morphism kills the pulled-back normalization
unit, its adjoint transpose descends through the normalization defect.  The finitely many
descended maps then assemble into one global morphism from the normalization defect to
the node-residue module.

The global morphism is an isomorphism provided each descended component is an
isomorphism on the stalk of its node.  Thus the remaining geometric input is entirely
local: construct these functionals from node charts and compare the global normalization
after completion with the two-axis normalization.

## Main definitions and results

* `AlgebraicGeometry.Scheme.IsNodalCurveOver.NormalizationNodeFunctional`: local data
  on the pullback of the normalization sequence at one node.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationDefectToNodeResidueSupport`:
  the resulting global comparison morphism.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.isIso_normalizationDefectToNodeResidueSupport`:
  the global isomorphism criterion in terms of the component maps at node stalks.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A functional on the normalization pushforward after pullback to one node, together
with the condition that it kills the pulled-back structure-sheaf unit.

For a chosen split-node chart, the expected functional is the difference of the two
branch constants.  Constructing it for the global normalization requires the comparison
between normalization and completed local normalization. -/
structure IsNodalCurveOver.NormalizationNodeFunctional
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (q : C.SplitNodePoints k) where
  hom : (Modules.pullback (C.fromSpecResidueField q.1)).obj
      h.normalizationPushforwardModule ⟶
    structureModule (Spec (C.residueField q.1))
  comp_unit :
    (Modules.pullback (C.fromSpecResidueField q.1)).map h.normalizationUnit ≫ hom = 0

/-- The component of the defect comparison supported at one node, obtained by
adjunction and descent through the normalization cokernel. -/
noncomputable def
    IsNodalCurveOver.normalizationDefectToNodeResidueComponent
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (q : C.SplitNodePoints k) (d : h.NormalizationNodeFunctional q) :
    h.normalizationDefectModule ⟶ residuePointSupportModule C q.1 :=
  Modules.cokernelToResiduePointSupportOfPullbackCompEqZero
    h.normalizationUnit q.1 d.hom d.comp_unit

/-- Assemble node functionals into a single global comparison from the normalization
defect to the finite residue-point module supported at all nodes. -/
noncomputable def
    IsNodalCurveOver.normalizationDefectToNodeResidueSupport
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (d : ∀ q : C.SplitNodePoints k, h.NormalizationNodeFunctional q) :
    h.normalizationDefectModule ⟶ h.nodeResidueSupportModule := by
  let _ : Finite (C.SplitNodePoints k) := h.finite_splitNodePoints
  exact Modules.finiteResiduePointSupportLift h.normalizationDefectModule
    (fun q : C.SplitNodePoints k ↦ q.1)
    (fun q ↦ h.normalizationDefectToNodeResidueComponent q (d q))

/-- Projection from the node-residue module to the summand supported at one node. -/
noncomputable def IsNodalCurveOver.nodeResidueSupportπ
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (q : C.SplitNodePoints k) :
    h.nodeResidueSupportModule ⟶ residuePointSupportModule C q.1 := by
  let _ : Finite (C.SplitNodePoints k) := h.finite_splitNodePoints
  exact Modules.finiteResiduePointSupportπ
    (fun p : C.SplitNodePoints k ↦ p.1) q

/-- Projecting the global defect comparison to one node recovers its descended
component map. -/
@[reassoc (attr := simp)]
lemma IsNodalCurveOver.normalizationDefectToNodeResidueSupport_comp_π
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (d : ∀ q : C.SplitNodePoints k, h.NormalizationNodeFunctional q)
    (q : C.SplitNodePoints k) :
    h.normalizationDefectToNodeResidueSupport d ≫
        h.nodeResidueSupportπ q =
      h.normalizationDefectToNodeResidueComponent q (d q) := by
  let _ : Finite (C.SplitNodePoints k) := h.finite_splitNodePoints
  change h.normalizationDefectToNodeResidueSupport d ≫
      Modules.finiteResiduePointSupportπ
        (fun p : C.SplitNodePoints k ↦ p.1) q = _
  apply Modules.finiteResiduePointSupportLift_comp_π

/-- The global comparison assembled from node functionals is an isomorphism if each
descended component is an isomorphism on the stalk of its node. -/
theorem IsNodalCurveOver.isIso_normalizationDefectToNodeResidueSupport
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (d : ∀ q : C.SplitNodePoints k, h.NormalizationNodeFunctional q)
    (hd : ∀ q : C.SplitNodePoints k, IsIso
      ((Modules.toPresheaf C ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q.1).map
          (h.normalizationDefectToNodeResidueComponent q (d q)))) :
    IsIso (h.normalizationDefectToNodeResidueSupport d) := by
  let _ : Finite (C.SplitNodePoints k) := h.finite_splitNodePoints
  let _ := Fintype.ofFinite (C.SplitNodePoints k)
  apply h.isIso_normalizationDefectToNodeResidueSupport_of_stalkwise
  intro x hx
  let q : C.SplitNodePoints k := ⟨x, hx⟩
  let F := Modules.toPresheaf C ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hπ : IsIso (F.map (h.nodeResidueSupportπ q)) := by
    change IsIso (F.map (Modules.finiteResiduePointSupportπ
      (fun p : C.SplitNodePoints k ↦ p.1) q))
    exact
    Modules.isIso_stalkFunctor_map_finiteResiduePointSupportπ
      (fun p : C.SplitNodePoints k ↦ p.1)
      h.isClosed_splitNodePoint Subtype.val_injective q
  let _ : IsIso (F.map (h.nodeResidueSupportπ q)) := hπ
  let _ : IsIso (F.map
      (h.normalizationDefectToNodeResidueComponent q (d q))) := hd q
  have hcomp : IsIso
      (F.map (h.normalizationDefectToNodeResidueSupport d) ≫
        F.map (h.nodeResidueSupportπ q)) := by
    rw [← F.map_comp,
      h.normalizationDefectToNodeResidueSupport_comp_π]
    infer_instance
  let _ : IsIso
      (F.map (h.normalizationDefectToNodeResidueSupport d) ≫
        F.map (h.nodeResidueSupportπ q)) := hcomp
  exact IsIso.of_isIso_comp_right
    (F.map (h.normalizationDefectToNodeResidueSupport d))
    (F.map (h.nodeResidueSupportπ q))

/-- Package a family of node functionals whose component maps are stalkwise
isomorphisms as an isomorphism from the normalization defect to the node-residue module. -/
noncomputable def
    IsNodalCurveOver.normalizationDefectIsoNodeResidueSupportOfFunctionals
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (d : ∀ q : C.SplitNodePoints k, h.NormalizationNodeFunctional q)
    (hd : ∀ q : C.SplitNodePoints k, IsIso
      ((Modules.toPresheaf C ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} q.1).map
          (h.normalizationDefectToNodeResidueComponent q (d q)))) :
    h.normalizationDefectModule ≅ h.nodeResidueSupportModule := by
  let _ : IsIso (h.normalizationDefectToNodeResidueSupport d) :=
    h.isIso_normalizationDefectToNodeResidueSupport d hd
  exact asIso (h.normalizationDefectToNodeResidueSupport d)

end AlgebraicGeometry.Scheme

end
