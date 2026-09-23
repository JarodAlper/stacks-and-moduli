module

public import StacksAndModuli.API.NodalCurveCompletedDefectComparison
public import StacksAndModuli.API.NormalizationComponentHOne

/-!
# The nodal genus formula from completed-axis comparisons

The completed local normalization calculation at every split node gives a global
isomorphism from the normalization defect to one residue-field module per node.  This
file feeds that isomorphism into the cohomological genus formula.

The first theorem packages completed-axis comparisons as
`NormalizationCohomologyData`.  The remaining theorems successively combine this with
the formal genus endgame, the componentwise normalization calculation, and the variant
where finite-dimensionality is transferred from the curve itself.

## Main results

* `NormalizationCohomologyData.of_completedAxisComparisons`: completed node
  comparisons supply all defect-side cohomological data.
* `genusOver_eq_graph_genus_of_completedAxisComparisons`: the genus formula with the
  normalization's first cohomology supplied directly.
* `genusOver_eq_graph_genus_of_completedAxisComparisons_of_component_finite`: the
  componentwise normalization reduction using the canonical comparison.
* `genusOver_eq_graph_genus_of_completedAxisComparisons_of_curve_finite`: the variant
  transferring finite-dimensionality from first cohomology of the curve.
* The corresponding `_of_H_one_comparison` declarations retain compatibility with an
  explicitly supplied comparison.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

noncomputable section

universe u v w

namespace AlgebraicGeometry.Scheme

/-- Completed-axis comparisons at all split nodes supply every defect-side input to
the nodal genus formula.  Only first cohomology of the normalization pushforward remains
to be provided. -/
theorem IsNodalCurveOver.NormalizationCohomologyData.of_completedAxisComparisons
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    (h_nodeCount : Nat.card (C.SplitNodePoints k) = G.edgeCount)
    (d : ∀ q : C.SplitNodePoints k,
      h.NormalizationNodeCompletedAxisComparison q)
    (normalization_H_one_finiteDimensional :
      FiniteDimensional k (Modules.H h.normalizationPushforwardModule 1))
    (normalization_h_one :
      Modules.h k h.normalizationPushforwardModule 1 = G.totalWeight) :
    h.NormalizationCohomologyData G :=
  IsNodalCurveOver.NormalizationCohomologyData.of_nodeResidueSupportIso h G h_nodeCount
    (h.normalizationDefectIsoNodeResidueSupportOfCompletedAxisComparisons d)
    normalization_H_one_finiteDimensional normalization_h_one

/-- A proper connected nodal curve has the genus of a supplied weighted graph once the
completed local defect comparisons, the vertex and node counts, and first cohomology of
the normalization have been identified. -/
theorem IsNodalCurveOver.genusOver_eq_graph_genus_of_completedAxisComparisons
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [ConnectedSpace C]
    [UniversallyClosed (C ↘ Spec (CommRingCat.of k))]
    (h : C.IsNodalCurveOver k)
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    (h_componentCount : Nat.card (irreducibleComponents C) = G.vertexCount)
    (h_nodeCount : Nat.card (C.SplitNodePoints k) = G.edgeCount)
    (d : ∀ q : C.SplitNodePoints k,
      h.NormalizationNodeCompletedAxisComparison q)
    (normalization_H_one_finiteDimensional :
      FiniteDimensional k (Modules.H h.normalizationPushforwardModule 1))
    (normalization_h_one :
      Modules.h k h.normalizationPushforwardModule 1 = G.totalWeight) :
    genusOver k C = G.genus :=
  h.genusOver_eq_graph_genus G h_componentCount
    (IsNodalCurveOver.NormalizationCohomologyData.of_completedAxisComparisons
      h G h_nodeCount d
      normalization_H_one_finiteDimensional normalization_h_one)

/-- The completed-axis genus formula with first cohomology computed componentwise.

The last equality identifies the sum of geometric genera of the normalized irreducible
components with the total weight of the supplied graph. -/
theorem
    IsNodalCurveOver.genusOver_eq_graph_genus_of_completedAxisComparisons_of_H_one_comparison
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [ConnectedSpace C]
    [UniversallyClosed (C ↘ Spec (CommRingCat.of k))]
    (h : C.IsNodalCurveOver k)
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    (h_componentCount : Nat.card (irreducibleComponents C) = G.vertexCount)
    (h_nodeCount : Nat.card (C.SplitNodePoints k) = G.edgeCount)
    (d : ∀ q : C.SplitNodePoints k,
      h.NormalizationNodeCompletedAxisComparison q)
    (hfinite :
      letI : IsNoetherian C := h.isNoetherian
      ∀ Z, FiniteDimensional k
        (Modules.H (structureModule
          (C.reducedIrreducibleComponentNormalization Z)) 1))
    (comparison : h.NormalizationPushforwardHOneComparison)
    (h_totalWeight :
      (letI : IsNoetherian C := h.isNoetherian
       letI := Fintype.ofFinite (irreducibleComponents C)
       ∑ Z, h.geometricGenusWeight Z) = G.totalWeight) :
    genusOver k C = G.genus := by
  apply h.genusOver_eq_graph_genus_of_completedAxisComparisons G
    h_componentCount h_nodeCount d
  · exact h.finiteDimensional_normalizationPushforward_H_one_of_comparison
      hfinite comparison
  · exact
      (h.normalizationPushforward_h_one_eq_sum_geometricGenusWeight_of_comparison
        hfinite comparison).trans h_totalWeight

/-- The completed-axis genus formula with first cohomology computed componentwise using
the canonical normalization-pushforward comparison. -/
theorem
    IsNodalCurveOver.genusOver_eq_graph_genus_of_completedAxisComparisons_of_component_finite
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [ConnectedSpace C]
    [UniversallyClosed (C ↘ Spec (CommRingCat.of k))]
    (h : C.IsNodalCurveOver k)
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    (h_componentCount : Nat.card (irreducibleComponents C) = G.vertexCount)
    (h_nodeCount : Nat.card (C.SplitNodePoints k) = G.edgeCount)
    (d : ∀ q : C.SplitNodePoints k,
      h.NormalizationNodeCompletedAxisComparison q)
    (hfinite :
      letI : IsNoetherian C := h.isNoetherian
      ∀ Z, FiniteDimensional k
        (Modules.H (structureModule
          (C.reducedIrreducibleComponentNormalization Z)) 1))
    (h_totalWeight :
      (letI : IsNoetherian C := h.isNoetherian
       letI := Fintype.ofFinite (irreducibleComponents C)
       ∑ Z, h.geometricGenusWeight Z) = G.totalWeight) :
    genusOver k C = G.genus :=
  h.genusOver_eq_graph_genus_of_completedAxisComparisons_of_H_one_comparison G
    h_componentCount h_nodeCount d hfinite
    h.normalizationPushforwardHOneComparison h_totalWeight

namespace IsNodalCurveOver

/-- The completed-axis genus formula when finite-dimensionality is known for first
cohomology of the curve itself.

Vanishing of first cohomology of the node-residue defect transfers this finiteness to
the normalization pushforward. The supplied pushforward comparison then computes its
dimension from the normalized irreducible components. -/
theorem
    genusOver_eq_graph_genus_of_completedAxisComparisons_of_curve_finite_of_H_one_comparison
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [ConnectedSpace C]
    [UniversallyClosed (C ↘ Spec (CommRingCat.of k))]
    (h : C.IsNodalCurveOver k)
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    (h_componentCount : Nat.card (irreducibleComponents C) = G.vertexCount)
    (h_nodeCount : Nat.card (C.SplitNodePoints k) = G.edgeCount)
    (d : ∀ q : C.SplitNodePoints k,
      h.NormalizationNodeCompletedAxisComparison q)
    (hcurve : FiniteDimensional k (Modules.H (structureModule C) 1))
    (comparison : h.NormalizationPushforwardHOneComparison)
    (h_totalWeight :
      (letI : IsNoetherian C := h.isNoetherian
       letI := Fintype.ofFinite (irreducibleComponents C)
       ∑ Z, h.geometricGenusWeight Z) = G.totalWeight) :
    genusOver k C = G.genus := by
  let e := h.normalizationDefectIsoNodeResidueSupportOfCompletedAxisComparisons d
  let hdefect : Subsingleton
      (Modules.H h.normalizationDefectModule 1) :=
    h.subsingleton_H_normalizationDefectModule_one_of_nodeResidueSupportIso e
  let hpushforward : FiniteDimensional k
      (Modules.H h.normalizationPushforwardModule 1) :=
    h.finiteDimensional_normalizationPushforward_H_one_of_curve_of_defect
      hcurve hdefect
  let hnormalization : FiniteDimensional k
      (Modules.H (structureModule h.normalizationScheme) 1) :=
    Module.Finite.equiv
      (h.normalizationPushforwardHOneLinearEquiv comparison)
  apply h.genusOver_eq_graph_genus_of_completedAxisComparisons G
    h_componentCount h_nodeCount d hpushforward
  exact (h.normalizationPushforwardHOneLinearEquiv comparison).finrank_eq.trans
    ((h.normalizationScheme_h_one_eq_sum_geometricGenusWeight_of_finiteDimensional
      hnormalization).trans h_totalWeight)

/-- The completed-axis genus formula when finite-dimensionality is known for first
cohomology of the curve itself, using the canonical normalization-pushforward
comparison. -/
theorem genusOver_eq_graph_genus_of_completedAxisComparisons_of_curve_finite
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [ConnectedSpace C]
    [UniversallyClosed (C ↘ Spec (CommRingCat.of k))]
    (h : C.IsNodalCurveOver k)
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    (h_componentCount : Nat.card (irreducibleComponents C) = G.vertexCount)
    (h_nodeCount : Nat.card (C.SplitNodePoints k) = G.edgeCount)
    (d : ∀ q : C.SplitNodePoints k,
      h.NormalizationNodeCompletedAxisComparison q)
    (hcurve : FiniteDimensional k (Modules.H (structureModule C) 1))
    (h_totalWeight :
      (letI : IsNoetherian C := h.isNoetherian
       letI := Fintype.ofFinite (irreducibleComponents C)
       ∑ Z, h.geometricGenusWeight Z) = G.totalWeight) :
    genusOver k C = G.genus :=
  h.genusOver_eq_graph_genus_of_completedAxisComparisons_of_curve_finite_of_H_one_comparison
    G h_componentCount h_nodeCount d hcurve
    h.normalizationPushforwardHOneComparison h_totalWeight

end IsNodalCurveOver

end AlgebraicGeometry.Scheme

end
