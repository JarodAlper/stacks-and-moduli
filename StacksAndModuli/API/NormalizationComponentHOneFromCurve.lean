module

public import StacksAndModuli.API.NormalizationComponentHOne

/-!
# First cohomology of a normalization from the curve

For a nodal curve, the normalization sequence transfers finite-dimensionality of first
cohomology from the curve to the normalization pushforward as soon as the normalization
defect has vanishing first cohomology.  If the canonical pushforward comparison is
bijective, this also gives finite-dimensional first cohomology for the normalization
scheme and for every normalized reduced irreducible component.

This file packages that transfer and combines it with the component decomposition of
normalization cohomology.  It is useful when proper-coherent-cohomology finiteness is
available for the original curve but not separately for each component.

## Main results

* `finiteDimensional_normalizationScheme_H_one_of_curve_of_defect_of_comparison`:
  transfer finite-dimensionality from the curve to its normalization.
* `finiteDimensional_normalizationScheme_H_one_of_curve_of_defect`:
  the unconditional transfer using the canonical normalization comparison.
* `finiteDimensional_normalizationScheme_H_one_of_curve_of_defect_of_exact`:
  the same transfer when abelian-sheaf pushforward is exact.
* `finiteDimensional_reducedComponentNormalization_H_one_of_curve_of_defect_of_comparison`:
  every normalized reduced component inherits finite-dimensional first cohomology.
* `normalizationPushforward_h_one_eq_sum_geometricGenusWeight_of_curve_of_defect`:
  compute normalization-pushforward first cohomology componentwise without a separate
  componentwise finiteness hypothesis.
* `normalizationPushforward_h_one_eq_sum_geometricGenusWeight_of_curve_of_defect_canonical`:
  the unconditional component formula using the canonical comparison.
* `genusOver_eq_graph_genus_of_nodeResidueSupportIso_of_curve_finite`:
  the nodal genus formula with finite-dimensionality assumed only on the curve.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Scheme

namespace IsNodalCurveOver

/-- Finite-dimensional first cohomology of a nodal curve transfers to its normalization
scheme when the normalization defect has vanishing first cohomology and the canonical
pushforward comparison is bijective. -/
theorem finiteDimensional_normalizationScheme_H_one_of_curve_of_defect_of_comparison
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (hdefect : Subsingleton
      (Modules.H h.normalizationDefectModule 1))
    (comparison : h.NormalizationPushforwardHOneComparison) :
    FiniteDimensional k
      (Modules.H (structureModule h.normalizationScheme) 1) := by
  let hpushforward : FiniteDimensional k
      (Modules.H h.normalizationPushforwardModule 1) :=
    h.finiteDimensional_normalizationPushforward_H_one_of_curve_of_defect
      hcurve hdefect
  let _ : FiniteDimensional k
      (Modules.H h.normalizationPushforwardModule 1) := hpushforward
  exact Module.Finite.equiv
    (h.normalizationPushforwardHOneLinearEquiv comparison)

/-- Finite-dimensional first cohomology of a nodal curve transfers to its
normalization scheme when the normalization defect has vanishing first
cohomology. -/
theorem finiteDimensional_normalizationScheme_H_one_of_curve_of_defect
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (hdefect : Subsingleton
      (Modules.H h.normalizationDefectModule 1)) :
    FiniteDimensional k
      (Modules.H (structureModule h.normalizationScheme) 1) :=
  h.finiteDimensional_normalizationScheme_H_one_of_curve_of_defect_of_comparison
    hcurve hdefect h.normalizationPushforwardHOneComparison

/-- Finite-dimensional first cohomology of a nodal curve transfers to its normalization
scheme when the normalization defect has vanishing first cohomology and abelian-sheaf
pushforward along normalization is exact. -/
theorem finiteDimensional_normalizationScheme_H_one_of_curve_of_defect_of_exact
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    [PreservesFiniteColimits
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.normalizationMap.base)]
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (hdefect : Subsingleton
      (Modules.H h.normalizationDefectModule 1)) :
    FiniteDimensional k
      (Modules.H (structureModule h.normalizationScheme) 1) :=
  h.finiteDimensional_normalizationScheme_H_one_of_curve_of_defect
    hcurve hdefect

/-- Under the same hypotheses, every normalized reduced irreducible component has
finite-dimensional first cohomology. -/
theorem finiteDimensional_reducedComponentNormalization_H_one_of_curve_of_defect_of_comparison
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (hdefect : Subsingleton
      (Modules.H h.normalizationDefectModule 1))
    (comparison : h.NormalizationPushforwardHOneComparison) :
    letI : IsNoetherian C := h.isNoetherian
    ∀ Z, FiniteDimensional k
      (Modules.H (structureModule
        (C.reducedIrreducibleComponentNormalization Z)) 1) := by
  let _ : IsReduced C := h.isReduced
  let _ : IsNoetherian C := h.isNoetherian
  let hnormalization : FiniteDimensional k
      (Modules.H (structureModule h.normalizationScheme) 1) :=
    h.finiteDimensional_normalizationScheme_H_one_of_curve_of_defect_of_comparison
      hcurve hdefect comparison
  exact fun Z ↦
    finiteDimensional_reducedComponentNormalization_H_one_of_normalization
      k C hnormalization Z

/-- Every normalized reduced irreducible component inherits
finite-dimensional first cohomology from the curve when the normalization
defect has vanishing first cohomology. -/
theorem finiteDimensional_reducedComponentNormalization_H_one_of_curve_of_defect
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (hdefect : Subsingleton
      (Modules.H h.normalizationDefectModule 1)) :
    letI : IsNoetherian C := h.isNoetherian
    ∀ Z, FiniteDimensional k
      (Modules.H (structureModule
        (C.reducedIrreducibleComponentNormalization Z)) 1) :=
  h.finiteDimensional_reducedComponentNormalization_H_one_of_curve_of_defect_of_comparison
    hcurve hdefect h.normalizationPushforwardHOneComparison

/-- Under exactness of abelian-sheaf pushforward along normalization, every normalized
reduced irreducible component inherits finite-dimensional first cohomology from the curve
when the normalization defect has vanishing first cohomology. -/
theorem finiteDimensional_reducedComponentNormalization_H_one_of_curve_of_defect_of_exact
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    [PreservesFiniteColimits
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.normalizationMap.base)]
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (hdefect : Subsingleton
      (Modules.H h.normalizationDefectModule 1)) :
    letI : IsNoetherian C := h.isNoetherian
    ∀ Z, FiniteDimensional k
      (Modules.H (structureModule
        (C.reducedIrreducibleComponentNormalization Z)) 1) :=
  h.finiteDimensional_reducedComponentNormalization_H_one_of_curve_of_defect
    hcurve hdefect

/-- If first cohomology of the curve is finite dimensional and first cohomology of the
normalization defect vanishes, the canonical pushforward comparison computes first
cohomology of the normalization pushforward as the sum of the component geometric genera.

No separate finite-dimensionality hypothesis on the normalized components is needed. -/
theorem normalizationPushforward_h_one_eq_sum_geometricGenusWeight_of_curve_of_defect
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (hdefect : Subsingleton
      (Modules.H h.normalizationDefectModule 1))
    (comparison : h.NormalizationPushforwardHOneComparison :=
      h.normalizationPushforwardHOneComparison) :
    Modules.h k h.normalizationPushforwardModule 1 =
      letI : IsNoetherian C := h.isNoetherian
      letI := Fintype.ofFinite (irreducibleComponents C)
      ∑ Z, h.geometricGenusWeight Z := by
  let _ : FiniteDimensional k
      (Modules.H h.normalizationPushforwardModule 1) :=
    h.finiteDimensional_normalizationPushforward_H_one_of_curve_of_defect
      hcurve hdefect
  let hnormalization : FiniteDimensional k
      (Modules.H (structureModule h.normalizationScheme) 1) :=
    Module.Finite.equiv
      (h.normalizationPushforwardHOneLinearEquiv comparison)
  exact (h.normalizationPushforwardHOneLinearEquiv comparison).finrank_eq.trans
    (h.normalizationScheme_h_one_eq_sum_geometricGenusWeight_of_finiteDimensional
      hnormalization)

/-- If first cohomology of the curve is finite dimensional and first
cohomology of the normalization defect vanishes, normalization-pushforward
first cohomology is the sum of the component genera. -/
theorem
    normalizationPushforward_h_one_eq_sum_geometricGenusWeight_of_curve_of_defect_canonical
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (hdefect : Subsingleton
      (Modules.H h.normalizationDefectModule 1)) :
    Modules.h k h.normalizationPushforwardModule 1 =
      letI : IsNoetherian C := h.isNoetherian
      letI := Fintype.ofFinite (irreducibleComponents C)
      ∑ Z, h.geometricGenusWeight Z :=
  h.normalizationPushforward_h_one_eq_sum_geometricGenusWeight_of_curve_of_defect
    hcurve hdefect h.normalizationPushforwardHOneComparison

/-- If first cohomology of the curve is finite dimensional, the normalization defect has
vanishing first cohomology, and abelian-sheaf pushforward along normalization is exact,
then normalization-pushforward first cohomology is the sum of the component genera. -/
theorem normalizationPushforward_h_one_eq_sum_geometricGenusWeight_of_curve_of_defect_of_exact
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    [PreservesFiniteColimits
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.normalizationMap.base)]
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (hdefect : Subsingleton
      (Modules.H h.normalizationDefectModule 1)) :
    Modules.h k h.normalizationPushforwardModule 1 =
      letI : IsNoetherian C := h.isNoetherian
      letI := Fintype.ofFinite (irreducibleComponents C)
      ∑ Z, h.geometricGenusWeight Z :=
  h.normalizationPushforward_h_one_eq_sum_geometricGenusWeight_of_curve_of_defect_canonical
    hcurve hdefect

/-- A proper connected nodal curve has the genus of a supplied weighted graph after
identifying its normalization defect with one residue-field module per node, assuming
finite-dimensional first cohomology only for the curve and bijectivity of the canonical
normalization-pushforward comparison.

The normalization exact sequence and component decomposition derive every
normalization-side finiteness input. -/
theorem genusOver_eq_graph_genus_of_nodeResidueSupportIso_of_curve_finite
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [ConnectedSpace C]
    [UniversallyClosed (C ↘ Spec (CommRingCat.of k))]
    (h : IsNodalCurveOver k C)
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    (h_componentCount : Nat.card (irreducibleComponents C) = G.vertexCount)
    (h_nodeCount : Nat.card (C.SplitNodePoints k) = G.edgeCount)
    (e : h.normalizationDefectModule ≅ h.nodeResidueSupportModule)
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (comparison : h.NormalizationPushforwardHOneComparison :=
      h.normalizationPushforwardHOneComparison)
    (h_totalWeight :
      (letI : IsNoetherian C := h.isNoetherian
       letI := Fintype.ofFinite (irreducibleComponents C)
       ∑ Z, h.geometricGenusWeight Z) = G.totalWeight) :
    genusOver k C = G.genus := by
  let hdefect : Subsingleton
      (Modules.H h.normalizationDefectModule 1) :=
    h.subsingleton_H_normalizationDefectModule_one_of_nodeResidueSupportIso e
  let hpushforward : FiniteDimensional k
      (Modules.H h.normalizationPushforwardModule 1) :=
    h.finiteDimensional_normalizationPushforward_H_one_of_curve_of_defect
      hcurve hdefect
  apply h.genusOver_eq_graph_genus G h_componentCount
  exact IsNodalCurveOver.NormalizationCohomologyData.of_nodeResidueSupportIso
    h G h_nodeCount e hpushforward
    ((h.normalizationPushforward_h_one_eq_sum_geometricGenusWeight_of_curve_of_defect
      hcurve hdefect comparison).trans h_totalWeight)

/-- A proper connected nodal curve has the genus of a supplied weighted graph
after identifying its normalization defect with one residue-field module per
node, assuming finite-dimensional first cohomology only for the curve. -/
theorem genusOver_eq_graph_genus_of_nodeResidueSupportIso_of_curve_finite_canonical
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [ConnectedSpace C]
    [UniversallyClosed (C ↘ Spec (CommRingCat.of k))]
    (h : IsNodalCurveOver k C)
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    (h_componentCount : Nat.card (irreducibleComponents C) = G.vertexCount)
    (h_nodeCount : Nat.card (C.SplitNodePoints k) = G.edgeCount)
    (e : h.normalizationDefectModule ≅ h.nodeResidueSupportModule)
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (h_totalWeight :
      (letI : IsNoetherian C := h.isNoetherian
       letI := Fintype.ofFinite (irreducibleComponents C)
       ∑ Z, h.geometricGenusWeight Z) = G.totalWeight) :
    genusOver k C = G.genus :=
  h.genusOver_eq_graph_genus_of_nodeResidueSupportIso_of_curve_finite G
    h_componentCount h_nodeCount e hcurve
    h.normalizationPushforwardHOneComparison h_totalWeight

/-- A proper connected nodal curve has the genus of a supplied weighted graph after
identifying its normalization defect with one residue-field module per node, provided
first cohomology of the curve is finite dimensional and abelian-sheaf pushforward along
normalization is exact. -/
theorem genusOver_eq_graph_genus_of_nodeResidueSupportIso_of_curve_finite_of_exact
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [ConnectedSpace C]
    [UniversallyClosed (C ↘ Spec (CommRingCat.of k))]
    (h : IsNodalCurveOver k C)
    [PreservesFiniteColimits
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.normalizationMap.base)]
    {n : ℕ} {VertexType : Type v} {EdgeType : Type w}
    (G : VertexWeightedMarkedGraph n VertexType EdgeType)
    (h_componentCount : Nat.card (irreducibleComponents C) = G.vertexCount)
    (h_nodeCount : Nat.card (C.SplitNodePoints k) = G.edgeCount)
    (e : h.normalizationDefectModule ≅ h.nodeResidueSupportModule)
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (h_totalWeight :
      (letI : IsNoetherian C := h.isNoetherian
       letI := Fintype.ofFinite (irreducibleComponents C)
       ∑ Z, h.geometricGenusWeight Z) = G.totalWeight) :
    genusOver k C = G.genus :=
  h.genusOver_eq_graph_genus_of_nodeResidueSupportIso_of_curve_finite_canonical G
    h_componentCount h_nodeCount e hcurve h_totalWeight

end IsNodalCurveOver

end AlgebraicGeometry.Scheme

end
