module

public import StacksAndModuli.API.IrreducibleComponentGeometricGenus
public import StacksAndModuli.API.NodalCurveCompletedGenusFormula
public import StacksAndModuli.API.NodalCurveFiniteness
public import StacksAndModuli.API.NodalCurveDefectStalkwiseIso
public import StacksAndModuli.API.NodalCurveGenusFormula
public import StacksAndModuli.API.NormalizationComponentHOneFromCurve
public import StacksAndModuli.API.SmoothPointComponents
public import StacksAndModuli.API.SplitNodeIncidenceGraphConnected
public import StacksAndModuli.API.StableMarkedGraph
public import StacksAndModuli.«Section6.3-Stable».«part6.3.1-definition»

/-!
# Stable curves: dual graphs

This module formalizes Definition 6.3.9 in §6.3 (Stable curves) of *Stacks and
Moduli*, section label
`sec:stable-curves`.

For a connected nodal curve, the underlying multigraph has irreducible components as
vertices and split nodes as edges. The two completed-local formal branches of a node
determine its endpoints, retaining self-nodes as loops and distinct nodes as parallel
edges. A vertex is weighted by the genus of the normalization of the corresponding
reduced irreducible component. Every smooth marking is assigned to the unique component
containing it.

The reusable abstract notions of finite vertex-weighted marked graph, graph genus,
loop-aware valence, and graph stability are defined in
`StacksAndModuli/API/StableMarkedGraph.lean`. Finiteness and connectedness of the geometric
incidence graph, and the component geometric-genus construction, are supplied by the
supporting API imported above.

## Main definition

* `AlgebraicGeometry.Scheme.IsPrestableNMarkedCurveOfGenusOver.dualGraph`: the book's dual
  graph of an `n`-pointed prestable curve.

## Supporting construction and API

* `AlgebraicGeometry.Scheme.nodalMarkedDualGraph`: the more general construction for a
  connected nodal curve with smooth ordered markings.
* `AlgebraicGeometry.Scheme.nodalMarkedDualGraph_toGraph`: the underlying multigraph is
  the split-node incidence graph.
* `AlgebraicGeometry.Scheme.nodalMarkedDualGraph_weight`: vertex weights are component
  geometric genera.
* `AlgebraicGeometry.Scheme.nodalMarkedDualGraph_marking_mem`: each marked point lies on
  the component to which the graph marking assigns it.
* `AlgebraicGeometry.Scheme.IsPrestableNMarkedCurveOfGenusOver.dualGraph_marking_eq_iff_point_mem`:
  the graph marking selects exactly the components containing the marked point.
* `IsPrestableNMarkedCurveOfGenusOver.dualGraph_markingMultiplicity_eq_ncard`:
  marking multiplicity counts the marking indices lying on a component.
* `IsPrestableNMarkedCurveOfGenusOver.dualGraph_valence_eq_node_ncard_add_selfNode_ncard`:
  graph valence counts each node on a component once and each self-node once more.
* `IsPrestableNMarkedCurveOfGenusOver.dualGraph_specialValence_eq_counts`:
  special valence adds the marking indices lying on the component to that node count.
* `IsPrestableNMarkedCurveOfGenusOver.dualGraph_genus_eq`:
  the genus formula after supplying the remaining normalization-cohomology computations.
* `IsPrestableNMarkedCurveOfGenusOver.dualGraph_genus_eq_of_nodeResidueSupportIso`:
  the reduced formula after identifying the defect with one residue module per node.
* `dualGraph_genus_eq_of_nodeResidueSupportIso_of_H_one_comparison`:
  the further reduction to componentwise finiteness and pushforward comparison.
* `dualGraph_genus_eq_of_nodeResidueSupportIso_of_curve_finite`:
  finite-dimensional curve cohomology and the canonical affine-normalization comparison
  remove all normalization-side cohomology premises.
* `dualGraph_genus_eq_of_nodeResidueSupportIso_of_curve_finite_of_H_one_comparison`:
  compatibility form accepting an explicit normalization-pushforward comparison.
* `dualGraph_genus_eq_of_nodeResidueSupportIso_of_curve_finite_of_exact`:
  compatibility form retaining the former exact-pushforward instance.
* `dualGraph_genus_eq_of_nodeResidueSupportIso_of_H_one_comparison_of_pos`:
  for positive genus, the same reduction needs no separate cohomology-finiteness input.
* `dualGraph_genus_eq_of_completedAxisComparisons`:
  completed-axis comparisons and component finiteness imply the genus formula canonically.
* `dualGraph_genus_eq_of_completedAxisComparisons_of_pos`:
  positive genus removes the final finiteness input from the completed-axis reduction.
* The corresponding `_of_H_one_comparison` declarations retain compatibility with an
  explicitly supplied normalization-pushforward comparison.
* `dualGraph_genus_eq_of_stalkwise_defect_of_H_one_comparison`:
  it is enough for one global defect comparison to be an isomorphism at every node.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

section DefDualGraph

namespace AlgebraicGeometry.Scheme

/-- Background definition for Definition 6.3.9 (reusable nodal-marked form): the
vertex-weighted marked dual graph of a connected nodal curve with smooth ordered
markings.

Vertices are irreducible components, edges are split nodes, and formal branches determine
edge endpoints. The weight of a component is the genus over `k` of the normalization of
its reduced induced subscheme. A marking is sent to the unique component containing its
smooth point. Local Noetherianity is the technical hypothesis needed to contract formal
branches to components; it follows from nodality in every book-facing application. -/
noncomputable def nodalMarkedDualGraph
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian C] {n : ℕ}
    (h : IsNodalCurveOver k C) (hconnected : ConnectedSpace C)
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k)))
    (hp : ∀ i, ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth) :
    VertexWeightedMarkedGraph n (irreducibleComponents C) (C.SplitNodePoints k) := by
  let _ : IsNodalCurveOver k C := h
  let _ : ConnectedSpace C := hconnected
  exact
    { toGraph := C.splitNodeIncidenceGraph k
      vertexSet_finite := h.splitNodeIncidenceGraph_vertexSet_finite
      edgeSet_finite := h.splitNodeIncidenceGraph_edgeSet_finite
      connected := h.splitNodeIncidenceGraph_connected
      weight := fun Z ↦ h.geometricGenusWeight Z.1
      marking := fun i ↦
        ⟨C.smoothSectionComponent (C ↘ Spec (CommRingCat.of k)) p hp i, Set.mem_univ _⟩ }

/-- Helper lemma for Definition 6.3.9: the graph underlying
`nodalMarkedDualGraph` is the split-node incidence graph. -/
@[simp]
theorem nodalMarkedDualGraph_toGraph
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian C] {n : ℕ}
    (h : IsNodalCurveOver k C) (hconnected : ConnectedSpace C)
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k)))
    (hp : ∀ i, ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth) :
    (nodalMarkedDualGraph h hconnected p hp).toGraph = C.splitNodeIncidenceGraph k :=
  rfl

/-- Helper lemma for Definition 6.3.9: evaluating the dual-graph weight at a
vertex returns the geometric genus of its irreducible component. -/
@[simp]
theorem nodalMarkedDualGraph_weight
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian C] {n : ℕ}
    (h : IsNodalCurveOver k C) (hconnected : ConnectedSpace C)
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k)))
    (hp : ∀ i, ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth)
    (Z : (nodalMarkedDualGraph h hconnected p hp).Vertex) :
    (nodalMarkedDualGraph h hconnected p hp).weight Z = h.geometricGenusWeight Z.1 :=
  rfl

/-- Helper lemma for Definition 6.3.9: the component underlying the graph marking
is the canonical component of the corresponding smooth section. -/
@[simp]
theorem nodalMarkedDualGraph_marking_val
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian C] {n : ℕ}
    (h : IsNodalCurveOver k C) (hconnected : ConnectedSpace C)
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k)))
    (hp : ∀ i, ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth)
    (i : Fin n) :
    ((nodalMarkedDualGraph h hconnected p hp).marking i).1 =
      C.smoothSectionComponent (C ↘ Spec (CommRingCat.of k)) p hp i :=
  rfl

/-- Helper lemma for Definition 6.3.9: every marked point lies on the irreducible
component selected by its graph marking. -/
theorem nodalMarkedDualGraph_marking_mem
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian C] {n : ℕ}
    (h : IsNodalCurveOver k C) (hconnected : ConnectedSpace C)
    (p : Fin n → C.SectionOver (Spec (CommRingCat.of k)))
    (hp : ∀ i, ((C ↘ Spec (CommRingCat.of k)).stalkMap (p i).point).hom.FormallySmooth)
    (i : Fin n) :
    (p i).point ∈ ((nodalMarkedDualGraph h hconnected p hp).marking i).1.1 := by
  exact C.smoothSectionComponent_mem (C ↘ Spec (CommRingCat.of k)) p hp i

/-- **Definition 6.3.9** (`def:dual-graph`): the dual graph of an `n`-pointed prestable
curve of genus `g`.

The prestability witness supplies nodality, connectedness, and smoothness of the marked
points. Its projectivity and specified total genus are not needed to assemble the graph,
but are part of the book's domain of definition. -/
noncomputable def IsPrestableNMarkedCurveOfGenusOver.dualGraph
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) :
    VertexWeightedMarkedGraph n (irreducibleComponents C) (C.SplitNodePoints k) := by
  let _ : IsNoetherian C := h.nodal.isNoetherian
  exact nodalMarkedDualGraph h.nodal h.connected p h.mark_smooth

/-- Helper lemma for Definition 6.3.9: the underlying graph of a prestable curve's
dual graph is its split-node incidence graph. -/
@[simp]
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_toGraph
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) :
    let _ : IsNoetherian C := h.nodal.isNoetherian
    h.dualGraph.toGraph = C.splitNodeIncidenceGraph k := by
  dsimp
  rfl

/-- Helper lemma for Definition 6.3.9: the vertex weights of a prestable curve's
dual graph are its irreducible-component geometric genera. -/
@[simp]
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_weight
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (Z : h.dualGraph.Vertex) :
    h.dualGraph.weight Z = h.nodal.geometricGenusWeight Z.1 :=
  rfl

/-- Helper lemma for Definition 6.3.9: the number of dual-graph vertices is the
number of irreducible components of the curve. -/
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_vertexCount
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) :
    h.dualGraph.vertexCount = Nat.card (irreducibleComponents C) := by
  rw [VertexWeightedMarkedGraph.vertexCount]
  change Nat.card (Set.univ : Set (irreducibleComponents C)) = _
  exact Nat.card_congr (Equiv.Set.univ _)

/-- Helper lemma for Definition 6.3.9: the number of dual-graph edges is the number
of split nodes of the curve. -/
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_edgeCount
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) :
    h.dualGraph.edgeCount = Nat.card (C.SplitNodePoints k) := by
  rw [VertexWeightedMarkedGraph.edgeCount]
  change Nat.card (Set.univ : Set (C.SplitNodePoints k)) = _
  exact Nat.card_congr (Equiv.Set.univ _)

/-- **Exercise 6.3.10** (unlabelled; component-weight computation): the total weight of
the dual graph is the sum of the geometric genera of the normalized reduced irreducible
components. -/
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_totalWeight_eq_sum_geometricGenusWeight
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) :
    h.dualGraph.totalWeight =
      letI : IsNoetherian C := h.nodal.isNoetherian
      letI := Fintype.ofFinite (irreducibleComponents C)
      ∑ Z, h.nodal.geometricGenusWeight Z := by
  let _ : IsNoetherian C := h.nodal.isNoetherian
  let _ : Fintype (irreducibleComponents C) := Fintype.ofFinite _
  let _ : Fintype h.dualGraph.Vertex := Fintype.ofFinite _
  rw [VertexWeightedMarkedGraph.totalWeight_eq]
  let e : h.dualGraph.Vertex ≃ irreducibleComponents C :=
    { toFun := Subtype.val
      invFun := fun Z ↦ ⟨Z, Set.mem_univ Z⟩
      left_inv := fun Z ↦ Subtype.ext rfl
      right_inv := fun _ ↦ rfl }
  apply Fintype.sum_equiv e
  intro Z
  rfl

/-- **Exercise 6.3.10** (unlabelled; normalization input): degree-zero cohomology of
the normalization pushforward counts the vertices of a prestable curve's dual graph. -/
theorem IsPrestableNMarkedCurveOfGenusOver.normalizationPushforward_h_zero_eq_vertexCount
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) :
    Modules.h k h.nodal.normalizationPushforwardModule 0 =
      h.dualGraph.vertexCount := by
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := h.proper
  exact h.nodal.normalizationPushforward_h_zero_eq_componentCount.trans
    h.dualGraph_vertexCount.symm

/-- **Exercise 6.3.10** (unlabelled; node-defect model): degree-zero cohomology of one
residue-field module at every node counts the edges of the dual graph. -/
theorem IsPrestableNMarkedCurveOfGenusOver.nodeResidueSupportModule_h_zero_eq_edgeCount
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) :
    Modules.h k h.nodal.nodeResidueSupportModule 0 =
      h.dualGraph.edgeCount :=
  h.nodal.h_nodeResidueSupportModule_zero.trans h.dualGraph_edgeCount.symm

/-- **Exercise 6.3.10** (unlabelled; conditional genus-formula bridge): a prestable
curve's dual graph has the specified genus once the standard normalization-cohomology
computations are supplied.

The canonical normalization sequence and its injectivity are already proved in
`NodalCurveGenusFormula`; the data argument records the remaining component-decomposition,
node-defect, and cohomological-finiteness inputs. Connectedness and properness from
prestability supply the degree-zero structure-sheaf cohomology automatically. -/
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_genus_eq
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (D : h.nodal.NormalizationCohomologyData h.dualGraph) :
    h.dualGraph.genus = g := by
  let _ : ConnectedSpace C := h.connected
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := h.proper
  exact (h.nodal.genusOver_eq_graph_genus h.dualGraph
    h.dualGraph_vertexCount.symm D).symm.trans h.genus_eq

/-- **Exercise 6.3.10** (unlabelled; point-support reduction): the dual graph has the
curve's specified genus after comparing the normalization defect with one residue-field
module at each node and computing first cohomology of the normalization. -/
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_genus_eq_of_nodeResidueSupportIso
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (e : h.nodal.normalizationDefectModule ≅
      h.nodal.nodeResidueSupportModule)
    (normalization_H_one_finiteDimensional :
      FiniteDimensional k
        (Modules.H h.nodal.normalizationPushforwardModule 1))
    (normalization_h_one :
      Modules.h k h.nodal.normalizationPushforwardModule 1 =
        h.dualGraph.totalWeight) :
    h.dualGraph.genus = g :=
  h.dualGraph_genus_eq
    (IsNodalCurveOver.NormalizationCohomologyData.of_nodeResidueSupportIso
      h.nodal h.dualGraph h.dualGraph_edgeCount.symm e
      normalization_H_one_finiteDimensional normalization_h_one)

namespace IsPrestableNMarkedCurveOfGenusOver

open IsNodalCurveOver

/-- **Exercise 6.3.10** (unlabelled; componentwise normalization reduction): the dual
graph has the curve's specified genus after identifying the normalization defect with one
residue-field module per node and comparing first cohomology of the normalization
pushforward with first cohomology of the normalization scheme.

The latter is computed componentwise as the sum of the geometric genera. -/
theorem dualGraph_genus_eq_of_nodeResidueSupportIso_of_H_one_comparison
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (e : h.nodal.normalizationDefectModule ≅
      h.nodal.nodeResidueSupportModule)
    (hfinite :
      letI : IsNoetherian C := h.nodal.isNoetherian
      ∀ Z, FiniteDimensional k
        (Modules.H (structureModule
          (C.reducedIrreducibleComponentNormalization Z)) 1))
    (comparison : h.nodal.NormalizationPushforwardHOneComparison) :
    h.dualGraph.genus = g := by
  apply h.dualGraph_genus_eq_of_nodeResidueSupportIso e
  · exact h.nodal.finiteDimensional_normalizationPushforward_H_one_of_comparison
      hfinite comparison
  · exact
      (h.nodal.normalizationPushforward_h_one_eq_sum_geometricGenusWeight_of_comparison
        hfinite comparison).trans
        h.dualGraph_totalWeight_eq_sum_geometricGenusWeight.symm

/-- **Exercise 6.3.10** (unlabelled; explicit-comparison compatibility form): the dual
graph has the curve's specified genus after identifying the normalization defect with one
residue-field module per node, assuming finite-dimensional first cohomology of the curve
and a supplied normalization-pushforward comparison.

The normalization sequence transfers finite-dimensionality to the normalization
pushforward; no separate componentwise finiteness hypothesis is needed. -/
theorem dualGraph_genus_eq_of_nodeResidueSupportIso_of_curve_finite_of_H_one_comparison
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (e : h.nodal.normalizationDefectModule ≅
      h.nodal.nodeResidueSupportModule)
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1))
    (comparison : h.nodal.NormalizationPushforwardHOneComparison) :
    h.dualGraph.genus = g := by
  let _ : ConnectedSpace C := h.connected
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := h.proper
  exact
    (h.nodal.genusOver_eq_graph_genus_of_nodeResidueSupportIso_of_curve_finite
      h.dualGraph h.dualGraph_vertexCount.symm h.dualGraph_edgeCount.symm e
      hcurve comparison
      h.dualGraph_totalWeight_eq_sum_geometricGenusWeight.symm).symm.trans
      h.genus_eq

/-- **Exercise 6.3.10** (unlabelled; curve-cohomology finiteness reduction): the dual
graph has the curve's specified genus after identifying the normalization defect with one
residue-field module per node and assuming finite-dimensional first cohomology only for
the curve itself.

The normalization sequence transfers finite-dimensionality to the normalization
pushforward, while the affine normalization map supplies the canonical first-cohomology
comparison. -/
theorem dualGraph_genus_eq_of_nodeResidueSupportIso_of_curve_finite
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (e : h.nodal.normalizationDefectModule ≅
      h.nodal.nodeResidueSupportModule)
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1)) :
    h.dualGraph.genus = g := by
  let _ : ConnectedSpace C := h.connected
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := h.proper
  exact
    (h.nodal.genusOver_eq_graph_genus_of_nodeResidueSupportIso_of_curve_finite_canonical
      h.dualGraph h.dualGraph_vertexCount.symm h.dualGraph_edgeCount.symm e
      hcurve h.dualGraph_totalWeight_eq_sum_geometricGenusWeight.symm).symm.trans
      h.genus_eq

/-- **Exercise 6.3.10** (unlabelled; exact-pushforward compatibility form): the dual
graph has the curve's specified genus after identifying the normalization defect with one
residue-field module per node and assuming finite-dimensional first cohomology of the
curve.

The exactness instance is retained for source compatibility; the affine normalization
comparison now proves the result without using it. -/
theorem dualGraph_genus_eq_of_nodeResidueSupportIso_of_curve_finite_of_exact
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    [CategoryTheory.Limits.PreservesFiniteColimits
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.nodal.normalizationMap.base)]
    (e : h.nodal.normalizationDefectModule ≅
      h.nodal.nodeResidueSupportModule)
    (hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1)) :
    h.dualGraph.genus = g :=
  h.dualGraph_genus_eq_of_nodeResidueSupportIso_of_curve_finite e hcurve

/-- **Exercise 6.3.10** (unlabelled; completed-axis reduction): the dual graph has the
curve's specified genus after comparing the completed normalization-defect stalk at each
node with the standard coordinate-axis defect and computing componentwise first
cohomology. The normalization-pushforward comparison is canonical. -/
theorem dualGraph_genus_eq_of_completedAxisComparisons
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (d : ∀ q : C.SplitNodePoints k,
      h.nodal.NormalizationNodeCompletedAxisComparison q)
    (hfinite :
      letI : IsNoetherian C := h.nodal.isNoetherian
      ∀ Z, FiniteDimensional k
        (Modules.H (structureModule
          (C.reducedIrreducibleComponentNormalization Z)) 1)) :
    h.dualGraph.genus = g := by
  let _ : ConnectedSpace C := h.connected
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := h.proper
  exact
    (h.nodal.genusOver_eq_graph_genus_of_completedAxisComparisons_of_component_finite
      h.dualGraph h.dualGraph_vertexCount.symm h.dualGraph_edgeCount.symm d
      hfinite h.dualGraph_totalWeight_eq_sum_geometricGenusWeight.symm).symm.trans
      h.genus_eq

/-- **Exercise 6.3.10** (unlabelled; explicit-comparison compatibility form): the dual
graph has the curve's specified genus after completed-axis comparisons, componentwise
first-cohomology finiteness, and a supplied normalization-pushforward comparison. -/
theorem dualGraph_genus_eq_of_completedAxisComparisons_of_H_one_comparison
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (d : ∀ q : C.SplitNodePoints k,
      h.nodal.NormalizationNodeCompletedAxisComparison q)
    (hfinite :
      letI : IsNoetherian C := h.nodal.isNoetherian
      ∀ Z, FiniteDimensional k
        (Modules.H (structureModule
          (C.reducedIrreducibleComponentNormalization Z)) 1))
    (comparison : h.nodal.NormalizationPushforwardHOneComparison) :
    h.dualGraph.genus = g := by
  let _ : ConnectedSpace C := h.connected
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := h.proper
  exact
    (h.nodal.genusOver_eq_graph_genus_of_completedAxisComparisons_of_H_one_comparison
      h.dualGraph h.dualGraph_vertexCount.symm h.dualGraph_edgeCount.symm d
      hfinite comparison
      h.dualGraph_totalWeight_eq_sum_geometricGenusWeight.symm).symm.trans
      h.genus_eq

/-- **Exercise 6.3.10** (unlabelled; node-stalk reduction): the dual graph has the
curve's specified genus once a global normalization-defect comparison is an isomorphism
on every node stalk, component cohomology is finite dimensional, and the canonical
normalization-pushforward cohomology map is bijective. -/
theorem dualGraph_genus_eq_of_stalkwise_defect_of_H_one_comparison
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (f : h.nodal.normalizationDefectModule ⟶
      h.nodal.nodeResidueSupportModule)
    (hf : ∀ x : C, C.IsSplitNodeAt k x → IsIso
      ((Modules.toPresheaf C ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f))
    (hfinite :
      letI : IsNoetherian C := h.nodal.isNoetherian
      ∀ Z, FiniteDimensional k
        (Modules.H (structureModule
          (C.reducedIrreducibleComponentNormalization Z)) 1))
    (comparison : h.nodal.NormalizationPushforwardHOneComparison) :
    h.dualGraph.genus = g :=
  h.dualGraph_genus_eq_of_nodeResidueSupportIso_of_H_one_comparison
    (h.nodal.normalizationDefectIsoNodeResidueSupportOfStalkwise f hf)
    hfinite comparison

/-- **Exercise 6.3.10** (unlabelled; positive-genus normalization reduction): for a
positive-genus prestable curve, the dual graph has the specified genus after identifying
the normalization defect with one residue-field module per node and comparing first
cohomology across normalization pushforward.

No separate finiteness hypothesis is needed: positivity of the specified curve genus
makes the curve's first cohomology finite dimensional, and the normalization exact
sequence transfers that finiteness to the normalization. -/
theorem dualGraph_genus_eq_of_nodeResidueSupportIso_of_H_one_comparison_of_pos
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (hg : 0 < g)
    (e : h.nodal.normalizationDefectModule ≅
      h.nodal.nodeResidueSupportModule)
    (comparison : h.nodal.NormalizationPushforwardHOneComparison) :
    h.dualGraph.genus = g := by
  let hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1) :=
    FiniteDimensional.of_finrank_pos (by
      rw [← genusOver_def, h.genus_eq]
      exact hg)
  let hdefect : Subsingleton
      (Modules.H h.nodal.normalizationDefectModule 1) :=
    h.nodal.subsingleton_H_normalizationDefectModule_one_of_nodeResidueSupportIso e
  let hpushforward : FiniteDimensional k
      (Modules.H h.nodal.normalizationPushforwardModule 1) :=
    h.nodal.finiteDimensional_normalizationPushforward_H_one_of_curve_of_defect
      hcurve hdefect
  let hnormalization : FiniteDimensional k
      (Modules.H (structureModule h.nodal.normalizationScheme) 1) :=
    Module.Finite.equiv
      (h.nodal.normalizationPushforwardHOneLinearEquiv comparison)
  apply h.dualGraph_genus_eq_of_nodeResidueSupportIso e hpushforward
  exact (h.nodal.normalizationPushforwardHOneLinearEquiv comparison).finrank_eq.trans
    ((h.nodal.normalizationScheme_h_one_eq_sum_geometricGenusWeight_of_finiteDimensional
      hnormalization).trans
      h.dualGraph_totalWeight_eq_sum_geometricGenusWeight.symm)

/-- **Exercise 6.3.10** (unlabelled; positive-genus completed-axis reduction): for a
positive-genus prestable curve, completed-axis comparisons at the nodes imply the
dual-graph genus formula. Positivity supplies the only finite-dimensionality input, and
the normalization-pushforward comparison is canonical. -/
theorem dualGraph_genus_eq_of_completedAxisComparisons_of_pos
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (hg : 0 < g)
    (d : ∀ q : C.SplitNodePoints k,
      h.nodal.NormalizationNodeCompletedAxisComparison q) :
    h.dualGraph.genus = g := by
  let _ : ConnectedSpace C := h.connected
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := h.proper
  let hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1) :=
    FiniteDimensional.of_finrank_pos (by
      rw [← genusOver_def, h.genus_eq]
      exact hg)
  exact
    (h.nodal.genusOver_eq_graph_genus_of_completedAxisComparisons_of_curve_finite
      h.dualGraph h.dualGraph_vertexCount.symm h.dualGraph_edgeCount.symm d
      hcurve h.dualGraph_totalWeight_eq_sum_geometricGenusWeight.symm).symm.trans
      h.genus_eq

/-- **Exercise 6.3.10** (unlabelled; positive-genus explicit-comparison compatibility
form): completed-axis comparisons and a supplied normalization-pushforward comparison
imply the dual-graph genus formula. Positivity supplies the only finiteness input. -/
theorem dualGraph_genus_eq_of_completedAxisComparisons_of_H_one_comparison_of_pos
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (hg : 0 < g)
    (d : ∀ q : C.SplitNodePoints k,
      h.nodal.NormalizationNodeCompletedAxisComparison q)
    (comparison : h.nodal.NormalizationPushforwardHOneComparison) :
    h.dualGraph.genus = g := by
  let _ : ConnectedSpace C := h.connected
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := h.proper
  let hcurve : FiniteDimensional k
      (Modules.H (structureModule C) 1) :=
    FiniteDimensional.of_finrank_pos (by
      rw [← genusOver_def, h.genus_eq]
      exact hg)
  exact
    (genusOver_eq_graph_genus_of_completedAxisComparisons_of_curve_finite_of_H_one_comparison
      h.nodal h.dualGraph h.dualGraph_vertexCount.symm h.dualGraph_edgeCount.symm d
      hcurve comparison
      h.dualGraph_totalWeight_eq_sum_geometricGenusWeight.symm).symm.trans
      h.genus_eq

/-- **Exercise 6.3.10** (unlabelled; positive-genus node-stalk reduction): at positive
genus, a global defect comparison that is an isomorphism at every node and bijectivity of
the canonical normalization-pushforward cohomology map imply the dual-graph genus formula
without a separate finiteness input. -/
theorem dualGraph_genus_eq_of_stalkwise_defect_of_H_one_comparison_of_pos
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (hg : 0 < g)
    (f : h.nodal.normalizationDefectModule ⟶
      h.nodal.nodeResidueSupportModule)
    (hf : ∀ x : C, C.IsSplitNodeAt k x → IsIso
      ((Modules.toPresheaf C ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f))
    (comparison : h.nodal.NormalizationPushforwardHOneComparison) :
    h.dualGraph.genus = g :=
  h.dualGraph_genus_eq_of_nodeResidueSupportIso_of_H_one_comparison_of_pos hg
    (h.nodal.normalizationDefectIsoNodeResidueSupportOfStalkwise f hf)
    comparison

end IsPrestableNMarkedCurveOfGenusOver

/-- Background definition for Definition 6.3.9: the set of split nodes lying on an
irreducible component. -/
def splitNodesOnComponent
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (Z : irreducibleComponents C) : Set (C.SplitNodePoints k) :=
  {q | q.1 ∈ Z.1}

/-- Background definition for Definition 6.3.9: the set of self-nodes of an irreducible
component, namely the nodes whose two formal branches belong to that component. -/
noncomputable def IsNodalCurveOver.selfNodesOnComponent
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (h : IsNodalCurveOver k C) (Z : irreducibleComponents C) :
    Set (C.SplitNodePoints k) := by
  let _ : IsNoetherian C := h.isNoetherian
  exact {q | q.incidentComponents = {Z}}

/-- Helper lemma for Definition 6.3.9: incident dual-graph edges at a component
are in bijection with the distinct split nodes lying on that component. -/
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_incidentEdgesAt_ncard
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (Z : h.dualGraph.Vertex) :
    (h.dualGraph.incidentEdgesAt Z).ncard =
      (splitNodesOnComponent (k := k) Z.1).ncard := by
  let _ : IsNoetherian C := h.nodal.isNoetherian
  apply Set.ncard_congr (fun e _ ↦ e.1)
  · intro e he
    have he' := (h.dualGraph.mem_incidentEdgesAt_iff Z e).mp he
    obtain ⟨W, hlink⟩ := he'
    have hlink' : (C.splitNodeIncidenceGraph k).IsLink e.1 Z.1 W.1 := by
      change (C.splitNodeIncidenceGraph k).IsLink e.1 Z.1 W.1 at hlink
      exact hlink
    change e.1.1 ∈ Z.1.1
    exact e.1.mem_component_of_inc Z.1 ⟨W.1, hlink'⟩
  · intro a b _ _ hab
    exact Subtype.ext hab
  · intro q hq
    let e : h.dualGraph.Edge := ⟨q, Set.mem_univ _⟩
    refine ⟨e, ?_, rfl⟩
    rw [h.dualGraph.mem_incidentEdgesAt_iff]
    have hinc : (C.splitNodeIncidenceGraph k).Inc q Z.1 := by
      rw [splitNodeIncidenceGraph_inc_iff_mem_incidentComponents]
      exact q.mem_incidentComponents_of_mem Z.1 hq
    obtain ⟨W, hlink⟩ := hinc
    refine ⟨⟨W, Set.mem_univ _⟩, ?_⟩
    change (C.splitNodeIncidenceGraph k).IsLink q Z.1 W
    exact hlink

/-- Helper lemma for Definition 6.3.9: loop edges at a component are in
bijection with its self-nodes. -/
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_loopEdgesAt_ncard
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (Z : h.dualGraph.Vertex) :
    (h.dualGraph.loopEdgesAt Z).ncard =
      (h.nodal.selfNodesOnComponent Z.1).ncard := by
  let _ : IsNoetherian C := h.nodal.isNoetherian
  apply Set.ncard_congr (fun e _ ↦ e.1)
  · intro e he
    change h.dualGraph.toGraph.IsLink e.1 Z.1 Z.1 at he
    change e.1.incidentComponents = {Z.1}
    change (C.splitNodeIncidenceGraph k).IsLink e.1 Z.1 Z.1 at he
    rw [splitNodeIncidenceGraph_isLink_iff] at he
    simpa using he
  · intro a b _ _ hab
    exact Subtype.ext hab
  · intro q hq
    let e : h.dualGraph.Edge := ⟨q, Set.mem_univ _⟩
    refine ⟨e, ?_, rfl⟩
    change (C.splitNodeIncidenceGraph k).IsLink q Z.1 Z.1
    rw [splitNodeIncidenceGraph_isLink_iff]
    change q.incidentComponents = {Z.1} at hq
    simpa using hq

/-- API lemma for Definition 6.3.9: the valence of a component is the number
of distinct nodes on it, plus one additional count for every self-node. Thus a node
joining two components contributes one at either endpoint, while a self-node contributes
two to the valence of its component. -/
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_valence_eq_node_ncard_add_selfNode_ncard
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (Z : h.dualGraph.Vertex) :
    h.dualGraph.valence Z =
      (splitNodesOnComponent (k := k) Z.1).ncard +
        (h.nodal.selfNodesOnComponent Z.1).ncard := by
  rw [h.dualGraph.valence_eq, h.dualGraph_incidentEdgesAt_ncard,
    h.dualGraph_loopEdgesAt_ncard]

/-- API lemma for Definition 6.3.9: a dual-graph marking is assigned to a
component exactly when that component contains the corresponding smooth marked point. -/
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_marking_eq_iff_point_mem
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (i : Fin n) (Z : h.dualGraph.Vertex) :
    h.dualGraph.marking i = Z ↔ (p i).point ∈ Z.1.1 := by
  let _ : IsNodalCurveOver k C := h.nodal
  let _ : IsNoetherian C := h.nodal.isNoetherian
  rw [Subtype.ext_iff]
  change C.smoothSectionComponent
      (C ↘ Spec (CommRingCat.of k)) p h.mark_smooth i = Z.1 ↔
    (p i).point ∈ Z.1.1
  constructor
  · intro hi
    exact (eq_smoothPointComponent_iff_mem
      (C ↘ Spec (CommRingCat.of k)) (p i).point (h.mark_smooth i) Z.1).mp hi.symm
  · intro hi
    exact ((eq_smoothPointComponent_iff_mem
      (C ↘ Spec (CommRingCat.of k)) (p i).point (h.mark_smooth i) Z.1).mpr hi).symm

/-- API lemma for Definition 6.3.9: the marking multiplicity at a vertex is
the number of marking indices whose points lie on the corresponding irreducible
component. -/
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_markingMultiplicity_eq_ncard
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (Z : h.dualGraph.Vertex) :
    h.dualGraph.markingMultiplicity Z =
      {i : Fin n | (p i).point ∈ Z.1.1}.ncard := by
  rw [h.dualGraph.markingMultiplicity_eq]
  congr 1
  ext i
  exact h.dualGraph_marking_eq_iff_point_mem i Z

/-- API lemma for Definition 6.3.9: special valence is the number of distinct
nodes on a component, plus the number of its self-nodes, plus the number of marking
indices lying on it. The middle term is the explicit correction that makes a self-node
contribute two flags. -/
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_specialValence_eq_counts
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (Z : h.dualGraph.Vertex) :
    h.dualGraph.specialValence Z =
      ((splitNodesOnComponent (k := k) Z.1).ncard +
        (h.nodal.selfNodesOnComponent Z.1).ncard) +
          {i : Fin n | (p i).point ∈ Z.1.1}.ncard := by
  rw [h.dualGraph.specialValence_eq,
    h.dualGraph_valence_eq_node_ncard_add_selfNode_ncard,
    h.dualGraph_markingMultiplicity_eq_ncard]

/-- Helper lemma for Definition 6.3.9: a marked point of a prestable curve lies on
the component selected by its dual-graph marking. -/
theorem IsPrestableNMarkedCurveOfGenusOver.dualGraph_marking_mem
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) (i : Fin n) :
    (p i).point ∈ (h.dualGraph.marking i).1.1 := by
  let _ : IsNoetherian C := h.nodal.isNoetherian
  unfold IsPrestableNMarkedCurveOfGenusOver.dualGraph
  exact nodalMarkedDualGraph_marking_mem h.nodal h.connected p h.mark_smooth i

end AlgebraicGeometry.Scheme

end DefDualGraph
