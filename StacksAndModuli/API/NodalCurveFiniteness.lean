module

public import StacksAndModuli.API.FiniteClosedComplement
public import StacksAndModuli.API.ReducedSchemeNormalization
public import StacksAndModuli.API.SplitNodeIncidenceGraph
public import StacksAndModuli.API.SplitNodeNotSmooth
public import StacksAndModuli.API.StalkKrullDimension

/-!
# Finiteness of the singular locus of a nodal curve

This file proves that the nonsmooth locus, and hence the split-node locus, of a nodal
curve over an algebraically closed field is finite. It also exposes the finite vertex and
edge sets of the split-node incidence graph.

## Main results

* `AlgebraicGeometry.Scheme.IsNodalCurveOver.not_formallySmooth_stalkMap_of_isSplitNodeAt`:
  a split node on a nodal curve is not smooth.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.isClosed_of_isSplitNodeAt`: every split node
  is a closed point.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.isSplitNodeAt_iff_not_formallySmooth`:
  the split nodes are exactly the nonsmooth points.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.nonsmoothLocus_finite`: the nonsmooth locus
  is finite.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.splitNodeLocus_finite`: the split-node locus
  is finite.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.finite_splitNodePoints`: the corresponding
  subtype is finite.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.splitNodeIncidenceGraph_vertexSet_finite` and
  `...edgeSet_finite`: finiteness data for the incidence graph.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A split node on a nodal curve is not formally smooth over the ground field. -/
theorem IsNodalCurveOver.not_formallySmooth_stalkMap_of_isSplitNodeAt
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) {x : C}
    (hnode : C.IsSplitNodeAt k x) :
    ¬ ((C ↘ Spec (CommRingCat.of k)).stalkMap x).hom.FormallySmooth := by
  let _ : IsNodalCurveOver k C := h
  let _ : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k))
  apply hnode.not_formallySmooth_stalkMap_of_ringKrullDim_le_one
  exact (C.ringKrullDim_stalk_le_topologicalKrullDim x).trans_eq
    h.isCurve.topologicalKrullDim_eq

/-- Every split node on a nodal curve over an algebraically closed field is a closed
point. -/
theorem IsNodalCurveOver.isClosed_of_isSplitNodeAt
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) {x : C}
    (hnode : C.IsSplitNodeAt k x) : IsClosed ({x} : Set C) := by
  let _ : AlgebraicGeometry.IsNoetherian C := h.isNoetherian
  let _ : AlgebraicGeometry.IsReduced C := h.isReduced
  let f : C ⟶ Spec (CommRingCat.of k) := C ↘ Spec (CommRingCat.of k)
  apply Set.isClosed_singleton_of_mem_of_closed_disjoint_dense_of_dim_le_one
    f.isOpen_smoothLocus.isClosed_compl f.dense_smoothLocus_of_perfectField
    disjoint_compl_left h.isCurve.topologicalKrullDim_eq.le
  change ¬ (f.stalkMap x).hom.FormallySmooth
  exact h.not_formallySmooth_stalkMap_of_isSplitNodeAt hnode

/-- The underlying point of every element of the split-node subtype of a nodal curve is
closed. -/
theorem IsNodalCurveOver.isClosed_splitNodePoint
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    (q : C.SplitNodePoints k) : IsClosed ({q.1} : Set C) :=
  h.isClosed_of_isSplitNodeAt q.2

/-- On a nodal curve over an algebraically closed field, a point is a split node exactly
when the structure morphism is not formally smooth at that point. -/
theorem IsNodalCurveOver.isSplitNodeAt_iff_not_formallySmooth
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) (x : C) :
    C.IsSplitNodeAt k x ↔
      ¬ ((C ↘ Spec (CommRingCat.of k)).stalkMap x).hom.FormallySmooth := by
  constructor
  · exact h.not_formallySmooth_stalkMap_of_isSplitNodeAt
  · intro hx
    let _ : IsNoetherian C := h.isNoetherian
    let _ : IsReduced C := h.isReduced
    let f : C ⟶ Spec (CommRingCat.of k) := C ↘ Spec (CommRingCat.of k)
    have hxclosed : IsClosed ({x} : Set C) := by
      apply Set.isClosed_singleton_of_mem_of_closed_disjoint_dense_of_dim_le_one
        f.isOpen_smoothLocus.isClosed_compl f.dense_smoothLocus_of_perfectField
        disjoint_compl_left h.isCurve.topologicalKrullDim_eq.le
      exact hx
    exact (h.smooth_or_isSplitNode x hxclosed).resolve_left hx

/-- Equivalently, a point of a nodal curve is smooth precisely when it is not a split
node. -/
theorem IsNodalCurveOver.formallySmooth_iff_not_isSplitNodeAt
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) (x : C) :
    ((C ↘ Spec (CommRingCat.of k)).stalkMap x).hom.FormallySmooth ↔
      ¬ C.IsSplitNodeAt k x := by
  rw [h.isSplitNodeAt_iff_not_formallySmooth]
  tauto

/-- The split-node locus of a nodal curve is the complement of its smooth locus. -/
theorem IsNodalCurveOver.splitNodeLocus_eq_compl_smoothLocus
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    {x : C | C.IsSplitNodeAt k x} =
      ((C ↘ Spec (CommRingCat.of k)).smoothLocus : Set C)ᶜ := by
  ext x
  exact h.isSplitNodeAt_iff_not_formallySmooth x

/-- The nonsmooth locus of a nodal curve over an algebraically closed field is finite. -/
theorem IsNodalCurveOver.nonsmoothLocus_finite
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    ((C ↘ Spec (CommRingCat.of k)).smoothLocus : Set C)ᶜ.Finite := by
  let _ : IsNodalCurveOver k C := h
  let _ : AlgebraicGeometry.IsNoetherian C := h.isNoetherian
  let _ : AlgebraicGeometry.IsReduced C := h.isReduced
  let f : C ⟶ Spec (CommRingCat.of k) := C ↘ Spec (CommRingCat.of k)
  apply Set.Finite.of_isClosed_disjoint_dense_of_topologicalKrullDim_le_one
  · exact f.isOpen_smoothLocus.isClosed_compl
  · exact f.dense_smoothLocus_of_perfectField
  · exact disjoint_compl_left
  · exact h.isCurve.topologicalKrullDim_eq.le

/-- The set of split-node points of a nodal curve is finite. -/
theorem IsNodalCurveOver.splitNodeLocus_finite
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    Set.Finite {x : C | C.IsSplitNodeAt k x} := by
  apply h.nonsmoothLocus_finite.subset
  intro x hnode
  change ¬ ((C ↘ Spec (CommRingCat.of k)).stalkMap x).hom.FormallySmooth
  exact h.not_formallySmooth_stalkMap_of_isSplitNodeAt hnode

/-- The coordinate-free subtype of split nodes of a nodal curve is finite. -/
theorem IsNodalCurveOver.finite_splitNodePoints
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    Finite (C.SplitNodePoints k) :=
  Set.finite_coe_iff.mpr h.splitNodeLocus_finite

/-- The vertex set of the split-node incidence graph of a nodal curve is finite. -/
theorem IsNodalCurveOver.splitNodeIncidenceGraph_vertexSet_finite
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian C]
    (h : IsNodalCurveOver k C) :
    (C.splitNodeIncidenceGraph k).vertexSet.Finite := by
  let _ : IsNodalCurveOver k C := h
  let _ : AlgebraicGeometry.IsNoetherian C := h.isNoetherian
  rw [splitNodeIncidenceGraph_vertexSet]
  exact Set.toFinite _

/-- The edge set of the split-node incidence graph of a nodal curve is finite. -/
theorem IsNodalCurveOver.splitNodeIncidenceGraph_edgeSet_finite
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian C]
    (h : IsNodalCurveOver k C) :
    (C.splitNodeIncidenceGraph k).edgeSet.Finite := by
  let _ : IsNodalCurveOver k C := h
  let _ : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (C ↘ Spec (CommRingCat.of k))
  let _ : Finite (C.SplitNodePoints k) := h.finite_splitNodePoints
  rw [splitNodeIncidenceGraph_edgeSet]
  exact Set.toFinite _

end AlgebraicGeometry.Scheme
