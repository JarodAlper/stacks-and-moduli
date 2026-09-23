module

public import StacksAndModuli.API.FormalBranchComponents
public import Mathlib.Combinatorics.Graph.Basic

/-!
# The incidence graph of split nodes and irreducible components

This file constructs the canonical undirected multigraph recording how the formal branches
at split nodes meet the irreducible components of a locally Noetherian scheme. Its vertices
are all irreducible components, its edges are all split-node points, and an edge joins the
components assigned by `SplitNodeBranches.toComponent` to its two formal branches. If both
branches lie on the same component, the corresponding edge is a loop.

The graph's incidence relation is defined without choosing coordinates or an ordering of
the two branches: the unordered endpoints are characterized by the range of the canonical
branch-to-component map. A noncanonical equivalence with `Fin 2` is used only to prove that
every split node has an endpoint pair.

No finiteness or connectedness assertion is made. In particular, this is an incidence-graph
precursor rather than a `VertexWeightedMarkedGraph` or the full dual graph of a curve.

## Main definitions

* `AlgebraicGeometry.Scheme.SplitNodePoints.componentOfBranch`: the component assigned to a
  formal branch at a fixed split node.
* `AlgebraicGeometry.Scheme.SplitNodePoints.incidentComponents`: the choice-free set of
  components incident to a split node.
* `AlgebraicGeometry.Scheme.splitNodeIncidenceGraph`: the resulting undirected multigraph.

## Main results

* `AlgebraicGeometry.Scheme.SplitNodePoints.incidentComponents_eq_pair_of_equivFinTwo`:
  every ordering of the two formal branches gives the same unordered endpoint set.
* `AlgebraicGeometry.Scheme.splitNodeIncidenceGraph_isLink_iff`: binary incidence is
  equality with the canonical incident-component set.
* `AlgebraicGeometry.Scheme.splitNodeIncidenceGraph_inc_iff_exists_formalBranch`: unary
  incidence means that some formal branch is assigned to the given component.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme

/-- The irreducible component assigned to a formal branch at a fixed split node. -/
noncomputable def SplitNodePoints.componentOfBranch
    {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) (b : X.FormalBranchesAt q.1) :
    irreducibleComponents X :=
  SplitNodeBranches.toComponent X (⟨q, b⟩ : X.SplitNodeBranches k)

/-- The defining equation for the component assigned to a branch at a split node. -/
@[simp]
theorem SplitNodePoints.componentOfBranch_eq
    {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) (b : X.FormalBranchesAt q.1) :
    q.componentOfBranch b =
      SplitNodeBranches.toComponent X (⟨q, b⟩ : X.SplitNodeBranches k) :=
  rfl

/-- The choice-free set of irreducible components incident to a split node: the range of
the canonical map from its formal branches to irreducible components. It has one element
at a self-node and otherwise has two. -/
noncomputable def SplitNodePoints.incidentComponents
    {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) : Set (irreducibleComponents X) :=
  Set.range q.componentOfBranch

/-- A component is incident to a split node exactly when it is assigned to one of the
node's formal branches. -/
@[simp]
theorem SplitNodePoints.mem_incidentComponents_iff
    {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) (V : irreducibleComponents X) :
    V ∈ q.incidentComponents ↔
      ∃ b : X.FormalBranchesAt q.1, q.componentOfBranch b = V :=
  Iff.rfl

/-- Any ordering of the two formal branches of a split node presents its canonical set of
incident components as the corresponding unordered pair. Thus the pair is independent of
the chosen equivalence with `Fin 2`. -/
theorem SplitNodePoints.incidentComponents_eq_pair_of_equivFinTwo
    {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) (e : X.FormalBranchesAt q.1 ≃ Fin 2) :
    q.incidentComponents =
      {q.componentOfBranch (e.symm 0), q.componentOfBranch (e.symm 1)} := by
  ext V
  rw [q.mem_incidentComponents_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨b, rfl⟩
    have hb : e b = 0 ∨ e b = 1 := by omega
    rcases hb with hb | hb
    · left
      exact congrArg q.componentOfBranch (e.injective (by simpa using hb))
    · right
      exact congrArg q.componentOfBranch (e.injective (by simpa using hb))
  · rintro (rfl | rfl)
    · exact ⟨e.symm 0, rfl⟩
    · exact ⟨e.symm 1, rfl⟩

/-- The incident-component set of every split node is an unordered pair. The two members
may coincide, precisely allowing a loop in the incidence graph. -/
theorem SplitNodePoints.exists_incidentComponents_eq_pair
    {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) :
    ∃ V W : irreducibleComponents X, q.incidentComponents = {V, W} := by
  obtain ⟨e⟩ := q.2.nonempty_formalBranchesEquivFinTwo
  exact ⟨q.componentOfBranch (e.symm 0), q.componentOfBranch (e.symm 1),
    q.incidentComponents_eq_pair_of_equivFinTwo e⟩

/-- The canonical undirected multigraph whose vertices are the irreducible components of
`X` and whose edges are its split nodes over `k`.

Every component and every split node belongs to the corresponding vertex or edge set.
The endpoints of a node are defined without ordering its branches: they are the range of
the canonical branch-to-component map. Distinct nodes remain distinct edges, and a node
whose two branches lie on one component becomes a loop. -/
noncomputable def splitNodeIncidenceGraph
    (X : Scheme.{u}) (k : Type u) [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X] :
    Graph (irreducibleComponents X) (X.SplitNodePoints k) where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink q V W := q.incidentComponents = {V, W}
  isLink_symm := by
    intro q _
    exact ⟨fun V W h ↦ h.trans (Set.pair_comm V W)⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro q V W V' W' h h'
    have hV : V ∈ q.incidentComponents := by
      rw [h]
      simp
    rw [h'] at hV
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hV
  edge_mem_iff_exists_isLink := by
    intro q
    constructor
    · intro _
      exact q.exists_incidentComponents_eq_pair
    · intro _
      exact Set.mem_univ q
  left_mem_of_isLink := by
    intro q V W _
    exact Set.mem_univ V

/-- Every irreducible component is a vertex of the split-node incidence graph. -/
@[simp]
theorem splitNodeIncidenceGraph_vertexSet
    (X : Scheme.{u}) (k : Type u) [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X] :
    (X.splitNodeIncidenceGraph k).vertexSet = Set.univ :=
  rfl

/-- Every split node is an edge of the split-node incidence graph. -/
@[simp]
theorem splitNodeIncidenceGraph_edgeSet
    (X : Scheme.{u}) (k : Type u) [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X] :
    (X.splitNodeIncidenceGraph k).edgeSet = Set.univ :=
  rfl

/-- Choice-independent characterization of the endpoints of a split-node edge: the
canonical incident-component set is their unordered pair. -/
@[simp]
theorem splitNodeIncidenceGraph_isLink_iff
    {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) (V W : irreducibleComponents X) :
    (X.splitNodeIncidenceGraph k).IsLink q V W ↔
      q.incidentComponents = {V, W} :=
  Iff.rfl

/-- Every equivalence ordering the two formal branches produces a valid ordering of the
endpoints of the split-node edge. -/
theorem splitNodeIncidenceGraph_isLink_of_equivFinTwo
    {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) (e : X.FormalBranchesAt q.1 ≃ Fin 2) :
    (X.splitNodeIncidenceGraph k).IsLink q
      (q.componentOfBranch (e.symm 0)) (q.componentOfBranch (e.symm 1)) :=
  q.incidentComponents_eq_pair_of_equivFinTwo e

/-- Choice-independent unary incidence: an edge is incident to a component exactly when
that component belongs to the node's canonical incident-component set. -/
theorem splitNodeIncidenceGraph_inc_iff_mem_incidentComponents
    {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) (V : irreducibleComponents X) :
    (X.splitNodeIncidenceGraph k).Inc q V ↔ V ∈ q.incidentComponents := by
  constructor
  · rintro ⟨W, hVW⟩
    have h := (splitNodeIncidenceGraph_isLink_iff q V W).mp hVW
    rw [h]
    simp
  · intro hV
    obtain ⟨A, B, hAB⟩ := q.exists_incidentComponents_eq_pair
    rw [hAB] at hV
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hV
    rcases hV with hVA | hVB
    · refine ⟨B, (splitNodeIncidenceGraph_isLink_iff q V B).mpr ?_⟩
      simpa only [hVA] using hAB
    · refine ⟨A, (splitNodeIncidenceGraph_isLink_iff q V A).mpr ?_⟩
      simpa only [hVB] using hAB.trans (Set.pair_comm A B)

/-- A split-node edge is incident to a component exactly when one of its formal branches
is assigned to that component. This characterization contains no choice of coordinates or
ordering of branches. -/
theorem splitNodeIncidenceGraph_inc_iff_exists_formalBranch
    {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) (V : irreducibleComponents X) :
    (X.splitNodeIncidenceGraph k).Inc q V ↔
      ∃ b : X.FormalBranchesAt q.1, q.componentOfBranch b = V := by
  rw [splitNodeIncidenceGraph_inc_iff_mem_incidentComponents,
    q.mem_incidentComponents_iff]

/-- The split node underlying an incident edge lies on the incident irreducible
component. -/
theorem SplitNodePoints.mem_component_of_inc
    {X : Scheme.{u}} {k : Type u} [Field k]
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X]
    (q : X.SplitNodePoints k) (V : irreducibleComponents X)
    (h : (X.splitNodeIncidenceGraph k).Inc q V) : q.1 ∈ V.1 := by
  obtain ⟨b, rfl⟩ :=
    (splitNodeIncidenceGraph_inc_iff_exists_formalBranch q V).mp h
  exact SplitNodeBranches.node_mem_toComponent X
    (⟨q, b⟩ : X.SplitNodeBranches k)

end AlgebraicGeometry.Scheme
