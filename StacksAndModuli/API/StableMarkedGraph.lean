module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Stable vertex-weighted marked graphs

This file packages the abstract combinatorial objects used for dual graphs of pointed
prestable curves in §6.3 of *Stacks and Moduli*. A `VertexWeightedMarkedGraph` consists of
a finite connected undirected multigraph, a nonnegative integral weight at each vertex, and
an ordered family of markings. Mathlib's `Graph` retains loops and parallel edges.

The valence counts every incident edge once and every loop once more, hence loops contribute
two. Stability is the vertexwise inequality

`2 * weight - 2 + valence + number of markings > 0`.

The actual construction of a dual graph from a curve is deliberately not included: it needs
normalization, branches at nodes, and geometric genera of irreducible components.

## Main definitions

- `VertexWeightedMarkedGraph`: finite connected vertex-weighted `n`-marked multigraphs.
- `VertexWeightedMarkedGraph.graphGenus`: `|E| + 1 - |V|`.
- `VertexWeightedMarkedGraph.genus`: graph genus plus the sum of the vertex weights.
- `VertexWeightedMarkedGraph.valence`: edge valence, with loops counted twice.
- `VertexWeightedMarkedGraph.logDualizingDegreeAt`: the componentwise numerical degree
  `2w - 2 + s` of the log dualizing sheaf.
- `VertexWeightedMarkedGraph.IsPrestable` and `VertexWeightedMarkedGraph.IsSemistable`:
  the graph-level prestable and semistable conditions.
- `VertexWeightedMarkedGraph.IsStable`: the stability inequality at every vertex.
- `StableMarkedGraph`: the subtype of stable vertex-weighted marked graphs.

## Main results

- `VertexWeightedMarkedGraph.isStableAt_iff`: the numerical vertex trichotomy.
- `VertexWeightedMarkedGraph.isStableAt_iff_vertex_trichotomy`: the form saying that a
  weight-one vertex lies on an edge or carries a marking.
- `VertexWeightedMarkedGraph.isStable_iff_logDualizingDegreeAt_pos`: stability is
  positivity of the log-dualizing degree at every vertex.
- `VertexWeightedMarkedGraph.isSemistable_iff_logDualizingDegreeAt_nonneg`: semistability
  is prestability plus nonnegativity of the log-dualizing degree at every vertex.
- `VertexWeightedMarkedGraph.sum_valence_eq_twice_edgeCount`: the handshaking identity,
  including loops and parallel edges.
- `VertexWeightedMarkedGraph.IsStable.two_mul_genus_add_markings_sub_two_pos`: stability
  implies `2g - 2 + n > 0`.
- `VertexWeightedMarkedGraph.isStable_iff_isPrestable_and_three_le_specialValence_of_weight_zero`:
  after excluding the exceptional unmarked genus-one graph, stability only needs to be
  checked at weight-zero vertices.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

universe u v

/-- A finite connected undirected multigraph with a nonnegative integral weight at each
vertex and an ordered family of `n` markings.

Connectivity is measured on `Graph.toSimpleGraph`: deleting loops and forgetting edge
multiplicity does not change whether a multigraph is connected. The vertex and edge types
may contain elements outside the graph; weights and markings are therefore indexed by the
subtype of actual vertices. -/
structure VertexWeightedMarkedGraph (n : ℕ) (VertexType : Type u) (EdgeType : Type v) where
  /-- The underlying undirected multigraph. Mathlib's `Graph` permits loops and parallel
  edges. -/
  toGraph : Graph VertexType EdgeType
  /-- The set of vertices of the underlying graph is finite. -/
  vertexSet_finite : toGraph.vertexSet.Finite
  /-- The set of edges of the underlying graph is finite. -/
  edgeSet_finite : toGraph.edgeSet.Finite
  /-- The underlying graph is connected and nonempty. -/
  connected : toGraph.toSimpleGraph.Connected
  /-- The nonnegative integral weight of each vertex. -/
  weight : toGraph.vertexSet → ℕ
  /-- The vertex carrying each of the `n` ordered markings. -/
  marking : Fin n → toGraph.vertexSet

namespace VertexWeightedMarkedGraph

variable {n : ℕ} {VertexType : Type u} {EdgeType : Type v}
  (G : VertexWeightedMarkedGraph n VertexType EdgeType)

/-- The type of actual vertices of a vertex-weighted marked graph. -/
abbrev Vertex := G.toGraph.vertexSet

/-- The type of actual edges of a vertex-weighted marked graph. -/
abbrev Edge := G.toGraph.edgeSet

instance : Finite G.Vertex := Set.finite_coe_iff.mpr G.vertexSet_finite

instance : Finite G.Edge := Set.finite_coe_iff.mpr G.edgeSet_finite

instance : Nonempty G.Vertex := G.connected.nonempty

/-- The number of vertices. -/
noncomputable def vertexCount : ℕ :=
  Nat.card G.Vertex

/-- The number of edges, with parallel edges counted separately. -/
noncomputable def edgeCount : ℕ :=
  Nat.card G.Edge

/-- A connected marked graph has at least one vertex. -/
@[simp]
theorem vertexCount_pos : 0 < G.vertexCount :=
  Finite.card_pos

/-- The sum of the weights of all vertices. -/
noncomputable def totalWeight : ℕ :=
  letI := Fintype.ofFinite G.Vertex
  ∑ x, G.weight x

/-- The defining formula for the total vertex weight. -/
theorem totalWeight_eq :
    G.totalWeight = (letI := Fintype.ofFinite G.Vertex; ∑ x, G.weight x) :=
  rfl

/-- The genus, or first Betti number, of the underlying connected graph:
`|E| - |V| + 1`, written with natural subtraction as `|E| + 1 - |V|`. -/
noncomputable def graphGenus : ℕ :=
  G.edgeCount + 1 - G.vertexCount

/-- The defining Euler-characteristic formula for the graph genus. -/
theorem graphGenus_eq : G.graphGenus = G.edgeCount + 1 - G.vertexCount :=
  rfl

/-- Forgetting loops and parallel-edge multiplicities cannot increase the number of edges.

The proof chooses one multiedge above every edge of `toSimpleGraph`; uniqueness of the
unordered endpoint pair makes this choice injective. -/
theorem simpleEdgeCount_le_edgeCount :
    Nat.card G.toGraph.toSimpleGraph.edgeSet ≤ G.edgeCount := by
  classical
  have hexists (s : G.toGraph.toSimpleGraph.edgeSet) :
      ∃ e : G.Edge, ∃ x y : G.Vertex,
        s.1 = s(x, y) ∧ G.toGraph.IsLink e.1 x.1 y.1 := by
    rcases s with ⟨s, hs⟩
    induction s using Sym2.inductionOn
    rw [SimpleGraph.mem_edgeSet] at hs
    obtain ⟨e, he⟩ := hs.2
    exact ⟨⟨e, he.edge_mem⟩, _, _, rfl, he⟩
  let edgeOf (s : G.toGraph.toSimpleGraph.edgeSet) : G.Edge :=
    Classical.choose (hexists s)
  have edgeOf_spec (s : G.toGraph.toSimpleGraph.edgeSet) :
      ∃ x y : G.Vertex,
        s.1 = s(x, y) ∧ G.toGraph.IsLink (edgeOf s).1 x.1 y.1 :=
    Classical.choose_spec (hexists s)
  have hinj : Function.Injective edgeOf := by
    intro s t hst
    obtain ⟨x, y, hs, hxy⟩ := edgeOf_spec s
    obtain ⟨x', y', ht, hx'y'⟩ := edgeOf_spec t
    apply Subtype.ext
    have hx'y'' : G.toGraph.IsLink (edgeOf s).1 x'.1 y'.1 := by
      simpa only [congrArg Subtype.val hst] using hx'y'
    have hedge : s(x, y) = s(x', y') := by
      obtain h | h := hxy.eq_and_eq_or_eq_and_eq hx'y''
      · rw [Subtype.ext h.1, Subtype.ext h.2]
      · rw [Subtype.ext h.1, Subtype.ext h.2, Sym2.eq_swap]
    exact hs.trans (hedge.trans ht.symm)
  unfold edgeCount
  exact Nat.card_le_card_of_injective edgeOf hinj

/-- A connected multigraph has at least one fewer edge than vertices. -/
theorem vertexCount_le_edgeCount_add_one : G.vertexCount ≤ G.edgeCount + 1 := by
  unfold vertexCount
  exact G.connected.card_vert_le_card_edgeSet_add_one.trans
    (Nat.add_le_add_right G.simpleEdgeCount_le_edgeCount 1)

/-- For a connected graph, natural subtraction in the graph-genus definition is exact. -/
theorem graphGenus_add_vertexCount :
    G.graphGenus + G.vertexCount = G.edgeCount + 1 := by
  rw [graphGenus_eq, Nat.sub_add_cancel G.vertexCount_le_edgeCount_add_one]

/-- The genus of a vertex-weighted graph: its graph genus plus the sum of its vertex
weights. -/
noncomputable def genus : ℕ :=
  G.graphGenus + G.totalWeight

/-- The defining formula for the genus of a vertex-weighted graph. -/
theorem genus_eq : G.genus = G.graphGenus + G.totalWeight :=
  rfl

/-- The set of edges incident to a vertex. A loop occurs once in this set. -/
def incidentEdgesAt (x : G.Vertex) : Set G.Edge :=
  {e | ∃ y : G.Vertex, G.toGraph.IsLink e.1 x.1 y.1}

/-- The set of loops based at a vertex. -/
def loopEdgesAt (x : G.Vertex) : Set G.Edge :=
  {e | G.toGraph.IsLink e.1 x.1 x.1}

/-- Membership in the set of edges incident to a vertex. -/
@[simp]
theorem mem_incidentEdgesAt_iff (x : G.Vertex) (e : G.Edge) :
    e ∈ G.incidentEdgesAt x ↔
      ∃ y : G.Vertex, G.toGraph.IsLink e.1 x.1 y.1 :=
  Iff.rfl

/-- Membership in the set of loops based at a vertex. -/
@[simp]
theorem mem_loopEdgesAt_iff (x : G.Vertex) (e : G.Edge) :
    e ∈ G.loopEdgesAt x ↔ G.toGraph.IsLink e.1 x.1 x.1 :=
  Iff.rfl

/-- The set of distinct vertices incident to an edge. A loop contributes one vertex. -/
def incidentVerticesOfEdge (e : G.Edge) : Set G.Vertex :=
  {x | e ∈ G.incidentEdgesAt x}

/-- The set of vertices at which an edge is a loop. It is empty for a nonloop and a
singleton for a loop. -/
def loopVerticesOfEdge (e : G.Edge) : Set G.Vertex :=
  {x | e ∈ G.loopEdgesAt x}

/-- Membership in the set of vertices incident to an edge. -/
@[simp]
theorem mem_incidentVerticesOfEdge_iff (e : G.Edge) (x : G.Vertex) :
    x ∈ G.incidentVerticesOfEdge e ↔ e ∈ G.incidentEdgesAt x :=
  Iff.rfl

/-- Membership in the set of vertices at which an edge is a loop. -/
@[simp]
theorem mem_loopVerticesOfEdge_iff (e : G.Edge) (x : G.Vertex) :
    x ∈ G.loopVerticesOfEdge e ↔ e ∈ G.loopEdgesAt x :=
  Iff.rfl

/-- Every edge has incidence multiplicity two: a nonloop has two distinct incident
vertices, while a loop has one incident vertex and one extra loop contribution. -/
theorem incidenceMultiplicityOfEdge_eq_two (e : G.Edge) :
    (G.incidentVerticesOfEdge e).ncard + (G.loopVerticesOfEdge e).ncard = 2 := by
  obtain ⟨x₀, y₀, hxy₀⟩ := G.toGraph.exists_isLink_of_mem_edgeSet e.2
  let x : G.Vertex := ⟨x₀, hxy₀.left_mem⟩
  let y : G.Vertex := ⟨y₀, hxy₀.right_mem⟩
  have hxy : G.toGraph.IsLink e.1 x.1 y.1 := hxy₀
  have hinc : G.incidentVerticesOfEdge e = {x, y} := by
    ext z
    simp only [mem_incidentVerticesOfEdge_iff, mem_incidentEdgesAt_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, hzw⟩
      obtain hzx | hzy := hzw.left_eq_or_eq hxy
      · exact Or.inl (Subtype.ext hzx)
      · exact Or.inr (Subtype.ext hzy)
    · rintro (rfl | rfl)
      · exact ⟨y, hxy⟩
      · exact ⟨x, hxy.symm⟩
  by_cases hne : x ≠ y
  · have hloop : G.loopVerticesOfEdge e = ∅ := by
      ext z
      change G.toGraph.IsLink e.1 z.1 z.1 ↔ False
      constructor
      · intro hzz
        obtain h | h := hzz.eq_and_eq_or_eq_and_eq hxy
        · exact hne (Subtype.ext (h.1.symm.trans h.2))
        · exact hne (Subtype.ext (h.2.symm.trans h.1))
      · exact False.elim
    rw [hinc, hloop, Set.ncard_pair hne, Set.ncard_empty]
  · have heq : x = y := not_ne_iff.mp hne
    have hxx : G.toGraph.IsLink e.1 x.1 x.1 := by
      simpa only [congrArg Subtype.val heq.symm] using hxy
    have hloop : G.loopVerticesOfEdge e = {x} := by
      ext z
      simp only [mem_loopVerticesOfEdge_iff, mem_loopEdgesAt_iff, Set.mem_singleton_iff]
      constructor
      · intro hzz
        obtain hzx | hzx := hzz.left_eq_or_eq hxy
        · exact Subtype.ext hzx
        · exact (Subtype.ext hzx).trans heq.symm
      · rintro rfl
        exact hxx
    rw [hinc, hloop]
    simp [heq]

/-- Every loop based at a vertex is incident to that vertex. -/
theorem loopEdgesAt_subset_incidentEdgesAt (x : G.Vertex) :
    G.loopEdgesAt x ⊆ G.incidentEdgesAt x := by
  intro e he
  exact ⟨x, he⟩

/-- The valence of a vertex, with loops counted twice.

The first summand counts every incident edge once. The second counts the loops once more;
parallel edges remain distinct elements of `G.Edge`. -/
noncomputable def valence (x : G.Vertex) : ℕ :=
  (G.incidentEdgesAt x).ncard + (G.loopEdgesAt x).ncard

/-- The defining formula for valence, exhibiting the extra contribution from loops. -/
theorem valence_eq (x : G.Vertex) :
    G.valence x = (G.incidentEdgesAt x).ncard + (G.loopEdgesAt x).ncard :=
  rfl

/-- The handshaking identity for a finite multigraph: the sum of the valences is twice the
number of edges. Parallel edges are distinct, and loops contribute twice. -/
theorem sum_valence_eq_twice_edgeCount :
    (letI := Fintype.ofFinite G.Vertex; ∑ x, G.valence x) = 2 * G.edgeCount := by
  classical
  let _ := Fintype.ofFinite G.Vertex
  let _ := Fintype.ofFinite G.Edge
  let incidentSwap : (Σ x, G.incidentEdgesAt x) ≃
      (Σ e, G.incidentVerticesOfEdge e) :=
    { toFun := fun z ↦ ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
      invFun := fun z ↦ ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
      left_inv := by rintro ⟨x, ⟨e, he⟩⟩; rfl
      right_inv := by rintro ⟨e, ⟨x, hx⟩⟩; rfl }
  let loopSwap : (Σ x, G.loopEdgesAt x) ≃ (Σ e, G.loopVerticesOfEdge e) :=
    { toFun := fun z ↦ ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
      invFun := fun z ↦ ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
      left_inv := by rintro ⟨x, ⟨e, he⟩⟩; rfl
      right_inv := by rintro ⟨e, ⟨x, hx⟩⟩; rfl }
  calc
    ∑ x, G.valence x =
        (∑ x, Nat.card (G.incidentEdgesAt x)) + ∑ x, Nat.card (G.loopEdgesAt x) := by
      simp only [valence_eq, Nat.card_coe_set_eq, Finset.sum_add_distrib]
    _ = Nat.card (Σ x, G.incidentEdgesAt x) + Nat.card (Σ x, G.loopEdgesAt x) := by
      rw [Nat.card_sigma, Nat.card_sigma]
    _ = Nat.card (Σ e, G.incidentVerticesOfEdge e) +
        Nat.card (Σ e, G.loopVerticesOfEdge e) := by
      rw [Nat.card_congr incidentSwap, Nat.card_congr loopSwap]
    _ = (∑ e, Nat.card (G.incidentVerticesOfEdge e)) +
        ∑ e, Nat.card (G.loopVerticesOfEdge e) := by
      rw [Nat.card_sigma, Nat.card_sigma]
    _ = ∑ e, ((G.incidentVerticesOfEdge e).ncard +
        (G.loopVerticesOfEdge e).ncard) := by
      simp only [Nat.card_coe_set_eq, Finset.sum_add_distrib]
    _ = ∑ _e : G.Edge, 2 := by
      apply Finset.sum_congr rfl
      intro e _
      exact G.incidenceMultiplicityOfEdge_eq_two e
    _ = 2 * G.edgeCount := by
      simp [edgeCount, Nat.card_eq_fintype_card, Nat.mul_comm]

/-- A vertex has positive valence exactly when it is incident to an edge. -/
theorem valence_pos_iff (x : G.Vertex) :
    0 < G.valence x ↔ (G.incidentEdgesAt x).Nonempty := by
  rw [valence_eq, add_pos_iff]
  constructor
  · rintro (h | h)
    · exact (Set.ncard_pos (s := G.incidentEdgesAt x)).mp h
    · obtain ⟨e, he⟩ := (Set.ncard_pos (s := G.loopEdgesAt x)).mp h
      exact ⟨e, G.loopEdgesAt_subset_incidentEdgesAt x he⟩
  · intro h
    exact Or.inl ((Set.ncard_pos (s := G.incidentEdgesAt x)).mpr h)

/-- The set of markings carried by a vertex. Each marking is a half-edge, so different
indices are counted separately even when they mark the same vertex. -/
def markingsAt (x : G.Vertex) : Set (Fin n) :=
  {i | G.marking i = x}

/-- Membership in the set of markings carried by a vertex. -/
@[simp]
theorem mem_markingsAt_iff (x : G.Vertex) (i : Fin n) :
    i ∈ G.markingsAt x ↔ G.marking i = x :=
  Iff.rfl

/-- The number of markings carried by a vertex. -/
noncomputable def markingMultiplicity (x : G.Vertex) : ℕ :=
  (G.markingsAt x).ncard

/-- The defining formula for the marking multiplicity at a vertex. -/
theorem markingMultiplicity_eq (x : G.Vertex) :
    G.markingMultiplicity x = (G.markingsAt x).ncard :=
  rfl

/-- The sum of the marking multiplicities over all vertices is the number `n` of markings. -/
theorem sum_markingMultiplicity_eq :
    (letI := Fintype.ofFinite G.Vertex; ∑ x, G.markingMultiplicity x) = n := by
  classical
  let _ := Fintype.ofFinite G.Vertex
  let E : (Σ x, G.markingsAt x) ≃ Fin n :=
    { toFun := fun z ↦ z.2.1
      invFun := fun i ↦ ⟨G.marking i, ⟨i, rfl⟩⟩
      left_inv := by
        rintro ⟨x, ⟨i, hi⟩⟩
        subst x
        rfl
      right_inv := fun _ ↦ rfl }
  calc
    ∑ x, G.markingMultiplicity x = ∑ x, Nat.card (G.markingsAt x) := by
      simp only [markingMultiplicity_eq, Nat.card_coe_set_eq]
    _ = Nat.card (Σ x, G.markingsAt x) := Nat.card_sigma.symm
    _ = Nat.card (Fin n) := Nat.card_congr E
    _ = n := Nat.card_fin n

/-- A vertex has positive marking multiplicity exactly when some marking lands on it. -/
theorem markingMultiplicity_pos_iff (x : G.Vertex) :
    0 < G.markingMultiplicity x ↔ ∃ i : Fin n, G.marking i = x := by
  rw [markingMultiplicity_eq, Set.ncard_pos]
  rfl

/-- An unmarked graph has marking multiplicity zero at every vertex. -/
@[simp]
theorem markingMultiplicity_eq_zero (G : VertexWeightedMarkedGraph 0 VertexType EdgeType)
    (x : G.Vertex) : G.markingMultiplicity x = 0 := by
  rw [markingMultiplicity_eq, Set.ncard_eq_zero]
  ext i
  exact Fin.elim0 i

/-- The total number of incident edges and marked half-edges at a vertex. Loops already
contribute twice through `valence`. -/
noncomputable def specialValence (x : G.Vertex) : ℕ :=
  G.valence x + G.markingMultiplicity x

/-- The defining formula for the combined edge-and-marking valence. -/
theorem specialValence_eq (x : G.Vertex) :
    G.specialValence x = G.valence x + G.markingMultiplicity x :=
  rfl

/-- The total special valence is twice the number of edges plus the number of markings. -/
theorem sum_specialValence_eq :
    (letI := Fintype.ofFinite G.Vertex; ∑ x, G.specialValence x) =
      2 * G.edgeCount + n := by
  classical
  let _ := Fintype.ofFinite G.Vertex
  simp_rw [specialValence_eq]
  rw [Finset.sum_add_distrib, G.sum_valence_eq_twice_edgeCount,
    G.sum_markingMultiplicity_eq]

/-- A vertex has positive special valence exactly when it lies on an edge or carries a
marked half-edge. -/
theorem specialValence_pos_iff (x : G.Vertex) :
    0 < G.specialValence x ↔
      (G.incidentEdgesAt x).Nonempty ∨ ∃ i : Fin n, G.marking i = x := by
  rw [specialValence_eq, add_pos_iff, valence_pos_iff, markingMultiplicity_pos_iff]

/-- The numerical degree of the log dualizing sheaf on the component represented by a
vertex: twice its weight minus two, plus the number of incident branches and markings.

This is the dual-graph formula only; it does not construct a dualizing sheaf. -/
noncomputable def logDualizingDegreeAt (x : G.Vertex) : ℤ :=
  2 * (G.weight x : ℤ) - 2 + (G.specialValence x : ℤ)

/-- The defining formula for the componentwise log-dualizing degree. -/
@[simp]
theorem logDualizingDegreeAt_eq (x : G.Vertex) :
    G.logDualizingDegreeAt x =
      2 * (G.weight x : ℤ) - 2 + (G.specialValence x : ℤ) :=
  rfl

/-- The graph-level prestability condition: exclude the unmarked genus-one case.

Finiteness, connectedness, nodality, and the regularity of markings belong to the geometric
curve represented by the graph and are not repeated in this combinatorial predicate. -/
def IsPrestable : Prop :=
  (G.genus, n) ≠ (1, 0)

/-- The graph-level semistability condition: prestability, together with at least two
special half-edges at every weight-zero vertex. -/
def IsSemistable : Prop :=
  G.IsPrestable ∧ ∀ x, G.weight x = 0 → 2 ≤ G.specialValence x

/-- Stability at a vertex: `2w(x) - 2 + val(x) + |m⁻¹(x)| > 0`. -/
def IsStableAt (x : G.Vertex) : Prop :=
  0 < G.logDualizingDegreeAt x

/-- A vertex-weighted marked graph is stable when the stability inequality holds at every
vertex. -/
def IsStable : Prop :=
  ∀ x, G.IsStableAt x

/-- The stability inequality at a vertex is positivity of its log-dualizing degree. -/
@[simp]
theorem isStableAt_iff_logDualizingDegreeAt_pos (x : G.Vertex) :
    G.IsStableAt x ↔ 0 < G.logDualizingDegreeAt x :=
  Iff.rfl

/-- A weighted marked graph is stable exactly when its log-dualizing degree is positive at
every vertex. -/
theorem isStable_iff_logDualizingDegreeAt_pos :
    G.IsStable ↔ ∀ x, 0 < G.logDualizingDegreeAt x :=
  Iff.rfl

/-- Semistability is prestability plus nonnegativity of the componentwise log-dualizing
degree. -/
theorem isSemistable_iff_logDualizingDegreeAt_nonneg :
    G.IsSemistable ↔
      G.IsPrestable ∧ ∀ x, 0 ≤ G.logDualizingDegreeAt x := by
  unfold IsSemistable
  apply and_congr Iff.rfl
  constructor
  · intro h x
    by_cases hx : G.weight x = 0
    · have hs := h x hx
      simp only [logDualizingDegreeAt_eq]
      omega
    · simp only [logDualizingDegreeAt_eq]
      omega
  · intro h x hx
    have hd := h x
    simp only [logDualizingDegreeAt_eq] at hd
    omega

/-- Every semistable weighted marked graph is prestable. -/
theorem IsSemistable.isPrestable (h : G.IsSemistable) : G.IsPrestable :=
  h.1

/-- A stable vertex-weighted `n`-marked graph of genus `g` satisfies
`2g - 2 + n > 0`. This is the combinatorial numerical analogue of the stable-curve
inequality discussed after Definition 6.3.2. -/
theorem IsStable.two_mul_genus_add_markings_sub_two_pos (h : G.IsStable) :
    (0 : ℤ) < 2 * (G.genus : ℤ) + (n : ℤ) - 2 := by
  classical
  let _ := Fintype.ofFinite G.Vertex
  have hsum : (0 : ℤ) < ∑ x : G.Vertex,
      (2 * (G.weight x : ℤ) - 2 + (G.specialValence x : ℤ)) := by
    apply Finset.sum_pos
    · intro x _
      exact h x
    · exact Finset.univ_nonempty
  have hv : Fintype.card G.Vertex = G.vertexCount := by
    rw [vertexCount, Nat.card_eq_fintype_card]
  have hw : (∑ x : G.Vertex, G.weight x) = G.totalWeight :=
    G.totalWeight_eq.symm
  have hs : (∑ x : G.Vertex, G.specialValence x) = 2 * G.edgeCount + n :=
    G.sum_specialValence_eq
  have hwz : (∑ x : G.Vertex, (G.weight x : ℤ)) = (G.totalWeight : ℤ) := by
    exact_mod_cast hw
  have hsz : (∑ x : G.Vertex, (G.specialValence x : ℤ)) =
      (2 * G.edgeCount + n : ℕ) := by
    exact_mod_cast hs
  have hexpr : (∑ x : G.Vertex,
      (2 * (G.weight x : ℤ) - 2 + (G.specialValence x : ℤ))) =
      2 * (G.totalWeight : ℤ) - 2 * (G.vertexCount : ℤ) +
        2 * (G.edgeCount : ℤ) + (n : ℤ) := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.mul_sum, hwz, hsz, Finset.card_univ, hv]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    omega
  rw [hexpr] at hsum
  have hg : (G.graphGenus : ℤ) + (G.vertexCount : ℤ) =
      (G.edgeCount : ℤ) + 1 := by
    exact_mod_cast G.graphGenus_add_vertexCount
  rw [genus_eq]
  simp only [Nat.cast_add]
  omega

/-- Equivalent natural-number form of the numerical stable-graph inequality:
`2 < 2g + n`. -/
theorem IsStable.two_lt_two_mul_genus_add_markings (h : G.IsStable) :
    2 < 2 * G.genus + n := by
  have hz := h.two_mul_genus_add_markings_sub_two_pos
  have hz' : (2 : ℤ) < 2 * (G.genus : ℤ) + (n : ℤ) := by omega
  exact_mod_cast hz'

/-- Every stable weighted marked graph is prestable. -/
theorem IsStable.isPrestable (h : G.IsStable) : G.IsPrestable := by
  intro hpair
  have hg : G.genus = 1 := congrArg Prod.fst hpair
  have hn : n = 0 := congrArg Prod.snd hpair
  have hpositive := h.two_lt_two_mul_genus_add_markings
  omega

/-- Every stable weighted marked graph is semistable. -/
theorem IsStable.isSemistable (h : G.IsStable) : G.IsSemistable := by
  rw [isSemistable_iff_logDualizingDegreeAt_nonneg]
  exact ⟨h.isPrestable, fun x ↦
    le_of_lt ((G.isStableAt_iff_logDualizingDegreeAt_pos x).mp (h x))⟩

/-- If `2g + n ≤ 2`, no weighted marked graph of genus `g` with `n` markings is stable. -/
theorem not_isStable_of_two_mul_genus_add_markings_le_two
    (h : 2 * G.genus + n ≤ 2) : ¬ G.IsStable :=
  fun hs ↦ (not_lt_of_ge h) hs.two_lt_two_mul_genus_add_markings

/-- The inequality `2g + n ≤ 2` singles out exactly the four exceptional pairs
`(g,n) = (0,0), (0,1), (0,2), (1,0)`. -/
theorem two_mul_genus_add_markings_le_two_iff :
    2 * G.genus + n ≤ 2 ↔
      (G.genus = 0 ∧ n = 0) ∨ (G.genus = 0 ∧ n = 1) ∨
        (G.genus = 0 ∧ n = 2) ∨ (G.genus = 1 ∧ n = 0) := by
  omega

/-- The stability inequality at a vertex is equivalent to the three numerical cases from
§6.3: weight at least two; weight one and positive special valence; or weight zero and
special valence at least three. -/
@[simp]
theorem isStableAt_iff (x : G.Vertex) :
    G.IsStableAt x ↔
      2 ≤ G.weight x ∨
        (G.weight x = 1 ∧ 0 < G.specialValence x) ∨
          (G.weight x = 0 ∧ 3 ≤ G.specialValence x) := by
  unfold IsStableAt logDualizingDegreeAt
  omega

/-- A weight-one vertex with zero special valence forces the whole connected graph to be
the exceptional unmarked graph of genus one.

Indeed, connectedness makes the isolated vertex the unique vertex; there are no edges or
markings, and its weight is one. -/
theorem genus_markings_eq_one_zero_of_weight_eq_one_of_specialValence_eq_zero
    (x : G.Vertex) (hw : G.weight x = 1) (hs : G.specialValence x = 0) :
    (G.genus, n) = (1, 0) := by
  have hnoinc : ¬ (G.incidentEdgesAt x).Nonempty := by
    intro h
    have : 0 < G.specialValence x :=
      (G.specialValence_pos_iff x).mpr (Or.inl h)
    omega
  have hnomark : ¬ ∃ i : Fin n, G.marking i = x := by
    intro h
    have : 0 < G.specialValence x :=
      (G.specialValence_pos_iff x).mpr (Or.inr h)
    omega
  have hvertex : ∀ y : G.Vertex, y = x := by
    intro y
    by_contra hyx
    have hreach := G.connected y x
    obtain ⟨z, hz⟩ := hreach.nonempty_neighborSet_right hyx
    have hadj : G.toGraph.Adj x.1 z.1 := hz.2
    obtain ⟨e, he⟩ := hadj
    apply hnoinc
    exact ⟨⟨e, he.edge_mem⟩, ⟨z, he⟩⟩
  let _ : Subsingleton G.Vertex :=
    ⟨fun y z ↦ (hvertex y).trans (hvertex z).symm⟩
  have hn : n = 0 := by
    by_contra hn
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    exact hnomark ⟨⟨0, hnpos⟩, Subsingleton.elim _ _⟩
  have hedge : G.edgeCount = 0 := by
    let _ : IsEmpty G.Edge := ⟨fun e ↦ by
      obtain ⟨y, z, hyz⟩ := G.toGraph.exists_isLink_of_mem_edgeSet e.2
      let Y : G.Vertex := ⟨y, hyz.left_mem⟩
      let Z : G.Vertex := ⟨z, hyz.right_mem⟩
      have hyz' : G.toGraph.IsLink e.1 Y.1 Z.1 := hyz
      rw [Subsingleton.elim Y x, Subsingleton.elim Z x] at hyz'
      exact hnoinc ⟨e, ⟨x, hyz'⟩⟩⟩
    exact Finite.card_eq_zero_iff.mpr inferInstance
  have hweight : G.totalWeight = 1 := by
    rw [G.totalWeight_eq]
    let _ := Fintype.ofFinite G.Vertex
    rw [Finset.sum_eq_single x]
    · exact hw
    · intro y _ hyx
      exact (hyx (Subsingleton.elim y x)).elim
    · simp
  have hvertexCount : G.vertexCount = 1 := by
    exact Nat.card_unique
  have hgenus : G.genus = 1 := by
    rw [G.genus_eq, G.graphGenus_eq, hedge, hvertexCount, hweight]
  exact Prod.ext hgenus hn

/-- For a finite connected weighted marked graph, stability is equivalent to graph
prestability together with the three-special-half-edge bound at every weight-zero
vertex.

The only additional case in the vertex trichotomy is a weight-one vertex. Connectedness
gives it positive special valence unless the entire graph is the exceptional unmarked
genus-one graph, which prestability excludes. -/
theorem isStable_iff_isPrestable_and_three_le_specialValence_of_weight_zero :
    G.IsStable ↔
      G.IsPrestable ∧ ∀ x, G.weight x = 0 → 3 ≤ G.specialValence x := by
  constructor
  · intro h
    refine ⟨h.isPrestable, ?_⟩
    intro x hx
    exact ((G.isStableAt_iff x).mp (h x)).resolve_left
      (not_le_of_gt (by omega : G.weight x < 2)) |>.resolve_left
      (by simp [hx]) |>.2
  · rintro ⟨hpre, hzero⟩ x
    rw [G.isStableAt_iff]
    by_cases htwo : 2 ≤ G.weight x
    · exact Or.inl htwo
    have hweight : G.weight x = 0 ∨ G.weight x = 1 := by omega
    rcases hweight with hx | hx
    · exact Or.inr (Or.inr ⟨hx, hzero x hx⟩)
    · refine Or.inr (Or.inl ⟨hx, ?_⟩)
      by_contra hpos
      have hs : G.specialValence x = 0 := Nat.eq_zero_of_not_pos hpos
      exact hpre
        (G.genus_markings_eq_one_zero_of_weight_eq_one_of_specialValence_eq_zero x hx hs)

/-- The book's vertex trichotomy for stability, with the weight-one case expressed as
"contained in an edge or half-edge". -/
theorem isStableAt_iff_vertex_trichotomy (x : G.Vertex) :
    G.IsStableAt x ↔
      2 ≤ G.weight x ∨
        (G.weight x = 1 ∧
          ((G.incidentEdgesAt x).Nonempty ∨ ∃ i : Fin n, G.marking i = x)) ∨
          (G.weight x = 0 ∧ 3 ≤ G.specialValence x) := by
  rw [isStableAt_iff, specialValence_pos_iff]

/-- A graph is stable exactly when every vertex satisfies the book's three alternatives. -/
theorem isStable_iff_vertex_trichotomy :
    G.IsStable ↔ ∀ x : G.Vertex,
      2 ≤ G.weight x ∨
        (G.weight x = 1 ∧
          ((G.incidentEdgesAt x).Nonempty ∨ ∃ i : Fin n, G.marking i = x)) ∨
          (G.weight x = 0 ∧ 3 ≤ G.specialValence x) := by
  simp only [IsStable, isStableAt_iff_vertex_trichotomy]

end VertexWeightedMarkedGraph

/-- A stable vertex-weighted `n`-marked graph. -/
abbrev StableMarkedGraph (n : ℕ) (VertexType : Type u) (EdgeType : Type v) :=
  {G : VertexWeightedMarkedGraph n VertexType EdgeType // G.IsStable}
