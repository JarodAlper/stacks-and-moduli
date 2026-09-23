module

public import StacksAndModuli.API.ComponentNormalizationFromSmoothStalks
public import StacksAndModuli.API.AffineLineCohomology
public import StacksAndModuli.API.ProjectiveLineIrreducibleComponent
public import StacksAndModuli.API.ProjectiveSpaceSmooth
public import StacksAndModuli.API.ReducedClosedImmersionRange
public import StacksAndModuli.API.ReducedComponentCompletionBranch
public import StacksAndModuli.API.SmoothReducedComponentNoSelfNode
public import StacksAndModuli.API.StableMarkedGraphLowValence
public import StacksAndModuli.«Section6.3-Stable».«part6.3.2-dual-graphs»

/-!
# Stable curves: low-valence rational components

This file sharpens the rational-component input in Exercise 6.3.10. A weight-zero
component need not itself be an embedded projective line: its normalization can be
`ℙ¹` while the component has self-nodes. The stability comparison only needs to present
weight-zero vertices whose special valence is less than three. Graph prestability rules
out self-nodes precisely in that low-valence case.

## Supporting reductions toward Exercise 6.3.10

* `IsPrestableNMarkedCurveOfGenusOver.dualGraph_loopEdgesAt_eq_empty_of_weight_zero_lowValence`:
  a low-valence weight-zero component has no loop in a prestable dual graph.
* `IsPrestableNMarkedCurveOfGenusOver.selfNodesOnComponent_eq_empty_of_weight_zero_lowValence`:
  geometrically, that component has no self-node.
* `dualGraph_specialValence_eq_counts_of_weight_zero_lowValence`:
  its special valence has no self-node correction term.
* `RationalSubcurveOver.ofNormalizedComponent`: a projective-line normalization whose
  normalization map is an isomorphism embeds as a rational subcurve.
* `RationalSubcurveOver.specialPoints_encard_eq_component_counts_of_range`:
  a rational subcurve with image one component has the expected node-and-mark count.
* `RationalSubcurveOver.componentNormalizationOverIsoOfRange`: a rational subcurve is
  the normalization of its reduced component, over the ground field.
* `RationalSubcurveOver.selfNodesOnComponent_eq_empty_of_range`: that smooth component
  has no self-node.
* `IsPrestableNMarkedCurveOfGenusOver.rationalSubcurve_dualGraph_data`: its vertex has
  projective-line genus, with self-nodes as the exact special-valence correction.
* `IsPrestableNMarkedCurveOfGenusOver.rationalSubcurve_to_weightZero`: every rational
  subcurve gives a weight-zero vertex with the same special-point count.
* `IsPrestableNMarkedCurveOfGenusOver.DualGraphLowValenceNormalizationData`:
  the precise local component-smoothness and genus-zero classification facts still
  needed to construct low-valence rational components.
* `IsPrestableNMarkedCurveOfGenusOver.DualGraphLowValenceCompletionData`: the sharper
  completed-local formulation using the formal-branch quotient of a node.
* `IsPrestableNMarkedCurveOfGenusOver.dualGraphLowValenceCompletionData_of_projectiveLineIso`:
  the completed-local field follows automatically from the absence of self-nodes.
* `IsPrestableNMarkedCurveOfGenusOver.DualGraphLowValenceComponentData`: the corrected
  rational-component interface needed for the stability comparison.
* `IsPrestableNMarkedCurveOfGenusOver.componentwiseStable_iff_dualGraph_isStable_of_lowValenceData`:
  the unconditional combinatorial deduction from that corrected interface.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

section DefDualGraph

namespace AlgebraicGeometry.Scheme

namespace RationalSubcurveOver

/-- **Exercise 6.3.10** (unlabelled; normalized-component construction): if the
normalization of a reduced irreducible component is isomorphic over `k` to `ℙ¹_k`, and
the normalization map is an isomorphism, then that component is represented by a
rational subcurve of the ambient curve. -/
noncomputable def ofNormalizedComponent
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsNoetherian C]
    (Z : irreducibleComponents C)
    (e : Over.mk (projectiveSpaceOverπ 1 (Spec (CommRingCat.of k))) ≅
      (C.reducedIrreducibleComponentNormalization Z).asOver
        (Spec (CommRingCat.of k)))
    (hnormal : IsIso
      (C.reducedIrreducibleComponent Z).normalizationMap) :
    RationalSubcurveOver k C where
  ι := e.hom ≫ Over.homMk
    (C.reducedIrreducibleComponentNormalizationι Z) rfl
  isClosedImmersion := by
    let hclosed : IsClosedImmersion
        (C.reducedIrreducibleComponentNormalizationι Z) := by
      let _ : IsIso
          (C.reducedIrreducibleComponent Z).normalizationMap := hnormal
      change IsClosedImmersion
        ((C.reducedIrreducibleComponent Z).normalizationMap ≫
          C.reducedIrreducibleComponentι Z)
      exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
        (C.reducedIrreducibleComponent Z).normalizationMap
        (C.reducedIrreducibleComponentι Z)).mpr inferInstance
    let _ : IsIso e.hom := inferInstance
    change IsClosedImmersion
      ((Over.forget (Spec (CommRingCat.of k))).map e.hom ≫
        C.reducedIrreducibleComponentNormalizationι Z)
    exact (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion
      ((Over.forget (Spec (CommRingCat.of k))).map e.hom)
      (C.reducedIrreducibleComponentNormalizationι Z)).mpr hclosed

/-- **Exercise 6.3.10** (unlabelled; normalized-component construction): the rational
subcurve obtained from a projective-line normalization has image exactly the chosen
irreducible component. -/
@[simp]
theorem range_ofNormalizedComponent
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsNoetherian C]
    (Z : irreducibleComponents C)
    (e : Over.mk (projectiveSpaceOverπ 1 (Spec (CommRingCat.of k))) ≅
      (C.reducedIrreducibleComponentNormalization Z).asOver
        (Spec (CommRingCat.of k)))
    (hnormal : IsIso
      (C.reducedIrreducibleComponent Z).normalizationMap) :
    Set.range (ofNormalizedComponent Z e hnormal).ι.left = Z.1 := by
  let _ : Surjective
      (C.reducedIrreducibleComponent Z).normalizationMap := inferInstance
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [← C.range_reducedIrreducibleComponentι Z]
    refine ⟨(C.reducedIrreducibleComponent Z).normalizationMap
      (e.hom.left y), ?_⟩
    rfl
  · intro hx
    rw [← C.range_reducedIrreducibleComponentι Z] at hx
    obtain ⟨y, rfl⟩ := hx
    obtain ⟨z, rfl⟩ :=
      (C.reducedIrreducibleComponent Z).normalizationMap.surjective y
    let _ : IsIso e.hom := inferInstance
    obtain ⟨w, rfl⟩ :=
      ((Over.forget (Spec (CommRingCat.of k))).map e.hom).surjective z
    exact ⟨w, rfl⟩

/-- **Exercise 6.3.10** (unlabelled; rational-subcurve component): the image of a
rational subcurve in a one-dimensional scheme is an irreducible component. -/
theorem range_mem_irreducibleComponents
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (E : RationalSubcurveOver k C) (hC : topologicalKrullDim C ≤ 1) :
    Set.range E.ι.left ∈ irreducibleComponents C := by
  let _ : IsClosedImmersion E.ι.left := E.isClosedImmersion
  exact
    ProjectiveSpace.range_mem_irreducibleComponents_of_projectiveLine_closedEmbedding
      k E.ι.left E.ι.left.isClosedEmbedding hC

/-- **Exercise 6.3.10** (unlabelled; rational-subcurve component): if the image of a
rational subcurve is an irreducible component, the subcurve is canonically isomorphic
to that component with its reduced induced scheme structure. -/
noncomputable def componentIsoOfRange
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (E : RationalSubcurveOver k C) (Z : irreducibleComponents C)
    (hrange : Set.range E.ι.left = Z.1) :
    projectiveSpaceOver 1 (Spec (CommRingCat.of k)) ≅
      C.reducedIrreducibleComponent Z := by
  let i : projectiveSpaceOver 1 (Spec (CommRingCat.of k)) ⟶ C := E.ι.left
  let _ : IsClosedImmersion i := E.isClosedImmersion
  let _ : IsClosedImmersion (C.reducedIrreducibleComponentι Z) :=
    C.reducedIrreducibleComponentι_isClosedImmersion Z
  let _ : IsReduced
      (projectiveSpaceOver 1 (Spec (CommRingCat.of k))) :=
    ProjectiveSpace.projectiveLine_isReduced k
  exact Scheme.isoOfReducedClosedImmersionsRangeEq i
    (C.reducedIrreducibleComponentι Z) (by
      rw [Scheme.range_reducedIrreducibleComponentι]
      exact hrange)

/-- **Exercise 6.3.10** (unlabelled; rational-subcurve component): the component
isomorphism commutes with the two closed immersions into the ambient curve. -/
@[reassoc (attr := simp)]
theorem componentIsoOfRange_hom_comp
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (E : RationalSubcurveOver k C) (Z : irreducibleComponents C)
    (hrange : Set.range E.ι.left = Z.1) :
    (componentIsoOfRange E Z hrange).hom ≫
      C.reducedIrreducibleComponentι Z = E.ι.left := by
  let i : projectiveSpaceOver 1 (Spec (CommRingCat.of k)) ⟶ C := E.ι.left
  let _ : IsClosedImmersion i := E.isClosedImmersion
  let _ : IsClosedImmersion (C.reducedIrreducibleComponentι Z) :=
    C.reducedIrreducibleComponentι_isClosedImmersion Z
  let _ : IsReduced
      (projectiveSpaceOver 1 (Spec (CommRingCat.of k))) :=
    ProjectiveSpace.projectiveLine_isReduced k
  exact Scheme.isoOfReducedClosedImmersionsRangeEq_hom_comp
    i (C.reducedIrreducibleComponentι Z) (by
      rw [Scheme.range_reducedIrreducibleComponentι]
      exact hrange)

/-- **Exercise 6.3.10** (unlabelled; rational-subcurve component): the component
isomorphism is an isomorphism over the ground field. -/
noncomputable def componentOverIsoOfRange
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (E : RationalSubcurveOver k C) (Z : irreducibleComponents C)
    (hrange : Set.range E.ι.left = Z.1) :
    Over.mk (projectiveSpaceOverπ 1 (Spec (CommRingCat.of k))) ≅
      (C.reducedIrreducibleComponent Z).asOver
        (Spec (CommRingCat.of k)) := by
  let _ : IsClosedImmersion E.ι.left := E.isClosedImmersion
  let e := componentIsoOfRange E Z hrange
  refine Over.isoMk e ?_
  change e.hom ≫
      (C.reducedIrreducibleComponentι Z ≫
        (C ↘ Spec (CommRingCat.of k))) =
    projectiveSpaceOverπ 1 (Spec (CommRingCat.of k))
  rw [← Category.assoc, componentIsoOfRange_hom_comp]
  exact E.ι.w

/-- **Exercise 6.3.10** (unlabelled; rational-subcurve component): a reduced
irreducible component represented by a rational subcurve is smooth over the ground
field. -/
theorem component_smooth_of_range
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (E : RationalSubcurveOver k C) (Z : irreducibleComponents C)
    (hrange : Set.range E.ι.left = Z.1) :
    Smooth (C.reducedIrreducibleComponent Z ↘ Spec (CommRingCat.of k)) := by
  let e := componentOverIsoOfRange E Z hrange
  let e' : projectiveSpaceOver 1 (Spec (CommRingCat.of k)) ≅
      C.reducedIrreducibleComponent Z :=
    (Over.forget (Spec (CommRingCat.of k))).mapIso e
  have hcomp : Smooth (e'.hom ≫
      (C.reducedIrreducibleComponent Z ↘ Spec (CommRingCat.of k))) := by
    rw [show e'.hom ≫
        (C.reducedIrreducibleComponent Z ↘ Spec (CommRingCat.of k)) =
      projectiveSpaceOverπ 1 (Spec (CommRingCat.of k)) from e.hom.w]
    infer_instance
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)
    e'.hom (C.reducedIrreducibleComponent Z ↘
      Spec (CommRingCat.of k))).1 hcomp

/-- **Exercise 6.3.10** (unlabelled; rational-subcurve normalization): a reduced
irreducible component represented by a rational subcurve agrees with its normalization.

Indeed, the component is isomorphic over the ground field to the smooth projective line,
so all its stalk maps are formally smooth; the one-dimensional normalization criterion
then applies. -/
theorem componentNormalizationMap_isIso_of_range
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsNoetherian C]
    [LocallyOfFinitePresentation (C ↘ Spec (CommRingCat.of k))]
    (E : RationalSubcurveOver k C) (Z : irreducibleComponents C)
    (hrange : Set.range E.ι.left = Z.1)
    (hC : topologicalKrullDim C ≤ 1) :
    IsIso (C.reducedIrreducibleComponent Z).normalizationMap := by
  let _ : Smooth (C.reducedIrreducibleComponent Z ↘
      Spec (CommRingCat.of k)) := E.component_smooth_of_range Z hrange
  apply C.reducedIrreducibleComponent_normalizationMap_isIso_of_formallySmooth_stalks
    Z (fun x ↦ (C.reducedIrreducibleComponent Z ↘
      Spec (CommRingCat.of k)).smoothLocus_eq_top.ge (Set.mem_univ x)) hC

/-- **Exercise 6.3.10** (unlabelled; rational-subcurve normalization): the projective
line is isomorphic over the ground field to the normalization of the component represented
by a rational subcurve. -/
noncomputable def componentNormalizationOverIsoOfRange
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsNoetherian C]
    [LocallyOfFinitePresentation (C ↘ Spec (CommRingCat.of k))]
    (E : RationalSubcurveOver k C) (Z : irreducibleComponents C)
    (hrange : Set.range E.ι.left = Z.1)
    (hC : topologicalKrullDim C ≤ 1) :
    Over.mk (projectiveSpaceOverπ 1 (Spec (CommRingCat.of k))) ≅
      (C.reducedIrreducibleComponentNormalization Z).asOver
        (Spec (CommRingCat.of k)) := by
  let hnormal := componentNormalizationMap_isIso_of_range E Z hrange hC
  letI : IsIso (C.reducedIrreducibleComponent Z).normalizationMap := hnormal
  let ν :
      (C.reducedIrreducibleComponentNormalization Z).asOver
          (Spec (CommRingCat.of k)) ⟶
        (C.reducedIrreducibleComponent Z).asOver
          (Spec (CommRingCat.of k)) :=
    Over.homMk (C.reducedIrreducibleComponent Z).normalizationMap rfl
  haveI : IsIso ((Over.forget (Spec (CommRingCat.of k))).map ν) := by
    change IsIso (C.reducedIrreducibleComponent Z).normalizationMap
    infer_instance
  letI : IsIso ν := isIso_of_reflects_iso ν
    (Over.forget (Spec (CommRingCat.of k)))
  exact componentOverIsoOfRange E Z hrange ≪≫ (asIso ν).symm

/-- **Exercise 6.3.10** (unlabelled; rational-subcurve weight): the geometric genus
of a component represented by a rational subcurve is the genus of the projective line. -/
theorem irreducibleComponentGeometricGenus_eq_projectiveLine
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsNoetherian C]
    [LocallyOfFinitePresentation (C ↘ Spec (CommRingCat.of k))]
    (E : RationalSubcurveOver k C) (Z : irreducibleComponents C)
    (hrange : Set.range E.ι.left = Z.1)
    (hC : topologicalKrullDim C ≤ 1) :
    C.irreducibleComponentGeometricGenus k Z =
      genusOver k (projectiveSpaceOver 1 (Spec (CommRingCat.of k))) := by
  exact (genusOver_eq_of_isoOver k
    (componentNormalizationOverIsoOfRange E Z hrange hC)).symm

/-- **Exercise 6.3.10** (unlabelled; rational-subcurve self-nodes): a rational
subcurve whose image is an irreducible component cannot have a self-node on that
component. -/
theorem selfNodesOnComponent_eq_empty_of_range
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    (h : IsNodalCurveOver k C) (E : RationalSubcurveOver k C)
    (Z : irreducibleComponents C) (hrange : Set.range E.ι.left = Z.1) :
    h.selfNodesOnComponent Z = ∅ := by
  let _ : IsNoetherian C := h.isNoetherian
  let _ : IsLocallyNoetherian C := inferInstance
  let _ : Smooth (C.reducedIrreducibleComponent Z ↘
      Spec (CommRingCat.of k)) := E.component_smooth_of_range Z hrange
  ext q
  constructor
  · intro hq
    change q.incidentComponents = {Z} at hq
    exact h.incidentComponents_ne_singleton_of_smooth_reducedComponent Z q hq
  · simp

/-- **Exercise 6.3.10** (unlabelled; component special-point count): if a rational
subcurve has image exactly one irreducible component, its special points count the
distinct nodes on that component plus the marking indices lying on it.

The node and marking contributions are disjoint because every marking is smooth, and
the marking contribution counts indices because the marked points are pairwise distinct. -/
theorem specialPoints_encard_eq_component_counts_of_range
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (E : RationalSubcurveOver k C) (Z : irreducibleComponents C)
    (hrange : Set.range E.ι.left = Z.1) :
    (E.specialPoints p).encard =
      (splitNodesOnComponent (k := k) Z).ncard +
        {i : Fin n | (p i).point ∈ Z.1}.ncard := by
  let _ : Finite (C.SplitNodePoints k) := h.nodal.finite_splitNodePoints
  let f : projectiveSpaceOver 1 (Spec (CommRingCat.of k)) → C :=
    fun x ↦ E.ι.left x
  let nodes : Set C :=
    Subtype.val '' splitNodesOnComponent (k := k) Z
  let componentMarks : Set (Fin n) := {i | (p i).point ∈ Z.1}
  let marks : Set C := (fun i ↦ (p i).point) '' componentMarks
  have hι : Function.Injective f := by
    let _ : IsClosedImmersion E.ι.left := E.isClosedImmersion
    exact E.ι.left.isEmbedding.injective
  have hpre : E.specialPoints p = f ⁻¹' (nodes ∪ marks) := by
    ext x
    constructor
    · rintro (hnode | ⟨i, hi⟩)
      · left
        refine ⟨⟨E.ι.left x, hnode⟩, ?_, rfl⟩
        change E.ι.left x ∈ Z.1
        rw [← hrange]
        exact ⟨x, rfl⟩
      · right
        refine ⟨i, ?_, hi⟩
        change (p i).point ∈ Z.1
        rw [hi, ← hrange]
        exact ⟨x, rfl⟩
    · rintro (⟨q, _, hqx⟩ | ⟨i, _, hix⟩)
      · left
        change q.1 = E.ι.left x at hqx
        exact hqx ▸ q.2
      · right
        exact ⟨i, hix⟩
  have hsubset : nodes ∪ marks ⊆ Set.range f := by
    intro x hx
    change x ∈ Set.range E.ι.left
    exact hrange.symm ▸ (by
      rcases hx with ⟨q, hq, rfl⟩ | ⟨i, hi, rfl⟩
      · exact hq
      · exact hi)
  have hdisjoint : Disjoint nodes marks := by
    rw [Set.disjoint_left]
    intro x hxnode hxmark
    rcases hxnode with ⟨q, _, hqx⟩
    rcases hxmark with ⟨i, _, hix⟩
    have hpoint : (p i).point = q.1 := hix.trans hqx.symm
    exact h.nodal.not_formallySmooth_stalkMap_of_isSplitNodeAt q.2
      (hpoint ▸ h.mark_smooth i)
  have hnodes : nodes.encard =
      (splitNodesOnComponent (k := k) Z).ncard := by
    rw [show nodes = Subtype.val '' splitNodesOnComponent (k := k) Z from rfl,
      Subtype.val_injective.encard_image]
    exact (Set.toFinite (splitNodesOnComponent (k := k) Z)).cast_ncard_eq.symm
  have hmarks : marks.encard = componentMarks.ncard := by
    rw [show marks = (fun i ↦ (p i).point) '' componentMarks from rfl,
      h.mark_point_injective.encard_image]
    exact (Set.toFinite componentMarks).cast_ncard_eq.symm
  rw [hpre, Set.encard_preimage_of_injective_subset_range hι hsubset,
    Set.encard_union_eq hdisjoint, hnodes, hmarks]

end RationalSubcurveOver

namespace IsPrestableNMarkedCurveOfGenusOver

/-- **Exercise 6.3.10** (unlabelled; rational-subcurve numerical data): every rational
subcurve determines a dual-graph vertex whose weight is the genus of `ℙ¹`; its special
points account for every flag and marking except the second flag at each self-node.

Consequently, `H¹(ℙ¹, 𝒪) = 0` gives weight zero.  Equality between the subcurve's
special-point count and graph special valence is then reduced exactly to the absence of
self-nodes on its component. -/
theorem rationalSubcurve_dualGraph_data
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (E : RationalSubcurveOver k C) :
    ∃ Z : h.dualGraph.Vertex,
      Set.range E.ι.left = Z.1.1 ∧
        h.dualGraph.weight Z =
          genusOver k (projectiveSpaceOver 1 (Spec (CommRingCat.of k))) ∧
        (E.specialPoints p).encard +
            (h.nodal.selfNodesOnComponent Z.1).ncard =
          h.dualGraph.specialValence Z := by
  let _ : IsNoetherian C := h.nodal.isNoetherian
  let _ : IsCurveOver k C := h.nodal.isCurve
  let Z₀ : irreducibleComponents C :=
    ⟨Set.range E.ι.left,
      E.range_mem_irreducibleComponents
        h.nodal.isCurve.topologicalKrullDim_eq.le⟩
  let Z : h.dualGraph.Vertex := ⟨Z₀, Set.mem_univ Z₀⟩
  refine ⟨Z, rfl, ?_, ?_⟩
  · rw [h.dualGraph_weight]
    exact E.irreducibleComponentGeometricGenus_eq_projectiveLine Z₀ rfl
      h.nodal.isCurve.topologicalKrullDim_eq.le
  · have hcount :=
      E.specialPoints_encard_eq_component_counts_of_range h Z₀ rfl
    have hval₀ : h.dualGraph.specialValence Z =
        ((splitNodesOnComponent (k := k) Z₀).ncard +
          (h.nodal.selfNodesOnComponent Z₀).ncard) +
            {i : Fin n | (p i).point ∈ Z₀.1}.ncard := by
      simpa only [Z] using h.dualGraph_specialValence_eq_counts Z
    have hval' :
        (splitNodesOnComponent (k := k) Z₀).ncard +
              {i : Fin n | (p i).point ∈ Z₀.1}.ncard +
            (h.nodal.selfNodesOnComponent Z₀).ncard =
          h.dualGraph.specialValence Z := by
      omega
    rw [hcount]
    exact_mod_cast hval'

/-- **Exercise 6.3.10** (unlabelled; rational-subcurve criterion): every rational
subcurve gives a weight-zero vertex with the same special-point count. -/
theorem rationalSubcurve_to_weightZero
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (E : RationalSubcurveOver k C) :
    ∃ Z : h.dualGraph.Vertex,
      h.dualGraph.weight Z = 0 ∧
        (E.specialPoints p).encard = h.dualGraph.specialValence Z := by
  obtain ⟨Z, hrange, hweight, hspecial⟩ := h.rationalSubcurve_dualGraph_data E
  refine ⟨Z, hweight.trans ?_, ?_⟩
  · exact ProjectiveSpace.Cohomology.projectiveLine_genusOver_eq_zero
  have hnoSelf := E.selfNodesOnComponent_eq_empty_of_range h.nodal Z.1 hrange
  rw [hnoSelf, Set.ncard_empty] at hspecial
  simpa using hspecial

/-- **Exercise 6.3.10** (unlabelled; low-valence reduction): a weight-zero vertex of
special valence less than three has no loop once the graph genus is identified with the
curve genus.

A loop would use both available incidences. Connectedness would then force the exceptional
one-vertex, one-loop, unmarked graph of genus one, excluded by prestability. -/
theorem dualGraph_loopEdgesAt_eq_empty_of_weight_zero_lowValence
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (hgenus : h.dualGraph.genus = g) (Z : h.dualGraph.Vertex)
    (hw : h.dualGraph.weight Z = 0) (hs : h.dualGraph.specialValence Z < 3) :
    h.dualGraph.loopEdgesAt Z = ∅ := by
  apply h.dualGraph.loopEdgesAt_eq_empty_of_isPrestable_of_weight_zero_lowValence
  · simpa only [VertexWeightedMarkedGraph.IsPrestable, hgenus] using
      h.not_genus_one_unmarked
  · exact hw
  · exact hs

/-- **Exercise 6.3.10** (unlabelled; geometric low-valence reduction): a weight-zero
component of special valence less than three has no self-node once graph and curve genera
agree.

Thus the converse rational-component argument only has to classify a proper smooth
geometrically integral genus-zero component, rather than a possibly self-nodal component. -/
theorem selfNodesOnComponent_eq_empty_of_weight_zero_lowValence
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (hgenus : h.dualGraph.genus = g) (Z : h.dualGraph.Vertex)
    (hw : h.dualGraph.weight Z = 0) (hs : h.dualGraph.specialValence Z < 3) :
    h.nodal.selfNodesOnComponent Z.1 = ∅ := by
  let _ : Finite (C.SplitNodePoints k) := h.nodal.finite_splitNodePoints
  have hloop := h.dualGraph_loopEdgesAt_eq_empty_of_weight_zero_lowValence
    hgenus Z hw hs
  have hncard := h.dualGraph_loopEdgesAt_ncard Z
  rw [hloop, Set.ncard_empty] at hncard
  exact (Set.ncard_eq_zero (by toFinite_tac)).mp hncard.symm

/-- **Exercise 6.3.10** (unlabelled; low-valence special-point count): on a
low-valence weight-zero component, special valence is just the number of distinct ambient
nodes on the component plus its marking multiplicity. There is no second self-node
correction because the preceding theorem rules out self-nodes. -/
theorem dualGraph_specialValence_eq_counts_of_weight_zero_lowValence
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (hgenus : h.dualGraph.genus = g) (Z : h.dualGraph.Vertex)
    (hw : h.dualGraph.weight Z = 0) (hs : h.dualGraph.specialValence Z < 3) :
    h.dualGraph.specialValence Z =
      (splitNodesOnComponent (k := k) Z.1).ncard +
        {i : Fin n | (p i).point ∈ Z.1.1}.ncard := by
  rw [h.dualGraph_specialValence_eq_counts Z,
    h.selfNodesOnComponent_eq_empty_of_weight_zero_lowValence hgenus Z hw hs,
    Set.ncard_empty, add_zero]

/-- **Exercise 6.3.10** (unlabelled; exact normalization input for low-valence
components): the remaining geometry needed to turn a low-valence weight-zero vertex
into an embedded projective line.

The first field is the remaining local branch calculation: at a node of a component
without self-nodes, the reduced component follows one smooth formal axis. Smooth ambient
points are handled automatically by the general component-normalization API, which then
makes the normalization map an isomorphism. The second is precisely the genus-zero
classification of that normalization as `ℙ¹_k`, restricted to the low-valence vertices
where it is needed. -/
structure DualGraphLowValenceNormalizationData
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) : Prop where
  /-- At an ambient node, a component without a self-node has a formally smooth stalk. -/
  reducedComponent_formallySmooth_at_node_of_noSelfNode :
    ∀ Z : h.dualGraph.Vertex, h.nodal.selfNodesOnComponent Z.1 = ∅ →
      ∀ x : C.reducedIrreducibleComponent Z.1,
        C.IsSplitNodeAt k (C.reducedIrreducibleComponentι Z.1 x) →
        ((C.reducedIrreducibleComponent Z.1 ↘
          Spec (CommRingCat.of k)).stalkMap x).hom.FormallySmooth
  /-- A low-valence weight-zero component normalization is a projective line over `k`. -/
  projectiveLineIso_of_weight_zero_lowValence :
    ∀ Z : h.dualGraph.Vertex, h.dualGraph.weight Z = 0 →
      h.dualGraph.specialValence Z < 3 →
        letI : IsNoetherian C := h.nodal.isNoetherian
        Nonempty
          (Over.mk (projectiveSpaceOverπ 1 (Spec (CommRingCat.of k))) ≅
            (C.reducedIrreducibleComponentNormalization Z.1).asOver
              (Spec (CommRingCat.of k)))

/-- **Exercise 6.3.10** (unlabelled; exact completed-local input): the concrete
geometric facts needed for the low-valence component argument.

At a node on a component without self-nodes, the completed local ring of the reduced
component must be a `CompletedLocalBranchTargetOver`: a surjective target of the ambient
completed node ring with minimal-prime kernel.  The formal-branch quotient API then
identifies this target with `k[[t]]`.  The second field is the remaining genus-zero
classification of the component normalization as `ℙ¹_k`. -/
structure DualGraphLowValenceCompletionData
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) : Prop where
  /-- The completed local ring of a component with one branch at a node is the
  corresponding formal-branch quotient of the completed node ring. -/
  reducedComponent_completedLocalBranchTarget :
    ∀ Z : h.dualGraph.Vertex, h.nodal.selfNodesOnComponent Z.1 = ∅ →
      ∀ x : C.reducedIrreducibleComponent Z.1,
        C.IsSplitNodeAt k (C.reducedIrreducibleComponentι Z.1 x) →
          CompletedLocalBranchTargetOver k
            (C.reducedIrreducibleComponentι Z.1 x) x
  /-- A low-valence weight-zero component normalization is a projective line over `k`. -/
  projectiveLineIso_of_weight_zero_lowValence :
    ∀ Z : h.dualGraph.Vertex, h.dualGraph.weight Z = 0 →
      h.dualGraph.specialValence Z < 3 →
        letI : IsNoetherian C := h.nodal.isNoetherian
        Nonempty
          (Over.mk (projectiveSpaceOverπ 1 (Spec (CommRingCat.of k))) ≅
            (C.reducedIrreducibleComponentNormalization Z.1).asOver
              (Spec (CommRingCat.of k)))

/-- **Exercise 6.3.10** (unlabelled; completed-local constructor): the
completed-branch field in `DualGraphLowValenceCompletionData` follows from the
absence of self-nodes.  Thus only the projective-line classification of the
low-valence weight-zero component normalizations remains as input. -/
theorem dualGraphLowValenceCompletionData_of_projectiveLineIso
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (hprojectiveLine :
      ∀ Z : h.dualGraph.Vertex, h.dualGraph.weight Z = 0 →
        h.dualGraph.specialValence Z < 3 →
          letI : IsNoetherian C := h.nodal.isNoetherian
          Nonempty
            (Over.mk (projectiveSpaceOverπ 1 (Spec (CommRingCat.of k))) ≅
              (C.reducedIrreducibleComponentNormalization Z.1).asOver
                (Spec (CommRingCat.of k)))) :
    h.DualGraphLowValenceCompletionData where
  reducedComponent_completedLocalBranchTarget Z hself x hx := by
    let _ : IsNoetherian C := h.nodal.isNoetherian
    apply hx.reducedComponent_completedLocalBranchTarget_of_not_selfNode Z.1 x
    intro hincident
    let q : C.SplitNodePoints k :=
      ⟨C.reducedIrreducibleComponentι Z.1 x, hx⟩
    have hq : q ∈ h.nodal.selfNodesOnComponent Z.1 := hincident
    rw [hself] at hq
    exact hq
  projectiveLineIso_of_weight_zero_lowValence Z hw hs :=
    hprojectiveLine Z hw hs

/-- **Exercise 6.3.10** (unlabelled; completed-local reduction): the exact
component-to-branch completion comparison implies formal smoothness of the component at
each node.  This uses regularity of a Noetherian domain whose completion is `k[[t]]`. -/
theorem DualGraphLowValenceCompletionData.toNormalizationData
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (D : h.DualGraphLowValenceCompletionData) :
    h.DualGraphLowValenceNormalizationData where
  reducedComponent_formallySmooth_at_node_of_noSelfNode Z hself x hx := by
    let _ : IsNoetherian C := h.nodal.isNoetherian
    let _ : IsCurveOver k C := h.nodal.isCurve
    exact hx.reducedComponent_formallySmooth_stalk_of_completedLocalBranchTarget
      Z.1 x (D.reducedComponent_completedLocalBranchTarget Z hself x hx)
  projectiveLineIso_of_weight_zero_lowValence Z hw hs :=
    D.projectiveLineIso_of_weight_zero_lowValence Z hw hs

/-- **Exercise 6.3.10** (unlabelled; low-valence normalized-component construction):
the exact normalization input above constructs the required embedded rational subcurve,
whose image is the chosen irreducible component; its special-point count agrees
automatically with graph special valence. -/
theorem DualGraphLowValenceNormalizationData.exists_rationalSubcurve
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (D : h.DualGraphLowValenceNormalizationData)
    (hgenus : h.dualGraph.genus = g) (Z : h.dualGraph.Vertex)
    (hw : h.dualGraph.weight Z = 0) (hs : h.dualGraph.specialValence Z < 3) :
    ∃ E : RationalSubcurveOver k C,
      Set.range E.ι.left = Z.1.1 ∧
        (E.specialPoints p).encard = h.dualGraph.specialValence Z := by
  let _ : IsNoetherian C := h.nodal.isNoetherian
  let _ : IsCurveOver k C := h.nodal.isCurve
  let _ : IsReduced C := h.nodal.isReduced
  have hself :=
    h.selfNodesOnComponent_eq_empty_of_weight_zero_lowValence hgenus Z hw hs
  have hformal : ∀ x : C.reducedIrreducibleComponent Z.1,
      ((C.reducedIrreducibleComponent Z.1 ↘
        Spec (CommRingCat.of k)).stalkMap x).hom.FormallySmooth := by
    intro x
    by_cases hxnode : C.IsSplitNodeAt k
        (C.reducedIrreducibleComponentι Z.1 x)
    · exact D.reducedComponent_formallySmooth_at_node_of_noSelfNode
        Z hself x hxnode
    · apply C.reducedIrreducibleComponent_formallySmooth_stalk_of_ambient Z.1 x
      exact (h.nodal.formallySmooth_iff_not_isSplitNodeAt _).mpr hxnode
  have hnormal :=
    C.reducedIrreducibleComponent_normalizationMap_isIso_of_formallySmooth_stalks
      Z hformal h.nodal.isCurve.topologicalKrullDim_eq.le
  obtain ⟨e⟩ := D.projectiveLineIso_of_weight_zero_lowValence Z hw hs
  let E : RationalSubcurveOver k C :=
    RationalSubcurveOver.ofNormalizedComponent Z.1 e hnormal
  have hrange : Set.range E.ι.left = Z.1.1 :=
    RationalSubcurveOver.range_ofNormalizedComponent Z.1 e hnormal
  refine ⟨E, hrange, ?_⟩
  have hcount :=
    RationalSubcurveOver.specialPoints_encard_eq_component_counts_of_range h E Z.1
      hrange
  have hspecial :=
    h.dualGraph_specialValence_eq_counts_of_weight_zero_lowValence
      hgenus Z hw hs
  rw [hcount]
  exact_mod_cast hspecial.symm

/-- **Exercise 6.3.10** (unlabelled; completed-local construction): the concrete
component-completion and genus-zero classification inputs construct the low-valence
rational subcurve. -/
theorem DualGraphLowValenceCompletionData.exists_rationalSubcurve
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (D : h.DualGraphLowValenceCompletionData)
    (hgenus : h.dualGraph.genus = g) (Z : h.dualGraph.Vertex)
    (hw : h.dualGraph.weight Z = 0) (hs : h.dualGraph.specialValence Z < 3) :
    ∃ E : RationalSubcurveOver k C,
      Set.range E.ι.left = Z.1.1 ∧
        (E.specialPoints p).encard = h.dualGraph.specialValence Z :=
  D.toNormalizationData h |>.exists_rationalSubcurve h hgenus Z hw hs

/-- **Exercise 6.3.10** (unlabelled; corrected geometric input for the stability
comparison): rational subcurves correspond to weight-zero vertices, while only
low-valence weight-zero vertices must conversely be represented by rational subcurves.

The restriction in the converse is essential. A weight-zero component can have
self-nodes, so its normalization can be `ℙ¹` without admitting a closed immersion
`ℙ¹ → C` onto that singular component. Such a component is already stable as soon as
its special valence is at least three and therefore does not enter the converse argument. -/
structure DualGraphLowValenceComponentData
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p) : Prop where
  /-- Every embedded smooth rational subcurve determines a weight-zero vertex with the
  same special-point count. -/
  rationalSubcurve_to_weightZero :
    ∀ E : RationalSubcurveOver k C, ∃ Z : h.dualGraph.Vertex,
      h.dualGraph.weight Z = 0 ∧
        (E.specialPoints p).encard = h.dualGraph.specialValence Z
  /-- Every low-valence weight-zero vertex is represented by an embedded smooth rational
  subcurve with the same special-point count. -/
  lowValenceWeightZero_to_rationalSubcurve :
    ∀ Z : h.dualGraph.Vertex, h.dualGraph.weight Z = 0 →
      h.dualGraph.specialValence Z < 3 →
        ∃ E : RationalSubcurveOver k C,
          (E.specialPoints p).encard = h.dualGraph.specialValence Z

/-- **Exercise 6.3.10** (unlabelled; normalized-component reduction): the exact local
smoothness and genus-zero classification facts isolated in
`DualGraphLowValenceNormalizationData` imply the corrected low-valence component
interface. -/
theorem dualGraphLowValenceComponentData_of_normalization
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (hgenus : h.dualGraph.genus = g)
    (D : h.DualGraphLowValenceNormalizationData) :
    h.DualGraphLowValenceComponentData where
  rationalSubcurve_to_weightZero := h.rationalSubcurve_to_weightZero
  lowValenceWeightZero_to_rationalSubcurve Z hw hs := by
    obtain ⟨E, _, hE⟩ := D.exists_rationalSubcurve h hgenus Z hw hs
    exact ⟨E, hE⟩

/-- **Exercise 6.3.10** (unlabelled; completed-local reduction): the completed
branch-target and genus-zero classification data imply the corrected low-valence
component interface. -/
theorem dualGraphLowValenceComponentData_of_completion
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (hgenus : h.dualGraph.genus = g)
    (D : h.DualGraphLowValenceCompletionData) :
    h.DualGraphLowValenceComponentData :=
  h.dualGraphLowValenceComponentData_of_normalization hgenus
    (D.toNormalizationData h)

/-- **Exercise 6.3.10** (unlabelled; stability half): componentwise stability of a
prestable marked curve is equivalent to stability of its dual graph once the corrected
low-valence rational-component comparisons and graph-genus equality are supplied. -/
theorem componentwiseStable_iff_dualGraph_isStable_of_lowValenceData
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (hgenus : h.dualGraph.genus = g)
    (D : h.DualGraphLowValenceComponentData) :
    IsComponentwiseStableNMarkedCurveOfGenusOver k g n C p ↔
      h.dualGraph.IsStable := by
  rw [h.dualGraph.isStable_iff_isPrestable_and_three_le_specialValence_of_weight_zero]
  constructor
  · intro hs
    refine ⟨?_, ?_⟩
    · simpa only [VertexWeightedMarkedGraph.IsPrestable, hgenus] using
        h.not_genus_one_unmarked
    · intro Z hZ
      by_contra hthree
      have hlt : h.dualGraph.specialValence Z < 3 := Nat.lt_of_not_ge hthree
      obtain ⟨E, hE⟩ := D.lowValenceWeightZero_to_rationalSubcurve Z hZ hlt
      have hbound := hs.2 E
      rw [hE] at hbound
      exact hthree (by exact_mod_cast hbound)
  · rintro ⟨_, hzero⟩
    refine ⟨h, ?_⟩
    intro E
    obtain ⟨Z, hZ, hspecial⟩ := D.rationalSubcurve_to_weightZero E
    have hthree := hzero Z hZ
    rw [hspecial]
    exact_mod_cast hthree

/-- **Exercise 6.3.10** (unlabelled; combined corrected form): componentwise stability
is equivalent to dual-graph stability once the normalization-cohomology calculations and
the low-valence rational-component comparisons are supplied. -/
theorem componentwiseStable_iff_dualGraph_isStable_of_data_of_lowValenceData
    {k : Type u} [Field k] [IsAlgClosed k] {g n : ℕ} {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    {p : Fin n → C.SectionOver (Spec (CommRingCat.of k))}
    (h : IsPrestableNMarkedCurveOfGenusOver k g n C p)
    (N : h.nodal.NormalizationCohomologyData h.dualGraph)
    (D : h.DualGraphLowValenceComponentData) :
    IsComponentwiseStableNMarkedCurveOfGenusOver k g n C p ↔
      h.dualGraph.IsStable :=
  h.componentwiseStable_iff_dualGraph_isStable_of_lowValenceData
    (h.dualGraph_genus_eq N) D

end IsPrestableNMarkedCurveOfGenusOver

end AlgebraicGeometry.Scheme

end DefDualGraph

end
