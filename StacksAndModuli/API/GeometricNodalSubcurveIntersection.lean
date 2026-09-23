module

public import StacksAndModuli.API.RationalBridgeIntersectionSupport
public import StacksAndModuli.API.RationalTailBridgeFieldReduction

/-!
# Intersections with a geometrically nodal curve over an arbitrary field

The image of a smooth genus-zero closed subcurve is closed.  A point where that image
meets the closure of its complement lies on the boundary of a closed subset of the
ambient curve.  In a Noetherian one-dimensional space such a boundary point is closed.
For a geometrically nodal curve, the point is then a node: formal smoothness would give
an open neighbourhood contained in the selected component, contradicting the boundary
condition.

The final result combines this node witness with an explicitly supplied descent of its
geometric split-node coordinates.  This is only the formal-local descent reduction
needed for Proposition 6.2.4; no unconditional form of that proposition is asserted.

## Main results

* `Set.isClosed_singleton_of_mem_closed_of_mem_closure_compl_of_dim_le_one`:
  boundary points of closed subsets of Noetherian one-dimensional spaces are closed.
* `Set.finite_inter_closure_compl_of_isClosed_of_dim_le_one`: the boundary of a
  closed subset in such a space is finite.
* `SmoothGenusZeroSubcurveOver.intersection_point_isClosed`: every supported
  intersection point maps to a closed ambient point.
* `SmoothGenusZeroSubcurveOver.intersection_point_isNode`: every such point is an
  ambient node over an arbitrary field.
* `SmoothGenusZeroSubcurveOver.intersection_finite_of_geometricallyNodal`: the
  subcurve intersection has finite support over an arbitrary field.
* `SmoothGenusZeroSubcurveOver.singleReducedIntersectionGeometricNode`: a chosen
  geometric split-node witness above a single reduced intersection point.
* `SmoothGenusZeroSubcurveOver.IsRationalTail.
  globalSections_finiteSeparable_of_attachingNodeCoordinatesDescend`: the rational-tail
  finite-separability conclusion, conditional on descent of the chosen geometric node
  coordinates.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Topology

universe u v

/-- A point belonging both to a closed subset and to the closure of its complement is
closed in a Noetherian `T₀` space of topological Krull dimension at most one. -/
theorem Set.isClosed_singleton_of_mem_closed_of_mem_closure_compl_of_dim_le_one
    {X : Type*} [TopologicalSpace X] [T0Space X] [NoetherianSpace X]
    {Z : Set X} (hZ : IsClosed Z) (hdim : topologicalKrullDim X ≤ 1)
    {x : X} (hxZ : x ∈ Z) (hxclosure : x ∈ closure Zᶜ) :
    IsClosed ({x} : Set X) := by
  let B : Set X := Z ∩ closure Zᶜ
  have hBclosed : IsClosed B := hZ.inter isClosed_closure
  have hinterior : interior B = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    have hzB : z ∈ B := interior_subset hz
    obtain ⟨w, hwB, hwcompl⟩ :=
      mem_closure_iff.mp hzB.2 (interior B) isOpen_interior hz
    exact hwcompl (interior_subset hwB).1
  apply Set.isClosed_singleton_of_mem_of_closed_disjoint_dense_of_dim_le_one
    hBclosed (interior_eq_empty_iff_dense_compl.mp hinterior)
    disjoint_compl_right hdim
  exact ⟨hxZ, hxclosure⟩

namespace AlgebraicGeometry.Scheme

namespace SmoothGenusZeroSubcurveOver

variable {k : Type u} [Field k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))]

/-- Every point of the scheme-theoretic intersection of a smooth genus-zero subcurve
with its reduced complement maps to a closed point of a geometrically nodal ambient
curve. -/
theorem intersection_point_isClosed
    (E : SmoothGenusZeroSubcurveOver k C)
    (h : IsGeometricallyNodalCurveOver k C) (y : E.intersection) :
    IsClosed ({E.intersectionι y} : Set C) := by
  let _ : IsNoetherian C := h.isNoetherian
  let _ : IsClosedImmersion E.ι.left := E.isClosedImmersion
  apply Set.isClosed_singleton_of_mem_closed_of_mem_closure_compl_of_dim_le_one
    (X := C) (Z := Set.range E.ι.left)
    E.ι.left.isClosedEmbedding.isClosed_range
    h.isCurve.topologicalKrullDim_eq.le
    (E.intersectionι_mem_range y) (E.intersectionι_mem_complementClosed y)

/-- The scheme-theoretic intersection has finitely many underlying points over an
arbitrary field.  This is a statement about support and does not assert reducedness. -/
theorem intersection_finite_of_geometricallyNodal
    (E : SmoothGenusZeroSubcurveOver k C)
    (h : IsGeometricallyNodalCurveOver k C) :
    Finite E.intersection := by
  let _ : IsNoetherian C := h.isNoetherian
  let _ : IsClosedImmersion E.ι.left := E.isClosedImmersion
  let B : Set C := Set.range E.ι.left ∩ closure ((Set.range E.ι.left)ᶜ)
  have hBfinite : B.Finite :=
    Set.finite_inter_closure_compl_of_isClosed_of_dim_le_one
      E.ι.left.isClosedEmbedding.isClosed_range
      h.isCurve.topologicalKrullDim_eq.le
  let _ : Finite B := Set.finite_coe_iff.mpr hBfinite
  apply Finite.of_injective
    (fun y : E.intersection ↦
      (⟨E.intersectionι y,
        E.intersectionι_mem_range y, E.intersectionι_mem_complementClosed y⟩ : B))
  intro y z hyz
  apply E.intersectionι.isClosedEmbedding.injective
  exact congrArg Subtype.val hyz

/-- The underlying topology of the scheme-theoretic intersection is discrete over an
arbitrary field. -/
theorem intersection_discreteTopology_of_geometricallyNodal
    (E : SmoothGenusZeroSubcurveOver k C)
    (h : IsGeometricallyNodalCurveOver k C) :
    DiscreteTopology E.intersection := by
  let _ : Finite E.intersection :=
    E.intersection_finite_of_geometricallyNodal h
  let _ : T1Space E.intersection := ⟨fun y ↦ by
    have hpreimage := (E.intersection_point_isClosed h y).preimage
      E.intersectionι.continuous
    convert hpreimage using 1
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact E.intersectionι.isClosedEmbedding.injective.eq_iff.symm⟩
  infer_instance

/-- The scheme-theoretic intersection is affine over an arbitrary field. -/
theorem intersection_isAffine_of_geometricallyNodal
    (E : SmoothGenusZeroSubcurveOver k C)
    (h : IsGeometricallyNodalCurveOver k C) :
    IsAffine E.intersection := by
  let _ : Finite E.intersection :=
    E.intersection_finite_of_geometricallyNodal h
  let _ : DiscreteTopology E.intersection :=
    E.intersection_discreteTopology_of_geometricallyNodal h
  infer_instance

/-- An intersection point cannot be formally smooth on the ambient curve: a smooth
point has an open neighbourhood contained in its unique irreducible component, whereas
an intersection point belongs to the closure of the component's complement. -/
theorem intersection_point_not_formallySmooth
    (E : SmoothGenusZeroSubcurveOver k C)
    (h : IsGeometricallyNodalCurveOver k C) (y : E.intersection) :
    ¬ ((C ↘ Spec (CommRingCat.of k)).stalkMap
      (E.intersectionι y)).hom.FormallySmooth := by
  intro hsmooth
  let _ : IsNoetherian C := h.isNoetherian
  let _ : IsCurveOver k C := h.isCurve
  let f : C ⟶ Spec (CommRingCat.of k) := C ↘ Spec (CommRingCat.of k)
  let Z : irreducibleComponents C :=
    ⟨Set.range E.ι.left,
      E.range_mem_irreducibleComponents h.isCurve.topologicalKrullDim_eq.le⟩
  have hxZ : E.intersectionι y ∈ Z.1 := E.intersectionι_mem_range y
  have hZeq : Z = C.smoothPointComponent f (E.intersectionι y) hsmooth :=
    (C.eq_smoothPointComponent_iff_mem f (E.intersectionι y) hsmooth Z).mpr hxZ
  obtain ⟨U, -, hxU, hU⟩ :=
    C.exists_affineOpen_mem_le_smoothPointComponent f (E.intersectionι y) hsmooth
  have hUrange : (U : Set C) ⊆ Set.range E.ι.left := by
    intro z hz
    have hz' := hU hz
    rw [← hZeq] at hz'
    exact hz'
  obtain ⟨z, hzU, hzcompl⟩ := mem_closure_iff.mp
    (E.intersectionι_mem_complementClosed y) U U.2 hxU
  exact hzcompl (hUrange hzU)

/-- Every point in the scheme-theoretic intersection of a smooth genus-zero subcurve
with its reduced complement is a node of a geometrically nodal ambient curve over an
arbitrary field. -/
theorem intersection_point_isNode
    (E : SmoothGenusZeroSubcurveOver k C)
    (h : IsGeometricallyNodalCurveOver k C) (y : E.intersection) :
    C.IsNodeAt k (E.intersectionι y) := by
  exact (h.smooth_or_isNode (E.intersectionι y)
    (E.intersection_point_isClosed h y)).resolve_left
      (E.intersection_point_not_formallySmooth h y)

/-- If a single reduced intersection is supported at `x`, then its ambient image is a
node of a geometrically nodal curve. -/
theorem isNodeAt_of_isSingleReducedIntersectionAt
    (E : SmoothGenusZeroSubcurveOver k C)
    (h : IsGeometricallyNodalCurveOver k C) (x : E.curve.left)
    (hx : E.IsSingleReducedIntersectionAt x) :
    C.IsNodeAt k (E.ι.left x) := by
  have hxrange : x ∈ Set.range E.intersectionToSubcurve := by
    rw [E.intersectionToSubcurve.range_eq_singleton_of_isSingleReducedPointAt hx]
    exact Set.mem_singleton x
  obtain ⟨y, hy⟩ := hxrange
  have hnode := E.intersection_point_isNode h y
  have himage : E.intersectionι y = E.ι.left x := by
    change E.ι.left (E.intersectionToSubcurve y) = E.ι.left x
    rw [hy]
  rwa [himage] at hnode

/-- The chosen geometric split-node witness above a point supporting a single reduced
intersection. -/
noncomputable def singleReducedIntersectionGeometricNode
    (E : SmoothGenusZeroSubcurveOver k C)
    (h : IsGeometricallyNodalCurveOver k C) (x : E.curve.left)
    (hx : E.IsSingleReducedIntersectionAt x) : geometricBaseChange k C :=
  (E.isNodeAt_of_isSingleReducedIntersectionAt h x hx).choose

/-- The chosen geometric node above a single reduced intersection projects to its
ambient image. -/
@[simp]
theorem singleReducedIntersectionGeometricNode_projection
    (E : SmoothGenusZeroSubcurveOver k C)
    (h : IsGeometricallyNodalCurveOver k C) (x : E.curve.left)
    (hx : E.IsSingleReducedIntersectionAt x) :
    geometricBaseChangeProjection k C
      (E.singleReducedIntersectionGeometricNode h x hx) = E.ι.left x :=
  (E.isNodeAt_of_isSingleReducedIntersectionAt h x hx).choose_spec.1

/-- The chosen geometric point above a single reduced intersection is a split node. -/
theorem singleReducedIntersectionGeometricNode_isSplitNode
    (E : SmoothGenusZeroSubcurveOver k C)
    (h : IsGeometricallyNodalCurveOver k C) (x : E.curve.left)
    (hx : E.IsSingleReducedIntersectionAt x) :
    (geometricBaseChange k C).IsSplitNodeAt (AlgebraicClosure k)
      (E.singleReducedIntersectionGeometricNode h x hx) :=
  (E.isNodeAt_of_isSingleReducedIntersectionAt h x hx).choose_spec.2

/-- A single reduced intersection admits a finite-separable split-node lift whenever
the split-node coordinates of its chosen geometric witness descend. -/
theorem hasFiniteSeparableSplitNodeLiftAt_of_singleReducedIntersectionCoordinatesDescend
    (E : SmoothGenusZeroSubcurveOver k C)
    (h : IsGeometricallyNodalCurveOver k C) (x : E.curve.left)
    (hx : E.IsSingleReducedIntersectionAt x)
    (hdesc : SplitNodeCoordinatesDescendToFiniteSeparableAt k C
      (E.singleReducedIntersectionGeometricNode h x hx)) :
    C.HasFiniteSeparableSplitNodeLiftAt k (E.ι.left x) := by
  exact hdesc.hasFiniteSeparableSplitNodeLiftAt
    (E.singleReducedIntersectionGeometricNode_projection h x hx)
    (E.singleReducedIntersectionGeometricNode_isSplitNode h x hx)

/-- A node supported by a single reduced intersection admits a finite-separable split
node lift whenever split-node coordinates descend for each geometric witness above its
ambient image. -/
theorem hasFiniteSeparableSplitNodeLiftAt_of_isSingleReducedIntersectionAt
    (E : SmoothGenusZeroSubcurveOver k C)
    (h : IsGeometricallyNodalCurveOver k C) (x : E.curve.left)
    (hx : E.IsSingleReducedIntersectionAt x)
    (hdesc : ∀ y : geometricBaseChange k C,
      geometricBaseChangeProjection k C y = E.ι.left x →
        SplitNodeCoordinatesDescendToFiniteSeparableAt k C y) :
    C.HasFiniteSeparableSplitNodeLiftAt k (E.ι.left x) := by
  exact IsNodeAt.hasFiniteSeparableSplitNodeLiftAt_of_coordinates_descend
    (E.isNodeAt_of_isSingleReducedIntersectionAt h x hx) hdesc

/-- A rational tail in a geometrically nodal curve has finite separable global
constants once split-node coordinates descend for the chosen geometric witness above
its attaching point.

This is a conditional reduction through `HasFiniteSeparableSplitNodeLiftAt`; it does not
assert the missing completed-local descent statement from Proposition 6.2.4. -/
theorem IsRationalTail.globalSections_finiteSeparable_of_attachingNodeCoordinatesDescend
    {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (hC : IsGeometricallyNodalCurveOver k C)
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k))]
    (h : E.IsRationalTail p)
    (hdesc : ∀ x (hx : E.IsSingleReducedIntersectionAt x),
      SplitNodeCoordinatesDescendToFiniteSeparableAt k C
        (E.singleReducedIntersectionGeometricNode hC x hx)) :
    FiniteDimensional k Γ(E.curve.left, ⊤) ∧
      Algebra.IsSeparable k Γ(E.curve.left, ⊤) := by
  apply h.globalSections_finiteSeparable_of_attachingNodeLift E p
  intro x hx
  exact
    E.hasFiniteSeparableSplitNodeLiftAt_of_singleReducedIntersectionCoordinatesDescend
      hC x hx (hdesc x hx)

/-- Compatibility form of the rational-tail finite-separability reduction which accepts
coordinate descent for every geometric point above the attaching point. -/
theorem IsRationalTail.globalSections_finiteSeparable_of_allAttachingNodeCoordinatesDescend
    {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (hC : IsGeometricallyNodalCurveOver k C)
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k))]
    (h : E.IsRationalTail p)
    (hdesc : ∀ x, E.IsSingleReducedIntersectionAt x →
      ∀ y : geometricBaseChange k C,
        geometricBaseChangeProjection k C y = E.ι.left x →
          SplitNodeCoordinatesDescendToFiniteSeparableAt k C y) :
    FiniteDimensional k Γ(E.curve.left, ⊤) ∧
      Algebra.IsSeparable k Γ(E.curve.left, ⊤) := by
  apply h.globalSections_finiteSeparable_of_attachingNodeCoordinatesDescend E p hC
  intro x hx
  exact hdesc x hx (E.singleReducedIntersectionGeometricNode hC x hx)
    (E.singleReducedIntersectionGeometricNode_projection hC x hx)

end SmoothGenusZeroSubcurveOver

end AlgebraicGeometry.Scheme
