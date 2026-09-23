module

public import StacksAndModuli.API.RationalBridgeIntersectionSupport
public import StacksAndModuli.API.RationalTailBridgeFieldReduction
public import StacksAndModuli.API.ReducedClosedImmersionRange
public import StacksAndModuli.API.ReducedComponentCompletionBranch
public import StacksAndModuli.API.ReducedComponentCompletionBranchMap
public import StacksAndModuli.API.SmoothReducedComponentNoSelfNode

/-!
# The ambient component represented by a smooth genus-zero subcurve

A smooth irreducible genus-zero closed subcurve in a one-dimensional scheme has
irreducible-component image.  Since the subcurve is reduced, its closed immersion
identifies it canonically with the reduced induced structure on that component.  This
identification respects the maps to the ground field and therefore transfers
smoothness to the reduced component.

For a nodal ambient curve over an algebraically closed field, the selected component
cannot contain both formal branches at an intersection point.  The completed local
ring of the reduced component is consequently one of the two formal-axis quotients of
the ambient completed node ring.  More precisely, the actual completed-local map
induced by the component inclusion has minimal-prime kernel.

Proving that the pullback with the reduced complement is itself reduced still requires
showing that the complement inclusion selects the other branch and computing the
pullback stalk as the quotient by the sum of the two inclusion-map kernels.  The global
ideal-sheaf identity is available as `Scheme.Hom.ker_pullback_fst_comp_eq_sup`; the
remaining API gap is the comparison between the stalk of `Scheme.Hom.ker` and the
ring-homomorphism kernel of `Scheme.Hom.stalkMap`.

## Main definitions and results

* `SmoothGenusZeroSubcurveOver.ambientComponent`: the represented irreducible
  component.
* `SmoothGenusZeroSubcurveOver.componentIso`: the canonical isomorphism with its
  reduced induced structure.
* `SmoothGenusZeroSubcurveOver.componentOverIso`: the isomorphism over the ground
  field.
* `SmoothGenusZeroSubcurveOver.ambientComponent_smooth`: smoothness of the reduced
  component.
* `SmoothGenusZeroSubcurveOver.
  intersection_component_completedLocalRingMap_ker_mem_minimalPrimes`: the actual
  inclusion-induced completed-local map cuts out a formal branch.
* `SmoothGenusZeroSubcurveOver.intersection_component_completedLocalBranchTarget`:
  the completed component stalk at an intersection point is one formal branch of
  the ambient node.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

namespace SmoothGenusZeroSubcurveOver

variable {k : Type u} [Field k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))]

/-- The irreducible component represented by a smooth genus-zero subcurve in a
one-dimensional ambient scheme. -/
noncomputable def ambientComponent
    (E : SmoothGenusZeroSubcurveOver k C)
    (hC : topologicalKrullDim C ≤ 1) : irreducibleComponents C :=
  ⟨Set.range E.ι.left, E.range_mem_irreducibleComponents hC⟩

/-- A smooth genus-zero subcurve is canonically isomorphic to the reduced induced
structure on its represented ambient component. -/
noncomputable def componentIso
    (E : SmoothGenusZeroSubcurveOver k C)
    (hC : topologicalKrullDim C ≤ 1) :
    E.curve.left ≅ C.reducedIrreducibleComponent (E.ambientComponent hC) := by
  let i : E.curve.left ⟶ C := E.ι.left
  let Z := E.ambientComponent hC
  let _ : IsClosedImmersion i := E.isClosedImmersion
  let _ : IsClosedImmersion (C.reducedIrreducibleComponentι Z) :=
    C.reducedIrreducibleComponentι_isClosedImmersion Z
  let _ : IsReduced E.curve.left := E.curve_isReduced
  change E.curve.left ≅ C.reducedIrreducibleComponent Z
  exact Scheme.isoOfReducedClosedImmersionsRangeEq i
    (C.reducedIrreducibleComponentι Z) (by
      rw [C.range_reducedIrreducibleComponentι]
      rfl)

/-- The component isomorphism commutes with the two closed immersions into the
ambient scheme. -/
@[reassoc (attr := simp)]
theorem componentIso_hom_comp
    (E : SmoothGenusZeroSubcurveOver k C)
    (hC : topologicalKrullDim C ≤ 1) :
    (E.componentIso hC).hom ≫
      C.reducedIrreducibleComponentι (E.ambientComponent hC) = E.ι.left := by
  let i : E.curve.left ⟶ C := E.ι.left
  let Z := E.ambientComponent hC
  let _ : IsClosedImmersion i := E.isClosedImmersion
  let _ : IsClosedImmersion (C.reducedIrreducibleComponentι Z) :=
    C.reducedIrreducibleComponentι_isClosedImmersion Z
  let _ : IsReduced E.curve.left := E.curve_isReduced
  change (E.componentIso hC).hom ≫ C.reducedIrreducibleComponentι Z = i
  exact Scheme.isoOfReducedClosedImmersionsRangeEq_hom_comp i
    (C.reducedIrreducibleComponentι Z) (by
      rw [C.range_reducedIrreducibleComponentι]
      rfl)

/-- The canonical component isomorphism is an isomorphism over the ground field. -/
noncomputable def componentOverIso
    (E : SmoothGenusZeroSubcurveOver k C)
    (hC : topologicalKrullDim C ≤ 1) :
    E.curve ≅ (C.reducedIrreducibleComponent
      (E.ambientComponent hC)).asOver (Spec (CommRingCat.of k)) := by
  let e := E.componentIso hC
  refine Over.isoMk e ?_
  change e.hom ≫
      (C.reducedIrreducibleComponentι (E.ambientComponent hC) ≫
        (C ↘ Spec (CommRingCat.of k))) = E.curve.hom
  rw [← Category.assoc, E.componentIso_hom_comp]
  exact E.ι.w

/-- The reduced induced structure on the represented ambient component is smooth
over the ground field. -/
theorem ambientComponent_smooth
    (E : SmoothGenusZeroSubcurveOver k C)
    (hC : topologicalKrullDim C ≤ 1) :
    Smooth (C.reducedIrreducibleComponent (E.ambientComponent hC) ↘
      Spec (CommRingCat.of k)) := by
  let e := E.componentOverIso hC
  let e' : E.curve.left ≅ C.reducedIrreducibleComponent (E.ambientComponent hC) :=
    (Over.forget (Spec (CommRingCat.of k))).mapIso e
  have hcomp : Smooth (e'.hom ≫
      (C.reducedIrreducibleComponent (E.ambientComponent hC) ↘
        Spec (CommRingCat.of k))) := by
    rw [show e'.hom ≫
        (C.reducedIrreducibleComponent (E.ambientComponent hC) ↘
          Spec (CommRingCat.of k)) = E.curve.hom from e.hom.w]
    exact E.smooth
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)
    e'.hom (C.reducedIrreducibleComponent (E.ambientComponent hC) ↘
      Spec (CommRingCat.of k))).1 hcomp

/-- At an intersection point with the reduced complement, the kernel of the actual
completed-local map induced by the represented component inclusion is a minimal
prime of the ambient completed node ring.

This retains the geometric map needed for a later pullback computation; a mere
equivalence between the target completion and `k[[t]]` would not suffice.  The
complement's actual map must still be proved to select the distinct minimal prime. -/
theorem intersection_component_completedLocalRingMap_ker_mem_minimalPrimes
    [IsAlgClosed k] (E : SmoothGenusZeroSubcurveOver k C)
    (h : IsNodalCurveOver k C) (y : E.intersection) :
    let hdim := h.isCurve.topologicalKrullDim_eq.le
    let Z := E.ambientComponent hdim
    let z := (E.componentIso hdim).hom (E.intersectionToSubcurve y)
    RingHom.ker
        ((C.reducedIrreducibleComponentι Z).completedLocalRingMap z
          ((C.reducedIrreducibleComponentι Z).stalkMap_surjective z)) ∈
      minimalPrimes
        (C.completedLocalRing (C.reducedIrreducibleComponentι Z z)) := by
  let _ : IsNoetherian C := h.isNoetherian
  let _ : IsLocallyNoetherian C := inferInstance
  dsimp only
  let hdim := h.isCurve.topologicalKrullDim_eq.le
  let Z := E.ambientComponent hdim
  let e := E.componentIso hdim
  let z := e.hom (E.intersectionToSubcurve y)
  have hx : C.reducedIrreducibleComponentι Z z = E.intersectionι y := by
    change C.reducedIrreducibleComponentι Z
      ((E.componentIso hdim).hom (E.intersectionToSubcurve y)) =
        E.intersectionι y
    rw [← Scheme.Hom.comp_apply, E.componentIso_hom_comp]
    rfl
  have hnode : C.IsSplitNodeAt k
      (C.reducedIrreducibleComponentι Z z) := by
    rw [hx]
    exact E.intersection_point_isSplitNode h y
  let _ : Smooth (C.reducedIrreducibleComponent Z ↘
      Spec (CommRingCat.of k)) := E.ambientComponent_smooth hdim
  let q : C.SplitNodePoints k :=
    ⟨C.reducedIrreducibleComponentι Z z, hnode⟩
  have hne : q.incidentComponents ≠ {Z} :=
    h.incidentComponents_ne_singleton_of_smooth_reducedComponent Z q
  apply
    IsSplitNodeAt.reducedComponent_completedLocalRingMap_ker_mem_minimalPrimes_of_not_selfNode
      Z z hnode
  exact hne

/-- At an intersection point with its reduced complement, the completed local ring
of the represented reduced component is one formal branch of the ambient node.

The supported point is a split node.  Smoothness of the reduced component excludes
a self-node there, and the completed-component branch theorem then identifies its
completed stalk with one of the two minimal-prime quotients of the node ring. -/
theorem intersection_component_completedLocalBranchTarget [IsAlgClosed k]
    (E : SmoothGenusZeroSubcurveOver k C) (h : IsNodalCurveOver k C)
    (y : E.intersection) :
    CompletedLocalBranchTargetOver k (E.intersectionι y)
      ((E.componentIso h.isCurve.topologicalKrullDim_eq.le).hom
        (E.intersectionToSubcurve y)) := by
  let _ : IsNoetherian C := h.isNoetherian
  let _ : IsLocallyNoetherian C := inferInstance
  let hdim := h.isCurve.topologicalKrullDim_eq.le
  let Z := E.ambientComponent hdim
  let e := E.componentIso hdim
  let z := e.hom (E.intersectionToSubcurve y)
  have hx : C.reducedIrreducibleComponentι Z z = E.intersectionι y := by
    change C.reducedIrreducibleComponentι Z
      ((E.componentIso hdim).hom (E.intersectionToSubcurve y)) =
        E.intersectionι y
    rw [← Scheme.Hom.comp_apply, E.componentIso_hom_comp]
    rfl
  have hnode : C.IsSplitNodeAt k
      (C.reducedIrreducibleComponentι Z z) := by
    rw [hx]
    exact E.intersection_point_isSplitNode h y
  let _ : Smooth (C.reducedIrreducibleComponent Z ↘
      Spec (CommRingCat.of k)) := E.ambientComponent_smooth hdim
  let q : C.SplitNodePoints k :=
    ⟨C.reducedIrreducibleComponentι Z z, hnode⟩
  have hne : q.incidentComponents ≠ {Z} :=
    h.incidentComponents_ne_singleton_of_smooth_reducedComponent Z q
  have htarget :=
    hnode.reducedComponent_completedLocalBranchTarget_of_not_selfNode Z z hne
  rw [hx] at htarget
  exact htarget

end SmoothGenusZeroSubcurveOver

end AlgebraicGeometry.Scheme

end
