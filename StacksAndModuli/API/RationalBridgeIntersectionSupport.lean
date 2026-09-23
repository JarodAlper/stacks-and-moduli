module

public import StacksAndModuli.API.IrreducibleComponentNeighborhood
public import StacksAndModuli.API.NodalCurveFiniteness
public import StacksAndModuli.«Section6.3-Stable».«part6.3.4-rational-tails-and-bridges»

/-!
# Support of a genus-zero subcurve intersection

Let `E` be a smooth genus-zero closed subcurve of a nodal curve over an
algebraically closed field.  The image of `E` is an irreducible component.  Every
point of the scheme-theoretic intersection of `E` with its reduced complementary
subcurve lies both on this component and in the closure of its complement.  Such a
point cannot be smooth on the ambient curve and is therefore a split node.

It follows that the intersection has a finite discrete underlying topological space
and is affine.  These conclusions concern its support; they deliberately do not
assert that the scheme-theoretic intersection is reduced.

## Main results

* `SmoothGenusZeroSubcurveOver.range_mem_irreducibleComponents`: the image of the
  subcurve is an irreducible component.
* `SmoothGenusZeroSubcurveOver.intersection_point_isSplitNode`: every supported
  intersection point is an ambient split node.
* `SmoothGenusZeroSubcurveOver.intersection_finite`: the intersection has finitely
  many underlying points.
* `SmoothGenusZeroSubcurveOver.intersection_discreteTopology`: its topology is
  discrete.
* `SmoothGenusZeroSubcurveOver.intersection_isAffine`: the intersection is affine.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

universe u

namespace AlgebraicGeometry.Scheme

namespace SmoothGenusZeroSubcurveOver

variable {k : Type u} [Field k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))]

/-- The image of a smooth genus-zero closed subcurve of a one-dimensional scheme is
an irreducible component.

The genus calculation is not needed here.  Irreducibility and the fact that a curve
has a nontrivial chain of irreducible closed subsets rule out a zero-dimensional
image. -/
theorem range_mem_irreducibleComponents
    (E : SmoothGenusZeroSubcurveOver k C)
    (hC : topologicalKrullDim C ≤ 1) :
    Set.range E.ι.left ∈ irreducibleComponents C := by
  let _ : IrreducibleSpace E.curve.left := E.irreducible
  apply
    TopologicalSpace.range_mem_irreducibleComponents_of_closedEmbedding_of_krullDim_le_one
      E.ι.left E.isClosedImmersion.isClosedEmbedding
  · have hpos : 0 < topologicalKrullDim E.curve.left := by
      rw [E.isCurveOver.topologicalKrullDim_eq]
      norm_num
    obtain ⟨Z, W, hZW⟩ := Order.krullDim_pos_iff.mp hpos
    exact ⟨Z, hZW.trans_le (fun _ _ ↦ Set.mem_univ _)⟩
  · exact hC

/-- Every point of the intersection maps into the image of the selected subcurve. -/
theorem intersectionι_mem_range
    (E : SmoothGenusZeroSubcurveOver k C) (y : E.intersection) :
    E.intersectionι y ∈ Set.range E.ι.left :=
  ⟨E.intersectionToSubcurve y, rfl⟩

/-- Every point of the intersection maps into the closure of the set-theoretic
complement of the selected subcurve. -/
theorem intersectionι_mem_complementClosed
    (E : SmoothGenusZeroSubcurveOver k C) (y : E.intersection) :
    E.intersectionι y ∈ closure ((Set.range E.ι.left)ᶜ) := by
  rw [← E.range_complementι]
  refine ⟨E.intersectionToComplement y, ?_⟩
  exact congrArg (fun f : E.intersection ⟶ C ↦ f y)
    E.intersectionToComplement_comp_complementι

/-- Every point in the scheme-theoretic intersection of a smooth genus-zero
subcurve with its reduced complement is a split node of the ambient nodal curve.

Indeed, a smooth point of a curve lies on a unique irreducible component and has an
open neighbourhood contained in that component.  This contradicts membership in
the closure of the component's complement. -/
theorem intersection_point_isSplitNode [IsAlgClosed k]
    (E : SmoothGenusZeroSubcurveOver k C) (h : IsNodalCurveOver k C)
    (y : E.intersection) : C.IsSplitNodeAt k (E.intersectionι y) := by
  apply (h.isSplitNodeAt_iff_not_formallySmooth _).mpr
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

/-- The scheme-theoretic intersection has finitely many underlying points. -/
theorem intersection_finite [IsAlgClosed k]
    (E : SmoothGenusZeroSubcurveOver k C) (h : IsNodalCurveOver k C) :
    Finite E.intersection := by
  let _ : Finite (C.SplitNodePoints k) := h.finite_splitNodePoints
  apply Finite.of_injective
    (fun y : E.intersection ↦
      (⟨E.intersectionι y, E.intersection_point_isSplitNode h y⟩ :
        C.SplitNodePoints k))
  intro y z hyz
  apply E.intersectionι.isClosedEmbedding.injective
  exact congrArg Subtype.val hyz

/-- The underlying topology of the scheme-theoretic intersection is discrete. -/
theorem intersection_discreteTopology [IsAlgClosed k]
    (E : SmoothGenusZeroSubcurveOver k C) (h : IsNodalCurveOver k C) :
    DiscreteTopology E.intersection := by
  let _ : Finite E.intersection := E.intersection_finite h
  let _ : T1Space E.intersection := ⟨fun y ↦ by
    have hclosed : IsClosed ({E.intersectionι y} : Set C) :=
      h.isClosed_of_isSplitNodeAt (E.intersection_point_isSplitNode h y)
    have hpreimage := hclosed.preimage E.intersectionι.continuous
    convert hpreimage using 1
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact E.intersectionι.isClosedEmbedding.injective.eq_iff.symm⟩
  infer_instance

/-- A scheme with the finite discrete topology underlying this intersection is
affine. -/
theorem intersection_isAffine [IsAlgClosed k]
    (E : SmoothGenusZeroSubcurveOver k C) (h : IsNodalCurveOver k C) :
    IsAffine E.intersection := by
  let _ : Finite E.intersection := E.intersection_finite h
  let _ : DiscreteTopology E.intersection := E.intersection_discreteTopology h
  infer_instance

end SmoothGenusZeroSubcurveOver

end AlgebraicGeometry.Scheme

end
