module

public import StacksAndModuli.API.NodalCurveFiniteness
public import StacksAndModuli.«Section6.3-Stable».«part6.3.1-definition»

/-!
# Finiteness of special points on a marked nodal curve

This file proves that a nodal curve with a finite marking type has only finitely many
special points. It also restricts this finiteness result to a rational subcurve.

## Main results

* `AlgebraicGeometry.Scheme.IsNodalCurveOver.specialPointLocus_finite`: the set of nodes
  and marked points is finite.
* `AlgebraicGeometry.Scheme.RationalSubcurveOver.specialPoints_finite`: a rational
  subcurve contains only finitely many special points.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

/-- A nodal curve with a finite marking type has only finitely many special points. -/
theorem IsNodalCurveOver.specialPointLocus_finite
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} [Finite I]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsNodalCurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    Set.Finite {x : C | C.IsSpecialPoint k p x} := by
  rw [show {x : C | C.IsSpecialPoint k p x} =
      {x : C | C.IsSplitNodeAt k x} ∪ Set.range (fun i ↦ (p i).point) by
    ext x
    change (C.IsSplitNodeAt k x ∨ ∃ i, (p i).point = x) ↔
      (C.IsSplitNodeAt k x ∨ ∃ i, (p i).point = x)
    rfl]
  exact h.splitNodeLocus_finite.union (Set.finite_range _)

namespace RationalSubcurveOver

/-- A rational subcurve of a nodal curve with finitely many markings contains only
finitely many special points. -/
theorem specialPoints_finite
    {k : Type u} [Field k] [IsAlgClosed k] {I : Type v} [Finite I]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (E : RationalSubcurveOver k C) (h : IsNodalCurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k))) :
    (E.specialPoints p).Finite := by
  change (E.ι.left ⁻¹' {x : C | C.IsSpecialPoint k p x}).Finite
  let _ : IsClosedImmersion E.ι.left := E.isClosedImmersion
  exact (h.specialPointLocus_finite p).preimage E.ι.left.isEmbedding.injective.injOn

end RationalSubcurveOver

end AlgebraicGeometry.Scheme
