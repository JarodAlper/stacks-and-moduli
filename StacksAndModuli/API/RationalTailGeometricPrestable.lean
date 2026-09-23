module

public import StacksAndModuli.API.GeometricNodalSubcurveIntersection
public import StacksAndModuli.API.RationalTailProjectiveLineReduction
public import StacksAndModuli.«Section6.3-Stable».«part6.3.1-definition»

/-!
# Rational tails on geometrically prestable curves

This file connects the arbitrary-field prestable interface from §6.3 with the
geometric-node intersection API.  An attaching point of a rational tail is
unconditionally an ambient node.  The finite-separable constants conclusion then
uses exactly the remaining formal-local descent input from Proposition 6.2.4, and the
projective-line conclusion additionally uses the isolated pointed genus-zero
classification and geometric-integrality inputs.

No theorem here assumes that a geometric split-node chart automatically descends to a
finite separable field extension.

## Main results

* `SmoothGenusZeroSubcurveOver.IsRationalTail.
  exists_attachingNode_of_geometricallyPrestable`: a rational tail attaches at an
  ambient node.
* `SmoothGenusZeroSubcurveOver.IsRationalTail.
  globalSections_finiteSeparable_of_geometricallyPrestable_of_coordinatesDescend`:
  its constants are finite separable, conditional precisely on completed-coordinate
  descent.
* `SmoothGenusZeroSubcurveOver.IsRationalTail.
  projectiveLineIso_over_globalSections_of_geometricallyPrestable`: the corresponding
  projective-line reduction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

namespace SmoothGenusZeroSubcurveOver.IsRationalTail

variable {k : Type u} [Field k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))]

/-- A rational tail on an arbitrary-field geometrically prestable curve attaches at
an ambient node.  This part uses geometric nodality alone and has no coordinate-descent
hypothesis. -/
theorem exists_attachingNode_of_geometricallyPrestable
    {I : Type v} {g : ℕ} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (hpre : IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p)
    (htail : E.IsRationalTail p) :
    ∃ x : E.curve.left,
      E.IsSingleReducedIntersectionAt x ∧
        E.ContainsNoMarkedPoints p ∧ C.IsNodeAt k (E.ι.left x) := by
  obtain ⟨x, hx, -, hmarks⟩ := htail.2
  exact ⟨x, hx, hmarks,
    E.isNodeAt_of_isSingleReducedIntersectionAt hpre.nodal x hx⟩

/-- On a geometrically prestable curve over an arbitrary field, a rational tail has
finite separable global constants once the geometric split-node coordinates above its
attaching point descend to finite separable fields.

The descent premise is exactly the currently isolated `(1) ⇒ (5)` input of
Proposition 6.2.4. -/
theorem globalSections_finiteSeparable_of_geometricallyPrestable_of_coordinatesDescend
    {I : Type v} {g : ℕ} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (hpre : IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p)
    (htail : E.IsRationalTail p)
    (hdesc : ∀ x (hx : E.IsSingleReducedIntersectionAt x),
      SplitNodeCoordinatesDescendToFiniteSeparableAt k C
        (E.singleReducedIntersectionGeometricNode hpre.nodal x hx)) :
    FiniteDimensional k Γ(E.curve.left, ⊤) ∧
      Algebra.IsSeparable k Γ(E.curve.left, ⊤) := by
  let _ : IsGeometricallyNodalCurveOver k C := hpre.nodal
  exact htail.globalSections_finiteSeparable_of_attachingNodeCoordinatesDescend
    E p hpre.nodal hdesc

/-- A rational tail on a geometrically prestable curve is the projective line over
its global constants once completed node coordinates descend, the curve is
geometrically integral over those constants, and the pointed genus-zero classification
is available there.

The ambient properness and the finite-separable constants extension are discharged by
geometric prestability and the coordinate-descent premise. -/
theorem projectiveLineIso_over_globalSections_of_geometricallyPrestable
    {I : Type v} {g : ℕ} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    (hpre : IsGeometricallyPrestableMarkedCurveOfGenusOver k g C p)
    (htail : E.IsRationalTail p)
    (hdesc : ∀ x (hx : E.IsSingleReducedIntersectionAt x),
      SplitNodeCoordinatesDescendToFiniteSeparableAt k C
        (E.singleReducedIntersectionGeometricNode hpre.nodal x hx))
    (hgeom : GeometricallyIntegral E.curve.left.toSpecGlobalSections) :
    letI : IsProper (C ↘ Spec (CommRingCat.of k)) := hpre.proper
    letI : Field Γ(E.curve.left, ⊤) :=
      E.globalSections_isField_of_ambient_isProper.toField
    letI : E.curve.left.Over
        (Spec (CommRingCat.of Γ(E.curve.left, ⊤))) :=
      ⟨E.curve.left.toSpecGlobalSections⟩
    HasPointedSmoothGenusZeroClassification Γ(E.curve.left, ⊤) →
      Nonempty (projectiveLineAsOver Γ(E.curve.left, ⊤) ≅
        E.curve.left.asOver
          (Spec (CommRingCat.of Γ(E.curve.left, ⊤)))) := by
  let _ : IsProper (C ↘ Spec (CommRingCat.of k)) := hpre.proper
  apply projectiveLineIso_over_globalSections_of_attachingNodeLift E p htail
  · intro x hx
    exact E.hasFiniteSeparableSplitNodeLiftAt_of_singleReducedIntersectionCoordinatesDescend
      hpre.nodal x hx (hdesc x hx)
  · exact hgeom

end SmoothGenusZeroSubcurveOver.IsRationalTail

end AlgebraicGeometry.Scheme

end
