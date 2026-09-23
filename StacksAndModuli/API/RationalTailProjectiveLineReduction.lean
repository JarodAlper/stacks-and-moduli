module

public import StacksAndModuli.API.GenusZeroCurveGlobalConstantsReduction
public import StacksAndModuli.API.GlobalConstantsSmooth
public import StacksAndModuli.API.RationalTailBridgeFieldReduction

/-!
# Projective-line reduction for rational tails

This file specializes the global-constants genus-zero reduction to a rational tail.
The tail definition already supplies a point where
`Γ(E, 𝒪_E) ⟶ κ(x)` is bijective.  Properness over the field of global constants,
the curve dimension, intrinsic genus zero, and the resulting rational section are
therefore all automatic.

The remaining hypotheses are displayed explicitly: separability of the finite
field of constants, geometric integrality for the canonical map to
`Spec Γ(E, 𝒪_E)`, and the pointed projective-line classification from
Exercise 6.1.13. Smoothness over the field of constants follows by cancellation
across its finite etale extension of the original field.

## Main result

* `AlgebraicGeometry.Scheme.SmoothGenusZeroSubcurveOver.IsRationalTail.
    projectiveLineIso_over_globalSections_of_pointedClassification`;
* `AlgebraicGeometry.Scheme.SmoothGenusZeroSubcurveOver.IsRationalTail.
    projectiveLineIso_over_globalSections_of_attachingNodeLift`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme

namespace SmoothGenusZeroSubcurveOver.IsRationalTail

variable {k : Type u} [Field k] {C : Scheme.{u}}
  [C.Over (Spec (CommRingCat.of k))]

/-- A rational tail is the projective line over its field of global constants once
that finite field extension is separable, the canonical structure map is
geometrically integral, and the pointed genus-zero classification is available over
that field.

Everything else in the book's argument is discharged here: the constants form a
finite field extension, properness descends to the canonical structure map, genus
zero descends through the finite field tower, and the tail point gives a section. -/
theorem projectiveLineIso_over_globalSections_of_pointedClassification
    {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    [IsProper (C ↘ Spec (CommRingCat.of k))]
    (htail : E.IsRationalTail p)
    (hsep :
      letI : Field Γ(E.curve.left, ⊤) :=
        E.globalSections_isField_of_ambient_isProper.toField
      Algebra.IsSeparable k Γ(E.curve.left, ⊤))
    (hgeom : GeometricallyIntegral E.curve.left.toSpecGlobalSections) :
    letI : Field Γ(E.curve.left, ⊤) :=
      E.globalSections_isField_of_ambient_isProper.toField
    letI : E.curve.left.Over
        (Spec (CommRingCat.of Γ(E.curve.left, ⊤))) :=
      ⟨E.curve.left.toSpecGlobalSections⟩
    HasPointedSmoothGenusZeroClassification Γ(E.curve.left, ⊤) →
      Nonempty (projectiveLineAsOver Γ(E.curve.left, ⊤) ≅
        E.curve.left.asOver
          (Spec (CommRingCat.of Γ(E.curve.left, ⊤)))) := by
  let hfield := E.globalSections_isField_of_ambient_isProper
  let _ : Field Γ(E.curve.left, ⊤) := hfield.toField
  let _ : E.curve.left.Over
      (Spec (CommRingCat.of Γ(E.curve.left, ⊤))) :=
    ⟨E.curve.left.toSpecGlobalSections⟩
  intro H
  obtain ⟨x, _, heval, _⟩ := htail.2
  let _ : IsProper (E.curve.left ↘ Spec (CommRingCat.of k)) :=
    E.curve_isProper
  have hsmooth : Smooth E.curve.left.toSpecGlobalSections :=
    smooth_toSpecGlobalSections_of_finiteSeparable E.curve.left hfield
      E.globalSections_finiteDimensional_of_ambient_isProper hsep E.smooth
  apply AlgebraicGeometry.Scheme.projectiveLineIso_over_globalSections_of_pointedClassification
    E.curve.left hfield
    (isProper_toSpecGlobalSections (k := k) E.curve.left)
    hsmooth hgeom E.isCurveOver.topologicalKrullDim_eq
    (genus_eq_zero_of_genusOver_eq_zero_of_finite_globalSections
      E.curve.left hfield
      E.globalSections_finiteDimensional_of_ambient_isProper
      E.genus_eq_zero)
    x heval H

/-- A rational tail whose attaching point admits a finite-separable split-node
lift is the projective line over its field of global constants, conditional only
on geometric integrality over that field and the pointed genus-zero
classification. -/
theorem projectiveLineIso_over_globalSections_of_attachingNodeLift
    {I : Type v} (E : SmoothGenusZeroSubcurveOver k C)
    (p : I → C.SectionOver (Spec (CommRingCat.of k)))
    [IsProper (C ↘ Spec (CommRingCat.of k))]
    (htail : E.IsRationalTail p)
    (hnode : ∀ x, E.IsSingleReducedIntersectionAt x →
      C.HasFiniteSeparableSplitNodeLiftAt k (E.ι.left x))
    (hgeom : GeometricallyIntegral E.curve.left.toSpecGlobalSections) :
    letI : Field Γ(E.curve.left, ⊤) :=
      E.globalSections_isField_of_ambient_isProper.toField
    letI : E.curve.left.Over
        (Spec (CommRingCat.of Γ(E.curve.left, ⊤))) :=
      ⟨E.curve.left.toSpecGlobalSections⟩
    HasPointedSmoothGenusZeroClassification Γ(E.curve.left, ⊤) →
      Nonempty (projectiveLineAsOver Γ(E.curve.left, ⊤) ≅
        E.curve.left.asOver
          (Spec (CommRingCat.of Γ(E.curve.left, ⊤)))) := by
  have hfiniteSeparable :=
    htail.globalSections_finiteSeparable_of_attachingNodeLift E p hnode
  exact projectiveLineIso_over_globalSections_of_pointedClassification
    E p htail hfiniteSeparable.2 hgeom

end SmoothGenusZeroSubcurveOver.IsRationalTail

end AlgebraicGeometry.Scheme

end
