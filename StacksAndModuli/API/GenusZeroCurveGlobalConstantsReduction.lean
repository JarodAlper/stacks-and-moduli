module

public import StacksAndModuli.API.GenusZeroCurveClassificationReduction
public import StacksAndModuli.API.GlobalSectionsRationalPoint
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# Genus-zero curves over their field of global constants

This file packages the exact global-constants form of the pointed genus-zero
classification used for rational tails.  A finite field of global constants and
genus zero over an original field imply intrinsic genus zero.  If the canonical
map to the spectrum of global constants is smooth and geometrically integral,
bijective evaluation at one point supplies every remaining hypothesis of the
pointed classification.

The conclusion is conditional only on
`HasPointedSmoothGenusZeroClassification`, the still-missing implication of
Exercise 6.1.13.  No smoothness or geometric-integrality claim after changing
the field of constants is hidden in the reduction.

## Main results

* `AlgebraicGeometry.Scheme.genus_eq_zero_of_genusOver_eq_zero_of_finite_globalSections`;
* `AlgebraicGeometry.Scheme.
    projectiveLineIso_over_globalSections_of_pointedClassification`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- If the global-sections ring is a finite field extension of the original base,
genus zero over the original field implies intrinsic genus zero. -/
theorem genus_eq_zero_of_genusOver_eq_zero_of_finite_globalSections
    {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    (hfield : IsField Γ(X, ⊤))
    (hfinite : Module.Finite k Γ(X, ⊤))
    (hgenus : genusOver k X = 0) : X.genus = 0 := by
  let _ : Field Γ(X, ⊤) := hfield.toField
  let _ : FiniteDimensional k Γ(X, ⊤) := hfinite
  rw [genusOver_def] at hgenus
  rw [genus_def]
  have htower := Module.finrank_mul_finrank k Γ(X, ⊤)
    (Modules.H (structureModule X) 1)
  rw [hgenus] at htower
  exact (Nat.mul_eq_zero.mp htower).resolve_left
    Module.finrank_pos.ne'

/-- The pointed genus-zero classification over the field of global constants.

Bijective evaluation constructs the rational section. Properness and smoothness
supply finite type, while `hdim` supplies the curve dimension. For a rational tail,
`GlobalConstantsSmooth` supplies the explicit smoothness hypothesis once the finite
field of constants is separable; geometric integrality over that field remains a
separate input. -/
theorem projectiveLineIso_over_globalSections_of_pointedClassification
    (X : Scheme.{u})
    (hfield : IsField Γ(X, ⊤))
    (hproper : IsProper X.toSpecGlobalSections)
    (hsmooth : Smooth X.toSpecGlobalSections)
    (hgeom : GeometricallyIntegral X.toSpecGlobalSections)
    (hdim : topologicalKrullDim X = 1)
    (hgenus : X.genus = 0) (x : X)
    (heval : Function.Bijective (X.Γevaluation x)) :
    letI : Field Γ(X, ⊤) := hfield.toField
    letI : X.Over (Spec (CommRingCat.of Γ(X, ⊤))) :=
      ⟨X.toSpecGlobalSections⟩
    HasPointedSmoothGenusZeroClassification Γ(X, ⊤) →
      Nonempty (projectiveLineAsOver Γ(X, ⊤) ≅
        X.asOver (Spec (CommRingCat.of Γ(X, ⊤)))) := by
  let _ : Field Γ(X, ⊤) := hfield.toField
  let _ : X.Over (Spec (CommRingCat.of Γ(X, ⊤))) :=
    ⟨X.toSpecGlobalSections⟩
  intro H
  let _ : IsProper (X ↘ Spec (CommRingCat.of Γ(X, ⊤))) := hproper
  let _ : Smooth (X ↘ Spec (CommRingCat.of Γ(X, ⊤))) := hsmooth
  let _ : GeometricallyIntegral
      (X ↘ Spec (CommRingCat.of Γ(X, ⊤))) := hgeom
  let _ : IsCurveOver Γ(X, ⊤) X :=
    ⟨inferInstance, inferInstance, hdim⟩
  apply H X
  · exact (genusOver_eq_genus Γ(X, ⊤) X
      (bijective_baseRingHom_toSpecGlobalSections X)).trans hgenus
  · exact ⟨sectionToSpecGlobalSectionsOfBijectiveEvaluation X x heval,
      sectionToSpecGlobalSectionsOfBijectiveEvaluation_comp X x heval⟩

end AlgebraicGeometry.Scheme

end
