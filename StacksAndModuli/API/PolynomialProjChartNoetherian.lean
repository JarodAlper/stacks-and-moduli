module

public import StacksAndModuli.API.MvPolynomialDegreeZero
public import StacksAndModuli.API.AffineOpenSectionsExact
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# The standard charts of polynomial `Proj` are noetherian affine opens

`Scheme.Modules.surjective_app_of_shortExact_of_isAffineOpen`
(`API/AffineOpenSectionsExact.lean`) makes quasicoherent sections exact on every affine open.
This file supplies the standard-chart affineness of `D₊(xᵢ)` and also records its
noetherian coordinate ring when `R` is noetherian.

The noetherian half is a three-step chain, each step already available:

* `MvPolynomial.degreeZeroRingEquiv` — the degree-zero part of the grading is `R`;
* `MvPolynomial.degreeZero_finiteType` and `HomogeneousLocalization.Away.finiteType` —
  `A⁰_{xᵢ}` is a finite-type algebra over it;
* `Algebra.FiniteType.isNoetherianRing` (Hilbert basis), then transport along
  `AlgebraicGeometry.Proj.basicOpenIsoAway`.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.polynomialProj_isLocallyNoetherian`;
* `AlgebraicGeometry.ProjectiveSpace.isAffineOpen_polynomialBasicOpen`;
* `AlgebraicGeometry.ProjectiveSpace.isNoetherianRing_sections_polynomialBasicOpen`;
* `AlgebraicGeometry.ProjectiveSpace.surjective_app_polynomialBasicOpen_of_shortExact`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.degreeZero_finiteType

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The degree-zero part of the standard grading on `R[x₀,…,xₙ]` is noetherian, being `R`. -/
instance polynomialDegreeZero_isNoetherianRing [IsNoetherianRing R] :
    IsNoetherianRing ↥((MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) 0) :=
  isNoetherianRing_of_ringEquiv R (MvPolynomial.degreeZeroRingEquiv _ R)

/-- `xᵢ` is a homogeneous element of degree one. -/
theorem stdVar_mem_one (i : Fin (n + 1)) :
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)
      ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R i)

/-- **The chart ring `A⁰_{xᵢ}` is noetherian.**  It is a finite-type algebra over the
degree-zero part, which is `R`. -/
instance polynomialAway_isNoetherianRing [IsNoetherianRing R] (i : Fin (n + 1)) :
    IsNoetherianRing (HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) := by
  haveI := HomogeneousLocalization.Away.finiteType
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) 1 (stdVar_mem_one n R i)
  exact Algebra.FiniteType.isNoetherianRing
    ↥((MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) 0) _

/-- **Polynomial `Proj` over a noetherian ring is locally noetherian.**  `Proj 𝒜 ⟶ Spec (𝒜 0)`
is locally of finite type (Mathlib, from `Algebra.FiniteType (𝒜 0) A`) and `𝒜 0` is `R`. -/
instance polynomialProj_isLocallyNoetherian [IsNoetherianRing R] :
    IsLocallyNoetherian (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) :=
  LocallyOfFiniteType.isLocallyNoetherian
    (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))

/-- **The standard chart is an affine open.** -/
theorem isAffineOpen_polynomialBasicOpen (i : Fin (n + 1)) :
    IsAffineOpen (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) :=
  Proj.isAffineOpen_basicOpen _ _ (stdVar_mem_one n R i) Nat.one_pos

/-- **The sections of the structure sheaf on the standard chart form a noetherian ring.** -/
instance isNoetherianRing_sections_polynomialBasicOpen [IsNoetherianRing R] (i : Fin (n + 1)) :
    IsNoetherianRing Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)) :=
  isNoetherianRing_of_ringEquiv _
    (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) (stdVar_mem_one n R i)
      Nat.one_pos).commRingCatIsoToRingEquiv

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binder over an explicit polynomial `Proj` makes instance search slow;
-- see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
/-- **Sections on a standard chart of polynomial `Proj` are exact over an arbitrary ring.**
For a short exact
sequence of module sheaves with quasicoherent kernel, `Γ(D₊(xᵢ), -)` is surjective on the
right.  This is what makes the graded model `Γ_*(E)/Γ_*(K)` of a quotient sheaf agree with the
sheaf on every chart, even though `Γ_*` itself is only left exact. -/
theorem surjective_app_polynomialBasicOpen_of_shortExact
    (i : Fin (n + 1))
    {S : ShortComplex (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    Function.Surjective (S.g.val.app (op (Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)))).hom :=
  Scheme.Modules.surjective_app_of_shortExact_of_isAffineOpen
    (isAffineOpen_polynomialBasicOpen n R i) hS

end AlgebraicGeometry.ProjectiveSpace

end

end
