module

public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Localizing polynomial coefficients below a prime

Let `q` be a prime of `A[x_i]` and let `p = q ∩ A`.  Base changing the polynomial ring
from `A` to the local ring `A_p` is a localization.  Hence `q` extends to a prime of
`A_p[x_i]`, and that extended prime lies over the closed point of `A_p`.

This is the ring-theoretic transport needed to apply local Noetherian approximation at an
arbitrary polynomial prime in the proof of Stacks Project tag 02JO.

Main declarations:
- `MvPolynomial.coefficientLocalizedPrime`.
- `MvPolynomial.coefficientLocalizedPrime_comap_C`.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace MvPolynomial

variable {A : Type u} [CommRing A] {sigma : Type v}

/-- The localization of the coefficient ring at the contraction of a polynomial prime. -/
abbrev coefficientLocalization
    (q : PrimeSpectrum (MvPolynomial sigma A)) :=
  Localization.AtPrime
    (q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)).asIdeal

/-- The polynomial ring after localizing its coefficient ring below a polynomial prime. -/
abbrev polynomialCoefficientLocalization
    (q : PrimeSpectrum (MvPolynomial sigma A)) :=
  MvPolynomial sigma (coefficientLocalization q)

/-- Extending a polynomial prime after localizing the coefficient ring at its contraction
again gives a prime. -/
noncomputable def coefficientLocalizedPrime
    (q : PrimeSpectrum (MvPolynomial sigma A)) :
    PrimeSpectrum (polynomialCoefficientLocalization q) := by
  let p : PrimeSpectrum A := q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)
  let Ap := Localization.AtPrime p.asIdeal
  let S := MvPolynomial sigma A
  let Sp := MvPolynomial sigma Ap
  let pc := Submonoid.map
    (MvPolynomial.C : A →+* S).toMonoidHom p.asIdeal.primeCompl
  letI : Algebra S Sp := MvPolynomial.algebraMvPolynomial
  letI : IsLocalization pc Sp := MvPolynomial.isLocalization p.asIdeal.primeCompl Ap
  have hdisj : Disjoint (pc : Set S) (q.asIdeal : Set S) := by
    rw [Set.disjoint_left]
    intro x hxpc hxq
    obtain ⟨a, ha, rfl⟩ := hxpc
    exact ha hxq
  exact ⟨q.asIdeal.map (algebraMap S Sp),
    IsLocalization.isPrime_of_isPrime_disjoint pc Sp q.asIdeal q.isPrime hdisj⟩

/-- After localizing the coefficient ring at the contraction of `q`, the extended
polynomial prime contracts to the closed maximal ideal of the localized coefficient ring. -/
theorem coefficientLocalizedPrime_comap_C
    (q : PrimeSpectrum (MvPolynomial sigma A)) :
    (coefficientLocalizedPrime q).asIdeal.comap
      (MvPolynomial.C : coefficientLocalization q →+*
        polynomialCoefficientLocalization q) =
      maximalIdeal (coefficientLocalization q) := by
  let p : PrimeSpectrum A := q.comap (MvPolynomial.C : A →+* MvPolynomial sigma A)
  let Ap := Localization.AtPrime p.asIdeal
  let S := MvPolynomial sigma A
  let Sp := MvPolynomial sigma Ap
  let pc := Submonoid.map
    (MvPolynomial.C : A →+* S).toMonoidHom p.asIdeal.primeCompl
  letI : Algebra S Sp := MvPolynomial.algebraMvPolynomial
  letI : IsLocalization pc Sp := MvPolynomial.isLocalization p.asIdeal.primeCompl Ap
  have hdisj : Disjoint (pc : Set S) (q.asIdeal : Set S) := by
    rw [Set.disjoint_left]
    intro x hxpc hxq
    obtain ⟨a, ha, rfl⟩ := hxpc
    exact ha hxq
  change Ideal.comap MvPolynomial.C
      (q.asIdeal.map (algebraMap S Sp)) = maximalIdeal Ap
  rw [← IsLocalization.map_under p.asIdeal.primeCompl Ap
      (Ideal.comap MvPolynomial.C (q.asIdeal.map (algebraMap S Sp))),
    ← IsLocalization.map_under p.asIdeal.primeCompl Ap (maximalIdeal Ap)]
  simp only [Ideal.comap_comap]
  rw [← MvPolynomial.algebraMap_eq (R := Ap),
    ← IsScalarTower.algebraMap_eq A Ap Sp,
    IsScalarTower.algebraMap_eq A S Sp, ← Ideal.comap_comap,
    ← Ideal.under_def S,
    IsLocalization.under_map_of_isPrime_disjoint pc Sp q.isPrime hdisj]
  congr 1
  exact (IsLocalization.AtPrime.under_maximalIdeal Ap p.asIdeal).symm

end MvPolynomial
