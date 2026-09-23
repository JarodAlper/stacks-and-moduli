module

public import StacksAndModuli.API.PureDimension
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Pure dimension of polynomial fibres

The spectrum of a polynomial ring in finitely many variables over a field is irreducible
and has Krull dimension equal to the number of variables.  Consequently, every residue
fibre of a polynomial algebra has that same pure dimension.

This is the pure-dimensional half of the fibre hypotheses in the polynomial specialization
of Stacks Project tag 00RA.

Main declarations:

* `TopologicalSpace.isPureOfDimension_of_irreducibleSpace`;
* `MvPolynomial.isPureOfDimension_primeSpectrum_of_field`;
* `Ideal.Fiber.isRegularRing_mvPolynomial`;
* `Ideal.Fiber.isPureOfDimension_mvPolynomial`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set

universe u

namespace MvPolynomial

/-- A polynomial ring in finitely many variables over a field has pure dimension equal to
the number of variables. -/
theorem isPureOfDimension_primeSpectrum_of_field
    (K sigma : Type u) [Field K] [Finite sigma] :
    TopologicalSpace.IsPureOfDimension
      (PrimeSpectrum (MvPolynomial sigma K)) (Nat.card sigma : WithBot ℕ∞) := by
  have h := TopologicalSpace.isPureOfDimension_of_irreducibleSpace
    (PrimeSpectrum (MvPolynomial sigma K))
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, zero_add] at h
  exact h

end MvPolynomial

namespace Ideal.Fiber

/-- Every residue fibre of a finite-variable polynomial algebra is a regular ring. -/
theorem isRegularRing_mvPolynomial
    {A sigma : Type u} [CommRing A] [Finite sigma] (p : PrimeSpectrum A) :
    IsRegularRing (p.asIdeal.Fiber (MvPolynomial sigma A)) := by
  let K := p.asIdeal.ResidueField
  let e : p.asIdeal.Fiber (MvPolynomial sigma A) ≃ₐ[K]
      MvPolynomial sigma K :=
    MvPolynomial.algebraTensorAlgEquiv A K
  let _ : IsRegularRing (MvPolynomial sigma K) :=
    MvPolynomial.isRegularRing_of_isRegularRing K
  exact IsRegularRing.of_ringEquiv e.toRingEquiv.symm

/-- Every residue fibre of a finite-variable polynomial algebra has pure dimension equal
to the number of variables. -/
theorem isPureOfDimension_mvPolynomial
    {A sigma : Type u} [CommRing A] [Finite sigma] (p : PrimeSpectrum A) :
    TopologicalSpace.IsPureOfDimension
      (PrimeSpectrum (p.asIdeal.Fiber (MvPolynomial sigma A)))
      (Nat.card sigma : WithBot ℕ∞) := by
  let K := p.asIdeal.ResidueField
  let e : p.asIdeal.Fiber (MvPolynomial sigma A) ≃ₐ[K]
      MvPolynomial sigma K :=
    MvPolynomial.algebraTensorAlgEquiv A K
  have hpoly := MvPolynomial.isPureOfDimension_primeSpectrum_of_field K sigma
  exact hpoly.homeomorph
    (PrimeSpectrum.homeomorphOfRingEquiv e.toRingEquiv).symm

end Ideal.Fiber

end
