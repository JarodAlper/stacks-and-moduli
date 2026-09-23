module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Dimension of a quasi-finite algebra over affine space

Stacks Project tag **00QG**, label
`lemma-dimension-quasi-finite-over-polynomial-algebra`, in `algebra.tex`,
§`00QC` (Dimension of fibres).

A quasi-finite algebra cannot have a longer chain of prime ideals than its base.  Indeed,
contraction is strictly increasing on every chain: comparable primes with the same
contraction coincide for a quasi-finite algebra.  Applying this to affine `n`-space over a
field gives the dimension bound in tag 00QG.

Main declarations:

* `Algebra.QuasiFinite.ringKrullDim_le`;
* `Algebra.QuasiFinite.ringKrullDim_le_nat_of_mvPolynomial`.
-/

@[expose] public section

universe u v

namespace Algebra.QuasiFinite

/-- The Krull dimension of a quasi-finite algebra is at most the Krull dimension of its
coefficient ring. -/
theorem ringKrullDim_le
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.QuasiFinite R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
  apply Order.krullDim_le_of_strictMono
    (PrimeSpectrum.comap (algebraMap R S))
  intro P Q hPQ
  change P.asIdeal.under R < Q.asIdeal.under R
  refine lt_of_le_of_ne (Ideal.comap_mono hPQ.le) ?_
  intro hunder
  exact hPQ.ne (PrimeSpectrum.ext <|
    Algebra.QuasiFinite.eq_of_le_of_under_eq
      (R := R) P.asIdeal Q.asIdeal hPQ.le hunder)

/-- **Lemma 10.125.5** (`00QG`,
`lemma-dimension-quasi-finite-over-polynomial-algebra`): a finite-type algebra over a
field which is quasi-finite over affine `n`-space has Krull dimension at most `n`. -/
@[stacks 00QG]
theorem ringKrullDim_le_nat_of_mvPolynomial
    (k : Type u) [Field k] (S : Type v) [CommRing S] [Algebra k S]
    (n : ℕ) [Algebra (MvPolynomial (Fin n) k) S]
    [IsScalarTower k (MvPolynomial (Fin n) k) S]
    [Algebra.FiniteType k S] [Algebra.QuasiFinite (MvPolynomial (Fin n) k) S] :
    ringKrullDim S ≤ (n : WithBot ℕ∞) := by
  calc
    ringKrullDim S ≤ ringKrullDim (MvPolynomial (Fin n) k) := ringKrullDim_le
    _ = ringKrullDim k + Nat.card (Fin n) :=
      MvPolynomial.ringKrullDim_of_isNoetherianRing
    _ = ringKrullDim k + n := by simp
    _ = (n : WithBot ℕ∞) := by
      rw [ringKrullDim_eq_zero_of_field, zero_add]

end Algebra.QuasiFinite

end
