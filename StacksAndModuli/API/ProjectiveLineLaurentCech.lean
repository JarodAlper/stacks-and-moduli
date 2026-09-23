module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Polynomial.Laurent

/-!
# The Laurent-polynomial Cech sequence for the projective line

This file proves the algebraic calculation underlying the standard two-affine-cover
computation of the structure-sheaf cohomology of the projective line. We represent
sections on the two charts by `R[X]` and sections on their overlap by `R[T;T⁻¹]`.
The second chart embeds after changing coordinates by `T ↦ T⁻¹`.

The resulting sequence of additive groups

`R → R[X] × R[X] → R[T;T⁻¹]`

is short exact: the first map sends a constant to the two identical constant
polynomials, while the second takes the difference of the two chart restrictions.
In particular, every Laurent polynomial is such a difference. Identifying these
explicit maps with the restriction maps of the actual standard opens is a separate
geometric comparison.

## Main results

* `LaurentPolynomial.twoChartDifference_surjective`;
* `LaurentPolynomial.twoChartDifference_eq_zero_iff`;
* `LaurentPolynomial.exact_twoChartConstantDiagonal_twoChartDifference`;
* `LaurentPolynomial.twoChartCech_shortExact`.
-/

@[expose] public noncomputable section

open scoped LaurentPolynomial Polynomial

universe u

namespace LaurentPolynomial

variable (R : Type u) [CommRing R]

/-- On a nonnegative exponent, the Laurent embedding preserves polynomial
coefficients. -/
@[simp]
lemma coeff_toLaurent_nat (p : R[X]) (n : ℕ) :
    (Polynomial.toLaurent p).coeff (n : ℤ) = p.coeff n := by
  rw [Polynomial.toLaurent_apply, AddMonoidAlgebra.mapDomain]
  rw [Finsupp.mapDomain_apply Nat.cast_injective]
  rfl

/-- A polynomial embedded into the Laurent polynomials has no coefficient at a
negative exponent. -/
@[simp]
lemma coeff_toLaurent_negSucc (p : R[X]) (n : ℕ) :
    (Polynomial.toLaurent p).coeff (Int.negSucc n) = 0 := by
  rw [Polynomial.toLaurent_apply, AddMonoidAlgebra.mapDomain]
  rw [Finsupp.mapDomain_of_notMem_range]
  rintro ⟨m, hm⟩
  omega

/-- The difference of the two restrictions from the standard affine charts of the
projective line to their overlap. The second restriction uses the inverse coordinate. -/
noncomputable def twoChartDifference : R[X] × R[X] →+ R[T;T⁻¹] where
  toFun pq := Polynomial.toLaurent pq.1 -
    invert (Polynomial.toLaurent pq.2)
  map_zero' := by simp
  map_add' p q := by
    simp only [map_add, Prod.fst_add, Prod.snd_add]
    abel

/-- Embed constants diagonally into the polynomial rings of the two standard charts. -/
noncomputable def twoChartConstantDiagonal : R →+ R[X] × R[X] where
  toFun r := (Polynomial.C r, Polynomial.C r)
  map_zero' := by simp
  map_add' r s := by simp

/-- Evaluation formula for the two-chart difference map. -/
@[simp]
lemma twoChartDifference_apply (pq : R[X] × R[X]) :
    twoChartDifference R pq = Polynomial.toLaurent pq.1 -
      invert (Polynomial.toLaurent pq.2) := rfl

/-- Every Laurent polynomial is the difference of a polynomial in `T` and a
polynomial in `T⁻¹`. -/
theorem twoChartDifference_surjective :
    Function.Surjective (twoChartDifference R) := by
  intro f
  induction f using LaurentPolynomial.induction_on' with
  | add f g hf hg =>
      obtain ⟨⟨p, q⟩, hpq⟩ := hf
      obtain ⟨⟨p', q'⟩, hpq'⟩ := hg
      refine ⟨⟨p + p', q + q'⟩, ?_⟩
      change twoChartDifference R ((p, q) + (p', q')) = f + g
      rw [map_add, hpq, hpq']
  | C_mul_T n a =>
      rcases n with n | n
      · refine ⟨⟨Polynomial.monomial n a, 0⟩, ?_⟩
        simp [twoChartDifference]
      · refine ⟨⟨0, Polynomial.monomial (n + 1) (-a)⟩, ?_⟩
        simp [twoChartDifference, Int.negSucc_eq]

/-- If a polynomial in `T` equals a polynomial in `T⁻¹`, both polynomials are
the same constant. -/
theorem eq_constant_of_toLaurent_eq_invert_toLaurent
    {p q : R[X]}
    (h : Polynomial.toLaurent p = invert (Polynomial.toLaurent q)) :
    p = Polynomial.C (p.coeff 0) ∧
      q = Polynomial.C (q.coeff 0) ∧ p.coeff 0 = q.coeff 0 := by
  have constant_of {a b : R[X]}
      (hab : Polynomial.toLaurent a = invert (Polynomial.toLaurent b)) :
      a = Polynomial.C (a.coeff 0) := by
    ext n
    rcases n with _ | n
    · simp
    · have hn : -((n + 1 : ℕ) : ℤ) = Int.negSucc n := by omega
      have hc := congrArg
        (fun z : R[T;T⁻¹] ↦ z.coeff ((n + 1 : ℕ) : ℤ)) hab
      rw [coeff_toLaurent_nat, invert_apply, hn,
        coeff_toLaurent_negSucc] at hc
      simpa using hc
  have hp := constant_of h
  have hinv := congrArg (invert (R := R)) h
  have hq : Polynomial.toLaurent q = invert (Polynomial.toLaurent p) := by
    rw [involutive_invert _] at hinv
    exact hinv.symm
  have hq' := constant_of hq
  refine ⟨hp, hq', ?_⟩
  have hc := congrArg (fun z : R[T;T⁻¹] ↦ z.coeff 0) h
  change (Polynomial.toLaurent p).coeff ((0 : ℕ) : ℤ) =
    (invert (Polynomial.toLaurent q)).coeff ((0 : ℕ) : ℤ) at hc
  rw [coeff_toLaurent_nat R p 0, invert_apply] at hc
  simp only [Nat.cast_zero, neg_zero] at hc
  exact hc.trans (by simpa using coeff_toLaurent_nat R q 0)

/-- The kernel of the two-chart difference map consists exactly of diagonal
constant polynomials. -/
theorem twoChartDifference_eq_zero_iff (p q : R[X]) :
    twoChartDifference R (p, q) = 0 ↔
      ∃ r : R, p = Polynomial.C r ∧ q = Polynomial.C r := by
  constructor
  · intro h
    have hpq : Polynomial.toLaurent p =
        invert (Polynomial.toLaurent q) := sub_eq_zero.mp h
    obtain ⟨hp, hq, hpq₀⟩ :=
      eq_constant_of_toLaurent_eq_invert_toLaurent R hpq
    exact ⟨p.coeff 0, hp, hq.trans (congrArg Polynomial.C hpq₀.symm)⟩
  · rintro ⟨r, rfl, rfl⟩
    simp [twoChartDifference]

/-- The diagonal-constant map and two-chart difference map are exact. -/
theorem exact_twoChartConstantDiagonal_twoChartDifference :
    Function.Exact (twoChartConstantDiagonal R) (twoChartDifference R) := by
  intro pq
  rcases pq with ⟨p, q⟩
  rw [twoChartDifference_eq_zero_iff]
  constructor
  · rintro ⟨r, rfl, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, Prod.mk.inj hr.symm⟩

/-- The diagonal embedding of constants into the two chart rings is injective. -/
theorem twoChartConstantDiagonal_injective :
    Function.Injective (twoChartConstantDiagonal R) := by
  intro r s h
  have hcoeff := congrArg (fun pq : R[X] × R[X] ↦ pq.1.coeff 0) h
  simpa [twoChartConstantDiagonal] using hcoeff

/-- The algebraic Cech sequence for the two standard charts of the projective line
is short exact, expressed as injectivity, exactness, and surjectivity of its maps. -/
theorem twoChartCech_shortExact :
    Function.Injective (twoChartConstantDiagonal R) ∧
      Function.Exact (twoChartConstantDiagonal R) (twoChartDifference R) ∧
      Function.Surjective (twoChartDifference R) :=
  ⟨twoChartConstantDiagonal_injective R,
    exact_twoChartConstantDiagonal_twoChartDifference R,
    twoChartDifference_surjective R⟩

end LaurentPolynomial

end
