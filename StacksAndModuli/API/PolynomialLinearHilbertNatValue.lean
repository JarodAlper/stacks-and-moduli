module

public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import StacksAndModuli.API.PolynomialHilbertNatValue

/-!
# Natural values of linear Hilbert polynomials

A rational polynomial of degree at most one is determined by two adjacent values.  When
those values are natural numbers with increment `a`, every later value is the corresponding
natural arithmetic progression.  This file records that elementary bridge in the
`Polynomial.hilbertNatValue` normalization used by the Quot Grassmannians.

Main declarations:

* `Polynomial.eval_nat_add_eq_of_natDegree_le_one`;
* `Polynomial.hilbertNatValue_nat_add_eq_of_natDegree_le_one`.
-/

@[expose] public section

namespace Polynomial

/-- A rational polynomial of degree at most one whose values at `d` and `d + 1` are
`q₀` and `q₀ + a` has value `q₀ + k * a` at `d + k`.

The hypotheses are oriented from the natural-number casts to polynomial evaluations so
that the conclusion feeds directly into `Polynomial.hilbertNatValue_eq`. -/
theorem eval_nat_add_eq_of_natDegree_le_one
    (P : Polynomial ℚ) (hP : P.natDegree ≤ 1)
    (d q₀ a : ℕ)
    (hd : (q₀ : ℚ) = P.eval (d : ℚ))
    (hsucc : ((q₀ + a : ℕ) : ℚ) = P.eval ((d + 1 : ℕ) : ℚ)) :
    ∀ k : ℕ, ((q₀ + k * a : ℕ) : ℚ) =
      P.eval ((d + k : ℕ) : ℚ) := by
  intro k
  rw [P.eq_X_add_C_of_natDegree_le_one hP] at hd hsucc ⊢
  simp only [eval_add, eval_mul, eval_C, eval_X] at hd hsucc ⊢
  push_cast at hd hsucc ⊢
  nlinarith

/-- Under the same adjacent-value hypotheses, the normalized natural values of a linear
Hilbert polynomial form the expected arithmetic progression. -/
theorem hilbertNatValue_nat_add_eq_of_natDegree_le_one
    (P : Polynomial ℚ) (hP : P.natDegree ≤ 1)
    (d q₀ a : ℕ)
    (hd : (q₀ : ℚ) = P.eval (d : ℚ))
    (hsucc : ((q₀ + a : ℕ) : ℚ) = P.eval ((d + 1 : ℕ) : ℚ)) :
    ∀ k : ℕ, P.hilbertNatValue (d + k) = q₀ + k * a := by
  intro k
  exact hilbertNatValue_eq
    (P.eval_nat_add_eq_of_natDegree_le_one hP d q₀ a hd hsucc k)

/-- If two adjacent normalized natural values differ by `a`, and both agree with a
degree-at-most-one polynomial, then all later normalized values have the same increment. -/
theorem hilbertNatValue_nat_add_eq_of_adjacent
    (P : Polynomial ℚ) (hP : P.natDegree ≤ 1) (d a : ℕ)
    (hd : (P.hilbertNatValue d : ℚ) = P.eval (d : ℚ))
    (hsucc : (P.hilbertNatValue (d + 1) : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (hgrowth : P.hilbertNatValue (d + 1) = P.hilbertNatValue d + a) :
    ∀ k : ℕ,
      P.hilbertNatValue (d + k) = P.hilbertNatValue d + k * a := by
  have hsucc' : ((P.hilbertNatValue d + a : ℕ) : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ) := by
    rw [← hgrowth]
    exact hsucc
  exact P.hilbertNatValue_nat_add_eq_of_natDegree_le_one
    hP d (P.hilbertNatValue d) a hd hsucc'

end Polynomial

end
