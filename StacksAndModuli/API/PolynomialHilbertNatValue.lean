module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Rat.Defs

/-!
# Natural values of rational Hilbert polynomials

For degrees at which a rational Hilbert polynomial is known to be the dimension of a
vector space, its value is a natural number.  This small module keeps the corresponding
normalization independent of the projective cohomology and rank infrastructure.
-/

@[expose] public section

/-- The natural-number value specified by a rational Hilbert polynomial in degree `d`.
When `P(d)` is the dimension of a vector space, this is exactly that dimension. -/
def Polynomial.hilbertNatValue (P : Polynomial ℚ) (d : ℕ) : ℕ :=
  (P.eval (d : ℚ)).num.natAbs

/-- A rational Hilbert-polynomial value already presented as a natural number is
recovered by `Polynomial.hilbertNatValue`. -/
lemma Polynomial.hilbertNatValue_eq {P : Polynomial ℚ} {d q : ℕ}
    (h : (q : ℚ) = P.eval (d : ℚ)) : P.hilbertNatValue d = q := by
  rw [Polynomial.hilbertNatValue, ← h]
  simp

end
