module

public import StacksAndModuli.API.PolynomialHilbertNatValue
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»

/-!
# Eventual natural values of a Hilbert polynomial

Once a rational polynomial agrees with the Hilbert function of a projective-space sheaf,
its sufficiently large values are natural numbers.  This file records the normalization in
the exact `Polynomial.hilbertNatValue` form used by the Grassmannian rank packages.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Filter Opposite

namespace AlgebraicGeometry.Scheme.HasHilbertPolynomialOver

/-- At a degree where the Hilbert function agrees with `P`, the normalized natural value of
`P` is exactly that Hilbert-function value. -/
theorem hilbertNatValue_eq_hilbertFunction
    {n : ℕ} {R : CommRingCat.{u}}
    {F : (projectiveSpaceOver n (Spec R)).Modules}
    {P : Polynomial ℚ} {d : ℕ}
    (h : (hilbertFunctionOver F (d : ℤ) : ℚ) =
      P.eval (d : ℚ)) :
    P.hilbertNatValue d = hilbertFunctionOver F (d : ℤ) :=
  Polynomial.hilbertNatValue_eq h

/-- A Hilbert polynomial takes its normalized natural value, viewed in `ℚ`, in every
sufficiently large degree. -/
theorem exists_bound_hilbertNatValue_cast_eq
    {n : ℕ} {R : CommRingCat.{u}}
    {F : (projectiveSpaceOver n (Spec R)).Modules}
    {P : Polynomial ℚ}
    (h : HasHilbertPolynomialOver F P) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      (P.hilbertNatValue d : ℚ) = P.eval (d : ℚ) := by
  change ∀ᶠ d : ℕ in atTop,
    (hilbertFunctionOver F (d : ℤ) : ℚ) = P.eval (d : ℚ) at h
  obtain ⟨D, hD⟩ := eventually_atTop.mp h
  refine ⟨D, ?_⟩
  intro d hd
  rw [hilbertNatValue_eq_hilbertFunction (hD d hd)]
  exact hD d hd

/-- Sufficiently far out, the normalized-value identities hold simultaneously in two
adjacent degrees. -/
theorem exists_bound_hilbertNatValue_cast_eq_and_succ
    {n : ℕ} {R : CommRingCat.{u}}
    {F : (projectiveSpaceOver n (Spec R)).Modules}
    {P : Polynomial ℚ}
    (h : HasHilbertPolynomialOver F P) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      (P.hilbertNatValue d : ℚ) = P.eval (d : ℚ) ∧
        (P.hilbertNatValue (d + 1) : ℚ) = P.eval ((d + 1 : ℕ) : ℚ) := by
  obtain ⟨D, hD⟩ := h.exists_bound_hilbertNatValue_cast_eq
  exact ⟨D, fun d hd ↦ ⟨hD d hd, hD (d + 1) (by omega)⟩⟩

end AlgebraicGeometry.Scheme.HasHilbertPolynomialOver

end
