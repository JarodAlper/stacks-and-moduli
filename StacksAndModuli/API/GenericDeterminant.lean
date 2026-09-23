module

public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The generic determinant is homogeneous

The determinant of the generic matrix — the matrix of variables
`Matrix.mvPolynomialX` — is a homogeneous polynomial of degree the size of the
matrix; together with Mathlib's `Matrix.det_mvPolynomialX_ne_zero` it is a
nonzero homogeneous element of the polynomial ring in the matrix entries.

This is the algebraic seed for the projective linear group: `PGL_{n+1}` is the
basic open `D₊(det)` of the projectivized matrix space
`ℙ(Mat_{n+1}) = Proj (MvPolynomial (Fin (n+1) × Fin (n+1)) R)`, and homogeneity
of the determinant is what makes that basic open well defined.  Consumer:
the representability programme for
`AlgebraicGeometry.projectiveLinearGroupPresheaf`
(`StacksAndModuli/API/ProjectiveLinearGroupPresheaf.lean`).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open MvPolynomial

namespace Matrix

/-- The determinant of the generic matrix is homogeneous of degree the size of
the matrix. -/
theorem isHomogeneous_det_mvPolynomialX (m : Type*) [Fintype m] [DecidableEq m]
    (R : Type*) [CommRing R] :
    MvPolynomial.IsHomogeneous ((Matrix.mvPolynomialX m m R).det)
      (Fintype.card m) := by
  rw [Matrix.det_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro σ _
  have hprod : MvPolynomial.IsHomogeneous
      (∏ i, Matrix.mvPolynomialX m m R (σ i) i) (Fintype.card m) := by
    have h := MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i ↦ Matrix.mvPolynomialX m m R (σ i) i) (fun _ ↦ 1)
      (fun i _ ↦ by
        rw [Matrix.mvPolynomialX_apply]
        exact MvPolynomial.isHomogeneous_X _ _)
    simpa using h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> rw [h]
  · simpa using hprod
  · simpa using hprod.neg

end Matrix
