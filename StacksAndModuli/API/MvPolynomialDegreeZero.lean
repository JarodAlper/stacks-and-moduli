module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.FiniteType

/-!
# The degree-zero part of a graded polynomial ring

Supporting API with no Stacks Project counterpart.

`ℙⁿ_ℤ` is defined in §2.1 as `Proj` of the standard graded polynomial ring
`ℤ[x_0, …, x_n]`, and its structure morphism to `Spec ℤ` is `Proj.toSpecZero`, which lands in
the spectrum of the *degree-zero part*. Identifying that degree-zero part with the base ring is
what lets the book's `ℙⁿ_ℤ → Spec ℤ` be recognised as `Proj.toSpecZero`, and hence proper by
Mathlib's `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean`.

Mathlib has `MvPolynomial.homogeneousSubmodule` and `MvPolynomial.isHomogeneous_iff_...` but no
packaged ring isomorphism for the degree-zero piece.

Proof route: a multivariate polynomial is homogeneous of degree `0` exactly when it is a
constant, so `MvPolynomial.C` and the constant-coefficient map are mutually inverse ring maps
between `R` and the degree-zero submodule. The relevant Mathlib input is
`MvPolynomial.isHomogeneous_zero_iff_eq_C` (or the corresponding `totalDegree` characterisation).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v

namespace MvPolynomial

/-- The degree-zero part of the standard grading on `MvPolynomial σ R` is `R`. -/
noncomputable def degreeZeroRingEquiv (σ : Type v) (R : Type u) [CommRing R] :
    R ≃+* ↥((MvPolynomial.homogeneousSubmodule σ R) 0) where
  toFun r := ⟨C r, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C σ r)⟩
  invFun p := MvPolynomial.coeff 0 p.1
  left_inv r := by simp
  right_inv p := by
    obtain ⟨p, hp⟩ := p
    apply Subtype.ext
    have h0 : p.totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := σ)).mpr
        ((mem_homogeneousSubmodule _ _).mp hp)
    exact (totalDegree_eq_zero_iff_eq_C.mp h0).symm
  map_add' a b := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

@[simp]
lemma degreeZeroRingEquiv_apply_coe (σ : Type v) (R : Type u) [CommRing R] (r : R) :
    ((degreeZeroRingEquiv σ R) r : MvPolynomial σ R) = C r := rfl

/-- A polynomial ring is of finite type over its degree-zero part.

Needed so that Mathlib's `IsProper (Proj.toSpecZero 𝒜)` instance
(`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Proper.lean:372`), which is stated under
`[Algebra.FiniteType (𝒜 0) A]`, applies to `ℙⁿ`. Immediate from `degreeZeroRingEquiv`
together with `MvPolynomial.finiteType`. -/
instance degreeZero_finiteType (σ : Type v) [Finite σ] (R : Type u) [CommRing R] :
    Algebra.FiniteType ↥((MvPolynomial.homogeneousSubmodule σ R) 0) (MvPolynomial σ R) := by
  classical
  cases nonempty_fintype σ
  refine ⟨⟨Finset.univ.image X, ?_⟩⟩
  rw [eq_top_iff]
  intro p _
  induction p using MvPolynomial.induction_on with
  | C r =>
    exact Subalgebra.algebraMap_mem _
      (⟨C r, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C σ r)⟩ :
        ↥((MvPolynomial.homogeneousSubmodule σ R) 0))
  | add p q hp hq => exact add_mem (hp trivial) (hq trivial)
  | mul_X p i hp =>
    exact mul_mem (hp trivial) (Algebra.subset_adjoin
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem X (Finset.mem_univ i))))

end MvPolynomial
