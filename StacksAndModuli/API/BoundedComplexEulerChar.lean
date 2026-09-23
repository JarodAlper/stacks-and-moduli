module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# The Euler characteristic of a bounded complex is computed by its cohomology

For a bounded cochain complex of finite-dimensional vector spaces, the alternating
sum of the dimensions of the terms equals the alternating sum of the dimensions of
the cohomology.  Mathlib defines both alternating sums
(`HomologicalComplex.eulerChar` and `HomologicalComplex.homologyEulerChar`) but does
not prove that they agree; this file supplies the identity in the concrete form used
by Cohomology and Base Change, where the complex is an explicit family of linear maps
`d i : M i →ₗ M (i + 1)`.

This is the linear-algebra engine of Theorem A.6.4, part (2):
once Theorem A.6.2 provides a bounded complex `K^•` of finite locally free modules
computing the cohomology of every base change, part (2) — local constancy of the Euler
characteristic `y ↦ χ(X_y, F_y)` — follows by combining the identity proved here (which
replaces the fibrewise cohomology dimensions by the fibrewise dimensions of the terms of
`K^•`) with local constancy of the ranks of a finite projective module
(`Module.isLocallyConstant_rankAtStalk`).

The companion statement for part (1), upper semicontinuity of `y ↦ h^i(X_y, F_y)`, runs
through the same complex via the book's Equation A.6.5 and additionally needs lower
semicontinuity of the rank of a matrix; that piece is not formalized here.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open Finset Module

namespace AlgebraicGeometry.BoundedComplex

universe u v

variable {K : Type u} [Field K] {M : ℕ → Type v} [∀ i, AddCommGroup (M i)]
  [∀ i, Module K (M i)] [∀ i, FiniteDimensional K (M i)]

/-- API lemma used in the proof of Theorem A.6.4: the alternating sums of a pair of
integer sequences differ by the telescoping boundary term.  Instantiated below with the
dimensions of the images and kernels of the differentials of a complex. -/
theorem alternating_identity (r k : ℕ → ℤ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (r i + k i) -
        (k 0 + ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * (k (i + 1) - r i)) =
      (-1 : ℤ) ^ n * r n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (f := fun i ↦ (-1 : ℤ) ^ i * (r i + k i)),
      Finset.sum_range_succ (f := fun i ↦ (-1 : ℤ) ^ (i + 1) * (k (i + 1) - r i))]
    linear_combination ih

section CohomologyOfComplex

variable {R : Type u} [Ring R] {N : ℕ → Type v} [∀ i, AddCommGroup (N i)]
  [∀ i, Module R (N i)] (e : ∀ i, N i →ₗ[R] N (i + 1))

/-- Background definition for Theorem A.6.4: the cohomology of the complex `e` at
position `i + 1`, as the quotient of the kernel of `e (i + 1)` by the image of `e i`.

Stated over an arbitrary ring, not only over a field: Theorem A.6.2 produces a complex of
projective modules over the base ring, and its cohomology is compared with the cohomology of
a sheaf before any residue field is taken. -/
abbrev cohomology (i : ℕ) : Type v :=
  ↥(LinearMap.ker (e (i + 1))) ⧸
    (LinearMap.range (e i)).comap (LinearMap.ker (e (i + 1))).subtype

end CohomologyOfComplex

variable (d : ∀ i, M i →ₗ[K] M (i + 1))

/-- API lemma used in the proof of Theorem A.6.4: the dimension of the cohomology at
position `i + 1` is the dimension of the kernel minus the dimension of the image. -/
theorem finrank_cohomology (i : ℕ)
    (hle : LinearMap.range (d i) ≤ LinearMap.ker (d (i + 1))) :
    (finrank K (LinearMap.ker (d (i + 1))) : ℤ) - finrank K (LinearMap.range (d i)) =
      (finrank K (cohomology d i) : ℤ) := by
  have h1 : finrank K (cohomology d i) +
      finrank K ((LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) =
      finrank K (LinearMap.ker (d (i + 1))) :=
    Submodule.finrank_quotient_add_finrank _
  have h2 : finrank K ((LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype)
      = finrank K (LinearMap.range (d i)) :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle)
  omega

/-- API lemma used in the proof of Theorem A.6.4 (the linear-algebra engine of part (2)):
for a cochain complex of finite-dimensional vector spaces whose differentials vanish in
degrees above `n`, the alternating sum of the dimensions of the terms equals the
alternating sum of the dimensions of the cohomology.  The Euler characteristic of the complex is
therefore computed by its terms alone, with no reference to the differentials — which is
what makes it locally constant in a family. -/
theorem alternating_sum_finrank_eq_alternating_sum_finrank_cohomology (n : ℕ)
    (hle : ∀ i, LinearMap.range (d i) ≤ LinearMap.ker (d (i + 1)))
    (hvanish : LinearMap.range (d n) = ⊥) :
    ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * finrank K (M i) =
      (finrank K (LinearMap.ker (d 0)) : ℤ) +
        ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * finrank K (cohomology d i) := by
  have hid := alternating_identity (fun i ↦ (finrank K (LinearMap.range (d i)) : ℤ))
    (fun i ↦ (finrank K (LinearMap.ker (d i)) : ℤ)) n
  have hrn : ∀ i, (finrank K (LinearMap.range (d i)) : ℤ) +
      (finrank K (LinearMap.ker (d i)) : ℤ) = (finrank K (M i) : ℤ) := fun i ↦ by
    have := LinearMap.finrank_range_add_finrank_ker (d i)
    omega
  have hcoh : ∀ i, (finrank K (LinearMap.ker (d (i + 1))) : ℤ) -
      (finrank K (LinearMap.range (d i)) : ℤ) = (finrank K (cohomology d i) : ℤ) :=
    fun i ↦ finrank_cohomology d i (hle i)
  have hzero : (finrank K (LinearMap.range (d n)) : ℤ) = 0 := by
    rw [hvanish]
    simp
  rw [hzero, mul_zero] at hid
  simp only [hrn, hcoh] at hid
  linarith [hid]

/-- API lemma used in the proof of Theorem A.6.4 (the local-constancy engine of
part (2)): the alternating sum of the fibrewise ranks of a bounded family of finite
projective modules is a locally constant function on the spectrum.  Combined with
`alternating_sum_finrank_eq_alternating_sum_finrank_cohomology`, applied to the fibres of
the complex supplied by Theorem A.6.2, this is exactly the local constancy of the Euler
characteristic `y ↦ χ(X_y, F_y)`. -/
theorem isLocallyConstant_alternating_sum_rankAtStalk {R : Type u} [CommRing R] (n : ℕ)
    (N : ℕ → Type v) [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, Module.FinitePresentation R (N i)] [∀ i, Module.Flat R (N i)] :
    IsLocallyConstant (fun p : PrimeSpectrum R ↦
      ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * Module.rankAtStalk (N i) p) := by
  have hterm : ∀ i : ℕ, IsLocallyConstant
      (fun p : PrimeSpectrum R ↦ (-1 : ℤ) ^ i * Module.rankAtStalk (N i) p) := fun i ↦
    (Module.isLocallyConstant_rankAtStalk (R := R) (M := N i)).comp
      (fun m : ℕ ↦ ((-1 : ℤ) ^ i * m))
  induction n with
  | zero => simpa using hterm 0
  | succ n ih =>
    have := ih.add (hterm (n + 1))
    simpa [Finset.sum_range_succ, Pi.add_def] using this

end AlgebraicGeometry.BoundedComplex
