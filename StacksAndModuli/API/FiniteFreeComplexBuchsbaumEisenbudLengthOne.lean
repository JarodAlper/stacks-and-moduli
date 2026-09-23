module

public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import StacksAndModuli.API.FiniteFreeComplexExactExpectedRanks

/-!
# The length-one Buchsbaum--Eisenbud implication

This file proves the first nontrivial case of the implication from the determinantal
grade conditions to exactness in the Buchsbaum--Eisenbud criterion (Stacks Project tag
00N1).  For a matrix with `n` columns, every `n × n` minor annihilates each vector in
the kernel.  Consequently, if the ideal of maximal column minors contains an element
regular on the coefficient ring, the associated linear map is injective.

For a finite free complex bounded above by degree one, the expected-rank recursion says
that the expected rank of its only displayed differential is the full rank of its
source.  A length-one regular-sequence witness in that determinantal ideal therefore
forces exactness in positive degree.  This direction needs neither locality nor
Noetherianity; the converse and the induction for longer complexes require the depth and
associated-prime arguments of the general criterion.

Main declarations:

* `Matrix.maximalMinor_smul_eq_zero_of_mulVec_eq_zero`;
* `Matrix.minorIdeal_card_cols_smul_eq_zero_of_mulVec_eq_zero`;
* `Matrix.toLin'_injective_of_isSMulRegular_mem_minorIdeal_card_cols`;
* `Matrix.FiniteFreeComplex.
  isExactInPositiveDegreesUpTo_one_of_buchsbaumEisenbudGrade`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace Matrix

variable {R : Type u} [CommRing R]

/-- A maximal column minor annihilates every vector in the kernel of a finite matrix.

The selected columns are a permutation of all columns.  After making that permutation
into an equivalence, the adjugate identity for the resulting square submatrix gives the
claim. -/
theorem maximalMinor_smul_eq_zero_of_mulVec_eq_zero
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) (x : Fin n → R)
    (hx : A *ᵥ x = 0) (rows : Fin n ↪ Fin m) (cols : Fin n ↪ Fin n) :
    (A.submatrix rows cols).det • x = 0 := by
  let e : Fin n ≃ Fin n := cols.equivOfSurjective
    (Finite.surjective_of_injective cols.injective)
  let B : Matrix (Fin n) (Fin n) R := A.submatrix rows e
  let v : Fin n → R := fun j ↦ x (e j)
  have hBv : B *ᵥ v = 0 := by
    change A.submatrix rows e *ᵥ v = 0
    rw [Matrix.submatrix_mulVec_equiv]
    have hv : v ∘ e.symm = x := by
      funext k
      simp [v]
    rw [hv, hx]
    rfl
  have hdetv : B.det • v = 0 := by
    calc
      B.det • v = (B.adjugate * B) *ᵥ v := by
        rw [B.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
      _ = B.adjugate *ᵥ (B *ᵥ v) :=
        (Matrix.mulVec_mulVec v B.adjugate B).symm
      _ = 0 := by rw [hBv, Matrix.mulVec_zero]
  have hB : B = A.submatrix rows cols := rfl
  rw [← hB]
  funext k
  obtain ⟨j, rfl⟩ := e.surjective k
  exact congrFun hdetv j

/-- The ideal of maximal column minors annihilates every vector in the kernel of a
finite matrix. -/
theorem minorIdeal_card_cols_smul_eq_zero_of_mulVec_eq_zero
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) (x : Fin n → R)
    (hx : A *ᵥ x = 0) (z : R) (hz : z ∈ minorIdeal A n) :
    z • x = 0 := by
  have hle : minorIdeal A n ≤
      (Submodule.span R ({x} : Set (Fin n → R))).annihilator := by
    rw [minorIdeal, Ideal.span_le]
    rintro d ⟨⟨rows, cols⟩, rfl⟩
    apply (Submodule.mem_annihilator_span_singleton x
      (A.submatrix rows cols).det).mpr
    exact maximalMinor_smul_eq_zero_of_mulVec_eq_zero A x hx rows cols
  exact (Submodule.mem_annihilator_span_singleton x z).mp (hle hz)

/-- A finite matrix is injective when its maximal column-minor ideal contains an element
that acts regularly on the coefficient ring. -/
theorem toLin'_injective_of_isSMulRegular_mem_minorIdeal_card_cols
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (z : R) (hzI : z ∈ minorIdeal A n) (hz : IsSMulRegular R z) :
    Function.Injective (Matrix.toLin' A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hzx : z • x = 0 :=
    minorIdeal_card_cols_smul_eq_zero_of_mulVec_eq_zero A x hx z hzI
  exact funext fun i ↦ hz.right_eq_zero_of_smul (congrFun hzx i)

/-- Element-regular version of
`Matrix.toLin'_injective_of_isSMulRegular_mem_minorIdeal_card_cols`. -/
theorem toLin'_injective_of_isRegular_mem_minorIdeal_card_cols
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (z : R) (hzI : z ∈ minorIdeal A n) (hz : IsRegular z) :
    Function.Injective (Matrix.toLin' A) :=
  toLin'_injective_of_isSMulRegular_mem_minorIdeal_card_cols
    A z hzI hz.isSMulRegular

namespace FiniteFreeComplex

/-- The determinantal-grade implication of the Buchsbaum--Eisenbud criterion for a
finite free complex bounded above by degree one.

The expected-rank recursion makes the expected minors maximal column minors.  The grade
condition is stated in the same unit-ideal-or-regular-sequence form used by the general
relative-fibre locus. -/
theorem isExactInPositiveDegreesUpTo_one_of_buchsbaumEisenbudGrade
    (C : FiniteFreeComplex R) (r : C.ExpectedRanks 1)
    (hbounded : C.IsBoundedAbove 1)
    (hgrade : minorIdeal (C.differential 0) (r.rank 0) = ⊤ ∨
      ∃ f : Fin 1 → R,
        (∀ j, f j ∈ minorIdeal (C.differential 0) (r.rank 0)) ∧
          RingTheory.Sequence.IsRegular R (List.ofFn f)) :
    C.IsExactInPositiveDegreesUpTo 1 := by
  have hrank : r.rank 0 = C.termRank 1 := by
    have hrec : r.rank 0 + r.rank 1 = C.termRank 1 := by
      simpa using r.add_succ 0 (by omega)
    rw [r.terminal, add_zero] at hrec
    exact hrec
  rw [hrank] at hgrade
  obtain ⟨z, hzI, hzreg⟩ : ∃ z : R,
      z ∈ minorIdeal (C.differential 0) (C.termRank 1) ∧
        IsSMulRegular R z := by
    rcases hgrade with htop | ⟨f, hfI, hfreg⟩
    · refine ⟨1, ?_, isRegular_one.isSMulRegular⟩
      rw [htop]
      exact Submodule.mem_top
    · refine ⟨f 0, hfI 0, ?_⟩
      have hweak : RingTheory.Sequence.IsWeaklyRegular R [f 0] := by
        simpa using hfreg.toIsWeaklyRegular
      exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff R (f 0)).mp hweak
  have hinj : Function.Injective (Matrix.toLin' (C.differential 0)) :=
    toLin'_injective_of_isSMulRegular_mem_minorIdeal_card_cols
      (C.differential 0) z hzI hzreg
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  rw [LinearMap.exact_iff]
  have hterm2 : C.termRank 2 = 0 := hbounded 2 (by omega)
  have hxzero (x : Fin (C.termRank 2) → R) : x = 0 := by
    funext j
    have hj := j.isLt
    omega
  have hzero : Matrix.toLin' (C.differential 1) = 0 := by
    apply LinearMap.ext
    intro x
    rw [hxzero x, map_zero]
    rfl
  rw [hzero, LinearMap.range_zero, LinearMap.ker_eq_bot.mpr hinj]

end FiniteFreeComplex

end Matrix

end
