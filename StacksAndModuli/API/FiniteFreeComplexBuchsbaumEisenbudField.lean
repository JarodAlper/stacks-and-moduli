module

public import StacksAndModuli.API.FiniteFreeComplexExactExpectedRanks

/-!
# The field case of the determinantal acyclicity criterion

Over a field, a matrix has rank at least `r` exactly when its ideal of `r`-minors is the
unit ideal.  Applying this degree by degree identifies exactness of a bounded finite free
complex, under its scheme-theoretic expected-rank upper bounds, with the unit-ideal
condition on every expected-size determinantal ideal.

This is the zero-dimensional local base case of the Buchsbaum--Eisenbud criterion.  The
general noetherian local theorem additionally permits expected-minor ideals containing
regular sequences of the relevant homological lengths.

Main declarations:

* `Matrix.minorIdeal_eq_top_iff_le_rank`;
* `Matrix.FiniteFreeComplex.isExactInPositiveDegreesUpTo_iff_minorIdeal_eq_top`;
* `Matrix.FiniteFreeComplex.
  isExactInPositiveDegreesUpTo_iff_expectedRankBounds_and_minorIdeal_eq_top`;
* `Matrix.FiniteFreeComplex.isExactInPositiveDegreesUpTo_residueField_iff_minorIdeal_eq_top`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v w

namespace Matrix

/-- Over a field, a rank lower bound makes the corresponding determinantal ideal the unit
ideal. -/
theorem minorIdeal_eq_top_of_le_rank
    {K : Type u} [Field K] {m : Type v} {n : Type w}
    [Finite m] [Fintype n] (A : Matrix m n K) {r : ℕ}
    (hr : r ≤ A.rank) :
    minorIdeal A r = ⊤ := by
  obtain ⟨rows, cols, hdet⟩ :=
    exists_minorDeterminant_ne_zero_of_le_rank A hr
  exact (minorIdeal A r).eq_top_of_isUnit_mem
    (minorDeterminant_mem_minorIdeal A r rows cols)
    (isUnit_iff_ne_zero.mpr hdet)

/-- If every minor one size above `r` vanishes over a field, the matrix rank is at most
`r`. -/
theorem rank_le_of_minorIdeal_succ_eq_bot
    {K : Type u} [Field K] {m : Type v} {n : Type w}
    [Finite m] [Fintype n] (A : Matrix m n K) {r : ℕ}
    (hminor : minorIdeal A (r + 1) = ⊥) :
    A.rank ≤ r := by
  by_contra hrank
  have hle : r + 1 ≤ A.rank := by omega
  obtain ⟨rows, cols, hdet⟩ :=
    exists_minorDeterminant_ne_zero_of_le_rank A hle
  have hmem := minorDeterminant_mem_minorIdeal A (r + 1) rows cols
  rw [hminor, Ideal.mem_bot] at hmem
  exact hdet hmem

/-- Over a field, the ideal of `r`-minors is the unit ideal exactly when the matrix has
rank at least `r`. -/
theorem minorIdeal_eq_top_iff_le_rank
    {K : Type u} [Field K] {m : Type v} {n : Type w}
    [Finite m] [Fintype n] (A : Matrix m n K) (r : ℕ) :
    minorIdeal A r = ⊤ ↔ r ≤ A.rank := by
  constructor
  · intro htop
    by_contra hrank
    have hbot : minorIdeal A r = ⊥ := by
      apply le_antisymm
      · rw [minorIdeal_le_iff]
        intro rows cols
        rw [Ideal.mem_bot]
        by_contra hdet
        exact hrank (le_rank_of_minorDeterminant_ne_zero A r rows cols hdet)
      · exact bot_le
    exact (show (⊥ : Ideal K) ≠ ⊤ from bot_ne_top) (hbot.symm.trans htop)
  · exact minorIdeal_eq_top_of_le_rank A

namespace FiniteFreeComplex

/-- Over a field, a bounded finite free complex satisfying the expected-rank upper bounds
is exact in its positive displayed degrees exactly when every expected-size determinantal
ideal is the unit ideal. -/
theorem isExactInPositiveDegreesUpTo_iff_minorIdeal_eq_top
    {K : Type u} [Field K]
    (C : FiniteFreeComplex K) (N : ℕ) (r : C.ExpectedRanks N)
    (hbounded : C.IsBoundedAbove N) (hbounds : C.HasExpectedRankBounds r) :
    C.IsExactInPositiveDegreesUpTo N ↔
      ∀ i : ℕ, i < N → minorIdeal (C.differential i) (r.rank i) = ⊤ := by
  rw [C.isExactInPositiveDegreesUpTo_iff_rank_eq_expectedRank N r hbounded]
  constructor
  · intro hrank i hi
    apply minorIdeal_eq_top_of_le_rank
    rw [hrank i (Nat.le_of_lt hi)]
  · intro hminor i hi
    by_cases hlt : i < N
    · have hle : (C.differential i).rank ≤ r.rank i :=
        rank_le_of_minorIdeal_succ_eq_bot (C.differential i) (hbounds i hlt)
      have hge : r.rank i ≤ (C.differential i).rank :=
        (minorIdeal_eq_top_iff_le_rank
          (C.differential i) (r.rank i)).mp (hminor i hlt)
      exact Nat.le_antisymm hle hge
    · have hiN : i = N := Nat.le_antisymm hi (Nat.le_of_not_gt hlt)
      subst i
      have hle : (C.differential N).rank ≤ C.termRank (N + 1) :=
        (C.differential N).rank_le_width
      have hle_zero : (C.differential N).rank ≤ 0 :=
        hle.trans_eq (hbounded (N + 1) (Nat.lt_succ_self N))
      exact (Nat.eq_zero_of_le_zero hle_zero).trans r.terminal.symm

/-- Over a field, the complete determinantal criterion for exactness consists of the
scheme-theoretic expected-rank upper bounds together with the unit-ideal condition on every
expected-size determinantal ideal. -/
theorem isExactInPositiveDegreesUpTo_iff_expectedRankBounds_and_minorIdeal_eq_top
    {K : Type u} [Field K]
    (C : FiniteFreeComplex K) (N : ℕ) (r : C.ExpectedRanks N)
    (hbounded : C.IsBoundedAbove N) :
    C.IsExactInPositiveDegreesUpTo N ↔
      C.HasExpectedRankBounds r ∧
        ∀ i : ℕ, i < N → minorIdeal (C.differential i) (r.rank i) = ⊤ := by
  constructor
  · intro hexact
    have hrank :=
      (C.isExactInPositiveDegreesUpTo_iff_rank_eq_expectedRank
        N r hbounded).mp hexact
    constructor
    · intro i hi
      rw [← hrank i (Nat.le_of_lt hi)]
      exact minorIdeal_succ_rank_eq_bot (C.differential i)
    · intro i hi
      apply minorIdeal_eq_top_of_le_rank
      rw [hrank i (Nat.le_of_lt hi)]
  · rintro ⟨hbounds, hminor⟩
    exact (C.isExactInPositiveDegreesUpTo_iff_minorIdeal_eq_top
      N r hbounded hbounds).mpr hminor

/-- Exactness of a residue-field fibre is equivalent to the unit-ideal condition for all
expected-size minors of the fibre differentials. -/
theorem isExactInPositiveDegreesUpTo_residueField_iff_minorIdeal_eq_top
    {R : Type u} [CommRing R]
    (C : FiniteFreeComplex R) (N : ℕ) (r : C.ExpectedRanks N)
    (hbounded : C.IsBoundedAbove N) (hbounds : C.HasExpectedRankBounds r)
    (q : PrimeSpectrum R) :
    (C.map (algebraMap R q.asIdeal.ResidueField)).IsExactInPositiveDegreesUpTo N ↔
      ∀ i : ℕ, i < N →
        minorIdeal
          ((C.differential i).map (algebraMap R q.asIdeal.ResidueField))
          (r.rank i) = ⊤ := by
  simpa only [map_differential, ExpectedRanks.map_rank] using
    (isExactInPositiveDegreesUpTo_iff_minorIdeal_eq_top
      (C.map (algebraMap R q.asIdeal.ResidueField)) N
      (r.map (algebraMap R q.asIdeal.ResidueField))
      (hbounded.map (algebraMap R q.asIdeal.ResidueField))
      (HasExpectedRankBounds.map r hbounds
        (algebraMap R q.asIdeal.ResidueField)))

end FiniteFreeComplex

end Matrix

end
