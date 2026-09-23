module

public import StacksAndModuli.API.ExactSequenceFinrank
public import StacksAndModuli.API.FiniteFreeComplexDeterminantalGrade

/-!
# Exact finite free complexes and their expected ranks

This file supplies the elementary linear-algebra half of the numerical input to the
Buchsbaum--Eisenbud acyclicity criterion.  Exactness of two adjacent differentials in a
finite free complex over a field says that their matrix ranks add to the rank of the
middle term.  Consequently, an exact bounded complex has expected ranks given by the
actual ranks of its differentials, and the minors one size larger vanish.

The final theorem applies this observation after passage to a residue field: if a fibre
complex is exact, then every displayed differential has the prescribed expected rank on
that fibre.  The converse implication from determinantal grade conditions to exactness is
not asserted here.

Main declarations:

* `Matrix.rank_add_rank_eq_card_of_exact_toLin'`;
* `Matrix.exact_toLin'_iff_rank_add_rank_eq_card`;
* `Matrix.FiniteFreeComplex.IsExactInPositiveDegreesUpTo`;
* `Matrix.FiniteFreeComplex.expectedRanksOfExact`;
* `Matrix.FiniteFreeComplex.isExactInPositiveDegreesUpTo_iff_rank_eq_expectedRank`;
* `Matrix.FiniteFreeComplex.expectedRanksOfExact_hasExpectedRankBounds`;
* `Matrix.FiniteFreeComplex.isExactInPositiveDegreesUpTo_iff_rank_residueField_eq_expectedRank`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

universe u v

namespace Matrix

/-- Exactness of two matrix maps over a field gives the expected rank sum at their
common finite-dimensional term. -/
theorem rank_add_rank_eq_card_of_exact_toLin'
    {K : Type u} [Field K]
    {l m n : Type v} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix l m K) (B : Matrix m n K)
    (h : Function.Exact (Matrix.toLin' B) (Matrix.toLin' A)) :
    A.rank + B.rank = Fintype.card m := by
  classical
  have hdim := Module.finrank_range_add_finrank_range_of_exact h
  rw [Matrix.range_toLin', Matrix.range_toLin',
    ← B.rank_eq_finrank_span_cols, ← A.rank_eq_finrank_span_cols,
    Module.finrank_fintype_fun_eq_card] at hdim
  simpa only [add_comm] using hdim

/-- For two consecutive matrix maps whose composite is zero, exactness at their common
finite-dimensional term is equivalent to the expected rank sum. -/
theorem exact_toLin'_iff_rank_add_rank_eq_card
    {K : Type u} [Field K]
    {l m n : Type v} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (A : Matrix l m K) (B : Matrix m n K) (hAB : A * B = 0) :
    Function.Exact (Matrix.toLin' B) (Matrix.toLin' A) ↔
      A.rank + B.rank = Fintype.card m := by
  constructor
  · exact Matrix.rank_add_rank_eq_card_of_exact_toLin' A B
  · intro hrank
    rw [LinearMap.exact_iff]
    have hle : LinearMap.range (Matrix.toLin' B) ≤
        LinearMap.ker (Matrix.toLin' A) := by
      rw [LinearMap.range_le_ker_iff, ← Matrix.toLin'_mul, hAB]
      simp
    have hA : A.rank = Module.finrank K
        (LinearMap.range (Matrix.toLin' A)) := by
      rw [A.rank_eq_finrank_span_cols, Matrix.range_toLin']
    have hB : B.rank = Module.finrank K
        (LinearMap.range (Matrix.toLin' B)) := by
      rw [B.rank_eq_finrank_span_cols, Matrix.range_toLin']
    have hnull := (Matrix.toLin' A).finrank_range_add_finrank_ker
    have hdim : Module.finrank K (m → K) = Fintype.card m :=
      Module.finrank_fintype_fun_eq_card K
    have heq : Module.finrank K (LinearMap.range (Matrix.toLin' B)) =
        Module.finrank K (LinearMap.ker (Matrix.toLin' A)) := by
      omega
    exact (Submodule.eq_of_le_of_finrank_eq hle heq).symm

/-- Every minor one size larger than the rank of a finite-column matrix over a field
vanishes. -/
theorem minorIdeal_succ_rank_eq_bot
    {K : Type u} [Field K] {m n : Type v} [Fintype n]
    (A : Matrix m n K) :
    Matrix.minorIdeal A (A.rank + 1) = ⊥ := by
  apply le_antisymm
  · rw [Matrix.minorIdeal_le_iff]
    intro rows cols
    rw [Ideal.mem_bot]
    by_contra hdet
    have hle := Matrix.le_rank_of_minorDeterminant_ne_zero
      A (A.rank + 1) rows cols hdet
    omega
  · exact bot_le

namespace FiniteFreeComplex

variable {R : Type u} [CommRing R]

/-- Exactness at every positive homological degree through `N`.

With the indexing convention for `FiniteFreeComplex`, exactness at the term in degree
`i + 1` is exactness of `differential (i + 1)` followed by `differential i`. -/
def IsExactInPositiveDegreesUpTo (C : FiniteFreeComplex R) (N : ℕ) : Prop :=
  ∀ i : ℕ, i < N →
    Function.Exact
      (Matrix.toLin' (C.differential (i + 1)))
      (Matrix.toLin' (C.differential i))

/-- Matrix exactness is the corresponding exactness statement for the displayed maps of
the associated chain complex. -/
theorem isExactInPositiveDegreesUpTo_iff_toChainComplex
    (C : FiniteFreeComplex R) (N : ℕ) :
    C.IsExactInPositiveDegreesUpTo N ↔
      ∀ i : ℕ, i < N →
        Function.Exact
          (C.toChainComplex.d ((i + 1) + 1) (i + 1)).hom
          (C.toChainComplex.d (i + 1) i).hom := by
  constructor
  · intro h i hi
    rw [LinearMap.exact_iff]
    simpa only [toChainComplex_d] using
      (LinearMap.exact_iff.mp (h i hi))
  · intro h i hi
    have h' := h i hi
    rw [LinearMap.exact_iff] at h' ⊢
    simpa only [toChainComplex_d] using h'

/-- Boundedness above is preserved by coefficient extension. -/
theorem IsBoundedAbove.map
    {S : Type v} [CommRing S] {C : FiniteFreeComplex R} {N : ℕ}
    (h : C.IsBoundedAbove N) (f : R →+* S) :
    (C.map f).IsBoundedAbove N := by
  intro i hi
  exact h i hi

namespace ExpectedRanks

/-- The expected-rank recursion determines all ranks through the upper bound. -/
theorem rank_eq_of_le
    {C : FiniteFreeComplex R} {N : ℕ}
    (r s : C.ExpectedRanks N) {i : ℕ} (hi : i ≤ N) :
    r.rank i = s.rank i := by
  induction hi using Nat.decreasingInduction with
  | self => exact r.terminal.trans s.terminal.symm
  | of_succ i hi ih =>
    have hr := r.add_succ i hi
    have hs := s.add_succ i hi
    omega

end ExpectedRanks

section Field

variable {K : Type u} [Field K]

/-- Exactness at a displayed term gives the expected rank recurrence for its adjacent
differentials. -/
theorem rank_add_rank_eq_termRank_of_exact
    (C : FiniteFreeComplex K) {N : ℕ}
    (h : C.IsExactInPositiveDegreesUpTo N) (i : ℕ) (hi : i < N) :
    (C.differential i).rank + (C.differential (i + 1)).rank =
      C.termRank (i + 1) := by
  simpa only [Fintype.card_fin] using
    Matrix.rank_add_rank_eq_card_of_exact_toLin'
      (C.differential i) (C.differential (i + 1)) (h i hi)

/-- The actual differential ranks form an expected-rank function for an exact complex
that is zero above `N`. -/
def expectedRanksOfExact
    (C : FiniteFreeComplex K) (N : ℕ)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N) :
    C.ExpectedRanks N where
  rank i := (C.differential i).rank
  terminal := by
    have hle : (C.differential N).rank ≤ C.termRank (N + 1) :=
      (C.differential N).rank_le_width
    have hzero := hbounded (N + 1) (Nat.lt_succ_self N)
    omega
  add_succ i hi := C.rank_add_rank_eq_termRank_of_exact hexact i hi

@[simp]
theorem expectedRanksOfExact_rank
    (C : FiniteFreeComplex K) (N : ℕ)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N) (i : ℕ) :
    (C.expectedRanksOfExact N hbounded hexact).rank i =
      (C.differential i).rank :=
  rfl

/-- An exact bounded complex over a field satisfies its determinantal expected-rank
bounds. -/
theorem expectedRanksOfExact_hasExpectedRankBounds
    (C : FiniteFreeComplex K) (N : ℕ)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N) :
    C.HasExpectedRankBounds (C.expectedRanksOfExact N hbounded hexact) := by
  intro i hi
  exact Matrix.minorIdeal_succ_rank_eq_bot (C.differential i)

/-- Any prescribed expected-rank function agrees through `N` with the actual ranks of an
exact bounded complex over a field. -/
theorem ExpectedRanks.rank_eq_differential_of_exact
    {C : FiniteFreeComplex K} {N : ℕ}
    (r : C.ExpectedRanks N)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N)
    {i : ℕ} (hi : i ≤ N) :
    r.rank i = (C.differential i).rank := by
  exact r.rank_eq_of_le (C.expectedRanksOfExact N hbounded hexact) hi

/-- For a bounded finite free complex over a field, exactness through `N` is equivalent
to every displayed differential through `N` having its prescribed expected rank. -/
theorem isExactInPositiveDegreesUpTo_iff_rank_eq_expectedRank
    (C : FiniteFreeComplex K) (N : ℕ) (r : C.ExpectedRanks N)
    (hbounded : C.IsBoundedAbove N) :
    C.IsExactInPositiveDegreesUpTo N ↔
      ∀ i : ℕ, i ≤ N → (C.differential i).rank = r.rank i := by
  constructor
  · intro hexact i hi
    exact (r.rank_eq_differential_of_exact hbounded hexact hi).symm
  · intro hrank i hi
    apply (Matrix.exact_toLin'_iff_rank_add_rank_eq_card
      (C.differential i) (C.differential (i + 1))
      (C.differential_sq i)).mpr
    rw [hrank i (Nat.le_of_lt hi), hrank (i + 1) (by omega)]
    simpa only [Fintype.card_fin] using r.add_succ i hi

end Field

/-- Residue-field exactness through `N` is equivalent to equality between all fibre
matrix ranks and the prescribed expected ranks through `N`. -/
theorem isExactInPositiveDegreesUpTo_iff_rank_residueField_eq_expectedRank
    (C : FiniteFreeComplex R) (N : ℕ) (r : C.ExpectedRanks N)
    (hbounded : C.IsBoundedAbove N) (q : PrimeSpectrum R) :
    IsExactInPositiveDegreesUpTo
        (C.map (algebraMap R q.asIdeal.ResidueField)) N ↔
      ∀ i : ℕ, i ≤ N →
        ((C.differential i).map
          (algebraMap R q.asIdeal.ResidueField)).rank = r.rank i := by
  simpa only [map_differential, ExpectedRanks.map_rank] using
    (isExactInPositiveDegreesUpTo_iff_rank_eq_expectedRank
      (C.map (algebraMap R q.asIdeal.ResidueField)) N
      (r.map (algebraMap R q.asIdeal.ResidueField))
      (hbounded.map (algebraMap R q.asIdeal.ResidueField)))

/-- Exactness of a residue-field complex forces its actual matrix ranks to equal the
prescribed expected ranks through the upper bound. -/
theorem rank_residueField_eq_expectedRank_of_exact
    (C : FiniteFreeComplex R) {N : ℕ} (r : C.ExpectedRanks N)
    (hbounded : C.IsBoundedAbove N) (q : PrimeSpectrum R)
    (hexact : IsExactInPositiveDegreesUpTo
      (C.map (algebraMap R q.asIdeal.ResidueField)) N)
    {i : ℕ} (hi : i ≤ N) :
    ((C.differential i).map
      (algebraMap R q.asIdeal.ResidueField)).rank = r.rank i := by
  exact (C.isExactInPositiveDegreesUpTo_iff_rank_residueField_eq_expectedRank
    N r hbounded q).mp hexact i hi

end FiniteFreeComplex

end Matrix

end
