module

public import StacksAndModuli.API.DeterminantalGradeLocus
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Determinantal ideals detect lower bounds on fibre rank

A nonvanishing selected minor gives a lower bound on matrix rank.  Conversely, over a field,
a rank lower bound produces a square submatrix of the corresponding size with nonzero
determinant.  Applying both implications after coefficient change to the residue field of a
prime identifies the open complement of a determinantal zero locus exactly with the
corresponding fibre-rank locus.

These are the elementary rank implications used in the determinant-and-grade approach to
openness of exactness loci.

Main declarations:

* `Matrix.le_rank_of_minorDeterminant_ne_zero`;
* `Matrix.exists_minorDeterminant_ne_zero_of_le_rank`;
* `Matrix.exists_minorDeterminant_ne_zero_iff_le_rank`;
* `Matrix.rank_residueField_ge_of_mem_rankAtLeastLocus`;
* `Matrix.mem_rankAtLeastLocus_iff_rank_residueField_ge`;
* `Matrix.mem_zeroLocus_minorIdeal_iff_rank_residueField_lt`;
* `Matrix.minorIdeal_le_iff_rank_residueField_lt`;
* `Matrix.minorIdeal_map_atPrime_eq_top_iff_rank_residueField_ge`;
* `Matrix.rankAtLeastLocus_eq_fibreRankLocus`;
* `Matrix.zeroLocus_minorIdeal_eq_fibreRankDropLocus`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v w

namespace Matrix

variable {R : Type u} [CommRing R]
variable {m : Type v} {n : Type w} [Fintype n]

/-- A nonzero selected `r × r` minor gives the lower bound `r ≤ rank A`. -/
theorem le_rank_of_minorDeterminant_ne_zero
    {K : Type u} [Field K] (A : Matrix m n K) (r : ℕ)
    (rows : Fin r ↪ m) (cols : Fin r ↪ n)
    (h : (A.submatrix rows cols).det ≠ 0) :
    r ≤ A.rank := by
  have hrank : (A.submatrix rows cols).rank = r := by
    rw [Matrix.rank_of_det_ne_zero h, Fintype.card_fin]
  rw [← hrank]
  exact Matrix.rank_submatrix_le A rows cols

section FiniteRows

variable [Finite m]
local instance : Fintype m := Fintype.ofFinite m
variable {K : Type u} [Field K]

/-- A matrix of rank at least `r` has `r` linearly independent columns. -/
theorem exists_embedding_linearIndependent_cols_of_le_rank
    (A : Matrix m n K) {r : ℕ} (hr : r ≤ A.rank) :
    ∃ cols : Fin r ↪ n, LinearIndependent K (fun i ↦ A.col (cols i)) := by
  let s : Set (m → K) := Set.range A.col
  obtain ⟨f, hfmem, _, hfind⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K s
  have hr' : r ≤ Module.finrank K (Submodule.span K s) := by
    rw [← A.rank_eq_finrank_span_cols]
    exact hr
  let chooseCol (i : Fin (Module.finrank K (Submodule.span K s))) : n :=
    Classical.choose (hfmem i)
  have hchoose (i : Fin (Module.finrank K (Submodule.span K s))) :
      A.col (chooseCol i) = f i :=
    Classical.choose_spec (hfmem i)
  have hchooseInjective : Function.Injective chooseCol := by
    intro i j hij
    apply hfind.injective
    rw [← hchoose i, ← hchoose j, hij]
  let e : Fin r ↪ Fin (Module.finrank K (Submodule.span K s)) :=
    ⟨Fin.castLE hr', Fin.castLE_injective hr'⟩
  let cols : Fin r ↪ n := e.trans ⟨chooseCol, hchooseInjective⟩
  refine ⟨cols, ?_⟩
  have hcomp := hfind.comp (fun i : Fin r ↦ e i) e.injective
  have hfamily : (fun i : Fin r ↦ A.col (cols i)) = fun i ↦ f (e i) := by
    funext i
    exact hchoose (e i)
  rw [hfamily]
  convert hcomp using 1
  · rfl
  · rfl

omit [Finite m] in
/-- A matrix with `r` linearly independent columns has rank `r`. -/
theorem rank_eq_card_of_linearIndependent_cols
    {r : ℕ} (A : Matrix m (Fin r) K)
    (hA : LinearIndependent K A.col) :
    A.rank = r := by
  rw [A.rank_eq_finrank_span_cols,
    finrank_span_eq_card hA, Fintype.card_fin]

/-- The transpose of a matrix with `r` linearly independent columns has rank `r`. -/
theorem rank_transpose_eq_card_of_linearIndependent_cols
    {r : ℕ} (A : Matrix m (Fin r) K)
    (hA : LinearIndependent K A.col) :
    A.transpose.rank = r := by
  rw [Matrix.rank_transpose,
    rank_eq_card_of_linearIndependent_cols A hA]

/-- From `r` linearly independent columns, select `r` linearly independent rows. -/
theorem exists_embedding_linearIndependent_rows_of_linearIndependent_cols
    {r : ℕ} (A : Matrix m (Fin r) K)
    (hA : LinearIndependent K A.col) :
    ∃ rows : Fin r ↪ m,
      LinearIndependent K (fun i ↦ A.transpose.col (rows i)) := by
  apply exists_embedding_linearIndependent_cols_of_le_rank (A := A.transpose)
  exact (rank_transpose_eq_card_of_linearIndependent_cols A hA).ge

/-- From `r` linearly independent columns, select a square submatrix with nonzero
determinant. -/
theorem exists_rows_minorDeterminant_ne_zero_of_linearIndependent_cols
    {r : ℕ} (A : Matrix m (Fin r) K)
    (hA : LinearIndependent K A.col) :
    ∃ rows : Fin r ↪ m, (A.submatrix rows id).det ≠ 0 := by
  obtain ⟨rows, hrows⟩ :=
    exists_embedding_linearIndependent_rows_of_linearIndependent_cols A hA
  refine ⟨rows, ?_⟩
  let B : Matrix (Fin r) (Fin r) K := A.submatrix rows id
  have hBfamily : B.transpose.col = fun i ↦ A.transpose.col (rows i) := by
    funext i j
    rfl
  have hBtrans : LinearIndependent K B.transpose.col := by
    rw [hBfamily]
    exact hrows
  have hdet : B.transpose.det ≠ 0 :=
    Matrix.nonsingular_iff_det_ne_zero.mp
      (Matrix.Nonsingular.of_linearIndependent_col hBtrans)
  change B.det ≠ 0
  rw [← Matrix.det_transpose]
  exact hdet

/-- A matrix over a field whose rank is at least `r` has a nonzero selected `r × r`
minor. -/
theorem exists_minorDeterminant_ne_zero_of_le_rank
    (A : Matrix m n K) {r : ℕ} (hr : r ≤ A.rank) :
    ∃ (rows : Fin r ↪ m) (cols : Fin r ↪ n),
      (A.submatrix rows cols).det ≠ 0 := by
  obtain ⟨cols, hcols⟩ :=
    exists_embedding_linearIndependent_cols_of_le_rank A hr
  let C : Matrix m (Fin r) K := A.submatrix id cols
  have hCfamily : C.col = fun i ↦ A.col (cols i) := by
    funext i j
    rfl
  have hCcols : LinearIndependent K C.col := by
    rw [hCfamily]
    exact hcols
  obtain ⟨rows, hdet⟩ :=
    exists_rows_minorDeterminant_ne_zero_of_linearIndependent_cols C hCcols
  refine ⟨rows, cols, ?_⟩
  convert hdet using 1
  rfl

/-- Over a field, the existence of a nonzero selected `r × r` minor is equivalent to
the rank lower bound `r ≤ A.rank`. -/
theorem exists_minorDeterminant_ne_zero_iff_le_rank
    (A : Matrix m n K) (r : ℕ) :
    (∃ (rows : Fin r ↪ m) (cols : Fin r ↪ n),
      (A.submatrix rows cols).det ≠ 0) ↔ r ≤ A.rank := by
  constructor
  · rintro ⟨rows, cols, hdet⟩
    exact le_rank_of_minorDeterminant_ne_zero A r rows cols hdet
  · exact exists_minorDeterminant_ne_zero_of_le_rank A

end FiniteRows

/-- On the open rank-at-least locus, the matrix over the residue field has rank at least
the prescribed minor size. -/
theorem rank_residueField_ge_of_mem_rankAtLeastLocus
    (A : Matrix m n R) (r : ℕ) (p : PrimeSpectrum R)
    (hp : p ∈ rankAtLeastLocus A r) :
    r ≤ (A.map (algebraMap R p.asIdeal.ResidueField)).rank := by
  obtain ⟨rows, cols, hminor⟩ := (mem_rankAtLeastLocus_iff A r p).mp hp
  refine le_rank_of_minorDeterminant_ne_zero
    (A := A.map (algebraMap R p.asIdeal.ResidueField)) r rows cols ?_
  change ((A.submatrix rows cols).map
    (algebraMap R p.asIdeal.ResidueField)).det ≠ 0
  change ((algebraMap R p.asIdeal.ResidueField).mapMatrix
    (A.submatrix rows cols)).det ≠ 0
  rw [← RingHom.map_det]
  intro hz
  exact hminor (Ideal.algebraMap_residueField_eq_zero.mp hz)

section FiniteRowsResidue

variable [Finite m]

/-- The nonvanishing-minor locus is exactly the locus on which the residue-field matrix
has rank at least `r`. -/
theorem mem_rankAtLeastLocus_iff_rank_residueField_ge
    (A : Matrix m n R) (r : ℕ) (p : PrimeSpectrum R) :
    p ∈ rankAtLeastLocus A r ↔
      r ≤ (A.map (algebraMap R p.asIdeal.ResidueField)).rank := by
  constructor
  · exact rank_residueField_ge_of_mem_rankAtLeastLocus A r p
  · intro hrank
    rw [mem_rankAtLeastLocus_iff]
    obtain ⟨rows, cols, hdet⟩ :=
      exists_minorDeterminant_ne_zero_of_le_rank
        (A.map (algebraMap R p.asIdeal.ResidueField)) hrank
    refine ⟨rows, cols, ?_⟩
    intro hmem
    apply hdet
    change ((A.submatrix rows cols).map
      (algebraMap R p.asIdeal.ResidueField)).det = 0
    change ((algebraMap R p.asIdeal.ResidueField).mapMatrix
      (A.submatrix rows cols)).det = 0
    rw [← RingHom.map_det]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hmem

/-- The determinantal zero locus is exactly the locus on which the residue-field matrix
has rank strictly smaller than `r`. -/
theorem mem_zeroLocus_minorIdeal_iff_rank_residueField_lt
    (A : Matrix m n R) (r : ℕ) (p : PrimeSpectrum R) :
    p ∈ PrimeSpectrum.zeroLocus (minorIdeal A r : Set R) ↔
      (A.map (algebraMap R p.asIdeal.ResidueField)).rank < r := by
  rw [← not_iff_not]
  change p ∈ rankAtLeastLocus A r ↔
    ¬ (A.map (algebraMap R p.asIdeal.ResidueField)).rank < r
  simpa only [not_lt] using
    mem_rankAtLeastLocus_iff_rank_residueField_ge A r p

/-- A prime contains the `r`-minor ideal exactly when the residue-field matrix has rank
strictly smaller than `r`. -/
theorem minorIdeal_le_iff_rank_residueField_lt
    (A : Matrix m n R) (r : ℕ) (p : PrimeSpectrum R) :
    minorIdeal A r ≤ p.asIdeal ↔
      (A.map (algebraMap R p.asIdeal.ResidueField)).rank < r := by
  change (minorIdeal A r : Set R) ⊆ (p.asIdeal : Set R) ↔
    (A.map (algebraMap R p.asIdeal.ResidueField)).rank < r
  rw [← PrimeSpectrum.mem_zeroLocus]
  exact mem_zeroLocus_minorIdeal_iff_rank_residueField_lt A r p

/-- After localization at a prime, the `r`-minor ideal is the unit ideal exactly when the
residue-field matrix has rank at least `r`. -/
theorem minorIdeal_map_atPrime_eq_top_iff_rank_residueField_ge
    (A : Matrix m n R) (r : ℕ) (p : PrimeSpectrum R) :
    minorIdeal
        (A.map (algebraMap R (Localization.AtPrime p.asIdeal))) r = ⊤ ↔
      r ≤ (A.map (algebraMap R p.asIdeal.ResidueField)).rank := by
  exact (minorIdeal_map_atPrime_eq_top_iff A r p.asIdeal).trans
    ((mem_rankAtLeastLocus_iff A r p).symm.trans
      (mem_rankAtLeastLocus_iff_rank_residueField_ge A r p))

/-- The determinantal open is literally the residue-field rank-at-least locus. -/
theorem rankAtLeastLocus_eq_fibreRankLocus (A : Matrix m n R) (r : ℕ) :
    rankAtLeastLocus A r =
      {p | r ≤ (A.map (algebraMap R p.asIdeal.ResidueField)).rank} := by
  ext p
  exact mem_rankAtLeastLocus_iff_rank_residueField_ge A r p

/-- The zero locus of the `r`-minor ideal is literally the residue-field rank-drop
locus. -/
theorem zeroLocus_minorIdeal_eq_fibreRankDropLocus
    (A : Matrix m n R) (r : ℕ) :
    PrimeSpectrum.zeroLocus (minorIdeal A r : Set R) =
      {p | (A.map (algebraMap R p.asIdeal.ResidueField)).rank < r} := by
  ext p
  exact mem_zeroLocus_minorIdeal_iff_rank_residueField_lt A r p

end FiniteRowsResidue

/-- If the residue-field matrix has rank smaller than `r`, then every `r × r` minor lies
in the prime. -/
theorem mem_zeroLocus_minorIdeal_of_rank_residueField_lt
    (A : Matrix m n R) (r : ℕ) (p : PrimeSpectrum R)
    (hp : (A.map (algebraMap R p.asIdeal.ResidueField)).rank < r) :
    p ∈ PrimeSpectrum.zeroLocus (minorIdeal A r : Set R) := by
  by_contra hnot
  have hge := rank_residueField_ge_of_mem_rankAtLeastLocus A r p hnot
  omega

/-- The ideal formulation of
`Matrix.mem_zeroLocus_minorIdeal_of_rank_residueField_lt`. -/
theorem minorIdeal_le_of_rank_residueField_lt
    (A : Matrix m n R) (r : ℕ) (p : PrimeSpectrum R)
    (hp : (A.map (algebraMap R p.asIdeal.ResidueField)).rank < r) :
    minorIdeal A r ≤ p.asIdeal := by
  rw [minorIdeal_le_iff]
  exact (mem_zeroLocus_minorIdeal_iff A r p).mp
    (mem_zeroLocus_minorIdeal_of_rank_residueField_lt A r p hp)

end Matrix

end

end
