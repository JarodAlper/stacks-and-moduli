module

public import StacksAndModuli.API.FiniteFreeComplexBuchsbaumEisenbudMinimal
public import StacksAndModuli.API.FiniteFreeComplexBuchsbaumEisenbudLengthOne
public import Mathlib.RingTheory.LocalRing.Module
public import StacksProject.Algebra.ColimitsAndMapsOfFinitePresentationII.«lemma-flat-finite-presentation-limit-flat»

/-!
# Cancelling the top unit-minor summand of a finite free complex

This file supplies the matrix algebra used in the unit-ideal branch of the local
Buchsbaum--Eisenbud induction.  If the highest differential has unit ideal of maximal
column minors, it is split injective over a local ring.  Its free cokernel replaces the
next term of the complex and shortens the complex by one.

The determinantal transport needed for the shortened complex is one-sided.  If
`A = B * Q` and the middle index is `Fin r`, every `r`-minor of `A` is the product of an
`r`-minor of `B` and an `r`-minor of `Q`.  Thus the old minor ideal is contained in the
new one; equality and a general Cauchy--Binet formula are unnecessary.

Main declarations:

* `Matrix.minorIdeal_mul_le_left_of_middle_fin`;
* `Matrix.minorIdeal_mul_le_right_of_middle_fin`;
* `Matrix.lTensor_toLin'_injective_of_minorIdeal_card_cols_eq_top`;
* `Matrix.FiniteFreeComplex.exists_unitCancellation`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v w

open Function IsLocalRing LinearMap Module

namespace Matrix

variable {R : Type u} [CommRing R]

/-- When the middle index has exactly `r` elements, every `r`-minor of a matrix
product belongs to the `r`-minor ideal of the left factor. -/
theorem minorIdeal_mul_le_left_of_middle_fin
    {m : Type v} {n : Type w}
    (A : Matrix m (Fin r) R) (B : Matrix (Fin r) n R) :
    minorIdeal (A * B) r ≤ minorIdeal A r := by
  rw [minorIdeal_le_iff]
  intro rows cols
  let e : Fin r ≃ Fin r := Equiv.refl _
  rw [Matrix.submatrix_mul A B rows e cols e.bijective, Matrix.det_mul]
  exact (minorIdeal A r).mul_mem_right _
    (minorDeterminant_mem_minorIdeal A r rows e.toEmbedding)

/-- When the middle index has exactly `r` elements, every `r`-minor of a matrix
product belongs to the `r`-minor ideal of the right factor. -/
theorem minorIdeal_mul_le_right_of_middle_fin
    {m : Type v} {n : Type w}
    (A : Matrix m (Fin r) R) (B : Matrix (Fin r) n R) :
    minorIdeal (A * B) r ≤ minorIdeal B r := by
  rw [minorIdeal_le_iff]
  intro rows cols
  let e : Fin r ≃ Fin r := Equiv.refl _
  rw [Matrix.submatrix_mul A B rows e cols e.bijective, Matrix.det_mul]
  exact (minorIdeal B r).mul_mem_left _
    (minorDeterminant_mem_minorIdeal B r e.toEmbedding cols)

/-- A matrix with `r` columns has no nonzero minors of size `r + 1`. -/
theorem minorIdeal_succ_card_cols_eq_bot
    {m : Type v} (A : Matrix m (Fin r) R) :
    minorIdeal A (r + 1) = ⊥ := by
  apply le_antisymm
  · rw [minorIdeal_le_iff]
    intro _ cols
    have hcard := Fintype.card_le_of_embedding cols
    simp only [Fintype.card_fin] at hcard
    omega
  · exact bot_le

/-- Under the standard finite-free base-change equivalences, injectivity of the
coefficientwise-mapped matrix implies injectivity of the tensor-extended linear map. -/
theorem lTensor_toLin'_injective_of_map_injective
    {S : Type u} [CommRing S] [Algebra R S]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (h : Function.Injective
      (Matrix.toLin' (A.map (algebraMap R S)))) :
    Function.Injective ((Matrix.toLin' A).lTensor S) := by
  let eM := TensorProduct.piScalarRight R S S (Fin n)
  let eN := TensorProduct.piScalarRight R S S (Fin m)
  have hcomm := Matrix.piScalarRight_toLin_map (A := S) A
  have hbase : Function.Injective ((Matrix.toLin' A).baseChange S) := by
    intro x y hxy
    apply eM.injective
    apply h
    calc
      Matrix.toLin' (A.map (algebraMap R S)) (eM x) =
          eN (((Matrix.toLin' A).baseChange S) x) :=
        (LinearMap.congr_fun hcomm x).symm
      _ = eN (((Matrix.toLin' A).baseChange S) y) := by rw [hxy]
      _ = Matrix.toLin' (A.map (algebraMap R S)) (eM y) :=
        LinearMap.congr_fun hcomm y
  simpa only [LinearMap.baseChange_eq_ltensor] using hbase

/-- Unit ideal of maximal column minors makes every scalar extension of the matrix
injective.  This is the tensor form needed by the local split-injection criterion. -/
theorem lTensor_toLin'_injective_of_minorIdeal_card_cols_eq_top
    {S : Type u} [CommRing S] [Algebra R S]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (hminor : minorIdeal A n = ⊤) :
    Function.Injective ((Matrix.toLin' A).lTensor S) := by
  have hminorMap :
      minorIdeal (A.map (algebraMap R S)) n = ⊤ := by
    rw [minorIdeal_map, hminor, Ideal.map_top]
  apply lTensor_toLin'_injective_of_map_injective A
  exact toLin'_injective_of_isSMulRegular_mem_minorIdeal_card_cols
    (A.map (algebraMap R S)) 1
      ((Ideal.eq_top_iff_one _).mp hminorMap) isRegular_one.isSMulRegular

/-- Unit ideal of maximal column minors makes the original matrix injective. -/
theorem toLin'_injective_of_minorIdeal_card_cols_eq_top
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (hminor : minorIdeal A n = ⊤) :
    Function.Injective (Matrix.toLin' A) := by
  exact toLin'_injective_of_isSMulRegular_mem_minorIdeal_card_cols
    A 1 ((Ideal.eq_top_iff_one _).mp hminor) isRegular_one.isSMulRegular

/-- Transporting the two finite index cardinalities of a matrix does not change its
determinantal ideals. -/
theorem minorIdeal_eq_mpr_fin
    {m n m' n' t : ℕ} (hm : m' = m) (hn : n' = n)
    (A : Matrix (Fin m) (Fin n) R) :
    minorIdeal
        (Eq.mpr (show Matrix (Fin m') (Fin n') R =
          Matrix (Fin m) (Fin n) R by rw [hm, hn]) A) t =
      minorIdeal A t := by
  subst m'
  subst n'
  rfl

/-- Transporting the three finite ranks in a pair of consecutive matrices does not
change exactness of their associated linear maps. -/
theorem exact_toLin'_eq_mpr_fin_iff
    {a b c a' b' c' : ℕ}
    (ha : a' = a) (hb : b' = b) (hc : c' = c)
    (A : Matrix (Fin b) (Fin c) R)
    (B : Matrix (Fin a) (Fin b) R) :
    Function.Exact
        (Matrix.toLin'
          (Eq.mpr (show Matrix (Fin b') (Fin c') R =
            Matrix (Fin b) (Fin c) R by rw [hb, hc]) A))
        (Matrix.toLin'
          (Eq.mpr (show Matrix (Fin a') (Fin b') R =
            Matrix (Fin a) (Fin b) R by rw [ha, hb]) B)) ↔
      Function.Exact (Matrix.toLin' A) (Matrix.toLin' B) := by
  subst a'
  subst b'
  subst c'
  rfl

/-- Transporting the three finite ranks in a composable pair of matrices preserves
the assertion that their product is zero. -/
theorem eq_mpr_mul_eq_zero_iff
    {a b c a' b' c' : ℕ}
    (ha : a' = a) (hb : b' = b) (hc : c' = c)
    (A : Matrix (Fin a) (Fin b) R)
    (B : Matrix (Fin b) (Fin c) R) :
    Eq.mpr (show Matrix (Fin a') (Fin b') R =
        Matrix (Fin a) (Fin b) R by rw [ha, hb]) A *
      Eq.mpr (show Matrix (Fin b') (Fin c') R =
        Matrix (Fin b) (Fin c) R by rw [hb, hc]) B = 0 ↔
      A * B = 0 := by
  subst a'
  subst b'
  subst c'
  rfl

/-- Transporting the finite row and column ranks of a matrix preserves injectivity of
its associated linear map. -/
theorem toLin'_eq_mpr_injective_iff
    {m n m' n' : ℕ} (hm : m' = m) (hn : n' = n)
    (A : Matrix (Fin m) (Fin n) R) :
    Function.Injective
        (Matrix.toLin'
          (Eq.mpr (show Matrix (Fin m') (Fin n') R =
            Matrix (Fin m) (Fin n) R by rw [hm, hn]) A)) ↔
      Function.Injective (Matrix.toLin' A) := by
  subst m'
  subst n'
  rfl

namespace FiniteFreeComplex

/-- Term ranks for a complex obtained by retaining the terms through degree `N`,
putting a new rank-`r` term in degree `N + 1`, and setting all higher terms to zero. -/
def shortenedTermRank (C : FiniteFreeComplex R) (N r i : ℕ) : ℕ :=
  if i ≤ N then C.termRank i else if i = N + 1 then r else 0

/-- Differentials for top shortening: keep the differentials below `N`, use `B` in
degree `N`, and use zero above it. -/
def shortenedDifferential (C : FiniteFreeComplex R) (N r : ℕ)
    (B : Matrix (Fin (C.termRank N)) (Fin r) R) (i : ℕ) :
    Matrix (Fin (C.shortenedTermRank N r i))
      (Fin (C.shortenedTermRank N r (i + 1))) R := by
  classical
  by_cases hi : i < N
  · simpa [shortenedTermRank, Nat.le_of_lt hi,
      Nat.succ_le_iff.mpr hi] using C.differential i
  · by_cases hiN : i = N
    · subst i
      simpa [shortenedTermRank] using B
    · exact 0

/-- Every differential strictly above the shortening degree is zero. -/
theorem shortenedDifferential_eq_zero_of_lt (C : FiniteFreeComplex R) (N r : ℕ)
    (B : Matrix (Fin (C.termRank N)) (Fin r) R) {i : ℕ} (hi : N < i) :
    C.shortenedDifferential N r B i = 0 := by
  simp [shortenedDifferential, show ¬ i < N by omega,
    show i ≠ N by omega]

/-- Reindexing below the shortening degree does not change a determinantal ideal. -/
theorem minorIdeal_shortenedDifferential_of_lt (C : FiniteFreeComplex R) (N r t : ℕ)
    (B : Matrix (Fin (C.termRank N)) (Fin r) R) {i : ℕ} (hi : i < N) :
    minorIdeal (C.shortenedDifferential N r B i) t =
      minorIdeal (C.differential i) t := by
  have hrow : C.shortenedTermRank N r i = C.termRank i := by
    simp [shortenedTermRank, Nat.le_of_lt hi]
  have hcol : C.shortenedTermRank N r (i + 1) = C.termRank (i + 1) := by
    simp [shortenedTermRank, Nat.succ_le_iff.mpr hi]
  simp only [shortenedDifferential, hi, ↓reduceDIte]
  simpa only using Matrix.minorIdeal_eq_mpr_fin hrow hcol (C.differential i)

/-- Reindexing at the shortening degree does not change a determinantal ideal. -/
theorem minorIdeal_shortenedDifferential_self (C : FiniteFreeComplex R) (N r t : ℕ)
    (B : Matrix (Fin (C.termRank N)) (Fin r) R) :
    minorIdeal (C.shortenedDifferential N r B N) t = minorIdeal B t := by
  have hrow : C.shortenedTermRank N r N = C.termRank N := by
    simp [shortenedTermRank]
  have hcol : C.shortenedTermRank N r (N + 1) = r := by
    simp [shortenedTermRank]
  simp only [shortenedDifferential, lt_self_iff_false, ↓reduceDIte]
  simpa only using Matrix.minorIdeal_eq_mpr_fin hrow hcol B

/-- Exactness at a degree whose two differentials lie below the shortening degree is
unchanged. -/
theorem exact_shortenedDifferential_iff_of_lt (C : FiniteFreeComplex R) (N r : ℕ)
    (B : Matrix (Fin (C.termRank N)) (Fin r) R) {i : ℕ}
    (hi : i < N) (hi' : i + 1 < N) :
    Function.Exact
        (Matrix.toLin' (C.shortenedDifferential N r B (i + 1)))
        (Matrix.toLin' (C.shortenedDifferential N r B i)) ↔
      Function.Exact
        (Matrix.toLin' (C.differential (i + 1)))
        (Matrix.toLin' (C.differential i)) := by
  have h₀ : C.shortenedTermRank N r i = C.termRank i := by
    simp [shortenedTermRank, Nat.le_of_lt hi]
  have h₁ : C.shortenedTermRank N r (i + 1) = C.termRank (i + 1) := by
    simp [shortenedTermRank, Nat.le_of_lt hi']
  have h₂ : C.shortenedTermRank N r (i + 2) = C.termRank (i + 2) := by
    have : i + 1 + 1 = i + 2 := by omega
    rw [← this]
    simp [shortenedTermRank, Nat.succ_le_iff.mpr hi']
  simp only [shortenedDifferential, hi, hi', ↓reduceDIte]
  simpa only using Matrix.exact_toLin'_eq_mpr_fin_iff h₀ h₁ h₂
    (C.differential (i + 1)) (C.differential i)

/-- Exactness at the new top boundary is exactness of `B` followed by the last
unchanged differential. -/
theorem exact_shortenedDifferential_succ_top_iff (C : FiniteFreeComplex R) (i r : ℕ)
    (B : Matrix (Fin (C.termRank (i + 1))) (Fin r) R) :
    Function.Exact
        (Matrix.toLin' (C.shortenedDifferential (i + 1) r B (i + 1)))
        (Matrix.toLin' (C.shortenedDifferential (i + 1) r B i)) ↔
      Function.Exact (Matrix.toLin' B) (Matrix.toLin' (C.differential i)) := by
  have h₀ : C.shortenedTermRank (i + 1) r i = C.termRank i := by
    simp [shortenedTermRank]
  have h₁ : C.shortenedTermRank (i + 1) r (i + 1) =
      C.termRank (i + 1) := by
    simp [shortenedTermRank]
  have h₂ : C.shortenedTermRank (i + 1) r (i + 2) = r := by
    simp [shortenedTermRank]
  simp only [shortenedDifferential, Nat.lt_succ_self, lt_self_iff_false,
    ↓reduceDIte]
  simpa only using Matrix.exact_toLin'_eq_mpr_fin_iff h₀ h₁ h₂ B
    (C.differential i)

/-- Build the shortened matrix complex once the single boundary square involving the
new top differential has been checked. -/
def shortenTop (C : FiniteFreeComplex R) (N r : ℕ)
    (B : Matrix (Fin (C.termRank N)) (Fin r) R)
    (hsq : ∀ i : ℕ,
      C.shortenedDifferential N r B i *
        C.shortenedDifferential N r B (i + 1) = 0) :
    FiniteFreeComplex R where
  termRank := C.shortenedTermRank N r
  differential := C.shortenedDifferential N r B
  differential_sq := hsq

@[simp]
theorem shortenTop_termRank (C : FiniteFreeComplex R) (N r : ℕ)
    (B : Matrix (Fin (C.termRank N)) (Fin r) R)
    (hsq) (i : ℕ) :
    (C.shortenTop N r B hsq).termRank i = C.shortenedTermRank N r i :=
  rfl

@[simp]
theorem shortenTop_differential (C : FiniteFreeComplex R) (N r : ℕ)
    (B : Matrix (Fin (C.termRank N)) (Fin r) R)
    (hsq) (i : ℕ) :
    (C.shortenTop N r B hsq).differential i =
      C.shortenedDifferential N r B i :=
  rfl

/-- Cancel the highest differential when its expected maximal-column minors generate
the unit ideal.  The replacement complex is one term shorter.  Expected-rank bounds
and Buchsbaum--Eisenbud grade pass to it, and its exactness implies exactness of the
original complex.

This is the specialized top-degree cancellation needed in the length induction for
the local Buchsbaum--Eisenbud criterion. -/
theorem exists_unitCancellation [IsLocalRing R]
    (C : FiniteFreeComplex R) (N : ℕ) (r : C.ExpectedRanks (N + 2))
    (hbounded : C.IsBoundedAbove (N + 2))
    (htop : minorIdeal (C.differential (N + 1)) (r.rank (N + 1)) = ⊤) :
    ∃ (D : FiniteFreeComplex R) (s : D.ExpectedRanks (N + 1)),
      D.IsBoundedAbove (N + 1) ∧
      (C.HasExpectedRankBounds r → D.HasExpectedRankBounds s) ∧
      (C.HasBuchsbaumEisenbudGrade r → D.HasBuchsbaumEisenbudGrade s) ∧
      (D.IsExactInPositiveDegreesUpTo (N + 1) →
        C.IsExactInPositiveDegreesUpTo (N + 2)) := by
  let f := Matrix.toLin' (C.differential (N + 1))
  let g := Matrix.toLin' (C.differential N)
  have hrTop : r.rank (N + 1) = C.termRank (N + 2) := by
    have hadd : r.rank (N + 1) + r.rank (N + 2) =
        C.termRank (N + 2) := by
      simpa only [show N + 1 + 1 = N + 2 by omega] using
        r.add_succ (N + 1) (by omega)
    simpa only [r.terminal, Nat.add_zero] using hadd
  have htop' : minorIdeal (C.differential (N + 1))
      (C.termRank (N + 2)) = ⊤ := by
    simpa only [hrTop] using htop
  have hf : Function.Injective f := by
    exact Matrix.toLin'_injective_of_minorIdeal_card_cols_eq_top
      (C.differential (N + 1)) htop'
  have hfTensor : Function.Injective
      (f.lTensor (ResidueField R)) := by
    exact Matrix.lTensor_toLin'_injective_of_minorIdeal_card_cols_eq_top
      (S := ResidueField R) (C.differential (N + 1)) htop'
  obtain ⟨σ, hσ⟩ :=
    (IsLocalRing.split_injective_iff_lTensor_residueField_injective f).mpr hfTensor
  let W := (Fin (C.termRank (N + 1)) → R) ⧸ LinearMap.range f
  let q : (Fin (C.termRank (N + 1)) → R) →ₗ[R] W :=
    (LinearMap.range f).mkQ
  have hq : Function.Surjective q :=
    Submodule.mkQ_surjective (LinearMap.range f)
  have hfg : LinearMap.range f ≤ LinearMap.ker g := by
    rw [LinearMap.range_le_ker_iff]
    exact C.differential_comp N
  let gbar : W →ₗ[R] (Fin (C.termRank N) → R) :=
    (LinearMap.range f).liftQ g hfg
  letI : Module.Finite R W := Module.Finite.of_surjective q hq
  letI : Module.Free R W :=
    Module.free_of_lTensor_residueField_injective f q hq
      f.exact_map_mkQ_range hfTensor
  let eSplit : (Fin (C.termRank (N + 1)) → R) ≃ₗ[R]
      (Fin (C.termRank (N + 2)) → R) × W :=
    ((f.exact_map_mkQ_range.splitInjectiveEquiv hq)
      ⟨σ, hσ⟩).1
  have heSplitRank := eSplit.finrank_eq
  have hrNext := r.add_succ N (by omega)
  have hWrank : Module.finrank R W = r.rank N := by
    rw [Module.finrank_pi, Fintype.card_fin, Module.finrank_prod,
      Module.finrank_pi, Fintype.card_fin] at heSplitRank
    omega
  let bW : Basis (Fin (r.rank N)) R W :=
    Module.finBasisOfFinrankEq R W hWrank
  let eW : (Fin (r.rank N) → R) ≃ₗ[R] W := bW.equivFun.symm
  let B : Matrix (Fin (C.termRank N)) (Fin (r.rank N)) R :=
    LinearMap.toMatrix' (gbar.comp eW.toLinearMap)
  let Q : Matrix (Fin (r.rank N)) (Fin (C.termRank (N + 1))) R :=
    LinearMap.toMatrix' (eW.symm.toLinearMap.comp q)
  have hfactorLin : g = (Matrix.toLin' B).comp (Matrix.toLin' Q) := by
    apply LinearMap.ext
    intro x
    simp only [B, Q, Matrix.toLin'_toMatrix', LinearMap.comp_apply,
      LinearEquiv.coe_coe]
    rw [eW.apply_symm_apply]
    exact (Submodule.liftQ_apply (LinearMap.range f) g x).symm
  have hfactor : C.differential N = B * Q := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul]
    exact hfactorLin
  have hsq : ∀ i : ℕ,
      C.shortenedDifferential N (r.rank N) B i *
        C.shortenedDifferential N (r.rank N) B (i + 1) = 0 := by
    intro i
    cases N with
    | zero =>
        have hz := C.shortenedDifferential_eq_zero_of_lt 0 (r.rank 0) B
          (i := i + 1) (by omega)
        rw [hz, Matrix.mul_zero]
    | succ k =>
        by_cases hik : i < k
        · have hi₀ : i < k + 1 := by omega
          have hi₁ : i + 1 < k + 1 := by omega
          have h₀ : C.shortenedTermRank (k + 1) (r.rank (k + 1)) i =
              C.termRank i := by
            simp [shortenedTermRank, Nat.le_of_lt hi₀]
          have h₁ : C.shortenedTermRank (k + 1) (r.rank (k + 1)) (i + 1) =
              C.termRank (i + 1) := by
            simp [shortenedTermRank, Nat.le_of_lt hi₁]
          have h₂ : C.shortenedTermRank (k + 1) (r.rank (k + 1)) (i + 2) =
              C.termRank (i + 2) := by
            have : i + 1 + 1 = i + 2 := by omega
            rw [← this]
            simp [shortenedTermRank, Nat.succ_le_iff.mpr hi₁]
          simp only [shortenedDifferential, hi₀, hi₁, ↓reduceDIte]
          exact (Matrix.eq_mpr_mul_eq_zero_iff h₀ h₁ h₂
            (C.differential i) (C.differential (i + 1))).mpr
              (C.differential_sq i)
        · by_cases hik' : i = k
          · subst i
            have hCB : C.differential k * B = 0 := by
              apply Matrix.toLin'.injective
              rw [Matrix.toLin'_mul]
              simp only [B, Matrix.toLin'_toMatrix']
              apply LinearMap.ext
              intro x
              simp only [LinearMap.comp_apply, map_zero, LinearMap.zero_apply]
              obtain ⟨y, hy⟩ := hq (eW x)
              have hzero := LinearMap.congr_fun (C.differential_comp k) y
              have hgbarq : gbar (q y) = g y := by
                change (LinearMap.range f).liftQ g hfg
                    ((LinearMap.range f).mkQ y) = g y
                exact Submodule.liftQ_apply (LinearMap.range f) g y
              calc
                Matrix.toLin' (C.differential k) (gbar (eW x)) =
                    Matrix.toLin' (C.differential k) (gbar (q y)) :=
                  congrArg _ (congrArg gbar hy.symm)
                _ = Matrix.toLin' (C.differential k) (g y) := by
                  rw [hgbarq]
                _ = 0 := by
                  simpa only [g, LinearMap.comp_apply, LinearMap.zero_apply] using hzero
            have h₀ : C.shortenedTermRank (k + 1) (r.rank (k + 1)) k =
                C.termRank k := by
              simp [shortenedTermRank]
            have h₁ : C.shortenedTermRank (k + 1) (r.rank (k + 1)) (k + 1) =
                C.termRank (k + 1) := by
              simp [shortenedTermRank]
            have h₂ : C.shortenedTermRank (k + 1) (r.rank (k + 1)) (k + 2) =
                r.rank (k + 1) := by
              simp [shortenedTermRank]
            simp only [shortenedDifferential, Nat.lt_succ_self,
              lt_self_iff_false, ↓reduceDIte]
            exact (Matrix.eq_mpr_mul_eq_zero_iff h₀ h₁ h₂
              (C.differential k) B).mpr hCB
          · have hki : k < i := by omega
            have hz := C.shortenedDifferential_eq_zero_of_lt (k + 1)
              (r.rank (k + 1)) B (i := i + 1) (by omega)
            rw [hz, Matrix.mul_zero]
  let D : FiniteFreeComplex R :=
    C.shortenTop N (r.rank N) B hsq
  let s : D.ExpectedRanks (N + 1) :=
    { rank := fun i ↦ if i ≤ N then r.rank i else 0
      terminal := by simp
      add_succ := by
        intro i hi
        by_cases hiN : i < N
        · change (if i ≤ N then r.rank i else 0) +
              (if i + 1 ≤ N then r.rank (i + 1) else 0) =
              C.shortenedTermRank N (r.rank N) (i + 1)
          simpa [shortenedTermRank, Nat.le_of_lt hiN,
            Nat.succ_le_iff.mpr hiN] using r.add_succ i (by omega)
        · have hiEq : i = N := by omega
          subst i
          change (if N ≤ N then r.rank N else 0) +
              (if N + 1 ≤ N then r.rank (N + 1) else 0) =
              C.shortenedTermRank N (r.rank N) (N + 1)
          simp [shortenedTermRank] }
  refine ⟨D, s, ?_, ?_, ?_, ?_⟩
  · intro i hi
    change C.shortenedTermRank N (r.rank N) i = 0
    simp [shortenedTermRank, show ¬ i ≤ N by omega,
      show i ≠ N + 1 by omega]
  · intro hbounds i hi
    by_cases hiN : i < N
    · have h := hbounds i (by omega)
      simpa only [D, s, shortenTop, if_pos (Nat.le_of_lt hiN),
        C.minorIdeal_shortenedDifferential_of_lt N (r.rank N)
          (r.rank i + 1) B hiN] using h
    · have hiEq : i = N := by omega
      subst i
      have hB := Matrix.minorIdeal_succ_card_cols_eq_bot B
      simpa only [D, s, shortenTop, if_pos le_rfl,
        C.minorIdeal_shortenedDifferential_self N (r.rank N)
          (r.rank N + 1) B] using hB
  · intro hgrade i hi
    by_cases hiN : i < N
    · have h := hgrade i (by omega)
      simpa only [D, s, shortenTop, if_pos (Nat.le_of_lt hiN),
        C.minorIdeal_shortenedDifferential_of_lt N (r.rank N)
          (r.rank i) B hiN] using h
    · have hiEq : i = N := by omega
      subst i
      have h := hgrade N (by omega)
      change minorIdeal (C.differential N) (r.rank N) = ⊤ ∨
          ∃ z : Fin (N + 1) → R,
            (∀ j, z j ∈ minorIdeal (C.differential N) (r.rank N)) ∧
              RingTheory.Sequence.IsRegular R (List.ofFn z) at h
      have hle : minorIdeal (C.differential N) (r.rank N) ≤
          minorIdeal B (r.rank N) := by
        calc
          minorIdeal (C.differential N) (r.rank N) =
              minorIdeal (B * Q) (r.rank N) :=
            congrArg (fun A ↦ minorIdeal A (r.rank N)) hfactor
          _ ≤ minorIdeal B (r.rank N) :=
            Matrix.minorIdeal_mul_le_left_of_middle_fin B Q
      have hBgrade : minorIdeal B (r.rank N) = ⊤ ∨
          ∃ z : Fin (N + 1) → R,
            (∀ j, z j ∈ minorIdeal B (r.rank N)) ∧
              RingTheory.Sequence.IsRegular R (List.ofFn z) := by
        rcases h with htopN | ⟨z, hz, hreg⟩
        · left
          exact top_unique (htopN ▸ hle)
        · exact Or.inr ⟨z, fun j ↦ hle (hz j), hreg⟩
      simpa only [D, s, shortenTop, if_pos le_rfl,
        C.minorIdeal_shortenedDifferential_self N (r.rank N)
          (r.rank N) B] using hBgrade
  · intro hD i hi
    by_cases hiN : i < N
    · by_cases hiN' : i + 1 < N
      · have h := hD i (by omega)
        have hshort : Function.Exact
            (Matrix.toLin'
              (C.shortenedDifferential N (r.rank N) B (i + 1)))
            (Matrix.toLin'
              (C.shortenedDifferential N (r.rank N) B i)) := by
          simpa only [D, shortenTop] using h
        exact (C.exact_shortenedDifferential_iff_of_lt
          N (r.rank N) B hiN hiN').mp hshort
      · have hiEq : i + 1 = N := by omega
        subst N
        have hDB : Function.Exact (Matrix.toLin' B)
            (Matrix.toLin' (C.differential i)) := by
          have h := hD i (by omega)
          have hshort : Function.Exact
              (Matrix.toLin'
                (C.shortenedDifferential (i + 1) (r.rank (i + 1)) B (i + 1)))
              (Matrix.toLin'
                (C.shortenedDifferential (i + 1) (r.rank (i + 1)) B i)) := by
            simpa only [D, shortenTop] using h
          exact (C.exact_shortenedDifferential_succ_top_iff
            i (r.rank (i + 1)) B).mp hshort
        have hbar : Function.Exact gbar
            (Matrix.toLin' (C.differential i)) := by
          have hpre : Function.Exact
              (gbar.comp eW.toLinearMap)
              (Matrix.toLin' (C.differential i)) := by
            simpa only [B, Matrix.toLin'_toMatrix'] using hDB
          exact (eW.surjective.comp_exact_iff_exact).mp hpre
        have hcomp : Function.Exact (gbar.comp q)
            (Matrix.toLin' (C.differential i)) :=
          (hq.comp_exact_iff_exact).mpr hbar
        have hgq : gbar.comp q = g :=
          (LinearMap.range f).liftQ_mkQ g hfg
        simpa only [hgq] using hcomp
    · by_cases hiEq : i = N
      · subst i
        have htopD : Function.Exact
            (Matrix.toLin'
              (C.shortenedDifferential N (r.rank N) B (N + 1)))
            (Matrix.toLin'
              (C.shortenedDifferential N (r.rank N) B N)) := by
          simpa only [D, shortenTop] using hD N (by omega)
        have hz := C.shortenedDifferential_eq_zero_of_lt N (r.rank N) B
          (i := N + 1) (Nat.lt_succ_self N)
        have hshortInj : Function.Injective
            (Matrix.toLin' (C.shortenedDifferential N (r.rank N) B N)) := by
          apply (LinearMap.exact_zero_iff_injective
            (Fin (C.shortenedTermRank N (r.rank N) (N + 2)) → R)
            (Matrix.toLin'
              (C.shortenedDifferential N (r.rank N) B N))).mp
          simpa only [hz, map_zero] using htopD
        have hBinj : Function.Injective (Matrix.toLin' B) := by
          have hrow : C.shortenedTermRank N (r.rank N) N = C.termRank N := by
            simp [shortenedTermRank]
          have hcol : C.shortenedTermRank N (r.rank N) (N + 1) = r.rank N := by
            simp [shortenedTermRank]
          simp only [shortenedDifferential, lt_self_iff_false, ↓reduceDIte]
            at hshortInj
          exact (Matrix.toLin'_eq_mpr_injective_iff hrow hcol B).mp hshortInj
        have hgbarInj : Function.Injective gbar := by
          intro x y hxy
          obtain ⟨x, rfl⟩ := eW.surjective x
          obtain ⟨y, rfl⟩ := eW.surjective y
          have hxy' : x = y := by
            apply hBinj
            simpa only [B, Matrix.toLin'_toMatrix', LinearMap.comp_apply,
              LinearEquiv.coe_coe] using hxy
          exact congrArg eW hxy'
        rw [LinearMap.exact_iff]
        exact (LinearMap.ker_eq_bot_range_liftQ_iff hfg).mp
          (LinearMap.ker_eq_bot.mpr hgbarInj)
      · have hiTop : i = N + 1 := by omega
        subst i
        have hzeroRank : C.termRank (N + 3) = 0 :=
          hbounded (N + 3) (by omega)
        have hzero : Matrix.toLin' (C.differential (N + 2)) = 0 := by
          apply LinearMap.ext
          intro x
          haveI : Subsingleton (Fin (C.termRank (N + 3)) → R) := by
            rw [hzeroRank]
            infer_instance
          have hx : x = 0 := Subsingleton.elim _ _
          subst x
          simp
        rw [hzero]
        exact (LinearMap.exact_zero_iff_injective
          (Fin (C.termRank (N + 3)) → R) f).mpr hf

end FiniteFreeComplex

end Matrix

end

end
