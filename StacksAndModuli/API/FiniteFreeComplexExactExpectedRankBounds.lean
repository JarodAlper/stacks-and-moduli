module

public import StacksAndModuli.API.FiniteFreeComplexAssociatedPrimeExactness
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Expected-rank bounds for exact finite free complexes

This file proves the scheme-theoretic rank half of the Buchsbaum--Eisenbud converse.
For a bounded exact finite free complex over a Noetherian ring, every differential has
rank at most its prescribed expected rank: all minors one size larger vanish in the
coefficient ring, not merely in its residue fields.

The proof localizes at the associated primes.  There the maximal ideal is associated,
so finite projective dimension makes each differential cokernel projective and hence
finite free.  Its free rank can be read after passage to the residue field, where
exactness gives the prescribed matrix rank.  Thus the range of the differential is
finite free of the prescribed rank, and the matrix factors through a standard free
module of that rank.  Padding this factorization by one zero column proves that every
successor-size minor vanishes.  Finally, localizations at the associated primes jointly
detect zero over a Noetherian ring.

Main declarations:

* `Ideal.eq_bot_of_map_at_associatedPrimes_eq_bot`;
* `Matrix.minorIdeal_succ_eq_bot_of_factor_fin`;
* `Matrix.FiniteFreeComplex.ExpectedRanks.
  minorIdeal_succ_eq_bot_of_exact_of_maximalIdeal_mem_associatedPrimes`;
* `Matrix.FiniteFreeComplex.
  hasExpectedRankBounds_of_isExactInPositiveDegreesUpTo`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v w

open Function IsLocalRing LinearMap Module

namespace Ideal

variable {R : Type u} [CommRing R]

/-- An element of a Noetherian ring which vanishes after localization at every
associated prime is zero. -/
theorem eq_zero_of_map_at_associatedPrimes_eq_zero
    [IsNoetherianRing R] {x : R}
    (h : ∀ p : PrimeSpectrum R,
      p.asIdeal ∈ associatedPrimes R R →
        algebraMap R (Localization.AtPrime p.asIdeal) x = 0) :
    x = 0 := by
  by_contra hx
  let M : Submodule R R := Submodule.span R ({x} : Set R)
  have hxM : (x : R) ∈ M := by
    exact Submodule.subset_span (Set.mem_singleton x)
  have hM : ¬ Subsingleton M := by
    intro hsub
    apply hx
    have heq : (⟨x, hxM⟩ : M) = 0 := Subsingleton.elim _ _
    exact congrArg Subtype.val heq
  letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
  obtain ⟨p, hpM⟩ := associatedPrimes.nonempty R M
  letI : p.IsPrime := IsAssociatedPrime.isPrime hpM
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  have hpR : p ∈ associatedPrimes R R :=
    associatedPrimes.subset_of_injective
      (f := M.subtype) Subtype.val_injective hpM
  have hxloc := h q hpR
  obtain ⟨s, hs⟩ :=
    (IsLocalization.map_eq_zero_iff p.primeCompl
      (Localization.AtPrime p) x).mp hxloc
  have hsAnnM : (s : R) ∈ (M : Submodule R R).annihilator := by
    change (s : R) ∈ (Submodule.span R ({x} : Set R)).annihilator
    rw [Submodule.mem_annihilator_span_singleton]
    simpa only [smul_eq_mul] using hs
  have hsAnnTop : (s : R) ∈ (⊤ : Submodule R M).annihilator := by
    rw [Submodule.mem_annihilator]
    intro y hy
    apply Subtype.ext
    exact (Submodule.mem_annihilator.mp hsAnnM) y.1 y.2
  have hsP : (s : R) ∈ p := hpM.annihilator_le hsAnnTop
  exact s.2 hsP

/-- An ideal of a Noetherian ring is zero if its extension to the localization at
every associated prime is zero. -/
theorem eq_bot_of_map_at_associatedPrimes_eq_bot
    [IsNoetherianRing R] (I : Ideal R)
    (h : ∀ p : PrimeSpectrum R,
      p.asIdeal ∈ associatedPrimes R R →
        I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊥) :
    I = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  apply eq_zero_of_map_at_associatedPrimes_eq_zero
  intro p hp
  have hxmap : algebraMap R (Localization.AtPrime p.asIdeal) x ∈
      I.map (algebraMap R (Localization.AtPrime p.asIdeal)) :=
    Ideal.mem_map_of_mem _ hx
  rw [h p hp] at hxmap
  exact Ideal.mem_bot.mp hxmap

end Ideal

namespace Matrix

variable {R : Type u} [CommRing R]

/-- A matrix which factors through a standard free module of rank `r` has vanishing
minors of size `r + 1`. -/
theorem minorIdeal_succ_eq_bot_of_factor_fin
    {m : Type v} {n : Type w}
    (A : Matrix m (Fin r) R) (B : Matrix (Fin r) n R) :
    minorIdeal (A * B) (r + 1) = ⊥ := by
  apply le_antisymm
  · rw [minorIdeal_le_iff]
    intro rows cols
    let A₀ : Matrix (Fin (r + 1)) (Fin r ⊕ Fin 1) R :=
      Matrix.fromCols
        (A.submatrix rows (fun j : Fin r ↦ j))
        (0 : Matrix (Fin (r + 1)) (Fin 1) R)
    let B₀ : Matrix (Fin r ⊕ Fin 1) (Fin (r + 1)) R :=
      Matrix.fromRows
        (B.submatrix (fun j : Fin r ↦ j) cols)
        (0 : Matrix (Fin 1) (Fin (r + 1)) R)
    let e : Fin (r + 1) ≃ Fin r ⊕ Fin 1 := finSumFinEquiv.symm
    have hproduct : (A * B).submatrix rows cols =
        A₀.submatrix (fun j : Fin (r + 1) ↦ j) e *
          B₀.submatrix e (fun j : Fin (r + 1) ↦ j) := by
      rw [Matrix.submatrix_mul_equiv A₀ B₀
          (fun j : Fin (r + 1) ↦ j) e
          (fun j : Fin (r + 1) ↦ j),
        Matrix.fromCols_mul_fromRows]
      simp only [Matrix.mul_zero, add_zero]
      exact (Matrix.submatrix_mul_equiv A B rows (Equiv.refl (Fin r)) cols).symm
    rw [Ideal.mem_bot, hproduct, Matrix.det_mul]
    have hzero :
        (A₀.submatrix (fun j : Fin (r + 1) ↦ j) e).det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero
        (e.symm (Sum.inr (0 : Fin 1)))
      intro i
      simp [A₀, e]
    rw [hzero, zero_mul]
  · exact bot_le

/-- If the range of a finite matrix is finite free, the minors one size larger than
its free rank vanish. -/
theorem minorIdeal_succ_finrank_range_eq_bot
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    [Nontrivial R]
    [Module.Finite R (LinearMap.range (Matrix.toLin' A))]
    [Module.Free R (LinearMap.range (Matrix.toLin' A))] :
    minorIdeal A
      (Module.finrank R (LinearMap.range (Matrix.toLin' A)) + 1) = ⊥ := by
  let P := LinearMap.range (Matrix.toLin' A)
  let b := Module.finBasis R P
  let q : (Fin n → R) →ₗ[R] P :=
    (Matrix.toLin' A).codRestrict P fun x ↦
      LinearMap.mem_range_self (Matrix.toLin' A) x
  let f : (Fin (Module.finrank R P) → R) →ₗ[R] (Fin m → R) :=
    P.subtype.comp b.equivFun.symm.toLinearMap
  let g : (Fin n → R) →ₗ[R] (Fin (Module.finrank R P) → R) :=
    b.equivFun.toLinearMap.comp q
  have hcomp : f.comp g = Matrix.toLin' A := by
    apply LinearMap.ext
    intro x
    simp [f, g, q]
  let U := LinearMap.toMatrix' f
  let V := LinearMap.toMatrix' g
  have hA : A = U * V := by
    calc
      A = LinearMap.toMatrix' (Matrix.toLin' A) :=
        (LinearMap.toMatrix'_toLin' A).symm
      _ = LinearMap.toMatrix' (f.comp g) := congrArg LinearMap.toMatrix' hcomp.symm
      _ = U * V := by
        simpa only [U, V] using LinearMap.toMatrix'_comp f g
  calc
    minorIdeal A
        (Module.finrank R (LinearMap.range (Matrix.toLin' A)) + 1) =
      minorIdeal (U * V)
        (Module.finrank R (LinearMap.range (Matrix.toLin' A)) + 1) :=
      congrArg
        (fun X ↦ minorIdeal X
          (Module.finrank R (LinearMap.range (Matrix.toLin' A)) + 1)) hA
    _ = ⊥ := by
      simpa only [P] using minorIdeal_succ_eq_bot_of_factor_fin U V

/-- The free rank of the cokernel of a matrix is the row count minus the rank of
the coefficientwise-mapped matrix over a field. -/
theorem finrank_coker_toLin'_eq_card_rows_sub_rank_map
    {K : Type u} [Field K] [Algebra R K]
    [StrongRankCondition R]
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    [Module.Finite R
      ((Fin m → R) ⧸ LinearMap.range (Matrix.toLin' A))]
    [Module.Free R
      ((Fin m → R) ⧸ LinearMap.range (Matrix.toLin' A))] :
    Module.finrank R
        ((Fin m → R) ⧸ LinearMap.range (Matrix.toLin' A)) =
      m - (A.map (algebraMap R K)).rank := by
  let g := Matrix.toLin' A
  let eM := TensorProduct.piScalarRight R K K (Fin m)
  let eN := TensorProduct.piScalarRight R K K (Fin n)
  let AK := A.map (algebraMap R K)
  have hcomm : eM.toLinearMap.comp (g.baseChange K) =
      (Matrix.toLin' AK).comp eN.toLinearMap := by
    simpa only [g, AK] using Matrix.piScalarRight_toLin_map (A := K) A
  have hrangeMap :
      (LinearMap.range (g.baseChange K)).map eM.toLinearMap =
        LinearMap.range (Matrix.toLin' AK) := by
    rw [← LinearMap.range_comp, hcomm,
      LinearMap.range_comp_of_range_eq_top _ eN.range]
  have hrangeFinrank :
      Module.finrank K (LinearMap.range (g.baseChange K)) = AK.rank := by
    rw [AK.rank_eq_finrank_span_cols, ← Matrix.range_toLin']
    exact (eM.ofSubmodules _ _ hrangeMap).finrank_eq
  calc
    Module.finrank R
          ((Fin m → R) ⧸ LinearMap.range (Matrix.toLin' A)) =
        Module.finrank K
          (TensorProduct R K ((Fin m → R) ⧸
            LinearMap.range (Matrix.toLin' A))) := by
      symm
      exact Module.finrank_baseChange
    _ = Module.finrank K
          ((TensorProduct R K (Fin m → R)) ⧸
            LinearMap.range (g.baseChange K)) :=
      (LinearMap.baseChangeCokerEquiv (T := K) g).finrank_eq.symm
    _ = Module.finrank K (TensorProduct R K (Fin m → R)) -
          Module.finrank K (LinearMap.range (g.baseChange K)) :=
      Submodule.finrank_quotient _
    _ = m - AK.rank := by
      rw [eM.finrank_eq, Module.finrank_fin_fun, hrangeFinrank]

namespace FiniteFreeComplex

variable {C : FiniteFreeComplex R} {N : ℕ}

namespace ExpectedRanks

/-- At an associated maximal ideal, exactness and boundedness force the actual
scheme-theoretic upper bound on every differential rank. -/
theorem minorIdeal_succ_eq_bot_of_exact_of_maximalIdeal_mem_associatedPrimes
    [IsNoetherianRing R] [IsLocalRing R]
    (r : C.ExpectedRanks N)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N)
    (hass : maximalIdeal R ∈ associatedPrimes R R)
    {i : ℕ} (hi : i < N) :
    minorIdeal (C.differential i) (r.rank i + 1) = ⊥ := by
  let K := ResidueField R
  let CK := C.map (algebraMap R K)
  let rK := r.map (algebraMap R K)
  have hboundedK : CK.IsBoundedAbove N :=
    hbounded.map (algebraMap R K)
  have hexactK : CK.IsExactInPositiveDegreesUpTo N :=
    hexact.map_residueField_of_maximalIdeal_mem_associatedPrimes
      hbounded hass
  have hrankK : r.rank i =
      ((C.differential i).map (algebraMap R K)).rank := by
    simpa only [CK, rK, map_differential, ExpectedRanks.map_rank] using
      rK.rank_eq_differential_of_exact hboundedK hexactK
        (Nat.le_of_lt hi)
  letI : Module.Projective R (C.differentialCoker i) :=
    Module.projective_of_hasProjectiveDimensionLE_of_maximalIdeal_mem_associatedPrimes
      hass
      (C.hasProjectiveDimensionLE_differentialCoker N hbounded hexact
        (Nat.le_of_lt hi))
  letI : Module.Flat R (C.differentialCoker i) :=
    Module.Flat.of_projective
  letI : Module.Free R (C.differentialCoker i) :=
    Module.free_of_flat_of_isLocalRing
  have hfinCoker : Module.finrank R (C.differentialCoker i) =
      C.termRank i - r.rank i := by
    simpa only [hrankK] using
      (Matrix.finrank_coker_toLin'_eq_card_rows_sub_rank_map
        (K := K) (C.differential i))
  let P := LinearMap.range (Matrix.toLin' (C.differential i))
  letI : Module.Finite R P :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  obtain ⟨liftMap, hliftMap⟩ :=
    Module.projective_lifting_property
      (Submodule.mkQ P) (LinearMap.id : C.differentialCoker i →ₗ[R]
        C.differentialCoker i) (Submodule.mkQ_surjective P)
  letI : Module.Projective R P := by
    have hsplit :=
      (Function.Exact.split_tfae
        (LinearMap.exact_subtype_mkQ P)
        Subtype.val_injective (Submodule.mkQ_surjective P)).out 0 1
    obtain ⟨s, hs⟩ := hsplit.mp ⟨liftMap, hliftMap⟩
    exact Module.Projective.of_split _ _ hs
  letI : Module.Flat R P := Module.Flat.of_projective
  letI : Module.Free R P := Module.free_of_flat_of_isLocalRing
  let e : (Fin (C.termRank i) → R) ≃ₗ[R]
      P × C.differentialCoker i :=
    ((LinearMap.exact_subtype_mkQ P).splitSurjectiveEquiv
      Subtype.val_injective ⟨liftMap, hliftMap⟩).1
  have hfinSum := e.finrank_eq
  have hrankLe : r.rank i ≤ C.termRank i := by
    rw [hrankK]
    simpa only [Fintype.card_fin] using
      ((C.differential i).map (algebraMap R K)).rank_le_height
  have hfinRange : Module.finrank R P = r.rank i := by
    rw [Module.finrank_prod, Module.finrank_fin_fun] at hfinSum
    change C.termRank i = Module.finrank R P +
      Module.finrank R (C.differentialCoker i) at hfinSum
    rw [hfinCoker] at hfinSum
    omega
  simpa only [P, hfinRange] using
    Matrix.minorIdeal_succ_finrank_range_eq_bot
      (C.differential i)

end ExpectedRanks

/-- A bounded exact finite free complex over a Noetherian ring satisfies the
scheme-theoretic upper bounds for any prescribed expected-rank function. -/
theorem hasExpectedRankBounds_of_isExactInPositiveDegreesUpTo
    [IsNoetherianRing R]
    (C : FiniteFreeComplex R) (N : ℕ) (r : C.ExpectedRanks N)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N) :
    C.HasExpectedRankBounds r := by
  intro i hi
  apply Ideal.eq_bot_of_map_at_associatedPrimes_eq_bot
  intro p hp
  let Rp := Localization.AtPrime p.asIdeal
  let Cp := C.map (algebraMap R Rp)
  let rp := r.map (algebraMap R Rp)
  have hboundedp : Cp.IsBoundedAbove N :=
    hbounded.map (algebraMap R Rp)
  have hexactp : Cp.IsExactInPositiveDegreesUpTo N :=
    hexact.map_of_flat
  have hass : maximalIdeal Rp ∈ associatedPrimes Rp Rp := by
    simpa only using
      (associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hp)
  have hlocal :=
    rp.minorIdeal_succ_eq_bot_of_exact_of_maximalIdeal_mem_associatedPrimes
      hboundedp hexactp hass hi
  simpa only [Cp, rp, map_differential, ExpectedRanks.map_rank,
    Matrix.minorIdeal_map] using hlocal

end FiniteFreeComplex

end Matrix

end

end
