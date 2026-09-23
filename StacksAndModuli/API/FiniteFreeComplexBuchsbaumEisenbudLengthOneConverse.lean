module

public import StacksAndModuli.API.FiniteFreeComplexBuchsbaumEisenbudField
public import StacksAndModuli.API.FiniteFreeComplexBuchsbaumEisenbudLengthOne
public import StacksAndModuli.API.IdealRegularElementAssociatedPrimes
public import StacksAndModuli.API.PolynomialModelBaseChange

/-!
# The converse length-one Buchsbaum--Eisenbud implication

This file proves the Noetherian converse to the length-one determinantal acyclicity
criterion.  The key rectangular-matrix statement is a form of McCoy's theorem: if the
linear map of a matrix with `n` columns is injective, its ideal of `n × n` minors contains
an element regular on the coefficient ring.

At an associated prime, injectivity persists after localization.  The residue field embeds
in the localized ring through an associated socle element, so the matrix must remain
injective over that residue field.  If every maximal minor lay in the associated prime, the
residue-field matrix would instead have rank below `n`, a contradiction.  Finite prime
avoidance then extracts the required regular element.

Main declarations:

* `Matrix.toLin'_map_residue_injective_of_maximalIdeal_mem_associatedPrimes`;
* `Matrix.minorIdeal_card_cols_not_le_associatedPrime_of_toLin'_injective`;
* `Matrix.exists_isSMulRegular_mem_minorIdeal_card_cols_of_toLin'_injective`;
* `Matrix.FiniteFreeComplex.
  isExactInPositiveDegreesUpTo_one_iff_buchsbaumEisenbudGrade`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open IsLocalRing LinearMap Module

universe u

namespace Matrix

/-- Flat change of coefficients preserves injectivity of a finite matrix. -/
theorem toLin'_map_injective_of_flat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] {m n : ℕ} (B : Matrix (Fin m) (Fin n) R)
    (hB : Function.Injective (Matrix.toLin' B)) :
    Function.Injective
      (Matrix.toLin' (B.map (algebraMap R S))) := by
  let eM := TensorProduct.piScalarRight R S S (Fin n)
  let eN := TensorProduct.piScalarRight R S S (Fin m)
  have hbc : Function.Injective ((Matrix.toLin' B).baseChange S) :=
    Module.Flat.lTensor_preserves_injective_linearMap
      (M := S) (Matrix.toLin' B) hB
  have hcomm := Matrix.piScalarRight_toLin_map (A := S) B
  intro x y hxy
  apply eM.symm.injective
  apply hbc
  apply eN.injective
  calc
    eN (((Matrix.toLin' B).baseChange S) (eM.symm x)) =
        Matrix.toLin' (B.map (algebraMap R S)) (eM (eM.symm x)) :=
      LinearMap.congr_fun hcomm (eM.symm x)
    _ = Matrix.toLin' (B.map (algebraMap R S)) x := by simp
    _ = Matrix.toLin' (B.map (algebraMap R S)) y := hxy
    _ = Matrix.toLin' (B.map (algebraMap R S)) (eM (eM.symm y)) := by simp
    _ = eN (((Matrix.toLin' B).baseChange S) (eM.symm y)) :=
      (LinearMap.congr_fun hcomm (eM.symm y)).symm

/-- At an associated maximal ideal of a Noetherian local ring, injectivity of a finite
matrix implies injectivity of its residue-field matrix. -/
theorem toLin'_map_residue_injective_of_maximalIdeal_mem_associatedPrimes
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {m n : ℕ} (B : Matrix (Fin m) (Fin n) A)
    (hass : maximalIdeal A ∈ associatedPrimes A A)
    (hB : Function.Injective (Matrix.toLin' B)) :
    Function.Injective
      (Matrix.toLin' (B.map (algebraMap A (ResidueField A)))) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have hass' := isAssociatedPrime_iff.mp <|
    AssociatedPrimes.mem_iff.mp hass
  rcases hass'.2 with ⟨x, hx⟩
  have hxker : maximalIdeal A =
      (LinearMap.toSpanSingleton A A x).ker :=
    hx.trans (by simp [SetLike.ext_iff])
  let i : ResidueField A →ₗ[A] A :=
    Submodule.liftQ _ (LinearMap.toSpanSingleton A A x)
      (le_of_eq hxker)
  have hi : Function.Injective i :=
    LinearMap.ker_eq_bot.mp
      (Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hxker.symm))
  have hv' : B.map (algebraMap A (ResidueField A)) *ᵥ v = 0 := by
    simpa only [Matrix.toLin'_apply] using hv
  have hcompat :
      B *ᵥ (fun j ↦ i (v j)) =
        fun k ↦ i ((B.map (algebraMap A (ResidueField A)) *ᵥ v) k) := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [Algebra.smul_def, Algebra.algebraMap_self_apply] using
      (i.map_smul (B k j) (v j)).symm
  have hiv : (fun j ↦ i (v j)) = 0 := by
    apply hB
    simp only [Matrix.toLin'_apply]
    rw [hcompat, hv']
    funext k
    simp
  funext j
  apply hi
  simpa using congrFun hiv j

/-- An injective rectangular matrix over a Noetherian ring has a maximal-column-minor
ideal contained in no associated prime of the coefficient ring. -/
theorem minorIdeal_card_cols_not_le_associatedPrime_of_toLin'_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {m n : ℕ} (B : Matrix (Fin m) (Fin n) R)
    (hB : Function.Injective (Matrix.toLin' B))
    (p : Ideal R) (hp : p ∈ associatedPrimes R R) :
    ¬ minorIdeal B n ≤ p := by
  intro hminor
  letI : p.IsPrime := IsAssociatedPrime.isPrime hp
  let Rp := Localization.AtPrime p
  let K := p.ResidueField
  let Bp : Matrix (Fin m) (Fin n) Rp :=
    B.map (algebraMap R Rp)
  let Bk : Matrix (Fin m) (Fin n) K :=
    Bp.map (algebraMap Rp K)
  have hBp : Function.Injective (Matrix.toLin' Bp) := by
    exact Matrix.toLin'_map_injective_of_flat B hB
  have hass : maximalIdeal Rp ∈ associatedPrimes Rp Rp := by
    simpa only using
      (associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hp)
  have hBk : Function.Injective (Matrix.toLin' Bk) := by
    exact Matrix.toLin'_map_residue_injective_of_maximalIdeal_mem_associatedPrimes
      Bp hass hBp
  have hminorBot : minorIdeal Bk n = ⊥ := by
    dsimp only [Bk, Bp]
    rw [Matrix.minorIdeal_map, Matrix.minorIdeal_map, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R Rp K,
      Ideal.map_eq_bot_iff_le_ker,
      Ideal.ker_algebraMap_residueField]
    exact hminor
  have hLI : LinearIndependent K Bk.col :=
    Matrix.mulVec_injective_iff.mp hBk
  have hrank : Bk.rank = n :=
    Matrix.rank_eq_card_of_linearIndependent_cols Bk hLI
  have hminorTop : minorIdeal Bk n = ⊤ :=
    Matrix.minorIdeal_eq_top_of_le_rank Bk (by omega)
  exact (show (⊥ : Ideal K) ≠ ⊤ from bot_ne_top)
    (hminorBot.symm.trans hminorTop)

/-- McCoy's maximal-minor criterion: an injective rectangular matrix over a Noetherian
ring has a regular element in its maximal-column-minor ideal. -/
theorem exists_isSMulRegular_mem_minorIdeal_card_cols_of_toLin'_injective
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {m n : ℕ} (B : Matrix (Fin m) (Fin n) R)
    (hB : Function.Injective (Matrix.toLin' B)) :
    ∃ z : R, z ∈ minorIdeal B n ∧ IsSMulRegular R z := by
  rw [Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrime_not_le]
  intro p hp
  exact minorIdeal_card_cols_not_le_associatedPrime_of_toLin'_injective
    B hB p hp

namespace FiniteFreeComplex

/-- Exactness of a finite free complex bounded above by degree one makes its only
displayed differential injective. -/
theorem differential_zero_injective_of_isExactInPositiveDegreesUpTo_one
    {R : Type u} [CommRing R] (C : FiniteFreeComplex R)
    (hbounded : C.IsBoundedAbove 1)
    (hexact : C.IsExactInPositiveDegreesUpTo 1) :
    Function.Injective (Matrix.toLin' (C.differential 0)) := by
  have hexact0 := hexact 0 (by omega)
  rw [LinearMap.exact_iff] at hexact0
  have hterm2 : C.termRank 2 = 0 := hbounded 2 (by omega)
  haveI : Subsingleton (Fin (C.termRank 2) → R) := by
    rw [hterm2]
    infer_instance
  have hzero : Matrix.toLin' (C.differential 1) = 0 := by
    apply LinearMap.ext
    intro x
    rw [Subsingleton.elim x 0, map_zero]
    rfl
  rw [hzero, LinearMap.range_zero] at hexact0
  exact LinearMap.ker_eq_bot.mp hexact0

/-- The converse determinantal-grade implication for a finite free complex bounded above
by degree one over a Noetherian ring. -/
theorem buchsbaumEisenbudGrade_one_of_isExactInPositiveDegreesUpTo
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : FiniteFreeComplex R) (r : C.ExpectedRanks 1)
    (hbounded : C.IsBoundedAbove 1)
    (hexact : C.IsExactInPositiveDegreesUpTo 1) :
    minorIdeal (C.differential 0) (r.rank 0) = ⊤ ∨
      ∃ f : Fin 1 → R,
        (∀ j, f j ∈ minorIdeal (C.differential 0) (r.rank 0)) ∧
          RingTheory.Sequence.IsRegular R (List.ofFn f) := by
  have hrank : r.rank 0 = C.termRank 1 := by
    simpa [r.terminal] using r.add_succ 0 (by omega)
  rw [hrank]
  have hinj : Function.Injective
      (Matrix.toLin' (C.differential 0)) :=
    C.differential_zero_injective_of_isExactInPositiveDegreesUpTo_one
      hbounded hexact
  obtain ⟨z, hzI, hzreg⟩ :=
    exists_isSMulRegular_mem_minorIdeal_card_cols_of_toLin'_injective
      (C.differential 0) hinj
  by_cases hzunit : IsUnit z
  · left
    exact (minorIdeal (C.differential 0) (C.termRank 1)).eq_top_of_isUnit_mem
      hzI hzunit
  · right
    let f : Fin 1 → R := fun _ ↦ z
    refine ⟨f, fun _ ↦ hzI, ?_⟩
    have hweak : RingTheory.Sequence.IsWeaklyRegular R [z] :=
      (RingTheory.Sequence.isWeaklyRegular_singleton_iff R z).mpr hzreg
    have hregular : RingTheory.Sequence.IsRegular R [z] := by
      refine ⟨hweak, ?_⟩
      simpa [Ideal.ofList_singleton] using
        (Ideal.span_singleton_ne_top hzunit).symm
    simpa [f] using hregular

/-- The complete length-one Buchsbaum--Eisenbud criterion over a Noetherian ring. -/
theorem isExactInPositiveDegreesUpTo_one_iff_buchsbaumEisenbudGrade
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : FiniteFreeComplex R) (r : C.ExpectedRanks 1)
    (hbounded : C.IsBoundedAbove 1) :
    C.IsExactInPositiveDegreesUpTo 1 ↔
      minorIdeal (C.differential 0) (r.rank 0) = ⊤ ∨
        ∃ f : Fin 1 → R,
          (∀ j, f j ∈ minorIdeal (C.differential 0) (r.rank 0)) ∧
            RingTheory.Sequence.IsRegular R (List.ofFn f) := by
  constructor
  · exact C.buchsbaumEisenbudGrade_one_of_isExactInPositiveDegreesUpTo
      r hbounded
  · exact C.isExactInPositiveDegreesUpTo_one_of_buchsbaumEisenbudGrade
      r hbounded

end FiniteFreeComplex

end Matrix

end
