module

public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import StacksAndModuli.API.FiniteFreeComplexBuchsbaumEisenbudField
public import StacksAndModuli.API.FiniteFreeComplexProjectiveDimension
public import StacksAndModuli.API.LinearMapCokernelBaseChange
public import StacksAndModuli.API.ModuleFiniteProjectiveDimensionDepthZero

/-!
# Exactness over residue fields of associated primes

For an exact bounded finite free complex over a Noetherian local ring whose maximal ideal
is associated, every differential cokernel has finite projective dimension and hence is
projective.  Tensor exactness with flat cokernel therefore shows that the complex remains
exact over the residue field, even though that residue field need not be flat.

After localization, every associated prime becomes an associated maximal ideal.  Applying
the local result gives exactness over the associated-prime residue field.  The resulting
field ranks show that no expected-size determinantal ideal of the original exact complex
can be contained in an associated prime.

Main declarations:

* `Matrix.FiniteFreeComplex.IsExactInPositiveDegreesUpTo.
  map_at_of_flat_differentialCoker`;
* `Matrix.FiniteFreeComplex.IsExactInPositiveDegreesUpTo.
  map_residueField_of_maximalIdeal_mem_associatedPrimes`;
* `Matrix.FiniteFreeComplex.IsExactInPositiveDegreesUpTo.
  map_localization_residueField_of_mem_associatedPrimes`;
* `Matrix.FiniteFreeComplex.ExpectedRanks.
  minorIdeal_not_le_associatedPrime_of_exact`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open IsLocalRing

universe u

namespace Matrix.FiniteFreeComplex

variable {R : Type u} [CommRing R]

/-- Exactness at one displayed degree is preserved by arbitrary coefficient extension
when the cokernel of the outgoing differential is flat. -/
theorem IsExactInPositiveDegreesUpTo.map_at_of_flat_differentialCoker
    {S : Type u} [CommRing S] [Algebra R S]
    {C : FiniteFreeComplex R} {N i : ℕ}
    (h : C.IsExactInPositiveDegreesUpTo N) (hi : i < N)
    [Module.Flat R (C.differentialCoker i)] :
    Function.Exact
      (Matrix.toLin'
        ((C.differential (i + 1)).map (algebraMap R S)))
      (Matrix.toLin' ((C.differential i).map (algebraMap R S))) := by
  let e₀ := TensorProduct.piScalarRight R S S (Fin (C.termRank i))
  let e₁ := TensorProduct.piScalarRight R S S (Fin (C.termRank (i + 1)))
  let e₂ := TensorProduct.piScalarRight R S S (Fin (C.termRank (i + 2)))
  have hbaseChange : Function.Exact
      ((Matrix.toLin' (C.differential (i + 1))).baseChange S)
      ((Matrix.toLin' (C.differential i)).baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor,
      LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_exact_of_exact_of_coker_flat
      (Matrix.toLin' (C.differential (i + 1)))
      (Matrix.toLin' (C.differential i)) (h i hi)
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (f₁₂ := (Matrix.toLin' (C.differential (i + 1))).baseChange S)
    (f₂₃ := (Matrix.toLin' (C.differential i)).baseChange S)
    (g₁₂ := Matrix.toLin'
      ((C.differential (i + 1)).map (algebraMap R S)))
    (g₂₃ := Matrix.toLin'
      ((C.differential i).map (algebraMap R S)))
    (e₁ := e₂) (e₂ := e₁) (e₃ := e₀)
    (Matrix.piScalarRight_toLin_map
      (A := S) (C.differential (i + 1))).symm
    (Matrix.piScalarRight_toLin_map
      (A := S) (C.differential i)).symm).mpr hbaseChange

/-- Over a Noetherian local ring whose maximal ideal is associated, a bounded exact
finite free complex remains exact over the residue field. -/
theorem IsExactInPositiveDegreesUpTo.map_residueField_of_maximalIdeal_mem_associatedPrimes
    [IsLocalRing R] [IsNoetherianRing R]
    {C : FiniteFreeComplex R} {N : ℕ}
    (h : C.IsExactInPositiveDegreesUpTo N)
    (hbounded : C.IsBoundedAbove N)
    (hass : maximalIdeal R ∈ associatedPrimes R R) :
    (C.map (algebraMap R (ResidueField R))).IsExactInPositiveDegreesUpTo N := by
  intro i hi
  letI : Module.Projective R (C.differentialCoker i) :=
    Module.projective_of_hasProjectiveDimensionLE_of_maximalIdeal_mem_associatedPrimes
      hass
      (C.hasProjectiveDimensionLE_differentialCoker N hbounded h
        (Nat.le_of_lt hi))
  exact h.map_at_of_flat_differentialCoker
    (S := ResidueField R) hi

/-- Localizing at an associated prime and then passing to its residue field preserves
exactness of a bounded finite free complex. -/
theorem IsExactInPositiveDegreesUpTo.map_localization_residueField_of_mem_associatedPrimes
    [IsNoetherianRing R]
    {C : FiniteFreeComplex R} {N : ℕ}
    (h : C.IsExactInPositiveDegreesUpTo N)
    (hbounded : C.IsBoundedAbove N)
    (q : PrimeSpectrum R)
    (hq : q.asIdeal ∈ associatedPrimes R R) :
    ((C.map (algebraMap R (Localization.AtPrime q.asIdeal))).map
      (algebraMap (Localization.AtPrime q.asIdeal)
        q.asIdeal.ResidueField)).IsExactInPositiveDegreesUpTo N := by
  let Rp := Localization.AtPrime q.asIdeal
  let Cp := C.map (algebraMap R Rp)
  have hCp : Cp.IsExactInPositiveDegreesUpTo N :=
    h.map_of_flat
  have hCpBounded : Cp.IsBoundedAbove N :=
    hbounded.map (algebraMap R Rp)
  have hass : maximalIdeal Rp ∈ associatedPrimes Rp Rp := by
    simpa only using
      (Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes hq)
  exact hCp.map_residueField_of_maximalIdeal_mem_associatedPrimes
    hCpBounded hass

namespace ExpectedRanks

/-- No expected-size minor ideal of a bounded exact finite free complex over a
Noetherian ring is contained in an associated prime of the coefficient ring. -/
theorem minorIdeal_not_le_associatedPrime_of_exact
    [IsNoetherianRing R]
    {C : FiniteFreeComplex R} {N : ℕ}
    (r : C.ExpectedRanks N)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N)
    {i : ℕ} (hi : i ≤ N)
    (q : PrimeSpectrum R)
    (hq : q.asIdeal ∈ associatedPrimes R R) :
    ¬ Matrix.minorIdeal (C.differential i) (r.rank i) ≤ q.asIdeal := by
  intro hminor
  let Rp := Localization.AtPrime q.asIdeal
  let K := q.asIdeal.ResidueField
  let Cp := C.map (algebraMap R Rp)
  let Ck := Cp.map (algebraMap Rp K)
  let rp := r.map (algebraMap R Rp)
  let rk := rp.map (algebraMap Rp K)
  have hboundedk : Ck.IsBoundedAbove N :=
    (hbounded.map (algebraMap R Rp)).map (algebraMap Rp K)
  have hexactk : Ck.IsExactInPositiveDegreesUpTo N := by
    exact hexact.map_localization_residueField_of_mem_associatedPrimes
      hbounded q hq
  have hrank : r.rank i = (Ck.differential i).rank := by
    simpa only [rk, rp, ExpectedRanks.map_rank] using
      rk.rank_eq_differential_of_exact hboundedk hexactk hi
  have hminorBot :
      Matrix.minorIdeal (Ck.differential i) (r.rank i) = ⊥ := by
    change Matrix.minorIdeal
      (((C.differential i).map (algebraMap R Rp)).map
        (algebraMap Rp K)) (r.rank i) = ⊥
    rw [Matrix.minorIdeal_map, Matrix.minorIdeal_map, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R Rp K,
      Ideal.map_eq_bot_iff_le_ker,
      Ideal.ker_algebraMap_residueField]
    exact hminor
  have hminorTop :
      Matrix.minorIdeal (Ck.differential i) (r.rank i) = ⊤ :=
    Matrix.minorIdeal_eq_top_of_le_rank (Ck.differential i) (by omega)
  exact (show (⊥ : Ideal K) ≠ ⊤ from bot_ne_top)
    (hminorBot.symm.trans hminorTop)

end ExpectedRanks

end Matrix.FiniteFreeComplex

end

end
