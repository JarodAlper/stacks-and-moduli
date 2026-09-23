module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksAndModuli.API.FiniteFreeComplexBuchsbaumEisenbudLengthOne
public import StacksAndModuli.API.FiniteFreeComplexBuchsbaumEisenbudMinimal
public import StacksAndModuli.API.FiniteFreeComplexUnitCancellation
public import StacksAndModuli.API.NoetherianExactnessLocus

/-!
# The local Buchsbaum--Eisenbud acyclicity criterion

This file supplies the dimension-induction infrastructure for the local
Buchsbaum--Eisenbud acyclicity criterion.  The natural-number measure of a Noetherian
local ring is the height of its maximal ideal.  Localizing at a nonclosed prime strictly
decreases this measure.  Exactness of the coefficientwise-localized matrix complex is
identified with exactness of the corresponding localized-module maps by the canonical
finite-free base-change equivalences.

These two facts form the punctured-spectrum branch of the induction.  The complementary
branch shortens a complex whose top expected-minor ideal is the unit ideal.

Main declarations:

* `Matrix.FiniteFreeComplex.localKrullDimNat`;
* `Matrix.FiniteFreeComplex.localKrullDimNat_atPrime_lt`;
* `Matrix.FiniteFreeComplex.exact_localizedMap_iff_map_atPrime`;
* `Matrix.FiniteFreeComplex.
  isExactInPositiveDegreesUpTo_of_buchsbaumEisenbudGrade`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Matrix.FiniteFreeComplex

variable {R : Type u} [CommRing R]

/-- The Krull dimension of a Noetherian local ring, represented as a natural number via
the finite height of its maximal ideal. -/
def localKrullDimNat (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] : ℕ :=
  (IsLocalRing.maximalIdeal R).height.toNat

/-- Localization of a Noetherian local ring at a nonclosed prime has strictly smaller
natural-number Krull dimension. -/
theorem localKrullDimNat_atPrime_lt
    [IsNoetherianRing R] [IsLocalRing R]
    (p : PrimeSpectrum R) (hp : p ≠ IsLocalRing.closedPoint R) :
    localKrullDimNat (Localization.AtPrime p.asIdeal) < localKrullDimNat R := by
  let Rp := Localization.AtPrime p.asIdeal
  have hpIdeal : p.asIdeal ≠ IsLocalRing.maximalIdeal R := by
    intro h
    apply hp
    exact PrimeSpectrum.ext h
  have hpLt : p.asIdeal < IsLocalRing.maximalIdeal R :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime p.asIdeal) hpIdeal
  have hheight : p.asIdeal.height < (IsLocalRing.maximalIdeal R).height :=
    Ideal.height_strict_mono_of_isPrime_of_isPrime hpLt
  have hRp : (IsLocalRing.maximalIdeal Rp).height = p.asIdeal.height := by
    apply WithBot.coe_injective
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal Rp]
  change (IsLocalRing.maximalIdeal Rp).height.toNat <
    (IsLocalRing.maximalIdeal R).height.toNat
  rw [hRp, ← ENat.natCast_lt_natCast,
    ENat.natCast_toNat (Ideal.height_ne_top_of_isPrime (I := p.asIdeal)),
    ENat.natCast_toNat
      (Ideal.height_ne_top_of_isPrime
        (I := IsLocalRing.maximalIdeal R))]
  exact hheight

/-- Exactness of two adjacent localized-module differentials is equivalent to exactness
of the coefficientwise-mapped matrices over the local ring at the prime. -/
theorem exact_localizedMap_iff_map_atPrime
    (C : FiniteFreeComplex R) (i : ℕ) (p : PrimeSpectrum R) :
    Function.Exact
        (LocalizedModule.map p.asIdeal.primeCompl
          (Matrix.toLin' (C.differential (i + 1))))
        (LocalizedModule.map p.asIdeal.primeCompl
          (Matrix.toLin' (C.differential i))) ↔
      Function.Exact
        (Matrix.toLin' ((C.differential (i + 1)).map
          (algebraMap R (Localization.AtPrime p.asIdeal))))
        (Matrix.toLin' ((C.differential i).map
          (algebraMap R (Localization.AtPrime p.asIdeal)))) := by
  rw [LinearMap.exact_localizedMap_iff_baseChange]
  let Rp := Localization.AtPrime p.asIdeal
  let e₀ := TensorProduct.piScalarRight R Rp Rp (Fin (C.termRank i))
  let e₁ := TensorProduct.piScalarRight R Rp Rp (Fin (C.termRank (i + 1)))
  let e₂ := TensorProduct.piScalarRight R Rp Rp (Fin (C.termRank (i + 2)))
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (f₁₂ := (Matrix.toLin' (C.differential (i + 1))).baseChange Rp)
    (f₂₃ := (Matrix.toLin' (C.differential i)).baseChange Rp)
    (g₁₂ := Matrix.toLin' ((C.differential (i + 1)).map
      (algebraMap R Rp)))
    (g₂₃ := Matrix.toLin' ((C.differential i).map
      (algebraMap R Rp)))
    (e₁ := e₂) (e₂ := e₁) (e₃ := e₀)
    (Matrix.piScalarRight_toLin_map
      (A := Rp) (C.differential (i + 1))).symm
    (Matrix.piScalarRight_toLin_map
      (A := Rp) (C.differential i)).symm).symm

/-- Strong-induction form of the local Buchsbaum--Eisenbud implication.  The induction
measure combines the local Krull dimension and the displayed length: localization at a
nonclosed prime lowers the first summand, while cancellation of a top unit-minor
summand lowers the second. -/
theorem isExactInPositiveDegreesUpTo_of_buchsbaumEisenbudGrade_of_measure
    (fuel : ℕ) :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
      (C : FiniteFreeComplex R) (N : ℕ) (r : C.ExpectedRanks N),
      localKrullDimNat R + N ≤ fuel →
        C.IsBoundedAbove N →
        C.HasExpectedRankBounds r →
        C.HasBuchsbaumEisenbudGrade r →
        C.IsExactInPositiveDegreesUpTo N := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro R _ _ _ C N r hmeasure hbounded hrank hgrade
    cases N with
    | zero =>
        intro i hi
        omega
    | succ N =>
      cases N with
      | zero =>
          exact C.isExactInPositiveDegreesUpTo_one_of_buchsbaumEisenbudGrade
            r hbounded (hgrade 0 (by omega))
      | succ N =>
        by_cases htop : minorIdeal (C.differential (N + 1))
            (r.rank (N + 1)) = ⊤
        · obtain ⟨D, s, hDbounded, hDbounds, hDgrade, hback⟩ :=
            C.exists_unitCancellation N r hbounded htop
          have hshort : localKrullDimNat R + (N + 1) < fuel := by
            omega
          have hDExact : D.IsExactInPositiveDegreesUpTo (N + 1) :=
            ih (localKrullDimNat R + (N + 1)) hshort
              (R := R) D (N + 1) s (le_refl _)
              hDbounded (hDbounds hrank) (hDgrade hgrade)
          exact hback hDExact
        · refine
            C.isExactInPositiveDegreesUpTo_succ_of_buchsbaumEisenbudGrade_of_topMinorIdeal_ne_top
              (N + 1) r hbounded hgrade htop ?_
          intro p hp i hi
          let Rp := Localization.AtPrime p.asIdeal
          let Cp := C.map (algebraMap R Rp)
          let rp := r.map (algebraMap R Rp)
          have hdim : localKrullDimNat Rp < localKrullDimNat R := by
            simpa only [Rp] using localKrullDimNat_atPrime_lt p hp
          have hlocal : localKrullDimNat Rp + (N + 2) < fuel := by
            omega
          have hCpBounded : Cp.IsBoundedAbove (N + 2) :=
            hbounded.map (algebraMap R Rp)
          have hCpBounds : Cp.HasExpectedRankBounds rp :=
            HasExpectedRankBounds.map r hrank (algebraMap R Rp)
          have hCpGrade : Cp.HasBuchsbaumEisenbudGrade rp :=
            HasBuchsbaumEisenbudGrade.map_atPrime r hgrade p.asIdeal
          have hCpExact : Cp.IsExactInPositiveDegreesUpTo (N + 2) :=
            ih (localKrullDimNat Rp + (N + 2)) hlocal
              (R := Rp) Cp (N + 2) rp (le_refl _)
              hCpBounded hCpBounds hCpGrade
          refine (C.exact_localizedMap_iff_map_atPrime i p).mpr ?_
          simpa only [Cp, map_termRank, map_differential] using hCpExact i hi

/-- A bounded finite free complex over a Noetherian local ring is exact in positive
degrees when its differentials satisfy the prescribed rank bounds and its expected-size
minor ideals satisfy the Buchsbaum--Eisenbud grade conditions. -/
theorem isExactInPositiveDegreesUpTo_of_buchsbaumEisenbudGrade
    [IsNoetherianRing R] [IsLocalRing R]
    (C : FiniteFreeComplex R) (N : ℕ) (r : C.ExpectedRanks N)
    (hbounded : C.IsBoundedAbove N)
    (hrank : C.HasExpectedRankBounds r)
    (hgrade : C.HasBuchsbaumEisenbudGrade r) :
    C.IsExactInPositiveDegreesUpTo N := by
  exact
    isExactInPositiveDegreesUpTo_of_buchsbaumEisenbudGrade_of_measure
      (localKrullDimNat R + N) C N r (le_refl _)
        hbounded hrank hgrade

end Matrix.FiniteFreeComplex

end

end
