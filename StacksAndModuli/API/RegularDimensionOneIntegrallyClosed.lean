module

public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular domains of dimension at most one are integrally closed

Mathlib defines regular rings through regularity of all prime localizations and already
provides the discrete-valuation-ring criterion for a one-dimensional regular local
domain.  This file packages the local-to-global consequence needed when normalizing a
smooth affine curve.

## Main result

* `Ring.DimensionLEOne.of_krullDimLE_one`: the legacy ideal-theoretic dimension class
  follows from Mathlib's order-theoretic Krull-dimension bound for a domain.
* `IsIntegrallyClosed.of_isRegularRing_of_dimensionLEOne`: a regular domain whose Krull
  dimension is at most one is integrally closed.
-/

@[expose] public section

open scoped nonZeroDivisors

/-- For a ring without zero divisors, an order-theoretic Krull-dimension bound of one
supplies the ideal-theoretic `Ring.DimensionLEOne` class. -/
theorem Ring.DimensionLEOne.of_krullDimLE_one
    (R : Type*) [CommRing R] [NoZeroDivisors R] [Ring.KrullDimLE 1 R] :
    Ring.DimensionLEOne R := by
  refine ⟨fun {p} hp hprime ↦ ?_⟩
  exact (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
    (inferInstance : Ring.KrullDimLE 1 R)) p hp hprime

/-- A regular domain of Krull dimension at most one is integrally closed.

At every maximal ideal, the localized ring is a regular local domain of dimension at
most one.  It is either a field or has dimension exactly one; in the latter case,
regularity makes its cotangent space one-dimensional, so the local ring is a discrete
valuation ring.  Integrally closedness then descends from all maximal localizations. -/
theorem IsIntegrallyClosed.of_isRegularRing_of_dimensionLEOne
    (R : Type*) [CommRing R] [IsDomain R] [IsRegularRing R]
    [Ring.DimensionLEOne R] : IsIntegrallyClosed R := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p hp inst
  let _ : p.IsMaximal := inst
  let _ : p.IsPrime := inst.isPrime
  let Rp := Localization.AtPrime p
  let _ : Ring.DimensionLEOne Rp :=
    Ring.DimensionLEOne.localization Rp p.primeCompl_le_nonZeroDivisors
  by_cases hfield : IsField Rp
  · let _ := hfield.toField
    infer_instance
  · have hle : ringKrullDim Rp ≤ 1 :=
      Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 Rp)
    have hnotle_zero : ¬ ringKrullDim Rp ≤ 0 := by
      intro hzero
      let _ : Ring.KrullDimLE 0 Rp := Ring.krullDimLE_iff.mpr hzero
      exact hfield Ring.KrullDimLE.isField_of_isDomain
    have hdim : ringKrullDim Rp = 1 :=
      le_antisymm hle (Order.succ_le_of_lt (lt_of_not_ge hnotle_zero))
    have hregular :
        (Module.finrank (IsLocalRing.ResidueField Rp)
          (IsLocalRing.CotangentSpace Rp) : WithBot ℕ∞) = ringKrullDim Rp :=
      (IsRegularLocalRing.iff_finrank_cotangentSpace Rp).mp inferInstance
    have hfinrank : Module.finrank (IsLocalRing.ResidueField Rp)
        (IsLocalRing.CotangentSpace Rp) = 1 := by
      exact_mod_cast hregular.trans hdim
    let _ : IsDiscreteValuationRing Rp :=
      IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hfinrank
    infer_instance

end
