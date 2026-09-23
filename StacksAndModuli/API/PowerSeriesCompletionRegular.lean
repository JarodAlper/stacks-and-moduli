module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regularity from a one-variable power-series completion

A Noetherian local domain whose maximal-ideal-adic completion is a one-variable
power-series ring over a field is regular.  This packages the commutative-algebra bridge
needed when a formal branch of a nodal curve has been identified with `k[[t]]`.

## Main result

* `isRegularLocalRing_of_adicCompletion_equiv_powerSeries`: a local domain is regular
  when its completion is ring-equivalent to `PowerSeries k`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open IsLocalRing

universe u

/-- A Noetherian local domain is regular if its maximal-ideal-adic completion is a
one-variable power-series ring over a field. -/
theorem isRegularLocalRing_of_adicCompletion_equiv_powerSeries
    (k R : Type u) [Field k] [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsDomain R]
    (e : AdicCompletion (maximalIdeal R) R ≃+* PowerSeries k) :
    IsRegularLocalRing R := by
  have hspanCompletion :
      (maximalIdeal (AdicCompletion (maximalIdeal R) R)).spanFinrank = 1 := by
    let _ : IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) :=
      IsRegularLocalRing.of_ringEquiv e.symm
    have hdimCompletion :
        ringKrullDim (AdicCompletion (maximalIdeal R) R) = 1 :=
      (ringKrullDim_eq_of_ringEquiv e).trans
        (IsPrincipalIdealRing.ringKrullDim_eq_one (PowerSeries k)
          PowerSeries.not_isField)
    have hregular :=
      IsRegularLocalRing.spanFinrank_maximalIdeal
        (R := AdicCompletion (maximalIdeal R) R)
    rw [hdimCompletion] at hregular
    exact_mod_cast hregular
  have hspan : (maximalIdeal R).spanFinrank = 1 := by
    rw [← AdicCompletion.spanFinrank_maximalIdeal_eq]
    exact hspanCompletion
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [hspan]
  have hnotfield : ¬ IsField R := by
    intro hfield
    have : (maximalIdeal R).spanFinrank = 0 := by
      rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield]
      exact Submodule.spanFinrank_bot
    omega
  have hnotzero : ¬ ringKrullDim R ≤ 0 := by
    intro hzero
    let _ : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr hzero
    exact hnotfield Ring.KrullDimLE.isField_of_isDomain
  simpa using (ENat.WithBot.add_one_le_iff (n := 0)).mpr
    (lt_of_not_ge hnotzero)
