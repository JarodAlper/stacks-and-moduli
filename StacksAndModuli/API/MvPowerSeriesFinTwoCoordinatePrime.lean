module

public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Coordinate prime ideals in two-variable power series

This file records that each coordinate variable generates a prime ideal in the
two-variable formal power series ring over a domain.  These algebraic facts are the
reusable input for proving that the standard node ideal `(xy)` is radical.

## Main results

* `mvPowerSeriesFinTwo_span_X_zero_isPrime`;
* `mvPowerSeriesFinTwo_span_X_one_isPrime`.
-/

@[expose] public section

universe u

/-- The first coordinate variable generates a prime ideal in a two-variable formal
power series ring over a domain. -/
theorem mvPowerSeriesFinTwo_span_X_zero_isPrime
    (k : Type u) [CommRing k] [IsDomain k] :
    (Ideal.span ({MvPowerSeries.X (0 : Fin 2)} :
      Set (MvPowerSeries (Fin 2) k))).IsPrime := by
  let e := (MvPowerSeries.finSuccEquiv k 1).toRingEquiv
  let _ : IsDomain (MvPowerSeries (Fin 1) k) := NoZeroDivisors.to_isDomain _
  have hmap : Ideal.map e
      (Ideal.span ({MvPowerSeries.X (0 : Fin 2)} :
        Set (MvPowerSeries (Fin 2) k))) =
      Ideal.span ({PowerSeries.X} :
        Set (PowerSeries (MvPowerSeries (Fin 1) k))) := by
    rw [Ideal.map_span]
    simp [e]
  have hprime : (Ideal.map e
      (Ideal.span ({MvPowerSeries.X (0 : Fin 2)} :
        Set (MvPowerSeries (Fin 2) k)))).IsPrime := by
    rw [hmap]
    exact PowerSeries.span_X_isPrime
  have hcomap := hprime.comap e
  simpa only [Ideal.comap_map_of_bijective e e.bijective] using hcomap

/-- The second coordinate variable generates a prime ideal in a two-variable formal
power series ring over a domain. -/
theorem mvPowerSeriesFinTwo_span_X_one_isPrime
    (k : Type u) [CommRing k] [IsDomain k] :
    (Ideal.span ({MvPowerSeries.X (1 : Fin 2)} :
      Set (MvPowerSeries (Fin 2) k))).IsPrime := by
  let e : MvPowerSeries (Fin 2) k ≃+* MvPowerSeries (Fin 2) k :=
    (MvPowerSeries.renameEquiv k (Equiv.swap (0 : Fin 2) (1 : Fin 2))).toRingEquiv
  have hmap : Ideal.map e
      (Ideal.span ({MvPowerSeries.X (1 : Fin 2)} :
        Set (MvPowerSeries (Fin 2) k))) =
      Ideal.span ({MvPowerSeries.X (0 : Fin 2)} :
        Set (MvPowerSeries (Fin 2) k)) := by
    rw [Ideal.map_span]
    simp [e]
  have hprime : (Ideal.map e
      (Ideal.span ({MvPowerSeries.X (1 : Fin 2)} :
        Set (MvPowerSeries (Fin 2) k)))).IsPrime := by
    rw [hmap]
    exact mvPowerSeriesFinTwo_span_X_zero_isPrime k
  have hcomap := hprime.comap e
  simpa only [Ideal.comap_map_of_bijective e e.bijective] using hcomap
