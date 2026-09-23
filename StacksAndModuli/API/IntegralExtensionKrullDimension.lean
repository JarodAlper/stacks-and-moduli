module

public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Krull dimension of an injective integral extension

An integral extension cannot increase Krull dimension: incomparability makes contraction
strictly monotone on chains of prime ideals.  If the algebra map is injective, lying over and
going up lift every finite chain in the coefficient ring, so the two Krull dimensions agree.

This supplies the dimension comparison needed to recover the exact number of parameters in
Noether normalization.

Main declarations:

* `Algebra.IsIntegral.ringKrullDim_le`;
* `Algebra.IsIntegral.ringKrullDim_eq_of_injective`.
-/

@[expose] public section

noncomputable section

universe u v

namespace Algebra.IsIntegral

/-- The Krull dimension of an integral algebra is at most that of its coefficient ring. -/
theorem ringKrullDim_le
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R := by
  change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
  apply Order.krullDim_le_of_strictMono
    (PrimeSpectrum.comap (algebraMap R S))
  intro P Q hPQ
  change P.asIdeal.under R < Q.asIdeal.under R
  exact Ideal.IsIntegral.comap_lt_comap hPQ

/-- An injective integral algebra has the same Krull dimension as its coefficient ring. -/
theorem ringKrullDim_eq_of_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim S = ringKrullDim R := by
  apply le_antisymm ringKrullDim_le
  let _ : FaithfulSMul R S :=
    (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
  rw [Order.krullDim, Order.krullDim]
  apply iSup_le
  intro l
  obtain ⟨P, hP⟩ := Algebra.IsIntegral.comap_surjective R S l.head
  let _ : P.asIdeal.LiesOver l.head.asIdeal := ⟨by
    have h := congrArg (fun q : PrimeSpectrum R ↦ q.asIdeal) hP
    exact h.symm⟩
  obtain ⟨L, hlength, _, _⟩ :=
    Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
  exact le_iSup_of_le L (by rw [hlength])

end Algebra.IsIntegral

end

end
