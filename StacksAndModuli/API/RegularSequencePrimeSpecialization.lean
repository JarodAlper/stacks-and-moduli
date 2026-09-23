module

public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Regular.Flat

/-!
# Passing regularity from a specialization to a prime

If `p ⊆ q` are prime ideals and a sequence contained in `p` is regular after
localization at `q`, then it is regular after localization at `p`.  The proof first
localizes `R_q` at the extension of `p`, then identifies that iterated localization with
`R_p`.

This is the specialization step used to reduce regularity at an arbitrary point of a
Jacobson finite-type fibre to regularity at a closed point in the same open neighbourhood.

Main declaration:

* `Ideal.exists_isMaximal_over_notMem_of_isJacobsonRing`;
* `RingTheory.Sequence.IsRegular.localizationAtPrime_of_le`.
-/

@[expose] public section

noncomputable section

universe u

namespace Ideal

/-- In a Jacobson ring, every basic open neighbourhood of a prime contains a maximal
specialization of that prime. -/
theorem exists_isMaximal_over_notMem_of_isJacobsonRing
    {R : Type u} [CommRing R] [IsJacobsonRing R]
    (p : Ideal R) [p.IsPrime] {f : R} (hf : f ∉ p) :
    ∃ m : Ideal R, m.IsMaximal ∧ p ≤ m ∧ f ∉ m := by
  by_contra hnone
  push Not at hnone
  apply hf
  have hj : p.jacobson = p :=
    (isJacobsonRing_iff_prime_eq.mp inferInstance) p inferInstance
  rw [← hj, Ideal.jacobson, Ideal.mem_sInf]
  intro m hm
  exact hnone m hm.2 hm.1

end Ideal

namespace RingTheory.Sequence.IsRegular

/-- Regularity at a larger prime specializes backwards to regularity at a smaller prime
containing the sequence. -/
theorem localizationAtPrime_of_le
    {R : Type u} [CommRing R]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime]
    (hpq : p ≤ q) (rs : List R) (hmem : ∀ x ∈ rs, x ∈ p)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime q)
      (rs.map (algebraMap R (Localization.AtPrime q)))) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime p)
      (rs.map (algebraMap R (Localization.AtPrime p))) := by
  let Rq := Localization.AtPrime q
  let Rp := Localization.AtPrime p
  let pRq : Ideal Rq := p.map (algebraMap R Rq)
  have hdisj : Disjoint (q.primeCompl : Set R) (p : Set R) := by
    rw [Set.disjoint_left]
    intro x hxq hxp
    exact hxq (hpq hxp)
  letI : pRq.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl Rq p inferInstance hdisj
  let T := Localization.AtPrime pRq
  have hpRq_under : pRq.under R = p :=
    IsLocalization.under_map_of_isPrime_disjoint
      q.primeCompl Rq inferInstance hdisj
  letI : IsLocalization.AtPrime T p := by
    have hloc : IsLocalization.AtPrime T (pRq.under R) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        q.primeCompl T pRq
    change IsLocalization (pRq.under R).primeCompl T at hloc
    change IsLocalization p.primeCompl T
    have hcompl : (pRq.under R).primeCompl = p.primeCompl := by
      ext x
      change (x ∉ pRq.under R) ↔ (x ∉ p)
      rw [hpRq_under]
    exact hcompl ▸ hloc
  have hmemRq : ∀ x ∈ rs.map (algebraMap R Rq), x ∈ pRq := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact Ideal.mem_map_of_mem (algebraMap R Rq) (hmem r hr)
  have hregT : RingTheory.Sequence.IsRegular T
      ((rs.map (algebraMap R Rq)).map (algebraMap Rq T)) :=
    hreg.toIsWeaklyRegular.isRegular_of_isLocalization_of_mem T pRq hmemRq
  have hmapsT :
      (rs.map (algebraMap R Rq)).map (algebraMap Rq T) =
        rs.map (algebraMap R T) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r _
    exact IsScalarTower.algebraMap_apply R Rq T r
  have hregT' : RingTheory.Sequence.IsRegular T
      (rs.map (algebraMap R T)) := by
    rw [← hmapsT]
    exact hregT
  let e : T ≃ₐ[R] Rp := IsLocalization.algEquiv p.primeCompl T Rp
  let eRing : T ≃+* Rp := e.toRingEquiv
  letI : RingHomInvPair (eRing : T →+* Rp) eRing.symm :=
    RingHomInvPair.of_ringEquiv eRing
  letI : RingHomInvPair (eRing.symm : Rp →+* T) eRing :=
    RingHomInvPair.of_ringEquiv_symm eRing
  let eLin : T ≃ₛₗ[(eRing : T →+* Rp)] Rp :=
    eRing.toSemilinearEquiv
  have hregRp : RingTheory.Sequence.IsRegular Rp
      ((rs.map (algebraMap R T)).map (eRing : T →+* Rp)) :=
    (eLin.isRegular_congr' (rs.map (algebraMap R T))).mp hregT'
  have hmaps :
      (rs.map (algebraMap R T)).map (eRing : T →+* Rp) =
        rs.map (algebraMap R Rp) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro r _
    exact e.commutes r
  rw [hmaps] at hregRp
  exact hregRp

end RingTheory.Sequence.IsRegular

end

end
