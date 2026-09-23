module

public import Mathlib.RingTheory.Regular.LinearMap

/-!
# Regular elements in an ideal and associated primes

Over a Noetherian ring, the zero divisors on a finite module are the union of its
associated primes.  Finite prime avoidance therefore says that an ideal contains an
element regular on the module exactly when it is contained in no associated prime.

This is the grade-one associated-prime input in the Buchsbaum--Eisenbud acyclicity
criterion.

Main declaration:

* `Ideal.exists_mem_isSMulRegular_iff_forall_associatedPrime_not_le`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v

open Module

namespace Ideal

/-- An ideal contains an element regular on a finite module exactly when it is contained
in no associated prime of that module. -/
theorem exists_mem_isSMulRegular_iff_forall_associatedPrime_not_le
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.Finite R M] (I : Ideal R) :
    (∃ r : R, r ∈ I ∧ IsSMulRegular M r) ↔
      ∀ p ∈ associatedPrimes R M, ¬I ≤ p := by
  constructor
  · rintro ⟨r, hrI, hreg⟩ p hp hIp
    have hrp : r ∈ p := hIp hrI
    have hunion : r ∈ ⋃ p ∈ associatedPrimes R M, p := by
      exact Set.mem_iUnion₂.mpr ⟨p, hp, hrp⟩
    rw [biUnion_associatedPrimes_eq_compl_regular R M] at hunion
    exact hunion hreg
  · intro havoid
    cases subsingleton_or_nontrivial M with
    | inl _ =>
        exact ⟨0, I.zero_mem, IsSMulRegular.zero⟩
    | inr _ =>
        by_contra! hnone
        have hsubset : (I : Set R) ⊆ ⋃ p ∈ associatedPrimes R M, p := by
          rw [biUnion_associatedPrimes_eq_compl_regular R M]
          exact fun r hrI ↦ hnone r hrI
        obtain ⟨p, hp⟩ := associatedPrimes.nonempty R M
        obtain ⟨q, hq, hIq⟩ :=
          (I.subset_union_prime_finite
            (associatedPrimes.finite R M) p p
            (fun q hq _ _ ↦ IsAssociatedPrime.isPrime hq)).mp hsubset
        exact havoid q hq hIq

end Ideal

end
