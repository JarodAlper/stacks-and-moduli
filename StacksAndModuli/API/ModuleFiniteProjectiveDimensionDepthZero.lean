module

public import StacksProject.Algebra.RegularFiniteGlDim.ProjectiveDimension

/-!
# Finite projective dimension at depth zero

Over a Noetherian local ring whose maximal ideal is associated to the ring, every finite
module of finite projective dimension is projective.  The proof repeatedly takes a minimal
finite free cover.  Its kernel again has finite projective dimension, hence is free by
induction; if that kernel were nonzero, minimality would force the socle of the ring to
vanish, contradicting the associated-prime hypothesis.

The main declaration is:

* `Module.projective_of_hasProjectiveDimensionLE_of_maximalIdeal_mem_associatedPrimes`.
-/

@[expose] public section

universe u

open IsLocalRing

namespace Module

/-- A finite module of finite projective dimension over a Noetherian local ring whose
maximal ideal is associated to the ring is projective. -/
theorem projective_of_hasProjectiveDimensionLE_of_maximalIdeal_mem_associatedPrimes
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hass : maximalIdeal R ∈ associatedPrimes R R)
    {d : ℕ} (hpd : Module.HasProjectiveDimensionLE R d M) :
    Module.Projective R M := by
  induction d generalizing M with
  | zero =>
      exact (Module.hasProjectiveDimensionLE_zero_iff_projective R M).mp hpd
  | succ d ih =>
      obtain ⟨ι, _, f, hf, hminimal⟩ := Module.exists_minimal_finite_free_cover R M
      letI : Module.Finite R (LinearMap.ker f) :=
        Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      have hkerPD : Module.HasProjectiveDimensionLE R d (LinearMap.ker f) :=
        Module.hasProjectiveDimensionLE_domain_of_projective R f hf
          (LinearMap.ker f).subtype Subtype.val_injective
          (Submodule.range_subtype _) hpd
      letI : Module.Projective R (LinearMap.ker f) := ih hkerPD
      letI : Module.Free R (LinearMap.ker f) :=
        Module.free_of_flat_of_isLocalRing
      have hker : LinearMap.ker f = ⊥ := by
        by_contra hne
        letI : Nontrivial (LinearMap.ker f) :=
          Submodule.nontrivial_iff_ne_bot.mpr hne
        have hsocle :
            ∃ r : R, r ≠ 0 ∧ ∀ a ∈ maximalIdeal R, a • r = 0 :=
          (Module.maximalIdeal_mem_associatedPrimes_iff).mp hass
        exact
          (Module.not_exists_annihilated_by_maximalIdeal_of_minimal_injection
            (LinearMap.ker f).subtype Subtype.val_injective
            (by simpa only [Submodule.range_subtype] using hminimal))
            hsocle
      exact Module.Projective.of_equiv
        (LinearEquiv.ofBijective f ⟨LinearMap.ker_eq_bot.mp hker, hf⟩)

end Module

end
