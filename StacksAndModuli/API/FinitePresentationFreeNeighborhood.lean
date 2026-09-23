module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Principal neighbourhoods of free localizations

If a finitely presented module is free at one prime, its free locus contains a principal
open neighbourhood of that prime.  On that principal localization the module is projective.
For finite modules over a Noetherian ring, finite presentation is automatic.

This packages the free-locus step used after lifting the terminal closed-fibre syzygy in the
Noetherian proof of openness of relative flatness.

Main declarations:

* `Module.FinitePresentation.exists_away_free_of_free_atPrime`;
* `Module.FinitePresentation.exists_away_projective_of_free_atPrime`;
* `Module.FinitePresentation.exists_away_projective_of_finite_of_free_atPrime`.
-/

@[expose] public section

universe u

open PrimeSpectrum TensorProduct

namespace Module.FinitePresentation

/-- A free prime localization of a finitely presented module spreads to a principal
neighbourhood on which the module is free. -/
theorem exists_away_free_of_free_atPrime
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M]
    (q : PrimeSpectrum R)
    (hfree : Module.Free (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal ⊗[R] M)) :
    ∃ f : R, f ∉ q.asIdeal ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away f M) := by
  let T := Localization.AtPrime q.asIdeal
  let MT := T ⊗[R] M
  let res : M →ₗ[R] MT := TensorProduct.mk R T M 1
  let _ : IsLocalizedModule q.asIdeal.primeCompl res :=
    (isLocalizedModule_iff_isBaseChange q.asIdeal.primeCompl T res).mpr
      (TensorProduct.isBaseChange R M T)
  let _ : Module.Free T MT := hfree
  obtain ⟨f, hf, hfreeAway, _hrank⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers
      q.asIdeal.primeCompl res T
  exact ⟨f, hf, hfreeAway⟩

/-- A free prime localization of a finitely presented module spreads to a principal
neighbourhood on which the module is projective. -/
theorem exists_away_projective_of_free_atPrime
    {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M]
    (q : PrimeSpectrum R)
    (hfree : Module.Free (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal ⊗[R] M)) :
    ∃ f : R, f ∉ q.asIdeal ∧
      Module.Projective (Localization.Away f) (LocalizedModule.Away f M) := by
  have hq : q ∈ Module.freeLocus R M :=
    (Module.mem_freeLocus_iff_tensor q (Localization.AtPrime q.asIdeal)).mpr hfree
  obtain ⟨V, hVsub, hVopen, hqV⟩ :=
    (isOpen_iff_forall_mem_open.mp Module.isOpen_freeLocus) q hq
  obtain ⟨W, ⟨f, rfl⟩, hqW, hWsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqV hVopen
  exact ⟨f, hqW, Module.basicOpen_subset_freeLocus_iff.mp (hWsub.trans hVsub)⟩

/-- Over a Noetherian ring, a free prime localization of a finite module spreads to a
principal neighbourhood on which the module is projective. -/
theorem exists_away_projective_of_finite_of_free_atPrime
    {R M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (q : PrimeSpectrum R)
    (hfree : Module.Free (Localization.AtPrime q.asIdeal)
      (Localization.AtPrime q.asIdeal ⊗[R] M)) :
    ∃ f : R, f ∉ q.asIdeal ∧
      Module.Projective (Localization.Away f) (LocalizedModule.Away f M) := by
  let _ : Module.FinitePresentation R M :=
    Module.finitePresentation_of_finite R M
  exact exists_away_projective_of_free_atPrime q hfree

end Module.FinitePresentation

end
