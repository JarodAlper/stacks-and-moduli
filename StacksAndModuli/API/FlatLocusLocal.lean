module

public import StacksAndModuli.API.FlatLocal
public import StacksAndModuli.API.FlatSourceLocalAtMaximal
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Gluing source-local flatness over a coefficient ring

Flatness of an `S`-module over a coefficient ring `R` can be checked on basic opens of
`Spec S`.  The basic opens need not be chosen in advance: if every prime of `S` has one
flat basic-open neighbourhood, the set of all such neighbourhoods spans the unit ideal, and
the source-local flatness theorem applies.

This is the gluing part of the flat-locus argument used in Stacks Project tag 02JO.  It does
not prove that flat neighbourhoods exist; that is the local eventual-flatness input of tags
00R6 and 00MO.
-/

@[expose] public section

noncomputable section

universe u v w

open TensorProduct

namespace Module.Flat

/-- If the localization of an `S`-module at every point of a basic open is flat over an
external coefficient ring `R`, then its localization on that basic open is flat over `R`.

The proof checks flatness after localizing at each maximal ideal of `S_f`.  Such an iterated
localization is canonically the localization at the corresponding prime of `S`; tensor
cancellation identifies the two localized module models. -/
theorem away_of_forall_mem_basicOpen_flat_localizationAtPrime
    {R : Type u} {S : Type v} {M : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (f : S)
    (hlocal : ∀ q : PrimeSpectrum S,
      q ∈ PrimeSpectrum.basicOpen f →
        Module.Flat R (Localization.AtPrime q.asIdeal ⊗[S] M)) :
    Module.Flat R (LocalizedModule.Away f M) := by
  let A := Localization.Away f
  let N := LocalizedModule.Away f M
  change Module.Flat R N
  apply Module.Flat.of_forall_maximal_localization_over_source (S := A) (M := N)
  intro J hJ
  let q : PrimeSpectrum S :=
    PrimeSpectrum.comap (algebraMap S A) ⟨J, hJ.isPrime⟩
  have hq : q ∈ PrimeSpectrum.basicOpen f := by
    change q ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum S))
    rw [← PrimeSpectrum.localization_away_comap_range A f]
    exact ⟨⟨J, hJ.isPrime⟩, rfl⟩
  have hqflat := hlocal q hq
  let U := Localization.AtPrime q.asIdeal
  let T := Localization.AtPrime J
  let L := LocalizedModule J.primeCompl N
  change Module.Flat R L
  let _ : IsLocalization.AtPrime T q.asIdeal := by
    change IsLocalization.AtPrime T (J.comap (algebraMap S A))
    exact IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (T := T) (Submonoid.powers f) J
  let eRing : U ≃ₐ[S] T :=
    IsLocalization.algEquiv q.asIdeal.primeCompl U T
  let eTensor : (U ⊗[S] M) ≃ₗ[S] (T ⊗[S] M) :=
    TensorProduct.congr eRing.toLinearEquiv (LinearEquiv.refl S M)
  let _ : Module.Flat R (U ⊗[S] M) := hqflat
  have hTflat : Module.Flat R (T ⊗[S] M) :=
    Module.Flat.of_linearEquiv (eTensor.symm.restrictScalars R)
  let eLocalized : L ≃ₗ[T] T ⊗[A] N :=
    LocalizedModule.equivTensorProduct J.primeCompl N
  let eAway : N ≃ₗ[A] A ⊗[S] M :=
    LocalizedModule.equivTensorProduct (Submonoid.powers f) M
  let eReplace : (T ⊗[A] N) ≃ₗ[T] (T ⊗[A] (A ⊗[S] M)) :=
    TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl T T) eAway
  let eCancel : (T ⊗[A] (A ⊗[S] M)) ≃ₗ[T] (T ⊗[S] M) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange S A T T M
  let eTarget : L ≃ₗ[T] (T ⊗[S] M) :=
    eLocalized.trans (eReplace.trans eCancel)
  let _ : Module.Flat R (T ⊗[S] M) := hTflat
  exact Module.Flat.of_linearEquiv (eTarget.restrictScalars R)

/-- If every prime of the source algebra has a basic-open neighbourhood on which a module is
flat over the coefficient ring, then the original module is flat over that coefficient ring.
-/
theorem of_forall_prime_exists_away
    {R : Type u} {S : Type v} {M : Type w} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
    (h : ∀ q : PrimeSpectrum S, ∃ f : S, f ∉ q.asIdeal ∧
      Module.Flat R (LocalizedModule.Away f M)) : Module.Flat R M := by
  let s : Set S := {f | Module.Flat R (LocalizedModule.Away f M)}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span s) hne
    let q : PrimeSpectrum S := ⟨m, hm.isPrime⟩
    obtain ⟨f, hf, hflat⟩ := h q
    exact hf (hle (Ideal.subset_span hflat))
  let Mₗ : s → Type max v w := fun f ↦ LocalizedModule.Away f.1 M
  let res : ∀ f : s, M →ₗ[S] Mₗ f := fun f ↦
    LocalizedModule.mkLinearMap (Submonoid.powers f.1) M
  apply Module.Flat.of_isLocalizedModule_span_of_isScalarTower s hs Mₗ res
  intro f
  exact f.2

end Module.Flat

end
