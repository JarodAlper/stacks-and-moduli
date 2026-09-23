module

public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finite projective modules are free on a basic open around every prime

Supporting API with no Stacks Project counterpart.

The coordinate charts of the Grassmannian (§2.1–§2.2) trivialize a finite projective module on
a basic open neighbourhood of each prime, with the free rank equal to the rank at the stalk.
Mathlib has each ingredient — `Module.FinitePresentation.exists_free_localizedModule_powers`,
`Module.free_of_flat_of_isLocalRing`, `Module.rankAtStalk` — but not this packaging, which is
what the chart constructions consume.

Main declarations:
- `Module.exists_basicOpen_free_of_finite_projective`;
- `IsLocalization.Away.nontrivial_of_notMem`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v w

/-- A localization away from an element outside a prime ideal is nontrivial: if `S` were
trivial then `0 ∈ Submonoid.powers f`, i.e. some `f ^ n = 0 ∈ p`, forcing `f ∈ p`. -/
theorem IsLocalization.Away.nontrivial_of_notMem {R : Type u} [CommRing R] {f : R}
    {p : Ideal R} [hp : p.IsPrime] (hf : f ∉ p) (S : Type v) [CommRing S] [Algebra R S]
    [IsLocalization.Away f S] : Nontrivial S := by
  rw [← not_subsingleton_iff_nontrivial]
  intro h
  obtain ⟨n, hn⟩ :=
    (IsLocalization.subsingleton_iff (M := Submonoid.powers f) (S := S)).mp h
  have hn' : f ^ n = 0 := hn
  exact hf (hp.mem_of_pow_mem n (by rw [hn']; exact p.zero_mem))

/-- A finite projective module over a commutative ring is finite free on a basic open
neighbourhood of every prime, with free rank equal to the rank at the stalk. -/
theorem Module.exists_basicOpen_free_of_finite_projective
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (p : PrimeSpectrum R) :
    ∃ f : R, p ∈ PrimeSpectrum.basicOpen f ∧
      Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
      Module.finrank (Localization.Away f) (LocalizedModule.Away f M) =
        Module.rankAtStalk M p := by
  have hfp : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  have hfree : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) := Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, h1, h2⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
    (Localization.AtPrime p.asIdeal)
  exact ⟨f, (PrimeSpectrum.mem_basicOpen f p).mpr hf, h1, h2⟩
