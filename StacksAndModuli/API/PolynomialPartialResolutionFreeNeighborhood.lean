module

public import StacksAndModuli.API.PolynomialPartialResolutionClosedFibre
public import StacksAndModuli.API.FinitePresentationFreeNeighborhood
public import StacksAndModuli.API.FlatLocal

/-!
# Projective neighbourhoods of polynomial syzygies

Let `A` be Noetherian local and let `q` be a prime of `A[x_i]` over the closed point.
For a sufficiently long finite partial projective resolution of an `A`-flat module, the
terminal syzygy is free at `q` and hence projective on a principal neighbourhood of `q`.

This assembles the closed-fibre regularity theorem, local lifting, localization of external
coefficient flatness, and openness of the finite-presentation free locus.  It is the
syzygy-neighbourhood step immediately preceding relative fibre-exactness spreading in the
Noetherian proof of openness of relative flatness.

Main declaration:

* `Module.IsPartialProjectiveResolution.exists_away_free_final_of_flat`;
* `Module.IsPartialProjectiveResolution.exists_away_projective_final_of_flat`.
-/

@[expose] public section

universe u

noncomputable section

open TensorProduct

namespace Module.IsPartialProjectiveResolution

set_option linter.style.haveILetI false

/-- The terminal syzygy of a sufficiently long polynomial resolution of a
coefficient-flat module is free on a principal neighbourhood of a prime over the closed
coefficient point. -/
theorem exists_away_free_final_of_flat
    {A sigma : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [Finite sigma]
    (q : PrimeSpectrum (MvPolynomial sigma A))
    (hq : (q.comap
      (MvPolynomial.C : A →+* MvPolynomial sigma A)).asIdeal =
        IsLocalRing.maximalIdeal A)
    {e : ℕ} {M K : Type u}
    [AddCommGroup M] [Module (MvPolynomial sigma A) M]
    [AddCommGroup K] [Module (MvPolynomial sigma A) K]
    [Module.Finite (MvPolynomial sigma A) M]
    [Module.Finite (MvPolynomial sigma A) K]
    (hres : Module.IsPartialProjectiveResolution
      (MvPolynomial sigma A) e M K)
    (hM : @Module.Flat A M _ _
      (Module.compHom M (algebraMap A (MvPolynomial sigma A))))
    (he : Nat.card sigma - 1 ≤ e) :
    ∃ f : MvPolynomial sigma A, f ∉ q.asIdeal ∧
      Module.Free (Localization.Away f)
        (LocalizedModule.Away f K) := by
  let S := MvPolynomial sigma A
  let T := Localization.AtPrime q.asIdeal
  let MT := T ⊗[S] M
  let KT := T ⊗[S] K
  have hresT : Module.IsPartialProjectiveResolution T e MT KT :=
    hres.baseChange T
  have hMT : @Module.Flat A MT _ _
      (Module.compHom MT (algebraMap A T)) := by
    let modDefault : Module A MT := inferInstance
    letI : Module A M := Module.compHom M (algebraMap A S)
    letI : IsScalarTower A S M := IsScalarTower.of_compHom A S M
    letI : Module.Flat A M := hM
    let res : M →ₗ[S] MT := TensorProduct.mk S T M 1
    letI : IsLocalizedModule q.asIdeal.primeCompl res :=
      (isLocalizedModule_iff_isBaseChange q.asIdeal.primeCompl T res).mpr
        (TensorProduct.isBaseChange S M T)
    have hflatDefault : @Module.Flat A MT _ _ modDefault :=
      Module.Flat.of_isLocalizedModule_of_flat_base
        (N := M) (Nₗ := MT) A q.asIdeal.primeCompl res
    have hmodule : modDefault = Module.compHom MT (algebraMap A T) := by
      apply Module.ext
      funext a x
      exact (IsScalarTower.algebraMap_smul T a x).symm
    exact hmodule ▸ hflatDefault
  have hfreeT : Module.Free T KT :=
    hresT.free_polynomialLocalization_of_flat q hq hMT he
  let _ : Module.FinitePresentation S K :=
    Module.finitePresentation_of_finite S K
  exact Module.FinitePresentation.exists_away_free_of_free_atPrime q hfreeT

/-- Projective form of `exists_away_free_final_of_flat`. -/
theorem exists_away_projective_final_of_flat
    {A sigma : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [Finite sigma]
    (q : PrimeSpectrum (MvPolynomial sigma A))
    (hq : (q.comap
      (MvPolynomial.C : A →+* MvPolynomial sigma A)).asIdeal =
        IsLocalRing.maximalIdeal A)
    {e : ℕ} {M K : Type u}
    [AddCommGroup M] [Module (MvPolynomial sigma A) M]
    [AddCommGroup K] [Module (MvPolynomial sigma A) K]
    [Module.Finite (MvPolynomial sigma A) M]
    [Module.Finite (MvPolynomial sigma A) K]
    (hres : Module.IsPartialProjectiveResolution
      (MvPolynomial sigma A) e M K)
    (hM : @Module.Flat A M _ _
      (Module.compHom M (algebraMap A (MvPolynomial sigma A))))
    (he : Nat.card sigma - 1 ≤ e) :
    ∃ f : MvPolynomial sigma A, f ∉ q.asIdeal ∧
      Module.Projective (Localization.Away f)
        (LocalizedModule.Away f K) := by
  obtain ⟨f, hf, hfree⟩ := hres.exists_away_free_final_of_flat q hq hM he
  let _ : Module.Free (Localization.Away f) (LocalizedModule.Away f K) := hfree
  exact ⟨f, hf, Module.Projective.of_free⟩

end Module.IsPartialProjectiveResolution

end

end
