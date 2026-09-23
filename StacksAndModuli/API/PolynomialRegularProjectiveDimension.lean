module

public import StacksProject.Algebra.RegularFiniteGlDim.ProjectiveDimension
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Projective-dimension bounds over polynomial rings over fields

A polynomial ring in a finite set of variables over a field is regular of Krull dimension
the number of variables.  Combining this with the local projective-dimension theorem gives
the corresponding uniform bound both globally and after localization at a prime.

These are the regular-fibre homological bounds used in the Noetherian proof of openness of
the relative flat locus.  Once a finite partial resolution stays exact on the coefficient
fibre, its final syzygy is projective over the fibre ring and finite free after localization
at a prime.

Main declarations:

* `Module.hasProjectiveDimensionLE_localizationAtPrime_mvPolynomial_of_field`;
* `Module.hasProjectiveDimensionLE_mvPolynomial_of_field`;
* `Module.IsPartialProjectiveResolution.projective_mvPolynomial_of_field`;
* `Module.IsPartialProjectiveResolution.projective_localizationAtPrime_mvPolynomial_of_field`;
* `Module.IsPartialProjectiveResolution.free_localizationAtPrime_mvPolynomial_of_field`.
-/

@[expose] public section

set_option linter.style.haveILetI false

universe u

open CategoryTheory

namespace Module

/-- A finite module over a prime localization of a polynomial ring in `n` variables over a
field has projective dimension at most `n`. -/
theorem hasProjectiveDimensionLE_localizationAtPrime_mvPolynomial_of_field
    (k sigma : Type u) [Field k] [Finite sigma]
    (q : PrimeSpectrum (MvPolynomial sigma k))
    (M : Type u) [AddCommGroup M]
    [Module (Localization.AtPrime q.asIdeal) M]
    [Module.Finite (Localization.AtPrime q.asIdeal) M] :
    Module.HasProjectiveDimensionLE
      (Localization.AtPrime q.asIdeal) (Nat.card sigma) M := by
  let S := MvPolynomial sigma k
  let T := Localization.AtPrime q.asIdeal
  haveI : IsRegularRing S := MvPolynomial.isRegularRing_of_isRegularRing k
  haveI : IsRegularLocalRing T := inferInstance
  obtain ⟨s, _hs, hscard⟩ :=
    IsRegularLocalRing.maximalIdeal_generated_by_dim (R := T)
  have hcard : s.card ≤ Nat.card sigma := by
    have hcard' : (s.card : WithBot ℕ∞) ≤ (Nat.card sigma : WithBot ℕ∞) := by
      calc
        (s.card : WithBot ℕ∞) = ringKrullDim T := hscard
        _ = q.asIdeal.height :=
          IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal T
        _ ≤ ringKrullDim S := Ideal.height_le_ringKrullDim_of_isPrime
        _ = (Nat.card sigma : WithBot ℕ∞) := by
          simp [S]
    exact_mod_cast hcard'
  have hpd : Module.HasProjectiveDimensionLE T s.card M :=
    Module.hasProjectiveDimensionLE_of_isRegularLocalRing
      s.card T hscard.symm M
  exact CategoryTheory.hasProjectiveDimensionLT_of_ge
    (ModuleCat.of T M) (s.card + 1) (Nat.card sigma + 1)
      (Nat.add_le_add_right hcard 1)

/-- A finite module over a polynomial ring in `n` variables over a field has projective
dimension at most `n`. -/
theorem hasProjectiveDimensionLE_mvPolynomial_of_field
    (k sigma : Type u) [Field k] [Finite sigma]
    (M : Type u) [AddCommGroup M] [Module (MvPolynomial sigma k) M]
    [Module.Finite (MvPolynomial sigma k) M] :
    Module.HasProjectiveDimensionLE (MvPolynomial sigma k) (Nat.card sigma) M := by
  apply (ModuleCat.hasProjectiveDimensionLE_iff_forall_primeSpectrum
    (R := MvPolynomial sigma k) (Nat.card sigma)
      (ModuleCat.of (MvPolynomial sigma k) M)).mpr
  intro q
  let N := LocalizedModule q.asIdeal.primeCompl M
  haveI : Module.Finite (Localization.AtPrime q.asIdeal) N := inferInstance
  letI : Module.Finite (Localization.AtPrime q.asIdeal) (Shrink.{u} N) :=
    Module.Finite.equiv (Shrink.linearEquiv (Localization.AtPrime q.asIdeal) N).symm
  change Module.HasProjectiveDimensionLE
    (Localization.AtPrime q.asIdeal) (Nat.card sigma)
      (Shrink.{u} N)
  exact hasProjectiveDimensionLE_localizationAtPrime_mvPolynomial_of_field
    k sigma q (Shrink.{u} N)

namespace IsPartialProjectiveResolution

/-- Over a polynomial ring over a field, the final syzygy in a sufficiently long finite
partial projective resolution is projective. -/
theorem projective_mvPolynomial_of_field
    (k sigma : Type u) [Field k] [Finite sigma]
    {e : ℕ} {M K : Type u}
    [AddCommGroup M] [Module (MvPolynomial sigma k) M]
    [AddCommGroup K] [Module (MvPolynomial sigma k) K]
    [Module.Finite (MvPolynomial sigma k) M]
    (hres : Module.IsPartialProjectiveResolution
      (MvPolynomial sigma k) e M K)
    (he : Nat.card sigma - 1 ≤ e) :
    Module.Projective (MvPolynomial sigma k) K :=
  hres.projective_of_projectiveDimension_le he
    (hasProjectiveDimensionLE_mvPolynomial_of_field k sigma M)

/-- After localization at a prime of a polynomial ring over a field, the final syzygy in a
sufficiently long finite partial projective resolution is projective. -/
theorem projective_localizationAtPrime_mvPolynomial_of_field
    (k sigma : Type u) [Field k] [Finite sigma]
    (q : PrimeSpectrum (MvPolynomial sigma k))
    {e : ℕ} {M K : Type u}
    [AddCommGroup M] [Module (Localization.AtPrime q.asIdeal) M]
    [AddCommGroup K] [Module (Localization.AtPrime q.asIdeal) K]
    [Module.Finite (Localization.AtPrime q.asIdeal) M]
    (hres : Module.IsPartialProjectiveResolution
      (Localization.AtPrime q.asIdeal) e M K)
    (he : Nat.card sigma - 1 ≤ e) :
    Module.Projective (Localization.AtPrime q.asIdeal) K :=
  hres.projective_of_projectiveDimension_le he
    (hasProjectiveDimensionLE_localizationAtPrime_mvPolynomial_of_field
      k sigma q M)

/-- A finite final syzygy as in
`projective_localizationAtPrime_mvPolynomial_of_field` is free over the local fibre ring. -/
theorem free_localizationAtPrime_mvPolynomial_of_field
    (k sigma : Type u) [Field k] [Finite sigma]
    (q : PrimeSpectrum (MvPolynomial sigma k))
    {e : ℕ} {M K : Type u}
    [AddCommGroup M] [Module (Localization.AtPrime q.asIdeal) M]
    [AddCommGroup K] [Module (Localization.AtPrime q.asIdeal) K]
    [Module.Finite (Localization.AtPrime q.asIdeal) M]
    [Module.Finite (Localization.AtPrime q.asIdeal) K]
    (hres : Module.IsPartialProjectiveResolution
      (Localization.AtPrime q.asIdeal) e M K)
    (he : Nat.card sigma - 1 ≤ e) :
    Module.Free (Localization.AtPrime q.asIdeal) K := by
  letI : Module.Projective (Localization.AtPrime q.asIdeal) K :=
    hres.projective_localizationAtPrime_mvPolynomial_of_field k sigma q he
  exact Module.free_of_flat_of_isLocalRing

end IsPartialProjectiveResolution

end Module

end
