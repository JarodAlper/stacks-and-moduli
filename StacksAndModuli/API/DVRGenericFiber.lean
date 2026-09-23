module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The generic fibre over a discrete valuation ring

Supporting API with no Stacks Project counterpart of its own, used by the formalization of
`prop:quot-proper` in §2.4: over a discrete valuation ring `R` with fraction field `K`, the
morphism `Spec K → Spec R` is an *open immersion* — the inclusion of the generic point, which
is open because `Spec R` has exactly two points and the closed point is closed.  Concretely,
`K = R[1/ϖ]` for any uniformizer `ϖ`, so `Spec K = D(ϖ)`.

Consequently the generic fibre `X_K → X_R` of any scheme over `R` is an open immersion (base
change), which is what lets the valuative criterion for the Quot functor treat the generic
fibre as an honest open subscheme and extend quotients by images of pushforwards along it.

Main declarations:
- `IsDiscreteValuationRing.isLocalization_away_of_irreducible`: `K` is the localization of a
  DVR away from any uniformizer;
- `IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing`: `Spec K → Spec R` is an
  open immersion;
- `IsDiscreteValuationRing.isOpenImmersion_pullback_fst_fractionRing`: the generic fibre of
  a scheme over `Spec R` is an open immersion.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace IsDiscreteValuationRing

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The fraction field of a discrete valuation ring is its localization away from any
uniformizer: every nonzero element is a unit multiple of a power of `ϖ`, so inverting `ϖ`
already inverts every nonzero denominator. -/
theorem isLocalization_away_of_irreducible {ϖ : R} (hϖ : Irreducible ϖ)
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] :
    IsLocalization.Away ϖ K := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · -- powers of the uniformizer become units
    rintro ⟨y, n, rfl⟩
    rw [map_pow]
    refine IsUnit.pow n (isUnit_iff_ne_zero.mpr ?_)
    simpa [map_eq_zero_iff _ (IsFractionRing.injective R K)] using hϖ.ne_zero
  · -- every fraction has a `ϖ`-power denominator
    intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hb0 hϖ
    refine ⟨⟨a * ((u⁻¹ : Rˣ) : R), ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
    have hϖn : (algebraMap R K) (ϖ ^ n) ≠ 0 := by
      simp only [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R K)]
      exact pow_ne_zero n hϖ.ne_zero
    have hu : (algebraMap R K) ((u : Rˣ) : R) ≠ 0 := by
      simp [map_eq_zero_iff _ (IsFractionRing.injective R K)]
    have huinv : (algebraMap R K) ((u⁻¹ : Rˣ) : R) =
        ((algebraMap R K) ((u : Rˣ) : R))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← map_mul]
      norm_cast
      rw [inv_mul_cancel, Units.val_one]
      exact map_one _
    show (algebraMap R K) a / (algebraMap R K) ((u : Rˣ) * ϖ ^ n) *
        (algebraMap R K) (ϖ ^ n) = (algebraMap R K) (a * ((u⁻¹ : Rˣ) : R))
    rw [map_mul, map_mul, huinv]
    field_simp
  · -- injectivity gives the equality criterion
    intro x y hxy
    exact ⟨1, by simpa using IsFractionRing.injective R K hxy⟩

open AlgebraicGeometry CategoryTheory Limits

/-- **The generic point of a DVR is an open immersion**: `Spec K → Spec R` is an open
immersion onto the basic open `D(ϖ)`. -/
theorem isOpenImmersion_specMap_fractionRing
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  haveI := isLocalization_away_of_irreducible hϖ K
  exact IsOpenImmersion.of_isLocalization ϖ

/-- The range of the generic-point inclusion of a discrete valuation ring is the basic
open of any uniformizer. -/
theorem opensRange_specMap_fractionRing {ϖ : R} (hϖ : Irreducible ϖ)
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K] :
    letI := isOpenImmersion_specMap_fractionRing (R := R) K
    (Spec.map (CommRingCat.ofHom (algebraMap R K))).opensRange =
      (Spec (CommRingCat.of R)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ϖ) := by
  letI := isOpenImmersion_specMap_fractionRing (R := R) K
  haveI := isLocalization_away_of_irreducible hϖ (K := K)
  rw [basicOpen_eq_of_affine]
  exact TopologicalSpace.Opens.ext
    (PrimeSpectrum.localization_away_comap_range K ϖ)

/-- The generic fibre of a scheme over a discrete valuation ring is an open immersion. -/
theorem isOpenImmersion_pullback_fst_fractionRing
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R)) :
    IsOpenImmersion (Limits.pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap R K)))) := by
  haveI := isOpenImmersion_specMap_fractionRing (R := R) K
  infer_instance

end IsDiscreteValuationRing

end
