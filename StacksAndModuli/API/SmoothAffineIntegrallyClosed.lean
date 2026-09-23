module

public import StacksAndModuli.API.RegularDimensionOneIntegrallyClosed
public import StacksAndModuli.API.SmoothStalkReduced

/-!
# Regularity and normality of smooth affine curves

For an affine scheme smooth over a field, every prime localization of its global-section
ring is identified with a regular local stalk.  Hence the global-section ring is regular.
If the scheme is integral and has topological Krull dimension at most one, this ring is
also an integrally closed domain.

## Main results

* `AlgebraicGeometry.Scheme.isRegularRing_globalSections_of_smooth_toSpec_field`:
  global sections of a smooth affine scheme over a field form a regular ring.
* `AlgebraicGeometry.Scheme.isIntegrallyClosed_globalSections_of_smooth_toSpec_field_of_dim_le_one`:
  global sections of an integral smooth affine curve are integrally closed.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- Global sections of an affine scheme smooth over a field form a regular ring. -/
theorem isRegularRing_globalSections_of_smooth_toSpec_field
    {K : Type u} [Field K] (X : Scheme.{u}) [IsAffine X]
    (f : X ⟶ Spec (.of K)) [Smooth f] : IsRegularRing Γ(X, ⊤) := by
  let hbase := isAffineOpen_top (Spec (.of K))
  let htop := isAffineOpen_top X
  let e : K ≃+* Γ(Spec (.of K), ⊤) :=
    (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv
  let _ : Field Γ(Spec (.of K), ⊤) :=
    (e.symm.isField (Field.toIsField K)).toField
  let φ := f.appLE (⊤ : (Spec (.of K)).Opens) (⊤ : X.Opens) (by simp)
  have hφ : φ.hom.Smooth := f.smooth_appLE hbase htop (by simp)
  algebraize [φ.hom]
  let _ : Algebra.Smooth Γ(Spec (.of K), ⊤) Γ(X, ⊤) := by
    rw [← RingHom.smooth_algebraMap]
    exact hφ
  let _ : IsNoetherianRing Γ(X, ⊤) :=
    Algebra.FiniteType.isNoetherianRing Γ(Spec (.of K), ⊤) Γ(X, ⊤)
  rw [isRegularRing_iff]
  intro p inst
  let _ : p.IsPrime := inst
  let y : PrimeSpectrum Γ(X, ⊤) := ⟨p, inst⟩
  let x : X := htop.fromSpec y
  have hx : (f.stalkMap x).hom.FormallySmooth := by
    rw [← Scheme.Hom.mem_smoothLocus, f.smoothLocus_eq_top]
    trivial
  let _ : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_formallySmooth_toSpec_field f x hx
  let _ : Algebra Γ(X, ⊤) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf
      (⟨x, by trivial⟩ : (⊤ : X.Opens))
  let _ : IsLocalization.AtPrime (X.presheaf.stalk x) p :=
    htop.isLocalization_stalk' y trivial
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl
      (X.presheaf.stalk x) (Localization.AtPrime p)).toRingEquiv

/-- Global sections of an integral smooth affine scheme of topological Krull dimension at
most one form an integrally closed domain. -/
theorem isIntegrallyClosed_globalSections_of_smooth_toSpec_field_of_dim_le_one
    {K : Type u} [Field K] (X : Scheme.{u}) [IsAffine X] [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [Smooth f]
    (hdim : topologicalKrullDim X ≤ 1) : IsIntegrallyClosed Γ(X, ⊤) := by
  let _ : IsRegularRing Γ(X, ⊤) :=
    isRegularRing_globalSections_of_smooth_toSpec_field X f
  have hspec : topologicalKrullDim (Spec Γ(X, ⊤)) ≤ 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq X.isoSpec.hom
      X.isoSpec.hom.homeomorph.isHomeomorph]
    exact hdim
  have hring : ringKrullDim Γ(X, ⊤) ≤ 1 := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hspec
  let _ : Ring.KrullDimLE 1 Γ(X, ⊤) := Ring.krullDimLE_iff.mpr hring
  let _ : Ring.DimensionLEOne Γ(X, ⊤) :=
    Ring.DimensionLEOne.of_krullDimLE_one Γ(X, ⊤)
  exact IsIntegrallyClosed.of_isRegularRing_of_dimensionLEOne Γ(X, ⊤)

end AlgebraicGeometry.Scheme

end
