module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.RingHom.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The Stein factorization object of a universally closed morphism

For a quasi-compact, quasi-separated, universally closed morphism `f : X ⟶ Y` —
in particular for any proper morphism — sections of `X` over the preimage of an
affine open of `Y` are integral over the base, so the integral closure defining
Mathlib's relative normalization is everything.  Consequently
`f.normalization` *is* the Stein factorization object `Spec_Y f_* 𝒪_X`:
its sections over `f.fromNormalization ⁻¹ᵁ U` are exactly `Γ(X, f ⁻¹ᵁ U)`
(`Scheme.Hom.steinObjIso`), computed by `f.toNormalization`
(`Scheme.Hom.steinObjIso_hom`), and `f = f.toNormalization ≫ f.fromNormalization`
with `f.fromNormalization` integral is the Stein factorization
(`Scheme.Hom.toNormalization_fromNormalization`, `IsIntegralHom` instance).
The finiteness of `f.fromNormalization` and the connectedness of the fibers of
`f.toNormalization` are the remaining, genuinely cohomological halves of the
Stein factorization theorem (coherence of proper pushforward and the theorem on
formal functions) and are not addressed here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- For a universally closed morphism, the map of sections over any affine open of
the target is integral. -/
theorem isIntegral_app_of_universallyClosed [UniversallyClosed f]
    {U : Y.Opens} (hU : IsAffineOpen U) : (f.app U).hom.IsIntegral := by
  have hAff : IsAffine U.toScheme := hU
  have htop := isIntegral_appTop_of_universallyClosed (f ∣_ U)
  rw [morphismRestrict_appTop, CommRingCat.hom_comp] at htop
  have h1 := (RingHom.isIntegral_respectsIso.cancel_right_isIso
    (f.app (U.ι ''ᵁ ⊤))
    (X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op)).mp htop
  have himg : U.ι ''ᵁ ⊤ = U := by simp
  rw [himg] at h1
  exact h1

variable [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f]

omit [QuasiCompact f] [QuasiSeparated f] in
/-- For a universally closed (qcqs) morphism, the integral closure defining the
relative normalization is everything: every section upstairs is integral over the
base. -/
theorem integralClosure_eq_top_of_universallyClosed
    {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U) = ⊤ := by
  let : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  rw [integralClosure_eq_top_iff, ← algebraMap_isIntegral_iff,
    RingHom.algebraMap_toAlgebra]
  exact f.isIntegral_app_of_universallyClosed hU

/-- The Stein factorization object: for a universally closed (qcqs) morphism, the
sections of the relative normalization over the preimage of an affine open are the
sections of `X` over its preimage — that is, `f.normalization` is
`Spec_Y f_* 𝒪_X`. -/
def steinObjIso {U : Y.Opens} (hU : IsAffineOpen U) :
    Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≅ Γ(X, f ⁻¹ᵁ U) :=
  letI := (f.app U).hom.toAlgebra
  f.normalizationObjIso hU ≪≫
    (RingEquiv.ofBijective
      ((integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom)
      ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, by
        rw [f.integralClosure_eq_top_of_universallyClosed hU]
        trivial⟩, rfl⟩⟩).toCommRingCatIso

set_option linter.unusedSectionVars false in
/-- The Stein-object identification is computed by `f.toNormalization`. -/
theorem steinObjIso_hom {U : Y.Opens} (hU : IsAffineOpen U) :
    (f.steinObjIso hU).hom =
      f.toNormalization.appLE (f.fromNormalization ⁻¹ᵁ U) (f ⁻¹ᵁ U)
        (by simp [← Scheme.Hom.comp_preimage]) := by
  rw [← f.normalizationObjIso_hom_val hU]
  rfl


/-- **The finite leg of the Stein factorization is finite exactly when it is locally of finite
type.**  Integrality is automatic: Mathlib already provides
`instance : IsIntegralHom f.fromNormalization` unconditionally, so
`IsFinite.iff_isIntegralHom_and_locallyOfFiniteType` collapses to the finite-type half.

This isolates what the Stein obligation of Theorem 4.1.17 actually needs.  The remaining
content is that `f_* 𝒪_X` is a finite-type `𝒪_Y`-algebra for `f` proper — i.e. coherence of
proper pushforward — and nothing else. -/
theorem isFinite_fromNormalization_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] :
    IsFinite f.fromNormalization ↔ LocallyOfFiniteType f.fromNormalization := by
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  exact ⟨fun h => h.2, fun h => ⟨inferInstance, h⟩⟩

end AlgebraicGeometry.Scheme.Hom
