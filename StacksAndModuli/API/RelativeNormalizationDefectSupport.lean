module

public import StacksAndModuli.API.SchemeModulesTensorLocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Local support of relative-normalization defects

For a relative normalization `f.fromNormalization`, this file gives an affine criterion
ensuring that its restriction is an isomorphism.  The criterion says that the map on
sections into the displayed ambient algebra is injective and that the target ring is
integrally closed in that algebra.  It then transports this geometric isomorphism to the
structure-sheaf adjunction unit and proves that its cokernel restricts to zero.

For the component-function-field normalization of a reduced nodal curve, the missing input
for applying the criterion on the smooth locus is an explicit comparison between sections
of the component-generic scheme over an irreducible affine neighbourhood and the function
field of that neighbourhood.  This file does not assume that comparison and does not claim
an unconditional normalization-defect computation for nodal curves.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosedIn`:
  relative normalization is an isomorphism over an affine integrally closed locus.
* `SheafOfModules.isIso_restrict_unitToPushforwardObjUnit_of_isIso_resLE`:
  the structure-sheaf unit restricts to an isomorphism wherever the underlying morphism
  does.
* `AlgebraicGeometry.Scheme.Hom.isZero_restrict_cokernel_normalizationUnit_of_isIntegrallyClosedIn`:
  the relative-normalization defect restricts to zero on such an affine open.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Relative normalization is an isomorphism over an affine open when the target's
section ring is integrally closed in the displayed ambient algebra.

Injectivity is stated separately because `IsIntegrallyClosedIn` contains it only behind
an abbreviation, whereas it is also the exact hypothesis needed to identify the integral
closure with the bottom subalgebra. -/
theorem Hom.isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosedIn
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {U : Y.Opens} (hU : IsAffineOpen U)
    (hinj : Function.Injective (f.app U).hom)
    (hclosed : letI := (f.app U).hom.toAlgebra
      IsIntegrallyClosedIn Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) :
    IsIso (f.fromNormalization ∣_ U) := by
  let _ := (f.app U).hom.toAlgebra
  have hclosure : integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U) = ⊥ :=
    (IsIntegrallyClosedIn.integralClosure_eq_bot_iff _ hinj).mpr hclosed
  let g : CommRingCat.of Γ(Y, U) ⟶
      CommRingCat.of (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) :=
    CommRingCat.ofHom (algebraMap _ _)
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      apply hinj
      exact congrArg Subtype.val hab
    · intro z
      have hz : (z : Γ(X, f ⁻¹ᵁ U)) ∈
          (⊥ : Subalgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) := by
        rw [← hclosure]
        exact z.property
      rw [Algebra.mem_bot, Set.mem_range] at hz
      obtain ⟨a, ha⟩ := hz
      refine ⟨a, Subtype.ext ?_⟩
      exact ha
  let _ : IsIso g :=
    (ConcreteCategory.isIso_iff_bijective g).mpr hg
  rw [isIso_morphismRestrict_iff_isIso_app f.fromNormalization hU,
    f.fromNormalization_app hU]
  infer_instance

/-- The structure-sheaf unit into a pushforward is an isomorphism when the scheme
morphism itself is an isomorphism. -/
theorem SheafOfModules.isIso_unitToPushforwardObjUnit_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit
      f.toRingCatSheafHom) := by
  rw [Modules.Hom.isIso_iff_isIso_app]
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  have hf : IsIso (f.app U) := by
    let _ : IsOpenImmersion f := by infer_instance
    exact f.isIso_app U (by
      rw [Hom.opensRange_of_isIso]
      exact le_top)
  exact (ConcreteCategory.isIso_iff_bijective (f.app U)).mp hf

/-- Restricting the structure-sheaf unit to an open gives an isomorphism when the
corresponding restriction of the scheme morphism is an isomorphism. -/
theorem SheafOfModules.isIso_restrict_unitToPushforwardObjUnit_of_isIso_resLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    [IsIso (f.resLE U (f ⁻¹ᵁ U) le_rfl)] :
    IsIso ((Modules.restrictFunctor U.ι).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) := by
  rw [Modules.Hom.isIso_iff_isIso_app]
  intro V
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  let g := f.resLE U (f ⁻¹ᵁ U) le_rfl
  let iX := (f ⁻¹ᵁ U).ι
  have hcomp : iX ≫ f = g ≫ U.ι :=
    (f.resLE_comp_ι le_rfl).symm
  have happ := IsOpenImmersion.app_eq_appIso_inv_app_of_comp_eq
    g U.ι (iX ≫ f) hcomp V
  rw [Scheme.Hom.comp_app] at happ
  have hix : IsIso (iX.app (f ⁻¹ᵁ (U.ι ''ᵁ V))) := by
    exact iX.isIso_app _ (by
      rw [Scheme.Opens.opensRange_ι]
      exact f.preimage_mono (U.ι_image_le V))
  have hmap : IsIso ((f ⁻¹ᵁ U).toScheme.presheaf.map
      (eqToHom (IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux
        g U.ι (iX ≫ f) hcomp V)).op) := by infer_instance
  have hright : IsIso
      (iX.app (f ⁻¹ᵁ (U.ι ''ᵁ V)) ≫
        (f ⁻¹ᵁ U).toScheme.presheaf.map
          (eqToHom (IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux
            g U.ι (iX ≫ f) hcomp V)).op) := by infer_instance
  have htail : IsIso
      ((iX ≫ f).app (U.ι ''ᵁ V) ≫
        (f ⁻¹ᵁ U).toScheme.presheaf.map
          (eqToHom (IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux
            g U.ι (iX ≫ f) hcomp V)).op) := by
    rw [← isIso_comp_left_iff (U.ι.appIso V).inv]
    rw [Scheme.Hom.comp_app]
    rw [← happ]
    infer_instance
  rw [Scheme.Hom.comp_app] at htail
  have hfapp : IsIso (f.app (U.ι ''ᵁ V)) := by
    apply IsIso.of_isIso_comp_right (f.app (U.ι ''ᵁ V))
      (iX.app (f ⁻¹ᵁ (U.ι ''ᵁ V)) ≫
        (f ⁻¹ᵁ U).toScheme.presheaf.map
          (eqToHom (IsOpenImmersion.app_eq_invApp_app_of_comp_eq_aux
            g U.ι (iX ≫ f) hcomp V)).op)
  exact (ConcreteCategory.isIso_iff_bijective (f.app (U.ι ''ᵁ V))).mp hfapp

/-- On an open where a scheme morphism is an isomorphism, the cokernel of the
structure-sheaf unit restricts to the zero module. -/
theorem SheafOfModules.isZero_restrict_cokernel_unitToPushforwardObjUnit_of_isIso_resLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    [IsIso (f.resLE U (f ⁻¹ᵁ U) le_rfl)] :
    IsZero ((Modules.restrictFunctor U.ι).obj
      (cokernel (SheafOfModules.unitToPushforwardObjUnit
        f.toRingCatSheafHom))) := by
  let a := SheafOfModules.unitToPushforwardObjUnit
    f.toRingCatSheafHom
  let _ : IsIso ((Modules.restrictFunctor U.ι).map a) :=
    SheafOfModules.isIso_restrict_unitToPushforwardObjUnit_of_isIso_resLE f U
  exact IsZero.of_iso
    (isZero_cokernel_of_epi ((Modules.restrictFunctor U.ι).map a))
    (PreservesCokernel.iso (Modules.restrictFunctor U.ι) a)

/-- On an affine open whose ring is integrally closed in the displayed ambient algebra,
the cokernel of the relative-normalization unit restricts to the zero module. -/
theorem Hom.isZero_restrict_cokernel_normalizationUnit_of_isIntegrallyClosedIn
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {U : Y.Opens} (hU : IsAffineOpen U)
    (hinj : Function.Injective (f.app U).hom)
    (hclosed : letI := (f.app U).hom.toAlgebra
      IsIntegrallyClosedIn Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) :
    IsZero ((Modules.restrictFunctor U.ι).obj
      (cokernel (SheafOfModules.unitToPushforwardObjUnit
        f.fromNormalization.toRingCatSheafHom))) := by
  let _ : IsIso (f.fromNormalization ∣_ U) :=
    f.isIso_morphismRestrict_fromNormalization_of_isIntegrallyClosedIn
      hU hinj hclosed
  let _ : IsIso (f.fromNormalization.resLE U
      (f.fromNormalization ⁻¹ᵁ U) le_rfl) := by
    rw [Hom.resLE_eq_morphismRestrict]
    infer_instance
  exact
    SheafOfModules.isZero_restrict_cokernel_unitToPushforwardObjUnit_of_isIso_resLE
      f.fromNormalization U

end AlgebraicGeometry.Scheme
