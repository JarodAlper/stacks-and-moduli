module

public import StacksAndModuli.API.QuasicoherentObjectProperties
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Kernels of finitely presented quasicoherent module sheaves

This file proves that kernels of morphisms of quasicoherent module sheaves are
quasicoherent.  Over a locally Noetherian scheme, a kernel whose source is finitely
presented is itself finitely presented.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.Limits
open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Evaluation of sheaves of modules on `Spec R`, retaining the underlying
`R`-module structure. -/
noncomputable def specEvaluation (R : CommRingCat.{u})
    (U : (Spec R).Opens) : (Spec R).Modules ⥤ ModuleCat R :=
  SheafOfModules.evaluation (R := (Spec R).ringCatSheaf) (op U) ⋙
    ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso R).inv ≫ (Spec R).presheaf.map U.leTop.op).hom)

instance specEvaluation_additive (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    (specEvaluation R U).Additive where
  map_add := by
    intros
    rfl

noncomputable instance specEvaluation_preservesFiniteLimits
    (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    PreservesFiniteLimits (specEvaluation R U) := by
  letI : PreservesFiniteLimits
      (SheafOfModules.evaluation (R := (Spec R).ringCatSheaf) (op U)) :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits _ (op U)
  exact comp_preservesFiniteLimits _ _

/-- Evaluation on an open identifies the categorical kernel with the ordinary
kernel of the induced linear map. -/
noncomputable def specEvaluationKernelLinearEquiv (R : CommRingCat.{u})
    (U : (Spec R).Opens) {M N : (Spec R).Modules} (q : M ⟶ N) :
    (specEvaluation R U).obj (kernel q) ≃ₗ[R]
      LinearMap.ker ((specEvaluation R U).map q).hom :=
  (PreservesKernel.iso (specEvaluation R U) q ≪≫
    ModuleCat.kernelIsoKer ((specEvaluation R U).map q)).toLinearEquiv

/-- On an affine spectrum, the kernel of a morphism of quasicoherent module sheaves
is quasicoherent. -/
lemma kernel_isQuasicoherent_spec {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (q : M ⟶ N) : (kernel q).IsQuasicoherent := by
  rw [AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ,
    AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing]
  intro r
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let fM : (specEvaluation R ⊤).obj M ⟶ (specEvaluation R U).obj M :=
    (modulesSpecToSheaf.obj M).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
  let fN : (specEvaluation R ⊤).obj N ⟶ (specEvaluation R U).obj N :=
    (modulesSpecToSheaf.obj N).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
  let g : (specEvaluation R ⊤).obj M ⟶ (specEvaluation R ⊤).obj N :=
    (specEvaluation R ⊤).map q
  let gU : (specEvaluation R U).obj M ⟶ (specEvaluation R U).obj N :=
    (specEvaluation R U).map q
  haveI hfM : IsLocalizedModule (Submonoid.powers r) fM.hom := by
    exact (AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing M).mp
      (inferInstance : IsIso M.fromTildeΓ) r
  haveI hfN : IsLocalizedModule (Submonoid.powers r) fN.hom := by
    exact (AlgebraicGeometry.isIso_fromTildeΓ_iff_isLocalizing N).mp
      (inferInstance : IsIso N.fromTildeΓ) r
  have hmap : IsLocalizedModule.map (Submonoid.powers r) fM.hom fN.hom g.hom =
      gU.hom := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r) fM.hom fN.hom
    rw [IsLocalizedModule.map_comp]
    ext x
    exact CategoryTheory.congr_fun
      ((modulesSpecToSheaf.map q).hom.naturality
        (homOfLE (le_top : U ≤ ⊤)).op) x |>.symm
  let eTop : ((specEvaluation R ⊤).obj (kernel q)) ≅ kernel g :=
    PreservesKernel.iso (specEvaluation R ⊤) q
  let eU : ((specEvaluation R U).obj (kernel q)) ≅ kernel gU :=
    PreservesKernel.iso (specEvaluation R U) q
  let lTop : (specEvaluation R ⊤).obj (kernel q) ≃ₗ[R] LinearMap.ker g.hom :=
    (eTop ≪≫ ModuleCat.kernelIsoKer g).toLinearEquiv
  let lU : (specEvaluation R U).obj (kernel q) ≃ₗ[R] LinearMap.ker gU.hom :=
    (eU ≪≫ ModuleCat.kernelIsoKer gU).toLinearEquiv
  let kRes : (specEvaluation R ⊤).obj (kernel q) ⟶
      (specEvaluation R U).obj (kernel q) :=
    (modulesSpecToSheaf.obj (kernel q)).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op
  let kerMapEquiv : LinearMap.ker
      (IsLocalizedModule.map (Submonoid.powers r) fM.hom fN.hom g.hom) ≃ₗ[R]
      LinearMap.ker gU.hom :=
    LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hmap)
  let toKer : LinearMap.ker g.hom →ₗ[R] LinearMap.ker gU.hom :=
    kerMapEquiv.toLinearMap ∘ₗ
      LinearMap.toKerIsLocalized (Submonoid.powers r) fM.hom fN.hom g.hom
  letI : Module Γ(Spec R, U) ((specEvaluation R U).obj M) :=
    inferInstanceAs (Module Γ(Spec R, U) Γ(M, U))
  letI : Module Γ(Spec R, U) ((specEvaluation R U).obj N) :=
    inferInstanceAs (Module Γ(Spec R, U) Γ(N, U))
  letI : IsScalarTower R Γ(Spec R, U) ((specEvaluation R U).obj M) :=
    inferInstanceAs (IsScalarTower R Γ(Spec R, U) Γ(M, U))
  letI : IsScalarTower R Γ(Spec R, U) ((specEvaluation R U).obj N) :=
    inferInstanceAs (IsScalarTower R Γ(Spec R, U) Γ(N, U))
  haveI : IsLocalizedModule (Submonoid.powers r)
      (LinearMap.toKerIsLocalized (Submonoid.powers r) fM.hom fN.hom g.hom) :=
    LinearMap.toKerLocalized_isLocalizedModule Γ(Spec R, U)
      (Submonoid.powers r) fM.hom fN.hom g.hom
  haveI : IsLocalizedModule (Submonoid.powers r) toKer := by
    dsimp only [toKer]
    infer_instance
  haveI : IsLocalizedModule (Submonoid.powers r)
      (lU.symm.toLinearMap ∘ₗ toKer ∘ₗ lTop.toLinearMap) := by
    infer_instance
  have hkRes : kRes.hom = lU.symm.toLinearMap ∘ₗ toKer ∘ₗ lTop.toLinearMap := by
    apply LinearMap.ext
    intro x
    change kRes.hom x = lU.symm (toKer (lTop x))
    apply (ConcreteCategory.bijective_of_isIso eU.hom).injective
    rw [show eU.hom.hom (lU.symm (toKer (lTop x))) =
        (ModuleCat.kernelIsoKer gU).inv.hom (toKer (lTop x)) by
      change ((ModuleCat.kernelIsoKer gU).inv ≫ eU.inv ≫ eU.hom).hom
        (toKer (lTop x)) = _
      simp]
    apply (ModuleCat.mono_iff_injective (kernel.ι gU)).mp inferInstance
    rw [← CategoryTheory.comp_apply, PreservesKernel.iso_hom,
      kernelComparison_comp_ι]
    change _ = ((ModuleCat.kernelIsoKer gU).inv ≫ kernel.ι gU).hom
      (toKer (lTop x))
    rw [ModuleCat.kernelIsoKer_inv_kernel_ι]
    change ((kernel.ι q).app U).hom (kRes.hom x) = _
    rw [show ((kernel.ι q).app U).hom (kRes.hom x) =
        fM.hom (((kernel.ι q).app ⊤).hom x) by
      exact CategoryTheory.congr_fun
        ((kernel.ι q).mapPresheaf.naturality
          (homOfLE (le_top : U ≤ ⊤)).op) x]
    change fM.hom (((kernel.ι q).app ⊤).hom x) = (toKer (lTop x)).1
    rw [show (toKer (lTop x)).1 = fM.hom (lTop x).1 by rfl]
    congr 1
    symm
    change (ModuleCat.ofHom g.hom.ker.subtype).hom
      ((ModuleCat.kernelIsoKer g).hom.hom (eTop.hom.hom x)) = _
    rw [← CategoryTheory.comp_apply, ModuleCat.kernelIsoKer_hom_ker_subtype,
      ← CategoryTheory.comp_apply, PreservesKernel.iso_hom,
      kernelComparison_comp_ι]
    rfl
  change IsLocalizedModule (Submonoid.powers r) kRes.hom
  rw [hkRes]
  infer_instance

/-- The kernel of a morphism of quasicoherent module sheaves on a scheme is
quasicoherent. -/
lemma kernel_isQuasicoherent {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (q : M ⟶ N) :
    (kernel q).IsQuasicoherent := by
  letI (i : X.affineCover.I₀) :=
    restrictFunctor_preservesKernel (X.affineCover.f i) q
  haveI : ∀ i, ((restrictFunctor (X.affineCover.f i)).obj
      (kernel q)).IsQuasicoherent := by
    intro i
    haveI : (kernel ((restrictFunctor (X.affineCover.f i)).map q)).IsQuasicoherent :=
      kernel_isQuasicoherent_spec ((restrictFunctor (X.affineCover.f i)).map q)
    exact (SheafOfModules.isQuasicoherent
      (X.affineCover.X i).ringCatSheaf).prop_of_iso
        (PreservesKernel.iso (restrictFunctor (X.affineCover.f i)) q).symm
        inferInstance
  exact isQuasicoherent_of_openCover_restrict _ X.affineCover

/-- On the spectrum of a Noetherian ring, the kernel of a morphism from a finitely
presented quasicoherent module sheaf to a quasicoherent module sheaf is finitely
presented. -/
lemma kernel_isFinitePresentation_spec {R : CommRingCat.{u}} [IsNoetherianRing R]
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [M.IsFinitePresentation]
    [N.IsQuasicoherent] (q : M ⟶ N) : (kernel q).IsFinitePresentation := by
  letI : (kernel q).IsQuasicoherent := kernel_isQuasicoherent_spec q
  have hMfp : Module.FinitePresentation R ((specEvaluation R ⊤).obj M) :=
    moduleSpecΓFunctor_finitePresentation_of_isFinitePresentation M
  letI : Module.FinitePresentation R ((specEvaluation R ⊤).obj M) := hMfp
  let g := (specEvaluation R ⊤).map q
  have hkerFG : (LinearMap.ker g.hom).FG := IsNoetherian.noetherian _
  letI : Module.Finite R (LinearMap.ker g.hom) := Module.Finite.of_fg hkerFG
  let e := specEvaluationKernelLinearEquiv R ⊤ q
  have hKfin : Module.Finite R ((specEvaluation R ⊤).obj (kernel q)) :=
    Module.Finite.equiv e.symm
  letI : Module.Finite R (moduleSpecΓFunctor.obj (kernel q)) := hKfin
  letI : Module.FinitePresentation R (moduleSpecΓFunctor.obj (kernel q)) :=
    Module.finitePresentation_of_finite R _
  exact AlgebraicGeometry.isFinitePresentation_of_moduleSpecΓFunctor (kernel q)

/-- Restriction along an open immersion preserves finite presentation. -/
lemma isFinitePresentation_restrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (M : Y.Modules) [M.IsFinitePresentation] :
    ((restrictFunctor f).obj M).IsFinitePresentation := by
  exact ObjectProperty.prop_of_iso
    (P := SheafOfModules.isFinitePresentation X.ringCatSheaf)
    ((restrictFunctorIsoPullback f).app M).symm inferInstance

/-- On an affine locally Noetherian scheme, the kernel of a morphism from a finitely
presented quasicoherent module sheaf to a quasicoherent module sheaf is finitely
presented. -/
lemma kernel_isFinitePresentation_of_isAffine {X : Scheme.{u}} [IsAffine X]
    [IsLocallyNoetherian X] {M N : X.Modules} [M.IsQuasicoherent]
    [M.IsFinitePresentation] [N.IsQuasicoherent] (q : M ⟶ N) :
    (kernel q).IsFinitePresentation := by
  letI : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top X⟩
  let f : Spec Γ(X, ⊤) ⟶ X := X.isoSpec.inv
  let qSpec := (restrictFunctor f).map q
  letI : ((restrictFunctor f).obj M).IsFinitePresentation :=
    isFinitePresentation_restrict f M
  have hSpec : (kernel qSpec).IsFinitePresentation :=
    kernel_isFinitePresentation_spec qSpec
  letI := restrictFunctor_preservesKernel f q
  have hRestrict : ((restrictFunctor f).obj (kernel q)).IsFinitePresentation :=
    ObjectProperty.prop_of_iso
      (P := SheafOfModules.isFinitePresentation (Spec Γ(X, ⊤)).ringCatSheaf)
      (PreservesKernel.iso (restrictFunctor f) q).symm hSpec
  letI : ((restrictFunctor f).obj (kernel q)).IsFinitePresentation := hRestrict
  have hBack : ((restrictFunctor X.isoSpec.hom).obj
      ((restrictFunctor f).obj (kernel q))).IsFinitePresentation :=
    isFinitePresentation_restrict X.isoSpec.hom _
  let eBack : (restrictFunctor X.isoSpec.hom).obj
      ((restrictFunctor f).obj (kernel q)) ≅ kernel q :=
    (restrictFunctorComp X.isoSpec.hom X.isoSpec.inv).symm.app (kernel q) ≪≫
      (restrictFunctorCongr X.isoSpec.hom_inv_id).app (kernel q) ≪≫
      restrictFunctorId.app (kernel q)
  exact ObjectProperty.prop_of_iso
    (P := SheafOfModules.isFinitePresentation X.ringCatSheaf) eBack hBack

/-- On a locally Noetherian scheme, the kernel of a morphism from a finitely
presented quasicoherent module sheaf to a quasicoherent module sheaf is finitely
presented. -/
lemma kernel_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsQuasicoherent] [M.IsFinitePresentation]
    [N.IsQuasicoherent] (q : M ⟶ N) : (kernel q).IsFinitePresentation := by
  letI : (kernel q).IsQuasicoherent := kernel_isQuasicoherent q
  let presData (U : X.affineOpens) :
      { P : SheafOfModules.Presentation ((kernel q).restrict U.1.ι) // P.IsFinite } := by
    let qU := (restrictFunctor U.1.ι).map q
    letI : ((restrictFunctor U.1.ι).obj M).IsFinitePresentation :=
      isFinitePresentation_restrict U.1.ι M
    have hKU : (kernel qU).IsFinitePresentation :=
      kernel_isFinitePresentation_of_isAffine qU
    letI := restrictFunctor_preservesKernel U.1.ι q
    have hRestrict : ((restrictFunctor U.1.ι).obj
        (kernel q)).IsFinitePresentation :=
      ObjectProperty.prop_of_iso
        (P := SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf)
        (PreservesKernel.iso (restrictFunctor U.1.ι) q).symm hKU
    letI : ((restrictFunctor U.1.ι).obj (kernel q)).IsFinitePresentation := hRestrict
    let h := exists_finitePresentation_of_isFinitePresentation_affine
      ((restrictFunctor U.1.ι).obj (kernel q))
    exact ⟨Classical.choose h, Classical.choose_spec h⟩
  let pres (U : X.affineOpens) :
      SheafOfModules.Presentation ((kernel q).restrict U.1.ι) := (presData U).1
  letI (U : X.affineOpens) : (pres U).IsFinite := (presData U).2
  exact isFinitePresentation_of_isOpenCover (kernel q)
    (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X) pres

end AlgebraicGeometry.Scheme.Modules
