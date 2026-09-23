module

public import StacksAndModuli.API.AffineQuasicoherentEpi
public import StacksAndModuli.API.QuasicoherentVectorBundles
public import StacksAndModuli.API.SchemeModulesKernelFinitePresentation

/-!
# Finite presentation of kernels with vector-bundle quotient

An epimorphism between finite locally free quasicoherent sheaves has a finitely
presented kernel over an arbitrary base scheme.  Affine-locally the map on
coordinates is surjective, its target is projective, and hence the exact
sequence splits.  The kernel is therefore a finite projective module.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace LinearMap

/-- The kernel of a surjection between finite projective modules is finite
projective. -/
lemma ker_finite_projective_of_surjective
    {R M N : Type u} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.Finite R (LinearMap.ker f) ∧
      Module.Projective R (LinearMap.ker f) := by
  letI : Module.FinitePresentation R N :=
    Module.finitePresentation_of_projective R N
  letI : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_fg (Module.FinitePresentation.fg_ker f hf)
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f
    (LinearMap.id : N →ₗ[R] N) hf
  let p : M →ₗ[R] LinearMap.ker f :=
    (LinearMap.id - s.comp f).codRestrict (LinearMap.ker f) (fun x ↦ by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        map_sub, LinearMap.comp_apply]
      rw [show f (s (f x)) = f x by
        exact DFunLike.congr_fun hs (f x)]
      exact sub_self _)
  have hp : p.comp (LinearMap.ker f).subtype =
      (LinearMap.id : LinearMap.ker f →ₗ[R] LinearMap.ker f) := by
    ext x
    change x.1 - s (f x.1) = x.1
    rw [x.2, map_zero, sub_zero]
  exact ⟨inferInstance,
    Module.Projective.of_split (LinearMap.ker f).subtype p hp⟩

end LinearMap

namespace AlgebraicGeometry.Scheme.Modules

set_option maxHeartbeats 3000000 in
-- Computing affine coordinate modules through the tilde equivalence is elaboration-heavy.
/-- On an affine spectrum, the kernel of an epimorphism between finite locally
free quasicoherent sheaves is finitely presented. -/
lemma kernel_isFinitePresentation_spec_of_epi_of_isFiniteLocallyFree
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hM : IsFiniteLocallyFree M) (hN : IsFiniteLocallyFree N)
    (f : M ⟶ N) [Epi f] : (kernel f).IsFinitePresentation := by
  letI : (kernel f).IsQuasicoherent := kernel_isQuasicoherent_spec f
  have hMcoord :=
    moduleSpecΓFunctor_finite_projective_of_isFiniteLocallyFree M hM
  have hNcoord :=
    moduleSpecΓFunctor_finite_projective_of_isFiniteLocallyFree N hN
  letI : Module.Finite R (moduleSpecΓFunctor.obj M) := hMcoord.1
  letI : Module.Projective R (moduleSpecΓFunctor.obj M) := hMcoord.2
  letI : Module.Finite R (moduleSpecΓFunctor.obj N) := hNcoord.1
  letI : Module.Projective R (moduleSpecΓFunctor.obj N) := hNcoord.2
  have hf : Function.Surjective (moduleSpecΓFunctor.map f) :=
    moduleSpecΓFunctor_map_surjective_of_epi f
  have hK := LinearMap.ker_finite_projective_of_surjective
    (moduleSpecΓFunctor.map f).hom hf
  have hKfinKer : Module.Finite R
      (LinearMap.ker ((specEvaluation R ⊤).map f).hom) := by
    change Module.Finite R
      (LinearMap.ker (moduleSpecΓFunctor.map f).hom)
    exact hK.1
  have hKprojKer : Module.Projective R
      (LinearMap.ker ((specEvaluation R ⊤).map f).hom) := by
    change Module.Projective R
      (LinearMap.ker (moduleSpecΓFunctor.map f).hom)
    exact hK.2
  letI : Module.Finite R
      (LinearMap.ker ((specEvaluation R ⊤).map f).hom) := hKfinKer
  letI : Module.Projective R
      (LinearMap.ker ((specEvaluation R ⊤).map f).hom) := hKprojKer
  let e := specEvaluationKernelLinearEquiv R ⊤ f
  have hKfin : Module.Finite R
      (moduleSpecΓFunctor.obj (kernel f)) :=
    Module.Finite.equiv e.symm
  have hKproj : Module.Projective R
      (moduleSpecΓFunctor.obj (kernel f)) :=
    Module.Projective.of_equiv' e.symm
  letI : Module.Finite R (moduleSpecΓFunctor.obj (kernel f)) := hKfin
  letI : Module.Projective R (moduleSpecΓFunctor.obj (kernel f)) := hKproj
  letI : Module.FinitePresentation R
      (moduleSpecΓFunctor.obj (kernel f)) :=
    Module.finitePresentation_of_projective R _
  exact isFinitePresentation_of_moduleSpecΓFunctor (kernel f)

set_option maxHeartbeats 3000000 in
-- Transport through both sides of the affine-spectrum equivalence is elaboration-heavy.
/-- On an arbitrary affine scheme, the kernel of an epimorphism between finite
locally free quasicoherent sheaves is finitely presented. -/
lemma kernel_isFinitePresentation_of_isAffine_of_epi_of_isFiniteLocallyFree
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hM : IsFiniteLocallyFree M) (hN : IsFiniteLocallyFree N)
    (f : M ⟶ N) [Epi f] : (kernel f).IsFinitePresentation := by
  let j : Spec Γ(X, ⊤) ⟶ X := X.isoSpec.inv
  let fSpec := (restrictFunctor j).map f
  letI : ((restrictFunctor j).obj M).IsQuasicoherent := by infer_instance
  letI : ((restrictFunctor j).obj N).IsQuasicoherent := by infer_instance
  letI : Epi fSpec := inferInstance
  have hMspec : IsFiniteLocallyFree ((restrictFunctor j).obj M) :=
    (hM.pullback j).of_iso ((restrictFunctorIsoPullback j).app M).symm
  have hNspec : IsFiniteLocallyFree ((restrictFunctor j).obj N) :=
    (hN.pullback j).of_iso ((restrictFunctorIsoPullback j).app N).symm
  have hSpec : (kernel fSpec).IsFinitePresentation :=
    kernel_isFinitePresentation_spec_of_epi_of_isFiniteLocallyFree
      hMspec hNspec fSpec
  letI := restrictFunctor_preservesKernel j f
  have hRestrict : ((restrictFunctor j).obj (kernel f)).IsFinitePresentation :=
    ObjectProperty.prop_of_iso
      (P := SheafOfModules.isFinitePresentation (Spec Γ(X, ⊤)).ringCatSheaf)
      (PreservesKernel.iso (restrictFunctor j) f).symm hSpec
  letI : ((restrictFunctor j).obj (kernel f)).IsFinitePresentation := hRestrict
  have hBack : ((restrictFunctor X.isoSpec.hom).obj
      ((restrictFunctor j).obj (kernel f))).IsFinitePresentation :=
    isFinitePresentation_restrict X.isoSpec.hom _
  let eBack : (restrictFunctor X.isoSpec.hom).obj
      ((restrictFunctor j).obj (kernel f)) ≅ kernel f :=
    (restrictFunctorComp X.isoSpec.hom X.isoSpec.inv).symm.app (kernel f) ≪≫
      (restrictFunctorCongr X.isoSpec.hom_inv_id).app (kernel f) ≪≫
      restrictFunctorId.app (kernel f)
  exact ObjectProperty.prop_of_iso
    (P := SheafOfModules.isFinitePresentation X.ringCatSheaf) eBack hBack

set_option maxHeartbeats 3000000 in
-- The affine-cover presentation packages several restriction and kernel comparisons.
/-- The kernel of an epimorphism between finite locally free quasicoherent
sheaves is finitely presented over an arbitrary scheme. -/
lemma kernel_isFinitePresentation_of_epi_of_isFiniteLocallyFree
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hM : IsFiniteLocallyFree M) (hN : IsFiniteLocallyFree N)
    (f : M ⟶ N) [Epi f] : (kernel f).IsFinitePresentation := by
  letI : (kernel f).IsQuasicoherent := kernel_isQuasicoherent f
  let presData (U : X.affineOpens) :
      { P : SheafOfModules.Presentation
          ((kernel f).restrict U.1.ι) // P.IsFinite } := by
    let fU := (restrictFunctor U.1.ι).map f
    letI : ((restrictFunctor U.1.ι).obj M).IsQuasicoherent := by
      infer_instance
    letI : ((restrictFunctor U.1.ι).obj N).IsQuasicoherent := by
      infer_instance
    letI : Epi fU := inferInstance
    have hMU : IsFiniteLocallyFree ((restrictFunctor U.1.ι).obj M) :=
      (hM.pullback U.1.ι).of_iso
        ((restrictFunctorIsoPullback U.1.ι).app M).symm
    have hNU : IsFiniteLocallyFree ((restrictFunctor U.1.ι).obj N) :=
      (hN.pullback U.1.ι).of_iso
        ((restrictFunctorIsoPullback U.1.ι).app N).symm
    have hKU : (kernel fU).IsFinitePresentation :=
      kernel_isFinitePresentation_of_isAffine_of_epi_of_isFiniteLocallyFree
        hMU hNU fU
    letI := restrictFunctor_preservesKernel U.1.ι f
    have hRestrict : ((restrictFunctor U.1.ι).obj
        (kernel f)).IsFinitePresentation :=
      ObjectProperty.prop_of_iso
        (P := SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf)
        (PreservesKernel.iso (restrictFunctor U.1.ι) f).symm hKU
    letI : ((restrictFunctor U.1.ι).obj
        (kernel f)).IsFinitePresentation := hRestrict
    let h := exists_finitePresentation_of_isFinitePresentation_affine
      ((restrictFunctor U.1.ι).obj (kernel f))
    exact ⟨Classical.choose h, Classical.choose_spec h⟩
  let pres (U : X.affineOpens) :
      SheafOfModules.Presentation ((kernel f).restrict U.1.ι) :=
    (presData U).1
  letI (U : X.affineOpens) : (pres U).IsFinite := (presData U).2
  exact isFinitePresentation_of_isOpenCover (kernel f)
    (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X) pres

end AlgebraicGeometry.Scheme.Modules

end

end
