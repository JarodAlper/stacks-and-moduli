module

public import StacksAndModuli.API.QuasicoherentCokernel
public import StacksAndModuli.API.SchemeModulesKernelFinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Kernels

/-!
# Finite presentation of cokernels of quasicoherent module sheaves

The cokernel of a morphism between finitely presented quasicoherent module
sheaves is finitely presented.  On a spectrum this is the corresponding
module-theoretic fact: a quotient of a finitely presented module by the image
of a finite module is finitely presented.  The general result follows by
transporting to the canonical spectrum model on affine opens.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.cokernel_isFinitePresentation_spec`;
* `AlgebraicGeometry.Scheme.Modules.cokernel_isFinitePresentation_of_isAffine`;
* `AlgebraicGeometry.Scheme.Modules.cokernel_isFinitePresentation`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The cokernel of a linear map from a finite module to a finitely presented
module is finitely presented. -/
lemma module_finitePresentation_rangeQuotient
    {R : Type u} [CommRing R]
    {N M : Type u} [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module R M]
    [Module.Finite R N] [Module.FinitePresentation R M]
    (f : N →ₗ[R] M) :
    Module.FinitePresentation R (M ⧸ LinearMap.range f) := by
  apply Module.finitePresentation_of_surjective
    (LinearMap.range f).mkQ (Submodule.mkQ_surjective _)
  rw [Submodule.ker_mkQ]
  have hfg := Module.Finite.fg_top.map f
  rw [Submodule.map_top] at hfg
  exact hfg

/-- On an affine spectrum, the cokernel of a morphism between finitely
presented quasicoherent module sheaves is finitely presented. -/
lemma cokernel_isFinitePresentation_spec {R : CommRingCat.{u}}
    {N M : (Spec R).Modules}
    [N.IsQuasicoherent] [N.IsFinitePresentation]
    [M.IsQuasicoherent] [M.IsFinitePresentation]
    (f : N ⟶ M) : (cokernel f).IsFinitePresentation := by
  let g := moduleSpecΓFunctor.map f
  have hN : Module.FinitePresentation R (moduleSpecΓFunctor.obj N) :=
    moduleSpecΓFunctor_finitePresentation_of_isFinitePresentation N
  have hM : Module.FinitePresentation R (moduleSpecΓFunctor.obj M) :=
    moduleSpecΓFunctor_finitePresentation_of_isFinitePresentation M
  letI : Module.FinitePresentation R (moduleSpecΓFunctor.obj N) := hN
  letI : Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := hM
  have hQ : Module.FinitePresentation R
      (moduleSpecΓFunctor.obj M ⧸ LinearMap.range g.hom) :=
    module_finitePresentation_rangeQuotient g.hom
  letI : Module.FinitePresentation R
      (moduleSpecΓFunctor.obj M ⧸ LinearMap.range g.hom) := hQ
  have hC : Module.FinitePresentation R (↑(cokernel g)) :=
    Module.FinitePresentation.of_equiv
      (ModuleCat.cokernelIsoRangeQuotient g).symm.toLinearEquiv
  letI : Module.FinitePresentation R (↑(cokernel g)) := hC
  have hId : Module.FinitePresentation R
      (↑((Functor.id (ModuleCat R)).obj (cokernel g))) := by
    simpa using hC
  letI : Module.FinitePresentation R
      (↑((Functor.id (ModuleCat R)).obj (cokernel g))) := hId
  have hTildeMod : Module.FinitePresentation R
      (moduleSpecΓFunctor.obj ((tilde.functor R).obj (cokernel g))) :=
    Module.FinitePresentation.of_equiv
      (tilde.toTildeΓNatIso.app (cokernel g)).toLinearEquiv
  letI : Module.FinitePresentation R
      (moduleSpecΓFunctor.obj ((tilde.functor R).obj (cokernel g))) := hTildeMod
  have hTilde : ((tilde.functor R).obj (cokernel g)).IsFinitePresentation :=
    isFinitePresentation_of_moduleSpecΓFunctor _
  exact ObjectProperty.prop_of_iso
    (P := SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf)
    (quasicoherentCokernelSpecTildeIso f).symm hTilde

/-- On an affine scheme, the cokernel of a morphism between finitely presented
quasicoherent module sheaves is finitely presented. -/
lemma cokernel_isFinitePresentation_of_isAffine {X : Scheme.{u}} [IsAffine X]
    {N M : X.Modules}
    [N.IsQuasicoherent] [N.IsFinitePresentation]
    [M.IsQuasicoherent] [M.IsFinitePresentation]
    (f : N ⟶ M) : (cokernel f).IsFinitePresentation := by
  let j : Spec Γ(X, ⊤) ⟶ X := X.isoSpec.inv
  let fSpec := (restrictFunctor j).map f
  letI : ((restrictFunctor j).obj N).IsFinitePresentation :=
    isFinitePresentation_restrict j N
  letI : ((restrictFunctor j).obj M).IsFinitePresentation :=
    isFinitePresentation_restrict j M
  have hSpec : (cokernel fSpec).IsFinitePresentation :=
    cokernel_isFinitePresentation_spec fSpec
  haveI := (restrictAdjunction j).leftAdjoint_preservesColimits
  have hRestrict : ((restrictFunctor j).obj (cokernel f)).IsFinitePresentation :=
    ObjectProperty.prop_of_iso
      (P := SheafOfModules.isFinitePresentation (Spec Γ(X, ⊤)).ringCatSheaf)
      (PreservesCokernel.iso (restrictFunctor j) f).symm hSpec
  letI : ((restrictFunctor j).obj (cokernel f)).IsFinitePresentation := hRestrict
  have hBack : ((restrictFunctor X.isoSpec.hom).obj
      ((restrictFunctor j).obj (cokernel f))).IsFinitePresentation :=
    isFinitePresentation_restrict X.isoSpec.hom _
  let eBack : (restrictFunctor X.isoSpec.hom).obj
      ((restrictFunctor j).obj (cokernel f)) ≅ cokernel f :=
    (restrictFunctorComp X.isoSpec.hom X.isoSpec.inv).symm.app (cokernel f) ≪≫
      (restrictFunctorCongr X.isoSpec.hom_inv_id).app (cokernel f) ≪≫
      restrictFunctorId.app (cokernel f)
  exact ObjectProperty.prop_of_iso
    (P := SheafOfModules.isFinitePresentation X.ringCatSheaf) eBack hBack

/-- The cokernel of a morphism between finitely presented quasicoherent module
sheaves on a scheme is finitely presented. -/
lemma cokernel_isFinitePresentation {X : Scheme.{u}}
    {N M : X.Modules}
    [N.IsQuasicoherent] [N.IsFinitePresentation]
    [M.IsQuasicoherent] [M.IsFinitePresentation]
    (f : N ⟶ M) : (cokernel f).IsFinitePresentation := by
  letI : (cokernel f).IsQuasicoherent := isQuasicoherent_cokernel f
  let presData (U : X.affineOpens) :
      { P : SheafOfModules.Presentation ((cokernel f).restrict U.1.ι) // P.IsFinite } := by
    let fU := (restrictFunctor U.1.ι).map f
    letI : ((restrictFunctor U.1.ι).obj N).IsFinitePresentation :=
      isFinitePresentation_restrict U.1.ι N
    letI : ((restrictFunctor U.1.ι).obj M).IsFinitePresentation :=
      isFinitePresentation_restrict U.1.ι M
    have hCU : (cokernel fU).IsFinitePresentation :=
      cokernel_isFinitePresentation_of_isAffine fU
    haveI := (restrictAdjunction U.1.ι).leftAdjoint_preservesColimits
    have hRestrict : ((restrictFunctor U.1.ι).obj
        (cokernel f)).IsFinitePresentation :=
      ObjectProperty.prop_of_iso
        (P := SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf)
        (PreservesCokernel.iso (restrictFunctor U.1.ι) f).symm hCU
    letI : ((restrictFunctor U.1.ι).obj
        (cokernel f)).IsFinitePresentation := hRestrict
    let h := exists_finitePresentation_of_isFinitePresentation_affine
      ((restrictFunctor U.1.ι).obj (cokernel f))
    exact ⟨Classical.choose h, Classical.choose_spec h⟩
  let pres (U : X.affineOpens) :
      SheafOfModules.Presentation ((cokernel f).restrict U.1.ι) :=
    (presData U).1
  letI (U : X.affineOpens) : (pres U).IsFinite := (presData U).2
  exact isFinitePresentation_of_isOpenCover (cokernel f)
    (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X) pres

end AlgebraicGeometry.Scheme.Modules

end
