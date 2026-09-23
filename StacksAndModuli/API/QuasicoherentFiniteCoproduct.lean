module

public import StacksAndModuli.API.SchemeModulesCokernelFinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Finite coproducts of finitely presented quasicoherent module sheaves

Quasicoherent module sheaves are closed under coproducts, and finitely
presented quasicoherent module sheaves are closed under finite coproducts.
On an affine spectrum this follows from the tilde equivalence; finite
presentation reduces to the corresponding finite-product result for modules.
The general statements are obtained on affine opens.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_coproduct`;
* `AlgebraicGeometry.Scheme.Modules.finiteCoproduct_isFinitePresentation`.
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

/-- The biproduct of a small finite family of modules is its dependent
function module. -/
noncomputable def moduleCatFiniteBiproductIsoPi
    {R : Type u} [Ring R] {J : Type u} [Finite J]
    (F : J → ModuleCat.{u} R) :
    ((⨁ F) : ModuleCat.{u} R) ≅ ModuleCat.of R (∀ j, F j) :=
  IsLimit.conePointUniqueUpToIso (biproduct.isLimit F)
    (ModuleCat.HasLimit.productLimitCone F).isLimit

/-- On a spectrum, a coproduct of quasicoherent sheaves is the tilde of the
coproduct of their coordinate modules. -/
noncomputable def quasicoherentCoproductSpecTildeIso
    {R : CommRingCat.{u}} {J : Type u}
    (F : J → (Spec R).Modules) [∀ j, (F j).IsQuasicoherent] :
    (∐ F) ≅ (tilde.functor R).obj
      (∐ fun j ↦ moduleSpecΓFunctor.obj (F j)) := by
  letI := (tilde.adjunction (R := R)).leftAdjoint_preservesColimits
  letI (j : J) : IsIso (Scheme.Modules.fromTildeΓNatTrans.app (F j)) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (F j)
  exact Sigma.mapIso (fun j ↦
      (asIso (Scheme.Modules.fromTildeΓNatTrans.app (F j))).symm) ≪≫
    (PreservesCoproduct.iso (tilde.functor R)
      (fun j ↦ moduleSpecΓFunctor.obj (F j))).symm

/-- A coproduct of quasicoherent module sheaves on a spectrum is
quasicoherent. -/
lemma isQuasicoherent_coproduct_spec
    {R : CommRingCat.{u}} {J : Type u}
    (F : J → (Spec R).Modules) [∀ j, (F j).IsQuasicoherent] :
    (∐ F).IsQuasicoherent := by
  have hTilde : ((tilde.functor R).obj
      (∐ fun j ↦ moduleSpecΓFunctor.obj (F j))).IsQuasicoherent := by
    infer_instance
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (quasicoherentCoproductSpecTildeIso F).symm hTilde

/-- A coproduct of quasicoherent module sheaves on a scheme is
quasicoherent. -/
lemma isQuasicoherent_coproduct {X : Scheme.{u}} {J : Type u}
    (F : J → X.Modules) [∀ j, (F j).IsQuasicoherent] :
    (∐ F).IsQuasicoherent := by
  let _ (a : X.affineCover.I₀) :
      ((restrictFunctor (X.affineCover.f a)).obj (∐ F)).IsQuasicoherent := by
    letI (j : J) :
        ((restrictFunctor (X.affineCover.f a)).obj (F j)).IsQuasicoherent := by
      infer_instance
    letI : (∐ fun j ↦
        (restrictFunctor (X.affineCover.f a)).obj (F j)).IsQuasicoherent :=
      isQuasicoherent_coproduct_spec _
    exact (SheafOfModules.isQuasicoherent
      (X.affineCover.X a).ringCatSheaf).prop_of_iso
        (PreservesCoproduct.iso (restrictFunctor (X.affineCover.f a)) F).symm
        inferInstance
  exact isQuasicoherent_of_openCover_restrict _ X.affineCover

/-- A small-index version of `isQuasicoherent_coproduct`.  Reindexing by
`ULift` lets this apply to families such as `Fin m → X.Modules` when the
scheme itself lives in a larger universe. -/
lemma isQuasicoherent_coproduct_small {X : Scheme.{u}} {J : Type}
    (F : J → X.Modules) [∀ j, (F j).IsQuasicoherent] :
    (∐ F).IsQuasicoherent := by
  let G : ULift.{u} J → X.Modules := fun j ↦ F j.down
  letI (j : ULift.{u} J) : (G j).IsQuasicoherent := by
    dsimp only [G]
    infer_instance
  have hG : (∐ G).IsQuasicoherent := isQuasicoherent_coproduct G
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Sigma.reindex Equiv.ulift.{u, 0} F) hG

/-- The categorical coproduct of a finite family of finitely presented modules
is finitely presented. -/
lemma moduleCat_finiteCoproduct_finitePresentation
    {R : Type u} [CommRing R] {J : Type u} [Finite J]
    (F : J → ModuleCat.{u} R)
    [∀ j, Module.FinitePresentation R (F j)] :
    Module.FinitePresentation R (↑(∐ F)) := by
  letI := Fintype.ofFinite J
  letI : HasFiniteBiproducts (ModuleCat.{u} R) :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  have hPi : Module.FinitePresentation R (∀ j, F j) := by
    infer_instance
  letI : Module.FinitePresentation R (∀ j, F j) := hPi
  let e : (↑(∐ F)) ≃ₗ[R] (∀ j, F j) :=
    ((biproduct.isoCoproduct F).symm ≪≫
      moduleCatFiniteBiproductIsoPi F).toLinearEquiv
  exact Module.FinitePresentation.of_equiv e.symm

/-- On a spectrum, a finite coproduct of finitely presented quasicoherent
module sheaves is finitely presented. -/
lemma finiteCoproduct_isFinitePresentation_spec
    {R : CommRingCat.{u}} {J : Type u} [Finite J]
    (F : J → (Spec R).Modules)
    [∀ j, (F j).IsQuasicoherent] [∀ j, (F j).IsFinitePresentation] :
    (∐ F).IsFinitePresentation := by
  let G : J → ModuleCat.{u} R := fun j ↦ moduleSpecΓFunctor.obj (F j)
  have hG (j : J) : Module.FinitePresentation R (G j) :=
    moduleSpecΓFunctor_finitePresentation_of_isFinitePresentation (F j)
  letI (j : J) : Module.FinitePresentation R (G j) := hG j
  have hCop : Module.FinitePresentation R (↑(∐ G)) :=
    moduleCat_finiteCoproduct_finitePresentation G
  letI : Module.FinitePresentation R (↑(∐ G)) := hCop
  have hId : Module.FinitePresentation R
      (↑((Functor.id (ModuleCat R)).obj (∐ G))) := by
    simpa using hCop
  letI : Module.FinitePresentation R
      (↑((Functor.id (ModuleCat R)).obj (∐ G))) := hId
  have hTildeMod : Module.FinitePresentation R
      (moduleSpecΓFunctor.obj ((tilde.functor R).obj (∐ G))) :=
    Module.FinitePresentation.of_equiv
      (tilde.toTildeΓNatIso.app (∐ G)).toLinearEquiv
  letI : Module.FinitePresentation R
      (moduleSpecΓFunctor.obj ((tilde.functor R).obj (∐ G))) := hTildeMod
  have hTilde : ((tilde.functor R).obj (∐ G)).IsFinitePresentation :=
    isFinitePresentation_of_moduleSpecΓFunctor _
  exact ObjectProperty.prop_of_iso
    (P := SheafOfModules.isFinitePresentation (Spec R).ringCatSheaf)
    (quasicoherentCoproductSpecTildeIso F).symm hTilde

/-- On an affine scheme, a finite coproduct of finitely presented
quasicoherent module sheaves is finitely presented. -/
lemma finiteCoproduct_isFinitePresentation_of_isAffine
    {X : Scheme.{u}} [IsAffine X] {J : Type u} [Finite J]
    (F : J → X.Modules)
    [∀ j, (F j).IsQuasicoherent] [∀ j, (F j).IsFinitePresentation] :
    (∐ F).IsFinitePresentation := by
  let k : Spec Γ(X, ⊤) ⟶ X := X.isoSpec.inv
  let G : J → (Spec Γ(X, ⊤)).Modules := fun j ↦
    (restrictFunctor k).obj (F j)
  letI (j : J) : (G j).IsFinitePresentation :=
    isFinitePresentation_restrict k (F j)
  have hSpec : (∐ G).IsFinitePresentation :=
    finiteCoproduct_isFinitePresentation_spec G
  haveI := (restrictAdjunction k).leftAdjoint_preservesColimits
  have hRestrict : ((restrictFunctor k).obj (∐ F)).IsFinitePresentation :=
    ObjectProperty.prop_of_iso
      (P := SheafOfModules.isFinitePresentation (Spec Γ(X, ⊤)).ringCatSheaf)
      (PreservesCoproduct.iso (restrictFunctor k) F).symm hSpec
  letI : ((restrictFunctor k).obj (∐ F)).IsFinitePresentation := hRestrict
  have hBack : ((restrictFunctor X.isoSpec.hom).obj
      ((restrictFunctor k).obj (∐ F))).IsFinitePresentation :=
    isFinitePresentation_restrict X.isoSpec.hom _
  let eBack : (restrictFunctor X.isoSpec.hom).obj
      ((restrictFunctor k).obj (∐ F)) ≅ ∐ F :=
    (restrictFunctorComp X.isoSpec.hom X.isoSpec.inv).symm.app (∐ F) ≪≫
      (restrictFunctorCongr X.isoSpec.hom_inv_id).app (∐ F) ≪≫
      restrictFunctorId.app (∐ F)
  exact ObjectProperty.prop_of_iso
    (P := SheafOfModules.isFinitePresentation X.ringCatSheaf) eBack hBack

/-- A finite coproduct of finitely presented quasicoherent module sheaves on a
scheme is finitely presented. -/
lemma finiteCoproduct_isFinitePresentation
    {X : Scheme.{u}} {J : Type u} [Finite J]
    (F : J → X.Modules)
    [∀ j, (F j).IsQuasicoherent] [∀ j, (F j).IsFinitePresentation] :
    (∐ F).IsFinitePresentation := by
  letI : (∐ F).IsQuasicoherent := isQuasicoherent_coproduct F
  let presData (U : X.affineOpens) :
      { P : SheafOfModules.Presentation ((∐ F).restrict U.1.ι) // P.IsFinite } := by
    let G : J → U.1.toScheme.Modules := fun j ↦
      (restrictFunctor U.1.ι).obj (F j)
    letI (j : J) : (G j).IsFinitePresentation :=
      isFinitePresentation_restrict U.1.ι (F j)
    have hGU : (∐ G).IsFinitePresentation :=
      finiteCoproduct_isFinitePresentation_of_isAffine G
    haveI := (restrictAdjunction U.1.ι).leftAdjoint_preservesColimits
    have hRestrict : ((restrictFunctor U.1.ι).obj (∐ F)).IsFinitePresentation :=
      ObjectProperty.prop_of_iso
        (P := SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf)
        (PreservesCoproduct.iso (restrictFunctor U.1.ι) F).symm hGU
    letI : ((restrictFunctor U.1.ι).obj (∐ F)).IsFinitePresentation := hRestrict
    let h := exists_finitePresentation_of_isFinitePresentation_affine
      ((restrictFunctor U.1.ι).obj (∐ F))
    exact ⟨Classical.choose h, Classical.choose_spec h⟩
  let pres (U : X.affineOpens) :
      SheafOfModules.Presentation ((∐ F).restrict U.1.ι) :=
    (presData U).1
  letI (U : X.affineOpens) : (pres U).IsFinite := (presData U).2
  exact isFinitePresentation_of_isOpenCover (∐ F)
    (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X) pres

/-- A small-index version of `finiteCoproduct_isFinitePresentation`.  This
removes the artificial universe mismatch for a finite family indexed by a
type such as `Fin m`. -/
lemma finiteCoproduct_isFinitePresentation_small
    {X : Scheme.{u}} {J : Type} [Finite J]
    (F : J → X.Modules)
    [∀ j, (F j).IsQuasicoherent] [∀ j, (F j).IsFinitePresentation] :
    (∐ F).IsFinitePresentation := by
  let G : ULift.{u} J → X.Modules := fun j ↦ F j.down
  letI (j : ULift.{u} J) : (G j).IsQuasicoherent := by
    dsimp only [G]
    infer_instance
  letI (j : ULift.{u} J) : (G j).IsFinitePresentation := by
    dsimp only [G]
    infer_instance
  have hG : (∐ G).IsFinitePresentation :=
    finiteCoproduct_isFinitePresentation G
  exact ObjectProperty.prop_of_iso
    (P := SheafOfModules.isFinitePresentation X.ringCatSheaf)
    (Sigma.reindex Equiv.ulift.{u, 0} F) hG

end AlgebraicGeometry.Scheme.Modules

end
