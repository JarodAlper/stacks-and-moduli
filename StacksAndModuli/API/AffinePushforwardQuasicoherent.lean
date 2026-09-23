module

public import StacksAndModuli.«Section3.1-Descent».«part3.1.2-descent-quasi-coherent»
public import StacksAndModuli.API.OpenImmersionModuleBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Quasicoherent pushforward along affine morphisms

This file proves that pushforward of quasicoherent modules along an affine morphism of
schemes is quasicoherent.  The main geometric input is an explicit Beck--Chevalley
isomorphism for restriction across a Cartesian square whose vertical maps are open
immersions.  Localizing on an affine cover of the target then reduces the result to the
`Spec` case established in the quasicoherent-descent API.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- On affine schemes, restriction across the canonical `isoSpec` maps identifies
pushforward with pushforward along the induced map of spectra. -/
noncomputable def restrictPushforwardIsoSpec (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y] (M : X.Modules) :
    (restrictFunctor Y.isoSpec.inv).obj ((pushforward f).obj M) ≅
      (pushforward (Spec.map f.appTop)).obj
        ((restrictFunctor X.isoSpec.inv).obj M) :=
  restrictPushforwardIsoOfOpenSquare f (Spec.map f.appTop)
    X.isoSpec.inv Y.isoSpec.inv (Scheme.isoSpec_inv_naturality f)
    (image_preimage_eq_of_isIso_square f (Spec.map f.appTop)
      X.isoSpec.inv Y.isoSpec.inv (Scheme.isoSpec_inv_naturality f)) M

set_option backward.isDefEq.respectTransparency.types false in
private lemma isQuasicoherent_overEquiv_inverse_aux (U : X.Opens)
    (N : U.toScheme.Modules) [N.IsQuasicoherent] :
    ((overEquiv U).inverse.obj N).IsQuasicoherent := by
  let _ := U.instIsDenseSubsiteSubtypeMemOverGrothendieckTopologyOverInverseOverEquivalence
  let _ (Z : Over U) :
      (Over.post (X := Z) U.overEquivalence.symm.inverse).IsContinuous
        (((Opens.grothendieckTopology X).over U).over Z)
        ((Opens.grothendieckTopology U.carrier).over
          (U.overEquivalence.symm.inverse.obj Z)) := by
    have h : CoverPreserving
        ((Opens.grothendieckTopology X).over U)
        (Opens.grothendieckTopology U.carrier)
        U.overEquivalence.functor :=
      Functor.IsDenseSubsite.coverPreserving
        ((Opens.grothendieckTopology X).over U)
        (Opens.grothendieckTopology U.carrier) U.overEquivalence.functor
    apply Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _
        (Over.post (X := Z) U.overEquivalence.symm.inverse))
    exact h.overPost Z
  dsimp [overEquiv, TopologicalSpace.Opens.sheafOfModulesEquivOver]
  apply SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    (η := U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)

private lemma isQuasicoherent_of_restrict_iso_aux
    {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules)
    [((restrictFunctor e.hom).obj M).IsQuasicoherent] : M.IsQuasicoherent := by
  let _ : ((restrictFunctor e.inv).obj
      ((restrictFunctor e.hom).obj M)).IsQuasicoherent := by infer_instance
  let iso : M ≅ (restrictFunctor e.inv).obj
      ((restrictFunctor e.hom).obj M) :=
    ((restrictFunctorId.app M).symm ≪≫
      (restrictFunctorCongr e.inv_hom_id).symm.app M) ≪≫
        (restrictFunctorComp e.inv e.hom).app M
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso iso.symm inferInstance

private lemma isQuasicoherent_of_schemeOpenCover_aux
    (M : X.Modules) (𝒰 : Scheme.OpenCover.{u} X)
    [∀ i, ((restrictFunctor (𝒰.f i)).obj M).IsQuasicoherent] :
    M.IsQuasicoherent := by
  let _ (i : 𝒰.I₀) :
      ((restrictFunctor (𝒰.f i).opensRange.ι).obj M).IsQuasicoherent := by
    let e : 𝒰.X i ≅ (𝒰.f i).opensRange.toScheme :=
      IsOpenImmersion.isoOfRangeEq (𝒰.f i) (𝒰.f i).opensRange.ι (by simp)
    let N := (restrictFunctor (𝒰.f i).opensRange.ι).obj M
    let iso : (restrictFunctor (𝒰.f i)).obj M ≅
        (restrictFunctor e.hom).obj N :=
      (restrictFunctorCongr
          (IsOpenImmersion.isoOfRangeEq_hom_fac (𝒰.f i)
            (𝒰.f i).opensRange.ι (by simp))).symm.app M ≪≫
        (restrictFunctorComp e.hom (𝒰.f i).opensRange.ι).app M
    let _ : ((restrictFunctor e.hom).obj N).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (𝒰.X i).ringCatSheaf).prop_of_iso iso
        (by infer_instance)
    exact isQuasicoherent_of_restrict_iso_aux e N
  have hcov : (_root_.Opens.grothendieckTopology (X : Type u)).CoversTop
      (fun i : 𝒰.I₀ ↦ (𝒰.f i).opensRange) := by
    rw [_root_.Opens.coversTop_iff]
    exact 𝒰.isOpenCover_opensRange
  let _ (i : 𝒰.I₀) : (M.over (𝒰.f i).opensRange).IsQuasicoherent := by
    let U := (𝒰.f i).opensRange
    let e := overEquiv U
    let oe := overFunctorEquiv U
    let _ : (e.inverse.obj ((restrictFunctor U.ι).obj M)).IsQuasicoherent :=
      isQuasicoherent_overEquiv_inverse_aux U _
    let iso : e.inverse.obj ((restrictFunctor U.ι).obj M) ≅ M.over U :=
      e.inverse.mapIso (oe.app M).symm ≪≫ (e.unitIso.app _).symm
    exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso iso
      (by infer_instance)
  exact SheafOfModules.IsQuasicoherent.of_coversTop M
    (fun i : 𝒰.I₀ ↦ (𝒰.f i).opensRange) hcov

/-- The structure sheaf, regarded as a module over itself, is quasicoherent. -/
lemma unit_isQuasicoherent (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := by
  let 𝒰 := X.affineOpenCover
  let _ (i : 𝒰.openCover.I₀) :
      (SheafOfModules.unit (𝒰.openCover.X i).ringCatSheaf).IsQuasicoherent := by
    change (SheafOfModules.unit (Spec (𝒰.X i)).ringCatSheaf).IsQuasicoherent
    exact (SheafOfModules.isQuasicoherent (Spec (𝒰.X i)).ringCatSheaf).prop_of_iso
      (AlgebraicGeometry.tildeSelf (R := 𝒰.X i)) inferInstance
  let _ (i : 𝒰.openCover.I₀) : ((restrictFunctor (𝒰.openCover.f i)).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (𝒰.openCover.X i).ringCatSheaf).prop_of_iso
      (restrictUnitIso (𝒰.openCover.f i)).symm inferInstance
  exact isQuasicoherent_of_schemeOpenCover_aux _ 𝒰.openCover

/-- Pushforward of a quasicoherent module along a morphism between affine schemes is
quasicoherent. -/
lemma isQuasicoherent_pushforward_of_affine_schemes (f : X ⟶ Y)
    [IsAffine X] [IsAffine Y] (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  let N := (pushforward f).obj M
  let _ : ((restrictFunctor X.isoSpec.inv).obj M).IsQuasicoherent := by
    infer_instance
  let _ : ((pushforward (Spec.map f.appTop)).obj
      ((restrictFunctor X.isoSpec.inv).obj M)).IsQuasicoherent :=
    isQuasicoherent_pushforward_Spec f.appTop _
  let _ : ((restrictFunctor Y.isoSpec.inv).obj N).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(Y, ⊤)).ringCatSheaf).prop_of_iso
      (restrictPushforwardIsoSpec f M).symm inferInstance
  let _ : ((restrictFunctor Y.isoSpec.symm.hom).obj N).IsQuasicoherent := by
    change ((restrictFunctor Y.isoSpec.inv).obj N).IsQuasicoherent
    infer_instance
  exact isQuasicoherent_of_restrict_iso_aux Y.isoSpec.symm N

/-- Pushforward of a quasicoherent module along an affine morphism of schemes is
quasicoherent. -/
lemma isQuasicoherent_pushforward_of_isAffineHom (f : X ⟶ Y) [IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  let N := (pushforward f).obj M
  let 𝒰 := Y.affineCover
  let _ (i : 𝒰.I₀) : ((restrictFunctor (𝒰.f i)).obj N).IsQuasicoherent := by
    let j := 𝒰.f i
    let P := CategoryTheory.Limits.pullback f j
    let pX : P ⟶ X := pullback.fst f j
    let pU : P ⟶ 𝒰.X i := pullback.snd f j
    let _ : IsAffine P := by dsimp [P, j]; infer_instance
    let _ : ((restrictFunctor pX).obj M).IsQuasicoherent := by infer_instance
    let _ : ((pushforward pU).obj
        ((restrictFunctor pX).obj M)).IsQuasicoherent :=
      isQuasicoherent_pushforward_of_affine_schemes pU _
    exact (SheafOfModules.isQuasicoherent (𝒰.X i).ringCatSheaf).prop_of_iso
      (restrictPushforwardIsoOfOpenSquare f pU pX j
        (by dsimp [pU, pX, j]; exact pullback.condition.symm)
        (fun W ↦ IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
          (.flip <| .of_hasPullback f j) W) M).symm inferInstance
  exact isQuasicoherent_of_schemeOpenCover_aux N 𝒰

end AlgebraicGeometry.Scheme.Modules
