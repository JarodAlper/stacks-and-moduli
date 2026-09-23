module

public import StacksAndModuli.API.CanonicalAffineGlobalSectionsBaseChange
public import StacksAndModuli.API.FlatGlobalSectionsBaseChange
public import StacksAndModuli.API.PrincipalClosedFiberCokernel

/-!
# Canonical base change on affine open squares

This file compares the restriction of a pullback module to an inverse-image open
with the pullback of the restricted module.  The Beck--Chevalley comparison is
shown to carry the global adjunction unit to the restricted adjunction unit.
Combined with canonical affine base change, this proves bijectivity of the
canonical open-section base-change map on every affine cartesian open square.

Main declarations:

* `Scheme.Modules.restrictPullbackOpenSectionsLinearEquiv_unit`;
* `Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_bijective_of_isPullback`;
* `Scheme.Modules.pullbackOpenSectionsBaseChangeLinearMap_bijective_of_isPullback`.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable def Scheme.Modules.openSectionsLinearEquivOfEq
    {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)
    (M : X.Modules) {U V : X.Opens} (hUV : U = V) :
    letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule p M U
    letI : Module R Γ(M, V) := Scheme.Modules.openSectionsModule p M V
    Γ(M, U) ≃ₗ[R] Γ(M, V) := by
  letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule p M U
  letI : Module R Γ(M, V) := Scheme.Modules.openSectionsModule p M V
  let eCat : M.presheaf.obj (Opposite.op U) ≅
      M.presheaf.obj (Opposite.op V) :=
    M.presheaf.mapIso (eqToIso hUV.symm).op
  exact
    { toEquiv :=
        { toFun := eCat.hom.hom
          invFun := eCat.inv.hom
          left_inv := fun m ↦ by simp
          right_inv := fun m ↦ by simp }
      map_add' := fun x y ↦ map_add eCat.hom.hom x y
      map_smul' := fun r m ↦ by
        change M.presheaf.map (eqToHom hUV.symm).op
            (Scheme.Modules.openBaseRingHom p U r • m) =
          Scheme.Modules.openBaseRingHom p V r •
            M.presheaf.map (eqToHom hUV.symm).op m
        rw [M.map_smul]
        congr 1
        change X.presheaf.map (eqToHom hUV.symm).op
            (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
              ((Scheme.Modules.baseRingHom p).hom r)) =
          X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
            ((Scheme.Modules.baseRingHom p).hom r)
        rw [← X.presheaf.map_comp_apply]
        rfl }

noncomputable def Scheme.Modules.pullbackOpenImageTopSectionsLinearEquiv
    {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)
    (M : X.Modules) (U : X.Opens) :
    let j := U.ι
    let MU := (Scheme.Modules.pullback j).obj M
    letI : Module R Γ(M, j ''ᵁ (⊤ : U.toScheme.Opens)) :=
      Scheme.Modules.openSectionsModule p M (j ''ᵁ (⊤ : U.toScheme.Opens))
    letI : Module R Γ(MU, ⊤) :=
      Scheme.Modules.globalSectionsModule (j ≫ p) MU
    Γ(M, j ''ᵁ (⊤ : U.toScheme.Opens)) ≃ₗ[R] Γ(MU, ⊤) := by
  let j := U.ι
  let MU := (Scheme.Modules.pullback j).obj M
  letI : Module R Γ(M, j ''ᵁ (⊤ : U.toScheme.Opens)) :=
    Scheme.Modules.openSectionsModule p M (j ''ᵁ (⊤ : U.toScheme.Opens))
  letI : Module R Γ(MU, ⊤) :=
    Scheme.Modules.globalSectionsModule (j ≫ p) MU
  let e := (Scheme.Modules.restrictFunctorIsoPullback j).app M
  let eTopCat : ((M.restrict j).val.obj (Opposite.op ⊤)) ≅
      (MU.val.obj (Opposite.op ⊤)) :=
    { hom := e.hom.val.app (Opposite.op ⊤)
      inv := e.inv.val.app (Opposite.op ⊤)
      hom_inv_id := congrArg (fun k ↦ k.val.app (Opposite.op ⊤)) e.hom_inv_id
      inv_hom_id := congrArg (fun k ↦ k.val.app (Opposite.op ⊤)) e.inv_hom_id }
  let eRestr : Γ(M.restrict j, ⊤) ≃+ Γ(M, j ''ᵁ (⊤ : U.toScheme.Opens)) :=
    { toFun := (M.restrictAppIso j ⊤).hom
      invFun := (M.restrictAppIso j ⊤).inv
      left_inv := fun m ↦ by simp
      right_inv := fun m ↦ by simp
      map_add' := fun x y ↦ map_add _ x y }
  let eAdd := eRestr.symm.trans eTopCat.toLinearEquiv.toAddEquiv
  exact
    { toEquiv := eAdd.toEquiv
      map_add' := eAdd.map_add
      map_smul' := fun r m ↦ by
        change e.hom.app ⊤ ((M.restrictAppIso j ⊤).inv
            (Scheme.Modules.openBaseRingHom p (j ''ᵁ (⊤ : U.toScheme.Opens)) r • m)) =
          (Scheme.Modules.baseRingHom (j ≫ p)).hom r •
            e.hom.app ⊤ ((M.restrictAppIso j ⊤).inv m)
        rw [show (M.restrictAppIso j ⊤).inv
            (Scheme.Modules.openBaseRingHom p (j ''ᵁ (⊤ : U.toScheme.Opens)) r • m) =
          (j.appIso ⊤).hom
              (Scheme.Modules.openBaseRingHom p
                (j ''ᵁ (⊤ : U.toScheme.Opens)) r) •
            (M.restrictAppIso j ⊤).inv m by simp]
        rw [Scheme.Modules.Hom.app_smul]
        congr 1
        rw [← Scheme.Modules.baseRingHom_comp_appTop,
          ConcreteCategory.comp_apply]
        dsimp only [j]
        simp only [Scheme.Opens.ι_appIso, Iso.refl_hom,
          Scheme.Modules.openBaseRingHom, Scheme.Opens.ι_appTop,
          CommRingCat.hom_id, RingHom.comp_apply]
        exact RingHom.id_apply _ }

noncomputable def Scheme.Modules.pullbackOpenSectionsLinearEquiv
    {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)
    (M : X.Modules) (U : X.Opens) :
    let MU := (Scheme.Modules.pullback U.ι).obj M
    letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule p M U
    letI : Module R Γ(MU, ⊤) :=
      Scheme.Modules.globalSectionsModule (U.ι ≫ p) MU
    Γ(M, U) ≃ₗ[R] Γ(MU, ⊤) := by
  let MU := (Scheme.Modules.pullback U.ι).obj M
  letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule p M U
  letI : Module R Γ(M,
      U.ι ''ᵁ (⊤ : U.toScheme.Opens)) :=
    Scheme.Modules.openSectionsModule p M (U.ι ''ᵁ (⊤ : U.toScheme.Opens))
  letI : Module R Γ(MU, ⊤) :=
    Scheme.Modules.globalSectionsModule (U.ι ≫ p) MU
  exact (Scheme.Modules.openSectionsLinearEquivOfEq p M U.ι_image_top.symm).trans
    (Scheme.Modules.pullbackOpenImageTopSectionsLinearEquiv p M U)


noncomputable def Scheme.Modules.pullbackOpenTargetSectionsLinearEquiv
    {S : CommRingCat.{u}} {X Y : Scheme.{u}} (g : Y ⟶ X)
    (pY : Y ⟶ Spec S) (M : X.Modules) (U : X.Opens) :
    let V := g ⁻¹ᵁ U
    let N := (Scheme.Modules.pullback g).obj M
    let MU := (Scheme.Modules.pullback U.ι).obj M
    let NVU := (Scheme.Modules.pullback (g ∣_ U)).obj MU
    letI : Module S Γ(N, V) := Scheme.Modules.openSectionsModule pY N V
    letI : Module S Γ(NVU, ⊤) :=
      Scheme.Modules.globalSectionsModule (V.ι ≫ pY) NVU
    Γ(N, V) ≃ₗ[S] Γ(NVU, ⊤) := by
  let V := g ⁻¹ᵁ U
  let N := (Scheme.Modules.pullback g).obj M
  let MU := (Scheme.Modules.pullback U.ι).obj M
  let NVU := (Scheme.Modules.pullback (g ∣_ U)).obj MU
  letI : Module S Γ(N, V) := Scheme.Modules.openSectionsModule pY N V
  letI : Module S Γ((Scheme.Modules.pullback V.ι).obj N, ⊤) :=
    Scheme.Modules.globalSectionsModule (V.ι ≫ pY) _
  letI : Module S Γ(NVU, ⊤) :=
    Scheme.Modules.globalSectionsModule (V.ι ≫ pY) NVU
  let eOpen := Scheme.Modules.pullbackOpenSectionsLinearEquiv pY N V
  let eComp := Scheme.Modules.Hom.pullbackCompCongrIso V.ι g
    (g ∣_ U) U.ι (morphismRestrict_ι g U).symm M
  exact eOpen.trans
    (Scheme.Modules.globalSectionsLinearEquivOfIso (V.ι ≫ pY) eComp)

noncomputable def Scheme.Modules.restrictOpenSectionsLinearEquiv
    {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)
    (M : X.Modules) (U : X.Opens) :
    let MU := (Scheme.Modules.restrictFunctor U.ι).obj M
    letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule p M U
    letI : Module R Γ(MU, ⊤) :=
      Scheme.Modules.globalSectionsModule (U.ι ≫ p) MU
    Γ(M, U) ≃ₗ[R] Γ(MU, ⊤) := by
  let j := U.ι
  let MU := (Scheme.Modules.restrictFunctor U.ι).obj M
  letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule p M U
  letI : Module R Γ(M, j ''ᵁ (⊤ : U.toScheme.Opens)) :=
    Scheme.Modules.openSectionsModule p M (j ''ᵁ (⊤ : U.toScheme.Opens))
  letI : Module R Γ(MU, ⊤) :=
    Scheme.Modules.globalSectionsModule (U.ι ≫ p) MU
  let eEq := Scheme.Modules.openSectionsLinearEquivOfEq p M U.ι_image_top.symm
  let eRestr : Γ(M.restrict j, ⊤) ≃+ Γ(M, j ''ᵁ (⊤ : U.toScheme.Opens)) :=
    { toFun := (M.restrictAppIso j ⊤).hom
      invFun := (M.restrictAppIso j ⊤).inv
      left_inv := fun m ↦ by simp
      right_inv := fun m ↦ by simp
      map_add' := fun x y ↦ map_add _ x y }
  let eAdd := eEq.toAddEquiv.trans eRestr.symm
  exact
    { toEquiv := eAdd.toEquiv
      map_add' := eAdd.map_add
      map_smul' := fun r m ↦ by
        change (M.restrictAppIso j ⊤).inv
            (eEq (Scheme.Modules.openBaseRingHom p U r • m)) =
          (Scheme.Modules.baseRingHom (j ≫ p)).hom r •
            (M.restrictAppIso j ⊤).inv (eEq m)
        have heEq := eEq.map_smul r m
        change eEq (Scheme.Modules.openBaseRingHom p U r • m) =
          Scheme.Modules.openBaseRingHom p
              (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) r • eEq m at heEq
        rw [heEq]
        rw [show (M.restrictAppIso j ⊤).inv
            (Scheme.Modules.openBaseRingHom p
                (j ''ᵁ (⊤ : U.toScheme.Opens)) r • eEq m) =
          (j.appIso ⊤).hom
              (Scheme.Modules.openBaseRingHom p
                (j ''ᵁ (⊤ : U.toScheme.Opens)) r) •
            (M.restrictAppIso j ⊤).inv (eEq m) by simp]
        congr 1
        rw [← Scheme.Modules.baseRingHom_comp_appTop,
          ConcreteCategory.comp_apply]
        dsimp only [j]
        simp only [Scheme.Opens.ι_appIso, Iso.refl_hom,
          Scheme.Modules.openBaseRingHom, Scheme.Opens.ι_appTop,
          CommRingCat.hom_id, RingHom.comp_apply]
        exact RingHom.id_apply _ }

lemma Scheme.Modules.restrictAppIso_inv_apply
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (U : X.Opens) (m : Γ(M, f ''ᵁ U)) :
    (M.restrictAppIso f U).inv m = m := rfl

noncomputable def Scheme.Modules.restrictPushPullIsoOfOpenSquare'
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (N : Z.Modules) :
    (Scheme.Modules.restrictFunctor j).obj
        ((Scheme.Modules.pushforward i).obj
          ((Scheme.Modules.pullback i).obj N)) ≅
      (Scheme.Modules.pushforward g).obj
        ((Scheme.Modules.pullback g).obj
          ((Scheme.Modules.restrictFunctor j).obj N)) :=
  Scheme.Modules.restrictPushforwardIsoOfOpenSquare i g k j hsq hopen
      ((Scheme.Modules.pullback i).obj N) ≪≫
    (Scheme.Modules.pushforward g).mapIso
      ((Scheme.Modules.restrictPullbackIsoOfOpenSquare i g k j hsq).app N)

@[reassoc]
lemma Scheme.Modules.map_unit_restrictPushPullIsoOfOpenSquare'_hom
    {Y Z W P : Scheme.{u}} (i : W ⟶ Z) (g : P ⟶ Y)
    (k : P ⟶ W) (j : Y ⟶ Z) [IsOpenImmersion k] [IsOpenImmersion j]
    (hsq : g ≫ j = k ≫ i)
    (hopen : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (N : Z.Modules) :
    (Scheme.Modules.restrictFunctor j).map
        ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N) ≫
      (Scheme.Modules.restrictPushPullIsoOfOpenSquare'
        i g k j hsq hopen N).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      ((Scheme.Modules.restrictFunctor j).obj N) := by
  let L := (Scheme.Modules.pullback i).obj N
  let bc := Scheme.Modules.restrictPushforwardIsoOfOpenSquare
    i g k j hsq hopen L
  let α := Scheme.Modules.restrictPullbackIsoOfOpenSquare i g k j hsq
  change (Scheme.Modules.restrictFunctor j).map
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N) ≫
        (bc ≪≫ (Scheme.Modules.pushforward g).mapIso (α.app N)).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Scheme.Modules.restrictFunctor j).obj N)
  refine ((Scheme.Modules.restrictAdjunction j).homEquiv N _).injective ?_
  rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
  rw [← cancel_mono ((Scheme.Modules.pushforwardComp g j).hom.app
    ((Scheme.Modules.restrictFunctor j ⋙
      Scheme.Modules.pullback g).obj N))]
  have hadj := Scheme.Modules.unit_restrictPullbackIsoOfOpenSquare_hom
    i g k j hsq N
  have hadj' := congrArg (fun q ↦ q ≫
    (Scheme.Modules.pushforwardComp g j).hom.app
      ((Scheme.Modules.restrictFunctor j ⋙
        Scheme.Modules.pullback g).obj N)) hadj
  simp only [Scheme.Modules.pushforwardCompIsoOfSquare, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc] at hadj'
  rw [← (Scheme.Modules.pushforwardComp g j).inv.naturality_assoc
    (α.hom.app N)] at hadj'
  simp only [Iso.inv_hom_id_app, Category.comp_id] at hadj'
  have hadjCommon :
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N ≫
          (Scheme.Modules.pushforward i).map
            ((Scheme.Modules.restrictAdjunction k).unit.app L) ≫
          (Scheme.Modules.pushforwardComp k i).hom.app
            ((Scheme.Modules.pullback i ⋙
              Scheme.Modules.restrictFunctor k).obj N) ≫
          (Scheme.Modules.pushforwardCongr hsq.symm).hom.app
            ((Scheme.Modules.pullback i ⋙
              Scheme.Modules.restrictFunctor k).obj N) ≫
          (Scheme.Modules.pushforward (g ≫ j)).map (α.hom.app N) =
        (Scheme.Modules.restrictAdjunction j).unit.app N ≫
          (Scheme.Modules.pushforward j).map
            ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
              ((Scheme.Modules.restrictFunctor j).obj N)) ≫
          (Scheme.Modules.pushforwardComp g j).hom.app
            ((Scheme.Modules.restrictFunctor j ⋙
              Scheme.Modules.pullback g).obj N) := by
    exact hadj'
  have hunit :
      (Scheme.Modules.restrictAdjunction j).unit.app N ≫
          (Scheme.Modules.pushforward j).map
            ((Scheme.Modules.restrictFunctor j).map
              ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N)) =
        (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N ≫
          (Scheme.Modules.restrictAdjunction j).unit.app
            ((Scheme.Modules.pushforward i).obj L) := by
    simpa only [Functor.id_obj, Functor.id_map, Functor.comp_obj,
      Functor.comp_map] using
        ((Scheme.Modules.restrictAdjunction j).unit.naturality
          ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app N)).symm
  have hcomp :
      (Scheme.Modules.pushforward j).map
            ((Scheme.Modules.pushforward g).map ((α.app N).hom)) ≫
          (Scheme.Modules.pushforwardComp g j).hom.app
            ((Scheme.Modules.restrictFunctor j ⋙
              Scheme.Modules.pullback g).obj N) =
        (Scheme.Modules.pushforwardComp g j).hom.app
            ((Scheme.Modules.pullback i ⋙
              Scheme.Modules.restrictFunctor k).obj N) ≫
          (Scheme.Modules.pushforward (g ≫ j)).map ((α.app N).hom) := by
    simpa only [Functor.comp_obj, Functor.comp_map] using
      (Scheme.Modules.pushforwardComp g j).hom.naturality ((α.app N).hom)
  have hbc :
      (Scheme.Modules.restrictAdjunction j).unit.app
            ((Scheme.Modules.pushforward i).obj L) ≫
          (Scheme.Modules.pushforward j).map bc.hom ≫
          (Scheme.Modules.pushforwardComp g j).hom.app
            ((Scheme.Modules.pullback i ⋙
              Scheme.Modules.restrictFunctor k).obj N) =
        (Scheme.Modules.pushforward i).map
            ((Scheme.Modules.restrictAdjunction k).unit.app L) ≫
          (Scheme.Modules.pushforwardComp k i).hom.app
            ((Scheme.Modules.pullback i ⋙
              Scheme.Modules.restrictFunctor k).obj N) ≫
          (Scheme.Modules.pushforwardCongr hsq.symm).hom.app
            ((Scheme.Modules.pullback i ⋙
              Scheme.Modules.restrictFunctor k).obj N) := by
    simpa only [bc, L, Functor.comp_obj] using
      Scheme.Modules.unit_restrictPushforwardIsoOfOpenSquare_hom
        i g k j hsq hopen L
  have hbcPost :
      (Scheme.Modules.restrictAdjunction j).unit.app
            ((Scheme.Modules.pushforward i).obj L) ≫
          (Scheme.Modules.pushforward j).map bc.hom ≫
          (Scheme.Modules.pushforwardComp g j).hom.app
              ((Scheme.Modules.pullback i ⋙
                Scheme.Modules.restrictFunctor k).obj N) ≫
          (Scheme.Modules.pushforward (g ≫ j)).map ((α.app N).hom) =
        (Scheme.Modules.pushforward i).map
            ((Scheme.Modules.restrictAdjunction k).unit.app L) ≫
          (Scheme.Modules.pushforwardComp k i).hom.app
              ((Scheme.Modules.pullback i ⋙
                Scheme.Modules.restrictFunctor k).obj N) ≫
          (Scheme.Modules.pushforwardCongr hsq.symm).hom.app
              ((Scheme.Modules.pullback i ⋙
                Scheme.Modules.restrictFunctor k).obj N) ≫
          (Scheme.Modules.pushforward (g ≫ j)).map ((α.app N).hom) := by
    simpa only [Category.assoc] using congrArg
      (fun q ↦ q ≫
        (Scheme.Modules.pushforward (g ≫ j)).map ((α.app N).hom)) hbc
  simp only [Category.assoc]
  rw [← Category.assoc, hunit]
  simp only [Category.assoc]
  rw [hcomp]
  rw [hbcPost]
  exact hadjCommon

noncomputable def Scheme.Modules.restrictPullbackOpenSectionsLinearEquiv
    {S : CommRingCat.{u}} {X Y : Scheme.{u}} (g : Y ⟶ X)
    (pY : Y ⟶ Spec S) (M : X.Modules) (U : X.Opens) :
    let V := g ⁻¹ᵁ U
    let b := Scheme.Modules.restrictToPreimage g U
    let N := (Scheme.Modules.pullback g).obj M
    let MU := (Scheme.Modules.restrictFunctor U.ι).obj M
    let NVU := (Scheme.Modules.pullback b).obj MU
    letI : Module S Γ(N, V) := Scheme.Modules.openSectionsModule pY N V
    letI : Module S Γ(NVU, ⊤) :=
      Scheme.Modules.globalSectionsModule (V.ι ≫ pY) NVU
    Γ(N, V) ≃ₗ[S] Γ(NVU, ⊤) := by
  let V := g ⁻¹ᵁ U
  let b := Scheme.Modules.restrictToPreimage g U
  let N := (Scheme.Modules.pullback g).obj M
  let MU := (Scheme.Modules.restrictFunctor U.ι).obj M
  let NVU := (Scheme.Modules.pullback b).obj MU
  letI : Module S Γ(N, V) := Scheme.Modules.openSectionsModule pY N V
  letI : Module S Γ((Scheme.Modules.restrictFunctor V.ι).obj N, ⊤) :=
    Scheme.Modules.globalSectionsModule (V.ι ≫ pY) _
  letI : Module S Γ(NVU, ⊤) :=
    Scheme.Modules.globalSectionsModule (V.ι ≫ pY) NVU
  have hsq : b ≫ U.ι = V.ι ≫ g := by
    dsimp only [b, Scheme.Modules.restrictToPreimage]
    exact g.resLE_comp_ι le_rfl
  let α := Scheme.Modules.restrictPullbackIsoOfOpenSquare g b V.ι U.ι hsq
  exact (Scheme.Modules.restrictOpenSectionsLinearEquiv pY N V).trans
    (Scheme.Modules.globalSectionsLinearEquivOfIso (V.ι ≫ pY) (α.app M))

@[simp]
lemma Scheme.Modules.globalSectionsLinearEquivOfIso_apply
    {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R)
    {M N : X.Modules} (e : M ≅ N) (m : Γ(M, ⊤)) :
    letI := Scheme.Modules.globalSectionsModule p M
    letI := Scheme.Modules.globalSectionsModule p N
    Scheme.Modules.globalSectionsLinearEquivOfIso p e m =
      Scheme.Modules.Hom.app e.hom ⊤ m := by
  rfl

set_option maxHeartbeats 800000 in
-- The explicit Beck--Chevalley component calculation needs additional elaboration time.
/-- The canonical pullback section over an open agrees, after the restriction
comparison, with the canonical pullback of the corresponding global section on
the restricted schemes. -/
lemma Scheme.Modules.restrictPullbackOpenSectionsLinearEquiv_unit
    {R S : CommRingCat.{u}} {X Y : Scheme.{u}} (g : Y ⟶ X)
    (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    let V := g ⁻¹ᵁ U
    let b := Scheme.Modules.restrictToPreimage g U
    let N := (Scheme.Modules.pullback g).obj M
    let MU := (Scheme.Modules.restrictFunctor U.ι).obj M
    let NVU := (Scheme.Modules.pullback b).obj MU
    letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule pX M U
    letI : Module R Γ(MU, ⊤) :=
      Scheme.Modules.globalSectionsModule (U.ι ≫ pX) MU
    letI : Module S Γ(N, V) := Scheme.Modules.openSectionsModule pY N V
    letI : Module S Γ(NVU, ⊤) :=
      Scheme.Modules.globalSectionsModule (V.ι ≫ pY) NVU
    Scheme.Modules.restrictPullbackOpenSectionsLinearEquiv g pY M U
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U m) =
      Scheme.Modules.pullbackGlobalSections b MU
        (Scheme.Modules.restrictOpenSectionsLinearEquiv pX M U m) := by
  dsimp only
  let V := g ⁻¹ᵁ U
  let b := Scheme.Modules.restrictToPreimage g U
  let N := (Scheme.Modules.pullback g).obj M
  let MU := (Scheme.Modules.restrictFunctor U.ι).obj M
  let NVU := (Scheme.Modules.pullback b).obj MU
  letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule pX M U
  letI : Module R Γ(MU, ⊤) :=
    Scheme.Modules.globalSectionsModule (U.ι ≫ pX) MU
  letI : Module S Γ(N, V) := Scheme.Modules.openSectionsModule pY N V
  letI : Module S Γ(NVU, ⊤) :=
    Scheme.Modules.globalSectionsModule (V.ι ≫ pY) NVU
  have hsq : b ≫ U.ι = V.ι ≫ g := by
    dsimp only [b, Scheme.Modules.restrictToPreimage]
    exact g.resLE_comp_ι le_rfl
  let hopen : ∀ W : U.toScheme.Opens,
      V.ι ''ᵁ (b ⁻¹ᵁ W) = g ⁻¹ᵁ (U.ι ''ᵁ W) :=
    Scheme.Modules.image_preimage_restrict_eq g U
  have hmap := Scheme.Modules.map_unit_restrictPushPullIsoOfOpenSquare'_hom
    g b V.ι U.ι hsq hopen M
  let mU : Γ(MU, ⊤) :=
    Scheme.Modules.restrictOpenSectionsLinearEquiv pX M U m
  let bc := Scheme.Modules.restrictPushforwardIsoOfOpenSquare
    g b V.ι U.ι hsq hopen N
  have hres :
      Scheme.Modules.Hom.app bc.hom ⊤
          (Scheme.Modules.Hom.app
            ((Scheme.Modules.restrictFunctor U.ι).map
              ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)) ⊤ mU) =
        Scheme.Modules.restrictOpenSectionsLinearEquiv pY N V
          (Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) U m) := by
    dsimp only [bc]
    change N.presheaf.map (eqToHom (hopen ⊤)).op
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.restrictFunctor U.ι).map
            ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)) ⊤ mU) = _
    change N.presheaf.map (eqToHom (hopen ⊤)).op
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
          (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) mU) = _
    dsimp only [mU]
    simp only [Scheme.Modules.restrictOpenSectionsLinearEquiv,
      Scheme.Modules.openSectionsLinearEquivOfEq,
      LinearEquiv.coe_mk]
    have hnat := CategoryTheory.congr_fun
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).mapPresheaf.naturality
        (eqToHom U.ι_image_top).op) m
    rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hnat
    change N.presheaf.map _
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
          (U.ι ''ᵁ (⊤ : U.toScheme.Opens))
          (M.presheaf.map (eqToHom U.ι_image_top).op m)) =
      N.presheaf.map _
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) U m)
    change Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M)
          (U.ι ''ᵁ (⊤ : U.toScheme.Opens))
          (M.presheaf.map (eqToHom U.ι_image_top).op m) =
      N.presheaf.map _
        (Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) U m) at hnat
    rw [hnat]
    rw [← N.presheaf.map_comp_apply]
    rfl
  have heval := congrArg
    (fun k : MU ⟶ (Scheme.Modules.pushforward b).obj NVU ↦
      Scheme.Modules.Hom.app k ⊤ mU) hmap
  dsimp only [Scheme.Modules.restrictPushPullIsoOfOpenSquare',
    Iso.trans_hom, Functor.mapIso_hom] at heval
  simp only [Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply,
    Scheme.Modules.pushforward_map_app] at heval
  let α := Scheme.Modules.restrictPullbackIsoOfOpenSquare g b V.ι U.ι hsq
  have hresPost := congrArg
    (fun x ↦ Scheme.Modules.Hom.app (α.app M).hom (b ⁻¹ᵁ ⊤) x) hres
  have hcore := hresPost.symm.trans heval
  dsimp only [α, b, V, N, MU, mU] at hcore
  simpa [Scheme.Modules.restrictPullbackOpenSectionsLinearEquiv,
    Scheme.Modules.restrictOpenSectionsLinearEquiv,
    Scheme.Modules.restrictPushPullIsoOfOpenSquare',
    Scheme.Modules.restrictPushforwardIsoOfOpenSquare,
    Scheme.Modules.pullbackGlobalSections] using hcore

/-- A cartesian square of affine schemes over affine spectra gives the expected
pushout square on the chosen base rings and global functions. -/
lemma Scheme.Modules.isPushout_baseRingHom_of_isPullback
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (g : Y ⟶ X)
    (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : IsPullback g pY pX (Spec.map φ)) :
    IsPushout (Scheme.Modules.baseRingHom pX) φ g.appTop
      (Scheme.Modules.baseRingHom pY) := by
  let hΓ := isPushout_appTop_of_isPullback h
  refine hΓ.of_iso (Scheme.ΓSpecIso R) (Iso.refl _) (Scheme.ΓSpecIso S)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [Scheme.Modules.baseRingHom]
  · exact Scheme.ΓSpecIso_naturality φ
  · simp
  · simp [Scheme.Modules.baseRingHom]

/-- The canonical scalar-extension map on global sections for a morphism over a
map of affine bases. -/
lemma Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_bijective_of_isPullback
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (g : Y ⟶ X)
    (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : IsPullback g pY pX (Spec.map φ))
    (M : X.Modules) [M.IsQuasicoherent] :
    let N := (Scheme.Modules.pullback g).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pX M
    letI : Module S Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pY N
    Function.Bijective
      (Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
        φ g pX pY h.w M) := by
  let N := (Scheme.Modules.pullback g).obj M
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Algebra R Γ(X, ⊤) :=
    (Scheme.Modules.baseRingHom pX).hom.toAlgebra
  letI : Algebra S Γ(Y, ⊤) :=
    (Scheme.Modules.baseRingHom pY).hom.toAlgebra
  letI : Algebra Γ(X, ⊤) Γ(Y, ⊤) := g.appTop.hom.toAlgebra
  letI : Algebra R Γ(Y, ⊤) :=
    (g.appTop.hom.comp (Scheme.Modules.baseRingHom pX).hom).toAlgebra
  letI : IsScalarTower R Γ(X, ⊤) Γ(Y, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hw : g.appTop.hom.comp (Scheme.Modules.baseRingHom pX).hom =
      (Scheme.Modules.baseRingHom pY).hom.comp φ.hom :=
    congrArg CommRingCat.Hom.hom
      (Scheme.Modules.isPushout_baseRingHom_of_isPullback φ g pX pY h).w
  letI : IsScalarTower R S Γ(Y, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ DFunLike.congr_fun hw x
  have hp : IsPushout
      (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R Γ(X, ⊤)))
      (CommRingCat.ofHom (algebraMap S Γ(Y, ⊤)))
      (CommRingCat.ofHom (algebraMap Γ(X, ⊤) Γ(Y, ⊤))) := by
    change IsPushout φ (Scheme.Modules.baseRingHom pX)
      (Scheme.Modules.baseRingHom pY) g.appTop
    exact
      (Scheme.Modules.isPushout_baseRingHom_of_isPullback φ g pX pY h).flip
  letI : Algebra.IsPushout R S Γ(X, ⊤) Γ(Y, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp hp
  letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pX M
  letI : IsScalarTower R Γ(X, ⊤) Γ(M, ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module S Γ(N, ⊤) := Scheme.Modules.globalSectionsModule pY N
  let T := Γ(Y, ⊤) ⊗[Γ(X, ⊤)] Γ(M, ⊤)
  letI : Module S T :=
    Module.compHom T (algebraMap S Γ(Y, ⊤))
  letI : IsScalarTower S Γ(Y, ⊤) T :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eCancel :=
    (Algebra.IsPushout.cancelBaseChange R S Γ(X, ⊤) Γ(Y, ⊤)
      Γ(M, ⊤)).symm
  let cAff := canonicalAffinePullbackSectionsBaseChangeLinearMap g M
  let eAff : T ≃ₗ[Γ(Y, ⊤)] Γ(N, ⊤) :=
    LinearEquiv.ofBijective cAff
      (canonicalAffinePullbackSectionsBaseChangeLinearMap_bijective g M)
  let eAff' : T ≃ₗ[S] Γ(N, ⊤) :=
    { toEquiv := eAff.toEquiv
      map_add' := eAff.map_add
      map_smul' := fun s x ↦ by
        change eAff ((algebraMap S Γ(Y, ⊤) s) • x) =
          (algebraMap S Γ(Y, ⊤) s) • eAff x
        exact eAff.map_smul (algebraMap S Γ(Y, ⊤) s) x }
  let eTotal := eCancel.trans eAff'
  let c := Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
    φ g pX pY h.w M
  have hc : c = eTotal.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
        rw [Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_tmul]
        change _ = eTotal (s ⊗ₜ[R] m)
        rw [show eTotal (s ⊗ₜ[R] m) =
            eAff' (eCancel (s ⊗ₜ[R] m)) by rfl]
        rw [show eCancel (s ⊗ₜ[R] m) =
            (algebraMap S Γ(Y, ⊤) s) ⊗ₜ[Γ(X, ⊤)] m by
          exact Algebra.IsPushout.cancelBaseChange_symm_tmul _ _ _ _ _ _ _]
        rw [show eAff'
            ((algebraMap S Γ(Y, ⊤) s) ⊗ₜ[Γ(X, ⊤)] m) =
            algebraMap S Γ(Y, ⊤) s •
              Scheme.Modules.pullbackGlobalSections g M m by
          exact canonicalAffinePullbackSectionsBaseChangeLinearMap_tmul
            g M _ _]
        rfl
  change Function.Bijective c
  rw [hc]
  exact eTotal.bijective

/-- If the square over an open and its inverse image is cartesian and both opens
are affine, the canonical base-change map on sections over that open is
bijective. -/
lemma Scheme.Modules.pullbackOpenSectionsBaseChangeLinearMap_bijective_of_isPullback
    {R S : CommRingCat.{u}} (φ : R ⟶ S) {X Y : Scheme.{u}}
    (g : Y ⟶ X) (pX : X ⟶ Spec R) (pY : Y ⟶ Spec S)
    (h : g ≫ pX = pY ≫ Spec.map φ) (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen (g ⁻¹ᵁ U))
    (hsq : IsPullback (Scheme.Modules.restrictToPreimage g U)
      ((g ⁻¹ᵁ U).ι ≫ pY) (U.ι ≫ pX) (Spec.map φ)) :
    let V := g ⁻¹ᵁ U
    let N := (Scheme.Modules.pullback g).obj M
    letI : Algebra R S := φ.hom.toAlgebra
    letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule pX M U
    letI : Module S Γ(N, V) := Scheme.Modules.openSectionsModule pY N V
    Function.Bijective
      (pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M U) := by
  let V := g ⁻¹ᵁ U
  let b := Scheme.Modules.restrictToPreimage g U
  let N := (Scheme.Modules.pullback g).obj M
  let MU := (Scheme.Modules.restrictFunctor U.ι).obj M
  let NVU := (Scheme.Modules.pullback b).obj MU
  letI : IsAffine U.toScheme := hU
  letI : IsAffine V.toScheme := hV
  letI : Algebra R S := φ.hom.toAlgebra
  letI : Module R Γ(M, U) := Scheme.Modules.openSectionsModule pX M U
  letI : Module R Γ(MU, ⊤) :=
    Scheme.Modules.globalSectionsModule (U.ι ≫ pX) MU
  letI : Module S Γ(N, V) := Scheme.Modules.openSectionsModule pY N V
  letI : Module S Γ(NVU, ⊤) :=
    Scheme.Modules.globalSectionsModule (V.ι ≫ pY) NVU
  let eU := Scheme.Modules.restrictOpenSectionsLinearEquiv pX M U
  let eSource := TensorProduct.AlgebraTensorModule.congr
    (LinearEquiv.refl S S) eU
  let eTarget :=
    Scheme.Modules.restrictPullbackOpenSectionsLinearEquiv g pY M U
  let cOpen := pullbackOpenSectionsBaseChangeLinearMap φ g pX pY h M U
  let cLocal := Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
    φ b (U.ι ≫ pX) (V.ι ≫ pY) hsq.w MU
  have hc : eTarget.toLinearMap.comp cOpen =
      cLocal.comp eSource.toLinearMap := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s m =>
        change eTarget (cOpen (s ⊗ₜ[R] m)) =
          cLocal (eSource (s ⊗ₜ[R] m))
        rw [show cOpen (s ⊗ₜ[R] m) =
            s • (show Γ(N, V) from
              ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U m) by
          exact pullbackOpenSectionsBaseChangeLinearMap_tmul
            φ g pX pY h M U s m]
        rw [eTarget.map_smul]
        rw [show eSource (s ⊗ₜ[R] m) = s ⊗ₜ[R] eU m by
          exact TensorProduct.AlgebraTensorModule.congr_tmul _ _ _ _]
        rw [show cLocal (s ⊗ₜ[R] eU m) =
            s • Scheme.Modules.pullbackGlobalSections b MU (eU m) by
          exact Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_tmul
            φ b (U.ι ≫ pX) (V.ι ≫ pY) hsq.w MU s (eU m)]
        exact congrArg (s • ·)
          (Scheme.Modules.restrictPullbackOpenSectionsLinearEquiv_unit
            g pX pY M U m)
  have hLocal : Function.Bijective cLocal :=
    Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_bijective_of_isPullback
      φ b (U.ι ≫ pX) (V.ι ≫ pY) hsq MU
  have hcomp : Function.Bijective (eTarget.toLinearMap.comp cOpen) := by
    rw [hc]
    exact hLocal.comp eSource.bijective
  change Function.Bijective cOpen
  exact (eTarget.bijective.of_comp_iff' cOpen).mp hcomp

end AlgebraicGeometry
