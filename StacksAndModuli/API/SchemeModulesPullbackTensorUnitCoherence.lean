module

public import StacksAndModuli.API.SchemeModulesPullbackTensor

/-!
# Unit coherence for the pullback tensor comparison

This file exposes the coherence equality underlying the proof that pullback commutes
with tensoring by the structure sheaf.  In particular, it identifies the canonical
oplax tensor comparison followed by the pulled-back unit comparison with the image of
the right unitor.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

set_option maxHeartbeats 800000 in
-- The equality is proved through the pullback--pushforward adjunction componentwise.
/-- The pullback tensor comparison is compatible with the right unitor and the
canonical comparison between the pulled-back structure sheaf and the structure
sheaf. -/
theorem pullbackTensorComparison_comp_unit
    (f : X ⟶ Y) (F : Y.Modules) :
    pullbackTensorComparison f F
          (SheafOfModules.unit Y.ringCatSheaf) ≫
        tensorMapRight ((pullback f).obj F)
          (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        (tensorUnitIso ((pullback f).obj F)).hom =
      (pullback f).map (tensorUnitIso F).hom := by
  let a := pullbackTensorComparison f F
    (SheafOfModules.unit Y.ringCatSheaf)
  let u := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  let eu := asIso u
  let t := (tensorRightIso ((pullback f).obj F) eu).hom ≫
    (tensorUnitIso ((pullback f).obj F)).hom
  change a ≫ t = (pullback f).map (tensorUnitIso F).hom
  apply (pullbackPushforwardAdjunction f).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_right]
  have hrhs := (pullbackPushforwardAdjunction f).homEquiv_naturality_left
    (tensorUnitIso F).hom (𝟙 ((pullback f).obj F))
  rw [Category.comp_id, Adjunction.homEquiv_id] at hrhs
  rw [hrhs]
  dsimp only [a, pullbackTensorComparison]
  simp only [Equiv.apply_symm_apply]
  let adjY := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  apply (adjY.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right]
  let h := MonoidalCategoryStruct.whiskerRight
    (C := Y.PresheafOfModules)
    ((pullbackPushforwardAdjunction f).unit.app F).val
    (SheafOfModules.unit Y.ringCatSheaf).val
  have hleft' :
      adjY.homEquiv _ _
        ((_root_.PresheafOfModules.sheafification
          (𝟙 Y.ringCatSheaf.obj)).map h) =
        h ≫ adjY.unit.app
          (((pullback f ⋙ pushforward f).obj F).val ⊗
            (SheafOfModules.unit Y.ringCatSheaf).val) := by
    rw [Adjunction.homEquiv_apply]
    simpa only [Functor.id_obj, Functor.id_map,
      Functor.comp_map] using (adjY.unit.naturality h).symm
  change (adjY.homEquiv _ _
    ((_root_.PresheafOfModules.sheafification
      (𝟙 Y.ringCatSheaf.obj)).map h) ≫ _) ≫ _ = _
  rw [hleft']
  slice_lhs 2 3 => rw [← Adjunction.homEquiv_apply]
  let h₂ := MonoidalCategoryStruct.whiskerLeft
    (C := Y.PresheafOfModules)
    ((pullback f ⋙ pushforward f).obj F).val
    ((pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit Y.ringCatSheaf)).val
  have hh₂ := adjY.homEquiv_naturality_left h₂
    (pushforwardTensorHom f ((pullback f).obj F)
      ((pullback f).obj (SheafOfModules.unit Y.ringCatSheaf)))
  have hh₂' :
      adjY.homEquiv
        (((pullback f ⋙ pushforward f).obj F).val ⊗
          (SheafOfModules.unit Y.ringCatSheaf).val) _
        ((_root_.PresheafOfModules.sheafification
          (𝟙 Y.ringCatSheaf.obj)).map h₂ ≫
            pushforwardTensorHom f ((pullback f).obj F)
              ((pullback f).obj (SheafOfModules.unit Y.ringCatSheaf))) =
        h₂ ≫ adjY.homEquiv _ _
          (pushforwardTensorHom f ((pullback f).obj F)
            ((pullback f).obj (SheafOfModules.unit Y.ringCatSheaf))) := by
    simpa only [Functor.id_obj] using hh₂
  change h ≫ (adjY.homEquiv _ _
    ((_root_.PresheafOfModules.sheafification
      (𝟙 Y.ringCatSheaf.obj)).map h₂ ≫
        pushforwardTensorHom f ((pullback f).obj F)
          ((pullback f).obj (SheafOfModules.unit Y.ringCatSheaf)))) ≫ _ = _
  rw [hh₂']
  dsimp only [pushforwardTensorHom]
  change h ≫ (h₂ ≫ adjY.homEquiv
    (((pushforward f).obj ((pullback f).obj F)).val ⊗
      ((pushforward f).obj ((pullback f).obj
        (SheafOfModules.unit Y.ringCatSheaf))).val) _
    ((adjY.homEquiv _ _).symm _)) ≫ _ = _
  rw [Equiv.apply_symm_apply]
  let ρ := (ρ_ F.val).hom
  let η := (pullbackPushforwardAdjunction f).unit.app F
  have hq := adjY.homEquiv_naturality_right
    (adjY.counit.app F) η
  have hcounit :
      adjY.homEquiv
          ((SheafOfModules.forget Y.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars
              (𝟙 Y.ringCatSheaf.obj)).obj F)
          F (adjY.counit.app F) = 𝟙 _ := by
    rw [← Adjunction.homEquiv_symm_id, Equiv.apply_symm_apply]
  simp only [Functor.id_obj] at hq
  rw [hcounit, Category.id_comp] at hq
  change adjY.homEquiv F.val ((pullback f ⋙ pushforward f).obj F)
    (adjY.counit.app F ≫ η) = _ at hq
  have hright := adjY.homEquiv_naturality_left ρ
    (adjY.counit.app F ≫ η)
  rw [hq] at hright
  change _ = adjY.homEquiv _ _
    ((_root_.PresheafOfModules.sheafification
      (𝟙 Y.ringCatSheaf.obj)).map ρ ≫
        adjY.counit.app F ≫ η)
  rw [hright]
  let adjX := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let k := MonoidalCategoryStruct.whiskerLeft
    (C := X.PresheafOfModules) ((pullback f).obj F).val eu.hom.val ≫
      (ρ_ ((pullback f).obj F).val).hom
  have htval :
      adjX.unit.app
          (((pullback f).obj F).val ⊗
            ((pullback f).obj
              (SheafOfModules.unit Y.ringCatSheaf)).val) ≫
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars
            (𝟙 X.ringCatSheaf.obj)).map t) = k := by
    change adjX.homEquiv _ _ t = k
    dsimp only [t, tensorRightIso, tensorMapRight, tensorUnitIso]
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    rw [← (sheafification X).map_comp_assoc]
    change adjX.homEquiv _ _
      ((sheafification X).map k ≫ adjX.counit.app _) = k
    calc
      _ = adjX.homEquiv _ _ ((adjX.homEquiv _ _).symm k) := by
        exact congrArg (adjX.homEquiv _ _)
          (adjX.homEquiv_counit _ _ k).symm
      _ = k := Equiv.apply_symm_apply _ _
  let pf := _root_.PresheafOfModules.pushforward
    f.toRingCatSheafHom.hom
  have htval' :
      pf.map (adjX.unit.app
          (((pullback f).obj F).val ⊗
            ((pullback f).obj
              (SheafOfModules.unit Y.ringCatSheaf)).val)) ≫
        ((SheafOfModules.forget Y.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars
            (𝟙 Y.ringCatSheaf.obj)).map ((pushforward f).map t)) =
        pf.map k := by
    change pf.map _ ≫ pf.map
      ((SheafOfModules.forget X.ringCatSheaf ⋙
        _root_.PresheafOfModules.restrictScalars
          (𝟙 X.ringCatSheaf.obj)).map t) = pf.map k
    rw [← pf.map_comp, htval]
  dsimp only [pf, adjX] at htval'
  simp only [Category.assoc, htval']
  have hu :
      (pullbackPushforwardAdjunction f).unit.app
          (SheafOfModules.unit Y.ringCatSheaf) ≫
        (pushforward f).map eu.hom =
      SheafOfModules.unitToPushforwardObjUnit
        f.toRingCatSheafHom := by
    calc
      _ = (pullbackPushforwardAdjunction f).homEquiv _ _ eu.hom :=
        ((pullbackPushforwardAdjunction f).homEquiv_apply _ _ eu.hom).symm
      _ = _ := by
        change (pullbackPushforwardAdjunction f).homEquiv _ _
          (SheafOfModules.pullbackObjUnitToUnit
            f.toRingCatSheafHom) = _
        exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m r
  have huU := congrArg (fun q ↦ q.val.app U) hu
  have hur := ConcreteCategory.congr_hom huU r
  simp [k, h, h₂, ρ, η, pushforwardPresheafTensorHom]
  let m' : ((pullback f).obj F).val.obj (.op (f ⁻¹ᵁ U.unop)) :=
    ((pullbackPushforwardAdjunction f).unit.app F).val.app U m
  change
    eu.hom.val.app (.op (f ⁻¹ᵁ U.unop))
          (((pullbackPushforwardAdjunction f).unit.app
            (SheafOfModules.unit Y.ringCatSheaf)).val.app U r) • m' =
      ((pullbackPushforwardAdjunction f).unit.app F).val.app U (r • m)
  change
    eu.hom.val.app (.op (f ⁻¹ᵁ U.unop))
        (((pullbackPushforwardAdjunction f).unit.app
          (SheafOfModules.unit Y.ringCatSheaf)).val.app U r) =
      f.app U.unop r at hur
  rw [hur]
  dsimp only [m']
  exact (((pullbackPushforwardAdjunction f).unit.app F).val.app U).hom.map_smul r m |>.symm

/-- In inverse form, compatibility with the right unitor moves the pullback tensor
comparison to the right of the pulled-back inverse unitor. -/
theorem tensorUnitIso_inv_comp_pullbackUnit_inv
    (f : X ⟶ Y) (F : Y.Modules)
    [IsIso (SheafOfModules.pullbackObjUnitToUnit
      f.toRingCatSheafHom)] :
    (tensorUnitIso ((pullback f).obj F)).inv ≫
        tensorMapRight ((pullback f).obj F)
          (inv (SheafOfModules.pullbackObjUnitToUnit
            f.toRingCatSheafHom)) =
      (pullback f).map (tensorUnitIso F).inv ≫
        pullbackTensorComparison f F
          (SheafOfModules.unit Y.ringCatSheaf) := by
  let a := pullbackTensorComparison f F
    (SheafOfModules.unit Y.ringCatSheaf)
  let u := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  let t := tensorMapRight ((pullback f).obj F) u ≫
    (tensorUnitIso ((pullback f).obj F)).hom
  letI : IsIso (tensorMapRight ((pullback f).obj F) u) := by
    change IsIso (tensorRightIso ((pullback f).obj F) (asIso u)).hom
    infer_instance
  letI : IsIso t := by
    dsimp only [t]
    infer_instance
  have ht : a ≫ t = (pullback f).map (tensorUnitIso F).hom := by
    exact pullbackTensorComparison_comp_unit f F
  rw [← cancel_mono t]
  calc
    ((tensorUnitIso ((pullback f).obj F)).inv ≫
          tensorMapRight ((pullback f).obj F) (inv u)) ≫ t =
        𝟙 ((pullback f).obj F) := by
      dsimp only [t]
      change (tensorUnitIso ((pullback f).obj F)).inv ≫
        (tensorRightIso ((pullback f).obj F) (asIso u)).inv ≫
        (tensorRightIso ((pullback f).obj F) (asIso u)).hom ≫
        (tensorUnitIso ((pullback f).obj F)).hom = _
      simp
    _ = (pullback f).map (tensorUnitIso F).inv ≫
          (pullback f).map (tensorUnitIso F).hom := by simp
    _ = ((pullback f).map (tensorUnitIso F).inv ≫ a) ≫ t := by
      rw [Category.assoc, ht]

end AlgebraicGeometry.Scheme.Modules

end

end
