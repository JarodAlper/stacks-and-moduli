module

public import StacksAndModuli.API.SchemeModulesTensorQuasicoherent
public import StacksAndModuli.API.PullbackAdjoint
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction

/-!
# Pullback and tensor products of scheme modules

This file constructs the canonical comparison from the pullback of a tensor product of
module sheaves to the tensor product of their pullbacks.  It also proves the comparison
up to a canonical isomorphism for open immersions, where pullback agrees with restriction
and restriction is already known to commute with tensor products. The comparison and its
open-immersion form are natural in both tensor factors.

The open-immersion form is particularly useful for generic fibres over a discrete
valuation ring, since the generic-point inclusion and its projective-space base change
are open immersions.

Main declarations:

- `AlgebraicGeometry.Scheme.Modules.pushforwardTensorHom`;
- `AlgebraicGeometry.Scheme.Modules.pullbackTensorComparison` and its left- and right-factor
  naturality theorems;
- `AlgebraicGeometry.Scheme.Modules.pullbackTensorComparison_isIso_of_iso_unit`;
- `AlgebraicGeometry.Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion` and its naturality
  theorems.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- The objectwise tensor map from the tensor product of two pushed-forward module
presheaves to the pushforward of their tensor product. -/
noncomputable def pushforwardPresheafTensorHom (f : X ⟶ Y) (F G : X.Modules) :
    MonoidalCategoryStruct.tensorObj (C := Y.PresheafOfModules)
        ((pushforward f).obj F).val ((pushforward f).obj G).val ⟶
      (_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj
        (MonoidalCategoryStruct.tensorObj (C := X.PresheafOfModules) F.val G.val) := by
  refine
    { app := fun U ↦ ?_
      naturality := ?_ }
  · exact ModuleCat.MonoidalCategory.tensorLift
      (fun m n ↦ m ⊗ₜ n)
      (by intro m m' n; rw [TensorProduct.add_tmul])
      (by intro _ _ _; rfl)
      (by intro m n n'; rw [TensorProduct.tmul_add])
      (by
        intro a m n
        change
          (show F.val.obj (.op (f ⁻¹ᵁ U.unop)) from m) ⊗ₜ[Γ(X, f ⁻¹ᵁ U.unop)]
              (f.app U.unop a •
                (show G.val.obj (.op (f ⁻¹ᵁ U.unop)) from n)) =
            f.app U.unop a •
              ((show F.val.obj (.op (f ⁻¹ᵁ U.unop)) from m) ⊗ₜ[Γ(X, f ⁻¹ᵁ U.unop)]
                (show G.val.obj (.op (f ⁻¹ᵁ U.unop)) from n))
        exact TensorProduct.tmul_smul _ _ _)
  · intro U V k
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl

/-- Pushforward has a natural tensor map.  It is obtained by sheafifying the
objectwise restriction-of-scalars tensor map. -/
noncomputable def pushforwardTensorHom (f : X ⟶ Y) (F G : X.Modules) :
    tensor ((pushforward f).obj F) ((pushforward f).obj G) ⟶
      (pushforward f).obj (tensor F G) := by
  let adjX := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let adjY := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  let u := adjX.unit.app
    (MonoidalCategoryStruct.tensorObj (C := X.PresheafOfModules) F.val G.val)
  exact (adjY.homEquiv _ _).symm
    (pushforwardPresheafTensorHom f F G ≫
      (_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map u)

/-- The canonical oplax tensor comparison for pullback of module sheaves. -/
noncomputable def pullbackTensorComparison (f : X ⟶ Y) (F G : Y.Modules) :
    (pullback f).obj (tensor F G) ⟶
      tensor ((pullback f).obj F) ((pullback f).obj G) :=
  ((pullbackPushforwardAdjunction f).homEquiv _ _).symm <|
    tensorMapLeft ((pullbackPushforwardAdjunction f).unit.app F) G ≫
      tensorMapRight ((pushforward f).obj ((pullback f).obj F))
        ((pullbackPushforwardAdjunction f).unit.app G) ≫
      pushforwardTensorHom f ((pullback f).obj F) ((pullback f).obj G)

/-- Pullback commutes with tensoring on the right by the structure sheaf. -/
noncomputable def pullbackTensorUnitIso (f : X ⟶ Y) (F : Y.Modules) :
    (pullback f).obj (tensor F (SheafOfModules.unit Y.ringCatSheaf)) ≅
      tensor ((pullback f).obj F)
        ((pullback f).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
  (pullback f).mapIso (tensorUnitIso F) ≪≫
    (tensorUnitIso ((pullback f).obj F)).symm ≪≫
    tensorRightIso ((pullback f).obj F)
      (asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)).symm

set_option maxHeartbeats 800000 in
-- The unit comparison is proved through the pullback--pushforward adjunction componentwise.
/-- The canonical pullback--tensor comparison is an isomorphism when the right factor
is the structure sheaf. -/
theorem pullbackTensorComparison_isIso_unit (f : X ⟶ Y) (F : Y.Modules) :
    IsIso (pullbackTensorComparison f F
      (SheafOfModules.unit Y.ringCatSheaf)) := by
  let a := pullbackTensorComparison f F
    (SheafOfModules.unit Y.ringCatSheaf)
  let u := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  let eu := asIso u
  let t := (tensorRightIso ((pullback f).obj F) eu).hom ≫
    (tensorUnitIso ((pullback f).obj F)).hom
  let _ : IsIso t := by
    dsimp [t]
    infer_instance
  suffices a ≫ t = (pullback f).map (tensorUnitIso F).hom by
    let _ : IsIso (a ≫ t) := this ▸ inferInstance
    exact IsIso.of_isIso_comp_right a t
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

/-- The presheaf-level tensor map for pushforward is natural in both module factors. -/
theorem pushforwardPresheafTensorHom_naturality
    (f : X ⟶ Y) {F F' G G' : X.Modules} (φ : F ⟶ F') (ψ : G ⟶ G') :
    MonoidalCategoryStruct.tensorHom (C := Y.PresheafOfModules)
        ((pushforward f).map φ).val ((pushforward f).map ψ).val ≫
        pushforwardPresheafTensorHom f F' G' =
      pushforwardPresheafTensorHom f F G ≫
        (_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
          (MonoidalCategoryStruct.tensorHom (C := X.PresheafOfModules)
            φ.val ψ.val) := by
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

/-- Under the sheafification adjunction, the pushforward tensor map is represented by
the presheaf tensor map followed by the sheafification unit. -/
theorem pushforwardTensorHom_homEquiv (f : X ⟶ Y) (F G : X.Modules) :
    ((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 Y.ringCatSheaf.obj)).homEquiv
        (((pushforward f).obj F).val ⊗ ((pushforward f).obj G).val)
        ((pushforward f).obj (tensor F G)))
      (pushforwardTensorHom f F G) =
    pushforwardPresheafTensorHom f F G ≫
      (_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
        ((_root_.PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app (F.val ⊗ G.val)) := by
  dsimp only [pushforwardTensorHom]
  exact Equiv.apply_symm_apply _ _

/-- Changing the left and right factors of a tensor product commutes. -/
theorem tensorMap_exchange {F F' G G' : X.Modules}
    (φ : F ⟶ F') (ψ : G ⟶ G') :
    tensorMapRight F ψ ≫ tensorMapLeft φ G' =
      tensorMapLeft φ G ≫ tensorMapRight F' ψ := by
  dsimp only [tensorMapLeft, tensorMapRight]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (sheafification X).map (whisker_exchange φ.val ψ.val)

set_option maxHeartbeats 800000 in
-- This naturality proof crosses the presheaf tensor and sheafification adjunction layers.
/-- The tensor map for pushforward is natural in both module factors. -/
theorem pushforwardTensorHom_naturality
    (f : X ⟶ Y) {F F' G G' : X.Modules} (φ : F ⟶ F') (ψ : G ⟶ G') :
    (tensorMapLeft ((pushforward f).map φ) ((pushforward f).obj G) ≫
        tensorMapRight ((pushforward f).obj F') ((pushforward f).map ψ)) ≫
        pushforwardTensorHom f F' G' =
      pushforwardTensorHom f F G ≫
        (pushforward f).map
          (tensorMapLeft φ G ≫ tensorMapRight F' ψ) := by
  let adjY := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  apply (adjY.homEquiv _ _).injective
  dsimp only [tensorMapLeft, tensorMapRight]
  rw [← Functor.map_comp]
  let hY :=
    ((SheafOfModules.forget Y.ringCatSheaf).map ((pushforward f).map φ) ▷
      ((pushforward f).obj G).val) ≫
    (((pushforward f).obj F').val ◁
      (SheafOfModules.forget Y.ringCatSheaf).map ((pushforward f).map ψ))
  have hleft := adjY.homEquiv_naturality_left hY
    (pushforwardTensorHom f F' G')
  change adjY.homEquiv _ _
    ((_root_.PresheafOfModules.sheafification
      (𝟙 Y.ringCatSheaf.obj)).map hY ≫
      pushforwardTensorHom f F' G') = _
  rw [hleft]
  rw [Adjunction.homEquiv_naturality_right]
  have hp' : adjY.homEquiv
      (((pushforward f).obj F').val ⊗ ((pushforward f).obj G').val)
      ((pushforward f).obj (tensor F' G'))
      (pushforwardTensorHom f F' G') =
      pushforwardPresheafTensorHom f F' G' ≫
        (_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
          ((_root_.PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app (F'.val ⊗ G'.val)) := by
    exact pushforwardTensorHom_homEquiv f F' G'
  change hY ≫ adjY.homEquiv
      (((pushforward f).obj F').val ⊗ ((pushforward f).obj G').val)
      ((pushforward f).obj (tensor F' G'))
      (pushforwardTensorHom f F' G') = _
  rw [hp']
  have hp : adjY.homEquiv
      (((pushforward f).obj F).val ⊗ ((pushforward f).obj G).val)
      ((pushforward f).obj (tensor F G))
      (pushforwardTensorHom f F G) =
      pushforwardPresheafTensorHom f F G ≫
        (_root_.PresheafOfModules.pushforward f.toRingCatSheafHom.hom).map
          ((_root_.PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app (F.val ⊗ G.val)) := by
    exact pushforwardTensorHom_homEquiv f F G
  change _ = adjY.homEquiv
      (((pushforward f).obj F).val ⊗ ((pushforward f).obj G).val)
      ((pushforward f).obj (tensor F G))
      (pushforwardTensorHom f F G) ≫ _
  rw [hp]
  have hy : hY =
      MonoidalCategoryStruct.tensorHom (C := Y.PresheafOfModules)
        ((pushforward f).map φ).val ((pushforward f).map ψ).val := by
    exact (tensorHom_def _ _).symm
  rw [hy]
  rw [← Category.assoc]
  rw [pushforwardPresheafTensorHom_naturality]
  let adjX := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let pf := _root_.PresheafOfModules.pushforward
    f.toRingCatSheafHom.hom
  let hX := MonoidalCategoryStruct.tensorHom (C := X.PresheafOfModules)
    φ.val ψ.val
  have hx : hX =
      (((SheafOfModules.forget X.ringCatSheaf).map φ) ▷ G.val) ≫
        (F'.val ◁ ((SheafOfModules.forget X.ringCatSheaf).map ψ)) := by
    exact tensorHom_def _ _
  have hu := adjX.unit.naturality hX
  have hu' : hX ≫ adjX.unit.app (F'.val ⊗ G'.val) =
      adjX.unit.app (F.val ⊗ G.val) ≫
        (SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars
            (𝟙 X.ringCatSheaf.obj)).map
          ((sheafification X).map hX) := by
    simpa only [Functor.id_obj, Functor.id_map, Functor.comp_map,
      sheafification] using hu
  change (pushforwardPresheafTensorHom f F G ≫ pf.map hX) ≫
      pf.map (adjX.unit.app (F'.val ⊗ G'.val)) = _
  have hs :
      (sheafification X).map
          (((SheafOfModules.forget X.ringCatSheaf).map φ) ▷ G.val) ≫
        (sheafification X).map
          (F'.val ◁ ((SheafOfModules.forget X.ringCatSheaf).map ψ)) =
      (sheafification X).map hX := by
    rw [← Functor.map_comp, ← hx]
  rw [hs]
  have hpf :
      (SheafOfModules.forget Y.ringCatSheaf ⋙
        _root_.PresheafOfModules.restrictScalars
          (𝟙 Y.ringCatSheaf.obj)).map
          ((pushforward f).map ((sheafification X).map hX)) =
      pf.map ((SheafOfModules.forget X.ringCatSheaf ⋙
        _root_.PresheafOfModules.restrictScalars
          (𝟙 X.ringCatSheaf.obj)).map
          ((sheafification X).map hX)) := by
    rfl
  rw [hpf]
  calc
    _ = pushforwardPresheafTensorHom f F G ≫
        pf.map (hX ≫ adjX.unit.app (F'.val ⊗ G'.val)) := by
      rw [pf.map_comp]
      simp only [Category.assoc]
    _ = pushforwardPresheafTensorHom f F G ≫
        pf.map (adjX.unit.app (F.val ⊗ G.val) ≫
          (SheafOfModules.forget X.ringCatSheaf ⋙
            _root_.PresheafOfModules.restrictScalars
              (𝟙 X.ringCatSheaf.obj)).map
            ((sheafification X).map hX)) := by
      rw [hu']
    _ = _ := by
      rw [pf.map_comp]
      simp only [Category.assoc]
      rfl

/-- Right-factor naturality of the tensor map for pushforward. -/
theorem pushforwardTensorHom_naturality_right
    (f : X ⟶ Y) (F : X.Modules) {G G' : X.Modules} (ψ : G ⟶ G') :
    tensorMapRight ((pushforward f).obj F) ((pushforward f).map ψ) ≫
        pushforwardTensorHom f F G' =
      pushforwardTensorHom f F G ≫
        (pushforward f).map (tensorMapRight F ψ) := by
  have h := pushforwardTensorHom_naturality f (𝟙 F) ψ
  have hid : (pushforward f).map (𝟙 F) = 𝟙 ((pushforward f).obj F) :=
    (pushforward f).map_id F
  have hr : tensorMapLeft (𝟙 F) G ≫ tensorMapRight F ψ =
      tensorMapRight F ψ := by
    rw [tensorMapLeft_id, Category.id_comp]
  rw [hid, tensorMapLeft_id, Category.id_comp, hr] at h
  exact h

set_option maxHeartbeats 800000 in
-- The mate calculation expands both tensor factors through the pullback adjunction.
/-- The canonical pullback--tensor comparison is natural in its right module factor. -/
theorem pullbackTensorComparison_naturality_right
    (f : X ⟶ Y) (F : Y.Modules) {G G' : Y.Modules} (ψ : G ⟶ G') :
    (pullback f).map (tensorMapRight F ψ) ≫
        pullbackTensorComparison f F G' =
      pullbackTensorComparison f F G ≫
        tensorMapRight ((pullback f).obj F) ((pullback f).map ψ) := by
  let adj := pullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp only [pullbackTensorComparison]
  let q' :=
    tensorMapLeft (adj.unit.app F) G' ≫
      tensorMapRight ((pushforward f).obj ((pullback f).obj F))
        (adj.unit.app G') ≫
      pushforwardTensorHom f ((pullback f).obj F) ((pullback f).obj G')
  let q :=
    tensorMapLeft (adj.unit.app F) G ≫
      tensorMapRight ((pushforward f).obj ((pullback f).obj F))
        (adj.unit.app G) ≫
      pushforwardTensorHom f ((pullback f).obj F) ((pullback f).obj G)
  change tensorMapRight F ψ ≫
      adj.homEquiv _ _ ((adj.homEquiv _ _).symm q') =
    adj.homEquiv _ _ ((adj.homEquiv _ _).symm q) ≫ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  dsimp only [q, q']
  slice_lhs 1 2 => rw [tensorMap_exchange]
  have hc :
      tensorMapRight ((pullback f ⋙ pushforward f).obj F) ψ ≫
        tensorMapRight ((pushforward f).obj ((pullback f).obj F))
          (adj.unit.app G') =
      tensorMapRight ((pullback f ⋙ pushforward f).obj F)
        (ψ ≫ adj.unit.app G') := by
    change
      tensorMapRight ((pullback f ⋙ pushforward f).obj F) ψ ≫
        tensorMapRight ((pullback f ⋙ pushforward f).obj F)
          (adj.unit.app G') = _
    rw [tensorMapRight_comp]
  slice_lhs 2 3 => rw [hc]
  have hu := adj.unit.naturality ψ
  have hu' : ψ ≫ adj.unit.app G' =
      adj.unit.app G ≫ (pushforward f).map ((pullback f).map ψ) := by
    simpa only [Functor.id_obj, Functor.id_map, Functor.comp_map] using hu
  rw [hu']
  rw [tensorMapRight_comp]
  have hn :
      tensorMapRight ((pullback f ⋙ pushforward f).obj F)
          ((pushforward f).map ((pullback f).map ψ)) ≫
        pushforwardTensorHom f ((pullback f).obj F) ((pullback f).obj G') =
      pushforwardTensorHom f ((pullback f).obj F) ((pullback f).obj G) ≫
        (pushforward f).map
          (tensorMapRight ((pullback f).obj F) ((pullback f).map ψ)) := by
    change
      tensorMapRight ((pushforward f).obj ((pullback f).obj F))
          ((pushforward f).map ((pullback f).map ψ)) ≫
        pushforwardTensorHom f ((pullback f).obj F) ((pullback f).obj G') = _
    exact pushforwardTensorHom_naturality_right f
      ((pullback f).obj F) ((pullback f).map ψ)
  slice_lhs 3 4 => rw [hn]
  simp only [Category.assoc]
  rfl

/-- Left-factor naturality of the tensor map for pushforward. -/
theorem pushforwardTensorHom_naturality_left
    (f : X ⟶ Y) {F F' : X.Modules} (φ : F ⟶ F') (G : X.Modules) :
    tensorMapLeft ((pushforward f).map φ) ((pushforward f).obj G) ≫
        pushforwardTensorHom f F' G =
      pushforwardTensorHom f F G ≫
        (pushforward f).map (tensorMapLeft φ G) := by
  have h := pushforwardTensorHom_naturality f φ (𝟙 G)
  have hid : (pushforward f).map (𝟙 G) = 𝟙 ((pushforward f).obj G) :=
    (pushforward f).map_id G
  have hr : tensorMapLeft φ G ≫ tensorMapRight F' (𝟙 G) =
      tensorMapLeft φ G := by
    rw [tensorMapRight_id, Category.comp_id]
  rw [hid, tensorMapRight_id, Category.comp_id, hr] at h
  exact h

set_option maxHeartbeats 800000 in
-- The mate calculation expands both tensor factors through the pullback adjunction.
/-- The canonical pullback--tensor comparison is natural in its left module factor. -/
theorem pullbackTensorComparison_naturality_left
    (f : X ⟶ Y) {F F' : Y.Modules} (φ : F ⟶ F') (G : Y.Modules) :
    (pullback f).map (tensorMapLeft φ G) ≫
        pullbackTensorComparison f F' G =
      pullbackTensorComparison f F G ≫
        tensorMapLeft ((pullback f).map φ) ((pullback f).obj G) := by
  let adj := pullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp only [pullbackTensorComparison]
  let q' :=
    tensorMapLeft (adj.unit.app F') G ≫
      tensorMapRight ((pushforward f).obj ((pullback f).obj F'))
        (adj.unit.app G) ≫
      pushforwardTensorHom f ((pullback f).obj F') ((pullback f).obj G)
  let q :=
    tensorMapLeft (adj.unit.app F) G ≫
      tensorMapRight ((pushforward f).obj ((pullback f).obj F))
        (adj.unit.app G) ≫
      pushforwardTensorHom f ((pullback f).obj F) ((pullback f).obj G)
  change tensorMapLeft φ G ≫
      adj.homEquiv _ _ ((adj.homEquiv _ _).symm q') =
    adj.homEquiv _ _ ((adj.homEquiv _ _).symm q) ≫ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  dsimp only [q, q']
  rw [← Category.assoc, ← tensorMapLeft_comp]
  have hu := adj.unit.naturality φ
  have hu' : φ ≫ adj.unit.app F' =
      adj.unit.app F ≫ (pushforward f).map ((pullback f).map φ) := by
    simpa only [Functor.id_obj, Functor.id_map, Functor.comp_map] using hu
  rw [hu', tensorMapLeft_comp]
  simp only [Category.assoc]
  have hex : tensorMapLeft ((pushforward f).map ((pullback f).map φ)) G ≫
      tensorMapRight ((pushforward f).obj ((pullback f).obj F')) (adj.unit.app G) =
    tensorMapRight ((pushforward f).obj ((pullback f).obj F)) (adj.unit.app G) ≫
      tensorMapLeft ((pushforward f).map ((pullback f).map φ))
        ((pushforward f).obj ((pullback f).obj G)) :=
    (tensorMap_exchange _ _).symm
  slice_lhs 2 3 => rw [hex]
  have hn : tensorMapLeft ((pushforward f).map ((pullback f).map φ))
        ((pushforward f).obj ((pullback f).obj G)) ≫
      pushforwardTensorHom f ((pullback f).obj F') ((pullback f).obj G) =
    pushforwardTensorHom f ((pullback f).obj F) ((pullback f).obj G) ≫
      (pushforward f).map (tensorMapLeft ((pullback f).map φ) ((pullback f).obj G)) :=
    pushforwardTensorHom_naturality_left f ((pullback f).map φ) ((pullback f).obj G)
  slice_lhs 3 4 => rw [hn]


/-- If the right tensor factor is isomorphic to the structure sheaf, the canonical
pullback--tensor comparison is an isomorphism. -/
theorem pullbackTensorComparison_isIso_of_iso_unit
    (f : X ⟶ Y) (F G : Y.Modules)
    (e : G ≅ SheafOfModules.unit Y.ringCatSheaf) :
    IsIso (pullbackTensorComparison f F G) := by
  let t := (pullback f).map (tensorMapRight F e.hom)
  let b := tensorMapRight ((pullback f).obj F) ((pullback f).map e.hom)
  let a := pullbackTensorComparison f F G
  let a' := pullbackTensorComparison f F
    (SheafOfModules.unit Y.ringCatSheaf)
  let _ : IsIso (tensorMapRight F e.hom) := by
    change IsIso (tensorRightIso F e).hom
    infer_instance
  let _ : IsIso t := by
    dsimp only [t]
    infer_instance
  let _ : IsIso ((pullback f).map e.hom) := by
    change IsIso ((pullback f).mapIso e).hom
    infer_instance
  let _ : IsIso b := by
    dsimp only [b]
    change IsIso (tensorRightIso ((pullback f).obj F)
      ((pullback f).mapIso e)).hom
    infer_instance
  let _ : IsIso a' :=
    pullbackTensorComparison_isIso_unit f F
  have h : t ≫ a' = a ≫ b := by
    exact pullbackTensorComparison_naturality_right f F e.hom
  let _ : IsIso (a ≫ b) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_right a b

/-- Pullback along an open immersion commutes with tensor products. -/
noncomputable def pullbackTensorIsoOfIsOpenImmersion (f : X ⟶ Y)
    [IsOpenImmersion f] (F G : Y.Modules) :
    (pullback f).obj (tensor F G) ≅
      tensor ((pullback f).obj F) ((pullback f).obj G) :=
  (((restrictFunctorIsoPullback f).symm.app (tensor F G)).trans
    (restrictTensorIso f F G)).trans
      ((tensorLeftIso ((restrictFunctorIsoPullback f).app F)
        ((restrictFunctor f).obj G)).trans
        (tensorRightIso ((pullback f).obj F)
          ((restrictFunctorIsoPullback f).app G)))

/-- Left-factor naturality of the pullback--tensor comparison along an open immersion. -/
theorem pullbackTensorIsoOfIsOpenImmersion_naturality_left (f : X ⟶ Y) [IsOpenImmersion f]
    {F F' : Y.Modules} (φ : F ⟶ F') (G : Y.Modules) :
    (pullback f).map (tensorMapLeft φ G) ≫
        (pullbackTensorIsoOfIsOpenImmersion f F' G).hom =
      (pullbackTensorIsoOfIsOpenImmersion f F G).hom ≫
        tensorMapLeft ((pullback f).map φ) ((pullback f).obj G) := by
  dsimp only [pullbackTensorIsoOfIsOpenImmersion, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    tensorLeftIso, tensorRightIso]
  -- naturality of `restrictFunctorIsoPullback` at `tensorMapLeft φ G`
  have h1 : (pullback f).map (tensorMapLeft φ G) ≫
      (restrictFunctorIsoPullback f).inv.app (tensor F' G) =
    (restrictFunctorIsoPullback f).inv.app (tensor F G) ≫
      (restrictFunctor f).map (tensorMapLeft φ G) :=
    (restrictFunctorIsoPullback f).inv.naturality (tensorMapLeft φ G)
  slice_lhs 1 2 => rw [h1]
  -- naturality of the restriction tensor comparison
  slice_lhs 2 3 => rw [restrictTensorIso_naturality_left f φ G]
  -- exchange the left map with the right-hand identification, then combine the left maps
  have h2 : tensorMapLeft ((restrictFunctor f).map φ) ((restrictFunctor f).obj G) ≫
      tensorMapLeft ((restrictFunctorIsoPullback f).hom.app F')
        ((restrictFunctor f).obj G) =
    tensorMapLeft ((restrictFunctorIsoPullback f).hom.app F)
        ((restrictFunctor f).obj G) ≫
      tensorMapLeft ((pullback f).map φ) ((restrictFunctor f).obj G) := by
    rw [← tensorMapLeft_comp, ← tensorMapLeft_comp,
      (restrictFunctorIsoPullback f).hom.naturality φ]
  slice_lhs 3 4 => rw [h2]
  slice_lhs 4 5 => rw [← tensorMap_exchange]
  simp only [Category.assoc]

/-- Left-factor naturality of the pullback--tensor comparison along an open immersion,
composed with an identification of the pulled-back right factor. -/
theorem pullbackTensorIsoOfIsOpenImmersion_tensorRight_naturality
    (f : X ⟶ Y) [IsOpenImmersion f] {F F' : Y.Modules} (φ : F ⟶ F') (W : Y.Modules)
    {W' : X.Modules} (eW : (pullback f).obj W ≅ W') :
    (pullback f).map (tensorMapLeft φ W) ≫
        ((pullbackTensorIsoOfIsOpenImmersion f F' W) ≪≫
          tensorRightIso ((pullback f).obj F') eW).hom =
      ((pullbackTensorIsoOfIsOpenImmersion f F W) ≪≫
          tensorRightIso ((pullback f).obj F) eW).hom ≫
        tensorMapLeft ((pullback f).map φ) W' := by
  dsimp only [Iso.trans_hom, tensorRightIso]
  rw [← Category.assoc, pullbackTensorIsoOfIsOpenImmersion_naturality_left]
  simp only [Category.assoc]
  congr 1
  exact (tensorMap_exchange _ _).symm

end AlgebraicGeometry.Scheme.Modules
