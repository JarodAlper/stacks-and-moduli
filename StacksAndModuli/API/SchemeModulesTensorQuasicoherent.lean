module

public import StacksAndModuli.API.SchemeModulesTensor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Quasicoherence and tensor products of scheme modules

This file develops the local tensor-product infrastructure needed to prove that
tensor products of quasicoherent modules on a scheme are quasicoherent. In particular,
restriction along an open immersion commutes with the tensor product of module sheaves.

Main declarations:

- `AlgebraicGeometry.Scheme.Modules.restrictPresheafTensorIso`;
- `AlgebraicGeometry.Scheme.Modules.restrictSheafificationIso`;
- `AlgebraicGeometry.Scheme.Modules.restrictTensorIso` and its naturality theorems;
- `AlgebraicGeometry.Scheme.Modules.tensorUnitIso` and
  `AlgebraicGeometry.Scheme.Modules.tensorLeftUnitIso`;
- `AlgebraicGeometry.Scheme.Modules.tensor_isQuasicoherent_of_iso_unit`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

section Restrict

variable (f : X ⟶ Y) [IsOpenImmersion f]

private instance moduleObj (Z : Scheme.{u}) (M : Z.Modules) (V : Z.Opensᵒᵖ) :
    Module Γ(Z, V.unop) (M.val.obj V) :=
  (M.val.obj V).isModule

/-- The objectwise tensor comparison underlying `restrictTensorIso`. -/
noncomputable def restrictTensorAppIso (F G : Y.Modules) (U : X.Opensᵒᵖ) :
    (MonoidalCategoryStruct.tensorObj (C := X.PresheafOfModules)
      ((restrictFunctor f).obj F).val ((restrictFunctor f).obj G).val).obj U ≅
      (ModuleCat.restrictScalars (f.appIso U.unop).inv.hom).obj
        ((MonoidalCategoryStruct.tensorObj (C := Y.PresheafOfModules)
          F.val G.val).obj (.op (f ''ᵁ U.unop))) := by
  letI : Module Γ(Y, f ''ᵁ U.unop)
      (F.val.obj (.op (f ''ᵁ U.unop))) :=
    (F.val.obj (.op (f ''ᵁ U.unop))).isModule
  letI : Module Γ(Y, f ''ᵁ U.unop)
      (G.val.obj (.op (f ''ᵁ U.unop))) :=
    (G.val.obj (.op (f ''ᵁ U.unop))).isModule
  let e : Γ(X, U.unop) ≃+* Γ(Y, f ''ᵁ U.unop) :=
    (f.appIso U.unop).symm.commRingCatIsoToRingEquiv
  letI : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv e
  letI : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    RingHomInvPair.of_ringEquiv e.symm
  let eF : ((restrictFunctor f).obj F).val.obj U ≃ₛₗ[e.toRingHom]
      F.val.obj (.op (f ''ᵁ U.unop)) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let eG : ((restrictFunctor f).obj G).val.obj U ≃ₛₗ[e.toRingHom]
      G.val.obj (.op (f ''ᵁ U.unop)) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let et := TensorProduct.congr eF eG
  let T := (ModuleCat.restrictScalars (f.appIso U.unop).inv.hom).obj
    ((MonoidalCategoryStruct.tensorObj (C := Y.PresheafOfModules)
      F.val G.val).obj (.op (f ''ᵁ U.unop)))
  letI : Module Γ(X, U.unop) T := T.isModule
  let S₀ := (MonoidalCategoryStruct.tensorObj (C := X.PresheafOfModules)
    ((restrictFunctor f).obj F).val ((restrictFunctor f).obj G).val).obj U
  letI : Module Γ(X, U.unop) S₀ := S₀.isModule
  let el : S₀ ≃ₗ[Γ(X, U.unop)] T :=
    { toFun := fun x ↦ et x
      invFun := fun x ↦ et.symm x
      left_inv := et.left_inv
      right_inv := et.right_inv
      map_add' := et.map_add
      map_smul' := fun a x ↦ by
        exact LinearEquiv.map_smulₛₗ et a x }
  exact LinearEquiv.toModuleIso el

/-- The ring-presheaf morphism underlying restriction of module sheaves along an open
immersion. -/
noncomputable def restrictRingHom :
    X.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ Y.ringCatSheaf.obj :=
  Functor.whiskerRight
    ({ app U := (f.appIso U.unop).inv } :
      X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf)
    (forget₂ CommRingCat RingCat)

/-- Restriction along an open immersion commutes with tensor products of presheaves of
modules. -/
noncomputable def restrictPresheafTensorIso (F G : Y.Modules) :
    MonoidalCategoryStruct.tensorObj (C := X.PresheafOfModules)
        ((restrictFunctor f).obj F).val ((restrictFunctor f).obj G).val ≅
      (_root_.PresheafOfModules.pushforward (restrictRingHom f)).obj
        (MonoidalCategoryStruct.tensorObj (C := Y.PresheafOfModules) F.val G.val) := by
  refine _root_.PresheafOfModules.isoMk
    (fun U ↦ restrictTensorAppIso f F G U) ?_
  intro U V k
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

/-- Local equivalences of presheaves of modules on a scheme. -/
abbrev moduleLocalEquivalences (Z : Scheme.{u}) :
    MorphismProperty Z.PresheafOfModules :=
  (Opens.grothendieckTopology Z).W.inverseImage
    (_root_.PresheafOfModules.toPresheaf Z.ringCatSheaf.obj)

/-- Sheafification of module presheaves is the localization at local equivalences,
restated at the scheme-specific spelling used by this file. -/
noncomputable instance instSheafificationIsLocalizationModuleLocalEquivalences
    (Z : Scheme.{u}) :
    (sheafification Z).IsLocalization (moduleLocalEquivalences Z) :=
  inferInstanceAs ((_root_.PresheafOfModules.sheafification
    (𝟙 Z.ringCatSheaf.obj)).IsLocalization
      ((Opens.grothendieckTopology Z).W.inverseImage
        (_root_.PresheafOfModules.toPresheaf Z.ringCatSheaf.obj)))

/-- Restriction along an open immersion preserves local equivalences of presheaves of
modules. -/
theorem restrictPreservesLocalEquivalence
    {P Q : Y.PresheafOfModules} (a : P ⟶ Q)
    (ha : moduleLocalEquivalences Y a) :
    moduleLocalEquivalences X
      ((_root_.PresheafOfModules.pushforward (restrictRingHom f)).map a) := by
  change (Opens.grothendieckTopology X).W
    ((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      ((_root_.PresheafOfModules.pushforward (restrictRingHom f)).map a))
  rw [(Opens.grothendieckTopology X).W_iff_isLocallyBijective]
  change (Opens.grothendieckTopology Y).W
    ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map a) at ha
  have hli := ha.isLocallyInjective
  have hls := ha.isLocallySurjective
  constructor
  · change Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (Functor.whiskerLeft f.opensFunctor.op
        ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map a))
    exact Presheaf.isLocallyInjective_whisker
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
      f.opensFunctor ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map a)
  · change Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (Functor.whiskerLeft f.opensFunctor.op
        ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map a))
    exact Presheaf.isLocallySurjective_whisker
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)
      f.opensFunctor ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map a)

/-- Module sheafification commutes with restriction along an open immersion. -/
noncomputable def restrictSheafificationIso (P : Y.PresheafOfModules) :
    (sheafification X).obj
        ((_root_.PresheafOfModules.pushforward (restrictRingHom f)).obj P) ≅
      (restrictFunctor f).obj ((sheafification Y).obj P) := by
  let adjY := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  let a := adjY.unit.app P
  have ha : moduleLocalEquivalences Y a := by
    change (Opens.grothendieckTopology Y).W
      ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map a)
    rw [show ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map a) =
        CategoryTheory.toSheafify (Opens.grothendieckTopology Y) P.presheaf by
      exact _root_.PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
        (𝟙 Y.ringCatSheaf.obj) P]
    exact (Opens.grothendieckTopology Y).W_toSheafify P.presheaf
  let b := (_root_.PresheafOfModules.pushforward (restrictRingHom f)).map a
  have hb : moduleLocalEquivalences X b :=
    restrictPreservesLocalEquivalence f a ha
  letI : IsIso ((sheafification X).map b) :=
    Localization.inverts (sheafification X) (moduleLocalEquivalences X) b hb
  let adjX := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adjX.counit :=
    Adjunction.counit_isIso_of_R_fully_faithful adjX
  exact asIso ((sheafification X).map b) ≪≫
    (asIso adjX.counit).app ((restrictFunctor f).obj ((sheafification Y).obj P))

/-- Restriction of module sheaves along an open immersion commutes with tensor products. -/
noncomputable def restrictTensorIso (F G : Y.Modules) :
    (restrictFunctor f).obj (tensor F G) ≅
      tensor ((restrictFunctor f).obj F) ((restrictFunctor f).obj G) :=
  (restrictSheafificationIso f
    (MonoidalCategoryStruct.tensorObj (C := Y.PresheafOfModules) F.val G.val)).symm ≪≫
    (sheafification X).mapIso (restrictPresheafTensorIso f F G).symm

/-- The presheaf tensor comparison for restriction is natural in both module factors. -/
theorem restrictPresheafTensorIso_naturality
    {F F' G G' : Y.Modules} (φ : F ⟶ F') (ψ : G ⟶ G') :
    MonoidalCategoryStruct.tensorHom (C := X.PresheafOfModules)
        ((restrictFunctor f).map φ).val ((restrictFunctor f).map ψ).val ≫
        (restrictPresheafTensorIso f F' G').hom =
      (restrictPresheafTensorIso f F G).hom ≫
        (_root_.PresheafOfModules.pushforward (restrictRingHom f)).map
          (MonoidalCategoryStruct.tensorHom (C := Y.PresheafOfModules)
            φ.val ψ.val) := by
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

/-- The comparison between restriction and sheafification is natural in the module
presheaf. -/
theorem restrictSheafificationIso_naturality
    {P Q : Y.PresheafOfModules} (a : P ⟶ Q) :
    (sheafification X).map
        ((_root_.PresheafOfModules.pushforward (restrictRingHom f)).map a) ≫
        (restrictSheafificationIso f Q).hom =
      (restrictSheafificationIso f P).hom ≫
        (restrictFunctor f).map ((sheafification Y).map a) := by
  dsimp only [restrictSheafificationIso, Iso.trans_hom, asIso_hom]
  let shX := sheafification X
  let push := _root_.PresheafOfModules.pushforward (restrictRingHom f)
  let adjX := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let adjY := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  rw [← Category.assoc, ← shX.map_comp, ← push.map_comp]
  have hu := adjY.unit.naturality a
  simp only [Functor.id_map, Functor.comp_map] at hu
  rw [hu]
  rw [push.map_comp, shX.map_comp]
  simp only [Category.assoc]
  have hpush :
      push.map
          ((_root_.PresheafOfModules.restrictScalars
              (𝟙 Y.ringCatSheaf.obj)).map
            ((SheafOfModules.forget Y.ringCatSheaf).map
              ((_root_.PresheafOfModules.sheafification
                (𝟙 Y.ringCatSheaf.obj)).map a))) =
        (_root_.PresheafOfModules.restrictScalars
            (𝟙 X.ringCatSheaf.obj)).map
          ((SheafOfModules.forget X.ringCatSheaf).map
            ((restrictFunctor f).map
              ((_root_.PresheafOfModules.sheafification
                (𝟙 Y.ringCatSheaf.obj)).map a))) := by
    rfl
  rw [hpush]
  let v := (restrictFunctor f).map
    ((_root_.PresheafOfModules.sheafification
      (𝟙 Y.ringCatSheaf.obj)).map a)
  have hc :
      (_root_.PresheafOfModules.sheafification
          (𝟙 X.ringCatSheaf.obj)).map
          ((_root_.PresheafOfModules.restrictScalars
              (𝟙 X.ringCatSheaf.obj)).map
            ((SheafOfModules.forget X.ringCatSheaf).map v)) ≫
          adjX.counit.app ((restrictFunctor f).obj
            ((_root_.PresheafOfModules.sheafification
              (𝟙 Y.ringCatSheaf.obj)).obj Q)) =
        adjX.counit.app ((restrictFunctor f).obj
            ((_root_.PresheafOfModules.sheafification
              (𝟙 Y.ringCatSheaf.obj)).obj P)) ≫ v := by
    simpa only [Functor.comp_map, Functor.id_map] using
      adjX.counit.naturality v
  let pre := shX.map (push.map (adjY.unit.app P))
  have hcomp := congrArg (fun k ↦ pre ≫ k) hc
  dsimp only [pre, v] at hcomp
  dsimp only [shX, push, adjX, adjY] at hcomp ⊢
  unfold sheafification at hcomp ⊢
  simpa only [Category.assoc, Functor.id_obj, asIso_hom, Iso.app_hom] using hcomp

set_option maxHeartbeats 800000 in
-- Naturality crosses both the presheaf tensor and sheafification adjunction layers.
/-- The tensor comparison for restriction is natural in both module factors. -/
theorem restrictTensorIso_naturality
    {F F' G G' : Y.Modules} (φ : F ⟶ F') (ψ : G ⟶ G') :
    (restrictFunctor f).map
        (tensorMapLeft φ G ≫ tensorMapRight F' ψ) ≫
        (restrictTensorIso f F' G').hom =
      (restrictTensorIso f F G).hom ≫
        (tensorMapLeft ((restrictFunctor f).map φ) ((restrictFunctor f).obj G) ≫
          tensorMapRight ((restrictFunctor f).obj F') ((restrictFunctor f).map ψ)) := by
  let hY := MonoidalCategoryStruct.tensorHom (C := Y.PresheafOfModules)
    φ.val ψ.val
  let hX := MonoidalCategoryStruct.tensorHom (C := X.PresheafOfModules)
    ((restrictFunctor f).map φ).val ((restrictFunctor f).map ψ).val
  have hYdef : hY =
      (((SheafOfModules.forget Y.ringCatSheaf).map φ) ▷ G.val) ≫
        (F'.val ◁ ((SheafOfModules.forget Y.ringCatSheaf).map ψ)) :=
    tensorHom_def _ _
  have hXdef : hX =
      (((SheafOfModules.forget X.ringCatSheaf).map
        ((restrictFunctor f).map φ)) ▷ ((restrictFunctor f).obj G).val) ≫
        (((restrictFunctor f).obj F').val ◁
          ((SheafOfModules.forget X.ringCatSheaf).map
            ((restrictFunctor f).map ψ))) :=
    tensorHom_def _ _
  have hsource : tensorMapLeft φ G ≫ tensorMapRight F' ψ =
      (sheafification Y).map hY := by
    dsimp only [tensorMapLeft, tensorMapRight]
    rw [← Functor.map_comp, ← hYdef]
  have htarget :
      tensorMapLeft ((restrictFunctor f).map φ) ((restrictFunctor f).obj G) ≫
          tensorMapRight ((restrictFunctor f).obj F') ((restrictFunctor f).map ψ) =
        (sheafification X).map hX := by
    dsimp only [tensorMapLeft, tensorMapRight]
    rw [← Functor.map_comp, ← hXdef]
  rw [hsource, htarget]
  let eP := restrictSheafificationIso f
    (MonoidalCategoryStruct.tensorObj (C := Y.PresheafOfModules) F.val G.val)
  let eQ := restrictSheafificationIso f
    (MonoidalCategoryStruct.tensorObj (C := Y.PresheafOfModules) F'.val G'.val)
  let rP := restrictPresheafTensorIso f F G
  let rQ := restrictPresheafTensorIso f F' G'
  let push := _root_.PresheafOfModules.pushforward (restrictRingHom f)
  have heHom := restrictSheafificationIso_naturality f hY
  change (sheafification X).map (push.map hY) ≫ eQ.hom =
    eP.hom ≫ (restrictFunctor f).map ((sheafification Y).map hY) at heHom
  have heInv :
      (restrictFunctor f).map ((sheafification Y).map hY) ≫ eQ.inv =
        eP.inv ≫ (sheafification X).map (push.map hY) := by
    rw [← cancel_mono eQ.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    symm
    rw [heHom, Iso.inv_hom_id_assoc]
  have hrHom := restrictPresheafTensorIso_naturality f φ ψ
  change hX ≫ rQ.hom = rP.hom ≫ push.map hY at hrHom
  have hrInv : push.map hY ≫ rQ.inv = rP.inv ≫ hX := by
    rw [← cancel_mono rQ.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    symm
    rw [hrHom, Iso.inv_hom_id_assoc]
  change
    (restrictFunctor f).map ((sheafification Y).map hY) ≫ eQ.inv ≫
        (sheafification X).map rQ.inv =
      (eP.inv ≫ (sheafification X).map rP.inv) ≫
        (sheafification X).map hX
  slice_lhs 1 2 => rw [heInv]
  simp only [Category.assoc]
  rw [← (sheafification X).map_comp]
  rw [hrInv]
  rw [(sheafification X).map_comp]

/-- Left-factor naturality of the tensor comparison for restriction. -/
theorem restrictTensorIso_naturality_left
    {F F' : Y.Modules} (φ : F ⟶ F') (G : Y.Modules) :
    (restrictFunctor f).map (tensorMapLeft φ G) ≫ (restrictTensorIso f F' G).hom =
      (restrictTensorIso f F G).hom ≫
        tensorMapLeft ((restrictFunctor f).map φ) ((restrictFunctor f).obj G) := by
  have h := restrictTensorIso_naturality f φ (𝟙 G)
  rw [(restrictFunctor f).map_id, tensorMapRight_id, tensorMapRight_id, Category.comp_id,
    Category.comp_id] at h
  exact h

end Restrict

/-- Tensoring a sheaf of modules on the right with the structure sheaf does nothing. -/
noncomputable def tensorUnitIso (F : X.Modules) :
    tensor F (SheafOfModules.unit X.ringCatSheaf) ≅ F :=
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit :=
    Adjunction.counit_isIso_of_R_fully_faithful adj
  (sheafification X).mapIso (ρ_ F.val) ≪≫
    (asIso adj.counit).app F

/-- Tensoring a sheaf of modules on the left with the structure sheaf does nothing. -/
noncomputable def tensorLeftUnitIso (F : X.Modules) :
    tensor (SheafOfModules.unit X.ringCatSheaf) F ≅ F :=
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit :=
    Adjunction.counit_isIso_of_R_fully_faithful adj
  (sheafification X).mapIso (λ_ F.val) ≪≫
    (asIso adj.counit).app F

/-- Tensoring a quasicoherent sheaf with a sheaf isomorphic to the structure sheaf
is quasicoherent. -/
theorem tensor_isQuasicoherent_of_iso_unit (F L : X.Modules)
    [F.IsQuasicoherent] (e : L ≅ SheafOfModules.unit X.ringCatSheaf) :
    (tensor F L).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (tensorRightIso F e ≪≫ tensorUnitIso F).symm inferInstance

end AlgebraicGeometry.Scheme.Modules
