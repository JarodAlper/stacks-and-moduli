module

public import StacksAndModuli.API.SchemeModulesPullbackTensorUnitCoherence
public import StacksAndModuli.API.SchemeModulesTensorSymmetry

/-!
# Coherence of pullback with tensor symmetry and associativity

This file develops the coherence squares for the canonical pullback--tensor
comparison that are needed to transport calculations with invertible module sheaves
through a morphism of schemes.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

noncomputable local instance instBraidedPresheafOfModulesX :
    BraidedCategory X.PresheafOfModules :=
  inferInstanceAs (BraidedCategory
    (_root_.PresheafOfModules.{u}
      (X.presheaf ⋙ forget₂ CommRingCat RingCat)))

noncomputable local instance instBraidedPresheafOfModulesY :
    BraidedCategory Y.PresheafOfModules :=
  inferInstanceAs (BraidedCategory
    (_root_.PresheafOfModules.{u}
      (Y.presheaf ⋙ forget₂ CommRingCat RingCat)))

/-- The objectwise tensor map for pushforward commutes with the presheaf tensor
symmetry. -/
lemma pushforwardPresheafTensorHom_comm (f : X ⟶ Y) (F G : X.Modules) :
    (β_ ((pushforward f).obj F).val ((pushforward f).obj G).val).hom ≫
        pushforwardPresheafTensorHom f G F =
      pushforwardPresheafTensorHom f F G ≫
        (_root_.PresheafOfModules.pushforward
          f.toRingCatSheafHom.hom).map (β_ F.val G.val).hom := by
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

/-- The tensor map for pushforward commutes with the chosen sheaf tensor symmetry. -/
lemma pushforwardTensorHom_comm (f : X ⟶ Y) (F G : X.Modules) :
    (tensorCommIso ((pushforward f).obj F) ((pushforward f).obj G)).hom ≫
        pushforwardTensorHom f G F =
      pushforwardTensorHom f F G ≫
        (pushforward f).map (tensorCommIso F G).hom := by
  let adjX := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let adjY := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  let pf := _root_.PresheafOfModules.pushforward
    f.toRingCatSheafHom.hom
  apply (adjY.homEquiv _ _).injective
  dsimp only [tensorCommIso, Functor.mapIso_hom]
  let bY := (β_ ((pushforward f).obj F).val
    ((pushforward f).obj G).val).hom
  have hleft := adjY.homEquiv_naturality_left bY
    (pushforwardTensorHom f G F)
  change adjY.homEquiv _ _
      ((_root_.PresheafOfModules.sheafification
        (𝟙 Y.ringCatSheaf.obj)).map bY ≫
          pushforwardTensorHom f G F) = _
  rw [hleft, Adjunction.homEquiv_naturality_right]
  rw [pushforwardTensorHom_homEquiv, pushforwardTensorHom_homEquiv]
  let bX := (β_ F.val G.val).hom
  change bY ≫ pushforwardPresheafTensorHom f G F ≫
      pf.map (adjX.unit.app (G.val ⊗ F.val)) =
    pushforwardPresheafTensorHom f F G ≫
      pf.map (adjX.unit.app (F.val ⊗ G.val)) ≫
      ((SheafOfModules.forget Y.ringCatSheaf ⋙
        _root_.PresheafOfModules.restrictScalars
          (𝟙 Y.ringCatSheaf.obj)).map
        ((pushforward f).map (tensorCommIso F G).hom))
  have hb := pushforwardPresheafTensorHom_comm f F G
  change bY ≫ pushforwardPresheafTensorHom f G F =
    pushforwardPresheafTensorHom f F G ≫ pf.map bX at hb
  have hu := adjX.unit.naturality bX
  have hu' : bX ≫ adjX.unit.app (G.val ⊗ F.val) =
      adjX.unit.app (F.val ⊗ G.val) ≫
        (SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars
            (𝟙 X.ringCatSheaf.obj)).map
          ((_root_.PresheafOfModules.sheafification
            (𝟙 X.ringCatSheaf.obj)).map bX) := by
    simpa only [Functor.id_obj, Functor.id_map, Functor.comp_map] using hu
  calc
    bY ≫ pushforwardPresheafTensorHom f G F ≫
          pf.map (adjX.unit.app (G.val ⊗ F.val)) =
        (pushforwardPresheafTensorHom f F G ≫ pf.map bX) ≫
          pf.map (adjX.unit.app (G.val ⊗ F.val)) :=
      congrArg (fun k ↦ k ≫
        pf.map (adjX.unit.app (G.val ⊗ F.val))) hb
    _ = pushforwardPresheafTensorHom f F G ≫
          pf.map (bX ≫ adjX.unit.app (G.val ⊗ F.val)) := by
      rw [pf.map_comp]
      simp only [Category.assoc]
    _ = pushforwardPresheafTensorHom f F G ≫
          pf.map (adjX.unit.app (F.val ⊗ G.val) ≫
            (SheafOfModules.forget X.ringCatSheaf ⋙
              _root_.PresheafOfModules.restrictScalars
                (𝟙 X.ringCatSheaf.obj)).map
              ((_root_.PresheafOfModules.sheafification
                (𝟙 X.ringCatSheaf.obj)).map bX)) := by rw [hu']
    _ = _ := by
      rw [pf.map_comp]
      rfl

set_option maxHeartbeats 800000 in
/-- The canonical pullback--tensor comparison commutes with the chosen tensor
symmetry. -/
lemma pullbackTensorComparison_comm (f : X ⟶ Y) (F G : Y.Modules) :
    pullbackTensorComparison f F G ≫
        (tensorCommIso ((pullback f).obj F) ((pullback f).obj G)).hom =
      (pullback f).map (tensorCommIso F G).hom ≫
        pullbackTensorComparison f G F := by
  let adj := pullbackPushforwardAdjunction f
  let ηF := adj.unit.app F
  let ηG := adj.unit.app G
  let PF := (pullback f).obj F
  let PG := (pullback f).obj G
  let qFG := tensorMapLeft ηF G ≫
    tensorMapRight ((pushforward f).obj PF) ηG ≫
    pushforwardTensorHom f PF PG
  let qGF := tensorMapLeft ηG F ≫
    tensorMapRight ((pushforward f).obj PG) ηF ≫
    pushforwardTensorHom f PG PF
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_left]
  dsimp only [pullbackTensorComparison]
  dsimp only [adj]
  simp only [Equiv.apply_symm_apply]
  change qFG ≫
      (pushforward f).map (tensorCommIso PF PG).hom =
    (tensorCommIso F G).hom ≫ qGF
  have hp := pushforwardTensorHom_comm f PF PG
  have hη :
      tensorMapLeft ηF G ≫
          tensorMapRight ((pushforward f).obj PF) ηG ≫
          (tensorCommIso ((pushforward f).obj PF)
            ((pushforward f).obj PG)).hom =
        (tensorCommIso F G).hom ≫
          tensorMapLeft ηG F ≫
          tensorMapRight ((pushforward f).obj PG) ηF := by
    calc
      tensorMapLeft ηF G ≫
            tensorMapRight ((pushforward f).obj PF) ηG ≫
            (tensorCommIso ((pushforward f).obj PF)
              ((pushforward f).obj PG)).hom =
          tensorMapLeft ηF G ≫
            (tensorCommIso ((pushforward f).obj PF) G).hom ≫
            tensorMapLeft ηG ((pushforward f).obj PF) := by
        have hr := tensorCommIso_hom_naturality_right
          ((pushforward f).obj PF) ηG
        change tensorMapRight ((pushforward f).obj PF) ηG ≫
            (tensorCommIso ((pushforward f).obj PF)
              ((pushforward f).obj PG)).hom =
          (tensorCommIso ((pushforward f).obj PF) G).hom ≫
            tensorMapLeft ηG ((pushforward f).obj PF) at hr
        simpa only [Category.assoc] using congrArg
          (fun k ↦ tensorMapLeft ηF G ≫ k) hr
      _ = (tensorCommIso F G).hom ≫
            tensorMapRight G ηF ≫
            tensorMapLeft ηG ((pushforward f).obj PF) := by
        have hl := tensorCommIso_hom_naturality_left ηF G
        change tensorMapLeft ηF G ≫
            (tensorCommIso ((pushforward f).obj PF) G).hom =
          (tensorCommIso F G).hom ≫ tensorMapRight G ηF at hl
        exact congrArg
          (fun k ↦ k ≫ tensorMapLeft ηG ((pushforward f).obj PF)) hl
      _ = (tensorCommIso F G).hom ≫
            tensorMapLeft ηG F ≫
            tensorMapRight ((pushforward f).obj PG) ηF := by
        exact congrArg (fun k ↦ (tensorCommIso F G).hom ≫ k)
          (tensorMap_exchange ηG ηF)
  dsimp only [qFG, qGF]
  calc
    tensorMapLeft ηF G ≫
          tensorMapRight ((pushforward f).obj PF) ηG ≫
          pushforwardTensorHom f PF PG ≫
          (pushforward f).map (tensorCommIso PF PG).hom =
        tensorMapLeft ηF G ≫
          tensorMapRight ((pushforward f).obj PF) ηG ≫
          (tensorCommIso ((pushforward f).obj PF)
            ((pushforward f).obj PG)).hom ≫
          pushforwardTensorHom f PG PF := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ tensorMapLeft ηF G ≫
          tensorMapRight ((pushforward f).obj PF) ηG ≫ k) hp.symm
    _ = ((tensorCommIso F G).hom ≫
          tensorMapLeft ηG F ≫
          tensorMapRight ((pushforward f).obj PG) ηF) ≫
          pushforwardTensorHom f PG PF :=
      congrArg (fun k ↦ k ≫ pushforwardTensorHom f PG PF) hη
    _ = _ := by simp only [Category.assoc]

/-- The chosen symmetry between the unit and a module, followed by the right
unitor, is the chosen left unitor. -/
lemma tensorCommIso_unit_comp_tensorUnitIso (F : X.Modules) :
    (tensorCommIso (SheafOfModules.unit X.ringCatSheaf) F).hom ≫
        (tensorUnitIso F).hom =
      (tensorLeftUnitIso F).hom := by
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit :=
    Adjunction.counit_isIso_of_R_fully_faithful adj
  have hinv :
      (tensorLeftUnitIso F).inv ≫
          (tensorCommIso (SheafOfModules.unit X.ringCatSheaf) F).hom =
        (tensorUnitIso F).inv := by
    dsimp only [tensorLeftUnitIso, tensorCommIso, tensorUnitIso]
    simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
      Functor.mapIso_hom, asIso_inv, Iso.app_inv]
    rw [Category.assoc, ← (sheafification X).map_comp]
    exact congrArg
      (fun k ↦ (asIso adj.counit).inv.app F ≫ (sheafification X).map k)
      (CategoryTheory.leftUnitor_inv_braiding F.val)
  rw [← cancel_epi (tensorLeftUnitIso F).inv]
  rw [← Category.assoc, hinv, Iso.inv_hom_id]
  exact (tensorLeftUnitIso F).inv_hom_id.symm

/-- If pullback commutes with a tensor product in one order, it also commutes with
the swapped tensor product. -/
theorem pullbackTensorComparison_isIso_swap
    (f : X ⟶ Y) (F G : Y.Modules)
    [IsIso (pullbackTensorComparison f F G)] :
    IsIso (pullbackTensorComparison f G F) := by
  let a := pullbackTensorComparison f F G ≫
    (tensorCommIso ((pullback f).obj F) ((pullback f).obj G)).hom
  let b := (pullback f).map (tensorCommIso F G).hom
  let c := pullbackTensorComparison f G F
  have h : a = b ≫ c := pullbackTensorComparison_comm f F G
  letI : IsIso a := by
    dsimp only [a]
    infer_instance
  letI : IsIso b := by
    dsimp only [b]
    infer_instance
  letI : IsIso (b ≫ c) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_left b c

/-- The canonical pullback--tensor comparison is compatible with the left unitor
and the comparison between the pulled-back structure sheaf and the structure
sheaf. -/
lemma pullbackTensorComparison_comp_leftUnit
    (f : X ⟶ Y) (F : Y.Modules) :
    pullbackTensorComparison f
          (SheafOfModules.unit Y.ringCatSheaf) F ≫
        tensorMapLeft
          (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
          ((pullback f).obj F) ≫
        (tensorLeftUnitIso ((pullback f).obj F)).hom =
      (pullback f).map (tensorLeftUnitIso F).hom := by
  let UY := SheafOfModules.unit Y.ringCatSheaf
  let UX := SheafOfModules.unit X.ringCatSheaf
  let PF := (pullback f).obj F
  let PU := (pullback f).obj UY
  let u : PU ⟶ UX :=
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  let cUF := pullbackTensorComparison f UY F
  let cFU := pullbackTensorComparison f F UY
  let bUF := (tensorCommIso UY F).hom
  let bPUF := (tensorCommIso PU PF).hom
  let bX := (tensorCommIso UX PF).hom
  have hcomm : cUF ≫ bPUF = (pullback f).map bUF ≫ cFU := by
    exact pullbackTensorComparison_comm f UY F
  have hnat : tensorMapLeft u PF ≫ bX =
      bPUF ≫ tensorMapRight PF u := by
    exact tensorCommIso_hom_naturality_left u PF
  have hunitY : bUF ≫ (tensorUnitIso F).hom =
      (tensorLeftUnitIso F).hom := tensorCommIso_unit_comp_tensorUnitIso F
  have hunitX : bX ≫ (tensorUnitIso PF).hom =
      (tensorLeftUnitIso PF).hom := tensorCommIso_unit_comp_tensorUnitIso PF
  have hright := pullbackTensorComparison_comp_unit f F
  change cFU ≫ tensorMapRight PF u ≫ (tensorUnitIso PF).hom =
    (pullback f).map (tensorUnitIso F).hom at hright
  change cUF ≫ tensorMapLeft u PF ≫ (tensorLeftUnitIso PF).hom =
    (pullback f).map (tensorLeftUnitIso F).hom
  calc
    cUF ≫ tensorMapLeft u PF ≫ (tensorLeftUnitIso PF).hom =
        cUF ≫ tensorMapLeft u PF ≫ bX ≫ (tensorUnitIso PF).hom := by
      exact congrArg (fun k ↦ cUF ≫ tensorMapLeft u PF ≫ k) hunitX.symm
    _ = cUF ≫ bPUF ≫ tensorMapRight PF u ≫
          (tensorUnitIso PF).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ cUF ≫ k ≫ (tensorUnitIso PF).hom) hnat
    _ = (pullback f).map bUF ≫ cFU ≫ tensorMapRight PF u ≫
          (tensorUnitIso PF).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ tensorMapRight PF u ≫ (tensorUnitIso PF).hom) hcomm
    _ = (pullback f).map bUF ≫
          (pullback f).map (tensorUnitIso F).hom :=
      congrArg (fun k ↦ (pullback f).map bUF ≫ k) hright
    _ = (pullback f).map (bUF ≫ (tensorUnitIso F).hom) := by
      rw [(pullback f).map_comp]
    _ = _ := by rw [hunitY]

/-- The chosen sheaf tensor associator carries the two canonical sheafification
maps out of the raw presheaf triple tensor into one another. -/
lemma tensorAssocIso_unit (F G H : X.Modules) :
    let adj := _root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    let uFG := adj.unit.app (F.val ⊗ G.val)
    let uGH := adj.unit.app (G.val ⊗ H.val)
    (uFG ▷ H.val) ≫
        adj.unit.app ((tensor F G).val ⊗ H.val) ≫
        (tensorAssocIso F G H).hom.val =
      (α_ F.val G.val H.val).hom ≫
        (F.val ◁ uGH) ≫
        adj.unit.app (F.val ⊗ (tensor G H).val) := by
  dsimp only
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let L := sheafification X
  let W := tensorLocalEquivalences X
  let uFG := adj.unit.app (F.val ⊗ G.val)
  let uGH := adj.unit.app (G.val ⊗ H.val)
  have hunitMem (A : X.PresheafOfModules) : W (adj.unit.app A) := by
    change (Opens.grothendieckTopology X).W
      ((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (adj.unit.app A))
    simpa [adj] using
      (Opens.grothendieckTopology X).W_toSheafify A.presheaf
  have huFGH : W (uFG ▷ H.val) :=
    W.whiskerRight_mem uFG (hunitMem (F.val ⊗ G.val)) H.val
  have hFuGH : W (F.val ◁ uGH) :=
    W.whiskerLeft_mem F.val uGH (hunitMem (G.val ⊗ H.val))
  let iFGH := Localization.isoOfHom L W (uFG ▷ H.val) huFGH
  let iFuGH := Localization.isoOfHom L W (F.val ◁ uGH) hFuGH
  have hleft := adj.unit.naturality (uFG ▷ H.val)
  have hright₁ := adj.unit.naturality (α_ F.val G.val H.val).hom
  have hright₂ := adj.unit.naturality (F.val ◁ uGH)
  change (uFG ▷ H.val) ≫
      adj.unit.app ((tensor F G).val ⊗ H.val) ≫
      (iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫ iFuGH.hom).val = _
  have hiFGH :
      adj.unit.app ((F.val ⊗ G.val) ⊗ H.val) ≫ iFGH.hom.val =
        (uFG ▷ H.val) ≫
          adj.unit.app ((tensor F G).val ⊗ H.val) := by
    change (uFG ▷ H.val) ≫
        adj.unit.app ((tensor F G).val ⊗ H.val) =
      adj.unit.app ((F.val ⊗ G.val) ⊗ H.val) ≫
        (L.map (uFG ▷ H.val)).val at hleft
    change adj.unit.app ((F.val ⊗ G.val) ⊗ H.val) ≫
        (L.map (uFG ▷ H.val)).val = _
    exact hleft.symm
  have hiFuGH :
      adj.unit.app (F.val ⊗ (G.val ⊗ H.val)) ≫ iFuGH.hom.val =
        (F.val ◁ uGH) ≫
          adj.unit.app (F.val ⊗ (tensor G H).val) := by
    change (F.val ◁ uGH) ≫
        adj.unit.app (F.val ⊗ (tensor G H).val) =
      adj.unit.app (F.val ⊗ (G.val ⊗ H.val)) ≫
        (L.map (F.val ◁ uGH)).val at hright₂
    change adj.unit.app (F.val ⊗ (G.val ⊗ H.val)) ≫
        (L.map (F.val ◁ uGH)).val = _
    exact hright₂.symm
  have ha :
      (α_ F.val G.val H.val).hom ≫
          adj.unit.app (F.val ⊗ (G.val ⊗ H.val)) =
        adj.unit.app ((F.val ⊗ G.val) ⊗ H.val) ≫
          (L.map (α_ F.val G.val H.val).hom).val := by
    change (α_ F.val G.val H.val).hom ≫
        adj.unit.app (F.val ⊗ (G.val ⊗ H.val)) =
      adj.unit.app ((F.val ⊗ G.val) ⊗ H.val) ≫
        (L.map (α_ F.val G.val H.val).hom).val at hright₁
    exact hright₁
  calc
    (uFG ▷ H.val) ≫
          adj.unit.app ((tensor F G).val ⊗ H.val) ≫
          (iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫
            iFuGH.hom).val =
        (adj.unit.app ((F.val ⊗ G.val) ⊗ H.val) ≫ iFGH.hom.val) ≫
          (iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫
            iFuGH.hom).val :=
      congrArg (fun k ↦ k ≫
        (iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫
          iFuGH.hom).val) hiFGH.symm
    _ = adj.unit.app ((F.val ⊗ G.val) ⊗ H.val) ≫
          (L.map (α_ F.val G.val H.val).hom).val ≫ iFuGH.hom.val := by
      have hc : iFGH.hom ≫
          (iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫ iFuGH.hom) =
          L.map (α_ F.val G.val H.val).hom ≫ iFuGH.hom := by simp
      change adj.unit.app ((F.val ⊗ G.val) ⊗ H.val) ≫
          (iFGH.hom ≫
            (iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫
              iFuGH.hom)).val = _
      rw [hc]
      rfl
    _ = ((α_ F.val G.val H.val).hom ≫
          adj.unit.app (F.val ⊗ (G.val ⊗ H.val))) ≫
          iFuGH.hom.val := congrArg (fun k ↦ k ≫ iFuGH.hom.val) ha.symm
    _ = (α_ F.val G.val H.val).hom ≫
          (F.val ◁ uGH) ≫
          adj.unit.app (F.val ⊗ (tensor G H).val) := by
      rw [Category.assoc, hiFuGH]

/-- Naturality of the chosen sheaf tensor associator in its right variable. -/
@[reassoc]
lemma tensorAssocIso_hom_naturality_right
    (F G : X.Modules) {H H' : X.Modules} (h : H ⟶ H') :
    tensorMapRight (tensor F G) h ≫ (tensorAssocIso F G H').hom =
      (tensorAssocIso F G H).hom ≫
        tensorMapRight F (tensorMapRight G h) := by
  let L := sheafification X
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let W := tensorLocalEquivalences X
  let uFG := adj.unit.app (F.val ⊗ G.val)
  let uGH := adj.unit.app (G.val ⊗ H.val)
  let uGH' := adj.unit.app (G.val ⊗ H'.val)
  have hunitMem (A : X.PresheafOfModules) : W (adj.unit.app A) := by
    change (Opens.grothendieckTopology X).W
      ((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (adj.unit.app A))
    simpa [adj] using
      (Opens.grothendieckTopology X).W_toSheafify A.presheaf
  have huFGH : W (uFG ▷ H.val) :=
    W.whiskerRight_mem uFG (hunitMem (F.val ⊗ G.val)) H.val
  have huFGH' : W (uFG ▷ H'.val) :=
    W.whiskerRight_mem uFG (hunitMem (F.val ⊗ G.val)) H'.val
  have hFuGH : W (F.val ◁ uGH) :=
    W.whiskerLeft_mem F.val uGH (hunitMem (G.val ⊗ H.val))
  have hFuGH' : W (F.val ◁ uGH') :=
    W.whiskerLeft_mem F.val uGH' (hunitMem (G.val ⊗ H'.val))
  let iFGH := Localization.isoOfHom L W (uFG ▷ H.val) huFGH
  let iFGH' := Localization.isoOfHom L W (uFG ▷ H'.val) huFGH'
  let iFuGH := Localization.isoOfHom L W (F.val ◁ uGH) hFuGH
  let iFuGH' := Localization.isoOfHom L W (F.val ◁ uGH') hFuGH'
  have hleftMap := congrArg L.map
    (MonoidalCategory.whisker_exchange uFG h.val)
  simp only [Functor.map_comp] at hleftMap
  change L.map ((F.val ⊗ G.val) ◁ h.val) ≫ iFGH'.hom =
    iFGH.hom ≫ L.map ((L.obj (F.val ⊗ G.val)).val ◁ h.val) at hleftMap
  have hleft :
      L.map ((L.obj (F.val ⊗ G.val)).val ◁ h.val) ≫ iFGH'.inv =
        iFGH.inv ≫ L.map ((F.val ⊗ G.val) ◁ h.val) := by
    rw [← cancel_mono iFGH'.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun k ↦ iFGH.inv ≫ k) hleftMap.symm
  have hassoc := congrArg L.map
    (MonoidalCategory.associator_naturality_right F.val G.val h.val)
  simp only [Functor.map_comp] at hassoc
  have hu := adj.unit.naturality (G.val ◁ h.val)
  have huraw :
      (G.val ◁ h.val) ≫ uGH' =
        uGH ≫ (L.map (G.val ◁ h.val)).val := by
    change (G.val ◁ h.val) ≫ uGH' =
      uGH ≫ (L.map (G.val ◁ h.val)).val at hu
    exact hu
  have huraw' :
      (F.val ◁ (G.val ◁ h.val)) ≫ (F.val ◁ uGH') =
        (F.val ◁ uGH) ≫
          (F.val ◁ (L.map (G.val ◁ h.val)).val) := by
    rw [← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp]
    exact congrArg (fun k ↦ F.val ◁ k) huraw
  have hrightMap := congrArg L.map huraw'
  simp only [Functor.map_comp] at hrightMap
  change L.map (F.val ◁ (G.val ◁ h.val)) ≫ iFuGH'.hom =
    iFuGH.hom ≫
      L.map (F.val ◁ (L.map (G.val ◁ h.val)).val) at hrightMap
  change L.map ((L.obj (F.val ⊗ G.val)).val ◁ h.val) ≫
      iFGH'.inv ≫ L.map (α_ F.val G.val H'.val).hom ≫ iFuGH'.hom =
    iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫ iFuGH.hom ≫
      L.map (F.val ◁ (L.map (G.val ◁ h.val)).val)
  calc
    L.map ((L.obj (F.val ⊗ G.val)).val ◁ h.val) ≫
          iFGH'.inv ≫ L.map (α_ F.val G.val H'.val).hom ≫
          iFuGH'.hom =
        (iFGH.inv ≫ L.map ((F.val ⊗ G.val) ◁ h.val)) ≫
          L.map (α_ F.val G.val H'.val).hom ≫ iFuGH'.hom :=
      congrArg (fun k ↦ k ≫ L.map (α_ F.val G.val H'.val).hom ≫
        iFuGH'.hom) hleft
    _ = iFGH.inv ≫
          (L.map ((F.val ⊗ G.val) ◁ h.val) ≫
            L.map (α_ F.val G.val H'.val).hom) ≫ iFuGH'.hom := by
      simp only [Category.assoc]
    _ = iFGH.inv ≫
          (L.map (α_ F.val G.val H.val).hom ≫
            L.map (F.val ◁ (G.val ◁ h.val))) ≫ iFuGH'.hom :=
      congrArg (fun k ↦ iFGH.inv ≫ k ≫ iFuGH'.hom) hassoc
    _ = iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫
          (L.map (F.val ◁ (G.val ◁ h.val)) ≫ iFuGH'.hom) := by
      simp only [Category.assoc]
    _ = iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫
          (iFuGH.hom ≫
            L.map (F.val ◁ (L.map (G.val ◁ h.val)).val)) :=
      congrArg (fun k ↦ iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫ k)
        hrightMap
    _ = _ := rfl

/-- Naturality of the chosen sheaf tensor associator in its middle variable. -/
@[reassoc]
lemma tensorAssocIso_hom_naturality_middle
    (F : X.Modules) {G G' : X.Modules} (g : G ⟶ G') (H : X.Modules) :
    tensorMapLeft (tensorMapRight F g) H ≫ (tensorAssocIso F G' H).hom =
      (tensorAssocIso F G H).hom ≫
        tensorMapRight F (tensorMapLeft g H) := by
  let L := sheafification X
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let W := tensorLocalEquivalences X
  let fg := F.val ◁ g.val
  let uFG := adj.unit.app (F.val ⊗ G.val)
  let uFG' := adj.unit.app (F.val ⊗ G'.val)
  let uGH := adj.unit.app (G.val ⊗ H.val)
  let uG'H := adj.unit.app (G'.val ⊗ H.val)
  have hunitMem (A : X.PresheafOfModules) : W (adj.unit.app A) := by
    change (Opens.grothendieckTopology X).W
      ((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (adj.unit.app A))
    simpa [adj] using
      (Opens.grothendieckTopology X).W_toSheafify A.presheaf
  have huFGH : W (uFG ▷ H.val) :=
    W.whiskerRight_mem uFG (hunitMem (F.val ⊗ G.val)) H.val
  have huFG'H : W (uFG' ▷ H.val) :=
    W.whiskerRight_mem uFG' (hunitMem (F.val ⊗ G'.val)) H.val
  have hFuGH : W (F.val ◁ uGH) :=
    W.whiskerLeft_mem F.val uGH (hunitMem (G.val ⊗ H.val))
  have hFuG'H : W (F.val ◁ uG'H) :=
    W.whiskerLeft_mem F.val uG'H (hunitMem (G'.val ⊗ H.val))
  let iFGH := Localization.isoOfHom L W (uFG ▷ H.val) huFGH
  let iFG'H := Localization.isoOfHom L W (uFG' ▷ H.val) huFG'H
  let iFuGH := Localization.isoOfHom L W (F.val ◁ uGH) hFuGH
  let iFuG'H := Localization.isoOfHom L W (F.val ◁ uG'H) hFuG'H
  have hunit :
      (fg ▷ H.val) ≫ (uFG' ▷ H.val) =
        (uFG ▷ H.val) ≫ (((L.map fg).val) ▷ H.val) := by
    rw [← MonoidalCategory.comp_whiskerRight,
      ← MonoidalCategory.comp_whiskerRight]
    exact congrArg (fun k ↦ k ▷ H.val) (adj.unit.naturality fg)
  change L.map ((L.map fg).val ▷ H.val) ≫ iFG'H.inv ≫
      L.map (α_ F.val G'.val H.val).hom ≫ iFuG'H.hom =
    iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫ iFuGH.hom ≫
      L.map (F.val ◁ (L.map (g.val ▷ H.val)).val)
  have hunitMap := congrArg L.map hunit
  simp only [Functor.map_comp] at hunitMap
  change L.map (fg ▷ H.val) ≫ iFG'H.hom =
    iFGH.hom ≫ L.map ((L.map fg).val ▷ H.val) at hunitMap
  have hleft : L.map ((L.map fg).val ▷ H.val) ≫ iFG'H.inv =
      iFGH.inv ≫ L.map (fg ▷ H.val) := by
    rw [← cancel_mono iFG'H.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun k ↦ iFGH.inv ≫ k) hunitMap.symm
  have hassoc := congrArg L.map
    (MonoidalCategory.associator_naturality_middle F.val g.val H.val)
  simp only [Functor.map_comp] at hassoc
  have hu := adj.unit.naturality (g.val ▷ H.val)
  have huraw :
      (g.val ▷ H.val) ≫ uG'H =
        uGH ≫ (L.map (g.val ▷ H.val)).val := by
    change (g.val ▷ H.val) ≫ uG'H =
      uGH ≫ (L.map (g.val ▷ H.val)).val at hu
    exact hu
  have huraw' :
      (F.val ◁ (g.val ▷ H.val)) ≫ (F.val ◁ uG'H) =
        (F.val ◁ uGH) ≫
          (F.val ◁ (L.map (g.val ▷ H.val)).val) := by
    rw [← MonoidalCategory.whiskerLeft_comp,
      ← MonoidalCategory.whiskerLeft_comp]
    exact congrArg (fun k ↦ F.val ◁ k) huraw
  have hrightMap := congrArg L.map huraw'
  simp only [Functor.map_comp] at hrightMap
  change L.map (F.val ◁ (g.val ▷ H.val)) ≫ iFuG'H.hom =
    iFuGH.hom ≫
      L.map (F.val ◁ (L.map (g.val ▷ H.val)).val) at hrightMap
  calc
    L.map ((L.map fg).val ▷ H.val) ≫ iFG'H.inv ≫
          L.map (α_ F.val G'.val H.val).hom ≫ iFuG'H.hom =
        (iFGH.inv ≫ L.map (fg ▷ H.val)) ≫
          L.map (α_ F.val G'.val H.val).hom ≫ iFuG'H.hom :=
      congrArg (fun k ↦ k ≫ L.map (α_ F.val G'.val H.val).hom ≫
        iFuG'H.hom) hleft
    _ = iFGH.inv ≫
          (L.map (fg ▷ H.val) ≫
            L.map (α_ F.val G'.val H.val).hom) ≫ iFuG'H.hom := by
      simp only [Category.assoc]
    _ = iFGH.inv ≫
          (L.map (α_ F.val G.val H.val).hom ≫
            L.map (F.val ◁ (g.val ▷ H.val))) ≫ iFuG'H.hom :=
      congrArg (fun k ↦ iFGH.inv ≫ k ≫ iFuG'H.hom) hassoc
    _ = iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫
          (L.map (F.val ◁ (g.val ▷ H.val)) ≫ iFuG'H.hom) := by
      simp only [Category.assoc]
    _ = iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫
          (iFuGH.hom ≫
            L.map (F.val ◁ (L.map (g.val ▷ H.val)).val)) :=
      congrArg (fun k ↦ iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫ k)
        hrightMap
    _ = _ := rfl

set_option maxHeartbeats 1600000 in
/-- The tensor map for pushforward commutes with the chosen sheaf tensor
associators. -/
lemma pushforwardTensorHom_assoc (f : X ⟶ Y) (F G H : X.Modules) :
    tensorMapLeft (pushforwardTensorHom f F G) ((pushforward f).obj H) ≫
        pushforwardTensorHom f (tensor F G) H ≫
        (pushforward f).map (tensorAssocIso F G H).hom =
      (tensorAssocIso ((pushforward f).obj F) ((pushforward f).obj G)
          ((pushforward f).obj H)).hom ≫
        tensorMapRight ((pushforward f).obj F)
          (pushforwardTensorHom f G H) ≫
        pushforwardTensorHom f F (tensor G H) := by
  let LX := sheafification X
  let LY := sheafification Y
  let adjX := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let adjY := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)
  let pf := _root_.PresheafOfModules.pushforward
    f.toRingCatSheafHom.hom
  let PF := (pushforward f).obj F
  let PG := (pushforward f).obj G
  let PH := (pushforward f).obj H
  let uFG := adjY.unit.app (PF.val ⊗ PG.val)
  let uGH := adjY.unit.app (PG.val ⊗ PH.val)
  let W := tensorLocalEquivalences Y
  have hunitMem (A : Y.PresheafOfModules) : W (adjY.unit.app A) := by
    change (Opens.grothendieckTopology Y).W
      ((_root_.PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        (adjY.unit.app A))
    simpa [adjY] using
      (Opens.grothendieckTopology Y).W_toSheafify A.presheaf
  have huFGH : W (uFG ▷ PH.val) :=
    W.whiskerRight_mem uFG (hunitMem (PF.val ⊗ PG.val)) PH.val
  have hFuGH : W (PF.val ◁ uGH) :=
    W.whiskerLeft_mem PF.val uGH (hunitMem (PG.val ⊗ PH.val))
  let iFGH := Localization.isoOfHom LY W (uFG ▷ PH.val) huFGH
  let iFuGH := Localization.isoOfHom LY W (PF.val ◁ uGH) hFuGH
  let pFG := pushforwardPresheafTensorHom f F G
  let pGH := pushforwardPresheafTensorHom f G H
  let qFG := pushforwardTensorHom f F G
  let qGH := pushforwardTensorHom f G H
  let qFGH := pushforwardTensorHom f (tensor F G) H
  let qFuGH := pushforwardTensorHom f F (tensor G H)
  let pFGH := pushforwardPresheafTensorHom f (tensor F G) H
  let pFuGH := pushforwardPresheafTensorHom f F (tensor G H)
  let rFG := pFG ≫ pf.map (adjX.unit.app (F.val ⊗ G.val))
  let rGH := pGH ≫ pf.map (adjX.unit.app (G.val ⊗ H.val))
  let rFGH := pFGH ≫
    pf.map (adjX.unit.app ((tensor F G).val ⊗ H.val))
  let rFuGH := pFuGH ≫
    pf.map (adjX.unit.app (F.val ⊗ (tensor G H).val))
  have hqFG : uFG ≫ qFG.val = rFG := by
    have h := pushforwardTensorHom_homEquiv f F G
    rw [Adjunction.homEquiv_apply] at h
    change uFG ≫ qFG.val = rFG at h
    exact h
  have hqGH : uGH ≫ qGH.val = rGH := by
    have h := pushforwardTensorHom_homEquiv f G H
    rw [Adjunction.homEquiv_apply] at h
    change uGH ≫ qGH.val = rGH at h
    exact h
  have hleft :
      LY.map (uFG ▷ PH.val) ≫ LY.map (qFG.val ▷ PH.val) =
        LY.map (rFG ▷ PH.val) := by
    rw [← LY.map_comp, ← MonoidalCategory.comp_whiskerRight, hqFG]
  have hright :
      iFuGH.hom ≫ LY.map (PF.val ◁ qGH.val) =
        LY.map (PF.val ◁ rGH) := by
    change LY.map (PF.val ◁ uGH) ≫ LY.map (PF.val ◁ qGH.val) = _
    rw [← LY.map_comp, ← MonoidalCategory.whiskerLeft_comp, hqGH]
  rw [← cancel_epi iFGH.hom]
  change LY.map (uFG ▷ PH.val) ≫ LY.map (qFG.val ▷ PH.val) ≫
        qFGH ≫ (pushforward f).map (tensorAssocIso F G H).hom =
    iFGH.hom ≫ iFGH.inv ≫
      LY.map (α_ PF.val PG.val PH.val).hom ≫ iFuGH.hom ≫
      LY.map (PF.val ◁ qGH.val) ≫ qFuGH
  rw [iFGH.hom_inv_id_assoc]
  calc
    LY.map (uFG ▷ PH.val) ≫ LY.map (qFG.val ▷ PH.val) ≫
          qFGH ≫ (pushforward f).map (tensorAssocIso F G H).hom =
        LY.map (rFG ▷ PH.val) ≫ qFGH ≫
          (pushforward f).map (tensorAssocIso F G H).hom :=
      congrArg (fun k ↦ k ≫ qFGH ≫
        (pushforward f).map (tensorAssocIso F G H).hom) hleft
    _ = LY.map (α_ PF.val PG.val PH.val).hom ≫
          LY.map (PF.val ◁ rGH) ≫ qFuGH := by
      have hqFGH : adjY.unit.app (((pushforward f).obj (tensor F G)).val ⊗
            PH.val) ≫ qFGH.val = rFGH := by
        have h := pushforwardTensorHom_homEquiv f (tensor F G) H
        rw [Adjunction.homEquiv_apply] at h
        change adjY.unit.app (((pushforward f).obj (tensor F G)).val ⊗
            PH.val) ≫ qFGH.val = rFGH at h
        exact h
      have hqFuGH : adjY.unit.app (PF.val ⊗
            ((pushforward f).obj (tensor G H)).val) ≫ qFuGH.val = rFuGH := by
        have h := pushforwardTensorHom_homEquiv f F (tensor G H)
        rw [Adjunction.homEquiv_apply] at h
        change adjY.unit.app (PF.val ⊗
            ((pushforward f).obj (tensor G H)).val) ≫ qFuGH.val = rFuGH at h
        exact h
      have hraw :
          (rFG ▷ PH.val) ≫ rFGH ≫
              pf.map (tensorAssocIso F G H).hom.val =
            (α_ PF.val PG.val PH.val).hom ≫
              (PF.val ◁ rGH) ≫ rFuGH := by
        apply _root_.PresheafOfModules.hom_ext
        intro U
        apply ModuleCat.MonoidalCategory.tensor_ext₃'
        intro x y z
        let V : (Opens X)ᵒᵖ := .op (f ⁻¹ᵁ U.unop)
        have hs := congrArg
          (fun k ↦ (k.app V).hom
            ((x ⊗ₜ[(((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj V) : RingCat)] y) ⊗ₜ z))
          (tensorAssocIso_unit F G H)
        change
          ((tensorAssocIso F G H).hom.val.app V).hom
              (((adjX.unit.app ((tensor F G).val ⊗ H.val)).app V).hom
                ((((adjX.unit.app (F.val ⊗ G.val)) ▷ H.val).app V).hom
                  ((x ⊗ₜ[(((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj V) : RingCat)] y) ⊗ₜ z))) =
            ((adjX.unit.app (F.val ⊗ (tensor G H).val)).app V).hom
              (((F.val ◁ adjX.unit.app (G.val ⊗ H.val)).app V).hom
                (((α_ F.val G.val H.val).hom.app V).hom
                  ((x ⊗ₜ[(((X.presheaf ⋙ forget₂ CommRingCat RingCat).obj V) : RingCat)] y) ⊗ₜ z)))
        exact hs
      apply (adjY.homEquiv _ _).injective
      rw [Adjunction.homEquiv_apply, Adjunction.homEquiv_apply]
      change adjY.unit.app ((PF.val ⊗ PG.val) ⊗ PH.val) ≫
          (LY.map (rFG ▷ PH.val)).val ≫ qFGH.val ≫
          ((pushforward f).map (tensorAssocIso F G H).hom).val =
        adjY.unit.app ((PF.val ⊗ PG.val) ⊗ PH.val) ≫
          (LY.map (α_ PF.val PG.val PH.val).hom).val ≫
          (LY.map (PF.val ◁ rGH)).val ≫ qFuGH.val
      have huLeft := adjY.unit.naturality (rFG ▷ PH.val)
      have huAssoc := adjY.unit.naturality
        (α_ PF.val PG.val PH.val).hom
      have huRight := adjY.unit.naturality (PF.val ◁ rGH)
      change (rFG ▷ PH.val) ≫
          adjY.unit.app (((pushforward f).obj (tensor F G)).val ⊗ PH.val) =
        adjY.unit.app ((PF.val ⊗ PG.val) ⊗ PH.val) ≫
          (LY.map (rFG ▷ PH.val)).val at huLeft
      change (α_ PF.val PG.val PH.val).hom ≫
          adjY.unit.app (PF.val ⊗ (PG.val ⊗ PH.val)) =
        adjY.unit.app ((PF.val ⊗ PG.val) ⊗ PH.val) ≫
          (LY.map (α_ PF.val PG.val PH.val).hom).val at huAssoc
      change (PF.val ◁ rGH) ≫
          adjY.unit.app (PF.val ⊗
            ((pushforward f).obj (tensor G H)).val) =
        adjY.unit.app (PF.val ⊗ (PG.val ⊗ PH.val)) ≫
          (LY.map (PF.val ◁ rGH)).val at huRight
      calc
        adjY.unit.app ((PF.val ⊗ PG.val) ⊗ PH.val) ≫
              (LY.map (rFG ▷ PH.val)).val ≫ qFGH.val ≫
              ((pushforward f).map (tensorAssocIso F G H).hom).val =
            ((rFG ▷ PH.val) ≫
              adjY.unit.app (((pushforward f).obj (tensor F G)).val ⊗
                PH.val)) ≫ qFGH.val ≫
              ((pushforward f).map (tensorAssocIso F G H).hom).val :=
          congrArg (fun k ↦ k ≫ qFGH.val ≫
            ((pushforward f).map (tensorAssocIso F G H).hom).val)
            huLeft.symm
        _ = (rFG ▷ PH.val) ≫ rFGH ≫
              pf.map (tensorAssocIso F G H).hom.val := by
          change (rFG ▷ PH.val) ≫
              adjY.unit.app (((pushforward f).obj (tensor F G)).val ⊗
                PH.val) ≫ qFGH.val ≫
              pf.map (tensorAssocIso F G H).hom.val = _
          simpa only [Category.assoc] using congrArg
            (fun k ↦ (rFG ▷ PH.val) ≫ k ≫
              pf.map (tensorAssocIso F G H).hom.val) hqFGH
        _ = (α_ PF.val PG.val PH.val).hom ≫
              (PF.val ◁ rGH) ≫ rFuGH := hraw
        _ = (α_ PF.val PG.val PH.val).hom ≫
              (PF.val ◁ rGH) ≫
              adjY.unit.app (PF.val ⊗
                ((pushforward f).obj (tensor G H)).val) ≫ qFuGH.val := by
          simpa only [Category.assoc] using congrArg
            (fun k ↦ (α_ PF.val PG.val PH.val).hom ≫
              (PF.val ◁ rGH) ≫ k) hqFuGH.symm
        _ = (α_ PF.val PG.val PH.val).hom ≫
              adjY.unit.app (PF.val ⊗ (PG.val ⊗ PH.val)) ≫
              (LY.map (PF.val ◁ rGH)).val ≫ qFuGH.val :=
          congrArg (fun k ↦ (α_ PF.val PG.val PH.val).hom ≫
            k ≫ qFuGH.val) huRight
        _ = adjY.unit.app ((PF.val ⊗ PG.val) ⊗ PH.val) ≫
              (LY.map (α_ PF.val PG.val PH.val).hom).val ≫
              (LY.map (PF.val ◁ rGH)).val ≫ qFuGH.val :=
          congrArg (fun k ↦ k ≫
            (LY.map (PF.val ◁ rGH)).val ≫ qFuGH.val) huAssoc
    _ = LY.map (α_ PF.val PG.val PH.val).hom ≫ iFuGH.hom ≫
          LY.map (PF.val ◁ qGH.val) ≫ qFuGH := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ LY.map (α_ PF.val PG.val PH.val).hom ≫ k ≫ qFuGH)
        hright.symm

set_option maxHeartbeats 1600000 in
/-- The canonical pullback--tensor comparison commutes with the chosen sheaf
tensor associators. -/
lemma pullbackTensorComparison_assoc (f : X ⟶ Y) (F G H : Y.Modules) :
    pullbackTensorComparison f (tensor F G) H ≫
        tensorMapLeft (pullbackTensorComparison f F G) ((pullback f).obj H) ≫
        (tensorAssocIso ((pullback f).obj F) ((pullback f).obj G)
          ((pullback f).obj H)).hom =
      (pullback f).map (tensorAssocIso F G H).hom ≫
        pullbackTensorComparison f F (tensor G H) ≫
        tensorMapRight ((pullback f).obj F)
          (pullbackTensorComparison f G H) := by
  let adj := pullbackPushforwardAdjunction f
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  dsimp only [pullbackTensorComparison, adj]
  simp only [Equiv.apply_symm_apply]
  let PF := (pullback f).obj F
  let PG := (pullback f).obj G
  let PH := (pullback f).obj H
  let PFG := (pullback f).obj (tensor F G)
  let PGH := (pullback f).obj (tensor G H)
  let QPF := (pushforward f).obj PF
  let QPG := (pushforward f).obj PG
  let QPH := (pushforward f).obj PH
  let QPFG := (pushforward f).obj PFG
  let QPGH := (pushforward f).obj PGH
  let ηF : F ⟶ QPF := (pullbackPushforwardAdjunction f).unit.app F
  let ηG : G ⟶ QPG := (pullbackPushforwardAdjunction f).unit.app G
  let ηH : H ⟶ QPH := (pullbackPushforwardAdjunction f).unit.app H
  let ηFG : tensor F G ⟶ QPFG :=
    (pullbackPushforwardAdjunction f).unit.app (tensor F G)
  let ηGH : tensor G H ⟶ QPGH :=
    (pullbackPushforwardAdjunction f).unit.app (tensor G H)
  let cFG := pullbackTensorComparison f F G
  let cGH := pullbackTensorComparison f G H
  let mFG := pushforwardTensorHom f PF PG
  let mGH := pushforwardTensorHom f PG PH
  let mPFGH := pushforwardTensorHom f PFG PH
  let mFPGH := pushforwardTensorHom f PF PGH
  let mTensorFGH := pushforwardTensorHom f (tensor PF PG) PH
  let mFTensorGH := pushforwardTensorHom f PF (tensor PG PH)
  let aY := (tensorAssocIso F G H).hom
  let aP := (tensorAssocIso PF PG PH).hom
  let aQ := (tensorAssocIso QPF QPG QPH).hom
  let qFG := tensorMapLeft ηF G ≫ tensorMapRight QPF ηG ≫ mFG
  let qGH := tensorMapLeft ηG H ≫ tensorMapRight QPG ηH ≫ mGH
  let qPFGH := tensorMapLeft ηFG H ≫
    tensorMapRight QPFG ηH ≫ mPFGH
  let qFPGH := tensorMapLeft ηF (tensor G H) ≫
    tensorMapRight QPF ηGH ≫ mFPGH
  change qPFGH ≫
      (pushforward f).map (tensorMapLeft cFG PH ≫ aP) =
    aY ≫ qFPGH ≫
      (pushforward f).map (tensorMapRight PF cGH)
  have hcFG : ηFG ≫ (pushforward f).map cFG = qFG := by
    dsimp only [ηFG, cFG, qFG, pullbackTensorComparison]
    calc
      (pullbackPushforwardAdjunction f).unit.app (tensor F G) ≫
            (pushforward f).map
              (((pullbackPushforwardAdjunction f).homEquiv _ _).symm _) =
          (pullbackPushforwardAdjunction f).homEquiv _ _
            (((pullbackPushforwardAdjunction f).homEquiv _ _).symm _) :=
        ((pullbackPushforwardAdjunction f).homEquiv_apply _ _ _).symm
      _ = _ := Equiv.apply_symm_apply _ _
  have hcGH : ηGH ≫ (pushforward f).map cGH = qGH := by
    dsimp only [ηGH, cGH, qGH, pullbackTensorComparison]
    calc
      (pullbackPushforwardAdjunction f).unit.app (tensor G H) ≫
            (pushforward f).map
              (((pullbackPushforwardAdjunction f).homEquiv _ _).symm _) =
          (pullbackPushforwardAdjunction f).homEquiv _ _
            (((pullbackPushforwardAdjunction f).homEquiv _ _).symm _) :=
        ((pullbackPushforwardAdjunction f).homEquiv_apply _ _ _).symm
      _ = _ := Equiv.apply_symm_apply _ _
  have hcGHexpanded :
      tensorMapLeft ηG H ≫ tensorMapRight QPG ηH ≫ mGH =
        ηGH ≫ (pushforward f).map cGH := by
    exact hcGH.symm
  have hnatFG :
      tensorMapLeft ((pushforward f).map cFG) QPH ≫ mTensorFGH =
        mPFGH ≫ (pushforward f).map (tensorMapLeft cFG PH) := by
    dsimp only [cFG, QPH, mTensorFGH, mPFGH, PFG, PF, PG, PH]
    exact pushforwardTensorHom_naturality_left f
      (pullbackTensorComparison f F G) ((pullback f).obj H)
  have hnatGH :
      tensorMapRight QPF ((pushforward f).map cGH) ≫ mFTensorGH =
        mFPGH ≫ (pushforward f).map (tensorMapRight PF cGH) := by
    dsimp only [cGH, QPF, mFTensorGH, mFPGH, PGH, PF, PG, PH]
    exact pushforwardTensorHom_naturality_right f
      ((pullback f).obj F) (pullbackTensorComparison f G H)
  have hη :
      tensorMapLeft (tensorMapLeft ηF G) H ≫
          tensorMapLeft (tensorMapRight QPF ηG) H ≫
          tensorMapRight (tensor QPF QPG) ηH ≫ aQ =
        aY ≫ tensorMapLeft ηF (tensor G H) ≫
          tensorMapRight QPF (tensorMapLeft ηG H) ≫
          tensorMapRight QPF (tensorMapRight QPG ηH) := by
    have hr := tensorAssocIso_hom_naturality_right QPF QPG ηH
    have hm := tensorAssocIso_hom_naturality_middle QPF ηG H
    have hl := tensorAssocIso_hom_naturality_left ηF G H
    change tensorMapRight (tensor QPF QPG) ηH ≫
        (tensorAssocIso QPF QPG QPH).hom =
      (tensorAssocIso QPF QPG H).hom ≫
        tensorMapRight QPF (tensorMapRight QPG ηH) at hr
    change tensorMapLeft (tensorMapRight QPF ηG) H ≫
        (tensorAssocIso QPF QPG H).hom =
      (tensorAssocIso QPF G H).hom ≫
        tensorMapRight QPF (tensorMapLeft ηG H) at hm
    change tensorMapLeft (tensorMapLeft ηF G) H ≫
        (tensorAssocIso QPF G H).hom =
      (tensorAssocIso F G H).hom ≫
        tensorMapLeft ηF (tensor G H) at hl
    dsimp only [aQ, aY] at ⊢
    calc
      tensorMapLeft (tensorMapLeft ηF G) H ≫
            tensorMapLeft (tensorMapRight QPF ηG) H ≫
            tensorMapRight (tensor QPF QPG) ηH ≫
            (tensorAssocIso QPF QPG QPH).hom =
          tensorMapLeft (tensorMapLeft ηF G) H ≫
            tensorMapLeft (tensorMapRight QPF ηG) H ≫
            (tensorAssocIso QPF QPG H).hom ≫
            tensorMapRight QPF (tensorMapRight QPG ηH) := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ tensorMapLeft (tensorMapLeft ηF G) H ≫
            tensorMapLeft (tensorMapRight QPF ηG) H ≫ k) hr
      _ = tensorMapLeft (tensorMapLeft ηF G) H ≫
            (tensorAssocIso QPF G H).hom ≫
            tensorMapRight QPF (tensorMapLeft ηG H) ≫
            tensorMapRight QPF (tensorMapRight QPG ηH) := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ tensorMapLeft (tensorMapLeft ηF G) H ≫ k ≫
            tensorMapRight QPF (tensorMapRight QPG ηH)) hm
      _ = (tensorAssocIso F G H).hom ≫
            tensorMapLeft ηF (tensor G H) ≫
            tensorMapRight QPF (tensorMapLeft ηG H) ≫
            tensorMapRight QPF (tensorMapRight QPG ηH) := by
        simpa only [Category.assoc] using congrArg
          (fun k ↦ k ≫ tensorMapRight QPF (tensorMapLeft ηG H) ≫
            tensorMapRight QPF (tensorMapRight QPG ηH)) hl
  have hassoc := pushforwardTensorHom_assoc f PF PG PH
  dsimp only [mFG, mGH, mTensorFGH, mFTensorGH, aP, aQ,
    PF, PG, PH, QPF, QPG, QPH] at hassoc
  calc
    qPFGH ≫ (pushforward f).map (tensorMapLeft cFG PH ≫ aP) =
        tensorMapLeft (tensorMapLeft ηF G) H ≫
          tensorMapLeft (tensorMapRight QPF ηG) H ≫
          tensorMapRight (tensor QPF QPG) ηH ≫
          tensorMapLeft mFG QPH ≫
          mTensorFGH ≫ (pushforward f).map aP := by
      dsimp only [qPFGH, qFG]
      rw [(pushforward f).map_comp]
      simp only [Category.assoc]
      slice_lhs 3 4 => rw [← hnatFG]
      slice_lhs 2 3 => rw [tensorMap_exchange]
      slice_lhs 1 2 => rw [← tensorMapLeft_comp, hcFG]
      rw [tensorMapLeft_comp, tensorMapLeft_comp]
      slice_lhs 3 4 => rw [← tensorMap_exchange]
      simp only [Category.assoc]
    _ = tensorMapLeft (tensorMapLeft ηF G) H ≫
          tensorMapLeft (tensorMapRight QPF ηG) H ≫
          tensorMapRight (tensor QPF QPG) ηH ≫ aQ ≫
          tensorMapRight QPF mGH ≫ mFTensorGH := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ tensorMapLeft (tensorMapLeft ηF G) H ≫
          tensorMapLeft (tensorMapRight QPF ηG) H ≫
          tensorMapRight (tensor QPF QPG) ηH ≫ k) hassoc
    _ = aY ≫ tensorMapLeft ηF (tensor G H) ≫
          tensorMapRight QPF (tensorMapLeft ηG H) ≫
          tensorMapRight QPF (tensorMapRight QPG ηH) ≫
          tensorMapRight QPF mGH ≫ mFTensorGH := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ tensorMapRight QPF mGH ≫ mFTensorGH) hη
    _ = aY ≫ qFPGH ≫
          (pushforward f).map (tensorMapRight PF cGH) := by
      dsimp only [qFPGH, qGH]
      simp only [Category.assoc]
      slice_lhs 4 5 => rw [← tensorMapRight_comp]
      slice_lhs 3 4 => rw [← tensorMapRight_comp]
      rw [hcGHexpanded, tensorMapRight_comp]
      slice_lhs 4 5 => rw [hnatGH]

set_option maxHeartbeats 1600000 in
-- The calculation transports a complete dual-pair triangle through every oplax
-- comparison, using associativity once and the two unit coherences at the ends.
/-- Pullback transports a left triangle identity when the comparison for the
paired objects is invertible. -/
lemma pullback_pairing_left_triangle
    (f : X ⟶ Y) (N D : Y.Modules)
    (coev : SheafOfModules.unit Y.ringCatSheaf ⟶ tensor N D)
    (ev : tensor D N ⟶ SheafOfModules.unit Y.ringCatSheaf)
    [IsIso (SheafOfModules.pullbackObjUnitToUnit
      f.toRingCatSheafHom)]
    [IsIso (pullbackTensorComparison f N D)]
    [IsIso (pullbackTensorComparison f D N)]
    (htriangle :
      (tensorLeftUnitIso N).inv ≫ tensorMapLeft coev N ≫
          (tensorAssocIso N D N).hom ≫ tensorMapRight N ev ≫
          (tensorUnitIso N).hom = 𝟙 N) :
    let u := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
    let PN := (pullback f).obj N
    let PD := (pullback f).obj D
    let coevX := inv u ≫ (pullback f).map coev ≫
      pullbackTensorComparison f N D
    let evX := inv (pullbackTensorComparison f D N) ≫
      (pullback f).map ev ≫ u
    (tensorLeftUnitIso PN).inv ≫ tensorMapLeft coevX PN ≫
        (tensorAssocIso PN PD PN).hom ≫ tensorMapRight PN evX ≫
        (tensorUnitIso PN).hom = 𝟙 PN := by
  dsimp only
  let UY := SheafOfModules.unit Y.ringCatSheaf
  let PN := (pullback f).obj N
  let PD := (pullback f).obj D
  let PU := (pullback f).obj UY
  let u : PU ⟶ SheafOfModules.unit X.ringCatSheaf :=
    SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom
  let cUN := pullbackTensorComparison f UY N
  let cNU := pullbackTensorComparison f N UY
  let cND := pullbackTensorComparison f N D
  let cDN := pullbackTensorComparison f D N
  let cNDN := pullbackTensorComparison f (tensor N D) N
  let cNDN' := pullbackTensorComparison f N (tensor D N)
  let p := pullback f
  letI : IsIso cNU := by
    dsimp only [cNU, UY]
    exact pullbackTensorComparison_isIso_unit f N
  letI : IsIso cUN := by
    dsimp only [cUN, cNU, UY]
    exact pullbackTensorComparison_isIso_swap f N UY
  have hleftUnit := pullbackTensorComparison_comp_leftUnit f N
  change cUN ≫ tensorMapLeft u PN ≫ (tensorLeftUnitIso PN).hom =
    p.map (tensorLeftUnitIso N).hom at hleftUnit
  have hleftUnitInv :
      (tensorLeftUnitIso PN).inv ≫ tensorMapLeft (inv u) PN ≫ inv cUN =
        p.map (tensorLeftUnitIso N).inv := by
    have huTensor :
        tensorMapLeft (inv u) PN ≫ tensorMapLeft u PN = 𝟙 _ := by
      have hu : inv u ≫ u = 𝟙 _ := by simp
      calc
        tensorMapLeft (inv u) PN ≫ tensorMapLeft u PN =
            tensorMapLeft (inv u ≫ u) PN :=
          (tensorMapLeft_comp (inv u) u PN).symm
        _ = tensorMapLeft (𝟙 (SheafOfModules.unit X.ringCatSheaf)) PN :=
          congrArg (fun k ↦ tensorMapLeft k PN) hu
        _ = 𝟙 _ := tensorMapLeft_id _ PN
    apply (cancel_mono (p.map (tensorLeftUnitIso N).hom)).1
    calc
      (tensorLeftUnitIso PN).inv ≫ tensorMapLeft (inv u) PN ≫ inv cUN ≫
            p.map (tensorLeftUnitIso N).hom =
          (tensorLeftUnitIso PN).inv ≫ tensorMapLeft (inv u) PN ≫ inv cUN ≫
            (cUN ≫ tensorMapLeft u PN ≫ (tensorLeftUnitIso PN).hom) :=
        congrArg
          (fun k ↦ (tensorLeftUnitIso PN).inv ≫
            tensorMapLeft (inv u) PN ≫ inv cUN ≫ k)
          hleftUnit.symm
      _ = 𝟙 PN := by
        rw [IsIso.inv_hom_id_assoc]
        calc
          (tensorLeftUnitIso PN).inv ≫ tensorMapLeft (inv u) PN ≫
                tensorMapLeft u PN ≫ (tensorLeftUnitIso PN).hom =
              (tensorLeftUnitIso PN).inv ≫
                (tensorMapLeft (inv u) PN ≫ tensorMapLeft u PN) ≫
                (tensorLeftUnitIso PN).hom := by
            simp only [Category.assoc]
          _ = (tensorLeftUnitIso PN).inv ≫ 𝟙 _ ≫
                (tensorLeftUnitIso PN).hom :=
            congrArg
              (fun k ↦ (tensorLeftUnitIso PN).inv ≫ k ≫
                (tensorLeftUnitIso PN).hom) huTensor
          _ = 𝟙 PN := by simp
      _ = p.map (tensorLeftUnitIso N).inv ≫
            p.map (tensorLeftUnitIso N).hom := by
        rw [← p.map_comp, Iso.inv_hom_id, p.map_id]
  have hcoev := pullbackTensorComparison_naturality_left f coev N
  change p.map (tensorMapLeft coev N) ≫ cNDN =
    cUN ≫ tensorMapLeft (p.map coev) PN at hcoev
  have hassoc := pullbackTensorComparison_assoc f N D N
  change cNDN ≫ tensorMapLeft cND PN ≫
      (tensorAssocIso PN PD PN).hom =
    p.map (tensorAssocIso N D N).hom ≫ cNDN' ≫
      tensorMapRight PN cDN at hassoc
  have hev := pullbackTensorComparison_naturality_right f N ev
  change p.map (tensorMapRight N ev) ≫ cNU =
    cNDN' ≫ tensorMapRight PN (p.map ev) at hev
  have hrightUnit := pullbackTensorComparison_comp_unit f N
  change cNU ≫ tensorMapRight PN u ≫ (tensorUnitIso PN).hom =
    p.map (tensorUnitIso N).hom at hrightUnit
  have hcoevExpand :
      tensorMapLeft (inv u ≫ p.map coev ≫ cND) PN =
        tensorMapLeft (inv u) PN ≫ tensorMapLeft (p.map coev) PN ≫
          tensorMapLeft cND PN := by
    rw [tensorMapLeft_comp, tensorMapLeft_comp]
  have hevExpand :
      tensorMapRight PN (inv cDN ≫ p.map ev ≫ u) =
        tensorMapRight PN (inv cDN) ≫ tensorMapRight PN (p.map ev) ≫
          tensorMapRight PN u := by
    rw [tensorMapRight_comp, tensorMapRight_comp]
  have hcDNcancel :
      tensorMapRight PN cDN ≫ tensorMapRight PN (inv cDN) = 𝟙 _ := by
    have hcDN : cDN ≫ inv cDN = 𝟙 _ := by simp
    calc
      tensorMapRight PN cDN ≫ tensorMapRight PN (inv cDN) =
          tensorMapRight PN (cDN ≫ inv cDN) :=
        (tensorMapRight_comp PN cDN (inv cDN)).symm
      _ = tensorMapRight PN (𝟙 _) :=
        congrArg (fun k ↦ tensorMapRight PN k) hcDN
      _ = 𝟙 _ := tensorMapRight_id PN _
  calc
    (tensorLeftUnitIso PN).inv ≫
          tensorMapLeft (inv u ≫ p.map coev ≫ cND) PN ≫
          (tensorAssocIso PN PD PN).hom ≫
          tensorMapRight PN (inv cDN ≫ p.map ev ≫ u) ≫
          (tensorUnitIso PN).hom =
        (tensorLeftUnitIso PN).inv ≫ tensorMapLeft (inv u) PN ≫
          tensorMapLeft (p.map coev) PN ≫ tensorMapLeft cND PN ≫
          (tensorAssocIso PN PD PN).hom ≫
          tensorMapRight PN (inv cDN ≫ p.map ev ≫ u) ≫
          (tensorUnitIso PN).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (tensorLeftUnitIso PN).inv ≫ k ≫
          (tensorAssocIso PN PD PN).hom ≫
          tensorMapRight PN (inv cDN ≫ p.map ev ≫ u) ≫
          (tensorUnitIso PN).hom) hcoevExpand
    _ = (tensorLeftUnitIso PN).inv ≫ tensorMapLeft (inv u) PN ≫
          tensorMapLeft (p.map coev) PN ≫ tensorMapLeft cND PN ≫
          (tensorAssocIso PN PD PN).hom ≫ tensorMapRight PN (inv cDN) ≫
          tensorMapRight PN (p.map ev) ≫ tensorMapRight PN u ≫
          (tensorUnitIso PN).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (tensorLeftUnitIso PN).inv ≫
          tensorMapLeft (inv u) PN ≫ tensorMapLeft (p.map coev) PN ≫
          tensorMapLeft cND PN ≫ (tensorAssocIso PN PD PN).hom ≫ k ≫
          (tensorUnitIso PN).hom) hevExpand
    _ =
        (tensorLeftUnitIso PN).inv ≫ tensorMapLeft (inv u) PN ≫ inv cUN ≫
          cUN ≫ tensorMapLeft (p.map coev) PN ≫ tensorMapLeft cND PN ≫
          (tensorAssocIso PN PD PN).hom ≫ tensorMapRight PN (inv cDN) ≫
          tensorMapRight PN (p.map ev) ≫ tensorMapRight PN u ≫
          (tensorUnitIso PN).hom := by
      simp only [Category.assoc, IsIso.inv_hom_id_assoc]
    _ = p.map (tensorLeftUnitIso N).inv ≫
          cUN ≫ tensorMapLeft (p.map coev) PN ≫ tensorMapLeft cND PN ≫
          (tensorAssocIso PN PD PN).hom ≫ tensorMapRight PN (inv cDN) ≫
          tensorMapRight PN (p.map ev) ≫ tensorMapRight PN u ≫
          (tensorUnitIso PN).hom := by
      slice_lhs 1 3 => rw [hleftUnitInv]
      simp only [Category.assoc]
    _ = p.map (tensorLeftUnitIso N).inv ≫
          p.map (tensorMapLeft coev N) ≫ cNDN ≫ tensorMapLeft cND PN ≫
          (tensorAssocIso PN PD PN).hom ≫ tensorMapRight PN (inv cDN) ≫
          tensorMapRight PN (p.map ev) ≫ tensorMapRight PN u ≫
          (tensorUnitIso PN).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ p.map (tensorLeftUnitIso N).inv ≫ k ≫
          tensorMapLeft cND PN ≫ (tensorAssocIso PN PD PN).hom ≫
          tensorMapRight PN (inv cDN) ≫ tensorMapRight PN (p.map ev) ≫
          tensorMapRight PN u ≫ (tensorUnitIso PN).hom) hcoev.symm
    _ = p.map (tensorLeftUnitIso N).inv ≫
          p.map (tensorMapLeft coev N) ≫ p.map (tensorAssocIso N D N).hom ≫
          cNDN' ≫ tensorMapRight PN cDN ≫ tensorMapRight PN (inv cDN) ≫
          tensorMapRight PN (p.map ev) ≫ tensorMapRight PN u ≫
          (tensorUnitIso PN).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ p.map (tensorLeftUnitIso N).inv ≫
          p.map (tensorMapLeft coev N) ≫ k ≫
          tensorMapRight PN (inv cDN) ≫ tensorMapRight PN (p.map ev) ≫
          tensorMapRight PN u ≫ (tensorUnitIso PN).hom) hassoc
    _ = p.map (tensorLeftUnitIso N).inv ≫
          p.map (tensorMapLeft coev N) ≫ p.map (tensorAssocIso N D N).hom ≫
          cNDN' ≫ tensorMapRight PN (p.map ev) ≫ tensorMapRight PN u ≫
          (tensorUnitIso PN).hom := by
      slice_lhs 5 6 => rw [hcDNcancel]
      slice_lhs 4 5 => rw [Category.comp_id]
      simp only [Category.assoc]
    _ = p.map (tensorLeftUnitIso N).inv ≫
          p.map (tensorMapLeft coev N) ≫ p.map (tensorAssocIso N D N).hom ≫
          p.map (tensorMapRight N ev) ≫ cNU ≫ tensorMapRight PN u ≫
          (tensorUnitIso PN).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ p.map (tensorLeftUnitIso N).inv ≫
          p.map (tensorMapLeft coev N) ≫ p.map (tensorAssocIso N D N).hom ≫
          k ≫ tensorMapRight PN u ≫ (tensorUnitIso PN).hom) hev.symm
    _ = p.map (tensorLeftUnitIso N).inv ≫
          p.map (tensorMapLeft coev N) ≫ p.map (tensorAssocIso N D N).hom ≫
          p.map (tensorMapRight N ev) ≫ p.map (tensorUnitIso N).hom := by
      exact congrArg
        (fun k ↦ p.map (tensorLeftUnitIso N).inv ≫
          p.map (tensorMapLeft coev N) ≫ p.map (tensorAssocIso N D N).hom ≫
          p.map (tensorMapRight N ev) ≫ k) hrightUnit
    _ = p.map ((tensorLeftUnitIso N).inv ≫ tensorMapLeft coev N ≫
          (tensorAssocIso N D N).hom ≫ tensorMapRight N ev ≫
          (tensorUnitIso N).hom) := by
      rw [p.map_comp, p.map_comp, p.map_comp, p.map_comp]
    _ = p.map (𝟙 N) := congrArg p.map htriangle
    _ = 𝟙 PN := p.map_id N

end AlgebraicGeometry.Scheme.Modules

end

end
