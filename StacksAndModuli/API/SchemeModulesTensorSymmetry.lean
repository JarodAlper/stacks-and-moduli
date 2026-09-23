module

public import StacksAndModuli.API.SchemeModulesTensor

/-!
# Symmetry and a chosen associator for tensor products of module sheaves

The sheaf tensor product is obtained by sheafifying the presheaf tensor product.  The
presheaf braiding therefore maps directly to an isomorphism of sheaf tensors.  Associativity
is available as `Modules.nonempty_tensorAssoc`; this file chooses one such isomorphism for
constructions which only need a fixed comparison.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

abbrev tensorLocalEquivalences (X : Scheme.{u}) :
    MorphismProperty X.PresheafOfModules :=
  (Opens.grothendieckTopology X).W.inverseImage
    (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)

noncomputable instance tensorLocalEquivalences_isMonoidal (X : Scheme.{u}) :
    (tensorLocalEquivalences X).IsMonoidal := by
  exact _root_.PresheafOfModules.localEquivalencesIsMonoidal X.presheaf

noncomputable instance sheafification_isLocalization_tensorLocalEquivalences
    (X : Scheme.{u}) :
    (sheafification X).IsLocalization (tensorLocalEquivalences X) :=
  inferInstanceAs ((_root_.PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).IsLocalization
      ((Opens.grothendieckTopology X).W.inverseImage
        (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)))

-- Restate the presheaf braiding at the scheme-specific spelling, as for
-- `instMonoidalPresheafOfModules`.
noncomputable local instance instBraidedPresheafOfModules (X : Scheme.{u}) :
    BraidedCategory X.PresheafOfModules :=
  inferInstanceAs (BraidedCategory
    (_root_.PresheafOfModules.{u}
      (X.presheaf ⋙ forget₂ CommRingCat RingCat)))

/-- Symmetry of the tensor product of module sheaves, induced by the braiding of module
presheaves. -/
noncomputable def tensorCommIso (F G : X.Modules) :
    tensor F G ≅ tensor G F :=
  (sheafification X).mapIso (β_ F.val G.val)

/-- Naturality of tensor symmetry in the left variable. -/
@[reassoc]
theorem tensorCommIso_hom_naturality_left
    {F F' : X.Modules} (f : F ⟶ F') (G : X.Modules) :
    tensorMapLeft f G ≫ (tensorCommIso F' G).hom =
      (tensorCommIso F G).hom ≫ tensorMapRight G f := by
  dsimp only [tensorMapLeft, tensorMapRight, tensorCommIso, Functor.mapIso_hom]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (sheafification X).map
    (BraidedCategory.braiding_naturality_left f.val G.val)

/-- Naturality of tensor symmetry in the right variable. -/
@[reassoc]
theorem tensorCommIso_hom_naturality_right
    (F : X.Modules) {G G' : X.Modules} (g : G ⟶ G') :
    tensorMapRight F g ≫ (tensorCommIso F G').hom =
      (tensorCommIso F G).hom ≫ tensorMapLeft g F := by
  dsimp only [tensorMapLeft, tensorMapRight, tensorCommIso, Functor.mapIso_hom]
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (sheafification X).map
    (BraidedCategory.braiding_naturality_right F.val g.val)

/-- The associativity isomorphism for the tensor product of module sheaves, written as
the localization zig-zag through the presheaf associator. -/
noncomputable def tensorAssocIso (F G H : X.Modules) :
    tensor (tensor F G) H ≅ tensor F (tensor G H) :=
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let W := tensorLocalEquivalences X
  let uFG := adj.unit.app (F.val ⊗ G.val)
  let uGH := adj.unit.app (G.val ⊗ H.val)
  let huFG : W uFG := by
    change (Opens.grothendieckTopology X).W
      ((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map uFG)
    simpa [uFG, adj] using
      (Opens.grothendieckTopology X).W_toSheafify
        (MonoidalCategoryStruct.tensorObj
          (C := X.PresheafOfModules) F.val G.val).presheaf
  let huGH : W uGH := by
    change (Opens.grothendieckTopology X).W
      ((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map uGH)
    simpa [uGH, adj] using
      (Opens.grothendieckTopology X).W_toSheafify
        (MonoidalCategoryStruct.tensorObj
          (C := X.PresheafOfModules) G.val H.val).presheaf
  let huFGH : W (uFG ▷ H.val) :=
    W.whiskerRight_mem uFG huFG H.val
  let hFuGH : W (F.val ◁ uGH) :=
    W.whiskerLeft_mem F.val uGH huGH
  (Localization.isoOfHom (sheafification X) W
      (uFG ▷ H.val) huFGH).symm ≪≫
    (sheafification X).mapIso (α_ F.val G.val H.val) ≪≫
    Localization.isoOfHom (sheafification X) W
      (F.val ◁ uGH) hFuGH

/-- Naturality of the sheaf tensor associator in its left variable. -/
@[reassoc]
theorem tensorAssocIso_hom_naturality_left
    {F F' : X.Modules} (f : F ⟶ F') (G H : X.Modules) :
    tensorMapLeft (tensorMapLeft f G) H ≫ (tensorAssocIso F' G H).hom =
      (tensorAssocIso F G H).hom ≫ tensorMapLeft f (tensor G H) := by
  let L := sheafification X
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let W := tensorLocalEquivalences X
  let fg := f.val ▷ G.val
  let uFG := adj.unit.app (F.val ⊗ G.val)
  let uF'G := adj.unit.app (F'.val ⊗ G.val)
  let uGH := adj.unit.app (G.val ⊗ H.val)
  have hunitMem (A : X.PresheafOfModules) : W (adj.unit.app A) := by
    change (Opens.grothendieckTopology X).W
      ((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (adj.unit.app A))
    simpa [adj] using
      (Opens.grothendieckTopology X).W_toSheafify A.presheaf
  have huFGH : W (uFG ▷ H.val) :=
    W.whiskerRight_mem uFG (hunitMem (F.val ⊗ G.val)) H.val
  have huF'GH : W (uF'G ▷ H.val) :=
    W.whiskerRight_mem uF'G (hunitMem (F'.val ⊗ G.val)) H.val
  have hFuGH : W (F.val ◁ uGH) :=
    W.whiskerLeft_mem F.val uGH (hunitMem (G.val ⊗ H.val))
  have hF'uGH : W (F'.val ◁ uGH) :=
    W.whiskerLeft_mem F'.val uGH (hunitMem (G.val ⊗ H.val))
  let iFGH := Localization.isoOfHom L W (uFG ▷ H.val) huFGH
  let iF'GH := Localization.isoOfHom L W (uF'G ▷ H.val) huF'GH
  let iFuGH := Localization.isoOfHom L W (F.val ◁ uGH) hFuGH
  let iF'uGH := Localization.isoOfHom L W (F'.val ◁ uGH) hF'uGH
  have hunit :
      (fg ▷ H.val) ≫ (uF'G ▷ H.val) =
        (uFG ▷ H.val) ≫ (((L.map fg).val) ▷ H.val) := by
    rw [← MonoidalCategory.comp_whiskerRight,
      ← MonoidalCategory.comp_whiskerRight]
    exact congrArg (fun k ↦ k ▷ H.val) (adj.unit.naturality fg)
  change L.map ((L.map fg).val ▷ H.val) ≫ iF'GH.inv ≫
      L.map (α_ F'.val G.val H.val).hom ≫ iF'uGH.hom =
    iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫ iFuGH.hom ≫
      L.map (f.val ▷ (L.obj (G.val ⊗ H.val)).val)
  have hunitMap := congrArg L.map hunit
  simp only [Functor.map_comp] at hunitMap
  change L.map (fg ▷ H.val) ≫ iF'GH.hom =
    iFGH.hom ≫ L.map ((L.map fg).val ▷ H.val) at hunitMap
  have hleft : L.map ((L.map fg).val ▷ H.val) ≫ iF'GH.inv =
      iFGH.inv ≫ L.map (fg ▷ H.val) := by
    rw [← cancel_mono iF'GH.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun k ↦ iFGH.inv ≫ k) hunitMap.symm
  have hassoc := congrArg L.map
    (MonoidalCategory.associator_naturality_left f.val G.val H.val)
  simp only [Functor.map_comp] at hassoc
  have hright := congrArg L.map
    (MonoidalCategory.whisker_exchange f.val uGH).symm
  simp only [Functor.map_comp] at hright
  change L.map (f.val ▷ (G.val ⊗ H.val)) ≫ iF'uGH.hom =
    iFuGH.hom ≫ L.map (f.val ▷ (L.obj (G.val ⊗ H.val)).val) at hright
  calc
    L.map ((L.map fg).val ▷ H.val) ≫ iF'GH.inv ≫
          L.map (α_ F'.val G.val H.val).hom ≫ iF'uGH.hom =
        (iFGH.inv ≫ L.map (fg ▷ H.val)) ≫
          L.map (α_ F'.val G.val H.val).hom ≫ iF'uGH.hom :=
      congrArg (fun k ↦ k ≫ L.map (α_ F'.val G.val H.val).hom ≫ iF'uGH.hom) hleft
    _ = iFGH.inv ≫
          (L.map (fg ▷ H.val) ≫ L.map (α_ F'.val G.val H.val).hom) ≫
          iF'uGH.hom := by simp only [Category.assoc]
    _ = iFGH.inv ≫
          (L.map (α_ F.val G.val H.val).hom ≫
            L.map (f.val ▷ (G.val ⊗ H.val))) ≫ iF'uGH.hom :=
      congrArg (fun k ↦ iFGH.inv ≫ k ≫ iF'uGH.hom) hassoc
    _ = iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫
          (L.map (f.val ▷ (G.val ⊗ H.val)) ≫ iF'uGH.hom) := by
      simp only [Category.assoc]
    _ = iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫
          (iFuGH.hom ≫ L.map (f.val ▷ (L.obj (G.val ⊗ H.val)).val)) :=
      congrArg (fun k ↦ iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫ k) hright
    _ = iFGH.inv ≫ L.map (α_ F.val G.val H.val).hom ≫ iFuGH.hom ≫
          L.map (f.val ▷ (L.obj (G.val ⊗ H.val)).val) := rfl

end AlgebraicGeometry.Scheme.Modules

end

end
