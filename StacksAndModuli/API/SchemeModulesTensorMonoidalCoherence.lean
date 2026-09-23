module

public import StacksAndModuli.API.SchemeModulesTensorQuasicoherent
public import StacksAndModuli.API.SchemeModulesTensorSymmetry
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import Mathlib.CategoryTheory.Bicategory.SingleObj
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.InducedCategory
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Monoidal coherence for tensor products of scheme modules

The tensor product on `X.Modules` is defined by sheafifying the presheaf tensor product.
Its chosen associator and unitors are explicit localization zigzags, so they do not come
with a `MonoidalCategory` instance directly. This file compares those choices with
Mathlib's lawful monoidal localization, transports the coherence laws to an auxiliary
induced category, and uses that comparison to prove triangle identities for invertible
pairings.

Main declarations:

* `CategoryTheory.isoPairing_right_triangle_of_left` derives the right snake identity
  from the left snake identity in any monoidal category;
* `CategoryTheory.isoPairing_right_triangle_of_left_whiskered` tensors that identity by
  an arbitrary object;
* `AlgebraicGeometry.Scheme.Modules.tensorPairing_right_triangle_of_left_whiskered`
  gives the corresponding theorem for the chosen tensor API on scheme modules.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.MonoidalCategory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

-- These staged simplifications expose the exact slices rewritten below; the linter's
-- `simp only` suggestions do not preserve those slice shapes.
set_option linter.flexible false in
/-- A factorized associator remains compatible after conjugating the three tensor
factors by isomorphisms. This is the abstract calculation used for the localized tensor
comparison on scheme modules. -/
lemma associator_comparison_of_factorization
    (LF LG LH F G H A B T U : C)
    (cF : LF ≅ F) (cG : LG ≅ G) (cH : LH ≅ H)
    (mFG : LF ⊗ LG ≅ A) (mGH : LG ⊗ LH ≅ B)
    (mAH : A ⊗ LH ≅ T) (mFB : LF ⊗ B ≅ U)
    (a : T ⟶ U)
    (ha : (α_ LF LG LH).hom =
      (mFG.hom ⊗ₘ 𝟙 LH) ≫ mAH.hom ≫ a ≫ mFB.inv ≫
        (𝟙 LF ⊗ₘ mGH.inv)) :
    (((cF.inv ▷ G) ≫ (LF ◁ cG.inv) ≫ mFG.hom) ⊗ₘ 𝟙 H) ≫
        (A ◁ cH.inv) ≫ mAH.hom ≫ a =
      (α_ F G H).hom ≫
        (𝟙 F ⊗ₘ ((cG.inv ▷ H) ≫ (LG ◁ cH.inv) ≫ mGH.hom)) ≫
        (cF.inv ▷ B) ≫ mFB.hom := by
  have ha' :
      (mFG.hom ⊗ₘ 𝟙 LH) ≫ mAH.hom ≫ a =
        (α_ LF LG LH).hom ≫ (𝟙 LF ⊗ₘ mGH.hom) ≫ mFB.hom := by
    rw [ha]
    slice_rhs 5 6 =>
      rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  calc
    (((cF.inv ▷ G) ≫ (LF ◁ cG.inv) ≫ mFG.hom) ⊗ₘ 𝟙 H) ≫
          (A ◁ cH.inv) ≫ mAH.hom ≫ a =
        (((cF.inv ⊗ₘ cG.inv) ⊗ₘ cH.inv) ≫
          (mFG.hom ⊗ₘ 𝟙 LH) ≫ mAH.hom ≫ a) := by
      simp [MonoidalCategory.tensorHom_def, Category.assoc]
      slice_lhs 5 6 =>
        rw [← MonoidalCategory.whisker_exchange]
      slice_lhs 4 5 =>
        rw [← MonoidalCategory.associator_inv_naturality_right]
      simp only [Category.assoc]
    _ = ((cF.inv ⊗ₘ cG.inv) ⊗ₘ cH.inv) ≫
          (α_ LF LG LH).hom ≫ (𝟙 LF ⊗ₘ mGH.hom) ≫ mFB.hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ ((cF.inv ⊗ₘ cG.inv) ⊗ₘ cH.inv) ≫ k) ha'
    _ = (α_ F G H).hom ≫
          (cF.inv ⊗ₘ (cG.inv ⊗ₘ cH.inv)) ≫
          (𝟙 LF ⊗ₘ mGH.hom) ≫ mFB.hom := by
      have hnat := MonoidalCategory.associator_naturality
        cF.inv cG.inv cH.inv
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ (𝟙 LF ⊗ₘ mGH.hom) ≫ mFB.hom) hnat
    _ = (α_ F G H).hom ≫
          (𝟙 F ⊗ₘ ((cG.inv ▷ H) ≫ (LG ◁ cH.inv) ≫ mGH.hom)) ≫
          (cF.inv ▷ B) ≫ mFB.hom := by
      simp [MonoidalCategory.tensorHom_def, Category.assoc]
      slice_lhs 1 2 =>
        rw [MonoidalCategory.associator_naturality_left]
      have hEx := (MonoidalCategory.whisker_exchange cF.inv
        ((cG.inv ▷ H) ≫ (LG ◁ cH.inv) ≫ mGH.hom)).symm
      simpa only [MonoidalCategory.whiskerLeft_comp, Category.assoc] using
        congrArg (fun k ↦ (α_ F G H).hom ≫ k ≫ mFB.hom) hEx

set_option backward.isDefEq.respectTransparency.types true in
set_option backward.isDefEq.respectTransparency true in
/-- A left triangle identity for two inverse pairing isomorphisms implies the right
triangle identity. The evaluation and coevaluation are independent inputs, so no
braiding comparison is needed when this theorem is transported between monoidal
structures. -/
lemma isoPairing_right_triangle_of_left
    (N D : C) (coev : N ⊗ D ≅ 𝟙_ C) (ev : D ⊗ N ≅ 𝟙_ C)
    (h : (λ_ N).inv ≫ coev.inv ▷ N ≫ (α_ N D N).hom ≫
      N ◁ ev.hom ≫ (ρ_ N).hom = 𝟙 N) :
    (ρ_ D).inv ≫ D ◁ coev.inv ≫ (α_ D N D).inv ≫
        ev.hom ▷ D ≫ (λ_ D).hom = 𝟙 D := by
  have hleft :
      coev.inv ▷ N ≫ (α_ N D N).hom ≫ N ◁ ev.hom =
        (λ_ N).hom ≫ (ρ_ N).inv := by
    rw [← cancel_epi (λ_ N).inv, ← cancel_mono (ρ_ N).hom]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.id_comp, Category.comp_id] using h
  have hleftM :
      coev.inv ▷ N ⊗≫ N ◁ ev.hom =
        (λ_ N).hom ≫ (ρ_ N).inv := by
    have hcoh :
        (MonoidalCoherence.iso : ((N ⊗ D) ⊗ N) ≅ N ⊗ (D ⊗ N)).hom =
          (α_ N D N).hom := by
      monoidal
    dsimp only [monoidalComp]
    rw [hcoh]
    simpa only [Category.assoc] using hleft
  have hrightM := Bicategory.right_triangle_of_left_triangle
    (B := MonoidalSingleObj C)
    (a := MonoidalSingleObj.star C) (b := MonoidalSingleObj.star C)
    (η := coev.symm) (ε := ev) hleftM
  change D ◁ coev.inv ⊗≫ ev.hom ▷ D =
    (ρ_ D).hom ≫ (λ_ D).inv at hrightM
  let rzig := D ◁ coev.inv ⊗≫ ev.hom ▷ D
  change rzig = (ρ_ D).hom ≫ (λ_ D).inv at hrightM
  change (ρ_ D).inv ≫ D ◁ coev.inv ≫ (α_ D N D).inv ≫
      ev.hom ▷ D ≫ (λ_ D).hom = 𝟙 D
  calc
    _ = (ρ_ D).inv ≫ rzig ≫ (λ_ D).hom := by
      have hcoh :
          (MonoidalCoherence.iso : (D ⊗ (N ⊗ D)) ≅ (D ⊗ N) ⊗ D).hom =
            (α_ D N D).inv := by
        monoidal
      dsimp only [rzig, monoidalComp]
      rw [hcoh]
      simp only [Category.assoc]
    _ = (ρ_ D).inv ≫ ((ρ_ D).hom ≫ (λ_ D).inv) ≫
          (λ_ D).hom := by rw [hrightM]
    _ = 𝟙 D := by simp

/-- The right triangle obtained from a left triangle remains true after tensoring on
the left by an arbitrary object. -/
lemma isoPairing_right_triangle_of_left_whiskered
    (F N D : C) (coev : N ⊗ D ≅ 𝟙_ C) (ev : D ⊗ N ≅ 𝟙_ C)
    (h : (λ_ N).inv ≫ coev.inv ▷ N ≫ (α_ N D N).hom ≫
      N ◁ ev.hom ≫ (ρ_ N).hom = 𝟙 N) :
    let B := F ⊗ D
    let cancel := (α_ F D N).hom ≫ F ◁ ev.hom ≫ (ρ_ F).hom
    (ρ_ B).inv ≫ B ◁ coev.inv ≫ (α_ B N D).inv ≫
      cancel ▷ D = 𝟙 B := by
  dsimp only
  have hright := isoPairing_right_triangle_of_left N D coev ev h
  calc
    (ρ_ (F ⊗ D)).inv ≫ (F ⊗ D) ◁ coev.inv ≫
          (α_ (F ⊗ D) N D).inv ≫
          ((α_ F D N).hom ≫ F ◁ ev.hom ≫ (ρ_ F).hom) ▷ D =
        F ◁ ((ρ_ D).inv ≫ D ◁ coev.inv ≫
          (α_ D N D).inv ≫ ev.hom ▷ D ≫ (λ_ D).hom) := by
      monoidal
    _ = F ◁ 𝟙 D := by rw [hright]
    _ = 𝟙 (F ⊗ D) := by monoidal

end CategoryTheory

open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The sheafification counit identifies the localized tensor unit with the
structure sheaf. -/
noncomputable def canonicalUnitIso (X : Scheme.{u}) :
    (sheafification X).obj (𝟙_ X.PresheafOfModules) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit :=
    Adjunction.counit_isIso_of_R_fully_faithful adj
  exact (asIso adj.counit).app (SheafOfModules.unit X.ringCatSheaf)

/-- The lawful monoidal localization of presheaves of modules at local
equivalences. Its underlying category is definitionally `X.Modules`. -/
def CanonicalModules (X : Scheme.{u}) :=
  LocalizedMonoidal (sheafification X) (tensorLocalEquivalences X)
    (canonicalUnitIso X)

noncomputable instance canonicalModulesCategory : Category (CanonicalModules X) :=
  inferInstanceAs (Category X.Modules)

noncomputable instance canonicalModulesMonoidalCategory :
    MonoidalCategory (CanonicalModules X) :=
  inferInstanceAs (MonoidalCategory
    (LocalizedMonoidal (sheafification X) (tensorLocalEquivalences X)
      (canonicalUnitIso X)))

/-- An auxiliary category with exactly the chosen tensor object, associator, and
unitors on scheme modules. `ULift` keeps its category instance distinct from the
ordinary category instance on `X.Modules`. -/
abbrev BespokeModules (X : Scheme.{u}) :=
  InducedCategory (CanonicalModules X)
    (fun F : ULift X.Modules ↦ (F.down : CanonicalModules X))

/-- The faithful functor from the auxiliary chosen-tensor category to the lawful
localized monoidal category. -/
abbrev forgetBespoke (X : Scheme.{u}) : BespokeModules X ⥤ CanonicalModules X :=
  inducedFunctor (fun F : ULift X.Modules ↦ (F.down : CanonicalModules X))

/-- The monoidal data on the auxiliary category obtained from the existing chosen
tensor API on scheme modules. Lawfulness is installed later by transport. -/
noncomputable instance bespokeStruct : MonoidalCategoryStruct (BespokeModules X) where
  tensorObj F G := ULift.up (tensor F.down G.down)
  whiskerLeft := fun (F : BespokeModules X) {G G' : BespokeModules X}
      (g : G ⟶ G') ↦ InducedCategory.homMk
        (tensorMapRight F.down g.hom)
  whiskerRight := fun {F F' : BespokeModules X} (f : F ⟶ F')
      (G : BespokeModules X) ↦ InducedCategory.homMk
        (tensorMapLeft f.hom G.down)
  tensorUnit := ULift.up (SheafOfModules.unit X.ringCatSheaf)
  associator F G H := InducedCategory.isoMk
    (tensorAssocIso F.down G.down H.down)
  leftUnitor F := InducedCategory.isoMk (tensorLeftUnitIso F.down)
  rightUnitor F := InducedCategory.isoMk (tensorUnitIso F.down)

/-- Comparison between the lawful localized tensor and the existing chosen tensor
of two scheme modules. -/
noncomputable def comparisonTensorIso (F G : BespokeModules X) :
    (forgetBespoke X).obj F ⊗ (forgetBespoke X).obj G ≅
      (forgetBespoke X).obj (F ⊗ G) := by
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit :=
    Adjunction.counit_isIso_of_R_fully_faithful adj
  let cF : ((sheafification X).obj F.down.val : CanonicalModules X) ≅
      (F.down : CanonicalModules X) :=
    (asIso adj.counit).app F.down
  let cG : ((sheafification X).obj G.down.val : CanonicalModules X) ≅
      (G.down : CanonicalModules X) :=
    (asIso adj.counit).app G.down
  let μFG := Localization.Monoidal.μ
    (sheafification X) (tensorLocalEquivalences X) (canonicalUnitIso X)
    F.down.val G.down.val
  exact (whiskerRightIso (C := CanonicalModules X)
      cF.symm (G.down : CanonicalModules X)) ≪≫
    (whiskerLeftIso (C := CanonicalModules X)
      ((sheafification X).obj F.down.val : CanonicalModules X) cG.symm) ≪≫
    μFG

/-- Naturality of `comparisonTensorIso` in its right tensor factor. -/
lemma comparison_whiskerLeft (F : BespokeModules X)
    {G G' : BespokeModules X} (g : G ⟶ G') :
    (forgetBespoke X).map (F ◁ g) =
      (comparisonTensorIso F G).inv ≫
        ((forgetBespoke X).obj F ◁ (forgetBespoke X).map g) ≫
        (comparisonTensorIso F G').hom := by
  dsimp only [forgetBespoke, inducedFunctor, bespokeStruct,
    InducedCategory.homMk_hom]
  rw [← cancel_epi (comparisonTensorIso F G).hom]
  simp only [Iso.hom_inv_id_assoc]
  change (comparisonTensorIso F G).hom ≫ tensorMapRight F.down g.hom =
    MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
      F.down g.hom ≫ (comparisonTensorIso F G').hom
  let L := sheafification X
  let W := tensorLocalEquivalences X
  let ε := canonicalUnitIso X
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit :=
    Adjunction.counit_isIso_of_R_fully_faithful adj
  let cF : (L.obj F.down.val : CanonicalModules X) ≅ F.down :=
    (asIso adj.counit).app F.down
  let cG : (L.obj G.down.val : CanonicalModules X) ≅ G.down :=
    (asIso adj.counit).app G.down
  let cG' : (L.obj G'.down.val : CanonicalModules X) ≅ G'.down :=
    (asIso adj.counit).app G'.down
  let μFG := Localization.Monoidal.μ L W ε F.down.val G.down.val
  let μFG' := Localization.Monoidal.μ L W ε F.down.val G'.down.val
  change MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
        cF.inv G.down ≫
      MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
        (L.obj F.down.val) cG.inv ≫ μFG.hom ≫
      tensorMapRight F.down g.hom =
    MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
        F.down g.hom ≫
      MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
        cF.inv G'.down ≫
      MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
        (L.obj F.down.val) cG'.inv ≫ μFG'.hom
  have hμ := Localization.Monoidal.μ_natural_right L W ε
    F.down.val g.hom.val
  change MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
      (L.obj F.down.val) (L.map g.hom.val) ≫ μFG'.hom =
    μFG.hom ≫ tensorMapRight F.down g.hom at hμ
  have hc := adj.counit.naturality g.hom
  change L.map g.hom.val ≫ cG'.hom = cG.hom ≫ g.hom at hc
  have hcInv : cG.inv ≫ L.map g.hom.val = g.hom ≫ cG'.inv := by
    apply (cancel_epi cG.hom).1
    simp only [Iso.hom_inv_id_assoc]
    simpa only [cG, cG', L, adj, Functor.comp_map, Functor.id_map,
      Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun k ↦ k ≫ cG'.inv) hc
  calc
    MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv G.down ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F.down.val) cG.inv ≫ μFG.hom ≫
          tensorMapRight F.down g.hom =
        MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv G.down ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F.down.val) cG.inv ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F.down.val) (L.map g.hom.val) ≫ μFG'.hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ MonoidalCategoryStruct.whiskerRight
            (C := CanonicalModules X) cF.inv G.down ≫
          MonoidalCategoryStruct.whiskerLeft
            (C := CanonicalModules X) (L.obj F.down.val) cG.inv ≫ k)
        hμ.symm
    _ = MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv G.down ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F.down.val) (cG.inv ≫ L.map g.hom.val) ≫ μFG'.hom := by
      rw [MonoidalCategory.whiskerLeft_comp]
      simp only [Category.assoc]
    _ = MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv G.down ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F.down.val) (g.hom ≫ cG'.inv) ≫ μFG'.hom := by
      rw [hcInv]
    _ = MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv G.down ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F.down.val) g.hom ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F.down.val) cG'.inv ≫ μFG'.hom := by
      rw [MonoidalCategory.whiskerLeft_comp]
      simp only [Category.assoc]
    _ = MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          F.down g.hom ≫
        MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv G'.down ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F.down.val) cG'.inv ≫ μFG'.hom := by
      have hEx := MonoidalCategory.whisker_exchange
        (C := CanonicalModules X) cF.inv g.hom
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ MonoidalCategoryStruct.whiskerLeft
          (C := CanonicalModules X) (L.obj F.down.val) cG'.inv ≫
          μFG'.hom) hEx.symm

/-- Naturality of `comparisonTensorIso` in its left tensor factor. -/
lemma comparison_whiskerRight {F F' : BespokeModules X}
    (f : F ⟶ F') (G : BespokeModules X) :
    (forgetBespoke X).map (f ▷ G) =
      (comparisonTensorIso F G).inv ≫
        ((forgetBespoke X).map f ▷ (forgetBespoke X).obj G) ≫
        (comparisonTensorIso F' G).hom := by
  dsimp only [forgetBespoke, inducedFunctor, bespokeStruct,
    InducedCategory.homMk_hom]
  rw [← cancel_epi (comparisonTensorIso F G).hom]
  simp only [Iso.hom_inv_id_assoc]
  change (comparisonTensorIso F G).hom ≫ tensorMapLeft f.hom G.down =
    MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
      f.hom G.down ≫ (comparisonTensorIso F' G).hom
  let L := sheafification X
  let W := tensorLocalEquivalences X
  let ε := canonicalUnitIso X
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit :=
    Adjunction.counit_isIso_of_R_fully_faithful adj
  let cF : (L.obj F.down.val : CanonicalModules X) ≅ F.down :=
    (asIso adj.counit).app F.down
  let cF' : (L.obj F'.down.val : CanonicalModules X) ≅ F'.down :=
    (asIso adj.counit).app F'.down
  let cG : (L.obj G.down.val : CanonicalModules X) ≅ G.down :=
    (asIso adj.counit).app G.down
  let μFG := Localization.Monoidal.μ L W ε F.down.val G.down.val
  let μF'G := Localization.Monoidal.μ L W ε F'.down.val G.down.val
  change MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
        cF.inv G.down ≫
      MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
        (L.obj F.down.val) cG.inv ≫ μFG.hom ≫
      tensorMapLeft f.hom G.down =
    MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
        f.hom G.down ≫
      MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
        cF'.inv G.down ≫
      MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
        (L.obj F'.down.val) cG.inv ≫ μF'G.hom
  have hμ := Localization.Monoidal.μ_natural_left L W ε
    f.hom.val G.down.val
  change MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
      (L.map f.hom.val) (L.obj G.down.val) ≫ μF'G.hom =
    μFG.hom ≫ tensorMapLeft f.hom G.down at hμ
  have hc := adj.counit.naturality f.hom
  change L.map f.hom.val ≫ cF'.hom = cF.hom ≫ f.hom at hc
  have hcInv : cF.inv ≫ L.map f.hom.val = f.hom ≫ cF'.inv := by
    apply (cancel_epi cF.hom).1
    simp only [Iso.hom_inv_id_assoc]
    simpa only [cF, cF', L, adj, Functor.comp_map, Functor.id_map,
      Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using congrArg (fun k ↦ k ≫ cF'.inv) hc
  calc
    MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv G.down ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F.down.val) cG.inv ≫ μFG.hom ≫
          tensorMapLeft f.hom G.down =
        MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv G.down ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F.down.val) cG.inv ≫
        MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          (L.map f.hom.val) (L.obj G.down.val) ≫ μF'G.hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ MonoidalCategoryStruct.whiskerRight
            (C := CanonicalModules X) cF.inv G.down ≫
          MonoidalCategoryStruct.whiskerLeft
            (C := CanonicalModules X) (L.obj F.down.val) cG.inv ≫ k)
        hμ.symm
    _ = MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv G.down ≫
        MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          (L.map f.hom.val) G.down ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F'.down.val) cG.inv ≫ μF'G.hom := by
      have hEx := MonoidalCategory.whisker_exchange
        (C := CanonicalModules X) (L.map f.hom.val) cG.inv
      simpa only [Category.assoc] using congrArg
        (fun k ↦ MonoidalCategoryStruct.whiskerRight
          (C := CanonicalModules X) cF.inv G.down ≫ k ≫ μF'G.hom) hEx
    _ = MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          (cF.inv ≫ L.map f.hom.val) G.down ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F'.down.val) cG.inv ≫ μF'G.hom := by
      have hComp := MonoidalCategory.comp_whiskerRight
        (C := CanonicalModules X) cF.inv (L.map f.hom.val) G.down
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ MonoidalCategoryStruct.whiskerLeft
          (C := CanonicalModules X) (L.obj F'.down.val) cG.inv ≫
          μF'G.hom) hComp.symm
    _ = MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          (f.hom ≫ cF'.inv) G.down ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F'.down.val) cG.inv ≫ μF'G.hom := by
      rw [hcInv]
    _ = MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          f.hom G.down ≫
        MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF'.inv G.down ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F'.down.val) cG.inv ≫ μF'G.hom := by
      have hComp := MonoidalCategory.comp_whiskerRight
        (C := CanonicalModules X) f.hom cF'.inv G.down
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ MonoidalCategoryStruct.whiskerLeft
          (C := CanonicalModules X) (L.obj F'.down.val) cG.inv ≫
          μF'G.hom) hComp

/-- Sheafification sends the adjunction unit to the inverse of the counit at the
sheafified object. -/
lemma sheafification_map_unit_eq_counit_inv
    (A : X.PresheafOfModules) :
    (sheafification X).map
        ((_root_.PresheafOfModules.sheafificationAdjunction
          (𝟙 X.ringCatSheaf.obj)).unit.app A) =
      ((asIso (_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit).app
          ((sheafification X).obj A)).inv := by
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  letI : IsIso adj.counit :=
    Adjunction.counit_isIso_of_R_fully_faithful adj
  change (sheafification X).map (adj.unit.app A) =
    ((asIso adj.counit).app ((sheafification X).obj A)).inv
  apply (cancel_mono ((asIso adj.counit).app
    ((sheafification X).obj A)).hom).1
  rw [Iso.inv_hom_id]
  change (sheafification X).map (adj.unit.app A) ≫
    adj.counit.app ((sheafification X).obj A) = 𝟙 _
  exact adj.left_triangle_components A

/-- Factorization of the tensor comparison when its left input is a
sheafification. -/
lemma comparisonTensorIso_on_sheafification_hom
    (A : X.PresheafOfModules) (H : X.Modules) :
    let L := sheafification X
    let W := tensorLocalEquivalences X
    let ε := canonicalUnitIso X
    let adj := _root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    let cA : (L.obj (L.obj A).val : CanonicalModules X) ≅
        (L.obj A : CanonicalModules X) :=
      (asIso adj.counit).app (L.obj A)
    let cH : (L.obj H.val : CanonicalModules X) ≅
        (H : CanonicalModules X) :=
      (asIso adj.counit).app H
    MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
        cA.inv H ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj (L.obj A).val) cH.inv ≫
        (Localization.Monoidal.μ L W ε (L.obj A).val H.val).hom =
      MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj A) cH.inv ≫
        (Localization.Monoidal.μ L W ε A H.val).hom ≫
        L.map (adj.unit.app A ▷ H.val) := by
  dsimp only
  let L := sheafification X
  let W := tensorLocalEquivalences X
  let ε := canonicalUnitIso X
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let cA : (L.obj (L.obj A).val : CanonicalModules X) ≅
      (L.obj A : CanonicalModules X) :=
    (asIso adj.counit).app (L.obj A)
  let cH : (L.obj H.val : CanonicalModules X) ≅
      (H : CanonicalModules X) :=
    (asIso adj.counit).app H
  have hcA : L.map (adj.unit.app A) = cA.inv := by
    exact sheafification_map_unit_eq_counit_inv A
  have hμ := Localization.Monoidal.μ_natural_left L W ε
    (adj.unit.app A) H.val
  change MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
      (L.map (adj.unit.app A)) (L.obj H.val) ≫
      (Localization.Monoidal.μ L W ε (L.obj A).val H.val).hom =
    (Localization.Monoidal.μ L W ε A H.val).hom ≫
      L.map (adj.unit.app A ▷ H.val) at hμ
  calc
    MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cA.inv H ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj (L.obj A).val) cH.inv ≫
          (Localization.Monoidal.μ L W ε (L.obj A).val H.val).hom =
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj A) cH.inv ≫
        MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cA.inv (L.obj H.val) ≫
          (Localization.Monoidal.μ L W ε (L.obj A).val H.val).hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫
          (Localization.Monoidal.μ L W ε (L.obj A).val H.val).hom)
        (MonoidalCategory.whisker_exchange
          (C := CanonicalModules X) cA.inv cH.inv).symm
    _ = MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj A) cH.inv ≫
        MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          (L.map (adj.unit.app A)) (L.obj H.val) ≫
          (Localization.Monoidal.μ L W ε (L.obj A).val H.val).hom := by
      rw [hcA]
    _ = MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj A) cH.inv ≫
          (Localization.Monoidal.μ L W ε A H.val).hom ≫
          L.map (adj.unit.app A ▷ H.val) := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ MonoidalCategoryStruct.whiskerLeft
          (C := CanonicalModules X) (L.obj A) cH.inv ≫ k) hμ

/-- Factorization of the tensor comparison when its right input is a
sheafification. -/
lemma comparisonTensorIso_sheafification_on_hom
    (F : X.Modules) (B : X.PresheafOfModules) :
    let L := sheafification X
    let W := tensorLocalEquivalences X
    let ε := canonicalUnitIso X
    let adj := _root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    let cF : (L.obj F.val : CanonicalModules X) ≅
        (F : CanonicalModules X) :=
      (asIso adj.counit).app F
    let cB : (L.obj (L.obj B).val : CanonicalModules X) ≅
        (L.obj B : CanonicalModules X) :=
      (asIso adj.counit).app (L.obj B)
    MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
        cF.inv (L.obj B) ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F.val) cB.inv ≫
        (Localization.Monoidal.μ L W ε F.val (L.obj B).val).hom =
      MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv (L.obj B) ≫
        (Localization.Monoidal.μ L W ε F.val B).hom ≫
        L.map (F.val ◁ adj.unit.app B) := by
  dsimp only
  let L := sheafification X
  let W := tensorLocalEquivalences X
  let ε := canonicalUnitIso X
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let cF : (L.obj F.val : CanonicalModules X) ≅
      (F : CanonicalModules X) :=
    (asIso adj.counit).app F
  let cB : (L.obj (L.obj B).val : CanonicalModules X) ≅
      (L.obj B : CanonicalModules X) :=
    (asIso adj.counit).app (L.obj B)
  have hcB : L.map (adj.unit.app B) = cB.inv := by
    exact sheafification_map_unit_eq_counit_inv B
  have hμ := Localization.Monoidal.μ_natural_right L W ε
    F.val (adj.unit.app B)
  change MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
      (L.obj F.val) (L.map (adj.unit.app B)) ≫
      (Localization.Monoidal.μ L W ε F.val (L.obj B).val).hom =
    (Localization.Monoidal.μ L W ε F.val B).hom ≫
      L.map (F.val ◁ adj.unit.app B) at hμ
  rw [← hcB] at *
  simpa only [Category.assoc] using congrArg
    (fun k ↦ MonoidalCategoryStruct.whiskerRight
      (C := CanonicalModules X) cF.inv (L.obj B) ≫ k) hμ

/-- The core associator comparison after the two outer sheafification-unit
zigzags have been removed. -/
lemma comparison_associator_core (F G H : X.Modules) :
    let L := sheafification X
    let W := tensorLocalEquivalences X
    let ε := canonicalUnitIso X
    let adj := _root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    let FC : CanonicalModules X := F
    let GC : CanonicalModules X := G
    let HC : CanonicalModules X := H
    let A := F.val ⊗ G.val
    let B := G.val ⊗ H.val
    let cF : (L.obj F.val : CanonicalModules X) ≅ FC :=
      (asIso adj.counit).app F
    let cG : (L.obj G.val : CanonicalModules X) ≅ GC :=
      (asIso adj.counit).app G
    let cH : (L.obj H.val : CanonicalModules X) ≅ HC :=
      (asIso adj.counit).app H
    let kFG : MonoidalCategoryStruct.tensorObj (C := CanonicalModules X)
        FC GC ⟶ (L.obj A : CanonicalModules X) :=
      MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv GC ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj F.val) cG.inv ≫
        (Localization.Monoidal.μ L W ε F.val G.val).hom
    let kGH : MonoidalCategoryStruct.tensorObj (C := CanonicalModules X)
        GC HC ⟶ (L.obj B : CanonicalModules X) :=
      MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cG.inv HC ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj G.val) cH.inv ≫
        (Localization.Monoidal.μ L W ε G.val H.val).hom
    let qL : MonoidalCategoryStruct.tensorObj (C := CanonicalModules X)
        (L.obj A) HC ⟶
        (L.obj (A ⊗ H.val) : CanonicalModules X) :=
      MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj A) cH.inv ≫
        (Localization.Monoidal.μ L W ε A H.val).hom
    let qR : MonoidalCategoryStruct.tensorObj (C := CanonicalModules X)
        FC (L.obj B) ⟶
        (L.obj (F.val ⊗ B) : CanonicalModules X) :=
      MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv (L.obj B) ≫
        (Localization.Monoidal.μ L W ε F.val B).hom
    (kFG ⊗ₘ 𝟙 HC) ≫ qL ≫ L.map (α_ F.val G.val H.val).hom =
      (α_ FC GC HC).hom ≫ (𝟙 FC ⊗ₘ kGH) ≫ qR := by
  dsimp only
  simp only [Category.assoc]
  apply CategoryTheory.associator_comparison_of_factorization
  exact Localization.Monoidal.associator_hom_app
    (sheafification X) (tensorLocalEquivalences X) (canonicalUnitIso X)
    F.val G.val H.val

/-- Compatibility of the chosen sheaf-module associator with the lawful localized
associator under `comparisonTensorIso`. -/
lemma comparison_associator (F G H : BespokeModules X) :
    (forgetBespoke X).map (α_ F G H).hom =
      ((((comparisonTensorIso (F ⊗ G) H).symm ≪≫
          ((comparisonTensorIso F G).symm ⊗ᵢ Iso.refl _))
        ≪≫ α_ ((forgetBespoke X).obj F)
          ((forgetBespoke X).obj G) ((forgetBespoke X).obj H)
        ≪≫ ((Iso.refl _ ⊗ᵢ comparisonTensorIso G H) ≪≫
          comparisonTensorIso F (G ⊗ H))).hom) := by
  dsimp only [forgetBespoke, inducedFunctor, bespokeStruct,
    InducedCategory.isoMk_hom]
  change (tensorAssocIso F.down G.down H.down).hom = _
  let FC := (forgetBespoke X).obj F
  let GC := (forgetBespoke X).obj G
  let HC := (forgetBespoke X).obj H
  let kOuter := comparisonTensorIso (F ⊗ G) H
  let kFG := comparisonTensorIso F G
  let kFGH := kFG ⊗ᵢ Iso.refl HC
  let kGH := comparisonTensorIso G H
  let kGHF := Iso.refl FC ⊗ᵢ kGH
  let kRight := comparisonTensorIso F (G ⊗ H)
  rw [← cancel_epi kOuter.hom]
  change kOuter.hom ≫ (tensorAssocIso F.down G.down H.down).hom =
    kOuter.hom ≫ kOuter.inv ≫ kFGH.inv ≫
      (α_ FC GC HC).hom ≫ kGHF.hom ≫ kRight.hom
  simp only [Iso.hom_inv_id_assoc]
  rw [← cancel_epi kFGH.hom]
  change kFGH.hom ≫ kOuter.hom ≫
      (tensorAssocIso F.down G.down H.down).hom =
    kFGH.hom ≫ kFGH.inv ≫ (α_ FC GC HC).hom ≫
      kGHF.hom ≫ kRight.hom
  simp only [Iso.hom_inv_id_assoc]
  let L := sheafification X
  let W := tensorLocalEquivalences X
  let ε := canonicalUnitIso X
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let F0 := F.down
  let G0 := G.down
  let H0 := H.down
  let A := F0.val ⊗ G0.val
  let B := G0.val ⊗ H0.val
  let LA : CanonicalModules X := L.obj A
  let LB : CanonicalModules X := L.obj B
  let cF : (L.obj F0.val : CanonicalModules X) ≅ FC :=
    (asIso adj.counit).app F0
  let cH : (L.obj H0.val : CanonicalModules X) ≅ HC :=
    (asIso adj.counit).app H0
  let qL : LA ⊗ HC ⟶
      (L.obj (A ⊗ H0.val) : CanonicalModules X) :=
    (LA ◁ cH.inv) ≫
      (Localization.Monoidal.μ L W ε A H0.val).hom
  let qR : FC ⊗ LB ⟶
      (L.obj (F0.val ⊗ B) : CanonicalModules X) :=
    MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
        cF.inv LB ≫
      (Localization.Monoidal.μ L W ε F0.val B).hom
  have hOuter := comparisonTensorIso_on_sheafification_hom A H0
  change kOuter.hom = qL ≫
    L.map (adj.unit.app A ▷ H0.val) at hOuter
  have hRight := comparisonTensorIso_sheafification_on_hom F0 B
  change kRight.hom = qR ≫
    L.map (F0.val ◁ adj.unit.app B) at hRight
  rw [hOuter, hRight]
  dsimp only [tensorAssocIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  have hunitMem (M : X.PresheafOfModules) : W (adj.unit.app M) := by
    change (Opens.grothendieckTopology X).W
      ((_root_.PresheafOfModules.toPresheaf
        X.ringCatSheaf.obj).map (adj.unit.app M))
    simpa [W, adj] using
      (Opens.grothendieckTopology X).W_toSheafify M.presheaf
  have huL : W (adj.unit.app A ▷ H0.val) :=
    W.whiskerRight_mem (adj.unit.app A) (hunitMem A) H0.val
  simp only [Category.assoc]
  rw [Localization.isoOfHom_hom_inv_id_assoc L W
    (adj.unit.app A ▷ H0.val) huL]
  rw [Localization.isoOfHom_hom]
  have hcore := comparison_associator_core F0 G0 H0
  change kFGH.hom ≫ qL ≫ L.map (α_ F0.val G0.val H0.val).hom =
    (α_ FC GC HC).hom ≫ kGHF.hom ≫ qR at hcore
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ L.map (F0.val ◁ adj.unit.app B)) hcore

/-- Compatibility of the chosen right unitor with the lawful localized right
unitor under `comparisonTensorIso`. -/
lemma comparison_rightUnitor (F : BespokeModules X) :
    (forgetBespoke X).map
        (MonoidalCategoryStruct.rightUnitor (C := BespokeModules X) F).hom =
      (comparisonTensorIso F (𝟙_ (BespokeModules X))).inv ≫
        (MonoidalCategoryStruct.rightUnitor (C := CanonicalModules X)
          ((forgetBespoke X).obj F)).hom := by
  dsimp only [forgetBespoke, inducedFunctor, bespokeStruct,
    InducedCategory.isoMk_hom]
  rw [← cancel_epi
    (comparisonTensorIso F (𝟙_ (BespokeModules X))).hom]
  simp only [Iso.hom_inv_id_assoc]
  let L := sheafification X
  let W := tensorLocalEquivalences X
  let ε := canonicalUnitIso X
  let I : CanonicalModules X := SheafOfModules.unit X.ringCatSheaf
  let LF : CanonicalModules X := L.obj F.down.val
  let cF : LF ≅ (F.down : CanonicalModules X) := by
    let adj := _root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    letI : IsIso adj.counit :=
      Adjunction.counit_isIso_of_R_fully_faithful adj
    exact (asIso adj.counit).app F.down
  let μFI := Localization.Monoidal.μ L W ε F.down.val
    (𝟙_ X.PresheafOfModules)
  change MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
        cF.inv I ≫
      MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
        LF ε.inv ≫ μFI.hom ≫ L.map (ρ_ F.down.val).hom ≫ cF.hom =
    (MonoidalCategoryStruct.rightUnitor (C := CanonicalModules X)
      F.down).hom
  have hRight := Localization.Monoidal.rightUnitor_hom_app
    L W ε F.down.val
  change (MonoidalCategoryStruct.rightUnitor (C := CanonicalModules X)
      LF).hom =
    MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X) LF ε.inv ≫
      μFI.hom ≫ L.map (ρ_ F.down.val).hom at hRight
  have hnat := MonoidalCategory.rightUnitor_naturality cF.inv
  change MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
      cF.inv I ≫
        (MonoidalCategoryStruct.rightUnitor (C := CanonicalModules X) LF).hom =
    (MonoidalCategoryStruct.rightUnitor (C := CanonicalModules X) F.down).hom ≫
      cF.inv at hnat
  calc
    MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv I ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          LF ε.inv ≫ μFI.hom ≫ L.map (ρ_ F.down.val).hom ≫ cF.hom =
      MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          cF.inv I ≫
        (MonoidalCategoryStruct.rightUnitor (C := CanonicalModules X) LF).hom ≫
          cF.hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ MonoidalCategoryStruct.whiskerRight
          (C := CanonicalModules X) cF.inv I ≫ k ≫ cF.hom) hRight.symm
    _ = (MonoidalCategoryStruct.rightUnitor (C := CanonicalModules X)
          F.down).hom ≫ cF.inv ≫ cF.hom := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ cF.hom) hnat
    _ = (MonoidalCategoryStruct.rightUnitor (C := CanonicalModules X)
          F.down).hom := by simp

/-- Compatibility of the chosen left unitor with the lawful localized left unitor
under `comparisonTensorIso`. -/
lemma comparison_leftUnitor (F : BespokeModules X) :
    (forgetBespoke X).map
        (MonoidalCategoryStruct.leftUnitor (C := BespokeModules X) F).hom =
      (comparisonTensorIso (𝟙_ (BespokeModules X)) F).inv ≫
        (MonoidalCategoryStruct.leftUnitor (C := CanonicalModules X)
          ((forgetBespoke X).obj F)).hom := by
  dsimp only [forgetBespoke, inducedFunctor, bespokeStruct,
    InducedCategory.isoMk_hom]
  rw [← cancel_epi
    (comparisonTensorIso (𝟙_ (BespokeModules X)) F).hom]
  simp only [Iso.hom_inv_id_assoc]
  let L := sheafification X
  let W := tensorLocalEquivalences X
  let ε := canonicalUnitIso X
  let I : CanonicalModules X := SheafOfModules.unit X.ringCatSheaf
  let LF : CanonicalModules X := L.obj F.down.val
  let cF : LF ≅ (F.down : CanonicalModules X) := by
    let adj := _root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    letI : IsIso adj.counit :=
      Adjunction.counit_isIso_of_R_fully_faithful adj
    exact (asIso adj.counit).app F.down
  let μIF := Localization.Monoidal.μ L W ε
    (𝟙_ X.PresheafOfModules) F.down.val
  change MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
        ε.inv F.down ≫
      MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
        (L.obj (𝟙_ X.PresheafOfModules)) cF.inv ≫
      μIF.hom ≫ L.map (λ_ F.down.val).hom ≫ cF.hom =
    (MonoidalCategoryStruct.leftUnitor (C := CanonicalModules X)
      F.down).hom
  have hLeft := Localization.Monoidal.leftUnitor_hom_app L W ε F.down.val
  change (MonoidalCategoryStruct.leftUnitor (C := CanonicalModules X)
      LF).hom =
    MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
        ε.inv LF ≫ μIF.hom ≫ L.map (λ_ F.down.val).hom at hLeft
  have hnat := MonoidalCategory.leftUnitor_naturality cF.inv
  change MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
      I cF.inv ≫
        (MonoidalCategoryStruct.leftUnitor (C := CanonicalModules X) LF).hom =
    (MonoidalCategoryStruct.leftUnitor (C := CanonicalModules X) F.down).hom ≫
      cF.inv at hnat
  have hEx := (MonoidalCategory.whisker_exchange
    (C := CanonicalModules X) ε.inv cF.inv).symm
  change MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
        ε.inv F.down ≫
      MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
        (L.obj (𝟙_ X.PresheafOfModules)) cF.inv =
    MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
        I cF.inv ≫
      MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
        ε.inv LF at hEx
  calc
    MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          ε.inv F.down ≫
        MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          (L.obj (𝟙_ X.PresheafOfModules)) cF.inv ≫
        μIF.hom ≫ L.map (λ_ F.down.val).hom ≫ cF.hom =
      MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          I cF.inv ≫
        MonoidalCategoryStruct.whiskerRight (C := CanonicalModules X)
          ε.inv LF ≫ μIF.hom ≫ L.map (λ_ F.down.val).hom ≫ cF.hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ k ≫ μIF.hom ≫ L.map (λ_ F.down.val).hom ≫ cF.hom) hEx
    _ = MonoidalCategoryStruct.whiskerLeft (C := CanonicalModules X)
          I cF.inv ≫
        (MonoidalCategoryStruct.leftUnitor (C := CanonicalModules X) LF).hom ≫
          cF.hom := by
      simpa only [Category.assoc] using congrArg
        (fun k ↦ MonoidalCategoryStruct.whiskerLeft
          (C := CanonicalModules X) I cF.inv ≫ k ≫ cF.hom) hLeft.symm
    _ = (MonoidalCategoryStruct.leftUnitor (C := CanonicalModules X)
          F.down).hom ≫ cF.inv ≫ cF.hom := by
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ cF.hom) hnat
    _ = (MonoidalCategoryStruct.leftUnitor (C := CanonicalModules X)
          F.down).hom := by simp

/-- The faithful comparison data which transports the lawful localized monoidal
structure to the existing chosen tensor data on scheme modules. -/
noncomputable def comparisonData :
    Monoidal.InducingFunctorData (forgetBespoke X) where
  μIso := comparisonTensorIso
  εIso := Iso.refl _
  whiskerLeft_eq := comparison_whiskerLeft
  whiskerRight_eq := comparison_whiskerRight
  tensorHom_eq := by
    intro F F' G G' f g
    dsimp only [MonoidalCategoryStruct.tensorHom, bespokeStruct]
    rw [Functor.map_comp]
    have hr := comparison_whiskerRight f G
    have hl := comparison_whiskerLeft F' g
    change (forgetBespoke X).map
        (InducedCategory.homMk (tensorMapLeft f.hom G.down)) = _ at hr
    change (forgetBespoke X).map
        (InducedCategory.homMk (tensorMapRight F'.down g.hom)) = _ at hl
    rw [hr, hl]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    change _ = (comparisonTensorIso F G).inv ≫
      MonoidalCategoryStruct.tensorHom (C := CanonicalModules X)
        ((forgetBespoke X).map f) ((forgetBespoke X).map g) ≫
      (comparisonTensorIso F' G').hom
    have ht := MonoidalCategory.tensorHom_def
      (C := CanonicalModules X) ((forgetBespoke X).map f)
        ((forgetBespoke X).map g)
    simpa only [Category.assoc] using congrArg
      (fun k ↦ (comparisonTensorIso F G).inv ≫ k ≫
        (comparisonTensorIso F' G').hom) ht.symm
  associator_eq := by
    intro F G H
    exact comparison_associator F G H
  leftUnitor_eq := by
    intro F
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
      Iso.refl_hom]
    change _ = (comparisonTensorIso (𝟙_ (BespokeModules X)) F).inv ≫
      MonoidalCategoryStruct.tensorHom (C := CanonicalModules X)
        (𝟙 (𝟙_ (CanonicalModules X))) (𝟙 ((forgetBespoke X).obj F)) ≫
      (MonoidalCategoryStruct.leftUnitor (C := CanonicalModules X)
        ((forgetBespoke X).obj F)).hom
    have hId := MonoidalCategory.id_tensorHom_id
      (C := CanonicalModules X) (𝟙_ (CanonicalModules X))
        ((forgetBespoke X).obj F)
    simp only [hId]
    exact comparison_leftUnitor F
  rightUnitor_eq := by
    intro F
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
      Iso.refl_hom]
    change _ = (comparisonTensorIso F (𝟙_ (BespokeModules X))).inv ≫
      MonoidalCategoryStruct.tensorHom (C := CanonicalModules X)
        (𝟙 ((forgetBespoke X).obj F)) (𝟙 (𝟙_ (CanonicalModules X))) ≫
      (MonoidalCategoryStruct.rightUnitor (C := CanonicalModules X)
        ((forgetBespoke X).obj F)).hom
    have hId := MonoidalCategory.id_tensorHom_id
      (C := CanonicalModules X) ((forgetBespoke X).obj F)
        (𝟙_ (CanonicalModules X))
    simp only [hId]
    exact comparison_rightUnitor F

/-- A left snake identity for the chosen tensor product of scheme modules implies
the right snake identity after tensoring on the left by an arbitrary module. -/
theorem tensorPairing_right_triangle_of_left_whiskered
    (F N D : X.Modules)
    (coev : tensor N D ≅ SheafOfModules.unit X.ringCatSheaf)
    (ev : tensor D N ≅ SheafOfModules.unit X.ringCatSheaf)
    (h : (tensorLeftUnitIso N).inv ≫ tensorMapLeft coev.inv N ≫
      (tensorAssocIso N D N).hom ≫ tensorMapRight N ev.hom ≫
      (tensorUnitIso N).hom = 𝟙 N) :
    let B := tensor F D
    let cancel := (tensorAssocIso F D N).hom ≫
      tensorMapRight F ev.hom ≫ (tensorUnitIso F).hom
    (tensorUnitIso B).inv ≫ tensorMapRight B coev.inv ≫
      (tensorAssocIso B N D).inv ≫ tensorMapLeft cancel D = 𝟙 B := by
  letI : MonoidalCategory (BespokeModules.{u, u + 1} X) :=
    Monoidal.induced (forgetBespoke X) comparisonData
  dsimp only
  let Fl : BespokeModules.{u, u + 1} X := ULift.up F
  let Nl : BespokeModules.{u, u + 1} X := ULift.up N
  let Dl : BespokeModules.{u, u + 1} X := ULift.up D
  let coevl : Nl ⊗ Dl ≅ 𝟙_ (BespokeModules.{u, u + 1} X) :=
    InducedCategory.isoMk coev
  let evl : Dl ⊗ Nl ≅ 𝟙_ (BespokeModules.{u, u + 1} X) :=
    InducedCategory.isoMk ev
  have hl :
      (λ_ Nl).inv ≫ coevl.inv ▷ Nl ≫ (α_ Nl Dl Nl).hom ≫
        Nl ◁ evl.hom ≫ (ρ_ Nl).hom = 𝟙 Nl := by
    apply InducedCategory.hom_ext
    exact h
  have hr := CategoryTheory.isoPairing_right_triangle_of_left_whiskered
    Fl Nl Dl coevl evl hl
  dsimp only at hr
  have hrhom := congrArg (fun k ↦ InducedCategory.Hom.hom k) hr
  exact hrhom

end AlgebraicGeometry.Scheme.Modules
