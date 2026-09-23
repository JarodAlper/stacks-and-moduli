module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Core
public import StacksAndModuli.API.PseudofunctorStack

/-!
# The core of a category-valued pseudofunctor

This file constructs the pseudofunctor obtained by taking the core of every value of a
category-valued pseudofunctor on a locally discrete bicategory. Its values are groupoids:
it keeps all objects and only the isomorphisms between them.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Pseudofunctor

open Bicategory

universe v v' u u'

variable {C : Type u} [Category.{v} C]

@[simp]
lemma _root_.CategoryTheory.Core.eqToHom_iso_hom {X Y : Core C} (h : X = Y) :
    (eqToHom h : X ⟶ Y).iso.hom = eqToHom (congrArg Core.of h) := by
  subst h
  rfl

@[simp]
lemma _root_.CategoryTheory.Core.isoMk_hom_iso_hom {X Y : Core C}
    (e : X.of ≅ Y.of) : (Core.isoMk e).hom.iso.hom = e.hom := by
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The pointwise core of a category-valued pseudofunctor. -/
def core (F : LocallyDiscrete C ⥤ᵖ Cat.{v', u'}) :
    LocallyDiscrete C ⥤ᵖ Cat.{v', u'} :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (Core (F.obj ⟨X⟩)))
    (fun f ↦ (F.map f.toLoc).toFunctor.core.toCatHom)
    (fun X ↦ Cat.Hom.isoMk ((Cat.Hom.toNatIso (F.mapId ⟨X⟩)).core))
    (fun f g ↦ Cat.Hom.isoMk ((Cat.Hom.toNatIso (F.mapComp f.toLoc g.toLoc)).core))
    (fun f g h ↦ by
      apply Cat.Hom₂.ext
      ext X
      apply Core.hom_ext
      dsimp
      simp only [Cat.Hom.isoMk_hom, Cat.Hom.isoMk_inv,
        NatTrans.toCatHom₂_toNatTrans, Iso.core_hom_app_iso_hom,
        Iso.core_inv_app_iso_hom, Cat.Hom.toNatIso_hom, Cat.Hom.toNatIso_inv,
        Functor.core_map_iso_hom]
      simp
      have H := congrArg (fun k ↦ k.toNatTrans.app X.of)
        (F.map₂_associator f.toLoc g.toLoc h.toLoc)
      rw [show (α_ f.toLoc g.toLoc h.toLoc).hom = eqToHom (by simp) from
        Subsingleton.elim _ _, PrelaxFunctor.map₂_eqToHom] at H
      dsimp at H
      convert H.symm using 1 <;>
        simp [Functor.core, Core.functorToCore, Cat.Hom₂.eqToHom_toNatTrans,
          CategoryTheory.eqToHom_app, Core.inclusion])
    (fun f ↦ by
      apply Cat.Hom₂.ext
      ext X
      apply Core.hom_ext
      dsimp
      simp only [Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans,
        Iso.core_hom_app_iso_hom, Cat.Hom.toNatIso_hom,
        Functor.core_map_iso_hom, Category.comp_id]
      simp
      have H := congrArg (fun k ↦ k.toNatTrans.app X.of)
        (F.map₂_left_unitor f.toLoc)
      rw [show (λ_ f.toLoc).hom = eqToHom (by simp) from Subsingleton.elim _ _,
        PrelaxFunctor.map₂_eqToHom] at H
      dsimp at H
      convert H.symm using 1 <;>
        simp [Functor.core, Core.functorToCore, Cat.Hom₂.eqToHom_toNatTrans,
          CategoryTheory.eqToHom_app, Core.inclusion])
    (fun f ↦ by
      apply Cat.Hom₂.ext
      ext X
      apply Core.hom_ext
      dsimp
      simp only [Cat.Hom.isoMk_hom, NatTrans.toCatHom₂_toNatTrans,
        Iso.core_hom_app_iso_hom, Cat.Hom.toNatIso_hom, Category.comp_id]
      simp
      have H := congrArg (fun k ↦ k.toNatTrans.app X.of)
        (F.map₂_right_unitor f.toLoc)
      rw [show (ρ_ f.toLoc).hom = eqToHom (by simp) from Subsingleton.elim _ _,
        PrelaxFunctor.map₂_eqToHom] at H
      dsimp at H
      convert H.symm using 1 <;>
        simp [Functor.core, Core.functorToCore, Cat.Hom₂.eqToHom_toNatTrans,
          CategoryTheory.eqToHom_app, Core.inclusion])

@[simp]
lemma core_map_obj_of (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})
    {b₀ b₁ : LocallyDiscrete C} (f : b₀ ⟶ b₁) (X : Core (F.obj b₀)) :
    (((F.core).map f).toFunctor.obj X).of = (F.map f).toFunctor.obj X.of := rfl

@[simp]
lemma core_map_map_iso_hom (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})
    {b₀ b₁ : LocallyDiscrete C} (f : b₀ ⟶ b₁)
    {X Y : Core (F.obj b₀)} (φ : X ⟶ Y) :
    (((F.core).map f).toFunctor.map φ).iso.hom =
      (F.map f).toFunctor.map φ.iso.hom := rfl

@[simp]
lemma core_mapComp'_hom_app_iso_hom
    (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})
    {b₀ b₁ b₂ : LocallyDiscrete C} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂)
    (fg : b₀ ⟶ b₂) (h : f ≫ g = fg) (X : Core (F.obj b₀)) :
    (((F.core).mapComp' f g fg h).hom.toNatTrans.app X).iso.hom =
      (F.mapComp' f g fg h).hom.toNatTrans.app X.of := by
  subst fg
  rw [F.core.mapComp'_eq_mapComp, F.mapComp'_eq_mapComp]
  rfl

@[simp]
lemma core_mapComp'_inv_app_iso_hom
    (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})
    {b₀ b₁ b₂ : LocallyDiscrete C} (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂)
    (fg : b₀ ⟶ b₂) (h : f ≫ g = fg) (X : Core (F.obj b₀)) :
    (((F.core).mapComp' f g fg h).inv.toNatTrans.app X).iso.hom =
      (F.mapComp' f g fg h).inv.toNatTrans.app X.of := by
  subst fg
  rw [F.core.mapComp'_eq_mapComp, F.mapComp'_eq_mapComp]
  rfl

namespace DescentData

open Opposite

universe t

variable {C : Type u} [Category.{v} C]
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
variable {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

@[simp]
lemma core_pullHom_iso_hom
    {X₁ X₂ : C} {M₁ : Core (F.obj (.mk (op X₁)))}
    {M₂ : Core (F.obj (.mk (op X₂)))} {Y : C} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.core.map f₁.op.toLoc).toFunctor.obj M₁ ⟶
      (F.core.map f₂.op.toLoc).toFunctor.obj M₂)
    {Y' : C} (g : Y' ⟶ Y) (gf₁ : Y' ⟶ X₁) (gf₂ : Y' ⟶ X₂)
    (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂) :
    (LocallyDiscreteOpToCat.pullHom φ g gf₁ gf₂ hgf₁ hgf₂).iso.hom =
      LocallyDiscreteOpToCat.pullHom φ.iso.hom g gf₁ gf₂ hgf₁ hgf₂ := by
  unfold LocallyDiscreteOpToCat.pullHom
  rw [coreCategory_comp_iso, coreCategory_comp_iso, Iso.trans_hom, Iso.trans_hom]
  simp only [core_mapComp'_hom_app_iso_hom, core_mapComp'_inv_app_iso_hom,
    core_map_map_iso_hom]
  rfl

/-- Forget that the objects and morphisms of a descent datum lie in pointwise cores. -/
def forgetCore (D : F.core.DescentData f) : F.DescentData f where
  obj i := (D.obj i).of
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := (D.hom q f₁ f₂ hf₁ hf₂).iso.hom
  pullHom_hom Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    have h := congrArg (fun k ↦ k.iso.hom)
      (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂)
    simpa only [core_pullHom_iso_hom] using h
  hom_self Y q i g hg := by
    have h := congrArg (fun k ↦ k.iso.hom) (D.hom_self q g hg)
    change (D.hom q g g).iso.hom = 𝟙 _ at h
    exact h

  hom_comp Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    have h := congrArg (fun k ↦ k.iso.hom)
      (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)
    change (D.hom q f₁ f₂).iso.hom ≫ (D.hom q f₂ f₃).iso.hom =
      (D.hom q f₁ f₃).iso.hom at h
    exact h

@[simp]
lemma forgetCore_hom (D : F.core.DescentData f) {Y : C} (q : Y ⟶ S)
    {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (forgetCore f D).hom q f₁ f₂ hf₁ hf₂ =
      (D.hom q f₁ f₂ hf₁ hf₂).iso.hom := rfl

/-- Forget the pointwise-core condition from a morphism of descent data. -/
def forgetCoreHom {D E : F.core.DescentData f} (φ : D ⟶ E) :
    forgetCore f D ⟶ forgetCore f E where
  hom i := (φ.hom i).iso.hom
  comm Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    have h := congrArg (fun k ↦ k.iso.hom)
      (φ.comm q f₁ f₂ hf₁ hf₂)
    rw [coreCategory_comp_iso, coreCategory_comp_iso, Iso.trans_hom, Iso.trans_hom] at h
    change (F.map f₁.op.toLoc).toFunctor.map (φ.hom i₁).iso.hom ≫
      (E.hom q f₁ f₂).iso.hom = (D.hom q f₁ f₂).iso.hom ≫
        (F.map f₂.op.toLoc).toFunctor.map (φ.hom i₂).iso.hom at h
    exact h

@[simp]
lemma forgetCoreHom_hom {D E : F.core.DescentData f} (φ : D ⟶ E) (i : ι) :
    (forgetCoreHom f φ).hom i = (φ.hom i).iso.hom := rfl

/-- A morphism of core-valued descent data becomes an isomorphism after forgetting
to the ambient categories. -/
noncomputable def forgetCoreIso {D E : F.core.DescentData f} (φ : D ⟶ E) :
    forgetCore f D ≅ forgetCore f E :=
  Pseudofunctor.DescentData.isoMk (fun i ↦ (φ.hom i).iso) (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
    exact (forgetCoreHom f φ).comm q f₁ f₂ hf₁ hf₂)

@[simp]
lemma forgetCoreIso_hom {D E : F.core.DescentData f} (φ : D ⟶ E) :
    (forgetCoreIso f φ).hom = forgetCoreHom f φ := by
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  rfl

/-- Pulling back a core object and then forgetting the core gives the usual
ambient descent datum. -/
noncomputable def ofObjForgetCoreIso (M : F.core.obj (.mk (op S))) :
    (F.toDescentData f).obj M.of ≅
      forgetCore f ((F.core.toDescentData f).obj M) :=
  Pseudofunctor.DescentData.isoMk (fun _ ↦ Iso.refl _) (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
    dsimp [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj, forgetCore]
    rw [coreCategory_comp_iso, Iso.trans_hom]
    simp only [core_mapComp'_hom_app_iso_hom, core_mapComp'_inv_app_iso_hom,
      Functor.map_id, Category.id_comp, Category.comp_id])

@[simp]
lemma ofObjForgetCoreIso_hom_hom (M : F.core.obj (.mk (op S))) (i : ι) :
    (ofObjForgetCoreIso f M).hom.hom i = 𝟙 _ := rfl

@[simp]
lemma ofObjForgetCoreIso_inv_hom (M : F.core.obj (.mk (op S))) (i : ι) :
    (ofObjForgetCoreIso f M).inv.hom i = 𝟙 _ := rfl

lemma ofObjForgetCoreIso_naturality
    {M N : F.core.obj (.mk (op S))} (φ : M ⟶ N) :
    (ofObjForgetCoreIso f M).hom ≫
        forgetCoreHom f ((F.core.toDescentData f).map φ) ≫
          (ofObjForgetCoreIso f N).inv =
      (F.toDescentData f).map φ.iso.hom := by
  apply Pseudofunctor.DescentData.hom_ext
  intro i
  simp only [Pseudofunctor.DescentData.comp_hom, ofObjForgetCoreIso_hom_hom,
    ofObjForgetCoreIso_inv_hom, forgetCoreHom_hom, Category.id_comp,
    Category.comp_id]
  rfl

@[simp]
lemma core_toDescentData_obj_hom_iso_hom
    (M : F.core.obj (.mk (op S))) {Y : C} (q : Y ⟶ S)
    {i₁ i₂ : ι} (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q) :
    (((F.core.toDescentData f).obj M).hom q f₁ f₂ hf₁ hf₂).iso.hom =
      ((F.toDescentData f).obj M.of).hom q f₁ f₂ hf₁ hf₂ := by
  dsimp [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj]
  rw [coreCategory_comp_iso, Iso.trans_hom]
  simp only [core_mapComp'_inv_app_iso_hom, core_mapComp'_hom_app_iso_hom]

/-- Descent for morphisms passes from a category-valued pseudofunctor to its
pointwise core. -/
noncomputable def fullyFaithfulToDescentData
    (hF : (F.toDescentData f).FullyFaithful) :
    (F.core.toDescentData f).FullyFaithful where
  preimage {M N} φ := by
    let φ₁ := forgetCoreHom f φ
    letI : IsIso φ₁ := by
      rw [show φ₁ = (forgetCoreIso f φ).hom from
        (forgetCoreIso_hom f φ).symm]
      infer_instance
    let φ₀ := (ofObjForgetCoreIso f M).hom ≫ φ₁ ≫
      (ofObjForgetCoreIso f N).inv
    letI : IsIso φ₀ := inferInstance
    haveI : IsIso ((F.toDescentData f).map (hF.preimage φ₀)) := by
      rw [hF.map_preimage]
      infer_instance
    letI : IsIso (hF.preimage φ₀) := hF.isIso_of_isIso_map _
    exact CoreHom.mk (asIso (hF.preimage φ₀))
  map_preimage {M N} φ := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    apply Core.hom_ext
    simpa only [Pseudofunctor.toDescentData_map_hom, core_map_map_iso_hom, asIso_hom,
      Pseudofunctor.DescentData.comp_hom,
      ofObjForgetCoreIso_hom_hom, ofObjForgetCoreIso_inv_hom,
      forgetCoreHom_hom, Category.id_comp, Category.comp_id] using
      congrArg (fun k ↦ k.hom i)
      (hF.map_preimage ((ofObjForgetCoreIso f M).hom ≫ forgetCoreHom f φ ≫
        (ofObjForgetCoreIso f N).inv))
  preimage_map {M N} φ := by
    apply Core.hom_ext
    change hF.preimage ((ofObjForgetCoreIso f M).hom ≫
      forgetCoreHom f ((F.core.toDescentData f).map φ) ≫
        (ofObjForgetCoreIso f N).inv) = φ.iso.hom
    rw [ofObjForgetCoreIso_naturality]
    exact hF.preimage_map φ.iso.hom

/-- Effective descent for objects passes from a category-valued pseudofunctor to
its pointwise core. -/
theorem essSurjToDescentData
    (hF : (F.toDescentData f).EssSurj) :
    (F.core.toDescentData f).EssSurj where
  mem_essImage D := by
    let D₀ : F.DescentData f := forgetCore f D
    let M := (F.toDescentData f).objPreimage D₀
    let e : (F.toDescentData f).obj M ≅ D₀ :=
      (F.toDescentData f).objObjPreimageIso D₀
    let MP : F.core.obj (.mk (op S)) := ⟨M⟩
    let eP : (F.core.toDescentData f).obj MP ≅ D :=
      Pseudofunctor.DescentData.isoMk
        (fun i ↦ Core.isoMk
          { hom := e.hom.hom i
            inv := e.inv.hom i
            hom_inv_id := congrArg (fun k ↦ k.hom i) e.hom_inv_id
            inv_hom_id := congrArg (fun k ↦ k.hom i) e.inv_hom_id })
        (fun Y q i₁ i₂ f₁ f₂ hf₁ hf₂ ↦ by
          apply Core.hom_ext
          rw [coreCategory_comp_iso, coreCategory_comp_iso, Iso.trans_hom, Iso.trans_hom]
          simpa only [D₀, MP, forgetCore_hom, core_toDescentData_obj_hom_iso_hom,
            Core.isoMk_hom_iso_hom, core_map_map_iso_hom,
            core_mapComp'_inv_app_iso_hom,
            core_mapComp'_hom_app_iso_hom] using
            e.hom.comm q f₁ f₂ hf₁ hf₂)
    exact ⟨MP, ⟨eP⟩⟩

end DescentData

universe t

variable {C : Type u} [Category.{v} C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

/-- Taking the pointwise core of a category-valued stack again gives a stack. -/
theorem core_isStack {J : GrothendieckTopology C} [F.IsStack J] : F.core.IsStack J := by
  apply Pseudofunctor.IsStack.of_isStackFor
  intro S R hR
  rw [Pseudofunctor.isStackFor_iff]
  let f : ∀ q : R.arrows.category, q.obj.left ⟶ S := fun q ↦ q.obj.hom
  change (F.core.toDescentData f).IsEquivalence
  have hf : Sieve.ofArrows (fun q : R.arrows.category ↦ q.obj.left) f = R := by
    rw [Sieve.ofArrows_category']
    simp
  have hRf : Sieve.ofArrows (fun q : R.arrows.category ↦ q.obj.left) f ∈ J S := by
    rwa [hf]
  exact
    { faithful := (DescentData.fullyFaithfulToDescentData f
        (F.fullyFaithfulToDescentData f hRf)).faithful
      full := (DescentData.fullyFaithfulToDescentData f
        (F.fullyFaithfulToDescentData f hRf)).full
      essSurj := DescentData.essSurjToDescentData f (by
        have hstack : F.IsStackFor R.arrows := F.isStackFor _ (by simpa)
        exact hstack.essSurj) }

end CategoryTheory.Pseudofunctor
