module

public import StacksAndModuli.API.PrestackProducts

/-!
# Reassembly of morphisms into products of based categories

Every based functor into a product is canonically isomorphic to the product lift of its
two projections. This is the objectwise uniqueness part of the product universal property,
packaged for reuse in prestack arguments.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedCategory

variable {S : Type u₁} [Category.{v₁} S]
  {T : BasedCategory.{v₄, u₄} S}
  {X : BasedCategory.{v₂, u₂} S}
  {Y : BasedCategory.{v₃, u₃} S}

/-- Rebuild a functor into a product from its two projections. -/
abbrev prodLiftProjections (F : T ⥤ᵇ prod X Y) : T ⥤ᵇ prod X Y :=
  prodLift (F.comp (fiberProductFst X.toBase Y.toBase))
    (F.comp (fiberProductSnd X.toBase Y.toBase))

/-- The component of the canonical reassembly isomorphism at an object. -/
def prodLiftProjectionsObjIso (F : T ⥤ᵇ prod X Y) (t : T.obj) :
    (prodLiftProjections F).obj t ≅ F.obj t := by
  let e₁ : ((prodLiftProjections F).obj t).fst ≅ (F.obj t).fst := eqToIso (by rfl)
  let e₂ : ((prodLiftProjections F).obj t).snd ≅ (F.obj t).snd := eqToIso (by rfl)
  apply FiberProductObj.isoMk e₁ e₂
  · change IsHomLift Y.p (X.p.map (𝟙 (F.obj t).fst)) (𝟙 (F.obj t).snd)
    rw [X.p.map_id]
    exact IsHomLift.id (F.obj t).over_eq
  · have ht : IsHomLift (base S).p (𝟙 (X.p.obj (F.obj t).fst))
        (F.obj t).iso.hom := (F.obj t).isHomLift
    have hs : IsHomLift (base S).p (𝟙 (X.p.obj (F.obj t).fst))
        ((prodLiftProjections F).obj t).iso.hom := by
      change IsHomLift (base S).p
        (𝟙 (X.p.obj ((prodLiftProjections F).obj t).fst))
        ((prodLiftProjections F).obj t).iso.hom
      exact ((prodLiftProjections F).obj t).isHomLift
    simpa [e₁, e₂] using
      (@base_hom_ext S _ (X.p.obj (F.obj t).fst) (X.p.obj (F.obj t).fst) _ _
        (F.obj t).iso.hom ((prodLiftProjections F).obj t).iso.hom ht hs)

@[simp]
lemma prodLiftProjectionsObjIso_hom_fst (F : T ⥤ᵇ prod X Y) (t : T.obj) :
    (prodLiftProjectionsObjIso F t).hom.fst = 𝟙 (F.obj t).fst := by
  change 𝟙 (F.obj t).fst = 𝟙 (F.obj t).fst
  rfl

@[simp]
lemma prodLiftProjectionsObjIso_hom_snd (F : T ⥤ᵇ prod X Y) (t : T.obj) :
    (prodLiftProjectionsObjIso F t).hom.snd = 𝟙 (F.obj t).snd := by
  change 𝟙 (F.obj t).snd = 𝟙 (F.obj t).snd
  rfl

@[simp]
lemma prodLiftProjectionsObjIso_inv_fst (F : T ⥤ᵇ prod X Y) (t : T.obj) :
    (prodLiftProjectionsObjIso F t).inv.fst = 𝟙 (F.obj t).fst := by
  change 𝟙 (F.obj t).fst = 𝟙 (F.obj t).fst
  rfl

@[simp]
lemma prodLiftProjectionsObjIso_inv_snd (F : T ⥤ᵇ prod X Y) (t : T.obj) :
    (prodLiftProjectionsObjIso F t).inv.snd = 𝟙 (F.obj t).snd := by
  change 𝟙 (F.obj t).snd = 𝟙 (F.obj t).snd
  rfl

/-- A functor into a product is canonically isomorphic to the product lift of its two
projections. -/
def prodLiftProjectionsIso (F : T ⥤ᵇ prod X Y) :
    prodLiftProjections F ≅ F :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (prodLiftProjectionsObjIso F)
      (fun {t t'} f ↦ by
        apply FiberProductHom.ext
        · change (F.map f).fst ≫ 𝟙 (F.obj t').fst =
            𝟙 (F.obj t).fst ≫ (F.map f).fst
          simp
        · change (F.map f).snd ≫ 𝟙 (F.obj t').snd =
            𝟙 (F.obj t).snd ≫ (F.map f).snd
          simp))
    (fun t ↦ FiberProductHom.isHomLift_of_fst _ (𝟙 (T.p.obj t)) (by
      change IsHomLift X.p (𝟙 (T.p.obj t)) (𝟙 (F.obj t).fst)
      rw [show T.p.obj t = X.p.obj (F.obj t).fst from
        (Functor.congr_obj F.w t).symm]
      infer_instance))

@[simp]
lemma prodLiftProjectionsIso_hom_app_fst (F : T ⥤ᵇ prod X Y) (t : T.obj) :
    ((prodLiftProjectionsIso F).hom.toNatTrans.app t).fst = 𝟙 (F.obj t).fst :=
  rfl

@[simp]
lemma prodLiftProjectionsIso_hom_app_snd (F : T ⥤ᵇ prod X Y) (t : T.obj) :
    ((prodLiftProjectionsIso F).hom.toNatTrans.app t).snd = 𝟙 (F.obj t).snd :=
  rfl

@[simp]
lemma prodLiftProjectionsIso_inv_app_fst (F : T ⥤ᵇ prod X Y) (t : T.obj) :
    ((prodLiftProjectionsIso F).inv.toNatTrans.app t).fst = 𝟙 (F.obj t).fst :=
  rfl

@[simp]
lemma prodLiftProjectionsIso_inv_app_snd (F : T ⥤ᵇ prod X Y) (t : T.obj) :
    ((prodLiftProjectionsIso F).inv.toNatTrans.app t).snd = 𝟙 (F.obj t).snd :=
  rfl

end CategoryTheory.BasedCategory
