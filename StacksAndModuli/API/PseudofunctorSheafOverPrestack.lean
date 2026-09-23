module

public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Morphism descent for sheaves on over-sites

The pseudofunctor sending an object `S` to sheaves on the induced site
`C / S` is a prestack.  The proof compares its morphism presheaves with the
ordinary internal Hom sheaves on `C / S`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

universe v' u' v u

namespace CategoryTheory.GrothendieckTopology

open Bicategory

/-- The compositor of `pseudofunctorOver` on a syntactically canonical composite is the
usual composition isomorphism for restriction of sheaves.  This normalization lemma is
useful before handling the equality transport in `Pseudofunctor.mapComp'`. -/
lemma pseudofunctorOver_mapComp'_eq_overMapPullbackComp
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type u') [Category.{v'} A] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (J.pseudofunctorOver A).mapComp' g.op.toLoc f.op.toLoc
      (g.op.toLoc ≫ f.op.toLoc) rfl =
        Cat.Hom.isoMk (J.overMapPullbackComp A f g).symm := by
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- The two descriptions of the category over an arrow `T : Over S` give naturally
isomorphic functors to `Over S`: first pass through the iterated slice equivalence and
then compose with `T.hom`, or simply forget the map to `T`.

This is the categorical comparison needed to identify the morphism presheaf of
`J.pseudofunctorOver A` with the usual internal Hom presheaf. -/
def iteratedSliceForwardOverMapOpIso {C : Type u} [Category.{v} C] {S : C}
    (T : Over S) :
    T.iteratedSliceForward.op ⋙ (Over.map T.hom).op ≅ (Over.forget T).op :=
  NatIso.ofComponents
    (fun U ↦
      (Over.isoMk
        (f := (Over.forget T).obj U.unop)
        (g := (Over.map T.hom).obj (T.iteratedSliceForward.obj U.unop))
        (Iso.refl _) (by simp)).op)
    (by
      rintro ⟨U⟩ ⟨V⟩ ⟨f⟩
      apply Quiver.Hom.unop_inj
      ext
      simp)

@[simp]
lemma iteratedSliceForwardOverMapOpIso_hom_app_unop_left
    {C : Type u} [Category.{v} C] {S : C} (T : Over S) (U : (Over T)ᵒᵖ) :
    ((iteratedSliceForwardOverMapOpIso T).hom.app U).unop.left = 𝟙 _ :=
  rfl

@[simp]
lemma iteratedSliceForwardOverMapOpIso_inv_app_unop_left
    {C : Type u} [Category.{v} C] {S : C} (T : Over S) (U : (Over T)ᵒᵖ) :
    ((iteratedSliceForwardOverMapOpIso T).inv.app U).unop.left = 𝟙 _ :=
  rfl

/-- Restriction along `T.hom` followed by the iterated-slice equivalence agrees with
restriction along the forgetful functor from `Over T`. -/
def iteratedSliceRestrictionIso
    {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] {S : C}
    (T : Over S) (F : (Over S)ᵒᵖ ⥤ A) :
    T.iteratedSliceForward.op ⋙ ((Over.map T.hom).op ⋙ F) ≅ (Over.forget T).op ⋙ F :=
  (Functor.associator _ _ F).symm.trans
    (Functor.isoWhiskerRight (iteratedSliceForwardOverMapOpIso T) F)

@[simp]
lemma iteratedSliceRestrictionIso_hom_app
    {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] {S : C}
    (T : Over S) (F : (Over S)ᵒᵖ ⥤ A) (U : (Over T)ᵒᵖ) :
    (iteratedSliceRestrictionIso T F).hom.app U =
      F.map ((iteratedSliceForwardOverMapOpIso T).hom.app U) := by
  simp [iteratedSliceRestrictionIso]

@[simp]
lemma iteratedSliceRestrictionIso_inv_app
    {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A] {S : C}
    (T : Over S) (F : (Over S)ᵒᵖ ⥤ A) (U : (Over T)ᵒᵖ) :
    (iteratedSliceRestrictionIso T F).inv.app U =
      F.map ((iteratedSliceForwardOverMapOpIso T).inv.app U) := by
  simp [iteratedSliceRestrictionIso]

/-- At an arrow `T : Over S`, the Hom type in the pseudofunctor of sheaves is
canonically equivalent to the value at `T` of the ordinary internal Hom presheaf on
`Over S`.

The only non-definitional step is the equivalence
`Over T ≃ Over T.left`; after precomposition by its forward functor, the two restricted
underlying presheaves agree up to `iteratedSliceForwardOverMapOpIso`. -/
noncomputable def pseudofunctorOverPresheafHomObjEquiv
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type u') [Category.{v'} A] {S : C} (M N : Sheaf (J.over S) A) (T : Over S) :
    ((J.pseudofunctorOver A).presheafHom M N).obj (op T) ≃
      (presheafHom M.obj N.obj).obj (op T) := by
  let _ : T.iteratedSliceForward.op.IsEquivalence :=
    Equivalence.isEquivalence_functor T.iteratedSliceEquiv.op
  refine Sheaf.homEquiv.trans
    (((Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringLeft (Over T)ᵒᵖ (Over T.left)ᵒᵖ A).obj
        T.iteratedSliceForward.op)).homEquiv
          (X := (Over.map T.hom).op ⋙ M.obj)
          (Y := (Over.map T.hom).op ⋙ N.obj)).trans ?_)
  exact Iso.homCongr
    (iteratedSliceRestrictionIso T M.obj)
    (iteratedSliceRestrictionIso T N.obj)

@[simp]
lemma pseudofunctorOverPresheafHomObjEquiv_apply
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type u') [Category.{v'} A] {S : C} (M N : Sheaf (J.over S) A) (T : Over S)
    (f : ((J.pseudofunctorOver A).presheafHom M N).obj (op T)) :
    pseudofunctorOverPresheafHomObjEquiv J A M N T f =
      Iso.homCongr
        (iteratedSliceRestrictionIso T M.obj)
        (iteratedSliceRestrictionIso T N.obj)
        (Functor.whiskerLeft T.iteratedSliceForward.op f.hom) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
lemma pseudofunctorOver_source_transport
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type u') [Category.{v'} A] {S : C} (M : Sheaf (J.over S) A)
    {T U : Over S} (f : U ⟶ T) (V : (Over U)ᵒᵖ) :
    M.obj.map ((iteratedSliceForwardOverMapOpIso U).inv.app V) ≫
      (U.iteratedSliceForward.op.whiskerLeft
        (((J.pseudofunctorOver A).mapComp'
          T.hom.op.toLoc f.left.op.toLoc U.hom.op.toLoc
          (by
            change (f.left ≫ T.hom).op.toLoc = _
            rw [Over.w f])).hom.toNatTrans.app M).hom).app V =
    ((Over.map f).op.whiskerLeft
      (Functor.whiskerRight
        (iteratedSliceForwardOverMapOpIso T).inv M.obj ≫
       (T.iteratedSliceForward.op.associator
         (Over.map T.hom).op M.obj).hom)).app V := by
  simp only [Pseudofunctor.mapComp', Iso.trans_hom,
    Cat.Hom₂.comp_app, PrelaxFunctor.map₂Iso_eqToIso]
  simp only [Functor.op_obj, Over.forget_obj,
    pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
    Cat.Hom.comp_toFunctor, Functor.comp_obj, Over.iteratedSliceForward_obj,
    pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
    Quiver.Hom.toLoc_as, Quiver.Hom.unop_op, eqToIso.hom,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom,
    Functor.whiskerLeft_comp, NatTrans.comp_app, LocallyDiscrete.comp_as,
    unop_comp, Functor.whiskerLeft_app,
    pseudofunctorOver_mapComp_hom_toNatTrans_app_hom_app,
    Over.map_obj_left, Over.map_obj_hom, Over.comp_left,
    Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id]
  rw [← eqToHom_map]
  · rw [← M.obj.map_comp, ← M.obj.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    ext
    simp [iteratedSliceForwardOverMapOpIso, Over.mapComp]
  · apply congrArg op
    rw [← Over.w f]

set_option backward.defeqAttrib.useBackward true in
lemma pseudofunctorOver_target_transport
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type u') [Category.{v'} A] {S : C} (N : Sheaf (J.over S) A)
    {T U : Over S} (f : U ⟶ T) (V : (Over U)ᵒᵖ) :
    (U.iteratedSliceForward.op.whiskerLeft
      (((J.pseudofunctorOver A).mapComp'
        T.hom.op.toLoc f.left.op.toLoc U.hom.op.toLoc
        (by
          change (f.left ≫ T.hom).op.toLoc = _
          rw [Over.w f])).inv.toNatTrans.app N).hom).app V ≫
      N.obj.map ((iteratedSliceForwardOverMapOpIso U).hom.app V) =
    ((Over.map f).op.whiskerLeft
      ((T.iteratedSliceForward.op.associator
          (Over.map T.hom).op N.obj).inv ≫
        Functor.whiskerRight
          (iteratedSliceForwardOverMapOpIso T).hom N.obj)).app V := by
  simp only [Pseudofunctor.mapComp', Iso.trans_inv,
    Cat.Hom₂.comp_app, PrelaxFunctor.map₂Iso_eqToIso]
  simp only [Functor.op_obj, Over.forget_obj,
    pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_obj_α,
    Cat.Hom.comp_toFunctor, Functor.comp_obj, Over.iteratedSliceForward_obj,
    pseudofunctorOver_toPrelaxFunctor_toPrelaxFunctorStruct_toPrefunctor_map_toFunctor_obj_obj_obj,
    Quiver.Hom.toLoc_as, Quiver.Hom.unop_op, eqToIso.inv,
    Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom,
    Functor.whiskerLeft_comp, NatTrans.comp_app, LocallyDiscrete.comp_as,
    unop_comp, Functor.whiskerLeft_app,
    pseudofunctorOver_mapComp_inv_toNatTrans_app_hom_app,
    Over.map_obj_left, Over.map_obj_hom, Over.comp_left,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp]
  rw [← eqToHom_map]
  · rw [← N.obj.map_comp, ← N.obj.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    ext
    simp [iteratedSliceForwardOverMapOpIso, Over.mapComp]
  · apply congrArg op
    rw [← Over.w f]

set_option backward.defeqAttrib.useBackward true in
lemma pseudofunctorOverPresheafHomObjEquiv_naturality
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type u') [Category.{v'} A] {S : C} (M N : Sheaf (J.over S) A)
    {T U : Over S} (f : U ⟶ T)
    (α : ((J.pseudofunctorOver A).presheafHom M N).obj (op T)) :
    pseudofunctorOverPresheafHomObjEquiv J A M N U
        (((J.pseudofunctorOver A).presheafHom M N).map (op f) α) =
      (presheafHom M.obj N.obj).map (op f)
        (pseudofunctorOverPresheafHomObjEquiv J A M N T α) := by
  rw [pseudofunctorOverPresheafHomObjEquiv_apply,
      pseudofunctorOverPresheafHomObjEquiv_apply]
  simp only [Iso.homCongr_apply]
  apply NatTrans.ext
  funext V
  have hα :
      (ConcreteCategory.hom
        (((J.pseudofunctorOver A).presheafHom M N).map (op f)) α).hom =
        (((J.pseudofunctorOver A).mapComp'
          T.hom.op.toLoc f.left.op.toLoc U.hom.op.toLoc _).hom.toNatTrans.app M).hom ≫
        (((J.pseudofunctorOver A).map f.left.op.toLoc).toFunctor.map α).hom ≫
        (((J.pseudofunctorOver A).mapComp'
          T.hom.op.toLoc f.left.op.toLoc U.hom.op.toLoc _).inv.toNatTrans.app N).hom := rfl
  simp only [NatTrans.comp_app, iteratedSliceRestrictionIso_inv_app,
    iteratedSliceRestrictionIso_hom_app]
  rw [hα]
  simp only [Functor.whiskerLeft_comp, NatTrans.comp_app]
  dsimp only [Pseudofunctor.presheafHom,
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom, presheafHom]
  simp only [← Category.assoc]
  rw [pseudofunctorOver_source_transport J A M f V]
  rw [Category.assoc]
  rw [pseudofunctorOver_target_transport J A N f V]
  rfl

/-- The objectwise internal-Hom comparison is natural in `Over S`. -/
noncomputable def pseudofunctorOverPresheafHomIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type u') [Category.{v'} A] {S : C} (M N : Sheaf (J.over S) A) :
    (J.pseudofunctorOver A).presheafHom M N ≅ presheafHom M.obj N.obj :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso
      (pseudofunctorOverPresheafHomObjEquiv J A M N T.unop)) (by
      rintro ⟨T⟩ ⟨U⟩ ⟨f⟩
      ext α
      exact pseudofunctorOverPresheafHomObjEquiv_naturality J A M N f α)

/-- Sheaves on slice sites satisfy descent for morphisms. -/
instance pseudofunctorOver_isPrestack
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (A : Type u') [Category.{v'} A] :
    (J.pseudofunctorOver A).IsPrestack J where
  isSheaf M N :=
    (Presheaf.isSheaf_of_iso_iff
      (pseudofunctorOverPresheafHomIso J A M N)).2 (N.property.hom (F := M.obj))

end CategoryTheory.GrothendieckTopology

