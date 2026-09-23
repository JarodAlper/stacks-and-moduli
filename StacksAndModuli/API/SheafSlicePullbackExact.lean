module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Exact extension from a slice site

For an object `U` of a small category, the pointwise left Kan extension along
`(Over.forget U).op` is a coproduct indexed by arrows into `U`.  This file makes that
description precise by exhibiting the identity factorizations as a final discrete
subcategory.  Since coproducts of abelian groups preserve monomorphisms, extension
from the slice site preserves monomorphisms, both for presheaves and after
sheafification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (U V : C)

/-- The composite arrow represented by a factorization occurring in the pointwise
left Kan extension along the opposite of a slice forgetful functor. -/
def Over.factorizationComposite
    (c : CostructuredArrow (Over.forget U).op (Opposite.op V)) : V ⟶ U :=
  c.hom.unop ≫ (Opposite.unop c.left).hom

/-- The identity factorization of an arrow into the slice vertex. -/
def Over.identityFactorization (f : V ⟶ U) :
    CostructuredArrow (Over.forget U).op (Opposite.op V) :=
  CostructuredArrow.mk (Y := Opposite.op (Over.mk f)) (𝟙 (Opposite.op V))

@[simp]
lemma Over.factorizationComposite_identityFactorization (f : V ⟶ U) :
    Over.factorizationComposite U V (Over.identityFactorization U V f) = f := by
  change 𝟙 V ≫ f = f
  simp

/-- Send a factorization to its composite arrow. -/
def Over.factorizationCompositeFunctor :
    CostructuredArrow (Over.forget U).op (Opposite.op V) ⥤ Discrete (V ⟶ U) where
  obj c := Discrete.mk (Over.factorizationComposite U V c)
  map {c c'} φ := Discrete.eqToHom (by
    change Over.factorizationComposite U V c = Over.factorizationComposite U V c'
    have h₁ := congrArg Opposite.unop (CostructuredArrow.w φ)
    have h₂ := Over.w φ.left.unop
    dsimp [Over.factorizationComposite] at h₁ h₂ ⊢
    change c'.hom.unop ≫ φ.left.unop.left = c.hom.unop at h₁
    calc
      c.hom.unop ≫ (Opposite.unop c.left).hom =
          (c'.hom.unop ≫ φ.left.unop.left) ≫ (Opposite.unop c.left).hom := by
            exact congrArg (fun k ↦ k ≫ (Opposite.unop c.left).hom) h₁.symm
      _ = c'.hom.unop ≫ (φ.left.unop.left ≫ (Opposite.unop c.left).hom) :=
        Category.assoc _ _ _
      _ = c'.hom.unop ≫ (Opposite.unop c'.left).hom := by
        exact congrArg (fun k ↦ c'.hom.unop ≫ k) h₂)

/-- Include composite arrows as their identity factorizations. -/
def Over.identityFactorizationFunctor :
    Discrete (V ⟶ U) ⥤ CostructuredArrow (Over.forget U).op (Opposite.op V) :=
  Discrete.functor fun f ↦ Over.identityFactorization U V f

@[simp]
lemma Over.factorizationCompositeFunctor_obj_identityFactorizationFunctor (f : Discrete (V ⟶ U)) :
    (Over.factorizationCompositeFunctor U V).obj
      ((Over.identityFactorizationFunctor U V).obj f) = f := by
  apply Discrete.ext
  simp [Over.factorizationCompositeFunctor, Over.identityFactorizationFunctor]

/-- Every factorization maps canonically to the identity factorization of its composite. -/
def Over.toIdentityFactorization
    (c : CostructuredArrow (Over.forget U).op (Opposite.op V)) :
    c ⟶ (Over.identityFactorizationFunctor U V).obj
      ((Over.factorizationCompositeFunctor U V).obj c) :=
  CostructuredArrow.homMk
    (Over.homMk c.hom.unop (by rfl)).op
    (by
      change c.hom ≫ 𝟙 _ = c.hom
      exact Category.comp_id _)

instance Over.subsingleton_hom_identityFactorization
    (c : CostructuredArrow (Over.forget U).op (Opposite.op V)) (f : V ⟶ U) :
    Subsingleton (c ⟶ Over.identityFactorization U V f) where
  allEq a b := by
    apply CostructuredArrow.hom_ext
    have hab : a.left.unop = b.left.unop := by
      apply Over.OverMorphism.ext
      have ha : a.left.unop.left = c.hom.unop := by
        apply Opposite.op_injective
        change (Over.forget U).op.map a.left = c.hom
        have h := CostructuredArrow.w a
        change (Over.forget U).op.map a.left ≫ 𝟙 _ = c.hom at h
        simpa only [Category.comp_id] using h
      have hb : b.left.unop.left = c.hom.unop := by
        apply Opposite.op_injective
        change (Over.forget U).op.map b.left = c.hom
        have h := CostructuredArrow.w b
        change (Over.forget U).op.map b.left ≫ 𝟙 _ = c.hom at h
        simpa only [Category.comp_id] using h
      exact ha.trans hb.symm
    exact congrArg Quiver.Hom.op hab

/-- The composite of an identity factorization, regarded as a morphism in the
discrete indexing category. -/
def Over.identityFactorizationCounit (f : Discrete (V ⟶ U)) :
    (Over.factorizationCompositeFunctor U V).obj
        ((Over.identityFactorizationFunctor U V).obj f) ⟶ f :=
  Discrete.eqToHom (by
    exact Over.factorizationComposite_identityFactorization U V f.as)

/-- Identity factorizations are right adjoint to the composite functor. -/
def Over.factorizationAdjunction :
    Over.factorizationCompositeFunctor U V ⊣ Over.identityFactorizationFunctor U V :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun c f ↦
        { toFun := fun a ↦ Over.toIdentityFactorization U V c ≫
              (Over.identityFactorizationFunctor U V).map a
          invFun := fun a ↦ (Over.factorizationCompositeFunctor U V).map a ≫
              Over.identityFactorizationCounit U V f
          left_inv := fun _ ↦ Subsingleton.elim _ _
          right_inv := fun _ ↦
            @Subsingleton.elim _
              (Over.subsingleton_hom_identityFactorization U V c f.as) _ _ }
      homEquiv_naturality_left_symm := by
        intros
        apply Subsingleton.elim
      homEquiv_naturality_right := by
        intro c f f' a b
        exact @Subsingleton.elim _
          (Over.subsingleton_hom_identityFactorization U V c f'.as) _ _ }

instance Over.identityFactorizationFunctor_final :
    (Over.identityFactorizationFunctor U V).Final :=
  Functor.final_of_adjunction (Over.factorizationAdjunction U V)

section LanNaturality

variable {D H : Type*} [Category* D] [Category* H]
  (L : C ⥤ D) [∀ (F : C ⥤ H), L.HasPointwiseLeftKanExtension F]

set_option backward.isDefEq.respectTransparency false in
/-- The pointwise-colimit description of left Kan extension is natural in the
presheaf being extended. -/
lemma Functor.leftKanExtensionObjIsoColimit_naturality
    {F G : C ⥤ H} (a : F ⟶ G) (X : D) :
    (L.leftKanExtensionObjIsoColimit F X).inv ≫ (L.lan.map a).app X ≫
        (L.leftKanExtensionObjIsoColimit G X).hom =
      colimMap (whiskerLeft (CostructuredArrow.proj L X) a) := by
  apply colimit.hom_ext
  intro c
  simp only [Functor.ι_leftKanExtensionObjIsoColimit_inv_assoc,
    ι_colimMap]
  rw [NatTrans.naturality_assoc]
  have h := congr_app (L.lanUnit.naturality a) c.left
  dsimp at h ⊢
  change a.app c.left ≫ (L.leftKanExtensionUnit G).app c.left =
    (L.leftKanExtensionUnit F).app c.left ≫
      (L.lan.map a).app (L.obj c.left) at h
  rw [← reassoc_of% h]
  apply congrArg (fun k ↦ a.app c.left ≫ k)
  exact Functor.ι_leftKanExtensionObjIsoColimit_hom L G X c

end LanNaturality

section AddCommGrp

variable {I : Type u} {J : Type u} [SmallCategory J]

/-- A colimit map of abelian groups is monic when it becomes a coproduct of
monomorphisms after restriction along a final functor from a discrete category. -/
lemma colimMap_mono_of_final_discrete (k : Discrete I ⥤ J) [k.Final]
    {F G : J ⥤ AddCommGrpCat.{u}} (a : F ⟶ G) [Mono a] :
    Mono (colimMap a) := by
  let _ (X : Discrete I) : Mono ((Functor.whiskerLeft k a).app X) := by
    change Mono (a.app (k.obj X))
    infer_instance
  let _ : Mono (Functor.whiskerLeft k a) := NatTrans.mono_of_mono_app _
  let _ : Mono (colimMap (Functor.whiskerLeft k a)) := by
    rw [colimMap_eq]
    infer_instance
  have hpre := colimit.pre_map a k
  have h : colimMap a = inv (colimit.pre F k) ≫
      colimMap (Functor.whiskerLeft k a) ≫ colimit.pre G k := by
    rw [← cancel_epi (colimit.pre F k)]
    simp only [IsIso.hom_inv_id_assoc]
    exact hpre
  rw [h]
  infer_instance

end AddCommGrp

section SliceLan

variable {C : Type u} [SmallCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Left Kan extension along the opposite of a slice forgetful functor preserves
monomorphisms of abelian-group-valued presheaves. -/
noncomputable instance Over.forgetOp_lan_preservesMonomorphisms (U : C) :
    ((Over.forget U).op.lan :
      ((Over U)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u})).PreservesMonomorphisms where
  preserves {F G} a _ := by
    let _ (X : Cᵒᵖ) : Mono (((Over.forget U).op.lan.map a).app X) := by
      obtain ⟨V⟩ := X
      let L := (Over.forget U).op
      let aX := Functor.whiskerLeft (CostructuredArrow.proj L (Opposite.op V)) a
      let _ (c : CostructuredArrow L (Opposite.op V)) : Mono (aX.app c) := by
        change Mono (a.app c.left)
        infer_instance
      let _ : Mono aX := NatTrans.mono_of_mono_app _
      have hc : Mono (colimMap aX) :=
        colimMap_mono_of_final_discrete (Over.identityFactorizationFunctor U V) aX
      let eF := L.leftKanExtensionObjIsoColimit F (Opposite.op V)
      let eG := L.leftKanExtensionObjIsoColimit G (Opposite.op V)
      have hnat := Functor.leftKanExtensionObjIsoColimit_naturality L a (Opposite.op V)
      have hm : ((Over.forget U).op.lan.map a).app (Opposite.op V) =
          eF.hom ≫ colimMap aX ≫ eG.inv := by
        rw [← cancel_epi eF.inv, ← cancel_mono eG.hom]
        simpa [aX, eF, eG, L] using hnat
      let _ : Mono (colimMap aX) := hc
      rw [hm]
      infer_instance
    exact NatTrans.mono_of_mono_app _

end SliceLan

section SliceSheafPullback

variable {C : Type u} [SmallCategory C]
  (J : GrothendieckTopology C) (U : C)
  [HasSheafify J AddCommGrpCat.{u}]

/-- The left-Kan-extension construction of extension from a slice site preserves
monomorphisms of abelian sheaves. -/
noncomputable instance Over.forget_sheafPullbackConstruction_preservesMonomorphisms :
    (Functor.sheafPullbackConstruction.sheafPullback (Over.forget U)
      AddCommGrpCat.{u} (J.over U) J).PreservesMonomorphisms := by
  dsimp only [Functor.sheafPullbackConstruction.sheafPullback]
  infer_instance

/-- Extension from a slice site preserves monomorphisms of abelian sheaves. -/
noncomputable instance Over.forget_sheafPullback_preservesMonomorphisms :
    ((Over.forget U).sheafPullback AddCommGrpCat.{u}
      (J.over U) J).PreservesMonomorphisms :=
  Functor.PreservesMonomorphisms.of_iso
    (Functor.sheafPullbackConstruction.sheafPullbackIso
      (Over.forget U) AddCommGrpCat.{u} (J.over U) J).symm

end SliceSheafPullback

end CategoryTheory
