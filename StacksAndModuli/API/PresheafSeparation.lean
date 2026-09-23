module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.LocallyInjective

/-!
# Separation of type-valued presheaves

This file constructs the reflection of type-valued presheaves into separated presheaves.
Two sections are identified when they agree on a covering sieve. The pointwise quotient is
again a presheaf, is separated, and has the expected universal property.

It also packages the plus construction on a separated presheaf as the second reflection,
from separated presheaves to sheaves. Thus the familiar two-step construction of
sheafification is expressed by two adjunctions.

Main definitions:

- `CategoryTheory.Presheaf.LocallyEqual` and `CategoryTheory.Presheaf.separation`;
- `CategoryTheory.presheafToSeparatedPresheaf` and
  `CategoryTheory.separationAdjunction`;
- `CategoryTheory.separatedPresheafToSheaf` and
  `CategoryTheory.plusSeparatedAdjunction`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Two sections of a presheaf are locally equal when their equalizer sieve is covering. -/
def LocallyEqual (J : GrothendieckTopology C) {F : Cᵒᵖ ⥤ Type w} {X : Cᵒᵖ}
    (x y : F.obj X) : Prop :=
  equalizerSieve (F := F) x y ∈ J X.unop

/-- Local equality is reflexive. -/
lemma locallyEqual_refl {F : Cᵒᵖ ⥤ Type w} {X : Cᵒᵖ}
    (x : F.obj X) : LocallyEqual J x x := by
  rw [LocallyEqual, equalizerSieve_self_eq_top]
  exact J.top_mem _

/-- Local equality is symmetric. -/
lemma locallyEqual_symm {F : Cᵒᵖ ⥤ Type w} {X : Cᵒᵖ}
    {x y : F.obj X} (h : LocallyEqual J x y) : LocallyEqual J y x := by
  change equalizerSieve (F := F) y x ∈ J X.unop
  change equalizerSieve (F := F) x y ∈ J X.unop at h
  refine J.superset_covering
    (R := equalizerSieve (F := F) y x)
    (S := equalizerSieve (F := F) x y) ?_ h
  intro Z f hf
  exact hf.symm

/-- Local equality is transitive. -/
lemma locallyEqual_trans {F : Cᵒᵖ ⥤ Type w} {X : Cᵒᵖ}
    {x y z : F.obj X} (hxy : LocallyEqual J x y) (hyz : LocallyEqual J y z) :
    LocallyEqual J x z := by
  change equalizerSieve (F := F) x z ∈ J X.unop
  change equalizerSieve (F := F) x y ∈ J X.unop at hxy
  change equalizerSieve (F := F) y z ∈ J X.unop at hyz
  apply J.superset_covering
    (S := equalizerSieve (F := F) x y ⊓ equalizerSieve (F := F) y z) ?_
    (J.intersection_covering hxy hyz)
  intro Z f hf
  exact hf.1.trans hf.2

/-- The setoid of local equality on the sections of a presheaf over one object. -/
def locallyEqualSetoid (F : Cᵒᵖ ⥤ Type w) (X : Cᵒᵖ) : Setoid (F.obj X) where
  r := LocallyEqual J
  iseqv := ⟨locallyEqual_refl J, locallyEqual_symm J, locallyEqual_trans J⟩

/-- Local equality is preserved by restriction. -/
lemma locallyEqual_map {F : Cᵒᵖ ⥤ Type w} {X Y : Cᵒᵖ} (f : X ⟶ Y)
    {x y : F.obj X} (h : LocallyEqual J x y) :
    LocallyEqual J (F.map f x) (F.map f y) := by
  change equalizerSieve (F := F) (F.map f x) (F.map f y) ∈ J Y.unop
  change equalizerSieve (F := F) x y ∈ J X.unop at h
  refine J.superset_covering
    (S := (equalizerSieve (F := F) x y).pullback f.unop) ?_
    (J.pullback_stable f.unop h)
  intro Z g hg
  change F.map g.op (F.map f x) = F.map g.op (F.map f y)
  change F.map (f ≫ g.op) x = F.map (f ≫ g.op) y at hg
  simpa only [Functor.map_comp_apply] using hg

/-- The separated presheaf obtained by quotienting sections by local equality. -/
def separation (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w where
  obj X := _root_.Quotient (locallyEqualSetoid J F X)
  map {X Y} f := ↾_root_.Quotient.map (F.map f) (by
    intro x y h
    change LocallyEqual J x y at h
    change LocallyEqual J (F.map f x) (F.map f y)
    exact locallyEqual_map J f h)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro q
    exact _root_.Quotient.inductionOn q fun x ↦
      congrArg (_root_.Quotient.mk (locallyEqualSetoid J F X))
        (ConcreteCategory.congr_hom (F.map_id X) x)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro q
    exact _root_.Quotient.inductionOn q fun x ↦
      congrArg (_root_.Quotient.mk (locallyEqualSetoid J F _))
        (Functor.map_comp_apply F f g x)

/-- Restriction in the separation presheaf is induced by restriction in the original
presheaf. -/
@[simp]
lemma separation_map_mk {F : Cᵒᵖ ⥤ Type w} {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj X) :
    (separation J F).map f (_root_.Quotient.mk (locallyEqualSetoid J F X) x) =
      _root_.Quotient.mk (locallyEqualSetoid J F Y) (F.map f x) :=
  rfl

/-- The quotient map from a presheaf to its separation. -/
def toSeparation (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w) : F ⟶ separation J F where
  app X := ↾fun x ↦ _root_.Quotient.mk (locallyEqualSetoid J F X) x

/-- Pulling back the equalizer sieve of two sections gives the equalizer sieve of their
restrictions. -/
lemma equalizerSieve_pullback {F : Cᵒᵖ ⥤ Type w} {X Y : C}
    (f : Y ⟶ X) (x y : F.obj (op X)) :
    (equalizerSieve (F := F) x y).pullback f =
      equalizerSieve (F := F) (F.map f.op x) (F.map f.op y) := by
  ext Z g
  change (F.map (f.op ≫ g.op) x = F.map (f.op ≫ g.op) y) ↔
    (F.map g.op (F.map f.op x) = F.map g.op (F.map f.op y))
  simp only [Functor.map_comp_apply]

/-- The quotient by local equality is a separated presheaf. -/
theorem separation_isSeparated (F : Cᵒᵖ ⥤ Type w) :
    Presieve.IsSeparated J (separation J F) := by
  intro X S hS x t₁ t₂ ht₁ ht₂
  obtain ⟨a, rfl⟩ := _root_.Quotient.exists_rep t₁
  obtain ⟨b, rfl⟩ := _root_.Quotient.exists_rep t₂
  apply _root_.Quotient.sound
  change LocallyEqual J a b
  change equalizerSieve (F := F) a b ∈ J X
  apply J.transitive hS
  intro Y f hf
  rw [equalizerSieve_pullback]
  have hq := (ht₁ f hf).trans (ht₂ f hf).symm
  change (_root_.Quotient.mk (locallyEqualSetoid J F (op Y)) (F.map f.op a)) =
    (_root_.Quotient.mk (locallyEqualSetoid J F (op Y)) (F.map f.op b)) at hq
  exact (_root_.Quotient.eq_iff_equiv).mp hq

/-- A morphism from a presheaf to a separated presheaf descends to the separation. -/
def separationLift {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G)
    (hG : Presieve.IsSeparated J G) : separation J F ⟶ G where
  app X := ↾_root_.Quotient.lift (η.app X) (by
    intro x y hxy
    change LocallyEqual J x y at hxy
    change equalizerSieve (F := F) x y ∈ J X.unop at hxy
    apply (hG _ hxy).ext
    intro Y f hf
    have hx := ConcreteCategory.congr_hom (η.naturality f.op) x
    have hy := ConcreteCategory.congr_hom (η.naturality f.op) y
    exact hx.symm.trans ((congrArg (η.app (op Y)) hf).trans hy))
  naturality {X Y} f := by
    apply ConcreteCategory.hom_ext
    intro q
    obtain ⟨x, rfl⟩ := _root_.Quotient.exists_rep q
    exact ConcreteCategory.congr_hom (η.naturality f) x

/-- The separation lift factors the original morphism through the quotient map. -/
@[reassoc]
lemma toSeparation_separationLift {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G)
    (hG : Presieve.IsSeparated J G) :
    toSeparation J F ≫ separationLift J η hG = η := by
  ext X x
  rfl

/-- The lift from the separation to a separated presheaf is unique. -/
theorem separationLift_unique {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G)
    (hG : Presieve.IsSeparated J G) (γ : separation J F ⟶ G)
    (hγ : toSeparation J F ≫ γ = η) :
    γ = separationLift J η hG := by
  ext X q
  obtain ⟨x, rfl⟩ := _root_.Quotient.exists_rep q
  exact ConcreteCategory.congr_hom (congr_app hγ X) x

/-- The morphism on separations induced by a morphism of presheaves. -/
def separationMap {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G) :
    separation J F ⟶ separation J G :=
  separationLift J (η ≫ toSeparation J G) (separation_isSeparated J G)

/-- `separationMap` acts on quotient representatives by applying the original morphism. -/
@[simp]
lemma separationMap_mk {F G : Cᵒᵖ ⥤ Type w} (η : F ⟶ G) {X : Cᵒᵖ}
    (x : F.obj X) :
    (separationMap J η).app X
      (_root_.Quotient.mk (locallyEqualSetoid J F X) x) =
    _root_.Quotient.mk (locallyEqualSetoid J G X) (η.app X x) :=
  rfl

/-- Separation as an endofunctor on type-valued presheaves. -/
def separationFunctor : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w) where
  obj := separation J
  map := separationMap J
  map_id F := by
    ext X q
    obtain ⟨x, rfl⟩ := _root_.Quotient.exists_rep q
    rfl
  map_comp η γ := by
    ext X q
    obtain ⟨x, rfl⟩ := _root_.Quotient.exists_rep q
    rfl

end CategoryTheory.Presheaf

namespace CategoryTheory

/-- The full subcategory of type-valued presheaves separated for `J`. -/
abbrev SeparatedPresheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :=
  ObjectProperty.FullSubcategory
    (fun F : Cᵒᵖ ⥤ Type w ↦ Presieve.IsSeparated J F)

/-- The inclusion of separated presheaves into presheaves. -/
def separatedPresheafToPresheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    SeparatedPresheaf.{w} J ⥤ (Cᵒᵖ ⥤ Type w) :=
  ObjectProperty.ι
    (fun F : Cᵒᵖ ⥤ Type w ↦ Presieve.IsSeparated J F)

/-- The separation functor, with codomain restricted to separated presheaves. -/
def presheafToSeparatedPresheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    (Cᵒᵖ ⥤ Type w) ⥤ SeparatedPresheaf.{w} J where
  obj F := ⟨Presheaf.separation J F, Presheaf.separation_isSeparated J F⟩
  map η := ObjectProperty.homMk (Presheaf.separationMap J η)
  map_id F := by
    apply ObjectProperty.hom_ext
    exact (Presheaf.separationFunctor J).map_id F
  map_comp η γ := by
    apply ObjectProperty.hom_ext
    exact (Presheaf.separationFunctor J).map_comp η γ

/-- Separation is left adjoint to the inclusion of separated presheaves. -/
def separationAdjunction {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    presheafToSeparatedPresheaf.{w} J ⊣ separatedPresheafToPresheaf.{w} J :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G =>
        { toFun := fun γ ↦ Presheaf.toSeparation J F ≫ γ.hom
          invFun := fun η ↦ ObjectProperty.homMk
            (Presheaf.separationLift J η G.property)
          left_inv := fun γ ↦ by
            apply ObjectProperty.hom_ext
            exact (Presheaf.separationLift_unique J _ G.property γ.hom rfl).symm
          right_inv := fun η ↦ Presheaf.toSeparation_separationLift J η G.property }
      homEquiv_naturality_left_symm := by
        intro P Q R η γ
        apply ObjectProperty.hom_ext
        ext X q
        obtain ⟨x, rfl⟩ := _root_.Quotient.exists_rep q
        rfl
      homEquiv_naturality_right := by
        intro P Q R η γ
        ext X x
        rfl }

/-- Applying the plus construction to a separated presheaf gives a sheaf. -/
noncomputable def separatedPresheafToSheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    SeparatedPresheaf.{max u v} J ⥤ Sheaf J (Type max u v) where
  obj F := ⟨J.plusObj F.obj, by
    apply GrothendieckTopology.Plus.isSheaf_of_sep
    intro X S x y hxy
    apply (F.property S.1 S.2).ext
    intro Y f hf
    exact hxy ⟨Y, f, hf⟩⟩
  map η := ObjectProperty.homMk (J.plusMap η.hom)
  map_id F := by
    apply ObjectProperty.hom_ext
    exact (J.plusFunctor (Type max u v)).map_id F.obj
  map_comp η γ := by
    apply ObjectProperty.hom_ext
    exact (J.plusFunctor (Type max u v)).map_comp η.hom γ.hom

/-- A sheaf is, in particular, a separated presheaf. -/
def sheafToSeparatedPresheaf {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    Sheaf J (Type max u v) ⥤ SeparatedPresheaf.{max u v} J where
  obj F := ⟨F.obj,
    ((isSheaf_iff_isSheaf_of_type J F.obj).mp F.property).isSeparated⟩
  map η := ObjectProperty.homMk η.hom

/-- On separated presheaves, the plus construction is left adjoint to the inclusion of
sheaves. -/
noncomputable def plusSeparatedAdjunction {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    separatedPresheafToSheaf J ⊣ sheafToSeparatedPresheaf J :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun F G =>
        { toFun := fun γ ↦ ObjectProperty.homMk (J.toPlus F.obj ≫ γ.hom)
          invFun := fun η ↦ ObjectProperty.homMk (J.plusLift η.hom G.property)
          left_inv := fun γ ↦ by
            apply ObjectProperty.hom_ext
            exact (J.plusLift_unique _ G.property γ.hom rfl).symm
          right_inv := fun η ↦ by
            apply ObjectProperty.hom_ext
            exact J.toPlus_plusLift η.hom G.property }
      homEquiv_naturality_left_symm := by
        intro P Q R η γ
        apply ObjectProperty.hom_ext
        exact (J.plusMap_plusLift η.hom γ.hom R.property).symm
      homEquiv_naturality_right := by
        intro P Q R η γ
        apply ObjectProperty.hom_ext
        change J.toPlus P.obj ≫ (η.hom ≫ γ.hom) =
          (J.toPlus P.obj ≫ η.hom) ≫ γ.hom
        exact (Category.assoc _ _ _).symm }

end CategoryTheory
