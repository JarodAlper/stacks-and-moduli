module

public import StacksAndModuli.API.AffineArrowPseudofunctor
public import StacksAndModuli.API.RepresentableSheafOverlap
public import Mathlib.CategoryTheory.Bicategory.Grothendieck

/-!
# Relative Yoneda on total categories

This file assembles the relative Yoneda embeddings of the over-categories of schemes
into a functor on the corresponding co-Grothendieck total categories.  A morphism in
the source is a cartesian-arrow-shaped pair consisting of a base morphism and a map to
the pullback over that base morphism.  Its image is the analogous pair for sheaves on
over-sites.

## Main definitions

- `AlgebraicGeometry.RelativeYoneda.functor`: relative Yoneda on the total categories.
- `AlgebraicGeometry.RelativeYoneda.preimage`: a left inverse on morphisms.
- `AlgebraicGeometry.RelativeYoneda.functor_faithful`: relative Yoneda is faithful.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory Opposite

universe u

namespace AlgebraicGeometry

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace RelativeYoneda

variable (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]

/-- The total category of scheme arrows, with base change as transition functors. -/
abbrev ArrowTotal := Pseudofunctor.CoGrothendieck overPullbackPseudofunctor

/-- The total category of sheaves on over-sites, with pullback as transition functors. -/
abbrev SheafTotal :=
  Pseudofunctor.CoGrothendieck (J.pseudofunctorOver (Type u))

/-- Relative Yoneda on objects of the total category. -/
noncomputable def obj (A : ArrowTotal.{u}) : SheafTotal J :=
  ⟨A.base, (J.over A.base).yoneda.obj A.fiber⟩

/-- Relative Yoneda on morphisms of the total category. -/
noncomputable def map {A B : ArrowTotal.{u}} (f : A ⟶ B) :
    obj J A ⟶ obj J B where
  base := f.base
  fiber := (J.over A.base).yoneda.map f.fiber ≫
    (J.overMapPullbackYonedaIso f.base B.fiber).hom

set_option maxHeartbeats 400000 in
-- Unfolding both pseudofunctor coherences needs more than the default heartbeat limit.
/-- The relative Yoneda construction is a functor on total categories. -/
noncomputable def functor : ArrowTotal.{u} ⥤ SheafTotal J where
  obj := obj J
  map := map J
  map_id A := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext
      (map J (𝟙 A)) (𝟙 (obj J A)) rfl
    dsimp [map]
    apply (sheafToPresheaf (J.over A.base) (Type u)).map_injective
    apply NatTrans.ext
    funext T
    simp [overPullbackPseudofunctor, obj,
      CategoryTheory.GrothendieckTopology.overMapPullbackYonedaIso,
      OverAdj.pseudofunctor, OverAdj.adjMapId,
      CategoryTheory.Bicategory.Adj.rightPseudofunctor,
      CategoryTheory.GrothendieckTopology.pseudofunctorOver,
      CategoryTheory.Over.pullbackId]
    apply ConcreteCategory.hom_ext
    intro h
    apply CategoryTheory.Over.OverMorphism.ext
    dsimp [Adjunction.compYonedaIso, CategoryTheory.Over.mapPullbackAdj]
    simp [OverAdj.adjMap, Category.assoc]
  map_comp {A B C} f g := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext
      (map J (f ≫ g)) (map J f ≫ map J g) rfl
    dsimp [map]
    apply (sheafToPresheaf (J.over A.base) (Type u)).map_injective
    apply NatTrans.ext
    funext T
    simp [overPullbackPseudofunctor, obj,
      CategoryTheory.GrothendieckTopology.overMapPullbackYonedaIso,
      OverAdj.pseudofunctor, OverAdj.adjMapComp,
      CategoryTheory.Bicategory.Adj.rightPseudofunctor,
      CategoryTheory.GrothendieckTopology.pseudofunctorOver,
      CategoryTheory.Over.pullbackComp, Category.assoc]
    apply ConcreteCategory.hom_ext
    intro h
    apply CategoryTheory.Over.OverMorphism.ext
    dsimp [Adjunction.compYonedaIso, CategoryTheory.Over.mapPullbackAdj]
    simp [OverAdj.adjMap, Category.assoc]

/-- Recover a scheme-arrow morphism from a morphism between its relative Yoneda
images. -/
noncomputable def preimage {A B : ArrowTotal.{u}}
    (f : obj J A ⟶ obj J B) : A ⟶ B where
  base := f.base
  fiber := (J.over A.base).yoneda.preimage
    (f.fiber ≫ (J.overMapPullbackYonedaIso f.base B.fiber).inv)

/-- Taking the preimage of the relative Yoneda image recovers the original
morphism. -/
lemma preimage_map {A B : ArrowTotal.{u}} (f : A ⟶ B) :
    preimage J (map J f) = f := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext
    (preimage J (map J f)) f rfl ?_
  dsimp [preimage, map]
  simp

/-- Applying relative Yoneda after taking a preimage recovers the original
morphism. -/
lemma map_preimage {A B : ArrowTotal.{u}} (f : obj J A ⟶ obj J B) :
    map J (preimage J f) = f := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext
    (map J (preimage J f)) f rfl ?_
  dsimp [preimage, map]
  simp [Category.assoc]

/-- Relative Yoneda is faithful on the total categories. -/
noncomputable instance functor_faithful : (functor J).Faithful where
  map_injective {A B} f g h := by
    rw [← preimage_map J f, ← preimage_map J g]
    change preimage J ((functor J).map f) =
      preimage J ((functor J).map g)
    rw [h]

end RelativeYoneda

end

end AlgebraicGeometry
