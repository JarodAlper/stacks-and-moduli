module

public import StacksAndModuli.API.RelativeYonedaTotal

/-!
# Universe-raised relative Yoneda on total categories

This file assembles the universe-raised relative Yoneda embeddings of the
over-categories of schemes into a functor on the corresponding
co-Grothendieck total categories.  The target consists of sheaves valued in
`Type max u w`, while the source remains the ordinary total category of
scheme arrows.

## Main definitions

- `CategoryTheory.GrothendieckTopology.overMapPullbackULiftYonedaIso`:
  universe-raised Yoneda commutes with pullback in an over-category.
- `AlgebraicGeometry.RelativeYonedaULift.functor`: universe-raised relative
  Yoneda on total categories.
- `AlgebraicGeometry.RelativeYonedaULift.preimage`: the inverse operation on
  morphisms.
- `AlgebraicGeometry.RelativeYonedaULift.functor_full` and
  `AlgebraicGeometry.RelativeYonedaULift.functor_faithful`: the total functor
  is full and faithful.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory Opposite

universe w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
variable (J : GrothendieckTopology C) [J.Subcanonical]

/-- Pullback commutes with the universe-raised Yoneda embedding on an
over-site. -/
noncomputable def overMapPullbackULiftYonedaIso
    {X Y : C} (f : X ⟶ Y) (Z : Over Y) :
    (J.over X).uliftYoneda.{w}.obj ((Over.pullback f).obj Z) ≅
      (J.overMapPullback (Type max v w) f).obj
        ((J.over Y).uliftYoneda.{w}.obj Z) :=
  (fullyFaithfulSheafToPresheaf (J.over X) (Type max v w)).preimageIso
    (Functor.isoWhiskerRight
      ((Over.mapPullbackAdj f).compYonedaIso.app Z) uliftFunctor.{w})

end CategoryTheory.GrothendieckTopology

namespace AlgebraicGeometry

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace RelativeYonedaULift

variable (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical]

/-- The total category of scheme arrows, with base change as transition
functors. -/
abbrev ArrowTotal := RelativeYoneda.ArrowTotal

/-- The total category of universe-raised sheaves on over-sites, with
pullback as transition functors. -/
abbrev SheafTotal :=
  Pseudofunctor.CoGrothendieck (J.pseudofunctorOver (Type max u w))

/-- Universe-raised relative Yoneda on objects of the total category. -/
noncomputable def obj (A : ArrowTotal.{u}) : SheafTotal.{w} J :=
  ⟨A.base, (J.over A.base).uliftYoneda.{w}.obj A.fiber⟩

/-- Universe-raised relative Yoneda on morphisms of the total category. -/
noncomputable def map {A B : ArrowTotal.{u}} (f : A ⟶ B) :
    obj.{w} J A ⟶ obj.{w} J B where
  base := f.base
  fiber := (J.over A.base).uliftYoneda.{w}.map f.fiber ≫
    (J.overMapPullbackULiftYonedaIso.{w} f.base B.fiber).hom

set_option maxHeartbeats 400000 in
-- Unfolding both pseudofunctor coherences needs more than the default heartbeat limit.
/-- The universe-raised relative Yoneda construction is a functor on total
categories. -/
noncomputable def functor : ArrowTotal.{u} ⥤ SheafTotal.{w} J where
  obj := obj.{w} J
  map := map.{w} J
  map_id A := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext
      (map.{w} J (𝟙 A)) (𝟙 (obj.{w} J A)) rfl
    dsimp [map]
    apply (sheafToPresheaf (J.over A.base)
      (Type max u w)).map_injective
    apply NatTrans.ext
    funext T
    simp [overPullbackPseudofunctor, obj,
      CategoryTheory.GrothendieckTopology.overMapPullbackULiftYonedaIso,
      OverAdj.pseudofunctor, OverAdj.adjMapId,
      CategoryTheory.Bicategory.Adj.rightPseudofunctor,
      CategoryTheory.GrothendieckTopology.pseudofunctorOver,
      CategoryTheory.Over.pullbackId]
    apply ConcreteCategory.hom_ext
    intro h
    apply ULift.ext
    apply CategoryTheory.Over.OverMorphism.ext
    dsimp [Adjunction.compYonedaIso,
      CategoryTheory.Over.mapPullbackAdj]
    simp [CategoryTheory.GrothendieckTopology.uliftYoneda,
      CategoryTheory.uliftFunctor,
      OverAdj.adjMap, Category.assoc]
  map_comp {A B C} f g := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext
      (map.{w} J (f ≫ g))
      (map.{w} J f ≫ map.{w} J g) rfl
    dsimp [map]
    apply (sheafToPresheaf (J.over A.base)
      (Type max u w)).map_injective
    apply NatTrans.ext
    funext T
    simp [overPullbackPseudofunctor, obj,
      CategoryTheory.GrothendieckTopology.overMapPullbackULiftYonedaIso,
      OverAdj.pseudofunctor, OverAdj.adjMapComp,
      CategoryTheory.Bicategory.Adj.rightPseudofunctor,
      CategoryTheory.GrothendieckTopology.pseudofunctorOver,
      CategoryTheory.Over.pullbackComp, Category.assoc]
    apply ConcreteCategory.hom_ext
    intro h
    apply ULift.ext
    apply CategoryTheory.Over.OverMorphism.ext
    dsimp [Adjunction.compYonedaIso,
      CategoryTheory.Over.mapPullbackAdj]
    simp [CategoryTheory.GrothendieckTopology.uliftYoneda,
      CategoryTheory.uliftFunctor,
      OverAdj.adjMap, Category.assoc]

/-- Recover a scheme-arrow morphism from a morphism between its
universe-raised relative Yoneda images. -/
noncomputable def preimage {A B : ArrowTotal.{u}}
    (f : obj.{w} J A ⟶ obj.{w} J B) : A ⟶ B where
  base := f.base
  fiber := (J.over A.base).uliftYoneda.{w}.preimage
    (f.fiber ≫
      (J.overMapPullbackULiftYonedaIso.{w} f.base B.fiber).inv)

/-- Taking the preimage of the universe-raised relative Yoneda image
recovers the original morphism. -/
lemma preimage_map {A B : ArrowTotal.{u}} (f : A ⟶ B) :
    preimage.{w} J (map.{w} J f) = f := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext
    (preimage.{w} J (map.{w} J f)) f rfl ?_
  dsimp [preimage, map]
  simp

/-- Applying universe-raised relative Yoneda after taking a preimage
recovers the original morphism. -/
lemma map_preimage {A B : ArrowTotal.{u}}
    (f : obj.{w} J A ⟶ obj.{w} J B) :
    map.{w} J (preimage.{w} J f) = f := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext
    (map.{w} J (preimage.{w} J f)) f rfl ?_
  dsimp [preimage, map]
  simp [Category.assoc]

/-- Universe-raised relative Yoneda is full on the total categories. -/
noncomputable instance functor_full : (functor.{w} J).Full where
  map_surjective {A B} f := by
    refine ⟨preimage.{w} J f, ?_⟩
    change map.{w} J (preimage.{w} J f) = f
    exact map_preimage.{w} J f

/-- Universe-raised relative Yoneda is faithful on the total categories. -/
noncomputable instance functor_faithful : (functor.{w} J).Faithful where
  map_injective {A B} f g h := by
    rw [← preimage_map.{w} J f, ← preimage_map.{w} J g]
    change preimage.{w} J ((functor.{w} J).map f) =
      preimage.{w} J ((functor.{w} J).map g)
    rw [h]

end RelativeYonedaULift

end


end AlgebraicGeometry
