module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The base-change square of a morphism in a slice category

Supporting API with no Stacks Project counterpart of its own: for `f : X ⟶ Y` in `C` and a
morphism `g : P ⟶ P'` of objects over `Y`, the square relating `g` with the morphism
`(Over.pullback f).map g` of base-changed objects is cartesian.  In other words,
`(Over.pullback f).map g` is *the* base change of the underlying morphism of `g` along the
projection `P' ×_Y X ⟶ P'`.

Consumed by the relative Grassmannian of §2.2: the Plücker morphism restricted to an open
part of the base is the base change of the global Plücker morphism, which is how the
closed-immersion property is checked locally on the base.

Main declarations:
- `CategoryTheory.Over.isPullback_pullback_map_left`.
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C]

/-- The square exhibiting `(Over.pullback f).map g` as the base change of `g.left` along
the projection `P'.left ×_Y X ⟶ P'.left`. -/
lemma isPullback_pullback_map_left {X Y : C} (f : X ⟶ Y) [HasPullbacksAlong f]
    {P P' : Over Y} (g : P ⟶ P') :
    IsPullback (pullback.fst P.hom f) ((Over.pullback f).map g).left g.left
      (pullback.fst P'.hom f) := by
  have hfst : pullback.fst P.hom f ≫ g.left =
      ((Over.pullback f).map g).left ≫ pullback.fst P'.hom f :=
    (pullback.lift_fst _ _ _).symm
  have hsnd : ((Over.pullback f).map g).left ≫ pullback.snd P'.hom f =
      pullback.snd P.hom f := pullback.lift_snd _ _ _
  refine IsPullback.of_bot ?_ hfst (IsPullback.of_hasPullback P'.hom f)
  rw [hsnd, Over.w g]
  exact IsPullback.of_hasPullback P.hom f

end CategoryTheory.Over
