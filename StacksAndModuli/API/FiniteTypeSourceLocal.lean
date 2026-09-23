module

public import StacksAndModuli.API.FiniteTypeSourceLocalAffine

/-!
# Source-locality of "locally of finite type" along a smooth surjection

If `g : X' ⟶ X` is smooth and surjective, `f : X ⟶ Y`, and `g ≫ f` is locally of finite
type, then so is `f`. This completes the chain begun in
`StacksAndModuli/API/FiniteTypeSmoothDescent.lean` (Stacks 0367 in the smooth case),
`StacksAndModuli/API/AffineRefinement.lean` (refining a smooth surjection by one from an affine
scheme) and `StacksAndModuli/API/FiniteTypeSourceLocalAffine.lean` (the case of affine source and
target).

The reduction to that case is the usual two-step Zariski argument, run through base changes
rather than `morphismRestrict`: cover the target by affines and replace `f` by
`𝒰.pullbackHom f i` (`IsZariskiLocalAtTarget`), then cover the source by affines and replace
`f` by `𝒰.f i ≫ f` (`IsZariskiLocalAtSource`). In each step the smooth surjection `g` is
replaced by its base change, which stays smooth and surjective, and the finite-type
hypothesis is transported along the base change of an open immersion — using that
`LocallyOfFiniteType` cancels on the right (`locallyOfFiniteType_of_comp`).

This is the `isLocalOnSourceAlong` hypothesis of
`AlgebraicGeometry.isSmoothLocal_locallyOfFiniteType`, one of the conditions under which
Definition 4.3.2 of *Stacks and Moduli* extends a property of morphisms of schemes to
morphisms of algebraic stacks.

## Main results

* `AlgebraicGeometry.locallyOfFiniteType_of_comp_of_smooth_surjective_of_isAffine_target`
* `AlgebraicGeometry.locallyOfFiniteType_of_comp_of_smooth_surjective`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Source-locality of "locally of finite type" along a smooth surjection, for an affine
target. -/
lemma locallyOfFiniteType_of_comp_of_smooth_surjective_of_isAffine_target
    {X' X Y : Scheme.{u}} [IsAffine Y] (g : X' ⟶ X) (f : X ⟶ Y)
    [Smooth g] [Surjective g] (h : LocallyOfFiniteType (g ≫ f)) :
    LocallyOfFiniteType f := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) X.affineCover]
  intro i
  have hgi : Smooth (pullback.snd g (X.affineCover.f i)) := inferInstance
  have hsi : Surjective (pullback.snd g (X.affineCover.f i)) := inferInstance
  refine locallyOfFiniteType_of_comp_of_smooth_surjective_of_isAffine
    (pullback.snd g (X.affineCover.f i)) (X.affineCover.f i ≫ f) ?_
  have he : pullback.snd g (X.affineCover.f i) ≫ (X.affineCover.f i ≫ f)
      = pullback.fst g (X.affineCover.f i) ≫ (g ≫ f) := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  rw [he]
  have hoi : IsOpenImmersion (pullback.fst g (X.affineCover.f i)) := inferInstance
  have := h
  infer_instance

/-- **Source-locality of "locally of finite type" along a smooth surjection.** If
`g : X' ⟶ X` is smooth and surjective and `g ≫ f` is locally of finite type, then so
is `f`. -/
lemma locallyOfFiniteType_of_comp_of_smooth_surjective
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Smooth g] [Surjective g] (h : LocallyOfFiniteType (g ≫ f)) :
    LocallyOfFiniteType f := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyOfFiniteType) Y.affineCover]
  intro i
  have hsm : Smooth (pullback.snd g (pullback.fst f (Y.affineCover.f i))) := inferInstance
  have hsj : Surjective (pullback.snd g (pullback.fst f (Y.affineCover.f i))) := inferInstance
  refine locallyOfFiniteType_of_comp_of_smooth_surjective_of_isAffine_target
    (pullback.snd g (pullback.fst f (Y.affineCover.f i)))
    (Y.affineCover.pullbackHom f i) ?_
  have key : (pullback.snd g (pullback.fst f (Y.affineCover.f i)) ≫
        Y.affineCover.pullbackHom f i) ≫ Y.affineCover.f i
      = pullback.fst g (pullback.fst f (Y.affineCover.f i)) ≫ (g ≫ f) := by
    rw [Category.assoc, Scheme.Cover.pullbackHom, ← pullback.condition,
      ← Category.assoc, ← pullback.condition, Category.assoc]
  have hoi : IsOpenImmersion (pullback.fst g (pullback.fst f (Y.affineCover.f i))) :=
    inferInstance
  have hcomp : LocallyOfFiniteType ((pullback.snd g (pullback.fst f (Y.affineCover.f i)) ≫
      Y.affineCover.pullbackHom f i) ≫ Y.affineCover.f i) := by
    rw [key]
    have := h
    infer_instance
  exact locallyOfFiniteType_of_comp _ (Y.affineCover.f i)

end AlgebraicGeometry
