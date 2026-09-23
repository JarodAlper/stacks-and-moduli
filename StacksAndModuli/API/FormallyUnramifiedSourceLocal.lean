module

public import StacksAndModuli.API.AffineRefinement
public import StacksAndModuli.API.FormallyUnramifiedSmoothDescent
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Source-locality of formal unramifiedness along a smooth surjection

If `g : X' ⟶ X` is smooth and surjective, `f : X ⟶ Y`, and `g ≫ f` is formally
unramified, then so is `f`. This is the unramified analogue of
`StacksAndModuli/API/FiniteTypeSourceLocal.lean`, and the two together give the source-locality
of "locally of finite type and formally unramified" — the book's *unramified* — along
étale (indeed smooth) surjections.

The argument runs through the same three steps. The ring-level input is
`RingHom.FormallyUnramified.of_comp_of_smooth_of_faithfullyFlat` (Jacobi–Zariski, see
`StacksAndModuli/API/FormallyUnramifiedSmoothDescent.lean`); the affine case refines `g` by a
morphism from an affine scheme (`AlgebraicGeometry.exists_affine_smooth_surjective`),
using that the refining morphism is étale, hence formally unramified, so that the
hypothesis on `g ≫ f` transports to the refinement; the general case is the usual
two-step Zariski reduction through base changes.

Unlike "locally of finite type", formal unramifiedness is *not* stable under
precomposition by an arbitrary morphism, which is why the affine refinement had to be
strengthened from "locally of finite type" to "étale".

This supplies the `isLocalOnSourceAlong` hypothesis of
`AlgebraicGeometry.isEtaleLocal_locallyOfFiniteType_inf_formallyUnramified`, one of the
conditions under which Definition 4.3.2 of *Stacks and Moduli* extends a property of
morphisms of schemes to morphisms of Deligne–Mumford stacks.

## Main results

* `AlgebraicGeometry.formallyUnramified_of_comp_of_smooth_surjective_of_isAffine`
* `AlgebraicGeometry.formallyUnramified_of_comp_of_smooth_surjective_of_isAffine_target`
* `AlgebraicGeometry.formallyUnramified_of_comp_of_smooth_surjective`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The affine case of source-locality for formal unramifiedness along a smooth
surjection. -/
lemma formallyUnramified_of_comp_of_smooth_surjective_of_isAffine
    {X' X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : X' ⟶ X) (f : X ⟶ Y)
    [Smooth g] [Surjective g] (h : FormallyUnramified (g ≫ f)) :
    FormallyUnramified f := by
  obtain ⟨W, hWaff, ρ, hρ, hsm, hsurj⟩ := exists_affine_smooth_surjective g
  have hρet : Etale ρ := hρ
  have hW : IsAffine W := hWaff
  have hsmooth : ((ρ ≫ g).appTop).hom.Smooth :=
    HasRingHomProperty.appTop (P := @Smooth) _ hsm
  have hff : ((ρ ≫ g).appTop).hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (ρ ≫ g)).mp
      ⟨inferInstance, hsurj⟩
  have hρfu : FormallyUnramified ρ := inferInstance
  have hcomp : FormallyUnramified (ρ ≫ (g ≫ f)) :=
    MorphismProperty.comp_mem @FormallyUnramified _ _ hρfu h
  have hfu : ((ρ ≫ (g ≫ f)).appTop).hom.FormallyUnramified :=
    HasRingHomProperty.appTop (P := @FormallyUnramified) _ hcomp
  have htri : (ρ ≫ (g ≫ f)).appTop = f.appTop ≫ (ρ ≫ g).appTop := by
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
      Category.assoc]
  rw [htri] at hfu
  have : (f.appTop).hom.FormallyUnramified :=
    RingHom.FormallyUnramified.of_comp_of_smooth_of_faithfullyFlat
      (f.appTop).hom ((ρ ≫ g).appTop).hom (by simpa using hfu) hsmooth hff
  exact (HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified)).mpr this

/-- Source-locality of formal unramifiedness along a smooth surjection, for an affine
target. -/
lemma formallyUnramified_of_comp_of_smooth_surjective_of_isAffine_target
    {X' X Y : Scheme.{u}} [IsAffine Y] (g : X' ⟶ X) (f : X ⟶ Y)
    [Smooth g] [Surjective g] (h : FormallyUnramified (g ≫ f)) :
    FormallyUnramified f := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @FormallyUnramified) X.affineCover]
  intro i
  have hgi : Smooth (pullback.snd g (X.affineCover.f i)) := inferInstance
  have hsi : Surjective (pullback.snd g (X.affineCover.f i)) := inferInstance
  refine formallyUnramified_of_comp_of_smooth_surjective_of_isAffine
    (pullback.snd g (X.affineCover.f i)) (X.affineCover.f i ≫ f) ?_
  have he : pullback.snd g (X.affineCover.f i) ≫ (X.affineCover.f i ≫ f)
      = pullback.fst g (X.affineCover.f i) ≫ (g ≫ f) := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  rw [he]
  exact MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance h

/-- **Source-locality of formal unramifiedness along a smooth surjection.** If
`g : X' ⟶ X` is smooth and surjective and `g ≫ f` is formally unramified, then so is
`f`. -/
lemma formallyUnramified_of_comp_of_smooth_surjective
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Smooth g] [Surjective g] (h : FormallyUnramified (g ≫ f)) :
    FormallyUnramified f := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @FormallyUnramified) Y.affineCover]
  intro i
  have hsm : Smooth (pullback.snd g (pullback.fst f (Y.affineCover.f i))) := inferInstance
  have hsj : Surjective (pullback.snd g (pullback.fst f (Y.affineCover.f i))) :=
    inferInstance
  refine formallyUnramified_of_comp_of_smooth_surjective_of_isAffine_target
    (pullback.snd g (pullback.fst f (Y.affineCover.f i)))
    (Y.affineCover.pullbackHom f i) ?_
  have key : (pullback.snd g (pullback.fst f (Y.affineCover.f i)) ≫
        Y.affineCover.pullbackHom f i) ≫ Y.affineCover.f i
      = pullback.fst g (pullback.fst f (Y.affineCover.f i)) ≫ (g ≫ f) := by
    rw [Category.assoc, Scheme.Cover.pullbackHom, ← pullback.condition,
      ← Category.assoc, ← pullback.condition, Category.assoc]
  have hoi : IsOpenImmersion (pullback.fst g (pullback.fst f (Y.affineCover.f i))) :=
    inferInstance
  have hcomp : FormallyUnramified ((pullback.snd g (pullback.fst f (Y.affineCover.f i)) ≫
      Y.affineCover.pullbackHom f i) ≫ Y.affineCover.f i) := by
    rw [key]
    exact MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance h
  have := hcomp
  exact FormallyUnramified.of_comp _ (Y.affineCover.f i)

end AlgebraicGeometry
