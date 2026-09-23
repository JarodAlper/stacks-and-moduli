module

public import StacksAndModuli.API.AffineRefinement
public import StacksAndModuli.API.QuasiFiniteFaithfullyFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Étale-locality of local quasi-finiteness on the source and the target

If `g : X' ⟶ X` is smooth and surjective, `f : X ⟶ Y`, and `g ≫ f` is locally
quasi-finite, then so is `f`; and the same property is local on the target along étale
surjections.

The ring-level input is `StacksAndModuli/API/QuasiFiniteFaithfullyFlatDescent.lean` — it needs only
faithful flatness, not smoothness — and the scheme-level reduction is the same two-step
Zariski argument as in `StacksAndModuli/API/FiniteTypeSourceLocal.lean` and
`StacksAndModuli/API/FormallyUnramifiedSourceLocal.lean`. Like formal unramifiedness and unlike
"locally of finite type", local quasi-finiteness is not stable under precomposition by an
arbitrary morphism, so the affine refinement is used through `Etale ρ` (via
`AlgebraicGeometry.LocallyQuasiFinite.of_etale`, which Mathlib does not have).

Target-locality is then formal, as for flatness: `pullback.fst f g` is an étale surjection,
being the base change of `g`, and `pullback.fst f g ≫ f = pullback.snd f g ≫ g` is locally
quasi-finite as soon as `pullback.snd f g` is, so source-locality applies.

This supplies both fields of `AlgebraicGeometry.isEtaleLocal_locallyQuasiFinite`, the
hypothesis under which §4.3.5 of *Stacks and Moduli* extends local quasi-finiteness to
morphisms of algebraic spaces and to representable morphisms of algebraic stacks.

## Main results

* `AlgebraicGeometry.LocallyQuasiFinite.of_etale`
* `AlgebraicGeometry.locallyQuasiFinite_of_comp_of_smooth_surjective_of_isAffine`
* `AlgebraicGeometry.locallyQuasiFinite_of_comp_of_smooth_surjective_of_isAffine_target`
* `AlgebraicGeometry.locallyQuasiFinite_of_comp_of_smooth_surjective`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- An étale morphism of schemes is locally quasi-finite. -/
instance (priority := 900) LocallyQuasiFinite.of_etale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Etale f] : LocallyQuasiFinite f where
  quasiFinite_appLE {_} hU {_} hV e := RingHom.QuasiFinite.of_etale (f.etale_appLE hU hV e)

/-- The affine case of source-locality for local quasi-finiteness along a smooth
surjection. -/
lemma locallyQuasiFinite_of_comp_of_smooth_surjective_of_isAffine
    {X' X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : X' ⟶ X) (f : X ⟶ Y)
    [Smooth g] [Surjective g] (h : LocallyQuasiFinite (g ≫ f)) :
    LocallyQuasiFinite f := by
  obtain ⟨W, hWaff, ρ, hρ, hsm, hsurj⟩ := exists_affine_smooth_surjective g
  have hρet : Etale ρ := hρ
  have hW : IsAffine W := hWaff
  -- `Γ(X) → Γ(W)` is faithfully flat
  have hff : ((ρ ≫ g).appTop).hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (ρ ≫ g)).mp
      ⟨inferInstance, hsurj⟩
  -- `Γ(Y) → Γ(W)` is quasi-finite
  have hcomp : LocallyQuasiFinite (ρ ≫ (g ≫ f)) :=
    MorphismProperty.comp_mem @LocallyQuasiFinite _ _ inferInstance h
  have hqf : ((ρ ≫ (g ≫ f)).appTop).hom.QuasiFinite :=
    HasRingHomProperty.appTop (P := @LocallyQuasiFinite) _ hcomp
  have htri : (ρ ≫ (g ≫ f)).appTop = f.appTop ≫ (ρ ≫ g).appTop := by
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
      Category.assoc]
  rw [htri] at hqf
  have : (f.appTop).hom.QuasiFinite :=
    RingHom.QuasiFinite.of_comp_of_faithfullyFlat
      (f.appTop).hom ((ρ ≫ g).appTop).hom (by simpa using hqf) hff
  exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyQuasiFinite)).mpr this

/-- Source-locality of local quasi-finiteness along a smooth surjection, for an affine
target. -/
lemma locallyQuasiFinite_of_comp_of_smooth_surjective_of_isAffine_target
    {X' X Y : Scheme.{u}} [IsAffine Y] (g : X' ⟶ X) (f : X ⟶ Y)
    [Smooth g] [Surjective g] (h : LocallyQuasiFinite (g ≫ f)) :
    LocallyQuasiFinite f := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyQuasiFinite) X.affineCover]
  intro i
  have hgi : Smooth (pullback.snd g (X.affineCover.f i)) := inferInstance
  have hsi : Surjective (pullback.snd g (X.affineCover.f i)) := inferInstance
  refine locallyQuasiFinite_of_comp_of_smooth_surjective_of_isAffine
    (pullback.snd g (X.affineCover.f i)) (X.affineCover.f i ≫ f) ?_
  have he : pullback.snd g (X.affineCover.f i) ≫ (X.affineCover.f i ≫ f)
      = pullback.fst g (X.affineCover.f i) ≫ (g ≫ f) := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
  rw [he]
  exact MorphismProperty.comp_mem @LocallyQuasiFinite _ _ inferInstance h

/-- **Source-locality of local quasi-finiteness along a smooth surjection.** If
`g : X' ⟶ X` is smooth and surjective and `g ≫ f` is locally quasi-finite, then so is
`f`. -/
lemma locallyQuasiFinite_of_comp_of_smooth_surjective
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Smooth g] [Surjective g] (h : LocallyQuasiFinite (g ≫ f)) :
    LocallyQuasiFinite f := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyQuasiFinite) Y.affineCover]
  intro i
  have hsm : Smooth (pullback.snd g (pullback.fst f (Y.affineCover.f i))) := inferInstance
  have hsj : Surjective (pullback.snd g (pullback.fst f (Y.affineCover.f i))) :=
    inferInstance
  refine locallyQuasiFinite_of_comp_of_smooth_surjective_of_isAffine_target
    (pullback.snd g (pullback.fst f (Y.affineCover.f i)))
    (Y.affineCover.pullbackHom f i) ?_
  have key : (pullback.snd g (pullback.fst f (Y.affineCover.f i)) ≫
        Y.affineCover.pullbackHom f i) ≫ Y.affineCover.f i
      = pullback.fst g (pullback.fst f (Y.affineCover.f i)) ≫ (g ≫ f) := by
    rw [Category.assoc, Scheme.Cover.pullbackHom, ← pullback.condition,
      ← Category.assoc, ← pullback.condition, Category.assoc]
  have hoi : IsOpenImmersion (pullback.fst g (pullback.fst f (Y.affineCover.f i))) :=
    inferInstance
  have hcomp : LocallyQuasiFinite ((pullback.snd g (pullback.fst f (Y.affineCover.f i)) ≫
      Y.affineCover.pullbackHom f i) ≫ Y.affineCover.f i) := by
    rw [key]
    exact MorphismProperty.comp_mem @LocallyQuasiFinite _ _ inferInstance h
  have := hcomp
  exact LocallyQuasiFinite.of_comp _ (Y.affineCover.f i)

end AlgebraicGeometry
