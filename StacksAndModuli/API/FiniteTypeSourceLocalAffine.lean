module

public import StacksAndModuli.API.AffineRefinement
public import StacksAndModuli.API.FiniteTypeSmoothDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Source-locality of "locally of finite type" along a smooth surjection: the affine case

If `g : X' ⟶ X` is smooth and surjective, `f : X ⟶ Y` and `g ≫ f` is locally of finite
type, then so is `f`. This file proves the case where `X` and `Y` are affine, which is the
case the general statement reduces to by Zariski-locality on the source and target.

The proof combines the two halves developed in
`StacksAndModuli/API/AffineRefinement.lean` and `StacksAndModuli/API/FiniteTypeSmoothDescent.lean`:
refine `g` by a morphism `ρ` from an *affine* `W` with `ρ ≫ g` still smooth and surjective,
so that `Γ(X) → Γ(W)` is smooth and faithfully flat
(`AlgebraicGeometry.Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`) while
`Γ(Y) → Γ(W)` is of finite type; then descend along it with
`RingHom.FiniteType.of_comp_of_smooth_of_faithfullyFlat`.

This is one of the hypotheses under which Definition 4.3.2 of *Stacks and Moduli* extends a
property of morphisms of schemes to morphisms of algebraic stacks; see the
`def:properties-of-morphisms-of-stacks` entries in
`StacksAndModuli/Section4.3-Properties/COMMENTARY.md`.

## Main results

* `AlgebraicGeometry.locallyOfFiniteType_of_comp_of_smooth_surjective_of_isAffine`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The affine case of source-locality for "locally of finite type" along a smooth
surjection. -/
lemma locallyOfFiniteType_of_comp_of_smooth_surjective_of_isAffine
    {X' X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (g : X' ⟶ X) (f : X ⟶ Y)
    [Smooth g] [Surjective g] (h : LocallyOfFiniteType (g ≫ f)) :
    LocallyOfFiniteType f := by
  obtain ⟨W, hWaff, ρ, hρ, hsm, hsurj⟩ := exists_affine_smooth_surjective g
  have hρet : Etale ρ := hρ
  have hW : IsAffine W := hWaff
  -- Γ(X) → Γ(W) is smooth and faithfully flat
  have hsmooth : ((ρ ≫ g).appTop).hom.Smooth :=
    HasRingHomProperty.appTop (P := @Smooth) _ hsm
  have hff : ((ρ ≫ g).appTop).hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (ρ ≫ g)).mp
      ⟨inferInstance, hsurj⟩
  -- Γ(Y) → Γ(W) is of finite type
  have hcomp : LocallyOfFiniteType (ρ ≫ (g ≫ f)) := by
    have := h; infer_instance
  have hft : ((ρ ≫ (g ≫ f)).appTop).hom.FiniteType :=
    HasRingHomProperty.appTop (P := @LocallyOfFiniteType) _ hcomp
  -- the triangle
  have htri : (ρ ≫ (g ≫ f)).appTop = f.appTop ≫ (ρ ≫ g).appTop := by
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
      Category.assoc]
  rw [htri] at hft
  have : (f.appTop).hom.FiniteType :=
    RingHom.FiniteType.of_comp_of_smooth_of_faithfullyFlat
      (f.appTop).hom ((ρ ≫ g).appTop).hom (by simpa using hft) hsmooth hff
  exact (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mpr this

end AlgebraicGeometry
