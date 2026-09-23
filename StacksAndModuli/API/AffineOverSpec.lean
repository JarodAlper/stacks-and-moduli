module

public import StacksAndModuli.API.AffineArrowPseudofunctor
public import Mathlib.Algebra.Category.Ring.Under.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Affine arrows over spectra and algebra base change

This file identifies affine arrows over an affine scheme with opposites of
commutative rings under its coordinate ring.  It also records the natural
comparison between pushout of commutative algebras and pullback of affine
scheme arrows.  These are the coordinate changes used in effective affine
descent.

## Main declarations

- `AlgebraicGeometry.underSpecAffineEquivalence`: affine arrows over `Spec R`
  are equivalent to `(Under R)ᵒᵖ`.
- `AlgebraicGeometry.pushoutSpecPullbackNatIso`: pushout of algebras becomes
  pullback of affine arrows under relative spectrum.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry

noncomputable section

/-- Relative spectrum on commutative rings under `R`, written directly in the
over-category. -/
def underSpec (R : CommRingCat.{u}) : (Under R)ᵒᵖ ⥤ Over (Spec R) :=
  { obj := fun A ↦ Over.mk (Spec.map A.unop.hom)
    map := fun h ↦ Over.homMk (Spec.map h.unop.right) (by
      change Spec.map h.unop.right ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp, h.unop.w])
    map_id := fun A ↦ by
      apply Over.OverMorphism.ext
      simp
    map_comp := fun f g ↦ by
      apply Over.OverMorphism.ext
      simp [← Spec.map_comp] }

@[simp]
lemma underSpec_obj_hom (R : CommRingCat.{u}) (A : (Under R)ᵒᵖ) :
    ((underSpec R).obj A).hom = Spec.map A.unop.hom := rfl

@[simp]
lemma underSpec_map_left (R : CommRingCat.{u})
    {A B : (Under R)ᵒᵖ} (f : A ⟶ B) :
    ((underSpec R).map f).left = Spec.map f.unop.right := rfl

/-- Relative spectrum restricted to affine arrows. -/
def underSpecAffine (R : CommRingCat.{u}) :
    (Under R)ᵒᵖ ⥤ AffineOver (Spec R) :=
  (MorphismProperty.overObj
    (@IsAffineHom : MorphismProperty Scheme.{u}) (X := Spec R)).lift
    (underSpec R) (fun _ ↦ by
      change IsAffineHom (Spec.map _)
      infer_instance)

/-- Affine arrows over `Spec R` are equivalent to opposites of commutative
rings under `R`. -/
def underSpecAffineEquivalence (R : CommRingCat.{u}) :
    (Under R)ᵒᵖ ≌ AffineOver (Spec R) :=
  (commAlgCatEquivUnder R).symm.op.trans (affineOverSpecEquivalence R)

/-- The pullback comparison obtained by applying `Spec` to the pushout square
of a ring under `R` and a base-change map `R ⟶ S`. -/
def pushoutSpecPullbackIso {R S : CommRingCat.{u}} (f : R ⟶ S)
    (A : (Under R)ᵒᵖ) :
    ((underSpecAffine S).obj ((Under.pushout f).op.obj A)).obj ≅
      ((affineOverPullback (Spec.map f)).obj
        ((underSpecAffine R).obj A)).obj :=
  Over.isoMk (isPullback_SpecMap_pushout A.unop.hom f).isoPullback (by
    exact (isPullback_SpecMap_pushout A.unop.hom f).isoPullback_hom_snd)

@[simp]
lemma pushoutSpecPullbackIso_hom_left {R S : CommRingCat.{u}}
    (f : R ⟶ S) (A : (Under R)ᵒᵖ) :
    (pushoutSpecPullbackIso f A).hom.left =
      (isPullback_SpecMap_pushout A.unop.hom f).isoPullback.hom := rfl

set_option linter.flexible false in
/-- Under relative spectrum, pushout of commutative algebras is naturally
isomorphic to pullback of affine scheme arrows. -/
def pushoutSpecPullbackNatIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (Under.pushout f).op ⋙ underSpecAffine S ≅
      underSpecAffine R ⋙ affineOverPullback (Spec.map f) :=
  NatIso.ofComponents (fun A ↦ ObjectProperty.isoMk
    (P := MorphismProperty.overObj
      (@IsAffineHom : MorphismProperty Scheme.{u}) (X := Spec S))
    (pushoutSpecPullbackIso f A)) (fun {A B} h ↦ by
      apply ObjectProperty.hom_ext
      change (underSpec S).map ((Under.pushout f).op.map h) ≫
          (pushoutSpecPullbackIso f B).hom =
        (pushoutSpecPullbackIso f A).hom ≫
          (Over.pullback (Spec.map f)).map ((underSpec R).map h)
      apply Over.OverMorphism.ext
      change ((underSpec S).map ((Under.pushout f).op.map h)).left ≫
          (pushoutSpecPullbackIso f B).hom.left =
        (pushoutSpecPullbackIso f A).hom.left ≫
          ((Over.pullback (Spec.map f)).map ((underSpec R).map h)).left
      apply pullback.hom_ext
      · simp [pushoutSpecPullbackIso, underSpecAffine, underSpec]
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        simp
      · simp [pushoutSpecPullbackIso, underSpecAffine, underSpec]
        rw [← Spec.map_comp]
        congr 1
        simp)

end

end AlgebraicGeometry
