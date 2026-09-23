module

public import StacksAndModuli.API.RightAdjointPseudofunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.Comma

/-!
# The pseudofunctor of affine scheme arrows

This file constructs the contravariant pseudofunctor whose value at a scheme
`X` is the category of affine morphisms to `X`, and whose transition functors
are base change.  The coherence is inherited from the adjunction
`Over.map f ⊣ Over.pullback f`.

## Main definitions

- `AlgebraicGeometry.AffineOver`: affine scheme arrows over a fixed scheme.
- `AlgebraicGeometry.affineOverPseudofunctor`: affine arrows and base change as
  a pseudofunctor.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u

namespace AlgebraicGeometry

noncomputable section

namespace OverAdj

/-- The base-change adjunction on over-categories, regarded as a morphism in
the bicategory of adjunctions. -/
noncomputable def adjMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Bicategory.Adj.mk (Cat.of (CategoryTheory.Over X)) ⟶
      Bicategory.Adj.mk (Cat.of (CategoryTheory.Over Y)) :=
  Bicategory.Adj.Hom.mk
    (CategoryTheory.Adjunction.toCat (CategoryTheory.Over.mapPullbackAdj f))

/-- Identity comparison for the base-change adjunctions on over-categories. -/
noncomputable def adjMapId (X : Scheme.{u}) :
    adjMap (𝟙 X) ≅
      𝟙 (Bicategory.Adj.mk (Cat.of (CategoryTheory.Over X))) :=
  Bicategory.Adj.iso₂Mk
    (Cat.Hom.isoMk (CategoryTheory.Over.mapId X))
    (Cat.Hom.isoMk (CategoryTheory.Over.pullbackId (X := X)).symm)

/-- Composition comparison for the base-change adjunctions on
over-categories. -/
noncomputable def adjMapComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    adjMap (f ≫ g) ≅ adjMap f ≫ adjMap g :=
  Bicategory.Adj.iso₂Mk
    (Cat.Hom.isoMk (CategoryTheory.Over.mapComp f g))
    (Cat.Hom.isoMk (CategoryTheory.Over.pullbackComp f g).symm)

/-- The pseudofunctor of over-category base-change adjunctions. -/
noncomputable def pseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u})
      (Bicategory.Adj Cat.{u, u + 1}) := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Bicategory.Adj.mk (Cat.of (CategoryTheory.Over X)))
    (fun f ↦ adjMap f)
    (fun X ↦ adjMapId X)
    (fun f g ↦ adjMapComp f g) ?_ ?_ ?_
  · intro W X Y Z f g h
    apply Bicategory.Adj.hom₂_ext
    ext A
    rfl
  · intro X Y f
    apply Bicategory.Adj.hom₂_ext
    ext A
    rfl
  · intro X Y f
    apply Bicategory.Adj.hom₂_ext
    ext A
    rfl

end OverAdj

/-- All scheme arrows, with pullback as contravariant functoriality. -/
noncomputable def overPullbackPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1} :=
  Bicategory.Adj.rightPseudofunctor OverAdj.pseudofunctor

local instance affineStableUnderBaseChangeAlong {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsAffineHom : MorphismProperty Scheme.{u}) f where
  of_isPullback pb h := MorphismProperty.of_isPullback
    (P := (@IsAffineHom : MorphismProperty Scheme.{u})) pb h

/-- The category of affine scheme morphisms with target `X`. -/
abbrev AffineOver (X : Scheme.{u}) :=
  (MorphismProperty.overObj
    (@IsAffineHom : MorphismProperty Scheme.{u}) (X := X)).FullSubcategory

/-- Base change of affine scheme arrows. -/
noncomputable def affineOverPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AffineOver Y ⥤ AffineOver X :=
  (MorphismProperty.overObj
    (@IsAffineHom : MorphismProperty Scheme.{u}) (X := X)).lift
    ((MorphismProperty.overObj
      (@IsAffineHom : MorphismProperty Scheme.{u}) (X := Y)).ι ⋙
        CategoryTheory.Over.pullback f) (fun A ↦
      MorphismProperty.pullback_snd
        (P := (@IsAffineHom : MorphismProperty Scheme.{u}))
        A.obj.hom f A.property)

@[simp]
lemma affineOverPullback_obj_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : AffineOver Y) :
    ((affineOverPullback f).obj A).obj =
      (CategoryTheory.Over.pullback f).obj A.obj := rfl

@[simp]
lemma affineOverPullback_map_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : AffineOver Y} (g : A ⟶ B) :
    ((affineOverPullback f).map g).hom =
      (CategoryTheory.Over.pullback f).map g.hom := rfl

/-- Identity comparison for pullback of affine arrows. -/
noncomputable def affineOverPullbackId (X : Scheme.{u}) :
    affineOverPullback (𝟙 X) ≅ 𝟭 (AffineOver X) :=
  NatIso.ofComponents
    (fun A ↦ ObjectProperty.isoMk
      (P := MorphismProperty.overObj
        (@IsAffineHom : MorphismProperty Scheme.{u}) (X := X))
      ((CategoryTheory.Over.pullbackId (X := X)).app A.obj))
    (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact (CategoryTheory.Over.pullbackId (X := X)).hom.naturality f.hom)

/-- Composition comparison for pullback of affine arrows. -/
noncomputable def affineOverPullbackComp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    affineOverPullback (f ≫ g) ≅ affineOverPullback g ⋙ affineOverPullback f :=
  NatIso.ofComponents
    (fun A ↦ ObjectProperty.isoMk
      (P := MorphismProperty.overObj
        (@IsAffineHom : MorphismProperty Scheme.{u}) (X := X))
      ((CategoryTheory.Over.pullbackComp f g).app A.obj))
    (fun h ↦ by
      apply ObjectProperty.hom_ext
      exact (CategoryTheory.Over.pullbackComp f g).hom.naturality h.hom)

/-- Affine scheme arrows form a contravariant pseudofunctor under base
change. -/
noncomputable def affineOverPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1} := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (AffineOver X.unop))
    (fun f ↦ (affineOverPullback f.unop).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (affineOverPullbackId X.unop))
    (fun f g ↦ Cat.Hom.isoMk (affineOverPullbackComp g.unop f.unop)) ?_ ?_ ?_
  · intro W X Y Z f g h
    apply Cat.Hom₂.ext
    ext A
    apply ObjectProperty.hom_ext
    have H := congrArg (fun k ↦ k.toNatTrans.app A.obj)
      (overPullbackPseudofunctor.map₂_associator
        f.toLoc g.toLoc h.toLoc)
    rw [show (α_ f.toLoc g.toLoc h.toLoc).hom = eqToHom (by simp) from
      Subsingleton.elim _ _, PrelaxFunctor.map₂_eqToHom] at H
    dsimp at H
    exact H.symm
  · intro X Y f
    apply Cat.Hom₂.ext
    ext A
    apply ObjectProperty.hom_ext
    have H := congrArg (fun k ↦ k.toNatTrans.app A.obj)
      (overPullbackPseudofunctor.map₂_left_unitor f.toLoc)
    rw [show (λ_ f.toLoc).hom = eqToHom (by simp) from
      Subsingleton.elim _ _, PrelaxFunctor.map₂_eqToHom] at H
    dsimp at H
    exact H.symm
  · intro X Y f
    apply Cat.Hom₂.ext
    ext A
    apply ObjectProperty.hom_ext
    have H := congrArg (fun k ↦ k.toNatTrans.app A.obj)
      (overPullbackPseudofunctor.map₂_right_unitor f.toLoc)
    rw [show (ρ_ f.toLoc).hom = eqToHom (by simp) from
      Subsingleton.elim _ _, PrelaxFunctor.map₂_eqToHom] at H
    dsimp at H
    exact H.symm

/-- Relative spectrum, restricted to affine arrows over an affine base. -/
noncomputable def algSpecAffine (R : CommRingCat.{u}) :
    (CommAlgCat R)ᵒᵖ ⥤ AffineOver (Spec R) :=
  (MorphismProperty.overObj
    (@IsAffineHom : MorphismProperty Scheme.{u}) (X := Spec R)).lift
    (algSpec R) (fun _ ↦ by
      change IsAffineHom (Spec.map _)
      infer_instance)

@[simp]
lemma algSpecAffine_obj_obj (R : CommRingCat.{u}) (A : (CommAlgCat R)ᵒᵖ) :
    ((algSpecAffine R).obj A).obj = (algSpec R).obj A := rfl

@[simp]
lemma algSpecAffine_map_hom (R : CommRingCat.{u})
    {A B : (CommAlgCat R)ᵒᵖ} (f : A ⟶ B) :
    ((algSpecAffine R).map f).hom = (algSpec R).map f := rfl

/-- Affine arrows over `Spec R` are equivalent to opposites of commutative
`R`-algebras. -/
noncomputable def affineOverSpecEquivalence (R : CommRingCat.{u}) :
    (CommAlgCat R)ᵒᵖ ≌ AffineOver (Spec R) := by
  letI : (algSpecAffine R).Faithful := by
    dsimp [algSpecAffine]
    infer_instance
  letI : (algSpecAffine R).Full := by
    dsimp [algSpecAffine]
    infer_instance
  letI : (algSpecAffine R).EssSurj := by
    constructor
    intro X
    have hX : IsAffine X.obj.left :=
      @isAffine_of_isAffineHom _ _ X.obj.hom X.property inferInstance
    obtain ⟨A, ⟨e⟩⟩ :=
      (essImage_algSpec (R := R) (G := X.obj)).mpr hX
    refine ⟨A, ⟨ObjectProperty.isoMk
      (P := MorphismProperty.overObj
        (@IsAffineHom : MorphismProperty Scheme.{u}) (X := Spec R)) e⟩⟩
  letI : (algSpecAffine R).IsEquivalence := { }
  exact (algSpecAffine R).asEquivalence

end

end AlgebraicGeometry
