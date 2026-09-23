module

public import StacksAndModuli.API.AffineArrowPseudofunctor
public import StacksAndModuli.API.ArrowCartesian
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.CategoryTheory.Sites.Descent.DescentData

/-!
# Descent data for scheme arrows as cartesian-arrow diagrams

This file converts descent data for the pseudofunctor of scheme arrows under
base change into a functor to the category of cartesian arrows.  The
conversion is the bridge between pseudofunctor descent and the raw gluing API
for cartesian scheme arrows.

## Main definitions

- `AlgebraicGeometry.OverPullbackDescent.cartesianFunctor`: the cartesian-arrow
  diagram associated to descent data for scheme arrows.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.OverPullbackDescent

noncomputable section

variable {S : Scheme.{u}} {R : Sieve S}

/-- Descent data, indexed by a sieve, for arbitrary scheme arrows under base
change. -/
abbrev Data := overPullbackPseudofunctor.DescentData
  (fun q : R.arrows.category ↦ q.obj.hom)

/-- Descent data, indexed by a sieve, for affine scheme arrows under base
change. -/
abbrev AffineData := affineOverPseudofunctor.DescentData
  (fun q : R.arrows.category ↦ q.obj.hom)

/-- Pullback of a morphism of affine arrows agrees with pullback of its
underlying morphism after forgetting the affine-property witnesses. -/
lemma affineMap_map_hom {X Y : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) {A B : affineOverPseudofunctor.obj X} (k : A ⟶ B) :
    (((affineOverPseudofunctor.map f).toFunctor.map k).hom) =
      (overPullbackPseudofunctor.map f).toFunctor.map k.hom := by
  rfl

/-- After forgetting the affine-property witness, the composition comparison
for affine pullback is the composition comparison for arbitrary arrows. -/
lemma affineMapComp_hom_hom {X Y Z : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : affineOverPseudofunctor.obj X) :
    (((affineOverPseudofunctor.mapComp f g).hom.toNatTrans.app A).hom) =
      (overPullbackPseudofunctor.mapComp f g).hom.toNatTrans.app A.obj := by
  rfl

/-- The hom of the flexible affine-pullback composition comparison agrees
with the corresponding comparison for arbitrary arrows after forgetting the
affine-property witness. -/
lemma affineMapComp'_hom_hom {X Y Z : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg)
    (A : affineOverPseudofunctor.obj X) :
    (((affineOverPseudofunctor.mapComp' f g fg h).hom.toNatTrans.app A).hom) =
      (overPullbackPseudofunctor.mapComp' f g fg h).hom.toNatTrans.app A.obj := by
  subst fg
  rw [affineOverPseudofunctor.mapComp'_eq_mapComp,
    overPullbackPseudofunctor.mapComp'_eq_mapComp]
  exact affineMapComp_hom_hom f g A

/-- The inverse of the flexible affine-pullback composition comparison agrees
with the corresponding comparison for arbitrary arrows after forgetting the
affine-property witness. -/
lemma affineMapComp'_inv_hom {X Y Z : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (h : f ≫ g = fg)
    (A : affineOverPseudofunctor.obj X) :
    (((affineOverPseudofunctor.mapComp' f g fg h).inv.toNatTrans.app A).hom) =
      (overPullbackPseudofunctor.mapComp' f g fg h).inv.toNatTrans.app A.obj := by
  subst fg
  rw [affineOverPseudofunctor.mapComp'_eq_mapComp,
    overPullbackPseudofunctor.mapComp'_eq_mapComp]
  rfl

/-- Forget the affine condition in affine-arrow descent data. -/
def forgetAffine (D : AffineData (R := R)) : Data (R := R) where
  obj q := (D.obj q).obj
  hom {Y} q {i₁ i₂} f₁ f₂ hf₁ hf₂ :=
    (D.hom q f₁ f₂ hf₁ hf₂).hom
  pullHom_hom {Y' Y} g q q' hq {i₁ i₂} f₁ f₂ hf₁ hf₂
      gf₁ gf₂ hgf₁ hgf₂ := by
    have h := congrArg (fun k ↦ k.hom)
      (D.pullHom_hom g q q' hq f₁ f₂ hf₁ hf₂ gf₁ gf₂
        hgf₁ hgf₂)
    unfold Pseudofunctor.LocallyDiscreteOpToCat.pullHom at h ⊢
    change
      ((affineOverPseudofunctor.mapComp' f₁.op.toLoc g.op.toLoc
          gf₁.op.toLoc _).hom.toNatTrans.app (D.obj i₁)).hom ≫
        ((affineOverPseudofunctor.map g.op.toLoc).toFunctor.map
          (D.hom q f₁ f₂ hf₁ hf₂)).hom ≫
        ((affineOverPseudofunctor.mapComp' f₂.op.toLoc g.op.toLoc
          gf₂.op.toLoc _).inv.toNatTrans.app (D.obj i₂)).hom =
        (D.hom q' gf₁ gf₂).hom at h
    simp only [affineMapComp'_hom_hom, affineMapComp'_inv_hom,
      affineMap_map_hom] at h
    exact h
  hom_self {Y} q {i} g hg := by
    have h := congrArg (fun k ↦ k.hom) (D.hom_self q g hg)
    exact h
  hom_comp {Y} q {i₁ i₂ i₃} f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    have h := congrArg (fun k ↦ k.hom)
      (D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃)
    exact h

/-- The inverse composition comparison for over-category pullback followed by
the projection to the original total space is the iterated pullback
projection. -/
lemma pullbackComp_inv_left_fst {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : CategoryTheory.Over Z) :
    ((CategoryTheory.Over.pullbackComp f g).inv.app A).left ≫
        pullback.fst A.hom (f ≫ g) =
      pullback.fst (pullback.snd A.hom g) f ≫
        pullback.fst A.hom g := by
  simp [CategoryTheory.Over.pullbackComp]

/-- A transition map in a scheme-arrow descent datum, regarded as a
cartesian square. -/
def cartesianMap (D : Data (R := R)) {q r : R.arrows.category}
    (k : q ⟶ r) :
    CategoryTheory.CartesianArrowHom
      (CategoryTheory.ArrowCartesian.mk (D.obj q).hom)
      (CategoryTheory.ArrowCartesian.mk (D.obj r).hom) := by
  let e : D.obj q ≅
      (CategoryTheory.Over.pullback k.hom.left).obj (D.obj r) :=
    ((CategoryTheory.Over.pullbackId (X := q.obj.left)).app
      (D.obj q)).symm ≪≫
        D.iso q.obj.hom (𝟙 q.obj.left) k.hom.left
  let eLeft : (D.obj q).left ≅
      ((CategoryTheory.Over.pullback k.hom.left).obj (D.obj r)).left :=
    (CategoryTheory.Over.forget q.obj.left).mapIso e
  refine
    { left := eLeft.hom ≫ pullback.fst (D.obj r).hom k.hom.left
      right := k.hom.left
      isPullback := ?_ }
  letI : IsIso eLeft.hom := eLeft.isIso_hom
  have h₁ : IsPullback eLeft.hom (D.obj q).hom
      ((CategoryTheory.Over.pullback k.hom.left).obj (D.obj r)).hom
      (𝟙 q.obj.left) := by
    apply IsPullback.of_horiz_isIso
    exact ⟨by
      change e.hom.left ≫
        ((CategoryTheory.Over.pullback k.hom.left).obj (D.obj r)).hom =
          (D.obj q).hom
      exact e.hom.w⟩
  exact h₁.paste_horiz
    (IsPullback.of_hasPullback (D.obj r).hom k.hom.left)

private def totalMap (D : Data (R := R))
    {q r : R.arrows.category} (k : q ⟶ r) :
    Pseudofunctor.CoGrothendieck.Hom
      ⟨q.obj.left, D.obj q⟩ ⟨r.obj.left, D.obj r⟩ where
  base := k.hom.left
  fiber :=
    (((CategoryTheory.Over.pullbackId (X := q.obj.left)).app
      (D.obj q)).symm ≪≫
        D.iso q.obj.hom (𝟙 q.obj.left) k.hom.left).hom

private def totalFunctor (D : Data (R := R)) :
    CategoryTheory.Functor R.arrows.category
      (Pseudofunctor.CoGrothendieck overPullbackPseudofunctor) where
  obj q := ⟨q.obj.left, D.obj q⟩
  map k := totalMap D k
  map_id q := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext
    · dsimp [totalMap]
      rw [D.hom_self q.obj.hom (𝟙 q.obj.left) (by simp)]
      simp only [Category.comp_id]
      rfl
    · rfl
  map_comp {X Y Z} k l := by
    apply Pseudofunctor.CoGrothendieck.Hom.ext
    · dsimp [totalMap]
      simp only [Category.comp_id]
      rw [← D.hom_comp X.obj.hom (𝟙 X.obj.left)
        k.hom.left (k.hom.left ≫ l.hom.left) (by simp) k.hom.w
        (by simp [Category.assoc, l.hom.w, k.hom.w])]
      rw [← D.pullHom_hom k.hom.left Y.obj.hom X.obj.hom
        k.hom.w (𝟙 Y.obj.left) l.hom.left (by simp) l.hom.w
        k.hom.left (k.hom.left ≫ l.hom.left) (by simp) rfl]
      dsimp [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
      rw [overPullbackPseudofunctor.mapComp'_id_comp_hom_app]
      simp only [Functor.map_comp, Category.assoc]
      rw [show
        (overPullbackPseudofunctor.mapId
          ⟨Opposite.op Y.obj.left⟩).inv.toNatTrans.app (D.obj Y) =
            (CategoryTheory.Over.pullbackId
              (X := Y.obj.left)).inv.app (D.obj Y) from rfl]
      simp only [Pseudofunctor.mapComp'_eq_mapComp]
    · rfl

/-- Descent data for arbitrary scheme arrows determines a diagram of arrows
whose transition squares are cartesian. -/
def cartesianFunctor (D : Data (R := R)) :
    CategoryTheory.Functor R.arrows.category
      (CategoryTheory.ArrowCartesian Scheme.{u}) where
  obj q := CategoryTheory.ArrowCartesian.mk (D.obj q).hom
  map k := cartesianMap D k
  map_id q := by
    apply CategoryTheory.CartesianArrowHom.ext
    · dsimp [cartesianMap]
      rw [D.hom_self q.obj.hom (𝟙 q.obj.left) (by simp)]
      have H := congrArg CategoryTheory.Over.Hom.left
        ((CategoryTheory.Over.pullbackId
          (X := q.obj.left)).inv_hom_id_app (D.obj q))
      exact H
    · rfl
  map_comp k l := by
    apply CategoryTheory.CartesianArrowHom.ext
    · dsimp [cartesianMap]
      have h := Pseudofunctor.CoGrothendieck.Hom.congr
        ((totalFunctor D).map_comp k l)
      dsimp [totalFunctor, totalMap] at h
      simp only [Category.comp_id] at h
      have hleft := congrArg CategoryTheory.Over.Hom.left h
      simp only [CategoryTheory.Over.comp_left] at hleft
      rw [hleft]
      dsimp [overPullbackPseudofunctor,
        CategoryTheory.Bicategory.Adj.rightPseudofunctor,
        OverAdj.pseudofunctor, OverAdj.adjMap, OverAdj.adjMapComp]
      simp only [Category.assoc]
      rw [pullbackComp_inv_left_fst]
      simp [Category.assoc]
      change _ = (cartesianMap D k).left ≫ (cartesianMap D l).left
      dsimp [cartesianMap]
      simp only [Category.assoc]
    · rfl

/-- The cartesian-arrow diagram underlying affine-arrow descent data. -/
def affineCartesianFunctor (D : AffineData (R := R)) :
    CategoryTheory.Functor R.arrows.category
      (CategoryTheory.ArrowCartesian Scheme.{u}) :=
  cartesianFunctor (forgetAffine D)

end

end AlgebraicGeometry.OverPullbackDescent
