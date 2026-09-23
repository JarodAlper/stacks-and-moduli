module

public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.4-fiber-products»
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The explicit fiber product of representable presheaves

The Yoneda embedding preserves limits (`CategoryTheory.yonedaFunctor_preservesLimits`), so
the fiber product of two representable presheaves is again representable: it is represented
by the pullback in the ambient category. What is *not* immediate is the comparison with the
**explicit** fiber product `CategoryTheory.Presheaf.fiberProduct` — the presheaf of
compatible pairs — since that is a hand-built presheaf rather than a categorical limit.
The comparison is supplied here by pairing the two limit descriptions of the same cospan.

This is the form the identification is needed in: the action groupoid
`AlgebraicGeometry.PresheafGroupoid.ofAction` of a group scheme acting on a scheme has
`R = G ×_S U` built with `Presheaf.fiberProduct`, and recognizing it as a representable
presheaf is what makes the algebraicity theorems of §4.4 applicable to it.

## Main definitions

* `CategoryTheory.Presheaf.fiberProductYonedaIso`: `Mor(-, X ×_Z Y) ≅ Mor(-, X) ×_{Mor(-,
  Z)} Mor(-, Y)`.

## Main results

* `CategoryTheory.Presheaf.isPullback_yoneda_map`: the Yoneda image of a pullback square is
  a pullback square of presheaves.
* `CategoryTheory.Presheaf.fiberProduct_isRepresentable`: the explicit fiber product of two
  representable presheaves is representable.
* `CategoryTheory.Presheaf.fiberProductYonedaIso_hom_comp_fst` and
  `…_hom_comp_snd`: the isomorphism is compatible with the two projections.
-/

@[expose] public section

namespace CategoryTheory.Presheaf

open CategoryTheory Limits

universe v u

variable {C : Type u} [Category.{v} C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The Yoneda image of a pullback square is a pullback square of presheaves: `yoneda`
preserves all limits that exist. -/
lemma isPullback_yoneda_map [HasPullback f g] :
    IsPullback (yoneda.map (pullback.fst f g)) (yoneda.map (pullback.snd f g))
      (yoneda.map f) (yoneda.map g) :=
  (IsPullback.of_hasPullback f g).map yoneda

/-- API theorem supporting Equation 3.3.13: the presheaf of compatible pairs
`Mor(-, X) ×_{Mor(-, Z)} Mor(-, Y)` is represented by the pullback `X ×_Z Y`. -/
noncomputable def fiberProductYonedaIso [HasPullback f g] :
    yoneda.obj (pullback f g) ≅ fiberProduct (yoneda.map f) (yoneda.map g) :=
  IsLimit.conePointUniqueUpToIso (isPullback_yoneda_map f g).isLimit
    (fiberProduct.isLimit (yoneda.map f) (yoneda.map g))

/-- The comparison isomorphism is compatible with the first projection. -/
@[reassoc (attr := simp)]
lemma fiberProductYonedaIso_hom_comp_fst [HasPullback f g] :
    (fiberProductYonedaIso f g).hom ≫ fiberProduct.fst (yoneda.map f) (yoneda.map g) =
      yoneda.map (pullback.fst f g) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left

/-- The comparison isomorphism is compatible with the second projection. -/
@[reassoc (attr := simp)]
lemma fiberProductYonedaIso_hom_comp_snd [HasPullback f g] :
    (fiberProductYonedaIso f g).hom ≫ fiberProduct.snd (yoneda.map f) (yoneda.map g) =
      yoneda.map (pullback.snd f g) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right

/-- The explicit fiber product of two representable presheaves is representable. -/
instance fiberProduct_isRepresentable [HasPullback f g] :
    (fiberProduct (yoneda.map f) (yoneda.map g)).IsRepresentable :=
  Functor.IsRepresentable.mk' (fiberProductYonedaIso f g)

end CategoryTheory.Presheaf
