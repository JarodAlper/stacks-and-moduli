module

public import StacksAndModuli.API.OverBasedProducts

/-!
# The based Yoneda equivalence for representable prestacks

This file packages the counit of the canonical equivalence between `overBased S`
and the prestack associated to `yoneda.obj S` as a based natural isomorphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v u

namespace CategoryTheory.BasedCategory

variable {C : Type u} [Category.{v} C]

/-- Passing from a representable prestack to its Yoneda presheaf prestack and back is
canonically isomorphic to the identity as a based functor. -/
def overBasedYonedaCounitIso (S : C) :
    (overBasedToOfPresheafYoneda S).comp (ofPresheafYonedaToOverBased S) ≅
      CategoryTheory.BasedFunctor.id (overBased S) :=
  BasedNatIso.mkNatIso
    (costructuredArrowYonedaOverEquivalence S).counitIso
    (fun x ↦ by
      apply over_isHomLift_of_left
      change IsHomLift (Functor.id C) (𝟙 x.left)
        ((costructuredArrowYonedaOverEquivalence S).counitIso.hom.app x).left
      exact IsHomLift.map (p := Functor.id C) (𝟙 x.left))

end CategoryTheory.BasedCategory
