module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.3-morphisms-of-prestacks»
public import Mathlib.CategoryTheory.HomCongr
public import Mathlib.Logic.Small.Basic

/-!
# Transporting hom-sets between isomorphic fiber objects

Vertical isomorphisms between objects in a target fiber identify their hom-sets.
This is the conjugation step used after replacing stack-valued points by local
lifts to a presentation.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe w v₀ v₁ v₂ u₀ u₁ u₂

namespace CategoryTheory.BasedFunctor

variable {C : Type u₀} [Category.{v₀} C]
  {X : BasedCategory.{v₁, u₁} C} {Y : BasedCategory.{v₂, u₂} C}

/-- Isomorphic replacements of two objects in a target fiber induce the
conjugation equivalence on their hom-sets. -/
def homEquivOfIsoOnFiber (P : BasedFunctor X Y) {S : C}
    {x y : X.p.Fiber S} {a b : Y.p.Fiber S}
    (ex : (P.onFiber S).obj x ≅ a) (ey : (P.onFiber S).obj y ≅ b) :
    (a ⟶ b) ≃ ((P.onFiber S).obj x ⟶ (P.onFiber S).obj y) :=
  (ex.homCongr ey).symm

@[simp]
lemma homEquivOfIsoOnFiber_apply (P : BasedFunctor X Y) {S : C}
    {x y : X.p.Fiber S} {a b : Y.p.Fiber S}
    (ex : (P.onFiber S).obj x ≅ a) (ey : (P.onFiber S).obj y ≅ b)
    (f : a ⟶ b) :
    homEquivOfIsoOnFiber P ex ey f = ex.hom ≫ f ≫ ey.inv :=
  rfl

@[simp]
lemma homEquivOfIsoOnFiber_symm_apply (P : BasedFunctor X Y) {S : C}
    {x y : X.p.Fiber S} {a b : Y.p.Fiber S}
    (ex : (P.onFiber S).obj x ≅ a) (ey : (P.onFiber S).obj y ≅ b)
    (f : (P.onFiber S).obj x ⟶ (P.onFiber S).obj y) :
    (homEquivOfIsoOnFiber P ex ey).symm f = ex.inv ≫ f ≫ ey.hom :=
  rfl

/-- Smallness of the hom-set between two objects is invariant under replacing
both objects by isomorphic points in the same fiber. -/
theorem small_hom_of_iso_onFiber (P : BasedFunctor X Y) {S : C}
    {x y : X.p.Fiber S} {a b : Y.p.Fiber S}
    (ex : (P.onFiber S).obj x ≅ a) (ey : (P.onFiber S).obj y ≅ b)
    [Small.{w} ((P.onFiber S).obj x ⟶ (P.onFiber S).obj y)] :
    Small.{w} (a ⟶ b) :=
  (small_congr (homEquivOfIsoOnFiber P ex ey)).mpr inferInstance

end CategoryTheory.BasedFunctor
