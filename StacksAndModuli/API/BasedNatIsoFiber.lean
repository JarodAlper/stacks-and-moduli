module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.3-morphisms-of-prestacks»

/-!
# Based natural isomorphisms on fibers

A based natural isomorphism restricts objectwise to an isomorphism in every fiber.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₀ v₁ v₂ u₀ u₁ u₂

namespace CategoryTheory.BasedNatIso

variable {C : Type u₀} [Category.{v₀} C]
  {𝒳 : BasedCategory.{v₁, u₁} C}
  {𝒴 : BasedCategory.{v₂, u₂} C}

/-- The component of a based natural isomorphism, regarded as an isomorphism in a
fiber category. -/
def appOnFiber {F G : BasedFunctor 𝒳 𝒴} (e : F ≅ G)
    (S : C) (x : 𝒳.p.Fiber S) :
    (F.onFiber S).obj x ≅ (G.onFiber S).obj x := by
  obtain ⟨x, hx⟩ := x
  subst S
  exact
    { hom := ⟨e.hom.toNatTrans.app x,
        BasedNatTrans.app_isHomLift (α := e.hom) x⟩
      inv := ⟨e.inv.toNatTrans.app x,
        BasedNatTrans.app_isHomLift (α := e.inv) x⟩
      hom_inv_id := by
        apply Fiber.hom_ext
        exact congrArg (fun t ↦ t.toNatTrans.app x) e.hom_inv_id
      inv_hom_id := by
        apply Fiber.hom_ext
        exact congrArg (fun t ↦ t.toNatTrans.app x) e.inv_hom_id }

@[simp]
lemma appOnFiber_hom_val {F G : BasedFunctor 𝒳 𝒴} (e : F ≅ G)
    (S : C) (x : 𝒳.p.Fiber S) :
    Fiber.fiberInclusion.map (appOnFiber e S x).hom =
      e.hom.toNatTrans.app x.1 :=
  by
    obtain ⟨x, hx⟩ := x
    subst S
    rfl

@[simp]
lemma appOnFiber_inv_val {F G : BasedFunctor 𝒳 𝒴} (e : F ≅ G)
    (S : C) (x : 𝒳.p.Fiber S) :
    Fiber.fiberInclusion.map (appOnFiber e S x).inv =
      e.inv.toNatTrans.app x.1 :=
  by
    obtain ⟨x, hx⟩ := x
    subst S
    rfl

end CategoryTheory.BasedNatIso
