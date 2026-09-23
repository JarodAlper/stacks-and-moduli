module

public import StacksAndModuli.API.PseudofunctorCore
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.1-definition-of-a-prestack»
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-!
# Pointwise cores and prestacks

The Grothendieck construction of a contravariant category-valued pseudofunctor is a
fibered category.  After taking the pointwise core, its fibers are groupoids, so its
projection is a prestack.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open CategoryTheory.Functor Opposite

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- The fiber over `S` of the Grothendieck construction of the pointwise core of
`F` is a groupoid. -/
noncomputable instance coreFiberGroupoid
    (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) (S : 𝒮) :
    Groupoid ((forget F.core).Fiber S) := by
  letI : Groupoid (F.core.obj ⟨op S⟩) := by
    change Groupoid (Core (F.obj ⟨op S⟩))
    infer_instance
  let e := (Fiber.inducedFunctor (comp_const F.core S)).asEquivalence
  exact Groupoid.ofFullyFaithfulToGroupoid e.inverse e.fullyFaithfulInverse

/-- The Grothendieck projection of the pointwise core of a contravariant
category-valued pseudofunctor is a prestack. -/
noncomputable instance coreForgetIsFiberedInGroupoids
    (F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}) :
    (forget F.core).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.of_isFibered_of_isIso
    (forget F.core) (fun S _ _ _ ↦ by
      letI := coreFiberGroupoid F S
      infer_instance)

end CategoryTheory.Pseudofunctor.CoGrothendieck
