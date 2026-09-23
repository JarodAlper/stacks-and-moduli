module

public import Mathlib.CategoryTheory.Sites.Descent.IsStack

/-!
# Basic functoriality of the stack condition

This file supplies small reusable facts about Mathlib's category-valued stack predicate.
-/

@[expose] public section

open CategoryTheory

universe v' v u' u

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C]
variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

/-- A stack for a finer Grothendieck topology is a stack for every coarser topology. -/
theorem IsStack.of_le {J K : GrothendieckTopology C} (h : J ≤ K)
    [F.IsStack K] : F.IsStack J where
  toIsPrestack := by
    constructor
    intro S M N
    apply (IsPrestack.isSheaf K M N).of_le
    intro Y R hR
    rw [J.mem_over_iff] at hR
    rw [K.mem_over_iff]
    exact h _ hR
  essSurj_of_sieve R hR := IsStack.essSurj_of_sieve F R (h _ hR)

end CategoryTheory.Pseudofunctor
