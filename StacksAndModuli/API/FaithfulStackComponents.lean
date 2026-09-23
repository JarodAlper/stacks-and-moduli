module

public import StacksAndModuli.API.PresheafRepresentedByStackSheaf

/-!
# Components of faithful stacks

The connected-component presheaf of a stack whose projection to the base is faithful
is a sheaf.  This packages the universe-polymorphic category-of-elements criterion
with the canonical component-prestack comparison.
-/

@[expose] public section

open CategoryTheory Functor Opposite

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {J : GrothendieckTopology C}
  {X : BasedCategory.{v₂, u₂} C}
  [X.p.IsFiberedInGroupoids] [X.p.Faithful]

/-- The presheaf of fiberwise connected components of a faithful stack is a sheaf. -/
theorem fiberComponents_isSheaf [IsStack J X] :
    Presieve.IsSheaf J (fiberComponents (𝒳 := X)) := by
  let E := componentPrestackComparison (𝒳 := X)
  let _ : E.toFunctor.IsEquivalence :=
    isEquivalence_componentPrestackComparison (𝒳 := X)
  exact Presieve.isSheaf_of_isRepresentedByStack_elements E

end CategoryTheory.BasedCategory
