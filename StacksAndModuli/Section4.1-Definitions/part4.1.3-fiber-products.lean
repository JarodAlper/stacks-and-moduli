module

public import StacksAndModuli.API.AlgebraicStackFiberProductPresentation
public import StacksAndModuli.API.RepresentableWithProdMap
public import StacksAndModuli.API.SurjectiveEtaleSourceLocal

/-!
# Fiber products of Deligne–Mumford and algebraic stacks

This module completes the unlabeled fiber-products exercise of §4.1 (Definitions of
algebraic spaces and stacks) of *Stacks and Moduli*,
section label `sec:algebraic-spaces-and-stacks`.

The algebraic-space case is proved in the preceding part.  Here a fiber product of stack
presentations is first represented by an algebraic space using representability of the
middle stack's diagonal, and an étale scheme atlas of that algebraic space supplies the
required presentation.

Main results:

- `AlgebraicGeometry.IsDeligneMumfordStack.fiberProduct`;
- `AlgebraicGeometry.IsAlgebraicStack.fiberProduct`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefAlgebraicStack

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe vX uX vY uY vY' uY' u

namespace AlgebraicGeometry

/-- API lemma for Section 4.1 (the unlabeled fiber-products
exercise): fiber products exist for Deligne–Mumford stacks — the fiber product of
prestacks of two morphisms of Deligne–Mumford stacks is a Deligne–Mumford stack. -/
theorem IsDeligneMumfordStack.fiberProduct
    {X : BasedCategory.{vX, uX} Scheme.{u}}
    {Y : BasedCategory.{vY, uY} Scheme.{u}}
    {Y' : BasedCategory.{vY', uY'} Scheme.{u}}
    [IsDeligneMumfordStack X] [IsDeligneMumfordStack Y]
    [IsDeligneMumfordStack Y']
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) :
    IsDeligneMumfordStack (fiberProduct F G) := by
  refine ⟨isStack_fiberProduct Scheme.etaleTopology F G, ?_⟩
  obtain ⟨U, pX, hpX⟩ := IsDeligneMumfordStack.exists_presentation (𝒳 := X)
  obtain ⟨V, pY, hpY⟩ := IsDeligneMumfordStack.exists_presentation (𝒳 := Y')
  have hlocal := fun ⦃S' S T⦄ p f hp ↦
    surjectiveEtale_iff_comp_of_surjectiveEtale
      (X' := S') (X := S) (Y := T) p f hp
  have hprod := hpX.prodMap hpY hlocal
  exact exists_fiberProduct_presentation F G hprod hlocal

/-- API lemma for Section 4.1 (the unlabeled fiber-products
exercise): fiber products exist for algebraic stacks — the fiber product of prestacks of
two morphisms of algebraic stacks is an algebraic stack. -/
theorem IsAlgebraicStack.fiberProduct
    {X : BasedCategory.{vX, uX} Scheme.{u}}
    {Y : BasedCategory.{vY, uY} Scheme.{u}}
    {Y' : BasedCategory.{vY', uY'} Scheme.{u}}
    [IsAlgebraicStack X] [IsAlgebraicStack Y] [IsAlgebraicStack Y']
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) :
    IsAlgebraicStack (fiberProduct F G) := by
  refine ⟨isStack_fiberProduct Scheme.etaleTopology F G, ?_⟩
  obtain ⟨U, pX, hpX⟩ := IsAlgebraicStack.exists_presentation (𝒳 := X)
  obtain ⟨V, pY, hpY⟩ := IsAlgebraicStack.exists_presentation (𝒳 := Y')
  have hlocal := fun ⦃S' S T⦄ p f hp ↦
    surjectiveSmooth_iff_comp_of_surjectiveEtale
      (X' := S') (X := S) (Y := T) p f hp
  have hprod := hpX.prodMap hpY hlocal
  exact exists_fiberProduct_presentation F G hprod hlocal

end AlgebraicGeometry

end DefAlgebraicStack
