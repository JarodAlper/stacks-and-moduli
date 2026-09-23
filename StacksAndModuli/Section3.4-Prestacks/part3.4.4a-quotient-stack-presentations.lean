module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.2a-action-quotient-prestacks»
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.4-two-yoneda-lemma»

/-!
# Quotient stack presentations

This module formalizes `ex:quotient-stack-presentation` of §3.4 (Prestacks) of
*Stacks and Moduli*, section label
`sec:prestacks`.

For a smooth affine group scheme `G → S` acting on `U`, the trivial principal
bundle `G ×ₛ U → U`, together with the action map to `U`, is an object of the
quotient stack over `U`. The 2-Yoneda construction turns this object into the
canonical morphism `U → [U/G]`.

Main declaration: `AlgebraicGeometry.Scheme.quotientPresentation`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExQuotientStackPresentation

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme

open CategoryTheory.BasedCategory

variable {S : Scheme.{u}} (G U : Over S) [GrpObj G] [ModObj G U]
  [Smooth G.hom] [IsAffineHom G.hom]

/-- Background construction for Example 3.4.26 (the
object): the trivial principal bundle `G ×ₛ U → U`, equipped with the action
map `G ×ₛ U → U`, is an object of `[U/G]` over `U`. -/
noncomputable def quotientPresentationObject : ActionQuotientObj G U where
  carrier :=
    { base := U
      bundle := GlobalPrincipalBundle.trivial G U }
  map := GlobalPrincipalBundle.trivialActionMap G U
  equivariant := GlobalPrincipalBundle.trivialActionMap_equivariant G U

/-- Background construction for Example 3.4.26 (the object in the
fiber): the quotient presentation object lies in `[U/G](U)`. -/
noncomputable def quotientPresentationFiber :
    (actionQuotientPrestack G U).p.Fiber U :=
  CategoryTheory.Functor.Fiber.mk
    (p := (actionQuotientPrestack G U).p)
    (a := quotientPresentationObject G U) rfl

/-- **Example 3.4.26** (`ex:quotient-stack-presentation`): under the 2-Yoneda
lemma, the trivial torsor with its action map determines the canonical morphism
of prestacks `U → [U/G]`. -/
noncomputable def quotientPresentation :
    overBased U ⥤ᵇ actionQuotientPrestack G U :=
  twoYonedaPullback U (quotientPresentationFiber G U)

/-- Supporting identification for Example 3.4.26 (the 2-Yoneda
identification): evaluating the canonical morphism at `id_U` recovers, up to
canonical isomorphism, the trivial torsor and its action map. -/
noncomputable def quotientPresentationEvalIso :
    (twoYonedaEval (𝒳 := actionQuotientPrestack G U) U).obj
      (quotientPresentation G U) ≅ quotientPresentationFiber G U := by
  let q := CategoryTheory.Functor.IsPreFibered.pullbackMap
    (quotientPresentationFiber G U).2 (𝟙 U)
  haveI : IsIso q :=
    CategoryTheory.Functor.IsFiberedInGroupoids.isIso_of_isHomLift_isIso
      (p := (actionQuotientPrestack G U).p) (𝟙 U) q
  exact asIso ⟨q, inferInstance⟩

end AlgebraicGeometry.Scheme

end ExQuotientStackPresentation
