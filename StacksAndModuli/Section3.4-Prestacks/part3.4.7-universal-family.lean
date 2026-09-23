module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.6a-classifying-stack-cartesian-diagrams»
public import StacksAndModuli.API.PointedCartesianFamily

/-!
# The universal family of smooth curves

This module formalizes `exer:universal-family-mg` (Exercise 3.4.42) of §3.4
(Prestacks) of *Stacks and Moduli*,
section label `sec:prestacks`.

As in Example 3.4.10, the genus condition is represented by an arbitrary
base-change-stable refinement `Q` of the smooth-curve property.  The marked
prestack consists of such families together with a section.  The universal
cartesian square is expressed fiberwise by the canonical equivalence between
sections of a pullback family and lifts to its total space.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExerUniversalFamilyMg

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange]

/-- **Exercise 3.4.42** (`exer:universal-family-mg`) (the implicit definition of
`ℳ_{g,1}`): the prestack of smooth-curve families in the chosen
base-change-stable genus class `Q`, equipped with a section. -/
abbrev pointedSmoothCurveSubprestack : BasedCategory Scheme.{u} :=
  CategoryTheory.pointedCartesianProperty (smoothCurveProperty.{u} ⊓ Q)

/-- Supporting instance for Exercise 3.4.42 (prestack assertion):
pointed smooth-curve families pull back along arbitrary base change. -/
instance pointedSmoothCurveSubprestack_isFiberedInGroupoids :
    (pointedSmoothCurveSubprestack Q).p.IsFiberedInGroupoids :=
  inferInstance

/-- **Exercise 3.4.42** (`exer:universal-family-mg`) (the forgetful morphism):
the morphism `ℳ_{g,1} → ℳ_g` forgets the chosen section. -/
def forgetMarkedPoint :
    BasedFunctor (pointedSmoothCurveSubprestack Q) (smoothCurveSubprestack Q) :=
  CategoryTheory.pointedCartesianProperty.forget (smoothCurveProperty.{u} ⊓ Q)

variable {Q}

/-- **Exercise 3.4.42** (`exer:universal-family-mg`): let `f : X → S` be a
family represented by an object of `ℳ_g`, and let `g : T → S`.  A section
of the pulled-back family `X ×_S T → T` is canonically equivalent to a lift
`T → X` of `g`.  Under the 2-Yoneda lemma this is precisely the equivalence on
fibers asserting that

`X → ℳ_{g,1}` over `S → ℳ_g`

is a cartesian square of prestacks; hence `ℳ_{g,1} → ℳ_g` is the
universal family. -/
noncomputable def universalFamilyFiberEquiv {X S T : Scheme.{u}} (f : X ⟶ S)
    (_hf : (smoothCurveProperty.{u} ⊓ Q) f) (g : T ⟶ S) :
    CategoryTheory.PullbackSection f g ≃ CategoryTheory.LiftOver f g :=
  CategoryTheory.pullbackSectionEquiv f g

end AlgebraicGeometry.Scheme

end ExerUniversalFamilyMg
