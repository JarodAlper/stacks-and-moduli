module

public import StacksAndModuli.API.CoreCoGrothendieckStack
public import StacksAndModuli.API.RelativeYonedaCartesianCore
public import StacksAndModuli.API.StackEquivalence

/-!
# From pointwise representable sheaves to Cartesian arrows

The pointwise core of the pseudofunctor of sheaves represented by `P`-morphisms has a
Grothendieck construction which is equivalent, over schemes, to the category of
`P`-morphisms and Cartesian squares.  Consequently its pseudofunctor stack condition
transfers to the geometric Cartesian-arrow model.
-/

@[expose] public section

open CategoryTheory Opposite

universe w u

namespace CategoryTheory.GrothendieckTopology

variable (J : GrothendieckTopology AlgebraicGeometry.Scheme.{u}) [J.Subcanonical]
variable (P : MorphismProperty AlgebraicGeometry.Scheme.{u}) [P.IsStableUnderBaseChange]

/-- Relative Yoneda supplies the stack bridge from the pointwise core of
`P`-representable sheaves to Cartesian `P`-arrows. -/
theorem representableSheafStackBridge :
    RepresentableSheafStackBridge.{w, u, u + 1} J P := by
  intro h
  let RF := ((J.representableByPropertyULift.{w} P).fullsubcategory).core
  let _ : RF.IsStack J := h
  let _ : BasedCategory.IsStack J (RepresentableCoreBased.{w} J P) := by
    infer_instance
  exact BasedCategory.IsStack.of_equivalence
    (representableCoreBasedFunctor.{w} J P)

end CategoryTheory.GrothendieckTopology
