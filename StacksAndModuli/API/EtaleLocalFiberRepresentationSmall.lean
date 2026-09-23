module

public import StacksAndModuli.API.FiberProductSmallSheafRepresentation
public import StacksAndModuli.API.QuotientStackPresentation

/-!
# Étale-local fiber representations from small self-intersections

This file joins two independent ingredients for representability of a prestack map.
A small represented self-intersection supplies a global small sheaf representation of
each faithful stack-valued fiber.  A scheme representation after one surjective étale
base change then supplies the local algebraic-space clause required by
`BasedFunctor.EtaleLocalFiberRepresentation`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {Ycat : BasedCategory.{v₃, u₃} Scheme.{u}}
  {T : Scheme.{u}} (g : overBased T ⥤ᵇ Ycat)

/-- Construct an étale-local fiber representation when the source is a small
presheaf, its self-intersection is represented by a small presheaf, and one
surjective étale base change of the fiber is represented by a scheme. -/
noncomputable def EtaleLocalFiberRepresentation.of_smallSelfIntersection
    {U R : Scheme.{u}ᵒᵖ ⥤ Type u}
    {F : ofPresheaf U ⥤ᵇ Ycat}
    [Ycat.p.IsFiberedInGroupoids]
    [(fiberProduct F g).p.Faithful]
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)]
    (hR : (fiberProduct F F).IsRepresentedByPresheaf R)
    {S W : Scheme.{u}} (p : S ⟶ T) (hpEtale : Etale p)
    (hpSurjective : Surjective p)
    (K : overBased W ⥤ᵇ
      fiberProduct F ((overBased.map p).comp g))
    (hK : K.toFunctor.IsEquivalence) :
    EtaleLocalFiberRepresentation F T g := by
  let D := smallEtaleSheafRepresentation_fiberProduct F g hR
  exact EtaleLocalFiberRepresentation.of_localSchemeRepresentation
    F T g D.isSheaf D.representation D.representation_isEquivalence
    p hpEtale hpSurjective K hK

end AlgebraicGeometry.BasedFunctor
