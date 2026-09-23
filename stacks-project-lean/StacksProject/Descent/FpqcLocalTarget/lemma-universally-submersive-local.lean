module

public import StacksAndModuli.API.UniversallySubmersive
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Universally submersive morphisms are fpqc local on the target

This file proves Stacks Project tag **0CEW**: universal submersiveness descends
along quasi-compact, flat, surjective morphisms.
-/

@[expose] public section

open CategoryTheory Limits MorphismProperty

universe u

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0CEW** (`descent-lemma-universally-submersive-local`): the property of
being universally submersive is fpqc local on the target. -/
@[stacks 0CEW]
instance descendsAlong_universallySubmersive_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @UniversallySubmersive
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong
  intro R X Y f g hf hfst
  letI : Surjective f := hf.1.1
  letI : Flat f := hf.1.2
  letI : QuasiCompact f := hf.2
  constructor
  apply universally_mk'
  intro T t _
  let p := pullback.fst (pullback.fst f t) (pullback.fst f g)
  let r : pullback (pullback.fst f t) (pullback.fst f g) ⟶ pullback t g :=
    pullback.map _ _ _ _ (pullback.snd _ _) (pullback.snd _ _) f
      (pullback.condition ..) (pullback.condition ..)
  have hp : Topology.IsQuotientMap p :=
    hfst.universally_isQuotientMap _ _ _
      (IsPullback.of_hasPullback (pullback.fst f t) (pullback.fst f g))
  have hc : Topology.IsQuotientMap (pullback.snd f t) :=
    Flat.isQuotientMap_of_surjective _
  have hcomp : topologically Topology.IsQuotientMap (p ≫ pullback.snd f t) := by
    change Topology.IsQuotientMap (_ ∘ _)
    exact hc.comp hp
  have heq : p ≫ pullback.snd f t = r ≫ pullback.fst t g := by
    dsimp [p, r]
    rw [pullback.lift_fst]
  rw [heq] at hcomp
  exact Topology.IsQuotientMap.of_comp r.continuous
    (pullback.fst t g).continuous hcomp

end AlgebraicGeometry
