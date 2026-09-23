module

public import StacksAndModuli.API.GeometricFiberProperty
public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Étale target-locality of geometric-fibre properties

Every property imposed independently on the fibres over algebraically closed fields is
local on the target for the étale precoverage.  Indeed, a geometric point lifts through
an étale covering family, and associativity of pullbacks identifies the fibre before and
after that lift.

## Main declarations

* `AlgebraicGeometry.Scheme.exists_lift_to_etaleCover_of_isSepClosed`: a point over a
  separably closed field lifts to one member of an étale covering family;
* `AlgebraicGeometry.geometricallyOver_isLocalAtTarget_etalePrecoverage`: every property
  constructed with `geometricallyOver` is étale-local on the target.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A point over a separably closed field lifts to one member of an étale covering
family. -/
theorem exists_lift_to_etaleCover_of_isSepClosed
    {Y : Scheme.{u}} (U : Precoverage.ZeroHypercover.{u + 1} etalePrecoverage Y)
    {K : Type u} [Field K] [IsSepClosed K] (y : Spec (CommRingCat.of K) ⟶ Y) :
    ∃ (i : U.I₀) (s : Spec (CommRingCat.of K) ⟶ U.X i), s ≫ U.f i = y := by
  have hcover : Sieve.generate U.presieve₀ ∈ etaleTopology Y :=
    Precoverage.generate_mem_toGrothendieck U.mem₀
  obtain ⟨V, q, hq, t, ht⟩ :=
    (geometricFiber K).jointly_surjective (Sieve.generate U.presieve₀) hcover y
  obtain ⟨W, k, p, ⟨i⟩, rfl⟩ := hq
  refine ⟨i, t ≫ k, ?_⟩
  change t ≫ (k ≫ U.f i) = y at ht
  simpa only [Category.assoc] using ht

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Every property imposed on fibres over algebraically closed fields is local on the
target for arbitrary étale covering families. -/
theorem geometricallyOver_isLocalAtTarget_etalePrecoverage
    (P : GeometricFiberPredicate.{u}) :
    MorphismProperty.IsLocalAtTarget (geometricallyOver P)
      Scheme.etalePrecoverage := by
  apply MorphismProperty.IsLocalAtTarget.mk_of_isStableUnderBaseChange
  intro X Y f U h K _ _ y Z fst snd sq
  obtain ⟨i, s, hs⟩ :=
    Scheme.exists_lift_to_etaleCover_of_isSepClosed U y
  let l : Z ⟶ pullback f (U.f i) :=
    pullback.lift fst (snd ≫ s) (by rw [Category.assoc, hs, sq.w])
  have hright : IsPullback (pullback.fst f (U.f i))
      (pullback.snd f (U.f i)) f (U.f i) :=
    IsPullback.of_hasPullback f (U.f i)
  have houter : IsPullback
      (l ≫ pullback.fst f (U.f i)) snd f (s ≫ U.f i) := by
    simpa only [l, pullback.lift_fst, hs] using sq
  have hleft : IsPullback l snd (pullback.snd f (U.f i)) s :=
    houter.of_right (pullback.lift_snd fst (snd ≫ s) _) hright
  exact h i s l snd hleft

end AlgebraicGeometry
