module

public import StacksAndModuli.API.SmoothStalkReduced
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-!
# Smooth schemes over fields are geometrically reduced

Smoothness is stable under arbitrary base change.  After changing the ground field,
the resulting scheme is therefore again smooth over a field and hence reduced.

## Main result

* `AlgebraicGeometry.geometricallyReduced_of_smooth_toSpec_field`: a smooth scheme
  over a field is geometrically reduced.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A scheme smooth over a field is geometrically reduced over that field. -/
theorem geometricallyReduced_of_smooth_toSpec_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [Smooth f] : GeometricallyReduced f := by
  rw [geometricallyReduced_iff]
  intro L _ y Z fst snd h
  let _ : Smooth snd :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@Smooth : MorphismProperty Scheme.{u})) h inferInstance
  exact Scheme.isReduced_of_smooth_toSpec_field snd

end AlgebraicGeometry

end
