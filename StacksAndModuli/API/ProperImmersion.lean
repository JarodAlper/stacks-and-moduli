module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper immersions

An immersion of schemes which is proper is a closed immersion.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- A proper immersion of schemes is a closed immersion. -/
theorem IsImmersion.isClosedImmersion_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] [IsProper f] :
    IsClosedImmersion f := by
  apply IsClosedImmersion.of_isPreimmersion f
  rw [← Set.image_univ]
  exact Scheme.Hom.isClosedMap f Set.univ isClosed_univ

end AlgebraicGeometry
