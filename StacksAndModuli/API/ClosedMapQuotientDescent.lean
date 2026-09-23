module

public import Mathlib.Topology.Maps.Basic

/-!
# Descent of closed maps across quotient maps

A map is closed if a pointwise-cartesian base change is closed and the map on the
base is a quotient map.  The result is stated for arbitrary topological spaces so that
stack point spaces can use it without exposing presentation-specific details.

## Main result

* `IsClosedMap.of_isQuotientMap_baseChange`: descent of closedness through a
  pointwise-cartesian square.
-/

@[expose] public section

open Set Topology

universe u₁ u₂ u₃ u₄

/-- Suppose a commutative square of maps of topological spaces has the point-lifting
property of a cartesian square.  If the upper horizontal map is closed, the left
vertical map is continuous, and the lower horizontal map is a quotient map, then the
original map is closed. -/
theorem IsClosedMap.of_isQuotientMap_baseChange
    {X : Type u₁} {X' : Type u₂} {Y : Type u₃} {Y' : Type u₄}
    [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]
    [TopologicalSpace Y']
    {f : X → Y} {f' : X' → Y'} {p : X' → X} {q : Y' → Y}
    (hq : IsQuotientMap q) (hp : Continuous p) (hf' : IsClosedMap f')
    (hcomm : ∀ x', f (p x') = q (f' x'))
    (hlift : ∀ x y', f x = q y' → ∃ x', p x' = x ∧ f' x' = y') :
    IsClosedMap f := by
  intro C hC
  rw [← hq.isClosed_preimage]
  have hpre : q ⁻¹' (f '' C) = f' '' (p ⁻¹' C) := by
    ext y'
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨x', hpx, hfx'⟩ := hlift x y' hxy
      exact ⟨x', by simpa only [Set.mem_preimage, hpx] using hx, hfx'⟩
    · rintro ⟨x', hx', rfl⟩
      exact ⟨p x', hx', hcomm x'⟩
  rw [hpre]
  exact hf' _ (hC.preimage hp)

