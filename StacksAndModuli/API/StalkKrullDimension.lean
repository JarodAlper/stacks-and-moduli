module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension

/-!
# Krull dimension of scheme stalks

This file compares the Krull dimension of a scheme's local ring at a point with the
topological Krull dimension of the whole scheme.

## Main result

* `AlgebraicGeometry.Scheme.ringKrullDim_stalk_le_topologicalKrullDim`: the dimension of
  every stalk is at most the dimension of the ambient scheme.
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] specializationOrder

/-- The Krull dimension of the local ring at a point is at most the topological Krull
dimension of the ambient scheme. -/
theorem ringKrullDim_stalk_le_topologicalKrullDim (X : Scheme.{u}) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ topologicalKrullDim X := by
  rw [ringKrullDim_stalk_eq_coheight]
  calc
    (↑(Order.coheight x) : WithBot ℕ∞) ≤ Order.krullDim X :=
      Order.coheight_le_krullDim x
    _ = topologicalKrullDim X :=
      (Order.krullDim_eq_of_orderIso
        (irreducibleSetEquivPoints (α := X))).symm

end AlgebraicGeometry.Scheme

