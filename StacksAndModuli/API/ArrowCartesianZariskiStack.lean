module

public import StacksAndModuli.API.ArrowCartesianZariski
public import StacksAndModuli.«Section3.5-Stacks».«part3.5.1-the-definition»

/-!
# The Zariski stack of cartesian scheme arrows

This module packages the raw gluing constructions from
`ArrowCartesianZariski` using the stack vocabulary introduced in §3.5.  It is
kept separate so the geometric gluing API remains usable by earlier sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme.ArrowCartesianZariski

/-- The cartesian-arrow fibration of schemes satisfies effective Zariski descent. -/
theorem isStack :
    (CategoryTheory.arrowCartesian Scheme.{u}).p.IsStack
      Scheme.zariskiTopology := by
  constructor
  · intro S R hR A B hA hB phi hphi hcompat
    exact MorphismGluing.existsUniqueGluingHom
      (hR := hR) (A := A) (B := B) (hA := hA) (hB := hB)
      (phi := fun {_} {_} hg {_} xi hxi ↦ phi hg xi hxi)
      (hphi := fun {_} {_} hg {_} xi hxi ↦ hphi hg xi hxi)
      (hcompat := fun {_} {_} {_} hg {_} {_} {_} chi xi hxi hchi ↦
        hcompat hg chi xi hxi hchi)
  · intro S R hR D hD hDlift
    exact existsGluingObject (hR := hR) (D := D) hD
      (fun {_} {_} k ↦ hDlift k)

end AlgebraicGeometry.Scheme.ArrowCartesianZariski
