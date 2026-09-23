module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Smooth points under scheme isomorphisms

This file supplies the pointwise isomorphism-invariance API for the formally smooth stalk-map
description of the smooth locus.

## Main result

* `AlgebraicGeometry.Scheme.formallySmooth_stalkMap_isoOver_iff`: corresponding points of
  schemes isomorphic over a common base are simultaneously smooth.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- Smoothness at corresponding points is preserved and reflected by an isomorphism over a
common base. -/
theorem formallySmooth_stalkMap_isoOver_iff {S X Y : Scheme.{u}}
    [X.Over S] [Y.Over S] (e : X.asOver S ≅ Y.asOver S) (x : X) :
    ((X ↘ S).stalkMap x).hom.FormallySmooth ↔
      ((Y ↘ S).stalkMap (((Over.forget S).mapIso e).hom x)).hom.FormallySmooth := by
  let E : X ≅ Y := (Over.forget S).mapIso e
  have he : E.hom ≫ (Y ↘ S) = X ↘ S := e.hom.w
  rw [← he, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ _

end AlgebraicGeometry.Scheme
