module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Stalk support of a scheme module

The stalk support of a sheaf of modules is the set of points where its underlying
additive-group stalk is nonzero.  This file also gives the local restriction criterion
used to exclude a point from that support.

## Main results

* `AlgebraicGeometry.Scheme.Modules.stalkSupport`: the set of points with nonzero stalk.
* `AlgebraicGeometry.Scheme.Modules.not_mem_stalkSupport_of_isZero_restrict`: a zero
  restriction on an open excludes every point of that open from the stalk support.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The stalk support of a scheme module: the points at which its underlying additive
group stalk is not a zero object. -/
def stalkSupport {X : Scheme.{u}} (M : X.Modules) : Set X :=
  {x | ¬ IsZero ((toPresheaf X ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj M)}

/-- If a scheme module restricts to zero on an open, then its stalk is zero at every
point of that open. -/
theorem isZero_stalk_of_isZero_restrict
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (hzero : IsZero ((restrictFunctor U.ι).obj M)) (x : U) :
    IsZero ((toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.1).obj M) := by
  have hlocal : IsZero
      ((toPresheaf U.toScheme ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
          ((restrictFunctor U.ι).obj M)) :=
    Functor.map_isZero
      (toPresheaf U.toScheme ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) hzero
  exact hlocal.of_iso ((restrictStalkNatIso U.ι x).app M).symm

/-- A zero restriction on an open excludes every point of that open from the stalk
support. -/
theorem not_mem_stalkSupport_of_isZero_restrict
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (hzero : IsZero ((restrictFunctor U.ι).obj M))
    {x : X} (hx : x ∈ U) : x ∉ stalkSupport M := by
  exact fun hxSupport ↦ hxSupport
    (isZero_stalk_of_isZero_restrict M U hzero ⟨x, hx⟩)

end AlgebraicGeometry.Scheme.Modules

end
