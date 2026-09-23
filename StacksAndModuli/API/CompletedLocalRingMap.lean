module

public import StacksAndModuli.API.SurjectiveAdicCompletion

/-!
# Functoriality of completed local rings for closed immersions

A scheme morphism whose map on a given stalk is surjective induces a map in the
same direction on completed local rings.  This file constructs that map, promotes
it to an algebra homomorphism over an affine base, and records its surjectivity and
kernel.

The construction applies in particular to closed immersions.  It is phrased using
surjectivity on the selected stalk so that it is also reusable for any morphism
with that local property.

## Main results

* `AlgebraicGeometry.Scheme.Hom.completedLocalRingMap`: the induced ring map on
  completed local rings.
* `AlgebraicGeometry.Scheme.Hom.completedLocalRingMapAlgHom`: its algebra-map
  form over a common affine base.
* `AlgebraicGeometry.Scheme.Hom.ker_completedLocalRingMap_eq`: over a
  Noetherian target stalk, its kernel is the extension of the stalk-map kernel.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme morphism surjective on a selected stalk induces a map on the
corresponding completed local rings. -/
noncomputable def Hom.completedLocalRingMap
    {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    (hg : Function.Surjective (g.stalkMap x)) :
    Y.completedLocalRing (g x) →+* X.completedLocalRing x := by
  letI : Algebra (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) :=
    (g.stalkMap x).hom.toAlgebra
  exact AdicCompletion.mapLocalRingHom hg

/-- The completed-local-ring map commutes with the canonical maps from the
ordinary local rings. -/
@[simp]
lemma Hom.completedLocalRingMap_toCompletedLocalRing
    {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    (hg : Function.Surjective (g.stalkMap x))
    (a : Y.presheaf.stalk (g x)) :
    g.completedLocalRingMap x hg (Y.toCompletedLocalRing (g x) a) =
      X.toCompletedLocalRing x (g.stalkMap x a) := by
  let _ : Algebra (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) :=
    (g.stalkMap x).hom.toAlgebra
  exact AdicCompletion.mapLocalRingHom_of hg a

/-- Over a common affine base, the map on completed local rings is an algebra
homomorphism. -/
noncomputable def Hom.completedLocalRingMapAlgHom
    {X Y : Scheme.{u}} {R : CommRingCat.{u}}
    (g : X ⟶ Y) (p : Y ⟶ Spec R) (x : X)
    (hg : Function.Surjective (g.stalkMap x)) :
    letI := completedLocalRingAlgebra p (g x)
    letI := completedLocalRingAlgebra (g ≫ p) x
    Y.completedLocalRing (g x) →ₐ[R] X.completedLocalRing x := by
  letI := completedLocalRingAlgebra p (g x)
  letI := completedLocalRingAlgebra (g ≫ p) x
  exact
    { g.completedLocalRingMap x hg with
      commutes' := fun r ↦ by
        rw [algebraMap_completedLocalRingAlgebra,
          algebraMap_completedLocalRingAlgebra]
        change g.completedLocalRingMap x hg
            (Y.toCompletedLocalRing (g x) (baseToStalk p (g x) r)) = _
        rw [g.completedLocalRingMap_toCompletedLocalRing]
        congr 1
        exact DFunLike.congr_fun
          (CommRingCat.hom_ext_iff.mp
            (baseToStalk_comp_stalkMap g p x)) r }

/-- The underlying function of the completed-local-ring algebra map is the
completed-local-ring map. -/
@[simp]
lemma Hom.completedLocalRingMapAlgHom_apply
    {X Y : Scheme.{u}} {R : CommRingCat.{u}}
    (g : X ⟶ Y) (p : Y ⟶ Spec R) (x : X)
    (hg : Function.Surjective (g.stalkMap x))
    (a : Y.completedLocalRing (g x)) :
    g.completedLocalRingMapAlgHom p x hg a =
      g.completedLocalRingMap x hg a :=
  rfl

/-- Surjectivity on a stalk implies surjectivity on the corresponding completed
local rings. -/
theorem Hom.completedLocalRingMap_surjective
    {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    (hg : Function.Surjective (g.stalkMap x)) :
    Function.Surjective (g.completedLocalRingMap x hg) := by
  let _ : Algebra (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) :=
    (g.stalkMap x).hom.toAlgebra
  exact AdicCompletion.mapLocalRingHom_surjective hg

/-- For a Noetherian target stalk, the kernel of the map on completed local
rings is the extension of the stalk-map kernel. -/
theorem Hom.ker_completedLocalRingMap_eq
    {X Y : Scheme.{u}} (g : X ⟶ Y) (x : X)
    [IsNoetherianRing (Y.presheaf.stalk (g x))]
    (hg : Function.Surjective (g.stalkMap x)) :
    RingHom.ker (g.completedLocalRingMap x hg) =
      (RingHom.ker (g.stalkMap x).hom).map
        (Y.toCompletedLocalRing (g x)) := by
  let _ : Algebra (Y.presheaf.stalk (g x)) (X.presheaf.stalk x) :=
    (g.stalkMap x).hom.toAlgebra
  exact AdicCompletion.ker_mapLocalRingHom_eq_idealMap hg

end AlgebraicGeometry.Scheme

end
