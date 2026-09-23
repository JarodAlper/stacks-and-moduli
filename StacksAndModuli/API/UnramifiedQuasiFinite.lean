module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Unramified morphisms are locally quasi-finite

Mathlib's `LocallyQuasiFinite` omits the finite-type condition, and consequently does
not register the usual implication from an unramified morphism as a typeclass instance.
This file supplies the explicit implication used by the stack-level representability
API.

## Main result

* `LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType`
* `formallyUnramified_locallyOfFiniteType_over_field`
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- A formally unramified morphism locally of finite type is locally quasi-finite. -/
theorem LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [FormallyUnramified f] [LocallyOfFiniteType f] :
    LocallyQuasiFinite f := by
  constructor
  intro U hU V hV e
  let _ : (f.appLE U V e).hom.FiniteType := f.finiteType_appLE hU hV e
  let _ : (f.appLE U V e).hom.FormallyUnramified :=
    f.formallyUnramified_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite _ _)

/-- A formally unramified morphism locally of finite type to the spectrum of a field is
separated and étale.

Local finite type over a field upgrades to local finite presentation, while flatness is
automatic.  For separatedness, local quasi-finiteness makes the source discrete because
the target has one point.  The self-pullback is discrete for the same reason, so the open
immersion given by the diagonal is also a closed immersion. -/
theorem formallyUnramified_locallyOfFiniteType_over_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [FormallyUnramified f]
    [LocallyOfFiniteType f] : IsSeparated f ∧ Etale f := by
  let _ : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType f
  let _ : Flat f := by infer_instance
  let _ : LocallyOfFinitePresentation f := by infer_instance
  let _ : Etale f := Etale.of_formallyUnramified_of_flat f
  have hXdiscrete : DiscreteTopology X := by
    apply isDiscrete_univ_iff.mp
    let y : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
    have h := f.isDiscrete_preimage_singleton y
    have hpre : f ⁻¹' ({y} : Set (Spec (CommRingCat.of K))) = Set.univ := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [hpre] at h
    exact h
  let _ : DiscreteTopology X := hXdiscrete
  have hPdiscrete : DiscreteTopology (pullback f f : Scheme.{u}) := by
    apply isDiscrete_univ_iff.mp
    have h := (pullback.fst f f).isDiscrete_preimage
      (isDiscrete_univ_iff.mpr inferInstance : _root_.IsDiscrete (Set.univ : Set X))
    simpa only [Set.preimage_univ] using h
  let _ : DiscreteTopology (pullback f f : Scheme.{u}) := hPdiscrete
  constructor
  · constructor
    exact IsClosedImmersion.of_isPreimmersion _ (isClosed_discrete _)
  · infer_instance

end AlgebraicGeometry
