module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.Algebra.Category.Ring.Instances

/-!
# Lifting along a formally smooth morphism against a nilpotent-kernel surjection

The infinitesimal lifting property of a formally smooth ring map, packaged for
`CommRingCat` arrows: given a commuting square with a formally smooth `α : R ⟶ S` on the
left and a surjection `p : B ⟶ B₀` with nilpotent kernel on the right, the diagonal filler
exists.

Mathlib has `Algebra.FormallySmooth.exists_lift` for `AlgHom`s; this is the same statement
transported to arrows of `CommRingCat`, which is the form the scheme-level lifting criteria
need.

## Main results

* `CommRingCat.exists_lift_of_formallySmooth_of_isNilpotent_ker`: the diagonal filler.
-/

@[expose] public section

open CategoryTheory

universe u

/-- **The diagonal filler.** Given a commuting square of `CommRingCat` arrows with a
formally smooth map on the left and a surjection with nilpotent kernel on the right, there
is a map making both triangles commute. This is `Algebra.FormallySmooth.exists_lift`
transported to arrows of `CommRingCat`. -/
theorem CommRingCat.exists_lift_of_formallySmooth_of_isNilpotent_ker {R S B B₀ : CommRingCat.{u}} (α : R ⟶ S) (hα : α.hom.FormallySmooth)
    (p : B ⟶ B₀) (hp : Function.Surjective p.hom) (hnil : IsNilpotent (RingHom.ker p.hom))
    (u : R ⟶ B) (v : S ⟶ B₀) (hsq : α ≫ v = u ≫ p) :
    ∃ w : S ⟶ B, w ≫ p = v ∧ α ≫ w = u := by
  letI : Algebra R S := α.hom.toAlgebra
  letI : Algebra R B := u.hom.toAlgebra
  haveI : Algebra.FormallySmooth R S := hα
  have hcomm : ∀ r : R, v.hom (algebraMap R S r) = p.hom (algebraMap R B r) :=
    fun r => congrArg (fun t : R ⟶ B₀ => t.hom r) hsq
  let e := RingHom.quotientKerEquivOfSurjective hp
  let g : S →ₐ[R] B ⧸ RingHom.ker p.hom :=
    { __ := (e.symm.toRingHom.comp v.hom)
      commutes' := by
        intro r
        change e.symm (v.hom (algebraMap R S r)) = _
        rw [hcomm r]
        exact RingHom.quotientKerEquivOfSurjective_symm_apply hp _ }
  obtain ⟨w', hw'⟩ := Algebra.FormallySmooth.exists_lift (R := R) (A := S) _ hnil g
  refine ⟨CommRingCat.ofHom w'.toRingHom, ?_, ?_⟩
  · ext s
    have : Ideal.Quotient.mk (RingHom.ker p.hom) (w' s) = e.symm (v.hom s) :=
      congrArg (fun t : S →ₐ[R] B ⧸ RingHom.ker p.hom => t s) hw'
    have := congrArg e this
    simpa [RingHom.quotientKerEquivOfSurjective_apply_mk, e] using this
  · ext r
    exact w'.commutes r
