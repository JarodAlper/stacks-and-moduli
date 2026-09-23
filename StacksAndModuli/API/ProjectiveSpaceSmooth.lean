module

public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.4-projective-space-comparison»

/-!
# Smoothness of relative projective space

Absolute projective space represents the rank-one Grassmannian, whose representing
scheme is smooth over the integers.  Since relative projective space is its base change,
its projection to the base is smooth.

## Main results

* `AlgebraicGeometry.Scheme.projectiveSpaceOver_over`: relative projective space
  carries its canonical structure over the base.
* `AlgebraicGeometry.Scheme.projectiveSpace_smooth`: absolute projective space is
  smooth over `Spec ℤ`.
* `AlgebraicGeometry.Scheme.projectiveSpaceOverπ_smooth`: relative projective space
  is smooth over its base.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Relative projective space carries its canonical structure over the base. -/
noncomputable instance projectiveSpaceOver_over (n : ℕ) (S : Scheme.{u}) :
    (projectiveSpaceOver n S).Over S :=
  ⟨projectiveSpaceOverπ n S⟩

/-- Projective space is smooth over the integers, by its identification with the
rank-one Grassmannian. -/
instance projectiveSpace_smooth (n : ℕ) :
    Smooth (specULiftZIsTerminal.from (projectiveSpace n : Scheme.{u})) :=
  smooth_of_grassmannianFunctor_representableBy
    (ProjectiveSpectrum.Proj.projectiveSpaceGrassmannianRepresentation n)

/-- Relative projective space is smooth over its base. -/
instance projectiveSpaceOverπ_smooth (n : ℕ) (S : Scheme.{u}) :
    Smooth (projectiveSpaceOverπ n S) := by
  change Smooth (pullback.fst (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (projectiveSpace n)))
  infer_instance

end AlgebraicGeometry.Scheme

end
