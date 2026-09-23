module

public import StacksAndModuli.API.ProjectiveTwistBaseChange
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»

/-!
# Finite twisted-free module sheaves on relative projective space

Finite coproducts of one relative twisting sheaf are finitely presented and
quasicoherent.  These scheme-facing wrappers expose the polynomial-`Proj`
presentation results without requiring a section file to define the corresponding
twisted-free abbreviation.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite coproduct of one relative projective-space twist is finitely
presented. -/
theorem projectiveSpaceOverTwistCoproduct_isFinitePresentation
    (J : Type u) [Finite J] (n : ℕ) (S : Scheme.{u}) (d : ℤ) :
    (∐ fun _ : J ↦
      Scheme.projectiveSpaceOverTwist n S d).IsFinitePresentation := by
  unfold Scheme.projectiveSpaceOverTwist
  exact ProjectiveSpectrum.Twist.pullbackPolynomialTwistCoproduct_isFinitePresentation
    (R := ULift.{u} ℤ) (Fin (n + 1))
      (pullback.snd
        (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (Scheme.projectiveSpace n))) J (fun _ ↦ d)

/-- A finite coproduct of one relative projective-space twist is
quasicoherent. -/
theorem projectiveSpaceOverTwistCoproduct_isQuasicoherent
    (J : Type u) [Finite J] (n : ℕ) (S : Scheme.{u}) (d : ℤ) :
    (∐ fun _ : J ↦
      Scheme.projectiveSpaceOverTwist n S d).IsQuasicoherent := by
  unfold Scheme.projectiveSpaceOverTwist
  exact ProjectiveSpectrum.Twist.pullbackPolynomialTwistCoproduct_isQuasicoherent
    (R := ULift.{u} ℤ) (Fin (n + 1))
      (pullback.snd
        (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (Scheme.projectiveSpace n))) J (fun _ ↦ d)

end AlgebraicGeometry.Scheme.Modules

end
