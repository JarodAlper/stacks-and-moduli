module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»

/-!
# Finite twisted-free modules on relative projective space

This file defines the finite direct sums of a fixed twisting sheaf used as ambient
modules in projective Hilbert and Quot constructions, and records their standard
finiteness and quasicoherence properties.

Main declarations:
- `AlgebraicGeometry.Scheme.projectiveSpaceOverTwistedFree`;
- `AlgebraicGeometry.Scheme.projectiveSpaceOverTwistedFree_isFinitePresentation`;
- `AlgebraicGeometry.Scheme.projectiveSpaceOverTwistedFree_isQuasicoherent`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The direct sum of `r` copies of `𝒪(-l)` on relative projective space. -/
noncomputable def projectiveSpaceOverTwistedFree
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) :
    (projectiveSpaceOver n S).Modules :=
  ∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n S (-l)

/-- A finite twisted-free module on relative projective space is finitely presented. -/
instance projectiveSpaceOverTwistedFree_isFinitePresentation
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) :
    (projectiveSpaceOverTwistedFree n S l r).IsFinitePresentation := by
  unfold projectiveSpaceOverTwistedFree projectiveSpaceOverTwist
  exact ProjectiveSpectrum.Twist.pullbackPolynomialTwistedFree_isFinitePresentation
    (R := ULift.{u} ℤ) (Fin (n + 1))
      (pullback.snd
        (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (projectiveSpace n))) r (-l)

/-- A finite twisted-free module on relative projective space is quasicoherent. -/
instance projectiveSpaceOverTwistedFree_isQuasicoherent
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) :
    (projectiveSpaceOverTwistedFree n S l r).IsQuasicoherent := by
  unfold projectiveSpaceOverTwistedFree projectiveSpaceOverTwist
  exact ProjectiveSpectrum.Twist.pullbackPolynomialTwistedFree_isQuasicoherent
    (R := ULift.{u} ℤ) (Fin (n + 1))
      (pullback.snd
        (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (projectiveSpace n))) r (-l)

end AlgebraicGeometry.Scheme

end
