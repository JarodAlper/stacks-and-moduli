module

public import StacksAndModuli.API.ProjectiveTwistMultiplication
public import StacksAndModuli.API.SchemeModulesPullbackPolynomialTwist
public import StacksAndModuli.API.SchemeModulesTensorCoproduct
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»

/-!
# Multiplication of twists on relative projective space

This file transports multiplication of twists from polynomial `Proj` to relative
projective space.  The pullback--tensor comparison is presently available when the
right-hand twist has a natural degree, which is the range needed for Serre twisting.
The result is also packaged after an arbitrary small coproduct in the left factor.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.MonoidalCategory
open ProjectiveSpectrum

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Scheme

/-- On relative projective space, tensoring `O(a)` by the natural-degree twist
`O(b)` gives `O(a + b)`. -/
noncomputable def projectiveSpaceOverTwist_addIso_nat
    (n : ℕ) (S : Scheme.{u}) (a : ℤ) (b : ℕ) :
    Modules.tensor
        (projectiveSpaceOverTwist n S a)
        (projectiveSpaceOverTwist n S (b : ℤ)) ≅
      projectiveSpaceOverTwist n S (a + (b : ℤ)) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ)
  let h := Limits.pullback.snd
    (specULiftZIsTerminal.from S)
    (specULiftZIsTerminal.from (projectiveSpace n))
  let Oa := ProjectiveSpectrum.Twist.twist 𝒜 a
  let Ob := ProjectiveSpectrum.Twist.twist 𝒜 (b : ℤ)
  let hc : IsIso (Modules.pullbackTensorComparison h Oa Ob) :=
    MvPolynomial.pullbackTensorComparison_polynomialTwist_nat_isIso
      n (ULift.{u} ℤ) h Oa b
  let e := @asIso _ _ _ _ (Modules.pullbackTensorComparison h Oa Ob) hc
  exact e.symm ≪≫
    (Modules.pullback h).mapIso
      (ProjectiveSpectrum.Twist.polynomialMultiplyIso
        (R := ULift.{u} ℤ) (Fin (n + 1)) a (b : ℤ))

/-- Tensoring a small coproduct of twists on relative projective space by a
natural-degree twist distributes over the coproduct and adds the degrees. -/
noncomputable def projectiveSpaceOverTwist_coproduct_addIso_nat
    {J : Type u} (n : ℕ) (S : Scheme.{u}) (a : J → ℤ) (b : ℕ) :
    Modules.tensor
        (∐ fun j : J => projectiveSpaceOverTwist n S (a j))
        (projectiveSpaceOverTwist n S (b : ℤ)) ≅
      ∐ fun j : J => projectiveSpaceOverTwist n S (a j + (b : ℤ)) :=
  Modules.tensorCoproductIso
      (fun j : J => projectiveSpaceOverTwist n S (a j))
      (projectiveSpaceOverTwist n S (b : ℤ)) ≪≫
    Sigma.mapIso (fun j => projectiveSpaceOverTwist_addIso_nat n S (a j) b)

/-- Twisting a small coproduct of copies of `O(-l)` by `O(d)`, for a natural
degree `d`, gives the corresponding coproduct of copies of `O(d-l)`. -/
noncomputable def projectiveSpaceOverNegativeTwist_coproduct_twistIso_nat
    {J : Type u} (n : ℕ) (S : Scheme.{u}) (l : ℤ) (d : ℕ) :
    Modules.tensor
        (∐ fun _ : J => projectiveSpaceOverTwist n S (-l))
        (projectiveSpaceOverTwist n S (d : ℤ)) ≅
      ∐ fun _ : J => projectiveSpaceOverTwist n S ((d : ℤ) - l) :=
  projectiveSpaceOverTwist_coproduct_addIso_nat
      n S (fun _ : J => -l) d ≪≫
    eqToIso (by rw [neg_add_eq_sub])

end AlgebraicGeometry.Scheme
