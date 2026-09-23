module

public import StacksAndModuli.API.ProjectiveSpaceTwistMultiplication
public import StacksAndModuli.API.SheafCohomologyFiniteCoproduct
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Cohomology of twisted-free sheaves on relative projective space

Twisting a finite coproduct of copies of `O(-l)` by a nonnegative degree `d`
identifies it with the corresponding finite coproduct of `O(d-l)`.  Consequently,
vanishing of the cohomology of the single twist `O(d-l)` gives vanishing for the
twisted-free ambient sheaf.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- If `Hⁱ(O(d-l))` vanishes, then `Hⁱ` of the twist by `O(d)` of a finite
coproduct of copies of `O(-l)` vanishes. -/
theorem subsingleton_H_projectiveSpaceOverNegativeTwist_coproduct_twist
    {J : Type u} [Finite J] (n : ℕ) (S : Scheme.{u})
    (l : ℤ) (d : ℕ) (i : ℕ)
    (h : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwist n S ((d : ℤ) - l))).H i)) :
    Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule
          (∐ fun _ : J ↦ Scheme.projectiveSpaceOverTwist n S (-l))
          (d : ℤ))).H i) := by
  apply subsingleton_H_of_iso
    (Scheme.projectiveSpaceOverNegativeTwist_coproduct_twistIso_nat
      (J := J) n S l d).symm i
  exact subsingleton_H_coproduct_of_finite
    (fun _ : J ↦ Scheme.projectiveSpaceOverTwist n S ((d : ℤ) - l)) i
    (fun _ ↦ h)

/-- The preceding cohomology-vanishing transfer, uniformly in every sufficiently
large natural twist. -/
theorem eventually_subsingleton_H_projectiveSpaceOverNegativeTwist_coproduct_twist
    {J : Type u} [Finite J] (n : ℕ) (S : Scheme.{u})
    (l : ℤ) (i : ℕ)
    (h : ∀ᶠ d : ℕ in Filter.atTop, Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwist n S ((d : ℤ) - l))).H i)) :
    ∀ᶠ d : ℕ in Filter.atTop, Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule
          (∐ fun _ : J ↦ Scheme.projectiveSpaceOverTwist n S (-l))
          (d : ℤ))).H i) := by
  filter_upwards [h] with d hd
  exact subsingleton_H_projectiveSpaceOverNegativeTwist_coproduct_twist
    (J := J) n S l d i hd

end AlgebraicGeometry.Scheme.Modules

end
