module

public import StacksAndModuli.API.ProjectiveSpaceTwistCohomology
public import StacksAndModuli.API.ProjectiveSpaceTwistMultiplication

/-!
# The scheme-level Serre-vanishing boundary on projective space

This file records the precise scheme-theoretic form of Serre vanishing needed by
the Chapter 2 Hilbert and Quot projectivity arguments.  It uses Mathlib's actual
derived sheaf cohomology `Sheaf.H`, rather than the separate graded-module model.

For every finitely presented quasicoherent module sheaf `M` on relative projective
space, `Scheme.ProjectiveSpaceHasSerreVanishing n S` asserts that `Hⁱ(M(d))`
vanishes for every fixed positive `i` and all sufficiently large natural `d`.
The definition is deliberately a proposition, not an axiom or an instance: APIs
which consume Serre vanishing can expose the one genuinely geometric missing input
without duplicating three separate eventual-vanishing hypotheses.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Scheme-level Serre vanishing on relative projective space: every positive
cohomology group of a finitely presented quasicoherent module sheaf vanishes after
a sufficiently positive twist. -/
def ProjectiveSpaceHasSerreVanishing (n : ℕ) (S : Scheme.{u}) : Prop :=
  ∀ (M : (projectiveSpaceOver n S).Modules),
    M.IsQuasicoherent → M.IsFinitePresentation →
      ∀ (i : ℕ), 1 ≤ i →
        ∀ᶠ d : ℕ in Filter.atTop, Subsingleton
          (((SheafOfModules.toSheaf _).obj
            (projectiveSpaceOverTwistModule M (d : ℤ))).H i)

namespace ProjectiveSpaceHasSerreVanishing

/-- Extract the eventual vanishing for one finitely presented quasicoherent sheaf
and one positive cohomological degree. -/
theorem eventually_subsingleton_H
    {n : ℕ} {S : Scheme.{u}} (h : ProjectiveSpaceHasSerreVanishing n S)
    (M : (projectiveSpaceOver n S).Modules)
    (hqc : M.IsQuasicoherent) (hfp : M.IsFinitePresentation)
    (i : ℕ) (hi : 1 ≤ i) :
    ∀ᶠ d : ℕ in Filter.atTop, Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (projectiveSpaceOverTwistModule M (d : ℤ))).H i) :=
  h M hqc hfp i hi

/-- Serre vanishing applied to `O(-l)`, transported through multiplication of
twists, gives eventual vanishing of `Hⁱ(O(d-l))`. -/
theorem eventually_subsingleton_H_projectiveSpaceOverTwist_sub
    {n : ℕ} {S : Scheme.{u}} (h : ProjectiveSpaceHasSerreVanishing n S)
    (l : ℤ) (i : ℕ) (hi : 1 ≤ i) :
    ∀ᶠ d : ℕ in Filter.atTop, Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (projectiveSpaceOverTwist n S ((d : ℤ) - l))).H i) := by
  have hO := h.eventually_subsingleton_H
    (projectiveSpaceOverTwist n S (-l))
    (by infer_instance) (by infer_instance) i hi
  filter_upwards [hO] with d hd
  let e : projectiveSpaceOverTwistModule
        (projectiveSpaceOverTwist n S (-l)) (d : ℤ) ≅
      projectiveSpaceOverTwist n S ((d : ℤ) - l) :=
    projectiveSpaceOverTwist_addIso_nat n S (-l) d ≪≫
      eqToIso (by rw [neg_add_eq_sub])
  exact Modules.subsingleton_H_of_iso e i hd

end ProjectiveSpaceHasSerreVanishing

end AlgebraicGeometry.Scheme

end
