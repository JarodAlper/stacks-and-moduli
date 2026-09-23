module

public import StacksAndModuli.API.ProjectiveSpaceZeroCohomology
public import StacksAndModuli.API.ProjectiveTwistedFreeSerre

/-!
# The twisted-free Serre quotient theorem on projective zero-space

Over a field, relative projective zero-space is a one-point affine scheme.  Actual
derived sheaf cohomology therefore vanishes in positive degrees.  Combining that
fact with the Noetherian twisted-free quotient theorem gives an unconditional,
sorry-free end-to-end base case for the Chapter 2 Serre reduction.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- On `ℙ⁰` over a Noetherian ring with nonempty subsingleton prime spectrum, every
finite twisted-free quotient has finite global sections and vanishing first
cohomology after all sufficiently positive twists. -/
theorem eventually_finite_globalSections_and_H_one_of_twistedFree_epi_zero_of_primeSpectrum
    {J : Type u} [Finite J] (R : Type u) [CommRing R] [IsNoetherianRing R]
    [Nonempty (PrimeSpectrum R)] [Subsingleton (PrimeSpectrum R)] (l : ℤ)
    {Q : (Scheme.projectiveSpaceOver 0 (Spec (.of R))).Modules}
    (q : (∐ fun _ : J ↦
      Scheme.projectiveSpaceOverTwist 0 (Spec (.of R)) (-l)) ⟶ Q)
    [Epi q] [Q.IsQuasicoherent] :
    ∀ᶠ d : ℕ in Filter.atTop,
      (letI := globalSectionsModule
         (Scheme.projectiveSpaceOverπ 0 (Spec (.of R)))
         (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
       Module.Finite R
         Γ(Scheme.projectiveSpaceOverTwistModule Q (d : ℤ), ⊤)) ∧
        Subsingleton
          (((SheafOfModules.toSheaf _).obj
            (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).H 1) := by
  exact
    eventually_finite_globalSections_and_H_one_of_twistedFree_epi_of_serre_of_noetherian
      (J := J) 0 (.of R) l q
        (Scheme.projectiveSpaceHasSerreVanishing_zero_spec_of_primeSpectrum R)

/-- On `ℙ⁰` over a field, every finite twisted-free quotient has finite global
sections and vanishing first cohomology after all sufficiently positive twists. -/
theorem eventually_finite_globalSections_and_H_one_of_twistedFree_epi_zero_field
    {J : Type u} [Finite J] (K : Type u) [Field K] (l : ℤ)
    {Q : (Scheme.projectiveSpaceOver 0 (Spec (.of K))).Modules}
    (q : (∐ fun _ : J ↦
      Scheme.projectiveSpaceOverTwist 0 (Spec (.of K)) (-l)) ⟶ Q)
    [Epi q] [Q.IsQuasicoherent] :
    ∀ᶠ d : ℕ in Filter.atTop,
      (letI := globalSectionsModule
         (Scheme.projectiveSpaceOverπ 0 (Spec (.of K)))
         (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
       Module.Finite K
         Γ(Scheme.projectiveSpaceOverTwistModule Q (d : ℤ), ⊤)) ∧
        Subsingleton
          (((SheafOfModules.toSheaf _).obj
            (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).H 1) := by
  exact
    eventually_finite_globalSections_and_H_one_of_twistedFree_epi_zero_of_primeSpectrum
      (J := J) K l q

end AlgebraicGeometry.Scheme.Modules

end
