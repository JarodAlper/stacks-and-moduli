module

public import StacksAndModuli.API.AffineKernelFiniteSections
public import StacksAndModuli.API.ProjectiveFiniteTwistedFreePresentation
public import StacksAndModuli.API.ProjectiveTwistModuleFaithful

/-!
# Finite homogeneous generators for kernels on projective space

An epimorphism between finitely presented quasicoherent modules has finitely generated
kernel sections on every standard affine chart, even over a non-noetherian base.  Applying
the chartwise-finite projective generation theorem produces finitely many homogeneous
sections of the kernel in one common degree.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "X" => Proj 𝒜
local notation "π" => Proj.polynomialToSpec (Fin (n + 1)) R
local notation "x" => _root_.AlgebraicGeometry.ProjectiveSpace.stdVars n R

set_option synthInstance.maxHeartbeats 1000000 in
-- The nested polynomial grading and open-section module structures make instance
-- synthesis for this declaration substantially more expensive than the default budget.
set_option maxHeartbeats 1000000 in
-- Constructing the degree-zero twist equivalence on every explicit polynomial chart and
-- elaborating the dependent family of homogeneous generators exceed the default budget.
/-- The kernel of an epimorphism between finitely presented quasicoherent modules on
polynomial projective space has finitely many homogeneous sections in one common degree,
beyond any prescribed bound, whose normalized restrictions generate on every standard
affine chart. -/
theorem exists_commonDegree_normalizedChart_generators_ge_kernel_of_epi
    {E Q : (Proj 𝒜).Modules} [E.IsQuasicoherent] [E.IsFinitePresentation]
    [Q.IsQuasicoherent] [Q.IsFinitePresentation] (p : E ⟶ Q) [Epi p] (B : ℕ) :
    ∃ (m : Fin (n + 1) → ℕ) (D : ℕ)
      (s : (Σ i, Fin (m i)) → (gammaStar 𝒜 π (kernel p) x).obj (D : ℤ)),
      B ≤ D ∧ ∀ i : Fin (n + 1),
        Submodule.span
          Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
          (Set.range (fun a ↦ normalizedChartSection (kernel p) i D (s a))) = ⊤ := by
  letI : (kernel p).IsQuasicoherent := Scheme.Modules.kernel_isQuasicoherent p
  have hfinite : ∀ i : Fin (n + 1),
      Module.Finite
        Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
        Γ(twistModule 𝒜 (kernel p) 0,
          basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)) := by
    intro i
    letI : Module.Finite
        Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
        Γ(kernel p, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)) :=
      Scheme.Modules.finite_sections_kernel_of_epi p
        (polynomialStandardAffineOpen (R := R) (n := n) i)
    let eU :
        Γ(twistModule 𝒜 (kernel p) 0,
          basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)) ≃ₗ[
            Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))]
        Γ(kernel p, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)) :=
      ((SheafOfModules.evaluation (R := (Proj 𝒜).ringCatSheaf)
        (op (basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)))).mapIso
          (twistModuleZeroIso (R := R) (n := n) (kernel p))).toLinearEquiv
    exact Module.Finite.equiv eU.symm
  exact exists_commonDegree_normalizedChart_generators_ge_of_finite_chart_sections
    (R := R) (n := n) (kernel p) B hfinite

end AlgebraicGeometry.Proj

end

end
