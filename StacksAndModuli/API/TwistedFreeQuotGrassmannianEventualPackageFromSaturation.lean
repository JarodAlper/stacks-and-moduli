module

public import StacksAndModuli.API.TwistedFreeQuotEventualCanonicalInputsAndKernelGeneration
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianEventualPackageFromNextDegree
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNextDegreeSaturation

/-!
# Eventual Quot immersion packages from next-degree saturation

This file connects the saturation criterion for the finite algebraic next-degree
cokernel to the eventual Quot-to-Grassmannian immersion package.  At every sufficiently
large degree, saturation identifies that cokernel with the reconstructed geometric
pushforward.  Separate regularity and Gotzmann-persistence callbacks then give the exact
rank equivalence consumed by the projective flattening-locus construction.

The final theorem has the parameter shape of the positive-dimensional projectivity root.
It keeps arbitrary-base noetherian Čech models and kernel generation as independent
hypotheses, so spreading and kernel-bound results can discharge them separately.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Eventual next-degree saturation, regularity, and persistence data supply the
eventual normalized algebraic rank equivalences used by projective flattening. -/
theorem
    exists_eventual_twistedFreeQuotUniversalNextDegreeFlatteningData_of_saturation
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hsaturation : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotUniversalNextDegreeSaturationData
          S n r (P.hilbertNatValue d) (r * (n + e).choose n)
            l P d e he
            (twistedFreeMonomialIndexEquiv r ((n + e).choose n)))) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotUniversalNextDegreeFlatteningData
          S n r (P.hilbertNatValue d) (r * (n + e).choose n)
            l P d e he
            (twistedFreeMonomialIndexEquiv r ((n + e).choose n))) := by
  obtain ⟨D, hD⟩ := hsaturation
  refine ⟨D, ?_⟩
  intro d hd e he
  obtain ⟨H⟩ := hD d hd e he
  exact ⟨H.toFlatteningData⟩

/-- Eventual canonical Grassmannian inputs, arbitrary-test-scheme kernel generation,
and next-degree saturation data produce the intrinsic eventual immersion packages. -/
theorem
    hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_nextDegreeSaturation
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hinputs : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotGrassmannianCanonicalInputs
          n S l r P d e he (r * (n + e).choose n)
            (P.hilbertNatValue d)
            (twistedFreeMonomialIndexEquiv r ((n + e).choose n))))
    (hkernel : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (T : Over S)
        (a : Modules.QuotientPullbackData
          (Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (projectiveSpaceOverπ n S) T),
        a.HasFiberwiseHilbertPolynomial P →
          TwistedFreeQuotKernelIsGloballyGenerated n T.left l r
            (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
              T a) d)
    (hsaturation : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotUniversalNextDegreeSaturationData
          S n r (P.hilbertNatValue d) (r * (n + e).choose n)
            l P d e he
            (twistedFreeMonomialIndexEquiv r ((n + e).choose n)))) :
    HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P := by
  apply
    hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_nextDegreeRank
      n S l r P hinputs hkernel
  exact
    exists_eventual_twistedFreeQuotUniversalNextDegreeFlatteningData_of_saturation
      n S l r P hsaturation

/-- Root-shaped positive-dimensional reduction to factored arbitrary-base models,
kernel generation, and eventual next-degree saturation geometry.

The chosen nonempty Quot family is used only to construct the canonical fixed-degree
Grassmannian inputs.  The two uniform arbitrary-base hypotheses remain separate from the
saturation/regularity/persistence callback, so each can be supplied by its own spreading
or Gotzmann theorem. -/
theorem
    hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_quotPoint_and_saturation
    (n : ℕ) (hn : 0 < n) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (T : Over S) (hT : Nonempty T.left)
    (z : (quotFunctorP (projectiveSpaceOverTwistedFree n S l r) P).obj (op T))
    (hmodel : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      HasUniversallyAffineNoetherianTwistedFreeQuotCechModel n r l P S d)
    (hkernel : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (A : Over S)
        (a : Modules.QuotientPullbackData
          (Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (projectiveSpaceOverπ n S) A),
        a.HasFiberwiseHilbertPolynomial P →
          TwistedFreeQuotKernelIsGloballyGenerated n A.left l r
            (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
              A a) d)
    (hsaturation : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotUniversalNextDegreeSaturationData
          S n r (P.hilbertNatValue d) (r * (n + e).choose n)
            l P d e he
            (twistedFreeMonomialIndexEquiv r ((n + e).choose n)))) :
    HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P := by
  let hinputs :=
    exists_eventual_twistedFreeQuotGrassmannianCanonicalInputs_of_quotPoint_of_noetherianCechModel
      n S l r P hn hmodel T hT z
  exact
    hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_nextDegreeSaturation
      n S l r P hinputs hkernel hsaturation

end AlgebraicGeometry.Scheme

end

end
