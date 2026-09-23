module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalFlatteningFiniteness
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianEventualImmersionPackage

/-!
# Eventual Quot-to-Grassmannian packages from one-step geometry

This file connects the one-step universal-flattening input to the intrinsic
eventual Quot-to-Grassmannian immersion package.  Finiteness of the universal
reconstruction and of its adjacent pushforwards is automatic over a locally
Noetherian base; the remaining geometric input is the four-field structure
`TwistedFreeQuotUniversalOneStepFlatteningGeometry`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Eventual canonical fixed-degree data, kernel generation, and the four
one-step universal geometric assertions produce intrinsic immersion packages
in every sufficiently large degree. -/
theorem
    hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_universalOneStepGeometry
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S] (hn : 0 < n)
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
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
    (hgeometry : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotUniversalOneStepFlatteningGeometry
          n S l r P d e he)) :
    HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P := by
  apply hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_universalGeometry
    n S l r P hinputs hkernel
      (exists_eventual_twistedFreeQuotUniversalFlatteningLocusWitness
        n S hn l r P hinputs hgeometry)

/-- Eventual canonical inputs, kernel generation, and reduced one-step
universal geometry produce intrinsic immersion packages.  The adjacent-rank
field is reconstructed from the canonical inputs in degrees `d` and `d+1`. -/
theorem
    hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_universalReducedOneStepGeometry
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S] (hn : 0 < n)
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
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
    (hgeometry : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotUniversalReducedOneStepFlatteningGeometry
          n S l r P d e he)) :
    HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P := by
  apply hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_universalGeometry
    n S l r P hinputs hkernel
  exact
    exists_eventual_twistedFreeQuotUniversalFlatteningLocusWitness_of_reducedGeometry
      n S hn l r P hinputs hgeometry

end AlgebraicGeometry.Scheme

end

end
