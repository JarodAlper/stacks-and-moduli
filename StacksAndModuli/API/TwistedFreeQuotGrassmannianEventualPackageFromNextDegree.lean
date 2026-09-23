module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianEventualImmersionPackage
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNextDegreeFlattening

/-!
# Eventual Quot immersion packages from algebraic next-degree ranks

This file connects the corrected algebraic Grassmannian coordinates to the eventual
Quot-to-Grassmannian immersion package.  In each sufficiently large degree, the universal
degree-`d+1` cokernel commutes with arbitrary base change.  A Gotzmann-range equivalence
between its prescribed rank and projective flattening therefore supplies the universal
represented immersed locus, without any global pushforward base-change assertion.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Eventual Gotzmann-range rank equivalences for the universal algebraic next-degree
modules supply the universal projective flattening witnesses. -/
theorem
    exists_eventual_twistedFreeQuotUniversalFlatteningLocusWitness_of_nextDegreeRank
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hnext : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotUniversalNextDegreeFlatteningData
          S n r (P.hilbertNatValue d) (r * (n + e).choose n)
            l P d e he
            (twistedFreeMonomialIndexEquiv r ((n + e).choose n)))) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (Modules.ProjectiveFlatteningLocusWitness n
          (grassmannianPointReconstructedQuotient
            (n := n) (r := r) (q := P.hilbertNatValue d) (l := l)
              (d := d) (e := e) (he := he)
              (σ := twistedFreeMonomialIndexEquiv r ((n + e).choose n))
              (grassmannianOverRepresentation S (P.hilbertNatValue d)
                (r * (n + e).choose n))
              (freeGrassmannianUniversalPoint S (P.hilbertNatValue d)
                (r * (n + e).choose n))) P) := by
  obtain ⟨D, hD⟩ := hnext
  refine ⟨D, ?_⟩
  intro d hd e he
  obtain ⟨H⟩ := hD d hd e he
  exact ⟨H.toLocusWitness⟩

/-- Eventual canonical inputs, kernel generation, and the algebraic next-degree
Gotzmann equivalence produce intrinsic Quot-to-Grassmannian immersion packages. -/
theorem
    hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_nextDegreeRank
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
    (hnext : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotUniversalNextDegreeFlatteningData
          S n r (P.hilbertNatValue d) (r * (n + e).choose n)
            l P d e he
            (twistedFreeMonomialIndexEquiv r ((n + e).choose n)))) :
    HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P := by
  apply hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_universalGeometry
    n S l r P hinputs hkernel
  exact
    exists_eventual_twistedFreeQuotUniversalFlatteningLocusWitness_of_nextDegreeRank
      n S l r P hnext

end AlgebraicGeometry.Scheme

end

end
