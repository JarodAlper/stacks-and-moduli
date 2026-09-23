module

public import StacksAndModuli.API.ProjectiveOneStepCanonicalBaseChange
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalFlatteningFiniteness

/-!
# Canonical one-step base change for the universal Quot reconstruction

For the universal reconstructed quotient on the relative Grassmannian, the
multiplication-compatible one-step base-change package has no coherence content beyond
Cohomology and Base Change in the two adjacent degrees.  The canonical maps are the
pullback--pushforward mates from `ProjectiveOneStepCanonicalBaseChange`; once they are
invertible in degrees `d` and `d + 1`, their multiplication square is automatic.

The eventual theorem records this reduction in the same dependent shape as the universal
one-step geometry package.  Thus a direct argument from the Grassmannian relation only
has to prove invertibility of the two canonical pushforward maps.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Adjacent canonical pushforward base-change isomorphisms give the one-step
multiplication base-change comparison for the universal reconstructed Quot family. -/
noncomputable def
    twistedFreeQuotUniversalMultiplicationBaseChangeComparison_of_canonical
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hdegree : Modules.ProjectiveTwistedPushforwardCanonicalBaseChange n
      (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) d)
    (hdegreeSucc : Modules.ProjectiveTwistedPushforwardCanonicalBaseChange n
      (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) (d + 1)) :
    Modules.ProjectiveOneStepMultiplicationBaseChangeComparison n
      (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) d :=
  Modules.ProjectiveOneStepMultiplicationBaseChangeComparison.ofCanonical
    n (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) d
    hdegree hdegreeSucc

/-- Eventual adjacent canonical Cohomology-and-Base-Change for the universal
reconstruction supplies eventual multiplication-compatible one-step base change. -/
theorem
    exists_eventual_twistedFreeQuotUniversalMultiplicationBaseChangeComparison_of_canonical
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hcanonical : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Modules.ProjectiveTwistedPushforwardCanonicalBaseChange n
            (twistedFreeQuotUniversalReconstructedQuotient
              n S l r P d e he) d ∧
          Modules.ProjectiveTwistedPushforwardCanonicalBaseChange n
            (twistedFreeQuotUniversalReconstructedQuotient
              n S l r P d e he) (d + 1)) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (Modules.ProjectiveOneStepMultiplicationBaseChangeComparison n
          (twistedFreeQuotUniversalReconstructedQuotient
            n S l r P d e he) d) := by
  obtain ⟨D, hD⟩ := hcanonical
  refine ⟨D, ?_⟩
  intro d hd e he
  obtain ⟨hdegree, hdegreeSucc⟩ := hD d hd e he
  exact ⟨twistedFreeQuotUniversalMultiplicationBaseChangeComparison_of_canonical
    n S l r P d e he hdegree hdegreeSucc⟩

end AlgebraicGeometry.Scheme

end

end
