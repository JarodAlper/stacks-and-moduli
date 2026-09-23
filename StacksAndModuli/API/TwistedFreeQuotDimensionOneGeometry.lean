module

public import StacksAndModuli.API.ProjectiveLineTwistedFreeQuotientFlatnessPersistence
public import StacksAndModuli.API.TwistedFreeQuotDimensionOneEventualImmersion

/-!
# Universal one-step geometry for twisted-free Quot on the projective line

The universal reconstructed quotient on `ℙ¹` is itself a quotient of the
twisted-free ambient sheaf.  Consequently the projective-line flatness
persistence theorem supplies the flatness field of
`TwistedFreeQuotUniversalDimensionOneGeometry` from its one-step pushforward
base-change comparison.

This is a conditional reduction, not an existence theorem for that comparison.
On the whole Grassmannian the comparison is false in general: specialization can
create a kernel in the universal relation and make geometric global sections jump.
The eventual Hilbert--Quot construction must instead impose the rank condition on
the algebraic graded cokernel, whose formation commutes with base change, before
identifying it with geometric global sections on the resulting flattening locus.
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

/-- On `ℙ¹`, the universal reconstructed twisted-free quotient has the
flatness-persistence property as soon as its two adjacent pushforwards and
multiplication have the one-step base-change comparison. -/
noncomputable def
    TwistedFreeQuotUniversalDimensionOneGeometry.ofMultiplicationBaseChange_one
    (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hd : l - 1 ≤ (d : ℤ))
    (C : Modules.ProjectiveOneStepMultiplicationBaseChangeComparison 1
      (twistedFreeQuotUniversalReconstructedQuotient
        1 S l r P d e he) d) :
    TwistedFreeQuotUniversalDimensionOneGeometry 1 S l r P d e he where
  multiplicationBaseChange := C
  flatnessPersistence :=
    Modules.ProjectiveOneStepFlatnessPersistenceEpi.of_twistedFreeQuotient_one
      (freeGrassmannianUniversalReconstructedQuotientMap S 1 r
        (P.hilbertNatValue d) (r * (1 + e).choose 1) l d e he
        (twistedFreeMonomialIndexEquiv r ((1 + e).choose 1))) hd C P

/-- Conditionally, an eventual family of multiplication base-change comparisons
supplies the complete eventual universal dimension-one geometry. -/
theorem exists_eventual_twistedFreeQuotUniversalDimensionOneGeometry_of_baseChange
    (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hbaseChange : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (Modules.ProjectiveOneStepMultiplicationBaseChangeComparison 1
          (twistedFreeQuotUniversalReconstructedQuotient
            1 S l r P d e he) d)) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotUniversalDimensionOneGeometry
          1 S l r P d e he) := by
  obtain ⟨D, hD⟩ := hbaseChange
  refine ⟨max D (l - 1).toNat, ?_⟩
  intro d hd e he
  have hDl : D ≤ d := le_trans (le_max_left _ _) hd
  have hld : l - 1 ≤ (d : ℤ) := by
    exact (Int.self_le_toNat (l - 1)).trans (by
      exact_mod_cast (le_trans (le_max_right D (l - 1).toNat) hd))
  obtain ⟨C⟩ := hD d hDl e he
  exact ⟨TwistedFreeQuotUniversalDimensionOneGeometry.ofMultiplicationBaseChange_one
    S l r P d e he hld C⟩

/-- Conditional reduction of the relative-projective-line immersion package to
arbitrary-base Čech models, kernel generation, and a universal one-step
multiplication base-change comparison.  The last premise does not hold on the
whole ambient Grassmannian in general. -/
theorem
    hasEventualTwistedFreeQuotGrassmannianImmersionPackages_one_of_baseChange
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (T : Over S) (hT : Nonempty T.left)
    (z : (quotFunctorP (projectiveSpaceOverTwistedFree 1 S l r) P).obj (op T))
    (hmodel : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ProjectiveSpace.HasUniversallyAffineNoetherianTwistedFreeQuotCechModel
        1 r l P S d)
    (hkernel : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (A : Over S)
        (a : Modules.QuotientPullbackData
          (Modules.QuotientPullbackData.twistedFreeAmbient
            (n := 1) (r := r) (l := l))
          (projectiveSpaceOverπ 1 S) A),
        a.HasFiberwiseHilbertPolynomial P →
          TwistedFreeQuotKernelIsGloballyGenerated 1 A.left l r
            (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
              A a) d)
    (hbaseChange : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (Modules.ProjectiveOneStepMultiplicationBaseChangeComparison 1
          (twistedFreeQuotUniversalReconstructedQuotient
            1 S l r P d e he) d)) :
    HasEventualTwistedFreeQuotGrassmannianImmersionPackages 1 S l r P := by
  obtain ⟨D, hD⟩ :=
    exists_eventual_twistedFreeQuotUniversalDimensionOneGeometry_of_baseChange
      S l r P hbaseChange
  exact hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_dimension_le_one
    1 (by omega) (by omega) S l r P T hT z hmodel hkernel ⟨D, hD⟩

end AlgebraicGeometry.Scheme

end

end
