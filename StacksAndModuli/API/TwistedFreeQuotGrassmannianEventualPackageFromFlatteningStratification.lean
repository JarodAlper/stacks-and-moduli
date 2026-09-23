module

public import StacksAndModuli.API.TwistedFreeQuotEventualCanonicalInputsAndKernelGeneration
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianEventualImmersionPackage
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalFlatteningFiniteness

/-!
# Eventual Quot immersion packages from projective flattening stratification

The flattening locus needed in the Quot-to-Grassmannian construction is the direct
projective flattening stratum of the universal reconstructed quotient.  Its existence is
the projective-space case of flattening stratification: over a locally Noetherian base, a
finitely presented projective-space sheaf has a represented immersed locus on which it is
flat with a prescribed fibrewise Hilbert polynomial.

This file packages that theorem as an explicit callback and connects it to the existing
eventual immersion API.  The universal reconstructed quotient is already finitely
presented.  The only numerical input needed to apply the callback is the inequality between
the Hilbert rank and the ambient free rank; it is supplied by the canonical fixed-degree
Grassmannian inputs.

In particular, no base-change assertion for the pushforward of the universal reconstructed
quotient is assumed here.  Such an assertion need not hold away from the flattening locus.

Main declarations:

* `exists_eventual_twistedFreeQuotUniversalFlatteningLocusWitness_of_projectiveFlattening`;
* `hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_projectiveFlatteningStratification`;
* `hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_quotPoint_and_flattening`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A direct projective flattening-stratification theorem, applied to the universal
reconstructed quotient, supplies its eventual flattening witnesses.  Canonical inputs are
used only for the rank inequality which makes the free Grassmannian locally Noetherian. -/
theorem
    exists_eventual_twistedFreeQuotUniversalFlatteningLocusWitness_of_projectiveFlattening
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hinputs : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotGrassmannianCanonicalInputs
          n S l r P d e he (r * (n + e).choose n)
            (P.hilbertNatValue d)
            (twistedFreeMonomialIndexEquiv r ((n + e).choose n))))
    (hflattening : ∀ (B : Scheme.{u}) [IsLocallyNoetherian B]
      (Q : (projectiveSpaceOver n B).Modules) [Q.IsFinitePresentation],
        Nonempty (Modules.ProjectiveFlatteningLocusWitness n Q P)) :
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
  obtain ⟨D, hD⟩ := hinputs
  refine ⟨D, ?_⟩
  intro d hd e he
  obtain ⟨I⟩ := hD d hd e he
  let G := grassmannianOverRepresentation S
    (P.hilbertNatValue d) (r * (n + e).choose n)
  let Q := twistedFreeQuotUniversalReconstructedQuotient
    n S l r P d e he
  letI : IsLocallyNoetherian G.left :=
    grassmannianOverRepresentation_isLocallyNoetherian S
      (P.hilbertNatValue d) (r * (n + e).choose n) I.rank_le
  letI : Q.IsFinitePresentation := by
    dsimp only [Q, twistedFreeQuotUniversalReconstructedQuotient]
    exact freeGrassmannianUniversalReconstructedQuotient_isFinitePresentation
  exact hflattening G.left Q

/-- Eventual canonical Grassmannian inputs, kernel generation, and projective flattening
stratification give the eventual intrinsic Quot-to-Grassmannian immersion packages. -/
theorem
    hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_projectiveFlatteningStratification
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
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
    (hflattening : ∀ (B : Scheme.{u}) [IsLocallyNoetherian B]
      (Q : (projectiveSpaceOver n B).Modules) [Q.IsFinitePresentation],
        Nonempty (Modules.ProjectiveFlatteningLocusWitness n Q P)) :
    HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P := by
  apply hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_universalGeometry
    n S l r P hinputs hkernel
  exact
    exists_eventual_twistedFreeQuotUniversalFlatteningLocusWitness_of_projectiveFlattening
      n S l r P hinputs hflattening

/-- Root-shaped reduction for the positive-dimensional twisted-free Quot construction.
Universal noetherian Cech models and one nonempty Quot point give the canonical fixed-degree
inputs; kernel generation and direct projective flattening stratification then give all
eventual immersion packages. -/
theorem
    hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_quotPoint_and_flattening
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
    (hflattening : ∀ (B : Scheme.{u}) [IsLocallyNoetherian B]
      (Q : (projectiveSpaceOver n B).Modules) [Q.IsFinitePresentation],
        Nonempty (Modules.ProjectiveFlatteningLocusWitness n Q P)) :
    HasEventualTwistedFreeQuotGrassmannianImmersionPackages n S l r P := by
  let hinputs :=
    exists_eventual_twistedFreeQuotGrassmannianCanonicalInputs_of_quotPoint_of_noetherianCechModel
      n S l r P hn hmodel T hT z
  exact
    hasEventualTwistedFreeQuotGrassmannianImmersionPackages_of_projectiveFlatteningStratification
      n S l r P hinputs hkernel hflattening

end AlgebraicGeometry.Scheme

end

end
