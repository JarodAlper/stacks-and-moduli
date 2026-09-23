module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianCanonicalPackageFromGeometry
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianEventualVeryAmple

/-!
# Eventual canonical Grassmannian packages from uniform geometry

This file performs the quantifier bookkeeping at the end of the Quot-to-Grassmannian
construction.  Uniform bounds for the canonical fixed-degree inputs, generation of the
twisted kernel, and projective flattening are combined with the elementary twist-difference
bound.  Ambient reconstruction coherence then constructs a canonical package in every
sufficiently large degree.

The theorem here intentionally keeps the three mathematical inputs separate.  Their bounds
come from different arguments (cohomology and base change, relative Serre generation, and
flattening), whereas taking their maximum is formal.
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

/-- Uniform fixed-degree canonical inputs, kernel generation, and projective flattening
produce the eventual canonical packages used both by W6 and by determinant very ampleness.
All finite-index choices are canonical; only the sufficiently large twist is selected. -/
theorem hasEventualTwistedFreeQuotGrassmannianCanonicalPackages_of_geometry
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hinputs : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotGrassmannianCanonicalInputs
          n S l r P d e he (r * (n + e).choose n) (P.hilbertNatValue d)
            (twistedFreeMonomialIndexEquiv r ((n + e).choose n))))
    (hkernel : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (T : Over S)
        (a : Modules.QuotientPullbackData
          (Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (projectiveSpaceOverπ n S) T),
        a.HasFiberwiseHilbertPolynomial P →
          TwistedFreeQuotKernelIsGloballyGenerated n T.left l r
            (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
            d)
    (hflattening : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
        (T : Over S)
        (g : uliftYoneda.{u + 1}.obj T ⟶
          Modules.grassmannianFunctorOver S (P.hilbertNatValue d)
            (r * (n + e).choose n)),
        Modules.ProjectiveFlatteningHasFiniteRankPresentation n
          (grassmannianPointReconstructedQuotient
            (n := n) (r := r) (q := P.hilbertNatValue d) (l := l)
              (d := d) (e := e) (he := he)
              (σ := twistedFreeMonomialIndexEquiv r ((n + e).choose n)) T g)
          (P := P)) :
    HasEventualTwistedFreeQuotGrassmannianCanonicalPackages n S l r P := by
  obtain ⟨DI, hI⟩ := hinputs
  obtain ⟨DK, hK⟩ := hkernel
  obtain ⟨DF, hF⟩ := hflattening
  obtain ⟨DT, hT⟩ := exists_bound_twistedFree_twistDifference l
  refine ⟨max DI (max DK (max DF DT)), ?_⟩
  intro d hd
  have hdI : DI ≤ d := by omega
  have hdK : DK ≤ d := by omega
  have hdF : DF ≤ d := by omega
  have hdT : DT ≤ d := by omega
  obtain ⟨e, he⟩ := hT d hdT
  let m := r * (n + e).choose n
  let σ := twistedFreeMonomialIndexEquiv r ((n + e).choose n)
  obtain ⟨I⟩ := hI d hdI e he
  refine ⟨e, he, m, σ, ?_⟩
  exact ⟨TwistedFreeQuotGrassmannianCanonicalPackage.ofCanonicalGeometryOfGlobalGeneration
    I (fun X ↦ twistedFreeAmbientReconstructionCompatibility n X l r d e he)
      (hK d hdK) (hF d hdF e he)⟩

end AlgebraicGeometry.Scheme

end

end
