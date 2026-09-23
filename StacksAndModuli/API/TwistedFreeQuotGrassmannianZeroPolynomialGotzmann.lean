module

public import StacksAndModuli.API.TwistedFreeQuotGotzmannSeedBoundZeroPolynomial
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNoetherianRankReduction

/-!
# The universal zero-polynomial Gotzmann implication

For quotients on the projective line with zero prescribed Hilbert polynomial,
the algebraic next-degree rank condition forces the universal reconstructed
family to be flat with that Hilbert polynomial.  The mathematical input is the
zero-polynomial Gotzmann persistence theorem; this file only performs the
universal Grassmannian normalization and reconstruction base-change transport.

The result is stated in the locally-noetherian-test interface consumed by the
one-sided projective-flattening reduction.  Its proof in fact does not use the
locally noetherian instance on the test scheme.

Main declaration:

* `AlgebraicGeometry.Scheme.
  twistedFreeQuotUniversalNextDegreeRankImpliesFlatHilbertOnLocallyNoetherianTests_zeroPolynomial`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On every locally noetherian test over the rank-zero Grassmannian, rank zero
of the pulled universal algebraic next-degree module forces the reconstructed
projective-line family to be flat with zero fibrewise Hilbert polynomial. -/
theorem
    twistedFreeQuotUniversalNextDegreeRankImpliesFlatHilbertOnLocallyNoetherianTests_zeroPolynomial
    (S : Scheme.{u}) (r m : ℕ) (l : ℤ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) :
    TwistedFreeQuotUniversalNextDegreeRankImpliesFlatHilbertOnLocallyNoetherianTests
      S 1 r 0 m l (0 : Polynomial ℚ) d e he σ := by
  intro A _ hnextUniversal
  let G := grassmannianOverRepresentation S 0 m
  let x := grassmannianPointFreeQuotient (q := 0) G
    (freeGrassmannianUniversalPoint S 0 m)
  let u₀ := grassmannianPointMonomialQuotientMap
    (n := 1) (r := r) (q := 0) (e := e) (σ := σ) G
    (freeGrassmannianUniversalPoint S 0 m)
  let E := (Modules.pullback A.hom).obj x.Q
  let u := pullbackFreeQuotientMap A.hom u₀
  letI hxqc : x.Q.IsQuasicoherent := x.isQuasicoherent
  let f := SheafOfModules.freeMap (R := G.left.ringCatSheaf) σ.symm
  letI hfiso : IsIso f := Modules.freeMap_isIso_of_equiv σ.symm
  letI hxu₀ : Epi u₀ := by
    dsimp only [u₀, grassmannianPointMonomialQuotientMap, f, x]
    letI : Epi (grassmannianPointFreeQuotient (q := 0) G
      (freeGrassmannianUniversalPoint S 0 m)).π :=
        (grassmannianPointFreeQuotient (q := 0) G
          (freeGrassmannianUniversalPoint S 0 m)).epi
    infer_instance
  letI hEqc : E.IsQuasicoherent := inferInstance
  letI hu : Epi u := by
    letI : Epi ((Modules.pullback A.hom).map u₀) := inferInstance
    letI : Epi
        (Modules.pullbackFreeIso A.hom
          (ULift.{u} (Fin r) × Fin ((1 + e).choose 1))).inv :=
      inferInstance
    dsimp only [u, pullbackFreeQuotientMap]
    exact epi_comp _ _
  have hEzero : Modules.IsProjectiveOfRank
      ((0 : Polynomial ℚ).hilbertNatValue d) E := by
    simpa [Polynomial.hilbertNatValue] using
      (x.isProjectiveOfRank.pullback A.hom)
  let EC := freeGrassmannianUniversalNextDegreeModulePullbackIso
    S 1 r m 0 e σ A.hom
  have hnext : Modules.IsProjectiveOfRank
      ((0 : Polynomial ℚ).hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule 1 A.left r e u) :=
    hnextUniversal.of_iso EC
  have hdirect :=
    (Modules.twistedFreeQuotNextDegreeGotzmannPersistence_zeroPolynomial
      A.left l r d e he u) hEzero hnext
  let EQ := reconstructedQuotient'PullbackIso 1 l r d e he
    A.hom u₀ x.isProjectiveOfRank.isFiniteLocallyFree
      (twistedFreeAmbientReconstructionCompatibility
        1 G.left l r d e he)
      (twistedFreeAmbientReconstructionCompatibility
        1 A.left l r d e he)
  exact ⟨Modules.FlatOver.of_iso EQ.symm hdirect.1,
    HasFiberwiseHilbertPolynomial.of_iso EQ.symm hdirect.2⟩

end AlgebraicGeometry.Scheme

end

end
