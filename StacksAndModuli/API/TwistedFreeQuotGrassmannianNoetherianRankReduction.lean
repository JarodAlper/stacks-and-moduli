module

public import StacksAndModuli.API.ProjectiveFlatteningNoetherianRankReduction
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalFlatteningFiniteness
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalNextDegree

/-!
# Noetherian-test reduction for the universal reconstructed Quot family

This file specializes the one-sided noetherian-test reduction for projective
flattening to the universal free-Grassmannian reconstruction used in the Quot
construction.  The proposed rank sheaf is
`freeGrassmannianUniversalNextDegreeModule`, while the projective family is
`freeGrassmannianUniversalReconstructedQuotient`.

Only the rank-to-family implication is restricted to locally noetherian test
schemes.  The converse, from a flat family with prescribed fibrewise Hilbert
polynomial to the algebraic next-degree rank, is still required on arbitrary
test schemes.  The final declaration packages these two inputs into the
represented immersed projective flattening locus; it does not assert either
mathematical implication.

Main declarations:

* `TwistedFreeQuotUniversalNextDegreeRankImpliesFlatHilbertOnLocallyNoetherianTests`;
* `TwistedFreeQuotUniversalNextDegreeFlatHilbertImpliesRank`;
* `twistedFreeQuotUniversalFlatteningLocusWitness_of_locallyNoetherianTests`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {n r q m : ℕ} {l : ℤ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
  {σ : ULift.{u} (Fin m) ≃
    ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- On locally noetherian tests over the universal free Grassmannian, the
prescribed rank of the pulled-back universal algebraic next-degree module
implies flatness and the prescribed fibrewise Hilbert polynomial for the
pulled-back reconstructed projective family.

This is a named input predicate, not an assertion that the implication holds. -/
def TwistedFreeQuotUniversalNextDegreeRankImpliesFlatHilbertOnLocallyNoetherianTests
    (S : Scheme.{u}) (n r q m : ℕ) (l : ℤ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n)) : Prop :=
  ∀ (A : Over (grassmannianOverRepresentation S q m).left)
      [IsLocallyNoetherian A.left],
    Modules.IsProjectiveOfRank (P.hilbertNatValue (d + 1))
        ((Modules.pullback A.hom).obj
          (freeGrassmannianUniversalNextDegreeModule S n r m q e σ)) →
      (Modules.projectiveFamilyAt n
        (freeGrassmannianUniversalReconstructedQuotient
          S n r q m l d e he σ) A).FlatOver
          (projectiveSpaceOverπ n A.left) ∧
        HasFiberwiseHilbertPolynomial
          (Modules.projectiveFamilyAt n
            (freeGrassmannianUniversalReconstructedQuotient
              S n r q m l d e he σ) A) P

/-- On arbitrary tests over the universal free Grassmannian, flatness with the
prescribed fibrewise Hilbert polynomial implies the prescribed rank of the
pulled-back universal algebraic next-degree module.

This is the direction which the ordinary rank-locus universal point does not
reduce to locally noetherian tests.  The definition makes no claim that the
implication holds. -/
def TwistedFreeQuotUniversalNextDegreeFlatHilbertImpliesRank
    (S : Scheme.{u}) (n r q m : ℕ) (l : ℤ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n)) : Prop :=
  ∀ A : Over (grassmannianOverRepresentation S q m).left,
    ((Modules.projectiveFamilyAt n
        (freeGrassmannianUniversalReconstructedQuotient
          S n r q m l d e he σ) A).FlatOver
          (projectiveSpaceOverπ n A.left) ∧
        HasFiberwiseHilbertPolynomial
          (Modules.projectiveFamilyAt n
            (freeGrassmannianUniversalReconstructedQuotient
              S n r q m l d e he σ) A) P) →
      Modules.IsProjectiveOfRank (P.hilbertNatValue (d + 1))
        ((Modules.pullback A.hom).obj
          (freeGrassmannianUniversalNextDegreeModule S n r m q e σ))

/-- The locally-noetherian-test rank implication and the arbitrary-test converse
produce the represented immersed flattening locus for the universal reconstructed
Quot family. -/
noncomputable def
    twistedFreeQuotUniversalFlatteningLocusWitness_of_locallyNoetherianTests
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (n r q m : ℕ) (hqm : q ≤ m) (l : ℤ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (hRankToFamily :
      TwistedFreeQuotUniversalNextDegreeRankImpliesFlatHilbertOnLocallyNoetherianTests
        S n r q m l P d e he σ)
    (hFamilyToRank :
      TwistedFreeQuotUniversalNextDegreeFlatHilbertImpliesRank
        S n r q m l P d e he σ) :
    Modules.ProjectiveFlatteningLocusWitness n
      (freeGrassmannianUniversalReconstructedQuotient
        S n r q m l d e he σ) P := by
  let G := grassmannianOverRepresentation S q m
  let E := freeGrassmannianUniversalNextDegreeModule S n r m q e σ
  let Q := freeGrassmannianUniversalReconstructedQuotient
    S n r q m l d e he σ
  letI : IsLocallyNoetherian G.left :=
    grassmannianOverRepresentation_isLocallyNoetherian S q m hqm
  letI : E.IsQuasicoherent :=
    freeGrassmannianUniversalNextDegreeModule_isQuasicoherent
      S n r m q e σ
  letI : Q.IsQuasicoherent :=
    freeGrassmannianUniversalReconstructedQuotient_isQuasicoherent
  apply Modules.projectiveFlatteningLocusWitness_of_locallyNoetherianTests
    n Q P E (P.hilbertNatValue (d + 1))
      (freeGrassmannianUniversalNextDegreeModule_isFinitePresentation
        S n r m q e σ)
  · intro A _ hRank
    exact hRankToFamily A hRank
  · intro A hFamily
    exact hFamilyToRank A hFamily

end AlgebraicGeometry.Scheme

end
