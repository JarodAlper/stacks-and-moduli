module

public import StacksAndModuli.API.ProjectiveFlatteningSingleRank
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalFlatteningFiniteness
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalNextDegree

/-!
# Projective flattening from the universal algebraic next-degree module

The universal algebraic next-degree cokernel is quasicoherent, finitely presented, and
commutes with arbitrary base change.  Consequently, the only substantive input needed to
make it represent the projective flattening locus is the Gotzmann-range equivalence between
its prescribed rank and flatness with the fixed fibrewise Hilbert polynomial.

This file records that equivalence as a structure and performs all remaining assembly into
`ProjectiveFlatteningSingleRankData` and `ProjectiveFlatteningLocusWitness`.  In particular,
the structure's field is phrased after normalized pullback of the tautological finite-free
quotient; the arbitrary-base-change isomorphism transports it to the intrinsic rank locus.
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

variable {S : Scheme.{u}} {n r m q : ℕ} {l : ℤ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
  {σ : ULift.{u} (Fin m) ≃
    ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- The exact Gotzmann-range input for cutting out the universal reconstructed
quotient's flattening locus by its algebraic next-degree module.

The degree-`d` quotient already has the tautological Grassmannian rank `q`.  This structure
asserts that imposing rank `P(d+1)` on the algebraic degree-`d+1` cokernel is equivalent,
after every normalized base change, to flatness and fibrewise Hilbert polynomial `P` of the
reconstructed projective family. -/
structure TwistedFreeQuotUniversalNextDegreeFlatteningData
    (S : Scheme.{u}) (n r q m : ℕ) (l : ℤ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n)) : Prop where
  /-- The normalized next-degree rank condition is precisely projective flattening. -/
  rank_iff (A : Over (grassmannianOverRepresentation S q m).left) :
    Modules.IsProjectiveOfRank (P.hilbertNatValue (d + 1))
        (twistedFreeNextDegreeModule n A.left r e
          (pullbackFreeQuotientMap A.hom
            (grassmannianPointMonomialQuotientMap
              (n := n) (r := r) (q := q) (e := e) (σ := σ)
              (grassmannianOverRepresentation S q m)
              (freeGrassmannianUniversalPoint S q m)))) ↔
      (Modules.projectiveFamilyAt n
          (freeGrassmannianUniversalReconstructedQuotient
            S n r q m l d e he σ) A).FlatOver
          (projectiveSpaceOverπ n A.left) ∧
        HasFiberwiseHilbertPolynomial
          (Modules.projectiveFamilyAt n
            (freeGrassmannianUniversalReconstructedQuotient
              S n r q m l d e he σ) A) P

namespace TwistedFreeQuotUniversalNextDegreeFlatteningData

/-- The universal algebraic next-degree module, together with the Gotzmann-range
equivalence, gives a single-rank presentation of projective flattening. -/
noncomputable def toSingleRankData
    (D : TwistedFreeQuotUniversalNextDegreeFlatteningData
      S n r q m l P d e he σ) :
    Modules.ProjectiveFlatteningSingleRankData n
      (freeGrassmannianUniversalReconstructedQuotient
        S n r q m l d e he σ) P where
  sheaf := freeGrassmannianUniversalNextDegreeModule S n r m q e σ
  rank := P.hilbertNatValue (d + 1)
  isQuasicoherent :=
    freeGrassmannianUniversalNextDegreeModule_isQuasicoherent
      S n r m q e σ
  isFinitePresentation :=
    freeGrassmannianUniversalNextDegreeModule_isFinitePresentation
      S n r m q e σ
  rank_iff A := by
    let E := freeGrassmannianUniversalNextDegreeModulePullbackIso
      S n r m q e σ A.hom
    constructor
    · intro h
      exact (D.rank_iff A).mp (h.of_iso E)
    · intro h
      exact ((D.rank_iff A).mpr h).of_iso E.symm

/-- The universal algebraic next-degree rank equivalence directly supplies the represented
immersed projective flattening locus. -/
noncomputable def toLocusWitness
    (D : TwistedFreeQuotUniversalNextDegreeFlatteningData
      S n r q m l P d e he σ) :
    Modules.ProjectiveFlatteningLocusWitness n
      (freeGrassmannianUniversalReconstructedQuotient
        S n r q m l d e he σ) P :=
  D.toSingleRankData.toLocusWitness

end TwistedFreeQuotUniversalNextDegreeFlatteningData

end AlgebraicGeometry.Scheme

end

end
