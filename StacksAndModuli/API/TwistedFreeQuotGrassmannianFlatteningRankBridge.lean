module

public import StacksAndModuli.API.ProjectiveFlatteningLocusBaseChange
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNextDegreeFlattening
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNumericalSaturation
public import StacksAndModuli.API.TwistedFreeQuotPushforwardRank

/-!
# Pushforward rank on the twisted-free flattening locus

The projective flattening locus supplies more than finite local freeness of an
unrelated coefficient sheaf.  Its universal point says that the pulled-back
projective family is flat with the prescribed fibrewise Hilbert polynomial.
The uniform fixed-degree cohomology theorem for twisted-free quotients therefore
makes every sufficiently large twisted pushforward finite locally free of rank
`P.hilbertNatValue t`.

For the single-rank flattening presentation defined by the algebraic
`twistedFreeNextDegreeModule`, the same universal point also gives that algebraic
module rank `P.hilbertNatValue (d + 1)`.  Hence, on the represented flattening
locus and once `d + 1` lies above the uniform cohomological bound, the algebraic
next-degree module and the geometric reconstructed pushforward are vector bundles
of exactly the same rank.  This is the numerical hypothesis consumed by
`TwistedFreeQuotGrassmannianNumericalSaturation.lean`.

The remaining mathematical input is not finite local freeness alone.  One must
construct the Gotzmann-range equivalence
`TwistedFreeQuotUniversalNextDegreeFlatteningData.rank_iff`, and the chosen degree
must lie above the uniform twisted-free pushforward bound.  Over a noetherian affine
base on the projective line, the final theorem combines these inputs with the
equal-rank saturation bridge.

Main declarations:

* `Scheme.Modules.exists_bound_flatteningLocus_pushforward_isProjectiveOfRank`;
* `Scheme.exists_bound_reconstructedQuotient_pushforward_isProjectiveOfRank`;
* `Scheme.exists_bound_universalNextDegreeFlattening_equal_ranks_on_locus`;
* `Scheme.exists_bound_twistedFreeNextDegreeReconstructionSaturation_of_flatHilbert_line`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On any represented flattening locus of a finitely presented twisted-free
quotient, every sufficiently large twisted pushforward is a vector bundle whose
rank is the natural value of the prescribed Hilbert polynomial.  The bound is
uniform in the family and in the base. -/
theorem exists_bound_flatteningLocus_pushforward_isProjectiveOfRank
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀
      (T : Scheme.{u}) [IsLocallyNoetherian T]
      (Q : (projectiveSpaceOver n T).Modules) [Q.IsQuasicoherent]
      (_hQfp : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        projectiveSpaceOverTwist n T (-l)) ⟶ Q) [Epi q]
      (D : ProjectiveFlatteningLocusWitness n Q P)
      (t : ℕ), d₀ ≤ (t : ℤ) →
      IsProjectiveOfRank (P.hilbertNatValue t)
        (projectiveTwistedPushforward n
          (projectiveFamilyAt n Q D.representative) t) := by
  obtain ⟨d₀, hd₀, h⟩ :=
    exists_bound_twistedFreeQuot_pushforward_isProjectiveOfRank_all_n
      n r l P
  refine ⟨d₀, hd₀, ?_⟩
  intro T _ Q hQqc hQfp q hq D t ht
  let Z := D.representative
  let QZ := projectiveFamilyAt n Q Z
  let qZ : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n Z.left (-l)) ⟶ QZ :=
    (projectiveSpaceOverTwistedFree_pullbackIso n r l Z.hom).inv ≫
      (pullback (projectiveSpaceOverMap n Z.hom)).map q
  letI hZimm : IsImmersion Z.hom := D.representative_hom_isImmersion
  letI hZlft : LocallyOfFiniteType Z.hom := inferInstance
  letI hZnoeth : IsLocallyNoetherian Z.left :=
    LocallyOfFiniteType.isLocallyNoetherian Z.hom
  haveI hQZfp : QZ.IsFinitePresentation :=
    isFinitePresentation_pullback_of_isFinitePresentation _ hQfp
  haveI hqZ : Epi qZ := by
    dsimp only [qZ]
    infer_instance
  let z := D.representableBy.homEquiv (𝟙 Z)
  exact h Z.left QZ hQZfp qZ hqZ z.down.down.1 z.down.down.2 t ht

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A reconstructed twisted-free quotient which lies in the flat,
fixed-Hilbert-polynomial locus has the expected pushforward rank in every
sufficiently large twist.  This is the pointwise form of the represented-locus
theorem and is uniform in the reconstruction degree. -/
theorem exists_bound_reconstructedQuotient_pushforward_isProjectiveOfRank
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (T : Scheme.{u}) [IsLocallyNoetherian T]
      (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
      (E : T.Modules) [E.IsQuasicoherent]
      (u : SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
      (_hflat : (reconstructedQuotient' n T l r d e he u).FlatOver
        (projectiveSpaceOverπ n T))
      (_hP : HasFiberwiseHilbertPolynomial
        (reconstructedQuotient' n T l r d e he u) P)
      (t : ℕ), d₀ ≤ (t : ℤ) →
      Modules.IsProjectiveOfRank (P.hilbertNatValue t)
        (Modules.projectiveTwistedPushforward n
          (reconstructedQuotient' n T l r d e he u) t) := by
  obtain ⟨d₀, hd₀, h⟩ :=
    exists_bound_twistedFreeQuot_pushforward_isProjectiveOfRank_all_n
      n r l P
  refine ⟨d₀, hd₀, ?_⟩
  intro T _ d e he E hE u hflat hP t ht
  let Q := reconstructedQuotient' n T l r d e he u
  let q := reconstructedQuotientMap' n T l r d e he u
  haveI hQfp : Q.IsFinitePresentation :=
    reconstructedQuotient'_isFinitePresentation n T l r d e he u
  haveI hq : Epi q := by
    dsimp only [q]
    infer_instance
  exact h T Q hQfp q hq hflat hP t ht

/-- On the represented algebraic next-degree flattening locus, the algebraic
next-degree module and the geometric reconstructed pushforward have the same
Hilbert-polynomial rank, once the next degree is above the uniform cohomological
bound. -/
theorem exists_bound_universalNextDegreeFlattening_equal_ranks_on_locus
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀
      (S : Scheme.{u}) [IsLocallyNoetherian S]
      (q m : ℕ) (_hqm : q ≤ m) (d e : ℕ)
      (he : (d : ℤ) - l = (e : ℤ))
      (σ : ULift.{u} (Fin m) ≃
        ULift.{u} (Fin r) × Fin ((n + e).choose n))
      (D : TwistedFreeQuotUniversalNextDegreeFlatteningData
        S n r q m l P d e he σ),
      d₀ ≤ ((d + 1 : ℕ) : ℤ) →
      let G := grassmannianOverRepresentation S q m
      let u₀ := grassmannianPointMonomialQuotientMap
        (n := n) (r := r) (q := q) (e := e) (σ := σ) G
        (freeGrassmannianUniversalPoint S q m)
      let H := D.toLocusWitness
      let Z := H.representative
      let uZ := pullbackFreeQuotientMap Z.hom u₀
      Modules.IsProjectiveOfRank (P.hilbertNatValue (d + 1))
          (twistedFreeNextDegreeModule n Z.left r e uZ) ∧
        Modules.IsProjectiveOfRank (P.hilbertNatValue (d + 1))
          (Modules.projectiveTwistedPushforward n
            (reconstructedQuotient' n Z.left l r d e he uZ) (d + 1)) := by
  obtain ⟨d₀, hd₀, hRank⟩ :=
    exists_bound_reconstructedQuotient_pushforward_isProjectiveOfRank
      n r l P
  refine ⟨d₀, hd₀, ?_⟩
  intro S _ q m hqm d e he σ D hd
  dsimp only
  let G := grassmannianOverRepresentation S q m
  let x := grassmannianPointFreeQuotient (q := q) G
    (freeGrassmannianUniversalPoint S q m)
  let u₀ := grassmannianPointMonomialQuotientMap
    (n := n) (r := r) (q := q) (e := e) (σ := σ) G
    (freeGrassmannianUniversalPoint S q m)
  let Q₀ := freeGrassmannianUniversalReconstructedQuotient
    S n r q m l d e he σ
  let H := D.toLocusWitness
  let Z := H.representative
  let uZ := pullbackFreeQuotientMap Z.hom u₀
  letI hGnoeth : IsLocallyNoetherian G.left :=
    grassmannianOverRepresentation_isLocallyNoetherian S q m hqm
  letI hZimm : IsImmersion Z.hom := H.representative_hom_isImmersion
  letI hZlft : LocallyOfFiniteType Z.hom := inferInstance
  letI hZnoeth : IsLocallyNoetherian Z.left :=
    LocallyOfFiniteType.isLocallyNoetherian Z.hom
  letI hxqc : x.Q.IsQuasicoherent := x.isQuasicoherent
  let f := SheafOfModules.freeMap (R := G.left.ringCatSheaf) σ.symm
  letI hfiso : IsIso f := Modules.freeMap_isIso_of_equiv σ.symm
  letI hxu : Epi u₀ := by
    dsimp only [u₀, grassmannianPointMonomialQuotientMap, f, x]
    letI : Epi (grassmannianPointFreeQuotient (q := q) G
      (freeGrassmannianUniversalPoint S q m)).π :=
        (grassmannianPointFreeQuotient (q := q) G
          (freeGrassmannianUniversalPoint S q m)).epi
    infer_instance
  have hxflf : Modules.IsFiniteLocallyFree x.Q :=
    x.isProjectiveOfRank.isFiniteLocallyFree
  let z := H.representableBy.homEquiv (𝟙 Z)
  have hfamily :
      (Modules.projectiveFamilyAt n Q₀ Z).FlatOver
          (projectiveSpaceOverπ n Z.left) ∧
        HasFiberwiseHilbertPolynomial
          (Modules.projectiveFamilyAt n Q₀ Z) P :=
    z.down.down
  have hnext : Modules.IsProjectiveOfRank
      (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule n Z.left r e uZ) :=
    (D.rank_iff Z).mpr hfamily
  let EQ := reconstructedQuotient'PullbackIso n l r d e he
    Z.hom u₀ hxflf
      (twistedFreeAmbientReconstructionCompatibility n G.left l r d e he)
      (twistedFreeAmbientReconstructionCompatibility n Z.left l r d e he)
  have hflatZ : (reconstructedQuotient' n Z.left l r d e he uZ).FlatOver
      (projectiveSpaceOverπ n Z.left) :=
    Modules.FlatOver.of_iso EQ hfamily.1
  have hPZ : HasFiberwiseHilbertPolynomial
      (reconstructedQuotient' n Z.left l r d e he uZ) P :=
    HasFiberwiseHilbertPolynomial.of_iso EQ hfamily.2
  have hpush := hRank Z.left d e he ((Modules.pullback Z.hom).obj x.Q)
    uZ hflatZ hPZ (d + 1) hd
  exact ⟨hnext, hpush⟩

/-- On a noetherian affine base on the projective line, membership in the flat
fixed-Hilbert-polynomial locus and the expected rank of the algebraic next-degree
module imply full next-degree saturation in every sufficiently large degree. -/
theorem exists_bound_twistedFreeNextDegreeReconstructionSaturation_of_flatHilbert_line
    (r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀
      (R : Type u) [CommRing R] [IsNoetherianRing R]
      (q d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
      (E : (Spec (.of R)).Modules) [E.IsQuasicoherent]
      (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
      [Epi u] (_hE : Modules.IsProjectiveOfRank q E)
      (_hflat : (reconstructedQuotient' 1 (Spec (.of R)) l r d e he u).FlatOver
        (projectiveSpaceOverπ 1 (Spec (.of R))))
      (_hP : HasFiberwiseHilbertPolynomial
        (reconstructedQuotient' 1 (Spec (.of R)) l r d e he u) P)
      (_hnext : Modules.IsProjectiveOfRank (P.hilbertNatValue (d + 1))
        (twistedFreeNextDegreeModule 1 (Spec (.of R)) r e u)),
      d₀ ≤ ((d + 1 : ℕ) : ℤ) →
      TwistedFreeNextDegreeReconstructionSaturation
        1 (Spec (.of R)) l r d e he u := by
  obtain ⟨d₀, hd₀, h⟩ :=
    exists_bound_reconstructedQuotient_pushforward_isProjectiveOfRank
      1 r l P
  refine ⟨d₀, hd₀, ?_⟩
  intro R _ _ q d e he E hE u hu hErank hflat hP hnext hd
  have hpush := h (Spec (.of R)) d e he E u hflat hP (d + 1) hd
  exact
    twistedFreeNextDegreeReconstructionSaturation_of_projectiveOfRank_line_of_equal_rank
      R q l r d e (P.hilbertNatValue (d + 1)) he u hErank hnext hpush

end AlgebraicGeometry.Scheme

end
