module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianGotzmannReduction

/-!
# The admissible Gotzmann input for reconstructed quotients on the projective line

Two adjacent ranks of an arbitrary truncated graded quotient do not determine the
associated projective sheaf.  The missing hypothesis is a module version of Gotzmann
persistence, with a bound depending on the ambient rank, the generating twist, and the
Hilbert polynomial.  In particular, the bound cannot faithfully be a property of the
polynomial alone.

This file gives that missing theorem a bounded, downstream-facing interface without
asserting it as an axiom.  A witness for admissibility is an actual nonempty family of
quotients of `O(-l)^r` with fibrewise Hilbert polynomial `P`.  Existing dimension-one
regularity proves from such a witness all elementary numerical hypotheses used by the
projective-line persistence argument.

The weakest genuinely missing result is isolated by
`TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound`: in every degree above one
uniform bound, the two adjacent algebraic ranks must force the two geometric seed
ranks over every affine base.  Pulling the algebraic ranks to affine test schemes
automatically gives the base-change-stable form used by the projective-line Cech
argument.  The stronger `TwistedFreeQuotProjectiveLineGotzmannSeedBound` asks
for the same comparison after arbitrary base change, and
`TwistedFreeQuotProjectiveLineEpimorphicSeedBound` additionally asks that the two
canonical pushforward base-change maps be epimorphisms.  The latter condition upgrades
the stable seed ranks to canonical base-change isomorphisms by the equal-rank argument
in `TwistedFreeQuotGrassmannianGotzmannReduction`.

No declaration in this file supplies these bounds.  The named propositions
`twistedFreeQuotProjectiveLineAffineGotzmannSeedStatement`,
`twistedFreeQuotProjectiveLineGotzmannSeedStatement`, and
`twistedFreeQuotProjectiveLineEpimorphicSeedStatement` record exactly the remaining
mathematical theorems.

Main declarations:

* `TwistedFreeQuotProjectiveLineHilbertPolynomialWitness`;
* `IsTwistedFreeQuotProjectiveLineAdmissible`;
* `TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound`;
* `TwistedFreeQuotNextDegreeGeometricSeedRanksUnderAffineBaseChange.upgrade`;
* `TwistedFreeQuotProjectiveLineGotzmannSeedBound`;
* `IsTwistedFreeQuotProjectiveLineAdmissible.exists_bound_gotzmannPersistence`;
* `TwistedFreeQuotProjectiveLineEpimorphicSeedBound`;
* `TwistedFreeQuotProjectiveLineEpimorphicSeedBound.canonicalSeedData`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A geometric witness that `P` occurs as the Hilbert polynomial of a quotient of
`O(-l)^r` on a nonempty projective line.

The base is allowed to be any nonempty scheme.  Passing to one residue-field fibre
recovers the usual field-valued notion of admissibility. -/
structure TwistedFreeQuotProjectiveLineHilbertPolynomialWitness
    (r : ℕ) (l : ℤ) (P : Polynomial ℚ) where
  /-- A nonempty base carrying the witness quotient. -/
  base : Scheme.{u}
  /-- The witness base has a point. -/
  nonemptyBase : Nonempty base
  /-- The quotient sheaf on the projective line. -/
  quotient : (projectiveSpaceOver 1 base).Modules
  /-- The witness quotient is quasicoherent. -/
  quotientQuasicoherent : quotient.IsQuasicoherent
  /-- The witness quotient is finitely presented. -/
  quotientFinitePresentation : quotient.IsFinitePresentation
  /-- The quotient map from the prescribed twisted-free ambient sheaf. -/
  quotientMap :
    (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist 1 base (-l)) ⟶ quotient
  /-- The witness map is a quotient. -/
  quotientMapEpi : Epi quotientMap
  /-- Every fibre has Hilbert polynomial `P`. -/
  hilbertPolynomial : HasFiberwiseHilbertPolynomial quotient P

namespace TwistedFreeQuotProjectiveLineHilbertPolynomialWitness

/-- An admissibility witness supplies the degree bound and natural-value assertions
used by the projective-line two-value persistence theorem. -/
theorem exists_eventual_numerics
    {r : ℕ} {l : ℤ} {P : Polynomial ℚ}
    (W : TwistedFreeQuotProjectiveLineHilbertPolynomialWitness r l P) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      l ≤ (d : ℤ) ∧ P.natDegree ≤ 1 ∧
        ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ) ∧
        ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
          P.eval ((d + 1 : ℕ) : ℚ) := by
  letI : W.quotient.IsQuasicoherent := W.quotientQuasicoherent
  letI : W.quotient.IsFinitePresentation := W.quotientFinitePresentation
  letI : Epi W.quotientMap := W.quotientMapEpi
  exact exists_eventual_hilbertPolynomial_numerics_of_dimension_le_one
    1 r zero_lt_one le_rfl W.base W.nonemptyBase l W.quotient
      W.quotientMap P W.hilbertPolynomial

end TwistedFreeQuotProjectiveLineHilbertPolynomialWitness

/-- A polynomial is admissible for quotients of `O(-l)^r` on the projective line if
such a quotient exists on some nonempty base. -/
def IsTwistedFreeQuotProjectiveLineAdmissible
    (r : ℕ) (l : ℤ) (P : Polynomial ℚ) : Prop :=
  Nonempty
    (TwistedFreeQuotProjectiveLineHilbertPolynomialWitness.{u} r l P)

namespace IsTwistedFreeQuotProjectiveLineAdmissible

/-- Admissibility supplies all elementary numerical prerequisites for sufficiently
large degrees.  It does not by itself supply the missing Gotzmann seed comparison. -/
theorem exists_eventual_numerics
    {r : ℕ} {l : ℤ} {P : Polynomial ℚ}
    (hP : IsTwistedFreeQuotProjectiveLineAdmissible r l P) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      l ≤ (d : ℤ) ∧ P.natDegree ≤ 1 ∧
        ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ) ∧
        ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
          P.eval ((d + 1 : ℕ) : ℚ) := by
  obtain ⟨W⟩ := hP
  exact W.exists_eventual_numerics

end IsTwistedFreeQuotProjectiveLineAdmissible

/-- Pulling a projective twisted pushforward through an open immersion of bases is an
isomorphism.  This is the open-restriction comparison for the pushforward, followed by
the compatibility of projective twisting with open pullback. -/
noncomputable def projectiveTwistedPushforwardPullbackIsoOfIsOpenImmersion
    (n : ℕ) {T T' : Scheme.{u}} (j : T' ⟶ T) [IsOpenImmersion j]
    (Q : (projectiveSpaceOver n T).Modules) (d : ℕ) :
    (pullback j).obj (projectiveTwistedPushforward n Q d) ≅
      projectiveTwistedPushforward n
        (projectiveFamilyAt n Q (Over.mk j)) d := by
  let m := projectiveSpaceOverMap n j
  let Qd := projectiveSpaceOverTwistModule Q (d : ℤ)
  let Qj := (pullback m).obj Q
  let Qjd := projectiveSpaceOverTwistModule Qj (d : ℤ)
  let eQ : (restrictFunctor m).obj Qd ≅ Qjd :=
    (restrictFunctorIsoPullback m).app Qd ≪≫
      projectiveSpaceOverTwistModule_pullbackIso_of_isOpenImmersion
        n j Q (d : ℤ)
  exact ((restrictFunctorIsoPullback j).app
      (projectiveTwistedPushforward n Q d)).symm ≪≫
    projectiveSpacePushforwardRestrictIso' n j Qd ≪≫
    (pushforward (projectiveSpaceOverπ n T')).mapIso eQ

/-- Affine-stable seed ranks, together with the two original algebraic ranks, give
seed-rank transfer after every base change.

For an arbitrary base change, the desired pushforward ranks are checked on affine
opens.  Open pullback commutes with the twisted pushforward, while the iterated
reconstructed family agrees with reconstruction after the composite base change. -/
theorem TwistedFreeQuotNextDegreeGeometricSeedRanksUnderAffineBaseChange.upgrade
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {E : T.Modules}
    [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E} [Epi u]
    (h : TwistedFreeQuotNextDegreeGeometricSeedRanksUnderAffineBaseChange
      n T l r P d e he u)
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hnext : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule n T r e u)) :
    TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange
      n T l r P d e he u := by
  let Q := reconstructedQuotient' n T l r d e he u
  intro A
  constructor
  · intro _
    have hQA : IsProjectiveOfRank (P.hilbertNatValue d)
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) := by
      apply IsProjectiveOfRank.of_affineOpen_pullbacks
      intro U
      let B : Over A.left := Over.mk U.1.ι
      let AB : Over T := (Over.map A.hom).obj B
      letI : IsAffine B.left := by
        dsimp only [B, Over.mk_left]
        exact U.2
      letI : IsAffine AB.left := by
        dsimp only [AB, Over.map_obj_left]
        infer_instance
      letI : IsOpenImmersion B.hom := by
        dsimp only [B, Over.mk_hom]
        infer_instance
      have hAB : IsProjectiveOfRank (P.hilbertNatValue d)
          (projectiveTwistedPushforward n (projectiveFamilyAt n Q AB) d) :=
        h.degree_familyAt hE AB
      have hiter : IsProjectiveOfRank (P.hilbertNatValue d)
          (projectiveTwistedPushforward n
            (projectiveFamilyAt n (projectiveFamilyAt n Q A) B) d) :=
        hAB.of_iso (projectiveTwistedPushforwardIso
          (projectiveFamilyAtBaseChangeIso n Q A.hom B).symm d)
      exact hiter.of_iso
        (projectiveTwistedPushforwardPullbackIsoOfIsOpenImmersion
          n B.hom (projectiveFamilyAt n Q A) d).symm
    let EQ := reconstructedQuotient'PullbackIso n l r d e he
      A.hom u hE.isFiniteLocallyFree
        (twistedFreeAmbientReconstructionCompatibility n T l r d e he)
        (twistedFreeAmbientReconstructionCompatibility n A.left l r d e he)
    exact hQA.of_iso (projectiveTwistedPushforwardIso EQ d)
  · intro _
    have hQA : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
        (projectiveTwistedPushforward n
          (projectiveFamilyAt n Q A) (d + 1)) := by
      apply IsProjectiveOfRank.of_affineOpen_pullbacks
      intro U
      let B : Over A.left := Over.mk U.1.ι
      let AB : Over T := (Over.map A.hom).obj B
      letI : IsAffine B.left := by
        dsimp only [B, Over.mk_left]
        exact U.2
      letI : IsAffine AB.left := by
        dsimp only [AB, Over.map_obj_left]
        infer_instance
      letI : IsOpenImmersion B.hom := by
        dsimp only [B, Over.mk_hom]
        infer_instance
      have hAB : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
          (projectiveTwistedPushforward n
            (projectiveFamilyAt n Q AB) (d + 1)) :=
        h.degreeSucc_familyAt hE hnext AB
      have hiter : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
          (projectiveTwistedPushforward n
            (projectiveFamilyAt n (projectiveFamilyAt n Q A) B) (d + 1)) :=
        hAB.of_iso (projectiveTwistedPushforwardIso
          (projectiveFamilyAtBaseChangeIso n Q A.hom B).symm (d + 1))
      exact hiter.of_iso
        (projectiveTwistedPushforwardPullbackIsoOfIsOpenImmersion
          n B.hom (projectiveFamilyAt n Q A) (d + 1)).symm
    let EQ := reconstructedQuotient'PullbackIso n l r d e he
      A.hom u hE.isFiniteLocallyFree
        (twistedFreeAmbientReconstructionCompatibility n T l r d e he)
        (twistedFreeAmbientReconstructionCompatibility n A.left l r d e he)
    exact hQA.of_iso (projectiveTwistedPushforwardIso EQ (d + 1))

/-- A uniform module-Gotzmann bound for the two geometric seed ranks on `ℙ¹`, stated
pointwise over affine bases.

This is the minimal local algebraic input.  Pulling the two algebraic ranks back to an
affine test scheme automatically produces the affine-stable form used by the reverse
implication. -/
structure TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound
    (r : ℕ) (l : ℤ) (P : Polynomial ℚ) where
  /-- A degree from which the affine pointwise seed comparison holds. -/
  bound : ℕ
  /-- The geometric seed comparison over every affine base above the bound. -/
  affineSeedRanks : ∀
    (T : Scheme.{u}) [IsAffine T]
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (E : T.Modules) [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u],
    bound ≤ d →
    IsProjectiveOfRank (P.hilbertNatValue d) E →
    IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule 1 T r e u) →
    TwistedFreeQuotNextDegreeGeometricSeedRanks
      1 T l r P d e he u

namespace TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound

/-- Evaluate the affine pointwise Gotzmann seed bound at one truncated quotient. -/
theorem seedRanks
    {r : ℕ} {l : ℤ} {P : Polynomial ℚ}
    (G : TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound.{u} r l P)
    {T : Scheme.{u}} [IsAffine T]
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    {E : T.Modules} [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E} [Epi u]
    (hd : G.bound ≤ d)
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hnext : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule 1 T r e u)) :
    TwistedFreeQuotNextDegreeGeometricSeedRanks
      1 T l r P d e he u :=
  G.affineSeedRanks T d e he E u hd hE hnext

/-- The pointwise theorem over affine bases supplies seed-rank transfer after every
affine base change of an arbitrary scheme. -/
theorem seedRanksUnderAffineBaseChange
    {r : ℕ} {l : ℤ} {P : Polynomial ℚ}
    (G : TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound.{u} r l P)
    {T : Scheme.{u}} {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    {E : T.Modules} [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E} [Epi u]
    (hd : G.bound ≤ d)
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hnext : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule 1 T r e u)) :
    TwistedFreeQuotNextDegreeGeometricSeedRanksUnderAffineBaseChange
      1 T l r P d e he u := by
  intro A hA
  let EA := (pullback A.hom).obj E
  let uA := pullbackFreeQuotientMap A.hom u
  letI : EA.IsQuasicoherent := inferInstance
  letI : Epi uA := by
    letI : Epi ((pullback A.hom).map u) := inferInstance
    letI : Epi (pullbackFreeIso A.hom
        (ULift.{u} (Fin r) × Fin ((1 + e).choose 1))).inv := inferInstance
    dsimp only [uA, pullbackFreeQuotientMap]
    exact epi_comp _ _
  letI : (twistedFreeNextDegreeModule 1 T r e u).IsQuasicoherent :=
    twistedFreeNextDegreeModule_isQuasicoherent 1 T r e u
  let EC := twistedFreeNextDegreeModulePullbackIso
    1 A.hom r e u hE.isFiniteLocallyFree
  have hEA : IsProjectiveOfRank (P.hilbertNatValue d) EA := hE.pullback A.hom
  have hnextA : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule 1 A.left r e uA) :=
    (hnext.pullback A.hom).of_iso EC
  exact G.seedRanks hd hEA hnextA

/-- Above a pointwise affine seed bound, the remaining projective-line Čech argument
gives reverse Gotzmann persistence. -/
theorem gotzmannPersistence
    {r : ℕ} {l : ℤ} {P : Polynomial ℚ}
    (G : TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound.{u} r l P)
    {T : Scheme.{u}} {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    {E : T.Modules} [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E} [Epi u]
    (hd : G.bound ≤ d) (hld : l ≤ (d : ℤ))
    (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ)) :
    TwistedFreeQuotNextDegreeGotzmannPersistence
      1 T l r P d e he u := by
  intro hE hnext
  exact
    (TwistedFreeQuotNextDegreeGotzmannPersistence.of_affineStableGeometricSeedRanks_one
      T l r P d e he u hld hPdeg hPd hPsucc
        (G.seedRanksUnderAffineBaseChange hd hE hnext)) hE hnext

end TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound

/-- A uniform module-Gotzmann bound for the two geometric seed ranks on `ℙ¹`.

For an arbitrary quotient of the degree-`d` monomial coefficient sheaf, the expected
ranks in degrees `d` and `d+1` must force the corresponding geometric pushforward
ranks after every base change.  Both algebraic rank assumptions occur before the
conclusion: this is essential, since neither adjacent rank is a saturation statement
by itself. -/
structure TwistedFreeQuotProjectiveLineGotzmannSeedBound
    (r : ℕ) (l : ℤ) (P : Polynomial ℚ) where
  /-- A degree from which the seed comparison holds. -/
  bound : ℕ
  /-- The stable geometric seed comparison above the bound. -/
  seedRanksUnderBaseChange : ∀
    (T : Scheme.{u}) (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (E : T.Modules) [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u],
    bound ≤ d →
    IsProjectiveOfRank (P.hilbertNatValue d) E →
    IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule 1 T r e u) →
    TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange
      1 T l r P d e he u

namespace TwistedFreeQuotProjectiveLineGotzmannSeedBound

/-- An arbitrary-base-change seed bound restricts to the pointwise affine bound. -/
noncomputable def toAffine
    {r : ℕ} {l : ℤ} {P : Polynomial ℚ}
    (G : TwistedFreeQuotProjectiveLineGotzmannSeedBound.{u} r l P) :
    TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound.{u} r l P where
  bound := G.bound
  affineSeedRanks T _ d e he E _ u _ hd hE hnext :=
    (G.seedRanksUnderBaseChange T d e he E u hd hE hnext).base hE

/-- Evaluate a uniform Gotzmann seed bound at one truncated quotient. -/
theorem seedRanks
    {r : ℕ} {l : ℤ} {P : Polynomial ℚ}
    (G : TwistedFreeQuotProjectiveLineGotzmannSeedBound.{u} r l P)
    {T : Scheme.{u}} {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    {E : T.Modules} [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E} [Epi u]
    (hd : G.bound ≤ d)
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hnext : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule 1 T r e u)) :
    TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange
      1 T l r P d e he u :=
  G.seedRanksUnderBaseChange T d e he E u hd hE hnext

/-- Above the seed bound, the stable algebraic-to-geometric comparison is the only
non-formal input needed for reverse Gotzmann persistence on the projective line. -/
theorem gotzmannPersistence
    {r : ℕ} {l : ℤ} {P : Polynomial ℚ}
    (G : TwistedFreeQuotProjectiveLineGotzmannSeedBound.{u} r l P)
    {T : Scheme.{u}} {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    {E : T.Modules} [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E} [Epi u]
    (hd : G.bound ≤ d) (hld : l ≤ (d : ℤ))
    (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ)) :
    TwistedFreeQuotNextDegreeGotzmannPersistence
      1 T l r P d e he u := by
  intro hE hnext
  exact
    (TwistedFreeQuotNextDegreeGotzmannPersistence.of_stableGeometricSeedRanks_one
      T l r P d e he u hld hPdeg hPd hPsucc
        (G.seedRanks hd hE hnext)) hE hnext

end TwistedFreeQuotProjectiveLineGotzmannSeedBound

namespace TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound

/-- A pointwise affine seed bound upgrades to the arbitrary-base-change form.

The two global algebraic rank hypotheses in the bound let the affine comparison be
applied on every affine open of an arbitrary base change; open-restriction base change
and local descent then recover the global geometric ranks. -/
noncomputable def toGotzmannSeedBound
    {r : ℕ} {l : ℤ} {P : Polynomial ℚ}
    (G : TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound.{u} r l P) :
    TwistedFreeQuotProjectiveLineGotzmannSeedBound.{u} r l P where
  bound := G.bound
  seedRanksUnderBaseChange T d e he E _ u _ hd hE hnext :=
    (G.seedRanksUnderAffineBaseChange (T := T) (d := d) (e := e) (he := he)
      (E := E) (u := u) hd hE hnext).upgrade hE hnext

end TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound

namespace IsTwistedFreeQuotProjectiveLineAdmissible

/-- Admissibility and a Gotzmann seed bound have a common uniform bound above which
reverse projective-line persistence holds for every truncated quotient. -/
theorem exists_bound_gotzmannPersistence
    {r : ℕ} {l : ℤ} {P : Polynomial ℚ}
    (hP : IsTwistedFreeQuotProjectiveLineAdmissible.{u} r l P)
    (G : TwistedFreeQuotProjectiveLineGotzmannSeedBound.{u} r l P) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → ∀
      (T : Scheme.{u}) (e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
      (E : T.Modules) [E.IsQuasicoherent]
      (u : SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u],
      TwistedFreeQuotNextDegreeGotzmannPersistence
        1 T l r P d e he u := by
  obtain ⟨DN, hN⟩ := hP.exists_eventual_numerics
  refine ⟨max DN G.bound, ?_⟩
  intro d hd T e he E hEqc u hu
  obtain ⟨hld, hPdeg, hPd, hPsucc⟩ :=
    hN d (le_trans (le_max_left DN G.bound) hd)
  exact G.gotzmannPersistence
    (le_trans (le_max_right DN G.bound) hd) hld hPdeg hPd hPsucc

/-- Admissibility and the minimal pointwise affine Gotzmann seed bound have a common
uniform bound above which reverse projective-line persistence holds for every
truncated quotient. -/
theorem exists_bound_gotzmannPersistence_of_affineSeedBound
    {r : ℕ} {l : ℤ} {P : Polynomial ℚ}
    (hP : IsTwistedFreeQuotProjectiveLineAdmissible.{u} r l P)
    (G : TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound.{u} r l P) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d → ∀
      (T : Scheme.{u}) (e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
      (E : T.Modules) [E.IsQuasicoherent]
      (u : SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u],
      TwistedFreeQuotNextDegreeGotzmannPersistence
        1 T l r P d e he u := by
  obtain ⟨DN, hN⟩ := hP.exists_eventual_numerics
  refine ⟨max DN G.bound, ?_⟩
  intro d hd T e he E hEqc u hu
  obtain ⟨hld, hPdeg, hPd, hPsucc⟩ :=
    hN d (le_trans (le_max_left DN G.bound) hd)
  exact G.gotzmannPersistence
    (le_trans (le_max_right DN G.bound) hd) hld hPdeg hPd hPsucc

end IsTwistedFreeQuotProjectiveLineAdmissible

/-- A Gotzmann seed bound together with epimorphy of the two canonical pushforward
base-change maps.  Equal ranks then make those canonical maps invertible.

The epimorphism fields are kept separate from the seed theorem because stable seed
ranks already suffice for the projective-line flatness and Hilbert-polynomial
arguments, while canonical base change is a stronger downstream interface. -/
structure TwistedFreeQuotProjectiveLineEpimorphicSeedBound
    (r : ℕ) (l : ℤ) (P : Polynomial ℚ) : Type
    extends TwistedFreeQuotProjectiveLineGotzmannSeedBound.{u} r l P where
  /-- Canonical base change in degree `d` is epic above the bound. -/
  degreeBaseChangeEpi : ∀
    (T : Scheme.{u}) (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (E : T.Modules) [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u],
    bound ≤ d →
    IsProjectiveOfRank (P.hilbertNatValue d) E →
    IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule 1 T r e u) →
    ∀ A : Over T, Epi (projectiveTwistedPushforwardBaseChangeHom 1
      (reconstructedQuotient' 1 T l r d e he u) d A)
  /-- Canonical base change in degree `d+1` is epic above the bound. -/
  degreeSuccBaseChangeEpi : ∀
    (T : Scheme.{u}) (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (E : T.Modules) [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u],
    bound ≤ d →
    IsProjectiveOfRank (P.hilbertNatValue d) E →
    IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule 1 T r e u) →
    ∀ A : Over T, Epi (projectiveTwistedPushforwardBaseChangeHom 1
      (reconstructedQuotient' 1 T l r d e he u) (d + 1) A)

namespace TwistedFreeQuotProjectiveLineEpimorphicSeedBound

/-- Evaluate the stronger bound to obtain the algebraic package of stable seed ranks
and epimorphic canonical maps. -/
theorem epimorphicStableSeedData
    {r : ℕ} {l : ℤ} {P : Polynomial ℚ}
    (G : TwistedFreeQuotProjectiveLineEpimorphicSeedBound.{u} r l P)
    {T : Scheme.{u}} {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    {E : T.Modules} [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E} [Epi u]
    (hd : G.bound ≤ d)
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hnext : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule 1 T r e u)) :
    TwistedFreeQuotNextDegreeEpimorphicStableSeedData
      1 T l r P d e he u where
  seedRanksUnderBaseChange :=
    G.seedRanksUnderBaseChange T d e he E u hd hE hnext
  degreeBaseChangeEpi :=
    G.degreeBaseChangeEpi T d e he E u hd hE hnext
  degreeSuccBaseChangeEpi :=
    G.degreeSuccBaseChangeEpi T d e he E u hd hE hnext

/-- Above the stronger bound, the adjacent algebraic ranks produce the canonical seed
data used by the reverse projective-line persistence theorem. -/
theorem canonicalSeedData
    {r : ℕ} {l : ℤ} {P : Polynomial ℚ}
    (G : TwistedFreeQuotProjectiveLineEpimorphicSeedBound.{u} r l P)
    {T : Scheme.{u}} {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    {E : T.Modules} [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E} [Epi u]
    (hd : G.bound ≤ d)
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hnext : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule 1 T r e u)) :
    TwistedFreeQuotNextDegreeCanonicalSeedData
      1 T l r P d e he u :=
  (G.epimorphicStableSeedData hd hE hnext).canonicalSeedData hE hnext

end TwistedFreeQuotProjectiveLineEpimorphicSeedBound

/-- The exact missing module-Gotzmann theorem in the minimal pointwise affine form used by
the projective-line reverse implication.

This is a named proposition, not an axiom: no proof is supplied here. -/
def twistedFreeQuotProjectiveLineAffineGotzmannSeedStatement : Prop :=
  ∀ (r : ℕ) (l : ℤ) (P : Polynomial ℚ),
    IsTwistedFreeQuotProjectiveLineAdmissible.{u} r l P →
      Nonempty
        (TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound.{u} r l P)

/-- The arbitrary-base-change form of the missing module-Gotzmann theorem for
geometric seed ranks on `ℙ¹`.

This is a named proposition, not an axiom: no proof is supplied here. -/
def twistedFreeQuotProjectiveLineGotzmannSeedStatement : Prop :=
  ∀ (r : ℕ) (l : ℤ) (P : Polynomial ℚ),
    IsTwistedFreeQuotProjectiveLineAdmissible.{u} r l P →
      Nonempty
        (TwistedFreeQuotProjectiveLineGotzmannSeedBound.{u} r l P)

/-- The pointwise affine and arbitrary-base-change formulations of the missing seed-bound
theorem are equivalent.  The nontrivial direction uses open-locality of projective
twisted pushforwards and the two algebraic ranks already carried by the bound. -/
theorem twistedFreeQuotProjectiveLineGotzmannSeedStatement_iff_affine :
    twistedFreeQuotProjectiveLineGotzmannSeedStatement.{u} ↔
      twistedFreeQuotProjectiveLineAffineGotzmannSeedStatement.{u} := by
  constructor
  · intro h r l P hP
    obtain ⟨G⟩ := h r l P hP
    exact ⟨G.toAffine⟩
  · intro h r l P hP
    obtain ⟨G⟩ := h r l P hP
    exact ⟨G.toGotzmannSeedBound⟩

/-- The stronger missing statement which also makes the two canonical pushforward
base-change maps epic.  Combined with equal ranks, it yields canonical base change in
the two seed degrees.  This too is only a named proposition. -/
def twistedFreeQuotProjectiveLineEpimorphicSeedStatement : Prop :=
  ∀ (r : ℕ) (l : ℤ) (P : Polynomial ℚ),
    IsTwistedFreeQuotProjectiveLineAdmissible.{u} r l P →
      Nonempty
        (TwistedFreeQuotProjectiveLineEpimorphicSeedBound.{u} r l P)

end AlgebraicGeometry.Scheme.Modules

end

end
