module

public import StacksAndModuli.API.ProjectiveFamilyAffineLocal
public import StacksAndModuli.API.ProjectiveDimensionOneMultiplicationEpi
public import StacksAndModuli.API.ProjectiveFlatteningUniversalFamily
public import StacksAndModuli.API.ProjectiveLineTwistedFreeQuotientFlatnessPersistence
public import StacksAndModuli.API.ProjectiveRankFieldIso
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFlatteningRankBridge

/-!
# Reducing the universal next-degree rank equivalence to pointwise Gotzmann persistence

The universal Grassmannian formulation of the missing Gotzmann theorem contains two
inessential layers of bookkeeping: normalized pullback of the tautological quotient and
comparison of the pulled universal reconstruction with reconstruction after base change.
This file removes both layers.

It isolates the remaining mathematical input as a statement about an arbitrary quotient
of the appropriate finite free sheaf on an arbitrary scheme.  Such a pointwise theorem,
in any projective-space dimension, supplies
`TwistedFreeQuotUniversalNextDegreeFlatteningData` without further hypotheses.  Thus the
remaining dimension-one problem can be attacked directly on a quotient over `T`, with no
reference to the universal Grassmannian.

On a noetherian affine projective line, the existing saturation and uniform pushforward
rank theorems prove the forward implication from the single relation-generation
epimorphism; relation-kernel `H¹`-vanishing is a sufficient cohomological formulation.
In the reverse direction, the existing projective-line Čech recurrence proves
flatness and Hilbert-polynomial persistence once the two algebraic seed ranks transfer to
the corresponding geometric pushforwards after every affine base change.  On residue-field
fibres, equal rank gives the arbitrary isomorphisms consumed by the recurrence; neither
canonical base change nor multiplication coherence is necessary.  The interfaces below
isolate this remaining algebraic-to-geometric comparison.

Main declarations:

* `Scheme.Modules.TwistedFreeQuotNextDegreeGotzmannPersistence`;
* `Scheme.Modules.TwistedFreeQuotNextDegreeRelationGeneration`;
* `Scheme.Modules.TwistedFreeQuotNextDegreeGeometricSeedRanks`;
* `Scheme.Modules.TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange`;
* `Scheme.Modules.TwistedFreeQuotNextDegreeGeometricSeedRanksUnderAffineBaseChange`;
* `Scheme.Modules.TwistedFreeQuotNextDegreeCanonicalSeedData`;
* `Scheme.Modules.TwistedFreeQuotNextDegreeGotzmannPersistence.`
  `of_affineStableGeometricSeedRanks_one`;
* `Scheme.Modules.twistedFreeQuotNextDegreeRankIffFlatHilbert_of_affine`;
* `Scheme.TwistedFreeQuotUniversalNextDegreeFlatteningData.ofAffinePointwise`.
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

namespace Modules

/-- Base change for two adjacent projective twisted pushforwards, with no
multiplication-coherence field.  This packages the canonical-base-change variant of the
projective-line Čech flatness and Hilbert-function arguments. -/
structure ProjectiveOneStepAdjacentBaseChangeComparison
    (n : ℕ) (Q : (projectiveSpaceOver n T).Modules) (d : ℕ) where
  /-- Base change in degree `d`. -/
  degree (A : Over T) :
    (pullback A.hom).obj (projectiveTwistedPushforward n Q d) ≅
      projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d
  /-- Base change in degree `d+1`. -/
  degreeSucc (A : Over T) :
    (pullback A.hom).obj (projectiveTwistedPushforward n Q (d + 1)) ≅
      projectiveTwistedPushforward n (projectiveFamilyAt n Q A) (d + 1)

namespace ProjectiveOneStepAdjacentBaseChangeComparison

/-- Forget multiplication coherence from a one-step base-change package. -/
noncomputable def ofMultiplication
    {n d : ℕ} {Q : (projectiveSpaceOver n T).Modules}
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison n Q d) :
    ProjectiveOneStepAdjacentBaseChangeComparison n Q d where
  degree := C.degree
  degreeSucc := C.degreeSucc

/-- Two adjacent canonical Cohomology-and-Base-Change assertions supply the
comparison package needed on the projective line. -/
noncomputable def ofCanonical
    {n d : ℕ} {Q : (projectiveSpaceOver n T).Modules}
    (hdegree : ProjectiveTwistedPushforwardCanonicalBaseChange n Q d)
    (hdegreeSucc : ProjectiveTwistedPushforwardCanonicalBaseChange n Q (d + 1)) :
    ProjectiveOneStepAdjacentBaseChangeComparison n Q d where
  degree A := by
    letI := hdegree A
    exact asIso (projectiveTwistedPushforwardBaseChangeHom n Q d A)
  degreeSucc A := by
    letI := hdegreeSucc A
    exact asIso (projectiveTwistedPushforwardBaseChangeHom n Q (d + 1) A)

/-- Degree-`d` base change after one prior base change. -/
noncomputable def degree_familyAt
    {n d : ℕ} {Q : (projectiveSpaceOver n T).Modules}
    (C : ProjectiveOneStepAdjacentBaseChangeComparison n Q d)
    (A : Over T) (B : Over A.left) :
    (pullback B.hom).obj
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) ≅
      projectiveTwistedPushforward n
        (projectiveFamilyAt n (projectiveFamilyAt n Q A) B) d :=
  projectiveTwistedPushforwardIteratedBaseChangeIso Q A B
    (C.degree A) (C.degree ((Over.map A.hom).obj B))

/-- Degree-`d+1` base change after one prior base change. -/
noncomputable def degreeSucc_familyAt
    {n d : ℕ} {Q : (projectiveSpaceOver n T).Modules}
    (C : ProjectiveOneStepAdjacentBaseChangeComparison n Q d)
    (A : Over T) (B : Over A.left) :
    (pullback B.hom).obj
        (projectiveTwistedPushforward n
          (projectiveFamilyAt n Q A) (d + 1)) ≅
      projectiveTwistedPushforward n
        (projectiveFamilyAt n (projectiveFamilyAt n Q A) B) (d + 1) :=
  projectiveTwistedPushforwardIteratedBaseChangeIso Q A B
    (C.degreeSucc A) (C.degreeSucc ((Over.map A.hom).obj B))

end ProjectiveOneStepAdjacentBaseChangeComparison

/-- A canonical twisted-pushforward base-change map is invertible if it is epic and
its source and target are vector bundles of the same rank.  The source rank is obtained
by pulling back the rank of the original pushforward. -/
theorem projectiveTwistedPushforwardCanonicalBaseChange_of_epi_of_familyAt_rank
    {T : Scheme.{u}} {n d q : ℕ}
    {Q : (projectiveSpaceOver n T).Modules} [Q.IsQuasicoherent]
    (hQ : IsProjectiveOfRank q (projectiveTwistedPushforward n Q d))
    (hfamily : ∀ A : Over T, IsProjectiveOfRank q
      (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d))
    (hepi : ∀ A : Over T,
      Epi (projectiveTwistedPushforwardBaseChangeHom n Q d A)) :
    ProjectiveTwistedPushforwardCanonicalBaseChange n Q d := by
  intro A
  letI : Epi (projectiveTwistedPushforwardBaseChangeHom n Q d A) := hepi A
  exact isIso_of_epi_of_isProjectiveOfRank
    (hQ.pullback A.hom) (hfamily A)
      (projectiveTwistedPushforwardBaseChangeHom n Q d A)

/-- The pointwise algebraic Gotzmann assertion needed by the universal next-degree
flattening construction.

For a quotient of the degree-`d` monomial module on a scheme `T`, it says that the
algebraic degree-`d+1` cokernel has the prescribed rank exactly when the reconstructed
quotient on `ℙⁿ_T` is flat with the prescribed fibrewise Hilbert polynomial. -/
def TwistedFreeQuotNextDegreeRankIffFlatHilbert
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : Prop :=
  IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule n T r e u) ↔
    (reconstructedQuotient' n T l r d e he u).FlatOver
        (projectiveSpaceOverπ n T) ∧
      HasFiberwiseHilbertPolynomial
        (reconstructedQuotient' n T l r d e he u) P

/-- The reverse, genuinely Gotzmann, half of the pointwise next-degree rank
equivalence.  The degree-`d` coefficient quotient is required to have its
Hilbert-polynomial rank; the expected algebraic rank in degree `d+1` must then
force relative flatness and the prescribed fibrewise Hilbert polynomial. -/
def TwistedFreeQuotNextDegreeGotzmannPersistence
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : Prop :=
  IsProjectiveOfRank (P.hilbertNatValue d) E →
    IsProjectiveOfRank (P.hilbertNatValue (d + 1))
        (twistedFreeNextDegreeModule n T r e u) →
      (reconstructedQuotient' n T l r d e he u).FlatOver
          (projectiveSpaceOverπ n T) ∧
        HasFiberwiseHilbertPolynomial
          (reconstructedQuotient' n T l r d e he u) P

/-- The forward regularity half of the pointwise next-degree rank equivalence.
It records exactly the two geometric conclusions used by the existing API:
next-degree saturation, and the expected rank of the geometric pushforward. -/
def TwistedFreeQuotNextDegreeFlatHilbertRegularity
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : Prop :=
  IsProjectiveOfRank (P.hilbertNatValue d) E →
    (reconstructedQuotient' n T l r d e he u).FlatOver
          (projectiveSpaceOverπ n T) ∧
        HasFiberwiseHilbertPolynomial
          (reconstructedQuotient' n T l r d e he u) P →
      TwistedFreeNextDegreeReconstructionSaturation
          n T l r d e he u ∧
        IsProjectiveOfRank (P.hilbertNatValue (d + 1))
          (projectiveTwistedPushforward n
            (reconstructedQuotient' n T l r d e he u) (d + 1))

/-- The remaining relation-generation input in the forward direction, expressed
cohomologically.  It only asks for the relation-kernel `H¹` vanishing on the
flat fixed-Hilbert-polynomial locus. -/
def TwistedFreeQuotNextDegreeRelationKernelRegularity
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : Prop :=
  (reconstructedQuotient' n T l r d e he u).FlatOver
        (projectiveSpaceOverπ n T) ∧
      HasFiberwiseHilbertPolynomial
        (reconstructedQuotient' n T l r d e he u) P →
    Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (kernel (tensorMapLeft
          (Abelian.factorThruImage
            (reconstructedRelation' n T l r d e he u))
          (projectiveSpaceOverTwist n T
            ((d + 1 : ℕ) : ℤ))))).H 1)

/-- The exact relation-generation input in the forward direction.  On the flat
fixed-Hilbert-polynomial locus, degree-one multiples of the degree-`d`
relations must generate the full kernel of the reconstructed degree-`d+1`
monomial map.  This is the second and genuinely non-formal field of
`TwistedFreeNextDegreeReconstructionSaturation`. -/
def TwistedFreeQuotNextDegreeRelationGeneration
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : Prop :=
  (reconstructedQuotient' n T l r d e he u).FlatOver
        (projectiveSpaceOverπ n T) ∧
      HasFiberwiseHilbertPolynomial
        (reconstructedQuotient' n T l r d e he u) P →
    Epi (twistedFreeNextDegreeReconstructedKernelLift
      n T l r d e he u)

/-- The exact algebraic-to-geometric seed-rank bridge needed by the
projective-line Čech persistence theorems.  It asks only for rank transfer in
degrees `d` and `d+1`, not for an isomorphism or for full saturation. -/
def TwistedFreeQuotNextDegreeGeometricSeedRanks
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : Prop :=
  (IsProjectiveOfRank (P.hilbertNatValue d) E →
      IsProjectiveOfRank (P.hilbertNatValue d)
        (projectiveTwistedPushforward n
          (reconstructedQuotient' n T l r d e he u) d)) ∧
    (IsProjectiveOfRank (P.hilbertNatValue (d + 1))
        (twistedFreeNextDegreeModule n T r e u) →
      IsProjectiveOfRank (P.hilbertNatValue (d + 1))
        (projectiveTwistedPushforward n
          (reconstructedQuotient' n T l r d e he u) (d + 1)))

/-- Algebraic-to-geometric seed-rank transfer after every base change.  This is the
base-change-stable form of the genuinely Gotzmann input: the quotient and its algebraic
next-degree module are first pulled back, then their ranks transfer to the reconstructed
geometric pushforwards. -/
def TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : Prop :=
  ∀ A : Over T, TwistedFreeQuotNextDegreeGeometricSeedRanks
    n A.left l r P d e he (pullbackFreeQuotientMap A.hom u)

/-- Algebraic-to-geometric seed-rank transfer after every affine base change.  This is
the weakest stable form used by the projective-line reverse implication: its flatness
proof restricts to affine charts and then to their residue fields. -/
def TwistedFreeQuotNextDegreeGeometricSeedRanksUnderAffineBaseChange
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : Prop :=
  ∀ (A : Over T) [IsAffine A.left],
    TwistedFreeQuotNextDegreeGeometricSeedRanks
      n A.left l r P d e he (pullbackFreeQuotientMap A.hom u)

namespace TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange

/-- Seed-rank transfer under arbitrary base change restricts to affine base changes. -/
theorem affine
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {E : T.Modules}
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E}
    (h : TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange
      n T l r P d e he u) :
    TwistedFreeQuotNextDegreeGeometricSeedRanksUnderAffineBaseChange
      n T l r P d e he u :=
  fun A ↦ h A

/-- Stable seed-rank transfer gives the degree-`d` geometric rank of every pulled
reconstructed family. -/
theorem degree_familyAt
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {E : T.Modules}
    [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E} [Epi u]
    (h : TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange
      n T l r P d e he u)
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E) (A : Over T) :
    IsProjectiveOfRank (P.hilbertNatValue d)
      (projectiveTwistedPushforward n
        (projectiveFamilyAt n
          (reconstructedQuotient' n T l r d e he u) A) d) := by
  let uA := pullbackFreeQuotientMap A.hom u
  let QA := projectiveFamilyAt n
    (reconstructedQuotient' n T l r d e he u) A
  let Q'A := reconstructedQuotient' n A.left l r d e he uA
  letI : Epi uA := by
    letI : Epi ((pullback A.hom).map u) := inferInstance
    letI : Epi (pullbackFreeIso A.hom
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))).inv := inferInstance
    dsimp only [uA, pullbackFreeQuotientMap]
    exact epi_comp _ _
  have hlocal : IsProjectiveOfRank (P.hilbertNatValue d)
      (projectiveTwistedPushforward n Q'A d) :=
    (h A).1 (hE.pullback A.hom)
  let EQ : QA ≅ Q'A := reconstructedQuotient'PullbackIso
    n l r d e he A.hom u hE.isFiniteLocallyFree
      (twistedFreeAmbientReconstructionCompatibility n T l r d e he)
      (twistedFreeAmbientReconstructionCompatibility n A.left l r d e he)
  exact hlocal.of_iso (projectiveTwistedPushforwardIso EQ.symm d)

/-- Stable seed-rank transfer gives the degree-`d+1` geometric rank of every pulled
reconstructed family. -/
theorem degreeSucc_familyAt
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {E : T.Modules}
    [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E} [Epi u]
    (h : TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange
      n T l r P d e he u)
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hnext : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule n T r e u)) (A : Over T) :
    IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (projectiveTwistedPushforward n
        (projectiveFamilyAt n
          (reconstructedQuotient' n T l r d e he u) A) (d + 1)) := by
  let uA := pullbackFreeQuotientMap A.hom u
  let QA := projectiveFamilyAt n
    (reconstructedQuotient' n T l r d e he u) A
  let Q'A := reconstructedQuotient' n A.left l r d e he uA
  letI : Epi uA := by
    letI : Epi ((pullback A.hom).map u) := inferInstance
    letI : Epi (pullbackFreeIso A.hom
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))).inv := inferInstance
    dsimp only [uA, pullbackFreeQuotientMap]
    exact epi_comp _ _
  letI : (twistedFreeNextDegreeModule n T r e u).IsQuasicoherent :=
    twistedFreeNextDegreeModule_isQuasicoherent n T r e u
  let EC := twistedFreeNextDegreeModulePullbackIso
    n A.hom r e u hE.isFiniteLocallyFree
  have hnextA : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule n A.left r e uA) :=
    (hnext.pullback A.hom).of_iso EC
  have hlocal : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (projectiveTwistedPushforward n Q'A (d + 1)) := (h A).2 hnextA
  let EQ : QA ≅ Q'A := reconstructedQuotient'PullbackIso
    n l r d e he A.hom u hE.isFiniteLocallyFree
      (twistedFreeAmbientReconstructionCompatibility n T l r d e he)
      (twistedFreeAmbientReconstructionCompatibility n A.left l r d e he)
  exact hlocal.of_iso (projectiveTwistedPushforwardIso EQ.symm (d + 1))

/-- Stable seed-rank transfer also supplies the two geometric seed ranks on the
original base, by applying it to the identity base change. -/
theorem base
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {E : T.Modules}
    [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E} [Epi u]
    (h : TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange
      n T l r P d e he u)
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E) :
    TwistedFreeQuotNextDegreeGeometricSeedRanks n T l r P d e he u := by
  let Q := reconstructedQuotient' n T l r d e he u
  let A : Over T := Over.mk (𝟙 T)
  let EI := projectiveTwistedPushforwardIso
    (projectiveFamilyAtIdentityIso n Q) d
  let EISucc := projectiveTwistedPushforwardIso
    (projectiveFamilyAtIdentityIso n Q) (d + 1)
  constructor
  · intro _
    exact (h.degree_familyAt hE A).of_iso EI
  · intro hnext
    exact (h.degreeSucc_familyAt hE hnext A).of_iso EISucc

end TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange

namespace TwistedFreeQuotNextDegreeGeometricSeedRanksUnderAffineBaseChange

/-- Affine-stable seed transfer gives the degree-`d` geometric rank of every affine
pulled reconstructed family. -/
theorem degree_familyAt
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {E : T.Modules}
    [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E} [Epi u]
    (h : TwistedFreeQuotNextDegreeGeometricSeedRanksUnderAffineBaseChange
      n T l r P d e he u)
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (A : Over T) [IsAffine A.left] :
    IsProjectiveOfRank (P.hilbertNatValue d)
      (projectiveTwistedPushforward n
        (projectiveFamilyAt n
          (reconstructedQuotient' n T l r d e he u) A) d) := by
  let uA := pullbackFreeQuotientMap A.hom u
  let QA := projectiveFamilyAt n
    (reconstructedQuotient' n T l r d e he u) A
  let Q'A := reconstructedQuotient' n A.left l r d e he uA
  letI : Epi uA := by
    letI : Epi ((pullback A.hom).map u) := inferInstance
    letI : Epi (pullbackFreeIso A.hom
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))).inv := inferInstance
    dsimp only [uA, pullbackFreeQuotientMap]
    exact epi_comp _ _
  have hlocal : IsProjectiveOfRank (P.hilbertNatValue d)
      (projectiveTwistedPushforward n Q'A d) :=
    (h A).1 (hE.pullback A.hom)
  let EQ : QA ≅ Q'A := reconstructedQuotient'PullbackIso
    n l r d e he A.hom u hE.isFiniteLocallyFree
      (twistedFreeAmbientReconstructionCompatibility n T l r d e he)
      (twistedFreeAmbientReconstructionCompatibility n A.left l r d e he)
  exact hlocal.of_iso (projectiveTwistedPushforwardIso EQ.symm d)

/-- Affine-stable seed transfer gives the degree-`d+1` geometric rank of every affine
pulled reconstructed family. -/
theorem degreeSucc_familyAt
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {E : T.Modules}
    [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E} [Epi u]
    (h : TwistedFreeQuotNextDegreeGeometricSeedRanksUnderAffineBaseChange
      n T l r P d e he u)
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hnext : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule n T r e u))
    (A : Over T) [IsAffine A.left] :
    IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (projectiveTwistedPushforward n
        (projectiveFamilyAt n
          (reconstructedQuotient' n T l r d e he u) A) (d + 1)) := by
  let uA := pullbackFreeQuotientMap A.hom u
  let QA := projectiveFamilyAt n
    (reconstructedQuotient' n T l r d e he u) A
  let Q'A := reconstructedQuotient' n A.left l r d e he uA
  letI : Epi uA := by
    letI : Epi ((pullback A.hom).map u) := inferInstance
    letI : Epi (pullbackFreeIso A.hom
        (ULift.{u} (Fin r) × Fin ((n + e).choose n))).inv := inferInstance
    dsimp only [uA, pullbackFreeQuotientMap]
    exact epi_comp _ _
  letI : (twistedFreeNextDegreeModule n T r e u).IsQuasicoherent :=
    twistedFreeNextDegreeModule_isQuasicoherent n T r e u
  let EC := twistedFreeNextDegreeModulePullbackIso
    n A.hom r e u hE.isFiniteLocallyFree
  have hnextA : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule n A.left r e uA) :=
    (hnext.pullback A.hom).of_iso EC
  have hlocal : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (projectiveTwistedPushforward n Q'A (d + 1)) := (h A).2 hnextA
  let EQ : QA ≅ Q'A := reconstructedQuotient'PullbackIso
    n l r d e he A.hom u hE.isFiniteLocallyFree
      (twistedFreeAmbientReconstructionCompatibility n T l r d e he)
      (twistedFreeAmbientReconstructionCompatibility n A.left l r d e he)
  exact hlocal.of_iso (projectiveTwistedPushforwardIso EQ.symm (d + 1))

end TwistedFreeQuotNextDegreeGeometricSeedRanksUnderAffineBaseChange

/-- Canonical comparison data sufficient for the projective-line reverse implication:
the two algebraic ranks transfer to the geometric pushforwards, and the canonical
pushforward base-change maps are invertible in those two degrees.  No multiplication
comparison is included.  Stable seed-rank transfer alone is a weaker sufficient input. -/
structure TwistedFreeQuotNextDegreeCanonicalSeedData
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : Prop where
  /-- Transfer of the two algebraic seed ranks to geometric pushforwards. -/
  seedRanks : TwistedFreeQuotNextDegreeGeometricSeedRanks
    n T l r P d e he u
  /-- Canonical Cohomology and Base Change in degree `d`. -/
  degreeBaseChange : ProjectiveTwistedPushforwardCanonicalBaseChange n
    (reconstructedQuotient' n T l r d e he u) d
  /-- Canonical Cohomology and Base Change in degree `d+1`. -/
  degreeSuccBaseChange : ProjectiveTwistedPushforwardCanonicalBaseChange n
    (reconstructedQuotient' n T l r d e he u) (d + 1)

/-- An algebraic package which additionally constructs canonical base change.
Seed-rank transfer is required uniformly after base change, while the canonical maps
themselves need only be epimorphisms.  Equal rank then upgrades them to the canonical
base-change isomorphisms in `TwistedFreeQuotNextDegreeCanonicalSeedData`.  The epi fields
are not needed for reverse Gotzmann persistence itself. -/
structure TwistedFreeQuotNextDegreeEpimorphicStableSeedData
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) : Prop where
  /-- The two algebraic ranks transfer to geometric ranks after every base change. -/
  seedRanksUnderBaseChange :
    TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange
      n T l r P d e he u
  /-- The canonical degree-`d` base-change map is epic. -/
  degreeBaseChangeEpi : ∀ A : Over T,
    Epi (projectiveTwistedPushforwardBaseChangeHom n
      (reconstructedQuotient' n T l r d e he u) d A)
  /-- The canonical degree-`d+1` base-change map is epic. -/
  degreeSuccBaseChangeEpi : ∀ A : Over T,
    Epi (projectiveTwistedPushforwardBaseChangeHom n
      (reconstructedQuotient' n T l r d e he u) (d + 1) A)

namespace TwistedFreeQuotNextDegreeCanonicalSeedData

/-- The canonical seed data supplies the adjacent comparison package consumed
by the projective-line Čech arguments. -/
noncomputable def adjacentBaseChangeComparison
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {E : T.Modules}
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E}
    (D : TwistedFreeQuotNextDegreeCanonicalSeedData
      n T l r P d e he u) :
    ProjectiveOneStepAdjacentBaseChangeComparison n
      (reconstructedQuotient' n T l r d e he u) d :=
  ProjectiveOneStepAdjacentBaseChangeComparison.ofCanonical
    D.degreeBaseChange D.degreeSuccBaseChange

end TwistedFreeQuotNextDegreeCanonicalSeedData

namespace TwistedFreeQuotNextDegreeEpimorphicStableSeedData

/-- Under the two algebraic rank assumptions used in reverse Gotzmann persistence,
stable seed transfer and epimorphic canonical maps supply the canonical seed package. -/
theorem canonicalSeedData
    {n : ℕ} {T : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {E : T.Modules}
    [E.IsQuasicoherent]
    {u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E} [Epi u]
    (D : TwistedFreeQuotNextDegreeEpimorphicStableSeedData
      n T l r P d e he u)
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hnext : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (twistedFreeNextDegreeModule n T r e u)) :
    TwistedFreeQuotNextDegreeCanonicalSeedData
      n T l r P d e he u := by
  let Q := reconstructedQuotient' n T l r d e he u
  letI hQqc : Q.IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent n T l r d e he u
  let hseeds := D.seedRanksUnderBaseChange.base hE
  exact {
    seedRanks := hseeds
    degreeBaseChange :=
      projectiveTwistedPushforwardCanonicalBaseChange_of_epi_of_familyAt_rank
        (hseeds.1 hE)
        (D.seedRanksUnderBaseChange.degree_familyAt hE)
        D.degreeBaseChangeEpi
    degreeSuccBaseChange :=
      projectiveTwistedPushforwardCanonicalBaseChange_of_epi_of_familyAt_rank
        (hseeds.2 hnext)
        (D.seedRanksUnderBaseChange.degreeSucc_familyAt hE hnext)
        D.degreeSuccBaseChangeEpi }

end TwistedFreeQuotNextDegreeEpimorphicStableSeedData

/-- On the projective line, fixed ranks of the two adjacent twisted pushforwards after
every base change imply relative flatness.  Over each residue field, the two sides of
the comparison have the same rank and hence are noncanonically isomorphic; no canonical
Cohomology-and-Base-Change map is needed. -/
theorem flatOver_one_of_familyAt_pushforward_ranks
    {T : Scheme.{u}} {r d q₀ q₁ : ℕ} {l : ℤ}
    {Q : (projectiveSpaceOver 1 T).Modules}
    [Q.IsQuasicoherent] [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist 1 T (-l)) ⟶ Q)
    [Epi q] (hd : l - 1 ≤ (d : ℤ))
    (h₀ : ∀ (A : Over T) [IsAffine A.left], IsProjectiveOfRank q₀
      (projectiveTwistedPushforward 1 (projectiveFamilyAt 1 Q A) d))
    (h₁ : ∀ (A : Over T) [IsAffine A.left], IsProjectiveOfRank q₁
      (projectiveTwistedPushforward 1
        (projectiveFamilyAt 1 Q A) (d + 1))) :
    Q.FlatOver (projectiveSpaceOverπ 1 T) := by
  apply ProjectiveSpace.flatOver_of_isFlatAbove_gammaStarPull_on_affineOpens
    1 T Q
  intro V
  let R : Type u := Γ(T, V.1)
  let B : Over T := Over.mk V.2.fromSpec
  letI : IsAffine B.left := by
    dsimp only [B, Over.mk_left]
    infer_instance
  let QV := projectiveFamilyAt 1 Q B
  let qV : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist 1 B.left (-l)) ⟶ QV :=
    (projectiveSpaceOverTwistedFree_pullbackIso 1 r l B.hom).inv ≫
      (pullback (projectiveSpaceOverMap 1 B.hom)).map q
  haveI hQVqc : QV.IsQuasicoherent := by
    dsimp only [QV, projectiveFamilyAt]
    infer_instance
  haveI hQVfp : QV.IsFinitePresentation := by
    dsimp only [QV, projectiveFamilyAt]
    infer_instance
  haveI hqV : Epi qV := by
    dsimp only [qV]
    infer_instance
  have h₀V : IsProjectiveOfRank q₀
      (projectiveTwistedPushforward 1 QV d) := h₀ B
  have h₁V : IsProjectiveOfRank q₁
      (projectiveTwistedPushforward 1 QV (d + 1)) := h₁ B
  have e₀ : ∀ (I : Ideal R) [I.IsMaximal],
      (pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R I.ResidueField)))).obj
          (projectiveTwistedPushforward 1 QV d) ≅
        projectiveTwistedPushforward 1
          (projectiveSpaceBaseChangeOfRingHom QV
            (algebraMap R I.ResidueField)) d := by
    intro I hI
    let D : Over B.left := Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap R I.ResidueField)))
    let BD : Over T := (Over.map B.hom).obj D
    letI : IsAffine BD.left := by
      dsimp only [BD, D, Over.map_obj_left, Over.mk_left]
      infer_instance
    have htarget : IsProjectiveOfRank q₀
        (projectiveTwistedPushforward 1
          (projectiveFamilyAt 1 QV D) d) :=
      (h₀ BD).of_iso (projectiveTwistedPushforwardIso
        (projectiveFamilyAtBaseChangeIso 1 Q B.hom D).symm d)
    let E := (h₀V.pullback D.hom).iso_of_isField
      (Field.toIsField I.ResidueField) htarget
    simpa only [D, QV, projectiveFamilyAt,
      projectiveSpaceBaseChangeOfRingHom, Over.mk_left, Over.mk_hom] using E
  have e₁ : ∀ (I : Ideal R) [I.IsMaximal],
      (pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R I.ResidueField)))).obj
          (projectiveTwistedPushforward 1 QV (d + 1)) ≅
        projectiveTwistedPushforward 1
          (projectiveSpaceBaseChangeOfRingHom QV
            (algebraMap R I.ResidueField)) (d + 1) := by
    intro I hI
    let D : Over B.left := Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap R I.ResidueField)))
    let BD : Over T := (Over.map B.hom).obj D
    letI : IsAffine BD.left := by
      dsimp only [BD, D, Over.map_obj_left, Over.mk_left]
      infer_instance
    have htarget : IsProjectiveOfRank q₁
        (projectiveTwistedPushforward 1
          (projectiveFamilyAt 1 QV D) (d + 1)) :=
      (h₁ BD).of_iso (projectiveTwistedPushforwardIso
        (projectiveFamilyAtBaseChangeIso 1 Q B.hom D).symm (d + 1))
    let E := (h₁V.pullback D.hom).iso_of_isField
      (Field.toIsField I.ResidueField) htarget
    simpa only [D, QV, projectiveFamilyAt,
      projectiveSpaceBaseChangeOfRingHom, Over.mk_left, Over.mk_hom] using E
  refine ⟨(d : ℤ), ?_⟩
  have hflat :=
    ProjectiveSpace.isFlatAbove_gammaStar_twistedFreeQuotient_of_pushforward_seed_baseChange
      r R l d q₀ q₁ hd QV qV h₀V h₁V e₀ e₁
  simpa only [R, B, QV, projectiveFamilyAt, ProjectiveSpace.projSpecπ,
    Over.mk_hom, Nat.reduceAdd] using hflat

/-- On the projective line, two adjacent pushforward ranks and base change in
those two degrees imply relative flatness.  Multiplication coherence is not
used: the Čech recurrence only needs the two iterated residue-field
comparisons. -/
theorem ProjectiveOneStepAdjacentBaseChangeComparison.flatOver_one
    {T : Scheme.{u}} {r d q₀ q₁ : ℕ} {l : ℤ}
    {Q : (projectiveSpaceOver 1 T).Modules}
    [Q.IsQuasicoherent] [Q.IsFinitePresentation]
    (C : ProjectiveOneStepAdjacentBaseChangeComparison 1 Q d)
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist 1 T (-l)) ⟶ Q)
    [Epi q] (hd : l - 1 ≤ (d : ℤ))
    (h₀ : IsProjectiveOfRank q₀ (projectiveTwistedPushforward 1 Q d))
    (h₁ : IsProjectiveOfRank q₁
      (projectiveTwistedPushforward 1 Q (d + 1))) :
    Q.FlatOver (projectiveSpaceOverπ 1 T) := by
  apply ProjectiveSpace.flatOver_of_isFlatAbove_gammaStarPull_on_affineOpens
    1 T Q
  intro V
  let R : Type u := Γ(T, V.1)
  let B : Over T := Over.mk V.2.fromSpec
  let QV := projectiveFamilyAt 1 Q B
  let qV : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist 1 B.left (-l)) ⟶ QV :=
    (projectiveSpaceOverTwistedFree_pullbackIso 1 r l B.hom).inv ≫
      (pullback (projectiveSpaceOverMap 1 B.hom)).map q
  haveI hQVqc : QV.IsQuasicoherent := by
    dsimp only [QV, projectiveFamilyAt]
    infer_instance
  haveI hQVfp : QV.IsFinitePresentation := by
    dsimp only [QV, projectiveFamilyAt]
    infer_instance
  haveI hqV : Epi qV := by
    dsimp only [qV]
    infer_instance
  have h₀V : IsProjectiveOfRank q₀
      (projectiveTwistedPushforward 1 QV d) :=
    IsProjectiveOfRank.of_iso (C.degree B) (h₀.pullback B.hom)
  have h₁V : IsProjectiveOfRank q₁
      (projectiveTwistedPushforward 1 QV (d + 1)) :=
    IsProjectiveOfRank.of_iso (C.degreeSucc B) (h₁.pullback B.hom)
  have e₀ : ∀ (I : Ideal R) [I.IsMaximal],
      (pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R I.ResidueField)))).obj
          (projectiveTwistedPushforward 1 QV d) ≅
        projectiveTwistedPushforward 1
          (projectiveSpaceBaseChangeOfRingHom QV
            (algebraMap R I.ResidueField)) d := by
    intro I hI
    let D : Over B.left := Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap R I.ResidueField)))
    simpa only [D, QV, projectiveFamilyAt,
      projectiveSpaceBaseChangeOfRingHom, Over.mk_left, Over.mk_hom] using
      C.degree_familyAt B D
  have e₁ : ∀ (I : Ideal R) [I.IsMaximal],
      (pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R I.ResidueField)))).obj
          (projectiveTwistedPushforward 1 QV (d + 1)) ≅
        projectiveTwistedPushforward 1
          (projectiveSpaceBaseChangeOfRingHom QV
            (algebraMap R I.ResidueField)) (d + 1) := by
    intro I hI
    let D : Over B.left := Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap R I.ResidueField)))
    simpa only [D, QV, projectiveFamilyAt,
      projectiveSpaceBaseChangeOfRingHom, Over.mk_left, Over.mk_hom] using
      C.degreeSucc_familyAt B D
  refine ⟨(d : ℤ), ?_⟩
  have hflat :=
    ProjectiveSpace.isFlatAbove_gammaStar_twistedFreeQuotient_of_pushforward_seed_baseChange
      r R l d q₀ q₁ hd QV qV h₀V h₁V e₀ e₁
  simpa only [R, B, QV, projectiveFamilyAt, ProjectiveSpace.projSpecπ,
    Over.mk_hom, Nat.reduceAdd] using hflat

/-- On the projective line, the ranks of two adjacent twisted pushforwards after every
base change determine the fibrewise Hilbert polynomial.  Only the ranks on field-valued
base changes enter the Hilbert-function window argument. -/
theorem hasFiberwiseHilbertPolynomial_one_of_familyAt_pushforward_ranks
    {T : Scheme.{u}} {r d : ℕ} {l : ℤ}
    {Q : (projectiveSpaceOver 1 T).Modules}
    [Q.IsQuasicoherent] [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist 1 T (-l)) ⟶ Q)
    [Epi q] (P : Polynomial ℚ) (hld : l ≤ (d : ℤ))
    (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (h₀ : ∀ (A : Over T) [IsAffine A.left],
      IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
        (projectiveTwistedPushforward 1 (projectiveFamilyAt 1 Q A) d))
    (h₁ : ∀ (A : Over T) [IsAffine A.left],
      IsProjectiveOfRank ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
        (projectiveTwistedPushforward 1
          (projectiveFamilyAt 1 Q A) (d + 1))) :
    HasFiberwiseHilbertPolynomial Q P := by
  intro K hK s
  let Qs := (pullback (projectiveSpaceOverMap 1 s)).obj Q
  haveI hQsfp : Qs.IsFinitePresentation :=
    isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  let qs : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist 1 (Spec K) (-l)) ⟶ Qs :=
    (projectiveSpaceOverTwistedFree_pullbackIso 1 r l s).inv ≫
      (pullback (projectiveSpaceOverMap 1 s)).map q
  haveI hqsepi : Epi qs := epi_comp _ _
  let A : Over T := Over.mk s
  letI : IsAffine A.left := by
    dsimp only [A, Over.mk_left]
    infer_instance
  have h₀s : IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
      (projectiveTwistedPushforward 1 Qs d) := h₀ A
  have h₁s : IsProjectiveOfRank
      ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
      (projectiveTwistedPushforward 1 Qs (d + 1)) := h₁ A
  let D : FieldRegularityModelOfIsField 1 K hK Qs d :=
    fieldRegularityModelOfIsField_of_twistedFreeQuotient_of_dimension_le_one
      1 r (by omega) (by omega) K hK l d hld Qs qs
  have hvalue (t : ℕ) (hdt : d ≤ t) :
      (hilbertFunctionOver Qs (t : ℤ) : ℚ) = P.eval (t : ℚ) := by
    apply D.hilbertFunctionOver_eq_of_window P hPdeg
    · intro i hi
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · have hv :=
          hilbertFunctionOver_eq_of_projectiveTwistedPushforward_isProjectiveOfRank
            1 K hK Qs (d : ℤ) ((P.eval (d : ℚ)).num.natAbs) h₀s
        rw [Nat.add_zero]
        exact (congrArg (fun z : ℕ ↦ (z : ℚ)) hv).trans hPd
      · have hv :=
          hilbertFunctionOver_eq_of_projectiveTwistedPushforward_isProjectiveOfRank
            1 K hK Qs ((d + 1 : ℕ) : ℤ)
              ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs) h₁s
        exact (congrArg (fun z : ℕ ↦ (z : ℚ)) hv).trans hPsucc
    · exact hdt
  filter_upwards [Filter.eventually_ge_atTop d] with t ht
  exact hvalue t ht

/-- On the projective line, two adjacent pushforward ranks and base change in
those degrees determine the fibrewise Hilbert polynomial.  This is the
dimension-one regularity argument with its unused multiplication hypothesis
removed. -/
theorem
    ProjectiveOneStepAdjacentBaseChangeComparison.hasFiberwiseHilbertPolynomial_one
    {T : Scheme.{u}} {r d : ℕ} {l : ℤ}
    {Q : (projectiveSpaceOver 1 T).Modules}
    [Q.IsQuasicoherent] [Q.IsFinitePresentation]
    (C : ProjectiveOneStepAdjacentBaseChangeComparison 1 Q d)
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist 1 T (-l)) ⟶ Q)
    [Epi q] (P : Polynomial ℚ) (hld : l ≤ (d : ℤ))
    (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (h₀ : IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
      (projectiveTwistedPushforward 1 Q d))
    (h₁ : IsProjectiveOfRank
      ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
      (projectiveTwistedPushforward 1 Q (d + 1))) :
    HasFiberwiseHilbertPolynomial Q P := by
  intro K hK s
  let Qs := (pullback (projectiveSpaceOverMap 1 s)).obj Q
  haveI hQsfp : Qs.IsFinitePresentation :=
    isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  let qs : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist 1 (Spec K) (-l)) ⟶ Qs :=
    (projectiveSpaceOverTwistedFree_pullbackIso 1 r l s).inv ≫
      (pullback (projectiveSpaceOverMap 1 s)).map q
  haveI hqsepi : Epi qs := epi_comp _ _
  have h₀s : IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
      (projectiveTwistedPushforward 1 Qs d) :=
    (h₀.pullback s).of_iso (C.degree (Over.mk s))
  have h₁s : IsProjectiveOfRank
      ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
      (projectiveTwistedPushforward 1 Qs (d + 1)) :=
    (h₁.pullback s).of_iso (C.degreeSucc (Over.mk s))
  let D : FieldRegularityModelOfIsField 1 K hK Qs d :=
    fieldRegularityModelOfIsField_of_twistedFreeQuotient_of_dimension_le_one
      1 r (by omega) (by omega) K hK l d hld Qs qs
  have hvalue (t : ℕ) (hdt : d ≤ t) :
      (hilbertFunctionOver Qs (t : ℤ) : ℚ) = P.eval (t : ℚ) := by
    apply D.hilbertFunctionOver_eq_of_window P hPdeg
    · intro i hi
      rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
      · have hv :=
          hilbertFunctionOver_eq_of_projectiveTwistedPushforward_isProjectiveOfRank
            1 K hK Qs (d : ℤ) ((P.eval (d : ℚ)).num.natAbs) h₀s
        rw [Nat.add_zero]
        exact (congrArg (fun z : ℕ ↦ (z : ℚ)) hv).trans hPd
      · have hv :=
          hilbertFunctionOver_eq_of_projectiveTwistedPushforward_isProjectiveOfRank
            1 K hK Qs ((d + 1 : ℕ) : ℤ)
              ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs) h₁s
        exact (congrArg (fun z : ℕ ↦ (z : ℚ)) hv).trans hPsucc
    · exact hdt
  filter_upwards [Filter.eventually_ge_atTop d] with t ht
  exact hvalue t ht

/-- On a noetherian affine projective line, relation-kernel `H¹`-vanishing
supplies the exact relation-generation epimorphism.  Finite local freeness of
the coefficient kernel and the other saturation fields are discharged by the
projective-line API. -/
theorem
    twistedFreeQuotNextDegreeRelationGeneration_line_of_relationKernelRegularity
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (q : ℕ) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of R)).Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u]
    (hE : IsProjectiveOfRank q E)
    (hrelation : TwistedFreeQuotNextDegreeRelationKernelRegularity
      1 (Spec (.of R)) l r P d e he u) :
    TwistedFreeQuotNextDegreeRelationGeneration
      1 (Spec (.of R)) l r P d e he u := by
  intro hfamily
  exact
    (Scheme.twistedFreeNextDegreeReconstructionSaturation_of_projectiveOfRank_line_vanishing
      R q l r d e he u hE (hrelation hfamily)).relationKernelLift_epi

/-- Forward regularity and reverse Gotzmann persistence assemble to the exact
pointwise next-degree rank equivalence. -/
theorem twistedFreeQuotNextDegreeRankIffFlatHilbert_of_regularity_and_persistence
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hregularity : TwistedFreeQuotNextDegreeFlatHilbertRegularity
      n T l r P d e he u)
    (hpersistence : TwistedFreeQuotNextDegreeGotzmannPersistence
      n T l r P d e he u) :
    TwistedFreeQuotNextDegreeRankIffFlatHilbert
      n T l r P d e he u := by
  constructor
  · exact hpersistence hE
  · intro hfamily
    obtain ⟨hsaturation, hpush⟩ := hregularity hE hfamily
    exact (twistedFreeNextDegreeModule_isProjectiveOfRank_iff_pushforward
      n T l r d e (P.hilbertNatValue (d + 1)) he u hsaturation).2 hpush

/-- On the projective line, adjacent base change and the two geometric seed
ranks imply reverse Gotzmann persistence.  The proof uses neither base-change
coherence for multiplication nor epimorphy of multiplication. -/
theorem
    TwistedFreeQuotNextDegreeGotzmannPersistence.of_geometricSeedRanks_adjacent_one
    (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u]
    (hld : l ≤ (d : ℤ)) (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (C : ProjectiveOneStepAdjacentBaseChangeComparison 1
      (reconstructedQuotient' 1 T l r d e he u) d)
    (hseeds : TwistedFreeQuotNextDegreeGeometricSeedRanks
      1 T l r P d e he u) :
    TwistedFreeQuotNextDegreeGotzmannPersistence
      1 T l r P d e he u := by
  intro hE hnext
  let Q := reconstructedQuotient' 1 T l r d e he u
  let p := reconstructedQuotientMap' 1 T l r d e he u
  haveI hQqc : Q.IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent 1 T l r d e he u
  haveI hp : Epi p := by
    dsimp only [p]
    infer_instance
  have hK := Scheme.twistedFreeMonomialQuotientMap_kernel_isFiniteLocallyFree
    1 T r e u hE.isFiniteLocallyFree
  letI hKqc : (kernel u).IsQuasicoherent := kernel_isQuasicoherent u
  haveI hQfp : Q.IsFinitePresentation :=
    reconstructedQuotient'_isFinitePresentation_of_kernel
      1 T l r d e he u hK.isFinitePresentation
  have h₀ : IsProjectiveOfRank (P.hilbertNatValue d)
      (projectiveTwistedPushforward 1 Q d) := hseeds.1 hE
  have h₁ : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (projectiveTwistedPushforward 1 Q (d + 1)) := hseeds.2 hnext
  exact ⟨C.flatOver_one p (by omega) h₀ h₁,
    C.hasFiberwiseHilbertPolynomial_one p P hld hPdeg hPd hPsucc h₀ h₁⟩

/-- On the projective line, algebraic-to-geometric seed-rank transfer after every affine
base change already implies reverse Gotzmann persistence.  The Čech flatness argument
uses noncanonical equal-rank isomorphisms on residue-field fibres, so neither canonical
base-change epimorphy nor any multiplication comparison is required. -/
theorem
    TwistedFreeQuotNextDegreeGotzmannPersistence.of_affineStableGeometricSeedRanks_one
    (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u]
    (hld : l ≤ (d : ℤ)) (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (hseeds : TwistedFreeQuotNextDegreeGeometricSeedRanksUnderAffineBaseChange
      1 T l r P d e he u) :
    TwistedFreeQuotNextDegreeGotzmannPersistence
      1 T l r P d e he u := by
  intro hE hnext
  let Q := reconstructedQuotient' 1 T l r d e he u
  let p := reconstructedQuotientMap' 1 T l r d e he u
  haveI hQqc : Q.IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent 1 T l r d e he u
  haveI hp : Epi p := by
    dsimp only [p]
    infer_instance
  have hK := Scheme.twistedFreeMonomialQuotientMap_kernel_isFiniteLocallyFree
    1 T r e u hE.isFiniteLocallyFree
  letI hKqc : (kernel u).IsQuasicoherent := kernel_isQuasicoherent u
  haveI hQfp : Q.IsFinitePresentation :=
    reconstructedQuotient'_isFinitePresentation_of_kernel
      1 T l r d e he u hK.isFinitePresentation
  have h₀ : ∀ (A : Over T) [IsAffine A.left],
      IsProjectiveOfRank (P.hilbertNatValue d)
        (projectiveTwistedPushforward 1 (projectiveFamilyAt 1 Q A) d) :=
    fun A ↦ hseeds.degree_familyAt hE A
  have h₁ : ∀ (A : Over T) [IsAffine A.left],
      IsProjectiveOfRank (P.hilbertNatValue (d + 1))
        (projectiveTwistedPushforward 1
          (projectiveFamilyAt 1 Q A) (d + 1)) :=
    fun A ↦ hseeds.degreeSucc_familyAt hE hnext A
  exact ⟨flatOver_one_of_familyAt_pushforward_ranks p (by omega) h₀ h₁,
    hasFiberwiseHilbertPolynomial_one_of_familyAt_pushforward_ranks
      p P hld hPdeg hPd hPsucc h₀ h₁⟩

/-- Stable seed-rank transfer under arbitrary base change implies the affine-stable
version, and hence reverse Gotzmann persistence on the projective line. -/
theorem
    TwistedFreeQuotNextDegreeGotzmannPersistence.of_stableGeometricSeedRanks_one
    (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u]
    (hld : l ≤ (d : ℤ)) (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (hseeds : TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange
      1 T l r P d e he u) :
    TwistedFreeQuotNextDegreeGotzmannPersistence
      1 T l r P d e he u :=
  TwistedFreeQuotNextDegreeGotzmannPersistence.of_affineStableGeometricSeedRanks_one
    T l r P d e he u hld hPdeg hPd hPsucc hseeds.affine

/-- On the projective line, the existing field-growth and Čech-flatness
theorems turn the two geometric seed ranks into the reverse Gotzmann
implication.  A multiplication-compatible package is accepted for backwards
compatibility, but its coherence field is not used. -/
theorem
    TwistedFreeQuotNextDegreeGotzmannPersistence.of_geometricSeedRanks_one
    (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u]
    (hld : l ≤ (d : ℤ)) (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison 1
      (reconstructedQuotient' 1 T l r d e he u) d)
    (hseeds : TwistedFreeQuotNextDegreeGeometricSeedRanks
      1 T l r P d e he u) :
    TwistedFreeQuotNextDegreeGotzmannPersistence
      1 T l r P d e he u :=
  TwistedFreeQuotNextDegreeGotzmannPersistence.of_geometricSeedRanks_adjacent_one
    T l r P d e he u hld hPdeg hPd hPsucc
      (ProjectiveOneStepAdjacentBaseChangeComparison.ofMultiplication C) hseeds

/-- The named residual canonical comparison package supplies all of reverse
Gotzmann persistence on the projective line. -/
theorem
    TwistedFreeQuotNextDegreeGotzmannPersistence.of_canonicalSeedData_one
    (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u]
    (hld : l ≤ (d : ℤ)) (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (D : TwistedFreeQuotNextDegreeCanonicalSeedData
      1 T l r P d e he u) :
    TwistedFreeQuotNextDegreeGotzmannPersistence
      1 T l r P d e he u :=
  TwistedFreeQuotNextDegreeGotzmannPersistence.of_geometricSeedRanks_adjacent_one
    T l r P d e he u hld hPdeg hPd hPsucc
      D.adjacentBaseChangeComparison D.seedRanks

/-- On the projective line, stable algebraic-to-geometric seed-rank transfer and
epimorphy of the two canonical base-change maps imply reverse Gotzmann persistence.
The epimorphism fields are stronger than necessary for this conclusion. -/
theorem
    TwistedFreeQuotNextDegreeGotzmannPersistence.of_epimorphicStableSeedData_one
    (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u]
    (hld : l ≤ (d : ℤ)) (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (D : TwistedFreeQuotNextDegreeEpimorphicStableSeedData
      1 T l r P d e he u) :
    TwistedFreeQuotNextDegreeGotzmannPersistence
      1 T l r P d e he u :=
  TwistedFreeQuotNextDegreeGotzmannPersistence.of_stableGeometricSeedRanks_one
    T l r P d e he u hld hPdeg hPd hPsucc D.seedRanksUnderBaseChange

/-- Projective-line forward regularity, algebraic-to-geometric seed-rank
transfer, and the one-step base-change comparison give the full pointwise rank
equivalence.  All Hilbert-function and relative-flatness persistence is
discharged by the existing dimension-one API. -/
theorem
    twistedFreeQuotNextDegreeRankIffFlatHilbert_of_regularity_and_geometricSeedRanks_one
    (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u]
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hregularity : TwistedFreeQuotNextDegreeFlatHilbertRegularity
      1 T l r P d e he u)
    (hld : l ≤ (d : ℤ)) (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison 1
      (reconstructedQuotient' 1 T l r d e he u) d)
    (hseeds : TwistedFreeQuotNextDegreeGeometricSeedRanks
      1 T l r P d e he u) :
    TwistedFreeQuotNextDegreeRankIffFlatHilbert
      1 T l r P d e he u :=
  twistedFreeQuotNextDegreeRankIffFlatHilbert_of_regularity_and_persistence
    1 T l r P d e he u hE hregularity
      (TwistedFreeQuotNextDegreeGotzmannPersistence.of_geometricSeedRanks_one
        T l r P d e he u hld hPdeg hPd hPsucc C hseeds)

/-- Forward regularity and affine-stable algebraic-to-geometric seed-rank transfer give
the full projective-line pointwise rank equivalence.  No base-change-map hypothesis occurs
in the reverse implication. -/
theorem
    twistedFreeQuotNextDegreeRankIffFlatHilbert_of_regularity_and_affineStableGeometricSeedRanks_one
    (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u]
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hregularity : TwistedFreeQuotNextDegreeFlatHilbertRegularity
      1 T l r P d e he u)
    (hld : l ≤ (d : ℤ)) (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (hseeds : TwistedFreeQuotNextDegreeGeometricSeedRanksUnderAffineBaseChange
      1 T l r P d e he u) :
    TwistedFreeQuotNextDegreeRankIffFlatHilbert
      1 T l r P d e he u :=
  twistedFreeQuotNextDegreeRankIffFlatHilbert_of_regularity_and_persistence
    1 T l r P d e he u hE hregularity
      (TwistedFreeQuotNextDegreeGotzmannPersistence.of_affineStableGeometricSeedRanks_one
        T l r P d e he u hld hPdeg hPd hPsucc hseeds)

/-- Stable seed-rank transfer under arbitrary base change implies the affine-stable
version, and hence the full projective-line pointwise rank equivalence. -/
theorem
    twistedFreeQuotNextDegreeRankIffFlatHilbert_of_regularity_and_stableGeometricSeedRanks_one
    (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u]
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hregularity : TwistedFreeQuotNextDegreeFlatHilbertRegularity
      1 T l r P d e he u)
    (hld : l ≤ (d : ℤ)) (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (hseeds : TwistedFreeQuotNextDegreeGeometricSeedRanksUnderBaseChange
      1 T l r P d e he u) :
    TwistedFreeQuotNextDegreeRankIffFlatHilbert
      1 T l r P d e he u :=
  twistedFreeQuotNextDegreeRankIffFlatHilbert_of_regularity_and_affineStableGeometricSeedRanks_one
    T l r P d e he u hE hregularity hld hPdeg hPd hPsucc hseeds.affine

/-- Forward regularity and the exact canonical seed package give the full
projective-line pointwise rank equivalence. -/
theorem
    twistedFreeQuotNextDegreeRankIffFlatHilbert_of_regularity_and_canonicalSeedData_one
    (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u]
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hregularity : TwistedFreeQuotNextDegreeFlatHilbertRegularity
      1 T l r P d e he u)
    (hld : l ≤ (d : ℤ)) (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (D : TwistedFreeQuotNextDegreeCanonicalSeedData
      1 T l r P d e he u) :
    TwistedFreeQuotNextDegreeRankIffFlatHilbert
      1 T l r P d e he u :=
  twistedFreeQuotNextDegreeRankIffFlatHilbert_of_regularity_and_persistence
    1 T l r P d e he u hE hregularity
      (TwistedFreeQuotNextDegreeGotzmannPersistence.of_canonicalSeedData_one
        T l r P d e he u hld hPdeg hPd hPsucc D)

/-- Forward regularity and the epimorphic stable seed package give the full
projective-line pointwise rank equivalence. -/
theorem
    twistedFreeQuotNextDegreeRankIffFlatHilbert_of_regularity_and_epimorphicStableSeedData_one
    (T : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u]
    (hE : IsProjectiveOfRank (P.hilbertNatValue d) E)
    (hregularity : TwistedFreeQuotNextDegreeFlatHilbertRegularity
      1 T l r P d e he u)
    (hld : l ≤ (d : ℤ)) (hPdeg : P.natDegree ≤ 1)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (D : TwistedFreeQuotNextDegreeEpimorphicStableSeedData
      1 T l r P d e he u) :
    TwistedFreeQuotNextDegreeRankIffFlatHilbert
      1 T l r P d e he u :=
  twistedFreeQuotNextDegreeRankIffFlatHilbert_of_regularity_and_persistence
    1 T l r P d e he u hE hregularity
      (TwistedFreeQuotNextDegreeGotzmannPersistence.of_epimorphicStableSeedData_one
        T l r P d e he u hld hPdeg hPd hPsucc D)

/-- On a noetherian affine projective line, the existing global-generation and
uniform pushforward-rank theorems reduce forward regularity to the literal
relation-generation field of next-degree saturation.  This is weaker than
assuming a cohomology vanishing which implies that epimorphism. -/
theorem
    exists_bound_twistedFreeQuotNextDegreeFlatHilbertRegularity_line_of_relationGeneration
    (r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀
      (R : Type u) [CommRing R] [IsNoetherianRing R]
      (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
      (E : (Spec (.of R)).Modules) [E.IsQuasicoherent]
      (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u],
      d₀ ≤ ((d + 1 : ℕ) : ℤ) →
      TwistedFreeQuotNextDegreeRelationGeneration
          1 (Spec (.of R)) l r P d e he u →
        TwistedFreeQuotNextDegreeFlatHilbertRegularity
          1 (Spec (.of R)) l r P d e he u := by
  obtain ⟨d₀, hd₀, hpush⟩ :=
    AlgebraicGeometry.Scheme.exists_bound_reconstructedQuotient_pushforward_isProjectiveOfRank
      1 r l P
  refine ⟨d₀, hd₀, ?_⟩
  intro R _ _ d e he E hEqc u hu hd hrelation hE hfamily
  have hmonomial : Epi (quotGrassmannianFreeMap 1 (Spec (.of R)) l r
      (reconstructedQuotientMap' 1 (Spec (.of R)) l r d e he u)
      (d + 1) (e + 1) (by omega)) :=
    Scheme.reconstructedNextDegreePushforwardMap_epi_of_finiteLocallyFree_line
      R l r d e he u hE.isFiniteLocallyFree
  have hsaturation : TwistedFreeNextDegreeReconstructionSaturation
      1 (Spec (.of R)) l r d e he u :=
    ⟨hmonomial, hrelation hfamily⟩
  have hnextPush : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (projectiveTwistedPushforward 1
        (reconstructedQuotient' 1 (Spec (.of R)) l r d e he u)
        (d + 1)) :=
    hpush (Spec (.of R)) d e he E u hfamily.1 hfamily.2 (d + 1) hd
  exact ⟨hsaturation, hnextPush⟩

/-- Consequently, on a noetherian affine projective line the full pointwise
rank equivalence follows from the exact relation-generation epimorphism in the
forward direction and algebraic Gotzmann persistence in the reverse direction. -/
theorem
    exists_bound_twistedFreeQuotNextDegreeRankIffFlatHilbert_line_of_relationGeneration
    (r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀
      (R : Type u) [CommRing R] [IsNoetherianRing R]
      (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
      (E : (Spec (.of R)).Modules) [E.IsQuasicoherent]
      (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u],
      d₀ ≤ ((d + 1 : ℕ) : ℤ) →
      TwistedFreeQuotNextDegreeRelationGeneration
          1 (Spec (.of R)) l r P d e he u →
      TwistedFreeQuotNextDegreeGotzmannPersistence
          1 (Spec (.of R)) l r P d e he u →
      IsProjectiveOfRank (P.hilbertNatValue d) E →
        TwistedFreeQuotNextDegreeRankIffFlatHilbert
          1 (Spec (.of R)) l r P d e he u := by
  obtain ⟨d₀, hd₀, hregularity⟩ :=
    exists_bound_twistedFreeQuotNextDegreeFlatHilbertRegularity_line_of_relationGeneration
      r l P
  refine ⟨d₀, hd₀, ?_⟩
  intro R _ _ d e he E hEqc u hu hd hrelation hpersistence hE
  exact twistedFreeQuotNextDegreeRankIffFlatHilbert_of_regularity_and_persistence
    1 (Spec (.of R)) l r P d e he u hE
      (hregularity R d e he E u hd hrelation) hpersistence

/-- On a noetherian affine projective line, the existing saturation and uniform
pushforward-rank theorems prove the forward regularity package from precisely
the relation-kernel `H¹` condition.  No Gotzmann persistence is used here. -/
theorem
    exists_bound_twistedFreeQuotNextDegreeFlatHilbertRegularity_line_of_relationKernel
    (r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀
      (R : Type u) [CommRing R] [IsNoetherianRing R]
      (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
      (E : (Spec (.of R)).Modules) [E.IsQuasicoherent]
      (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u],
      d₀ ≤ ((d + 1 : ℕ) : ℤ) →
      TwistedFreeQuotNextDegreeRelationKernelRegularity
          1 (Spec (.of R)) l r P d e he u →
        TwistedFreeQuotNextDegreeFlatHilbertRegularity
          1 (Spec (.of R)) l r P d e he u := by
  obtain ⟨d₀, hd₀, hpush⟩ :=
    AlgebraicGeometry.Scheme.exists_bound_reconstructedQuotient_pushforward_isProjectiveOfRank
      1 r l P
  refine ⟨d₀, hd₀, ?_⟩
  intro R _ _ d e he E hEqc u hu hd hrelation hE hfamily
  have hsaturation : TwistedFreeNextDegreeReconstructionSaturation
      1 (Spec (.of R)) l r d e he u :=
    Scheme.twistedFreeNextDegreeReconstructionSaturation_of_projectiveOfRank_line_vanishing
      R (P.hilbertNatValue d) l r d e he u hE (hrelation hfamily)
  have hnextPush : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (projectiveTwistedPushforward 1
        (reconstructedQuotient' 1 (Spec (.of R)) l r d e he u)
        (d + 1)) :=
    hpush (Spec (.of R)) d e he E u hfamily.1 hfamily.2 (d + 1) hd
  exact ⟨hsaturation, hnextPush⟩

/-- Consequently, on a noetherian affine projective line the full pointwise
rank equivalence follows from exactly two named inputs: relation-kernel
regularity in the forward direction and algebraic Gotzmann persistence in the
reverse direction. -/
theorem
    exists_bound_twistedFreeQuotNextDegreeRankIffFlatHilbert_line_of_relationKernel_and_persistence
    (r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀
      (R : Type u) [CommRing R] [IsNoetherianRing R]
      (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
      (E : (Spec (.of R)).Modules) [E.IsQuasicoherent]
      (u : SheafOfModules.free (R := (Spec (.of R)).ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u],
      d₀ ≤ ((d + 1 : ℕ) : ℤ) →
      TwistedFreeQuotNextDegreeRelationKernelRegularity
          1 (Spec (.of R)) l r P d e he u →
      TwistedFreeQuotNextDegreeGotzmannPersistence
          1 (Spec (.of R)) l r P d e he u →
      IsProjectiveOfRank (P.hilbertNatValue d) E →
        TwistedFreeQuotNextDegreeRankIffFlatHilbert
          1 (Spec (.of R)) l r P d e he u := by
  obtain ⟨d₀, hd₀, hregularity⟩ :=
    exists_bound_twistedFreeQuotNextDegreeFlatHilbertRegularity_line_of_relationKernel
      r l P
  refine ⟨d₀, hd₀, ?_⟩
  intro R _ _ d e he E hEqc u hu hd hrelation hpersistence hE
  exact twistedFreeQuotNextDegreeRankIffFlatHilbert_of_regularity_and_persistence
    1 (Spec (.of R)) l r P d e he u hE
      (hregularity R d e he E u hd hrelation) hpersistence

/-- The pointwise Gotzmann assertion is Zariski-local on the base: it is enough to prove
it for epimorphic finite-locally-free quotients over affine schemes. -/
theorem twistedFreeQuotNextDegreeRankIffFlatHilbert_of_affine
    (n q : ℕ) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (haffine : ∀ (T : Scheme.{u}) [IsAffine T] (E : T.Modules)
      [E.IsQuasicoherent]
      (u : SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) [Epi u],
      IsProjectiveOfRank q E →
        TwistedFreeQuotNextDegreeRankIffFlatHilbert
          n T l r P d e he u)
    (T : Scheme.{u}) (E : T.Modules) [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) [Epi u]
    (hE : IsProjectiveOfRank q E) :
    TwistedFreeQuotNextDegreeRankIffFlatHilbert
      n T l r P d e he u := by
  let C := twistedFreeNextDegreeModule n T r e u
  let Q := reconstructedQuotient' n T l r d e he u
  letI hCqc : C.IsQuasicoherent :=
    twistedFreeNextDegreeModule_isQuasicoherent n T r e u
  letI hQqc : Q.IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent n T l r d e he u
  constructor
  · intro hnext
    have hlocal (X : Scheme.{u}) [IsAffine X] (g : X ⟶ T) :
        let QX := (pullback (projectiveSpaceOverMap n g)).obj Q
        QX.FlatOver (projectiveSpaceOverπ n X) ∧
          HasFiberwiseHilbertPolynomial QX P := by
      dsimp only
      let EX := (pullback g).obj E
      let uX := pullbackFreeQuotientMap g u
      letI hEXqc : EX.IsQuasicoherent := inferInstance
      letI huX : Epi uX := by
        letI : Epi ((pullback g).map u) := inferInstance
        letI : Epi
            (pullbackFreeIso g
              (ULift.{u} (Fin r) × Fin ((n + e).choose n))).inv :=
          inferInstance
        dsimp only [uX, pullbackFreeQuotientMap]
        exact epi_comp _ _
      have hEX : IsProjectiveOfRank q EX := hE.pullback g
      let EC := twistedFreeNextDegreeModulePullbackIso
        n g r e u hE.isFiniteLocallyFree
      have hnextX : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
          (twistedFreeNextDegreeModule n X r e uX) :=
        (hnext.pullback g).of_iso EC
      have hdirect := (haffine X EX uX hEX).mp hnextX
      let EQ := reconstructedQuotient'PullbackIso n l r d e he
        g u hE.isFiniteLocallyFree
          (twistedFreeAmbientReconstructionCompatibility n T l r d e he)
          (twistedFreeAmbientReconstructionCompatibility n X l r d e he)
      exact ⟨FlatOver.of_iso EQ.symm hdirect.1,
        HasFiberwiseHilbertPolynomial.of_iso EQ.symm hdirect.2⟩
    have hflat : Q.FlatOver (projectiveSpaceOverπ n T) :=
      FlatOver.of_affineCover_projectiveSpace (Q := Q) fun i ↦
        (hlocal (T.affineCover.X i) (T.affineCover.f i)).1
    have hP : HasFiberwiseHilbertPolynomial Q P :=
      HasFiberwiseHilbertPolynomial.of_affineOpen_pullbacks fun U ↦ by
        letI : IsAffine U.1.toScheme := U.2
        exact (hlocal U.1.toScheme U.1.ι).2
    exact ⟨hflat, hP⟩
  · rintro ⟨hflat, hP⟩
    apply IsProjectiveOfRank.of_affineOpen_pullbacks
    intro U
    letI : IsAffine U.1.toScheme := U.2
    let g := U.1.ι
    let EX := (pullback g).obj E
    let uX := pullbackFreeQuotientMap g u
    letI hEXqc : EX.IsQuasicoherent := inferInstance
    letI huX : Epi uX := by
      letI : Epi ((pullback g).map u) := inferInstance
      letI : Epi
          (pullbackFreeIso g
            (ULift.{u} (Fin r) × Fin ((n + e).choose n))).inv :=
        inferInstance
      dsimp only [uX, pullbackFreeQuotientMap]
      exact epi_comp _ _
    have hEX : IsProjectiveOfRank q EX := hE.pullback g
    let EQ := reconstructedQuotient'PullbackIso n l r d e he
      g u hE.isFiniteLocallyFree
        (twistedFreeAmbientReconstructionCompatibility n T l r d e he)
        (twistedFreeAmbientReconstructionCompatibility
          n U.1.toScheme l r d e he)
    have hflatX : (reconstructedQuotient'
        n U.1.toScheme l r d e he uX).FlatOver
        (projectiveSpaceOverπ n U.1.toScheme) := by
      apply FlatOver.of_iso EQ
      exact FlatOver.pullback_of_isPullback
        (projectiveSpaceOverMap n g)
        (projectiveSpaceOverπ n U.1.toScheme)
        (projectiveSpaceOverπ n T) g
        (isPullback_projectiveSpaceOverMap n g).flip Q hflat
    have hPX : HasFiberwiseHilbertPolynomial
        (reconstructedQuotient' n U.1.toScheme l r d e he uX) P :=
      HasFiberwiseHilbertPolynomial.of_iso EQ
        (HasFiberwiseHilbertPolynomial.pullback g hP)
    have hnextX : IsProjectiveOfRank (P.hilbertNatValue (d + 1))
        (twistedFreeNextDegreeModule n U.1.toScheme r e uX) :=
      (haffine U.1.toScheme EX uX hEX).mpr ⟨hflatX, hPX⟩
    let EC := twistedFreeNextDegreeModulePullbackIso
      n g r e u hE.isFiniteLocallyFree
    exact hnextX.of_iso EC.symm

end Modules

namespace TwistedFreeQuotUniversalNextDegreeFlatteningData

variable {S : Scheme.{u}} {n r m q : ℕ} {l : ℤ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
  {σ : ULift.{u} (Fin m) ≃
    ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- A pointwise Gotzmann theorem for arbitrary finite-locally-free quotients supplies the
universal next-degree flattening equivalence.

The proof only normalizes the pulled tautological quotient and transports flatness and
the fibrewise Hilbert polynomial across the reconstruction base-change isomorphism. -/
theorem ofPointwise
    (hpointwise : ∀ (T : Scheme.{u}) (E : T.Modules) [E.IsQuasicoherent]
      (u : SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) [Epi u],
      Modules.IsProjectiveOfRank q E →
        Modules.TwistedFreeQuotNextDegreeRankIffFlatHilbert
          n T l r P d e he u) :
    TwistedFreeQuotUniversalNextDegreeFlatteningData
      S n r q m l P d e he σ where
  rank_iff A := by
    let G := grassmannianOverRepresentation S q m
    let x := grassmannianPointFreeQuotient (q := q) G
      (freeGrassmannianUniversalPoint S q m)
    let u₀ := grassmannianPointMonomialQuotientMap
      (n := n) (r := r) (q := q) (e := e) (σ := σ) G
      (freeGrassmannianUniversalPoint S q m)
    let E := (Modules.pullback A.hom).obj x.Q
    let u := pullbackFreeQuotientMap A.hom u₀
    letI hxqc : x.Q.IsQuasicoherent := x.isQuasicoherent
    let f := SheafOfModules.freeMap (R := G.left.ringCatSheaf) σ.symm
    letI hfiso : IsIso f := Modules.freeMap_isIso_of_equiv σ.symm
    letI hxu₀ : Epi u₀ := by
      dsimp only [u₀, grassmannianPointMonomialQuotientMap, f, x]
      letI : Epi (grassmannianPointFreeQuotient (q := q) G
        (freeGrassmannianUniversalPoint S q m)).π :=
          (grassmannianPointFreeQuotient (q := q) G
            (freeGrassmannianUniversalPoint S q m)).epi
      infer_instance
    letI hEqc : E.IsQuasicoherent := inferInstance
    letI hu : Epi u := by
      letI : Epi ((Modules.pullback A.hom).map u₀) := inferInstance
      letI : Epi
          (Modules.pullbackFreeIso A.hom
            (ULift.{u} (Fin r) × Fin ((n + e).choose n))).inv :=
        inferInstance
      dsimp only [u, pullbackFreeQuotientMap]
      exact epi_comp _ _
    have hE : Modules.IsProjectiveOfRank q E :=
      x.isProjectiveOfRank.pullback A.hom
    let EQ := reconstructedQuotient'PullbackIso n l r d e he
      A.hom u₀ x.isProjectiveOfRank.isFiniteLocallyFree
        (twistedFreeAmbientReconstructionCompatibility n G.left l r d e he)
        (twistedFreeAmbientReconstructionCompatibility n A.left l r d e he)
    have h := hpointwise A.left E u hE
    constructor
    · intro hnext
      have hdirect := h.mp hnext
      exact ⟨Modules.FlatOver.of_iso EQ.symm hdirect.1,
        HasFiberwiseHilbertPolynomial.of_iso EQ.symm hdirect.2⟩
    · rintro ⟨hflat, hP⟩
      apply h.mpr
      exact ⟨Modules.FlatOver.of_iso EQ hflat,
        HasFiberwiseHilbertPolynomial.of_iso EQ hP⟩

/-- An affine pointwise Gotzmann theorem supplies the universal next-degree flattening
equivalence.  This is the smallest scheme-theoretic input: all non-affine descent,
universal-Grassmannian normalization, and reconstruction base change are discharged by
the two reduction theorems in this file. -/
theorem ofAffinePointwise
    (haffine : ∀ (T : Scheme.{u}) [IsAffine T] (E : T.Modules)
      [E.IsQuasicoherent]
      (u : SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) [Epi u],
      Modules.IsProjectiveOfRank q E →
        Modules.TwistedFreeQuotNextDegreeRankIffFlatHilbert
          n T l r P d e he u) :
    TwistedFreeQuotUniversalNextDegreeFlatteningData
      S n r q m l P d e he σ :=
  ofPointwise fun T E _ u _ hE ↦
    Modules.twistedFreeQuotNextDegreeRankIffFlatHilbert_of_affine
      n q l r P d e he haffine T E u hE

end TwistedFreeQuotUniversalNextDegreeFlatteningData

end AlgebraicGeometry.Scheme

end

end
