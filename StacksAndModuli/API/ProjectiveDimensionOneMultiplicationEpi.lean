module

public import StacksAndModuli.API.AffineQuasicoherentEpi
public import StacksAndModuli.API.ProjectiveDimensionOneQuotientRegularity
public import StacksAndModuli.API.ProjectiveGammaStarMultiplicationComparison
public import StacksAndModuli.API.ProjectiveOneStepResidueMultiplicationEpi
public import StacksAndModuli.API.QuasicoherentFiniteCoproduct
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalFlatteningFiniteness

/-!
# Degree-one multiplication for quotients on the projective line

This file converts the dimension-one regularity model of a twisted-free quotient into
epimorphy of the concrete degree-one multiplication map on its twisted pushforwards.  The
proof passes through the kernel-route graded model, its degree-zero Cech cohomology, and the
direct comparison with `Proj.gammaStar`.

Main declarations:

* `Scheme.Modules.projectiveTwistedPushforwardMul_epi_of_twistedFreeQuotient_of_dimension_le_one`
  proves the field case from the dimension-one regularity model.
* In `Scheme.Modules.ProjectiveOneStepMultiplicationBaseChangeComparison`,
  `multiplication_epi_familyAt_of_twistedFreeQuotient_of_dimension_le_one` lifts the field
  case over an arbitrary base by the residue-field criterion.
* `Scheme.twistedFreeQuotUniversal_multiplicationEpi_of_dimension_le_one` packages the
  result in the exact form of the universal Quot-family `multiplicationEpi` hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.ProjectiveSpace
open ProjectiveSpectrum.Twist

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Over a field, degree-one multiplication on the twisted pushforwards of a
twisted-free quotient is epic in every degree at least the source twist, when the
projective dimension is positive and at most one. -/
theorem projectiveTwistedPushforwardMul_epi_of_twistedFreeQuotient_of_dimension_le_one
    (n r : ℕ) (hn : 0 < n) (hn₁ : n ≤ 1)
    (K : CommRingCat.{u}) (hK : IsField K) (l : ℤ) (d : ℕ)
    (hld : l ≤ (d : ℤ))
    (Q : (Scheme.projectiveSpaceOver n (Spec K)).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec K) (-l)) ⟶ Q)
    [Epi q] :
    Epi (projectiveTwistedPushforwardMul n Q d) := by
  letI : Field K := hK.toField
  let E := ProjectiveSpace.projAmbient n r l (R := K)
  let G := (pullback (projectiveSpaceOverSpecIso n K).inv).obj Q
  let p := (pullback (projectiveSpaceOverSpecIso n K).inv).map q
  let M := Proj.kernelQuotientModule
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (projSpecπ n K) (stdVars n K) p
  haveI hp : Epi p := inferInstance
  haveI hAmbientFp : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec K) (-l)).IsFinitePresentation :=
    Scheme.twistedFreeAmbient_isFinitePresentation n (Spec K) l r
  haveI hEfp : E.IsFinitePresentation :=
    isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hGfp : G.IsFinitePresentation :=
    isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hEqc : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) E a).IsQuasicoherent :=
    fun a ↦ twistModule_std_isQuasicoherent _ a
  haveI hGqc : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) G a).IsQuasicoherent :=
    fun a ↦ twistModule_std_isQuasicoherent _ a
  haveI hKqc : (kernel p).IsQuasicoherent := kernel_isQuasicoherent p
  haveI hKtwistQc : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (kernel p) a).IsQuasicoherent :=
    fun a ↦ twistModule_std_isQuasicoherent_of_isQuasicoherent n _ a
  let D := fieldRegularityModelOfIsField_of_twistedFreeQuotient_of_dimension_le_one
    n r hn hn₁ K hK l d hld Q q
  have hMspan : (M.cechHgr 0).mulSpan (d : ℤ) ((d + 1 : ℕ) : ℤ) = ⊤ := by
    change (D.C.Hgr D.M 0).mulSpan (d : ℤ) ((d + 1 : ℕ) : ℤ) = ⊤
    exact D.C.mulSpan_eq_top_of_field D.coherent D.infiniteBaseChange D.regular
      le_rfl (by omega)
  let f := GradedModule.cechHgrMap
    (Proj.kernelQuotientToGammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (projSpecπ n K) (stdVars n K) p) 0
  have hCechSpan : ((Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (projSpecπ n K) G (stdVars n K)).cechHgr 0).mulSpan
        (d : ℤ) ((d + 1 : ℕ) : ℤ) = ⊤ := by
    apply GradedModule.mulSpan_eq_top_of_surjective f (fun e ↦ ?_)
      (d : ℤ) ((d + 1 : ℕ) : ℤ) hMspan
    haveI := Proj.isIso_cechHgrMap_kernelQuotientToGammaStar_all
      (projSpecπ n K) p 0 e
    exact (ModuleCat.epi_iff_surjective (f.app e)).mp inferInstance
  have hGammaSpan : (Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (projSpecπ n K) G (stdVars n K)).mulSpan
        (d : ℤ) ((d + 1 : ℕ) : ℤ) = ⊤ := by
    apply GradedModule.mulSpan_eq_top_of_cechHgrZero_of_bijective_cechAug
    · exact ProjectiveSpace.bijective_gammaStar_cechAug_of_isFinitePresentation
        (projSpecπ n K) G (d : ℤ)
    · exact ProjectiveSpace.bijective_gammaStar_cechAug_of_isFinitePresentation
        (projSpecπ n K) G ((d + 1 : ℕ) : ℤ)
    · exact hCechSpan
  letI : (∐ fun _ : Fin ((n + 1).choose n) ↦
      projectiveTwistedPushforward n Q d).IsQuasicoherent :=
    isQuasicoherent_coproduct_small _
  apply epi_of_appTop_surjective
  exact ProjectiveSpace.surjective_app_top_projectiveTwistedPushforwardMul_of_gammaStar_mulSpan
    Q d hGammaSpan

namespace ProjectiveOneStepMultiplicationBaseChangeComparison

/-- A one-step base-change comparison lifts the preceding field theorem to an
arbitrary intermediate base, provided the target twisted pushforward is a vector bundle.
Thus the only non-field input needed for multiplication epimorphy is local freeness of the
degree-`d+1` target. -/
theorem multiplication_epi_familyAt_of_twistedFreeQuotient_of_dimension_le_one
    {T : Scheme.{u}} {n r d : ℕ} (hn : 0 < n) (hn₁ : n ≤ 1)
    {l : ℤ} (hld : l ≤ (d : ℤ))
    {Q : (Scheme.projectiveSpaceOver n T).Modules}
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi q]
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison n Q d)
    (A : Over T) {q₁ : ℕ}
    (hTarget : IsProjectiveOfRank q₁
      (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) (d + 1))) :
    Epi (projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d) := by
  apply C.multiplication_epi_familyAt_of_field A hTarget
  intro K hK s
  let B : Over A.left := Over.mk s
  let AB : Over T := (Over.map A.hom).obj B
  let QAB := projectiveFamilyAt n Q AB
  haveI hQABfp : QAB.IsFinitePresentation :=
    isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  let qAB : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec K) (-l)) ⟶ QAB :=
    (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l AB.hom).inv ≫
      (pullback (Scheme.projectiveSpaceOverMap n AB.hom)).map q
  haveI hqAB : Epi qAB := epi_comp _ _
  change Epi (projectiveTwistedPushforwardMul n QAB d)
  exact projectiveTwistedPushforwardMul_epi_of_twistedFreeQuotient_of_dimension_le_one
    n r hn hn₁ K hK l d hld QAB qAB

end ProjectiveOneStepMultiplicationBaseChangeComparison

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

open Modules.QuotientPullbackData

/-- In positive projective dimension at most one, the adjacent canonical rank input and
the one-step base-change comparison supply multiplication epimorphy on every flat
fixed-polynomial pullback of the universal reconstructed quotient. -/
theorem twistedFreeQuotUniversal_multiplicationEpi_of_dimension_le_one
    (n : ℕ) (hn : 0 < n) (hn₁ : n ≤ 1)
    (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (C : Modules.ProjectiveOneStepMultiplicationBaseChangeComparison n
      (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) d)
    (I₁ : TwistedFreeQuotGrassmannianCanonicalInputs n S l r P
      (d + 1) (e + 1) (by omega)
      (r * (n + (e + 1)).choose n) (P.hilbertNatValue (d + 1))
      (twistedFreeMonomialIndexEquiv r ((n + (e + 1)).choose n))) :
    ∀ A : Over (grassmannianOverRepresentation S (P.hilbertNatValue d)
      (r * (n + e).choose n)).left,
      let QA := Modules.projectiveFamilyAt n
        (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) A
      QA.FlatOver (projectiveSpaceOverπ n A.left) ∧
          HasFiberwiseHilbertPolynomial QA P →
        Epi (Modules.projectiveTwistedPushforwardMul n QA d) := by
  intro A
  dsimp only
  intro hfamily
  let G := grassmannianOverRepresentation S
    (P.hilbertNatValue d) (r * (n + e).choose n)
  let T : Over S := (Over.map G.hom).obj A
  let Q := twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he
  let QA := Modules.projectiveFamilyAt n Q A
  let p := freeGrassmannianUniversalReconstructedQuotientMap S n r
    (P.hilbertNatValue d) (r * (n + e).choose n) l d e he
      (twistedFreeMonomialIndexEquiv r ((n + e).choose n))
  let pA : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n A.left (-l)) ⟶ QA :=
    (projectiveSpaceOverTwistedFree_pullbackIso n r l A.hom).inv ≫
      (Modules.pullback (projectiveSpaceOverMap n A.hom)).map p
  haveI hQfp : Q.IsFinitePresentation := by
    dsimp only [Q, twistedFreeQuotUniversalReconstructedQuotient]
    infer_instance
  haveI hQAqc : QA.IsQuasicoherent := by
    dsimp only [QA, Modules.projectiveFamilyAt]
    infer_instance
  haveI hQAfp : QA.IsFinitePresentation := by
    dsimp only [QA, Modules.projectiveFamilyAt]
    infer_instance
  haveI hp : Epi p := by
    dsimp only [p]
    infer_instance
  haveI hpA : Epi pA := by
    dsimp only [pA]
    infer_instance
  let b := Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace
    (n := n) (r := r) (l := l) T QA (by infer_instance) hfamily.1 pA
  let hPb :=
    ofTwistedFreeQuotientOnProjectiveSpace_hasFiberwiseHilbertPolynomial
      T QA (by infer_instance) hfamily.1 pA P hfamily.2
  let E := ofTwistedFreeQuotientOnProjectiveSpace_quotDataIso
    (n := n) (r := r) (l := l) T QA (by infer_instance) hfamily.1 pA
  let E₁ := (Modules.pushforward (projectiveSpaceOverπ n A.left)).mapIso
    (Modules.tensorLeftIso E
      (projectiveSpaceOverTwist n A.left ((d + 1 : ℕ) : ℤ)))
  have h₁ : Modules.IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (Modules.projectiveTwistedPushforward n QA (d + 1)) :=
    (I₁.isProjectiveOfRank T b hPb).of_iso E₁
  exact C.multiplication_epi_familyAt_of_twistedFreeQuotient_of_dimension_le_one
    hn hn₁ (by omega) p A h₁

end AlgebraicGeometry.Scheme

end

end
