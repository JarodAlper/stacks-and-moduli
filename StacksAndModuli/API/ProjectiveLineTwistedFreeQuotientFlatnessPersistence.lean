module

public import StacksAndModuli.API.ProjGammaStarEventuallyFlat
public import StacksAndModuli.API.ProjectiveDVRQuotientPullbackSerre
public import StacksAndModuli.API.ProjectiveLineTwistedFreeQuotientFlatTail
public import StacksAndModuli.API.ProjectiveOneStepIteratedBaseChange
public import StacksAndModuli.API.ProjectiveReconstructedGotzmannPersistence

/-!
# Relative flatness persistence for twisted-free quotients on the projective line

The affine projective-line calculation makes `Γ_*` eventually flat from two
finite-projective pushforward seeds and their residue-field base-change
comparisons.  This file applies that calculation on every affine open of an
arbitrary intermediate base.  A one-step multiplication base-change package
supplies both the rank transport to each affine chart and the two iterated
base-change comparisons needed over its residue fields.

Main declaration:

* `ProjectiveOneStepFlatnessPersistenceEpi.of_twistedFreeQuotient_one`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On the projective line, a twisted-free quotient and a one-step pushforward
base-change comparison make the two adjacent locally-free rank conditions imply
relative flatness.  The multiplication epimorphism in the persistence interface
is not needed for this implication. -/
theorem ProjectiveOneStepFlatnessPersistenceEpi.of_twistedFreeQuotient_one
    {T : Scheme.{u}} {r d : ℕ} {l : ℤ}
    {Q : (Scheme.projectiveSpaceOver 1 T).Modules}
    [Q.IsQuasicoherent] [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist 1 T (-l)) ⟶ Q)
    [Epi q] (hd : l - 1 ≤ (d : ℤ))
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison 1 Q d)
    (P : Polynomial ℚ) :
    ProjectiveOneStepFlatnessPersistenceEpi 1 Q P d := by
  intro A h₀ h₁ _hmul
  let QA := projectiveFamilyAt 1 Q A
  let qA : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist 1 A.left (-l)) ⟶ QA :=
    (Scheme.projectiveSpaceOverTwistedFree_pullbackIso 1 r l A.hom).inv ≫
      (pullback (Scheme.projectiveSpaceOverMap 1 A.hom)).map q
  haveI hQAqc : QA.IsQuasicoherent := by
    dsimp only [QA, projectiveFamilyAt]
    infer_instance
  haveI hQAfp : QA.IsFinitePresentation := by
    dsimp only [QA, projectiveFamilyAt]
    infer_instance
  haveI hqA : Epi qA := by
    dsimp only [qA]
    infer_instance
  apply ProjectiveSpace.flatOver_of_isFlatAbove_gammaStarPull_on_affineOpens
    1 A.left QA
  intro V
  let R : Type u := Γ(A.left, V.1)
  let B : Over A.left := Over.mk V.2.fromSpec
  let QV := projectiveFamilyAt 1 QA B
  let qV : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist 1 B.left (-l)) ⟶ QV :=
    (Scheme.projectiveSpaceOverTwistedFree_pullbackIso 1 r l B.hom).inv ≫
      (pullback (Scheme.projectiveSpaceOverMap 1 B.hom)).map qA
  haveI hQVqc : QV.IsQuasicoherent := by
    dsimp only [QV, projectiveFamilyAt]
    infer_instance
  haveI hQVfp : QV.IsFinitePresentation := by
    dsimp only [QV, projectiveFamilyAt]
    infer_instance
  haveI hqV : Epi qV := by
    dsimp only [qV]
    infer_instance
  have h₀V : IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
      (projectiveTwistedPushforward 1 QV d) :=
    IsProjectiveOfRank.of_iso (C.degree_familyAt A B) (h₀.pullback B.hom)
  have h₁V : IsProjectiveOfRank
      ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
      (projectiveTwistedPushforward 1 QV (d + 1)) :=
    IsProjectiveOfRank.of_iso (C.degreeSucc_familyAt A B) (h₁.pullback B.hom)
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
      (projectiveTwistedPushforwardIteratedBaseChangeIso QA B D
        (C.degree_familyAt A B)
        (C.degree_familyAt A ((Over.map B.hom).obj D)))
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
      (projectiveTwistedPushforwardIteratedBaseChangeIso QA B D
        (C.degreeSucc_familyAt A B)
        (C.degreeSucc_familyAt A ((Over.map B.hom).obj D)))
  refine ⟨(d : ℤ), ?_⟩
  have hflat :=
    ProjectiveSpace.isFlatAbove_gammaStar_twistedFreeQuotient_of_pushforward_seed_baseChange
      r R l d ((P.eval (d : ℚ)).num.natAbs)
      ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs) hd QV qV h₀V h₁V e₀ e₁
  simpa only [R, B, QV, projectiveFamilyAt, ProjectiveSpace.projSpecπ,
    Over.mk_hom, Nat.reduceAdd] using hflat

end AlgebraicGeometry.Scheme.Modules

end

end
