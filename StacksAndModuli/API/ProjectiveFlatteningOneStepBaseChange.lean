module

public import StacksAndModuli.API.ProjectiveFlatteningOneStep
public import StacksAndModuli.API.SchemeModulesProjectiveRankZero

/-!
# Base-change interface for one-step projective flattening

The rank loci used by projective flattening live on the original base, so at a
test scheme they see pullbacks of the original twisted pushforwards.  Regularity
and Gotzmann persistence, on the other hand, naturally speak about the twisted
pushforwards of the base-changed family.  This file isolates the comparison
between those two formulations.

`ProjectiveOneStepBaseChangeComparison` asks only for the three isomorphisms
actually consumed in degrees `d`, `d+1`, and by the multiplication defect.
Given them, actual-base-change CBC/rank and Gotzmann statements assemble the
one-step finite-rank presentation without any further descent or gluing.

The remaining substantive statements are therefore visible separately:

* `ProjectiveOneStepActualRanks` is the forward regularity/CBC theorem;
* `ProjectiveOneStepGotzmannPersistence` is the reverse algebraic persistence
  theorem.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.ProjectiveOneStepBaseChangeComparison`;
* `AlgebraicGeometry.Scheme.Modules.ProjectiveOneStepMultiplicationBaseChangeComparison`;
* `AlgebraicGeometry.Scheme.Modules.ProjectiveOneStepActualRanks`;
* `AlgebraicGeometry.Scheme.Modules.ProjectiveOneStepActualRanksAndEpi`;
* `AlgebraicGeometry.Scheme.Modules.ProjectiveOneStepGotzmannPersistence`;
* `AlgebraicGeometry.Scheme.Modules.ProjectiveOneStepGotzmannPersistenceEpi`;
* `AlgebraicGeometry.Scheme.Modules.OneStepProjectiveFlatteningData.ofActual`.
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

attribute [local instance] MvPolynomial.gradedAlgebra

variable {T : Scheme.{u}} {n : ℕ}
  {Q : (Scheme.projectiveSpaceOver n T).Modules} [Q.IsQuasicoherent]
  {P : Polynomial ℚ} {d : ℕ}

/-- The three base-change comparisons used by one-step projective flattening.
The right-hand sides are formed from the actual base-changed projective family;
the left-hand sides are the pullbacks seen by flattening strata on `T`. -/
structure ProjectiveOneStepBaseChangeComparison
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules) (d : ℕ) where
  /-- Base change for the degree-`d` twisted pushforward. -/
  degree (A : Over T) :
    (pullback A.hom).obj (projectiveTwistedPushforward n Q d) ≅
      projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d
  /-- Base change for the degree-`d+1` twisted pushforward. -/
  degreeSucc (A : Over T) :
    (pullback A.hom).obj (projectiveTwistedPushforward n Q (d + 1)) ≅
      projectiveTwistedPushforward n (projectiveFamilyAt n Q A) (d + 1)
  /-- Base change for the cokernel of degree-one multiplication. -/
  multiplicationDefect (A : Over T) :
    (pullback A.hom).obj (projectiveTwistedPushforwardMulDefect n Q d) ≅
      projectiveTwistedPushforwardMulDefect n (projectiveFamilyAt n Q A) d

/-- The canonical base-change isomorphism on the finite coproduct forming the
source of degree-one multiplication, induced termwise from base change in
degree `d`. -/
noncomputable def projectiveOneStepMultiplicationSourceBaseChangeIso
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules) (d : ℕ)
    (A : Over T)
    (e : (pullback A.hom).obj (projectiveTwistedPushforward n Q d) ≅
      projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) :
    (pullback A.hom).obj
        (∐ fun _ : Fin ((n + 1).choose n) ↦
          projectiveTwistedPushforward n Q d) ≅
      (∐ fun _ : Fin ((n + 1).choose n) ↦
        projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) :=
  PreservesCoproduct.iso (pullback A.hom)
      (fun _ : Fin ((n + 1).choose n) ↦
        projectiveTwistedPushforward n Q d) ≪≫
    Sigma.mapIso (fun _ ↦ e)

/-- A more primitive base-change package for degree-one multiplication.  It
records base change for the two adjacent terms and a commuting square for the
multiplication map itself.  Preservation of coproducts and cokernels supplies
the source and defect comparisons automatically. -/
structure ProjectiveOneStepMultiplicationBaseChangeComparison
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules) (d : ℕ) where
  /-- Base change for the degree-`d` twisted pushforward. -/
  degree (A : Over T) :
    (pullback A.hom).obj (projectiveTwistedPushforward n Q d) ≅
      projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d
  /-- Base change for the degree-`d+1` twisted pushforward. -/
  degreeSucc (A : Over T) :
    (pullback A.hom).obj (projectiveTwistedPushforward n Q (d + 1)) ≅
      projectiveTwistedPushforward n (projectiveFamilyAt n Q A) (d + 1)
  /-- The multiplication map commutes with the preceding base-change
  identifications. -/
  multiplication_comm (A : Over T) :
    (pullback A.hom).map (projectiveTwistedPushforwardMul n Q d) ≫
        (degreeSucc A).hom =
      (projectiveOneStepMultiplicationSourceBaseChangeIso
        n Q d A (degree A)).hom ≫
        projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d

namespace ProjectiveOneStepMultiplicationBaseChangeComparison

omit [Q.IsQuasicoherent] in
/-- A commuting base-change square for multiplication induces the required
base-change isomorphism on its cokernel. -/
noncomputable def toBaseChangeComparison
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison n Q d) :
    ProjectiveOneStepBaseChangeComparison n Q d where
  degree := C.degree
  degreeSucc := C.degreeSucc
  multiplicationDefect A := by
    change (pullback A.hom).obj
        (cokernel (projectiveTwistedPushforwardMul n Q d)) ≅
      cokernel (projectiveTwistedPushforwardMul n
        (projectiveFamilyAt n Q A) d)
    exact PreservesCokernel.iso (pullback A.hom)
        (projectiveTwistedPushforwardMul n Q d) ≪≫
      cokernel.mapIso
        ((pullback A.hom).map (projectiveTwistedPushforwardMul n Q d))
        (projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d)
        (projectiveOneStepMultiplicationSourceBaseChangeIso
          n Q d A (C.degree A)) (C.degreeSucc A)
        (C.multiplication_comm A)

end ProjectiveOneStepMultiplicationBaseChangeComparison

/-- The forward regularity/CBC conclusion in its native formulation: after
forming the actual base-changed family, its two adjacent twisted pushforwards
have the Hilbert-polynomial ranks and its degree-one multiplication defect has
rank zero. -/
def ProjectiveOneStepActualRanks
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (P : Polynomial ℚ) (d : ℕ) : Prop :=
  ∀ (A : Over T),
    (projectiveFamilyAt n Q A).FlatOver
        (Scheme.projectiveSpaceOverπ n A.left) ∧
      Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q A) P →
    IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) ∧
      IsProjectiveOfRank ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) (d + 1)) ∧
      IsProjectiveOfRank 0
        (projectiveTwistedPushforwardMulDefect n
          (projectiveFamilyAt n Q A) d)

/-- The native forward regularity conclusion with surjectivity of multiplication
left in its usual categorical form.  This is often the statement delivered by
global-generation arguments. -/
def ProjectiveOneStepActualRanksAndEpi
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (P : Polynomial ℚ) (d : ℕ) : Prop :=
  ∀ (A : Over T),
    (projectiveFamilyAt n Q A).FlatOver
        (Scheme.projectiveSpaceOverπ n A.left) ∧
      Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q A) P →
    IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) ∧
      IsProjectiveOfRank ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) (d + 1)) ∧
      Epi (projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d)

omit [Q.IsQuasicoherent] in
/-- Surjectivity of the actual degree-one multiplication map turns its
cokernel condition into projectivity of rank zero. -/
theorem ProjectiveOneStepActualRanksAndEpi.toActualRanks
    (h : ProjectiveOneStepActualRanksAndEpi n Q P d) :
    ProjectiveOneStepActualRanks n Q P d := by
  intro A hfamily
  obtain ⟨h₀, h₁, hmul⟩ := h A hfamily
  letI : Epi (projectiveTwistedPushforwardMul n
      (projectiveFamilyAt n Q A) d) := hmul
  refine ⟨h₀, h₁, ?_⟩
  change IsProjectiveOfRank 0
    (cokernel (projectiveTwistedPushforwardMul n
      (projectiveFamilyAt n Q A) d))
  exact cokernel_isProjectiveOfRank_zero_of_epi _

/-- The exact Gotzmann input left by the one-step construction.  It is stated
for the actual base-changed family, with no pullback/pushforward comparison
mixed into the algebraic assertion. -/
def ProjectiveOneStepGotzmannPersistence
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (P : Polynomial ℚ) (d : ℕ) : Prop :=
  ∀ (A : Over T),
    IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) →
    IsProjectiveOfRank ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) (d + 1)) →
    IsProjectiveOfRank 0
        (projectiveTwistedPushforwardMulDefect n
          (projectiveFamilyAt n Q A) d) →
    (projectiveFamilyAt n Q A).FlatOver
        (Scheme.projectiveSpaceOverπ n A.left) ∧
      Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q A) P

/-- Gotzmann persistence in its usual algebraic formulation, with
surjectivity of degree-one multiplication rather than a rank-zero cokernel
condition. -/
def ProjectiveOneStepGotzmannPersistenceEpi
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (P : Polynomial ℚ) (d : ℕ) : Prop :=
  ∀ (A : Over T),
    IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) →
    IsProjectiveOfRank ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) (d + 1)) →
    Epi (projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d) →
    (projectiveFamilyAt n Q A).FlatOver
        (Scheme.projectiveSpaceOverπ n A.left) ∧
      Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q A) P

/-- For the quasicoherent multiplication defect, the rank-zero and
epimorphism formulations of the Gotzmann input agree. -/
theorem ProjectiveOneStepGotzmannPersistenceEpi.toGotzmannPersistence
    (h : ProjectiveOneStepGotzmannPersistenceEpi n Q P d) :
    ProjectiveOneStepGotzmannPersistence n Q P d := by
  intro A h₀ h₁ hmul
  apply h A h₀ h₁
  haveI : (projectiveFamilyAt n Q A).IsQuasicoherent := inferInstance
  haveI : (cokernel (projectiveTwistedPushforwardMul n
      (projectiveFamilyAt n Q A) d)).IsQuasicoherent := by
    change (projectiveTwistedPushforwardMulDefect n
      (projectiveFamilyAt n Q A) d).IsQuasicoherent
    infer_instance
  exact (cokernel_isProjectiveOfRank_zero_iff_epi
    (projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d)).mp hmul

namespace ProjectiveOneStepBaseChangeComparison

omit [Q.IsQuasicoherent] in
/-- Actual-base-change rank statements transport to the pullback rank
statements consumed by the finite flattening strata. -/
theorem projectiveOneStepRanks
    (C : ProjectiveOneStepBaseChangeComparison n Q d)
    (h : ProjectiveOneStepActualRanks n Q P d) :
    ProjectiveOneStepRanks n Q P d := by
  intro A hfamily
  obtain ⟨h₀, h₁, hmul⟩ := h A hfamily
  exact ⟨h₀.of_iso (C.degree A).symm,
    h₁.of_iso (C.degreeSucc A).symm,
    hmul.of_iso (C.multiplicationDefect A).symm⟩

omit [Q.IsQuasicoherent] in
/-- Gotzmann persistence for actual base-changed pushforwards transports to
the pullback formulation consumed by the finite flattening strata. -/
theorem projectiveOneStepPersistence
    (C : ProjectiveOneStepBaseChangeComparison n Q d)
    (h : ProjectiveOneStepGotzmannPersistence n Q P d) :
    ProjectiveOneStepPersistence n Q P d := by
  intro A h₀ h₁ hmul
  exact h A (h₀.of_iso (C.degree A))
    (h₁.of_iso (C.degreeSucc A))
    (hmul.of_iso (C.multiplicationDefect A))

end ProjectiveOneStepBaseChangeComparison

namespace OneStepProjectiveFlatteningData

/-- Constructor from the native CBC/regularity and Gotzmann statements.  The
three explicit base-change comparisons are the only bridge needed to the rank
loci on the original base. -/
theorem ofActual
    (hfp₀ : (projectiveTwistedPushforward n Q d).IsFinitePresentation)
    (hfp₁ : (projectiveTwistedPushforward n Q (d + 1)).IsFinitePresentation)
    (C : ProjectiveOneStepBaseChangeComparison n Q d)
    (hranks : ProjectiveOneStepActualRanks n Q P d)
    (hpersist : ProjectiveOneStepGotzmannPersistence n Q P d) :
    OneStepProjectiveFlatteningData n Q P d where
  pushforward_isFinitePresentation := hfp₀
  pushforward_succ_isFinitePresentation := hfp₁
  ranks := C.projectiveOneStepRanks hranks
  persistence := C.projectiveOneStepPersistence hpersist

/-- Constructor accepting the forward regularity conclusion with an
epimorphic multiplication map. -/
theorem ofActualEpi
    (hfp₀ : (projectiveTwistedPushforward n Q d).IsFinitePresentation)
    (hfp₁ : (projectiveTwistedPushforward n Q (d + 1)).IsFinitePresentation)
    (C : ProjectiveOneStepBaseChangeComparison n Q d)
    (hranks : ProjectiveOneStepActualRanksAndEpi n Q P d)
    (hpersist : ProjectiveOneStepGotzmannPersistence n Q P d) :
    OneStepProjectiveFlatteningData n Q P d :=
  ofActual hfp₀ hfp₁ C hranks.toActualRanks hpersist

/-- The native CBC/regularity package and actual Gotzmann persistence give the
finite-rank presentation of projective flattening. -/
theorem projectiveFlatteningHasFiniteRankPresentation_ofActual
    (hfp₀ : (projectiveTwistedPushforward n Q d).IsFinitePresentation)
    (hfp₁ : (projectiveTwistedPushforward n Q (d + 1)).IsFinitePresentation)
    (C : ProjectiveOneStepBaseChangeComparison n Q d)
    (hranks : ProjectiveOneStepActualRanks n Q P d)
    (hpersist : ProjectiveOneStepGotzmannPersistence n Q P d) :
    ProjectiveFlatteningHasFiniteRankPresentation n Q (P := P) :=
  (ofActual hfp₀ hfp₁ C hranks hpersist).projectiveFlatteningHasFiniteRankPresentation

/-- The native CBC/rank theorem with surjective multiplication and actual
Gotzmann persistence give the finite-rank presentation directly. -/
theorem projectiveFlatteningHasFiniteRankPresentation_ofActualEpi
    (hfp₀ : (projectiveTwistedPushforward n Q d).IsFinitePresentation)
    (hfp₁ : (projectiveTwistedPushforward n Q (d + 1)).IsFinitePresentation)
    (C : ProjectiveOneStepBaseChangeComparison n Q d)
    (hranks : ProjectiveOneStepActualRanksAndEpi n Q P d)
    (hpersist : ProjectiveOneStepGotzmannPersistence n Q P d) :
    ProjectiveFlatteningHasFiniteRankPresentation n Q (P := P) :=
  OneStepProjectiveFlatteningData.projectiveFlatteningHasFiniteRankPresentation
    (ofActualEpi hfp₀ hfp₁ C hranks hpersist)

/-- A commuting base-change square for multiplication, the usual forward
regularity theorem, and actual Gotzmann persistence give the finite-rank
presentation.  No separate cokernel base-change theorem is required. -/
theorem projectiveFlatteningHasFiniteRankPresentation_ofMultiplicationBaseChange
    (hfp₀ : (projectiveTwistedPushforward n Q d).IsFinitePresentation)
    (hfp₁ : (projectiveTwistedPushforward n Q (d + 1)).IsFinitePresentation)
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison n Q d)
    (hranks : ProjectiveOneStepActualRanksAndEpi n Q P d)
    (hpersist : ProjectiveOneStepGotzmannPersistence n Q P d) :
    ProjectiveFlatteningHasFiniteRankPresentation n Q (P := P) :=
  projectiveFlatteningHasFiniteRankPresentation_ofActualEpi
    hfp₀ hfp₁ C.toBaseChangeComparison hranks hpersist

/-- The complete one-step interface in the standard algebraic formulation:
adjacent finite presentation, compatible base change for multiplication,
forward CBC/regularity, and Gotzmann persistence with an epimorphic
multiplication map. -/
theorem projectiveFlatteningHasFiniteRankPresentation_ofMultiplicationBaseChangeEpi
    (hfp₀ : (projectiveTwistedPushforward n Q d).IsFinitePresentation)
    (hfp₁ : (projectiveTwistedPushforward n Q (d + 1)).IsFinitePresentation)
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison n Q d)
    (hranks : ProjectiveOneStepActualRanksAndEpi n Q P d)
    (hpersist : ProjectiveOneStepGotzmannPersistenceEpi n Q P d) :
    ProjectiveFlatteningHasFiniteRankPresentation n Q (P := P) :=
  projectiveFlatteningHasFiniteRankPresentation_ofMultiplicationBaseChange
    hfp₀ hfp₁ C hranks hpersist.toGotzmannPersistence

end OneStepProjectiveFlatteningData

end AlgebraicGeometry.Scheme.Modules

end
