module

public import StacksAndModuli.API.ProjectiveFlatteningFiniteDegree
public import StacksAndModuli.API.SchemeModulesCokernelFinitePresentation
public import StacksAndModuli.API.QuasicoherentFiniteCoproduct
public import StacksAndModuli.API.ProjectiveTwistedFreePresentation

/-!
# One-step projective flattening and twisted-free reconstruction

For a quotient generated in a sufficiently large degree, Gotzmann persistence
uses only three conditions: the ranks of `pi_* Q(d)` and `pi_* Q(d+1)`, and
surjectivity of degree-one multiplication between them.  This file packages
exactly those three canonical conditions and turns them into the general
finite-degree projective-flattening data.

All formal geometry around the persistence theorem is discharged here.  The
remaining field `ProjectiveOneStepPersistence` is the precise Gotzmann input:
after every base change, the two ranks and zero multiplication defect must
force flatness and the fixed fibrewise Hilbert polynomial.

The file also proves that the reconstructed twisted-free quotient is
quasicoherent over an arbitrary base and finitely presented over a locally
Noetherian base.  Thus the reconstruction itself contributes no further
gluing obligation.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.ProjectiveOneStepRanks`;
* `AlgebraicGeometry.Scheme.Modules.ProjectiveOneStepPersistence`;
* `AlgebraicGeometry.Scheme.Modules.OneStepProjectiveFlatteningData`;
* `AlgebraicGeometry.Scheme.Modules.projectiveFlatteningHasFiniteRankPresentation_of_oneStep`;
* `AlgebraicGeometry.Scheme.reconstructedQuotient'_isQuasicoherent`;
* `AlgebraicGeometry.Scheme.reconstructedQuotient'_isFinitePresentation`;
* `AlgebraicGeometry.Scheme.reconstructedQuotient'_projectiveFlatteningHasFiniteRankPresentation`.
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

/-- The three canonical conditions in a one-step Gotzmann presentation:
pushforward ranks in degrees `d` and `d+1`, followed by vanishing of the
degree-`d` multiplication defect. -/
def projectiveOneStepCondition (d : ℕ) :
    Fin 3 → ProjectiveFiniteDegreeCondition :=
  Fin.cases (.pushforward d) fun i ↦
    Fin.cases (.pushforward (d + 1)) (fun _ ↦ .multiplicationDefect d) i

@[simp]
lemma projectiveOneStepCondition_zero :
    projectiveOneStepCondition d 0 = .pushforward d := rfl

@[simp]
lemma projectiveOneStepCondition_one :
    projectiveOneStepCondition d 1 = .pushforward (d + 1) := rfl

@[simp]
lemma projectiveOneStepCondition_two :
    projectiveOneStepCondition d 2 = .multiplicationDefect d := rfl

/-- The multiplication defect of a quasicoherent projective family is
quasicoherent. -/
instance projectiveTwistedPushforwardMulDefect_isQuasicoherent
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules)
    [Q.IsQuasicoherent] (d : ℕ) :
    (projectiveTwistedPushforwardMulDefect n Q d).IsQuasicoherent := by
  letI : (∐ fun _ : Fin ((n + 1).choose n) ↦
      projectiveTwistedPushforward n Q d).IsQuasicoherent :=
    isQuasicoherent_coproduct_small _
  dsimp only [projectiveTwistedPushforwardMulDefect]
  apply isQuasicoherent_cokernel

/-- If the two adjacent twisted pushforwards are finitely presented, so is
their degree-one multiplication defect. -/
lemma projectiveTwistedPushforwardMulDefect_isFinitePresentation
    (h₀ : (projectiveTwistedPushforward n Q d).IsFinitePresentation)
    (h₁ : (projectiveTwistedPushforward n Q (d + 1)).IsFinitePresentation) :
    (projectiveTwistedPushforwardMulDefect n Q d).IsFinitePresentation := by
  letI : (projectiveTwistedPushforward n Q d).IsFinitePresentation := h₀
  letI : (projectiveTwistedPushforward n Q (d + 1)).IsFinitePresentation := h₁
  letI : (∐ fun _ : Fin ((n + 1).choose n) ↦
      projectiveTwistedPushforward n Q d).IsFinitePresentation :=
    finiteCoproduct_isFinitePresentation_small _
  dsimp only [projectiveTwistedPushforwardMulDefect]
  exact cokernel_isFinitePresentation (projectiveTwistedPushforwardMul n Q d)

/-- Uniform regularity and cohomology-and-base-change in the two adjacent
degrees, including surjectivity of degree-one multiplication. -/
def ProjectiveOneStepRanks
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (P : Polynomial ℚ) (d : ℕ) : Prop :=
  ∀ (A : Over T),
    (projectiveFamilyAt n Q A).FlatOver
        (Scheme.projectiveSpaceOverπ n A.left) ∧
      Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q A) P →
    IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
        ((pullback A.hom).obj (projectiveTwistedPushforward n Q d)) ∧
      IsProjectiveOfRank ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
        ((pullback A.hom).obj (projectiveTwistedPushforward n Q (d + 1))) ∧
      IsProjectiveOfRank 0
        ((pullback A.hom).obj (projectiveTwistedPushforwardMulDefect n Q d))

/-- The exact one-step Gotzmann persistence statement needed for projective
flattening.  It is deliberately quantified after every base change: the two
adjacent pushforward ranks and surjective degree-one multiplication must force
both flatness and the fibrewise Hilbert polynomial. -/
def ProjectiveOneStepPersistence
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (P : Polynomial ℚ) (d : ℕ) : Prop :=
  ∀ (A : Over T),
    IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
        ((pullback A.hom).obj (projectiveTwistedPushforward n Q d)) →
    IsProjectiveOfRank ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
        ((pullback A.hom).obj (projectiveTwistedPushforward n Q (d + 1))) →
    IsProjectiveOfRank 0
        ((pullback A.hom).obj (projectiveTwistedPushforwardMulDefect n Q d)) →
    (projectiveFamilyAt n Q A).FlatOver
        (Scheme.projectiveSpaceOverπ n A.left) ∧
      Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q A) P

/-- The finite sheaf-theoretic input around a one-step Gotzmann theorem.  Only
the adjacent pushforwards need separate finite-presentation hypotheses; the
multiplication defect is a finitely presented cokernel automatically. -/
structure OneStepProjectiveFlatteningData
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules)
    [Q.IsQuasicoherent] (P : Polynomial ℚ) (d : ℕ) where
  /-- Finite presentation of `pi_* Q(d)`. -/
  pushforward_isFinitePresentation :
    (projectiveTwistedPushforward n Q d).IsFinitePresentation
  /-- Finite presentation of `pi_* Q(d+1)`. -/
  pushforward_succ_isFinitePresentation :
    (projectiveTwistedPushforward n Q (d + 1)).IsFinitePresentation
  /-- The forward CBC/regularity implication. -/
  ranks : ProjectiveOneStepRanks n Q P d
  /-- The reverse Gotzmann-persistence implication. -/
  persistence : ProjectiveOneStepPersistence n Q P d

namespace OneStepProjectiveFlatteningData

/-- A one-step package supplies the general finite-degree projective
flattening package with exactly three conditions. -/
noncomputable def toFiniteDegree
    (D : OneStepProjectiveFlatteningData n Q P d) :
    FiniteDegreeProjectiveFlatteningData n Q P where
  count := 3
  condition := projectiveOneStepCondition d
  isQuasicoherent := by
    intro i
    refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun _ ↦ ?_) j) i
    · change (projectiveTwistedPushforward n Q d).IsQuasicoherent
      infer_instance
    · change (projectiveTwistedPushforward n Q (d + 1)).IsQuasicoherent
      infer_instance
    · change (projectiveTwistedPushforwardMulDefect n Q d).IsQuasicoherent
      infer_instance
  isFinitePresentation := by
    intro i
    refine Fin.cases D.pushforward_isFinitePresentation
      (fun j ↦ Fin.cases D.pushforward_succ_isFinitePresentation
        (fun _ ↦ ?_) j) i
    exact projectiveTwistedPushforwardMulDefect_isFinitePresentation
      D.pushforward_isFinitePresentation D.pushforward_succ_isFinitePresentation
  projectiveRanks := by
    intro A h i
    obtain ⟨h₀, h₁, hmul⟩ := D.ranks A h
    exact Fin.cases h₀ (fun j ↦ Fin.cases h₁ (fun _ ↦ hmul) j) i
  multiplicationPersistence := by
    intro A h
    exact D.persistence A (h 0) (h 1) (h 2)

/-- One-step CBC and Gotzmann persistence give a finite-rank presentation of
the projective flattening functor. -/
theorem projectiveFlatteningHasFiniteRankPresentation
    (D : OneStepProjectiveFlatteningData n Q P d) :
    ProjectiveFlatteningHasFiniteRankPresentation n Q (P := P) :=
  projectiveFlatteningHasFiniteRankPresentation_of_finiteDegree Q P D.toFiniteDegree

end OneStepProjectiveFlatteningData

/-- Direct constructor from the two finite-presentation facts, forward
regularity/CBC, and one-step persistence. -/
theorem projectiveFlatteningHasFiniteRankPresentation_of_oneStep
    (hfp₀ : (projectiveTwistedPushforward n Q d).IsFinitePresentation)
    (hfp₁ : (projectiveTwistedPushforward n Q (d + 1)).IsFinitePresentation)
    (hranks : ProjectiveOneStepRanks n Q P d)
    (hpersist : ProjectiveOneStepPersistence n Q P d) :
    ProjectiveFlatteningHasFiniteRankPresentation n Q (P := P) :=
  OneStepProjectiveFlatteningData.projectiveFlatteningHasFiniteRankPresentation
    (OneStepProjectiveFlatteningData.mk hfp₀ hfp₁ hranks hpersist)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The twisted-free quotient reconstructed from a quasicoherent target on the
base is quasicoherent, over an arbitrary base scheme. -/
lemma reconstructedQuotient'_isQuasicoherent
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    (reconstructedQuotient' n T l r d e he u).IsQuasicoherent := by
  letI : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  letI : ((Modules.pullback (projectiveSpaceOverπ n T)).obj
      (kernel u)).IsQuasicoherent :=
    Modules.isQuasicoherent_pullback (projectiveSpaceOverπ n T) (kernel u)
  letI : (Modules.tensor
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (projectiveSpaceOverTwist n T (-(d : ℤ)))).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (-(d : ℤ))).IsQuasicoherent
    infer_instance
  letI : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)).IsQuasicoherent :=
    Modules.projectiveSpaceOverTwistCoproduct_isQuasicoherent _ n T _
  dsimp only [reconstructedQuotient']
  apply Modules.isQuasicoherent_cokernel

/-- Over a locally Noetherian base, the reconstructed twisted-free quotient is
finitely presented.  The noetherian hypothesis enters only through finite
presentation of the kernel of the base quotient. -/
lemma reconstructedQuotient'_isFinitePresentation
    (n : ℕ) (T : Scheme.{u}) [IsLocallyNoetherian T]
    (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E) :
    (reconstructedQuotient' n T l r d e he u).IsFinitePresentation := by
  letI hFreeFp : (SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n))).IsFinitePresentation := by
    exact Modules.isFinitePresentation_of_globalPresentation
      (Modules.freePresentation
        (X := T) (ULift.{u} (Fin r) × Fin ((n + e).choose n)))
  letI hKqc : (kernel u).IsQuasicoherent := Modules.kernel_isQuasicoherent u
  letI hPullKqc : ((Modules.pullback (projectiveSpaceOverπ n T)).obj
      (kernel u)).IsQuasicoherent :=
    Modules.isQuasicoherent_pullback (projectiveSpaceOverπ n T) (kernel u)
  letI hKfp : (kernel u).IsFinitePresentation :=
    Modules.kernel_isFinitePresentation u
  letI hPullKfp : ((Modules.pullback (projectiveSpaceOverπ n T)).obj
      (kernel u)).IsFinitePresentation :=
    Modules.isFinitePresentation_pullback_of_isFinitePresentation
      (projectiveSpaceOverπ n T) hKfp
  letI hSourceFp : (Modules.tensor
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (projectiveSpaceOverTwist n T (-(d : ℤ)))).IsFinitePresentation := by
    change (projectiveSpaceOverTwistModule
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (-(d : ℤ))).IsFinitePresentation
    infer_instance
  letI hSourceQc : (Modules.tensor
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (projectiveSpaceOverTwist n T (-(d : ℤ)))).IsQuasicoherent := by
    change (projectiveSpaceOverTwistModule
      ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
      (-(d : ℤ))).IsQuasicoherent
    infer_instance
  letI hTargetFp : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)).IsFinitePresentation :=
    Modules.projectiveSpaceOverTwistCoproduct_isFinitePresentation _ n T _
  letI hTargetQc : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n T (-l)).IsQuasicoherent :=
    Modules.projectiveSpaceOverTwistCoproduct_isQuasicoherent _ n T _
  dsimp only [reconstructedQuotient']
  exact Modules.cokernel_isFinitePresentation _

/-- For a reconstructed twisted-free quotient, the only remaining ingredients
for projective flattening are the adjacent pushforward finiteness statements,
forward CBC/regularity, and the exact one-step persistence theorem. -/
theorem reconstructedQuotient'_projectiveFlatteningHasFiniteRankPresentation
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (P : Polynomial ℚ)
    (hfp₀ : (Modules.projectiveTwistedPushforward n
      (reconstructedQuotient' n T l r d e he u) d).IsFinitePresentation)
    (hfp₁ : (Modules.projectiveTwistedPushforward n
      (reconstructedQuotient' n T l r d e he u) (d + 1)).IsFinitePresentation)
    (hranks : Modules.ProjectiveOneStepRanks n
      (reconstructedQuotient' n T l r d e he u) P d)
    (hpersist : Modules.ProjectiveOneStepPersistence n
      (reconstructedQuotient' n T l r d e he u) P d) :
    letI : (reconstructedQuotient' n T l r d e he u).IsQuasicoherent :=
      reconstructedQuotient'_isQuasicoherent n T l r d e he u
    Modules.ProjectiveFlatteningHasFiniteRankPresentation n
      (reconstructedQuotient' n T l r d e he u) (P := P) := by
  letI : (reconstructedQuotient' n T l r d e he u).IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent n T l r d e he u
  exact Modules.projectiveFlatteningHasFiniteRankPresentation_of_oneStep
    hfp₀ hfp₁ hranks hpersist

end AlgebraicGeometry.Scheme

end
