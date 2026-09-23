module

public import StacksAndModuli.API.ProjectiveFlatteningUniversalFamily
public import StacksAndModuli.API.SheafFlatteningProjectiveRank
public import StacksAndModuli.API.QuotGrassmannianReconstruction
public import StacksAndModuli.API.QcqsPushforwardQuasicoherent

/-!
# Finite-degree projective flattening

Projective flattening is reduced here to the precise finite-degree input supplied by
cohomology and base change plus a Gotzmann-type persistence theorem.  The finite
conditions are not arbitrary sheaves: they are

* the twisted pushforwards `pi_* Q(d)`, required to have rank `P(d)`; and
* the cokernels of the degree-one multiplication maps
  `pi_* Q(d)^{n+1} -> pi_* Q(d+1)`, required to have rank zero.

`FiniteDegreeProjectiveFlatteningData` records a finite list of these canonical
conditions, the forward implication from flatness with Hilbert polynomial `P`, and
the reverse multiplication-persistence implication.  The main theorem turns this
data into `ProjectiveFlatteningHasFiniteRankPresentation`.  Its proof includes all
chartwise-to-intrinsic rank conversion, functoriality, finite-intersection gluing,
representability, and the immersion conclusion.  Thus a future CBC/Gotzmann theorem
has only to construct the finite-degree data; no representability bookkeeping remains.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.FiniteDegreeProjectiveFlatteningData`;
* `AlgebraicGeometry.Scheme.Modules.projectiveFlatteningHasFiniteRankPresentation_of_finiteDegree`;
* `AlgebraicGeometry.Scheme.Modules.projectiveFlatteningFiniteDegreeRepresentableBy`;
* `AlgebraicGeometry.Scheme.Modules.projectiveFlatteningFiniteDegree_hom_isImmersion`.
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

variable {T : Scheme.{u}}

/-- The degree-`d` twisted pushforward `pi_* Q(d)`. -/
noncomputable def projectiveTwistedPushforward (n : ℕ)
    (Q : (Scheme.projectiveSpaceOver n T).Modules) (d : ℕ) : T.Modules :=
  (pushforward (Scheme.projectiveSpaceOverπ n T)).obj
    (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))

/-- Multiplication by one degree-one monomial, before applying `pi_*`. -/
noncomputable def projectiveTwistMulOne (n : ℕ)
    (Q : (Scheme.projectiveSpaceOver n T).Modules) (d : ℕ)
    (i : Fin ((n + 1).choose n)) :
    Scheme.projectiveSpaceOverTwistModule Q (d : ℤ) ⟶
      Scheme.projectiveSpaceOverTwistModule Q ((d + 1 : ℕ) : ℤ) :=
  tensorMapRight Q
    (Scheme.twistMonomialMulHom n T (d : ℤ) ((d + 1 : ℕ) : ℤ)
      1 (by omega) i)

/-- The degree-one multiplication map
`pi_* Q(d)^{(n+1)} -> pi_* Q(d+1)`, indexed by the degree-one monomial basis. -/
noncomputable def projectiveTwistedPushforwardMul (n : ℕ)
    (Q : (Scheme.projectiveSpaceOver n T).Modules) (d : ℕ) :
    (∐ fun _ : Fin ((n + 1).choose n) ↦ projectiveTwistedPushforward n Q d) ⟶
      projectiveTwistedPushforward n Q (d + 1) :=
  Limits.Sigma.desc (fun i ↦
    (pushforward (Scheme.projectiveSpaceOverπ n T)).map
      (projectiveTwistMulOne n Q d i))

/-- The defect of degree-one persistence: the cokernel of the multiplication map
from degree `d` to degree `d+1`. -/
noncomputable def projectiveTwistedPushforwardMulDefect (n : ℕ)
    (Q : (Scheme.projectiveSpaceOver n T).Modules) (d : ℕ) : T.Modules :=
  cokernel (projectiveTwistedPushforwardMul n Q d)

instance projectiveTwistedPushforward_isQuasicoherent
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules)
    [Q.IsQuasicoherent] (d : ℕ) :
    (projectiveTwistedPushforward n Q d).IsQuasicoherent := by
  dsimp only [projectiveTwistedPushforward]
  infer_instance

/-- A canonical finite-degree condition used by projective flattening. -/
inductive ProjectiveFiniteDegreeCondition where
  /-- The twisted pushforward in degree `d` has the Hilbert-polynomial rank. -/
  | pushforward (d : ℕ)
  /-- Multiplication from degree `d` to degree `d+1` is surjective, expressed by
  requiring its cokernel to be locally free of rank zero. -/
  | multiplicationDefect (d : ℕ)
  deriving DecidableEq

namespace ProjectiveFiniteDegreeCondition

/-- The canonical sheaf whose rank realizes a finite-degree condition. -/
noncomputable def sheaf (c : ProjectiveFiniteDegreeCondition) (n : ℕ)
    (Q : (Scheme.projectiveSpaceOver n T).Modules) : T.Modules :=
  match c with
  | .pushforward d => projectiveTwistedPushforward n Q d
  | .multiplicationDefect d => projectiveTwistedPushforwardMulDefect n Q d

/-- The rank prescribed by a finite-degree condition. -/
def rank (c : ProjectiveFiniteDegreeCondition) (P : Polynomial ℚ) : ℕ :=
  match c with
  | .pushforward d => (P.eval (d : ℚ)).num.natAbs
  | .multiplicationDefect _ => 0

end ProjectiveFiniteDegreeCondition

/-- The exact finite-degree input for projective flattening.

The first implication is the output expected from uniform regularity and cohomology
and base change.  The second is the Gotzmann-style persistence statement: the listed
pushforward ranks and vanishing multiplication defects force flatness and the fixed
fibrewise Hilbert polynomial after every base change. -/
structure FiniteDegreeProjectiveFlatteningData
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules)
    [Q.IsQuasicoherent] (P : Polynomial ℚ) where
  /-- Number of degree and multiplication-defect conditions. -/
  count : ℕ
  /-- The finite list of canonical conditions. -/
  condition : Fin count → ProjectiveFiniteDegreeCondition
  /-- Finite presentation of every sheaf occurring in the finite list. -/
  isQuasicoherent : ∀ i, ((condition i).sheaf n Q).IsQuasicoherent
  /-- Finite presentation of every sheaf occurring in the finite list. -/
  isFinitePresentation : ∀ i, ((condition i).sheaf n Q).IsFinitePresentation
  /-- Uniform CBC/regularity: a flat fixed-polynomial family satisfies all listed
  pushforward-rank and multiplication-defect conditions after every base change. -/
  projectiveRanks : ∀ (A : Over T),
    (projectiveFamilyAt n Q A).FlatOver
        (Scheme.projectiveSpaceOverπ n A.left) ∧
      Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q A) P →
    ∀ i, IsProjectiveOfRank ((condition i).rank P)
      ((pullback A.hom).obj ((condition i).sheaf n Q))
  /-- Multiplication persistence: the finite pushforward-rank and zero-defect
  conditions force projective flatness with fibrewise Hilbert polynomial `P`. -/
  multiplicationPersistence : ∀ (A : Over T),
    (∀ i, IsProjectiveOfRank ((condition i).rank P)
      ((pullback A.hom).obj ((condition i).sheaf n Q))) →
    (projectiveFamilyAt n Q A).FlatOver
        (Scheme.projectiveSpaceOverπ n A.left) ∧
      Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q A) P

namespace FiniteDegreeProjectiveFlatteningData

variable {n : ℕ} {Q : (Scheme.projectiveSpaceOver n T).Modules}
  [Q.IsQuasicoherent] {P : Polynomial ℚ}

/-- Extract one component from the recursively defined finite conjunction. -/
noncomputable def finProdPointComponent :
    ∀ {k : ℕ} (F : Fin k → (Over T)ᵒᵖ ⥤ Type (u + 1))
      (i : Fin k) (A : (Over T)ᵒᵖ),
      (finProdFunctorLarge F).obj A → (F i).obj A
  | 0, _, i, _, _ => Fin.elim0 i
  | _ + 1, F, i, A, x =>
      Fin.cases x.1
        (fun j ↦ finProdPointComponent (fun t ↦ F t.succ) j A x.2) i

/-- Assemble a point of the recursively defined finite conjunction from its
components. -/
noncomputable def finProdPointOfComponents :
    ∀ {k : ℕ} (F : Fin k → (Over T)ᵒᵖ ⥤ Type (u + 1))
      (A : (Over T)ᵒᵖ), (∀ i, (F i).obj A) →
      (finProdFunctorLarge F).obj A
  | 0, _, A, _ =>
      ULift.up (Over.homMk A.unop.hom (by simp) : A.unop ⟶ Over.mk (𝟙 T))
  | _ + 1, F, A, x =>
      (x 0, finProdPointOfComponents (fun i ↦ F i.succ) A (fun i ↦ x i.succ))

/-- A point satisfying all finite rank conditions gives a point of the projective
flattening functor by multiplication persistence. -/
noncomputable def projectivePointOfFiniteDegreePoint
    (D : FiniteDegreeProjectiveFlatteningData n Q P)
    (A : Over T)
    (x : (finProdFunctorLarge (fun i ↦
      flatRankFunctorOver ((D.condition i).sheaf n Q)
        ((D.condition i).rank P) ⋙ uliftFunctor.{u + 1})).obj (op A)) :
    (projectiveFlatteningFunctor n Q (P := P)).obj (op A) := by
  have hRank : ∀ i, IsProjectiveOfRank ((D.condition i).rank P)
      ((pullback A.hom).obj ((D.condition i).sheaf n Q)) := by
    intro i
    letI : ((D.condition i).sheaf n Q).IsQuasicoherent :=
      D.isQuasicoherent i
    let xi := finProdPointComponent (fun j ↦
      flatRankFunctorOver ((D.condition j).sheaf n Q)
        ((D.condition j).rank P) ⋙ uliftFunctor.{u + 1}) i (op A) x
    exact (locallyFactors_affineStratum_iff_isProjectiveOfRank
      ((D.condition i).sheaf n Q) (D.isFinitePresentation i)
      ((D.condition i).rank P) A).mp xi.down.down.down
  exact ULift.up (PLift.up (D.multiplicationPersistence A hRank))

/-- A flat fixed-polynomial projective family gives every finite rank condition in
the package. -/
noncomputable def finiteDegreePointOfProjectivePoint
    (D : FiniteDegreeProjectiveFlatteningData n Q P)
    (A : Over T)
    (x : (projectiveFlatteningFunctor n Q (P := P)).obj (op A)) :
    (finProdFunctorLarge (fun i ↦
      flatRankFunctorOver ((D.condition i).sheaf n Q)
        ((D.condition i).rank P) ⋙ uliftFunctor.{u + 1})).obj (op A) :=
  finProdPointOfComponents (fun i ↦
      flatRankFunctorOver ((D.condition i).sheaf n Q)
        ((D.condition i).rank P) ⋙ uliftFunctor.{u + 1}) (op A) (fun i ↦ by
    letI : ((D.condition i).sheaf n Q).IsQuasicoherent :=
      D.isQuasicoherent i
    exact ULift.up (ULift.up (PLift.up
      ((locallyFactors_affineStratum_iff_isProjectiveOfRank
          ((D.condition i).sheaf n Q) (D.isFinitePresentation i)
          ((D.condition i).rank P) A).mpr
            (D.projectiveRanks A x.down.down i)))))

/-- The finite conjunction of the canonical degree conditions is naturally the
projective flattening functor. -/
noncomputable def functorIso
    (D : FiniteDegreeProjectiveFlatteningData n Q P) :
    finProdFunctorLarge (fun i ↦
      flatRankFunctorOver ((D.condition i).sheaf n Q)
        ((D.condition i).rank P) ⋙ uliftFunctor.{u + 1}) ≅
      projectiveFlatteningFunctor n Q (P := P) where
  hom :=
    { app := fun A ↦ ↾fun x ↦
        D.projectivePointOfFiniteDegreePoint A.unop x
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        exact (projectiveFlatteningFunctor_subsingleton n Q P B).elim _ _ }
  inv :=
    { app := fun A ↦ ↾fun x ↦
        D.finiteDegreePointOfProjectivePoint A.unop x
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        haveI := finProdFunctorLarge_subsingleton (fun i ↦
          flatRankFunctorOver ((D.condition i).sheaf n Q)
            ((D.condition i).rank P) ⋙ uliftFunctor.{u + 1}) (fun i C ↦ by
          change Subsingleton
            (ULift ((flatRankFunctorOver ((D.condition i).sheaf n Q)
              ((D.condition i).rank P)).obj C))
          haveI := Scheme.factorsFunctor_subsingleton
            (affineStratum ((D.condition i).sheaf n Q)
              ((D.condition i).rank P)) C
          infer_instance) B
        exact Subsingleton.elim _ _ }
  hom_inv_id := by
    ext A x
    haveI := finProdFunctorLarge_subsingleton (fun i ↦
      flatRankFunctorOver ((D.condition i).sheaf n Q)
        ((D.condition i).rank P) ⋙ uliftFunctor.{u + 1}) (fun i C ↦ by
      change Subsingleton
        (ULift ((flatRankFunctorOver ((D.condition i).sheaf n Q)
          ((D.condition i).rank P)).obj C))
      haveI := Scheme.factorsFunctor_subsingleton
        (affineStratum ((D.condition i).sheaf n Q)
          ((D.condition i).rank P)) C
      infer_instance) A
    exact Subsingleton.elim _ _
  inv_hom_id := by
    ext A x
    exact (projectiveFlatteningFunctor_subsingleton n Q P A).elim _ _

/-- The finite-flat-rank presentation associated with finite-degree CBC and
multiplication-persistence data. -/
noncomputable def finiteFlatRankPresentation
    (D : FiniteDegreeProjectiveFlatteningData n Q P) :
    FiniteFlatRankPresentation (projectiveFlatteningFunctor n Q (P := P)) where
  count := D.count
  sheaf := fun i ↦ (D.condition i).sheaf n Q
  rank := fun i ↦ (D.condition i).rank P
  isQuasicoherent := D.isQuasicoherent
  finite := fun i U ↦ by
    have hfpPull : ((pullback U.1.ι).obj
        ((D.condition i).sheaf n Q)).IsFinitePresentation :=
      isFinitePresentation_pullback_of_isFinitePresentation U.1.ι
        (D.isFinitePresentation i)
    have hfpSec : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
        Γ((pullback U.1.ι).obj ((D.condition i).sheaf n Q), ⊤) :=
      (Scheme.Modules.isFinitePresentation_iff_sections_affineOpens
        ((pullback U.1.ι).obj ((D.condition i).sheaf n Q))).mp
          hfpPull ⟨⊤, isAffineOpen_top _⟩
    letI : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
        Γ((pullback U.1.ι).obj ((D.condition i).sheaf n Q), ⊤) := hfpSec
    infer_instance
  iso := D.functorIso

end FiniteDegreeProjectiveFlatteningData

/-- Finite-degree CBC plus multiplication persistence supplies the projective
flattening finite-rank presentation. -/
theorem projectiveFlatteningHasFiniteRankPresentation_of_finiteDegree
    {n : ℕ} (Q : (Scheme.projectiveSpaceOver n T).Modules)
    [Q.IsQuasicoherent] (P : Polynomial ℚ)
    (D : FiniteDegreeProjectiveFlatteningData n Q P) :
    ProjectiveFlatteningHasFiniteRankPresentation n Q (P := P) :=
  ⟨D.finiteFlatRankPresentation⟩

/-- The canonical representative obtained from finite-degree projective flattening
data. -/
noncomputable def projectiveFlatteningFiniteDegreeRepresentative
    {n : ℕ} (Q : (Scheme.projectiveSpaceOver n T).Modules)
    [Q.IsQuasicoherent] (P : Polynomial ℚ)
    (D : FiniteDegreeProjectiveFlatteningData n Q P) : Over T :=
  D.finiteFlatRankPresentation.representative

/-- Finite-degree projective flattening data represents the flat fixed-polynomial
condition. -/
noncomputable def projectiveFlatteningFiniteDegreeRepresentableBy
    {n : ℕ} (Q : (Scheme.projectiveSpaceOver n T).Modules)
    [Q.IsQuasicoherent] (P : Polynomial ℚ)
    (D : FiniteDegreeProjectiveFlatteningData n Q P) :
    (projectiveFlatteningFunctor n Q (P := P)).RepresentableBy
      (projectiveFlatteningFiniteDegreeRepresentative Q P D) :=
  D.finiteFlatRankPresentation.representableBy

/-- The representative supplied by finite-degree CBC and multiplication persistence
is immersed in the base. -/
theorem projectiveFlatteningFiniteDegree_hom_isImmersion
    {n : ℕ} (Q : (Scheme.projectiveSpaceOver n T).Modules)
    [Q.IsQuasicoherent] (P : Polynomial ℚ)
    (D : FiniteDegreeProjectiveFlatteningData n Q P) :
    IsImmersion (projectiveFlatteningFiniteDegreeRepresentative Q P D).hom :=
  D.finiteFlatRankPresentation.representative_hom_isImmersion

end AlgebraicGeometry.Scheme.Modules

end
