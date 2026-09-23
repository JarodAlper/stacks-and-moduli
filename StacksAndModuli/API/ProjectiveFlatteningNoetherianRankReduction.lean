module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksAndModuli.API.ProjectiveFlatteningSingleRank
public import StacksAndModuli.API.SheafFlatteningImmersion

/-!
# Reducing the rank-to-flattening implication to locally noetherian tests

Suppose a fixed projective flattening condition is to be identified with one
finite-projective-rank condition on a finitely presented quasicoherent sheaf over a
locally noetherian base.  The implication from the rank condition to the projective
flattening condition only has to be proved on locally noetherian test schemes.

Indeed, the ordinary rank condition has an immersed representative.  That representative
is locally of finite type over the locally noetherian base, hence is itself locally
noetherian.  Applying the test-scheme implication to its universal point makes the
projective family flat with the prescribed Hilbert polynomial there.  Every rank point on
an arbitrary test scheme factors through this representative, and the projective
flattening condition is preserved by pullback.

This argument is deliberately one-sided.  It does not reduce the converse implication
from a flat family with prescribed fibrewise Hilbert polynomial to the rank condition:
such a family on an arbitrary test scheme is not known to descend to a locally noetherian
test scheme merely from the flattening-witness API.  The predicate
`ProjectiveFlatteningFlatHilbertImpliesRank` names that remaining input.

Main declarations:

* `ProjectiveFlatteningRankImpliesFlatHilbertOnLocallyNoetherianTests`;
* `projectiveFlatteningRankImpliesFlatHilbert_of_locallyNoetherianTests`;
* `ProjectiveFlatteningFlatHilbertImpliesRank`;
* `projectiveFlatteningSingleRankData_of_locallyNoetherianTests`;
* `projectiveFlatteningLocusWitness_of_locallyNoetherianTests`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {T : Scheme.{u}} (n : ℕ)
variable (Q : (Scheme.projectiveSpaceOver n T).Modules) [Q.IsQuasicoherent]
variable (P : Polynomial ℚ)
variable (E : T.Modules) [E.IsQuasicoherent] (r : ℕ)

/-- The rank-to-flattening implication restricted to locally noetherian test schemes.

This is enough to obtain the same implication on all test schemes when the base is
locally noetherian and `E` is finitely presented; see
`projectiveFlatteningRankImpliesFlatHilbert_of_locallyNoetherianTests`. -/
def ProjectiveFlatteningRankImpliesFlatHilbertOnLocallyNoetherianTests : Prop :=
  ∀ (A : Over T) [IsLocallyNoetherian A.left],
    IsProjectiveOfRank r ((pullback A.hom).obj E) →
      (projectiveFamilyAt n Q A).FlatOver
          (Scheme.projectiveSpaceOverπ n A.left) ∧
        Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q A) P

/-- The converse projective-flattening-to-rank implication on arbitrary test schemes.

Unlike the rank-to-flattening direction, this does not follow formally by evaluating on
the universal ordinary rank locus.  In applications it is the remaining arbitrary-base
cohomology-and-base-change/regularity input. -/
def ProjectiveFlatteningFlatHilbertImpliesRank : Prop :=
  ∀ (A : Over T),
    ((projectiveFamilyAt n Q A).FlatOver
          (Scheme.projectiveSpaceOverπ n A.left) ∧
        Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q A) P) →
      IsProjectiveOfRank r ((pullback A.hom).obj E)

/-- Over a locally noetherian base, the rank-to-flattening implication for a finitely
presented quasicoherent rank sheaf need only be checked on locally noetherian test
schemes. -/
theorem projectiveFlatteningRankImpliesFlatHilbert_of_locallyNoetherianTests
    [IsLocallyNoetherian T] (hfp : E.IsFinitePresentation)
    (h : ProjectiveFlatteningRankImpliesFlatHilbertOnLocallyNoetherianTests
      n Q P E r) :
    ∀ (A : Over T),
      IsProjectiveOfRank r ((pullback A.hom).obj E) →
        (projectiveFamilyAt n Q A).FlatOver
            (Scheme.projectiveSpaceOverπ n A.left) ∧
          Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q A) P := by
  let hfin : ∀ U : T.affineOpens, haveI : IsAffine U.1.toScheme := U.2;
      Module.Finite ↥Γ(U.1.toScheme, ⊤)
        ↥Γ((pullback U.1.ι).obj E, ⊤) := fun U ↦ by
    have hfpPull : ((pullback U.1.ι).obj E).IsFinitePresentation :=
      isFinitePresentation_pullback_of_isFinitePresentation U.1.ι hfp
    have hfpSec : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
        Γ((pullback U.1.ι).obj E, ⊤) :=
      (Scheme.Modules.isFinitePresentation_iff_sections_affineOpens
        ((pullback U.1.ι).obj E)).mp hfpPull ⟨⊤, isAffineOpen_top _⟩
    letI : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
        Γ((pullback U.1.ι).obj E, ⊤) := hfpSec
    infer_instance
  let R : Over T := flatRankRepresentativeOfFinite E r hfin
  let repr : (flatRankFunctorOver E r).RepresentableBy R :=
    flatRankRepresentableByOfFinite E r hfin
  letI : IsImmersion R.hom :=
    flatRankRepresentativeOfFinite_hom_isImmersion E r hfin
  letI : IsLocallyNoetherian R.left :=
    LocallyOfFiniteType.isLocallyNoetherian R.hom
  let xR : (flatRankFunctorOver E r).obj (op R) := repr.homEquiv (𝟙 R)
  have hRankR : IsProjectiveOfRank r ((pullback R.hom).obj E) :=
    (locallyFactors_affineStratum_iff_isProjectiveOfRank E hfp r R).mp
      xR.down.down
  have hFamilyR :
      (projectiveFamilyAt n Q R).FlatOver
          (Scheme.projectiveSpaceOverπ n R.left) ∧
        Scheme.HasFiberwiseHilbertPolynomial (projectiveFamilyAt n Q R) P :=
    h R hRankR
  let yR : (projectiveFlatteningFunctor n Q (P := P)).obj (op R) :=
    ULift.up (PLift.up hFamilyR)
  intro A hRankA
  let xA : (flatRankFunctorOver E r).obj (op A) :=
    ULift.up (PLift.up
      ((locallyFactors_affineStratum_iff_isProjectiveOfRank E hfp r A).mpr hRankA))
  let c : A ⟶ R := repr.homEquiv.symm xA
  exact ((projectiveFlatteningFunctor n Q (P := P)).map c.op yR).down.down

/-- A locally-noetherian-test proof of rank implying projective flattening, together
with the arbitrary-test converse, supplies the single-rank datum consumed by the
projective-flattening representability API. -/
noncomputable def projectiveFlatteningSingleRankData_of_locallyNoetherianTests
    [IsLocallyNoetherian T] (hfp : E.IsFinitePresentation)
    (hRankToFamily :
      ProjectiveFlatteningRankImpliesFlatHilbertOnLocallyNoetherianTests
        n Q P E r)
    (hFamilyToRank : ProjectiveFlatteningFlatHilbertImpliesRank n Q P E r) :
    ProjectiveFlatteningSingleRankData n Q P where
  sheaf := E
  rank := r
  isQuasicoherent := inferInstance
  isFinitePresentation := hfp
  rank_iff A :=
    ⟨projectiveFlatteningRankImpliesFlatHilbert_of_locallyNoetherianTests
        n Q P E r hfp hRankToFamily A,
      hFamilyToRank A⟩

/-- The locally-noetherian-test rank implication and the arbitrary-test converse
directly produce the represented immersed projective flattening locus. -/
noncomputable def projectiveFlatteningLocusWitness_of_locallyNoetherianTests
    [IsLocallyNoetherian T] (hfp : E.IsFinitePresentation)
    (hRankToFamily :
      ProjectiveFlatteningRankImpliesFlatHilbertOnLocallyNoetherianTests
        n Q P E r)
    (hFamilyToRank : ProjectiveFlatteningFlatHilbertImpliesRank n Q P E r) :
    ProjectiveFlatteningLocusWitness n Q P :=
  (projectiveFlatteningSingleRankData_of_locallyNoetherianTests
    n Q P E r hfp hRankToFamily hFamilyToRank).toLocusWitness

end AlgebraicGeometry.Scheme.Modules

end
