module

public import StacksAndModuli.API.ProjectiveGradedNoetherianCechComplexModel
public import StacksAndModuli.API.TwistedFreeQuotCanonicalBaseChangeFromRank
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianCanonicalPackage

/-!
# Noetherian approximation interface for twisted-free Quot Čech complexes

The arbitrary-base fixed-rank theorem is reduced here to the precise noetherian-approximation
output supplied mathematically by Stacks Project tag 02JO.  On every affine chart of a Quot
family, it is enough to descend the fixed-degree graded Čech model to a noetherian coefficient
ring so that finite generation, flatness of the Čech cochains, and the uniform field-fibre
vanishing remain visible there.

Once such a model is given, noetherian Serre finiteness produces a one-term strictly perfect
replacement.  The replacement is then extended back to the original coefficient ring and
transported across the model isomorphism.  Thus no further properness, finiteness, or
base-change assumption remains after `HasAffineNoetherianTwistedFreeQuotCechModel`.

No existence claim for the noetherian model is made in this file; that assertion is exactly
the unresolved relative flat-spreading layer of 02JO.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Affine-local noetherian models for the fixed-degree Čech complexes attached to one
twisted-free quotient.  Existence is the exact relative flat-spreading input left by 02JO. -/
def HasAffineNoetherianTwistedFreeQuotCechModel
    (n r : ℕ) (l : ℤ) {T : Scheme.{u}}
    (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) : Prop :=
  ∀ U : T.affineOpens,
    let R := Γ(U.1.toScheme, ⊤)
    let gU : Spec (CommRingCat.of R) ⟶ T := U.1.toScheme.isoSpec.inv ≫ U.1.ι
    let mU := Scheme.projectiveSpaceOverMap n gU
    let QU := (Scheme.Modules.pullback mU).obj Q
    let qU := (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l gU).inv ≫
      (Scheme.Modules.pullback mU).map q
    let pU := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map qU
    let M := Proj.kernelQuotientModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (projSpecπ n R) (stdVars n R) pU
    Nonempty (GradedModule.NoetherianCechComplexModel M (d : ℤ))

/-- A noetherian Čech model on every affine chart supplies the affine strictly-perfect
replacement hypothesis consumed by the arbitrary-base pushforward-rank theorem. -/
theorem HasAffineNoetherianTwistedFreeQuotCechModel.toStrictlyPerfectReplacement
    (n r : ℕ) (l : ℤ) {T : Scheme.{u}}
    (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ)
    (H : HasAffineNoetherianTwistedFreeQuotCechModel n r l Q q d) :
    HasAffineStrictlyPerfectTwistedFreeQuotCechReplacement n r l Q q d := by
  intro U
  obtain ⟨E⟩ := H U
  exact ⟨E.strictlyPerfectReplacement⟩

/-- Uniform noetherian Čech models for all normalized twisted-free Quot data over one base.
This is the family-level formulation of the remaining 02JO existence theorem. -/
def HasUniversallyAffineNoetherianTwistedFreeQuotCechModel
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) (S : Scheme.{u}) (d : ℕ) : Prop :=
  ∀ (T : Over S)
    (a : Scheme.Modules.QuotientPullbackData
      (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (Scheme.projectiveSpaceOverπ n S) T),
    a.HasFiberwiseHilbertPolynomial P →
      HasAffineNoetherianTwistedFreeQuotCechModel n r l
        (Scheme.twistedFreeQuotientSheaf n S l r a)
        (Scheme.Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a) d

/-- Universal noetherian Čech models imply the universal affine strictly-perfect replacement
hypothesis used by the canonical Grassmannian natural-transformation package. -/
theorem HasUniversallyAffineNoetherianTwistedFreeQuotCechModel.toStrictlyPerfectReplacement
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) (S : Scheme.{u}) (d : ℕ)
    (H : HasUniversallyAffineNoetherianTwistedFreeQuotCechModel n r l P S d) :
    HasUniversallyAffineStrictlyPerfectTwistedFreeQuotCechReplacement n r l P S d := by
  intro T a hP
  exact (H T a hP).toStrictlyPerfectReplacement n r l
    (Scheme.twistedFreeQuotientSheaf n S l r a)
    (Scheme.Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a) d

set_option synthInstance.maxHeartbeats 1000000 in
-- The wrapper elaborates the three independent uniform bounds simultaneously.
set_option maxHeartbeats 4000000 in
/-- Uniform noetherian models of the affine fixed-degree Čech complexes supply all
intrinsic data for the canonical twisted-free Quot-to-Grassmannian transformation.  Thus the
only additional input, beyond the already formalized uniform regularity bounds, is the
relative flat-spreading assertion encoded by the noetherian models. -/
theorem
    exists_bound_twistedFreeQuotGrassmannianQuotientNatTransData_of_noetherianCechModel
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (S : Scheme.{u})
      (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)), d₀ ≤ (d : ℤ) →
      ∀ {m : ℕ}
        (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)),
      HasUniversallyAffineNoetherianTwistedFreeQuotCechModel n r l P S d →
        Nonempty (Scheme.TwistedFreeQuotGrassmannianQuotientNatTransData
          n S l r P d e he m (P.hilbertNatValue d) σ) := by
  obtain ⟨d₀, hd₀0, H⟩ :=
    exists_bound_twistedFreeQuotGrassmannianQuotientNatTransData_of_strictlyPerfectReplacement
      n r hn l P
  refine ⟨d₀, hd₀0, ?_⟩
  intro S d e he hd m σ hmodel
  exact H S d e he hd σ
    (hmodel.toStrictlyPerfectReplacement n r l P S d)

set_option synthInstance.maxHeartbeats 1000000 in
-- The constructor retains the canonical CBC morphism while elaborating all uniform bounds.
set_option maxHeartbeats 4000000 in
/-- Uniform noetherian Čech models retain the canonical base-change witness needed by the
fixed-degree Grassmannian input package.  A single Quot point over a nonempty scheme supplies
the numerical rank inequality; without this witness the universal family assertion may be
vacuous. -/
theorem
    exists_bound_twistedFreeQuotGrassmannianCanonicalInputs_of_noetherianCechModel
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (S : Scheme.{u})
      (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)), d₀ ≤ (d : ℤ) →
      ∀ {m : ℕ}
        (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)),
      HasUniversallyAffineNoetherianTwistedFreeQuotCechModel n r l P S d →
      ∀ (T : Over S)
        (a : Scheme.Modules.QuotientPullbackData
          (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
            (n := n) (r := r) (l := l))
          (Scheme.projectiveSpaceOverπ n S) T),
        a.HasFiberwiseHilbertPolynomial P → Nonempty T.left →
        Nonempty (Scheme.TwistedFreeQuotGrassmannianCanonicalInputs
          n S l r P d e he m (P.hilbertNatValue d) σ) := by
  obtain ⟨dRank, hdRank0, hRank⟩ :=
    exists_bound_twistedFreeQuot_pushforward_isProjectiveOfRank_of_strictlyPerfectReplacement
      n r hn l P
  obtain ⟨dGen, hdGen0, hGen⟩ :=
    exists_bound_surjective_twistedFreeQuotGrassmannianFreeMap_arbitrary_of_universalRank
      n r l P
  obtain ⟨dBC, hdBC0, hBC⟩ :=
    exists_bound_twistedFreeQuotientTwistPushforwardBaseChange_isIso_of_universalRank
      n r l P
  refine ⟨max dRank (max dGen dBC), by omega, ?_⟩
  intro S d e he hd m σ hmodel T a hP hT
  have hdRank : dRank ≤ (d : ℤ) := le_trans (le_max_left _ _) hd
  have hdGen : dGen ≤ (d : ℤ) :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hd
  have hdBC : dBC ≤ (d : ℤ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hd
  let hperfect := hmodel.toStrictlyPerfectReplacement n r l P S d
  have hM : ∀ (T : Over S)
      (a : Scheme.Modules.QuotientPullbackData
        (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l))
        (Scheme.projectiveSpaceOverπ n S) T),
      a.HasFiberwiseHilbertPolynomial P →
        Scheme.Modules.IsProjectiveOfRank (P.hilbertNatValue d)
          (Scheme.twistedFreeQuotientTwistPushforward n S l r a d) := by
    intro T a hP
    let Q := Scheme.twistedFreeQuotientSheaf n S l r a
    let q :=
      Scheme.Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a
    haveI : Q.IsFinitePresentation :=
      Scheme.Modules.QuotientPullbackData.quotDataOnProjectiveSpace_isFinitePresentation_over
        T a
    haveI : Epi q :=
      Scheme.Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_epi T a
    have hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n T.left) :=
      Scheme.Modules.QuotientPullbackData.quotDataOnProjectiveSpace_flatOver_over T a
    exact hRank T.left Q (by infer_instance) q (by infer_instance)
      hflat hP d hdRank (hperfect T a hP)
  have hsurj := hGen S d e he hdGen σ hM
  have hbaseChange := hBC S d e he hdBC σ hM
  let p := Scheme.twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ
  let M := Scheme.twistedFreeQuotientTwistPushforward n S l r a d
  letI : M.IsQuasicoherent :=
    Scheme.twistedFreeQuotientTwistPushforward_isQuasicoherent n S l r a d
  have hsurjT : ∀ U : T.left.affineOpens,
      Function.Surjective (Scheme.Modules.finFreeSectionsMap' p U.1) :=
    hsurj T a hP
  letI : Epi p := Scheme.Modules.epi_of_surjective_on_affineOpens p
    (Scheme.Modules.hom_app_surjective_of_finFreeSectionsMap'_surjective p hsurjT)
  have hle : P.hilbertNatValue d ≤ m :=
    (hM T a hP).rank_le_of_epi_finFree p hT
  exact ⟨
    { isProjectiveOfRank := hM
      baseChange_isIso := fun {T T'} g a hP ↦ hbaseChange T a hP T' g
      surjective := hsurj
      rank_le := hle }⟩

end AlgebraicGeometry.ProjectiveSpace

end

end
