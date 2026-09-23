module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalFlatteningLocus
public import StacksAndModuli.API.TwistedFreeQuotPushforwardRank
public import StacksAndModuli.API.ProjectiveReconstructedGotzmannPersistence

/-!
# Finiteness around the universal Grassmannian reconstruction

The base of the universal free-Grassmannian family is locally Noetherian whenever the
original base is: the relative Grassmannian is strongly projective, hence locally of
finite type.  Its reconstructed projective family is quasicoherent and finitely
presented over an arbitrary base.

This file also extracts a useful consequence of the kernel-quotient Cech model.  Over a
Noetherian affine base, every twist of a finitely presented quotient of a finite
twisted-free sheaf has finite global sections, without any flatness hypothesis.  Thus
the corresponding projective pushforward is finitely presented.  This supplies the two
finite-presentation fields in a one-step projective-flattening presentation; the
remaining inputs are the base-change/regularity and Gotzmann-persistence assertions.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

open Modules.QuotientPullbackData

/-- A free relative Grassmannian over a locally Noetherian scheme is locally
Noetherian.  The hypothesis on the base is essential: strong projectivity only gives
local finite type over the base. -/
theorem grassmannianOverRepresentation_isLocallyNoetherian
    (S : Scheme.{u}) [IsLocallyNoetherian S] (q m : ℕ) (hqm : q ≤ m) :
    IsLocallyNoetherian (grassmannianOverRepresentation S q m).left := by
  obtain ⟨N, i, hi, hcomp⟩ :=
    grassmannianOverRepresentation_isHProjective_of_le S q m hqm
  letI : IsClosedImmersion i := hi
  have hfinite : LocallyOfFiniteType
      (i ≫ projectiveSpaceOverπ N S) := inferInstance
  rw [hcomp] at hfinite
  letI : LocallyOfFiniteType (grassmannianOverRepresentation S q m).hom :=
    hfinite
  exact LocallyOfFiniteType.isLocallyNoetherian
    (grassmannianOverRepresentation S q m).hom

variable {S : Scheme.{u}} {n r m q : ℕ} {l : ℤ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
  {σ : ULift.{u} (Fin m) ≃
    ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- The reconstructed projective family attached to the universal point of a
free relative Grassmannian. -/
noncomputable abbrev freeGrassmannianUniversalReconstructedQuotient
    (S : Scheme.{u}) (n r q m : ℕ) (l : ℤ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    (projectiveSpaceOver n
      (grassmannianOverRepresentation S q m).left).Modules :=
  grassmannianPointReconstructedQuotient
    (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
      (he := he) (σ := σ)
      (grassmannianOverRepresentation S q m)
      (freeGrassmannianUniversalPoint S q m)

/-- The canonical twisted-free quotient map onto the reconstructed projective
family attached to the universal free-Grassmannian point. -/
noncomputable abbrev freeGrassmannianUniversalReconstructedQuotientMap
    (S : Scheme.{u}) (n r q m : ℕ) (l : ℤ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n
      (grassmannianOverRepresentation S q m).left (-l)) ⟶
      freeGrassmannianUniversalReconstructedQuotient
        S n r q m l d e he σ :=
  grassmannianPointReconstructedQuotientMap
    (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
      (he := he) (σ := σ)
      (grassmannianOverRepresentation S q m)
      (freeGrassmannianUniversalPoint S q m)

/-- The quotient reconstructed from the universal free-Grassmannian point is
quasicoherent over an arbitrary base. -/
theorem freeGrassmannianUniversalReconstructedQuotient_isQuasicoherent :
    (grassmannianPointReconstructedQuotient
      (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
        (he := he) (σ := σ)
        (grassmannianOverRepresentation S q m)
        (freeGrassmannianUniversalPoint S q m)).IsQuasicoherent := by
  infer_instance

/-- The quotient reconstructed from the universal free-Grassmannian point is finitely
presented over an arbitrary base. -/
theorem freeGrassmannianUniversalReconstructedQuotient_isFinitePresentation :
    (grassmannianPointReconstructedQuotient
      (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
        (he := he) (σ := σ)
        (grassmannianOverRepresentation S q m)
        (freeGrassmannianUniversalPoint S q m)).IsFinitePresentation := by
  infer_instance

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
-- The graded Cech comparison has a deep projective-sheaf instance search.
/-- On a Noetherian affine base, every twist of a finitely presented quotient of a
finite twisted-free sheaf has finite global sections.  No flatness or Hilbert-polynomial
hypothesis is needed. -/
theorem twistedFreeQuot_globalSections_finite
    (n r : ℕ) (hn : 0 < n) (l : ℤ)
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
    [Epi q] (d : ℕ) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    Module.Finite R
      (Scheme.Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) := by
  haveI hAmb : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)).IsFinitePresentation :=
    Scheme.twistedFreeAmbient_isFinitePresentation n (Spec (.of R)) l r
  let E := projAmbient n r l (R := R)
  let G := (Scheme.Modules.pullback
    (projectiveSpaceOverSpecIso n R).inv).obj Q
  let p := (Scheme.Modules.pullback
    (projectiveSpaceOverSpecIso n R).inv).map q
  haveI hp : Epi p := inferInstance
  haveI hEfp : E.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hGfp : G.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hEqc : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E a).IsQuasicoherent :=
    fun a ↦ twistModule_std_isQuasicoherent _ a
  haveI hGqc : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) G a).IsQuasicoherent :=
    fun a ↦ twistModule_std_isQuasicoherent _ a
  have hKqc : (kernel p).IsQuasicoherent :=
    Scheme.Modules.kernel_isQuasicoherent p
  letI : (kernel p).IsQuasicoherent := hKqc
  haveI hKtwistQc : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) a).IsQuasicoherent :=
    fun a ↦ twistModule_std_isQuasicoherent_of_isQuasicoherent n _ a
  let M := Proj.kernelQuotientModule
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (projSpecπ n R) (stdVars n R) p
  have hMfg : GradedModule.IsFG M :=
    isFG_kernelQuotientModule_twistedFree_arbitrary n r hn l R Q q
  let C := cechSchemeGlobalSectionsComparisonQuotientModel_arbitrary n R Q p
  have hdC : C.bound ≤ d := by
    simp [C, cechSchemeGlobalSectionsComparisonQuotientModel_arbitrary]
  haveI hfiniteM : Module.Finite R ((M.cechHgr 0).obj (d : ℤ)) :=
    GradedModule.finiteDimensional_cechHgr_of_isFG M hMfg 0 (d : ℤ)
  letI := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
    (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
  exact Module.Finite.equiv (C.globalSectionsIso d hdC)

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
-- Transporting finiteness through affine global sections has deep instance search.
/-- On a Noetherian affine base, the pushforward of every twist of a finitely
presented twisted-free quotient is finitely presented. -/
theorem twistedFreeQuot_pushforward_twist_isFinitePresentation_spec
    (n r : ℕ) (hn : 0 < n) (l : ℤ)
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
    [Epi q] (d : ℕ) :
    ((Scheme.Modules.pushforward
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))).obj
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).IsFinitePresentation := by
  let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
  let M := (Scheme.Modules.pushforward
    (Scheme.projectiveSpaceOverπ n (Spec (.of R)))).obj Qd
  haveI hMQc : M.IsQuasicoherent := by
    dsimp only [M]
    infer_instance
  have hfin :
      letI := Scheme.Modules.globalSectionsModule
        (Scheme.projectiveSpaceOverπ n (Spec (.of R))) Qd
      Module.Finite R Γ(Qd, ⊤) :=
    twistedFreeQuot_globalSections_finite n r hn l R Q q d
  have hfp : Module.FinitePresentation R
      ((AlgebraicGeometry.moduleSpecΓFunctor (R := CommRingCat.of R)).obj M) := by
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R))) Qd
    haveI : Module.Finite R Γ(Qd, ⊤) := hfin
    change Module.FinitePresentation R Γ(Qd, ⊤)
    exact Module.finitePresentation_of_finite R _
  letI : Module.FinitePresentation R
      ((AlgebraicGeometry.moduleSpecΓFunctor (R := CommRingCat.of R)).obj M) := hfp
  exact AlgebraicGeometry.isFinitePresentation_of_moduleSpecΓFunctor
    (R := CommRingCat.of R) M

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite presentation of a quasicoherent module sheaf can be checked after
pullback to every affine open of the scheme. -/
theorem isFinitePresentation_of_affineOpen_pullbacks
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    (hM : ∀ U : X.affineOpens,
      ((pullback U.1.ι).obj M).IsFinitePresentation) :
    M.IsFinitePresentation := by
  let presData (U : X.affineOpens) :
      { P : SheafOfModules.Presentation (M.restrict U.1.ι) // P.IsFinite } := by
    have hRestrict : (M.restrict U.1.ι).IsFinitePresentation :=
      ObjectProperty.prop_of_iso
        (P := SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf)
        ((restrictFunctorIsoPullback U.1.ι).app M).symm (hM U)
    letI : (M.restrict U.1.ι).IsFinitePresentation := hRestrict
    let h := exists_finitePresentation_of_isFinitePresentation_affine
      (M.restrict U.1.ι)
    exact ⟨Classical.choose h, Classical.choose_spec h⟩
  let pres (U : X.affineOpens) :
      SheafOfModules.Presentation (M.restrict U.1.ι) := (presData U).1
  letI (U : X.affineOpens) : (pres U).IsFinite := (presData U).2
  exact isFinitePresentation_of_isOpenCover M
    (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X) pres

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2500000 in
-- Comparing projective pushforwards across the affine-base isomorphism is expensive.
/-- On an affine locally Noetherian base, the pushforward of every twist of a
finitely presented twisted-free quotient is finitely presented. -/
theorem twistedFreeQuot_pushforward_twist_isFinitePresentation_of_isAffine
    (n r : ℕ) (hn : 0 < n) (l : ℤ)
    (B : Scheme.{u}) [IsAffine B] [IsLocallyNoetherian B]
    (Q : (Scheme.projectiveSpaceOver n B).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n B (-l)) ⟶ Q)
    [Epi q] (d : ℕ) :
    ((Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n B)).obj
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).IsFinitePresentation := by
  let R := Γ(B, ⊤)
  haveI hR : IsNoetherianRing R :=
    IsLocallyNoetherian.component_noetherian
      ⟨⊤, AlgebraicGeometry.isAffineOpen_top B⟩
  let g : Spec (CommRingCat.of R) ⟶ B := B.isoSpec.inv
  let m := Scheme.projectiveSpaceOverMap n g
  haveI : IsOpenImmersion g := inferInstance
  haveI : IsOpenImmersion m := inferInstance
  let QU := (Scheme.Modules.pullback m).obj Q
  haveI hQUfp : QU.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  let qU := (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l g).inv ≫
    (Scheme.Modules.pullback m).map q
  haveI hqU : Epi qU := epi_comp _ _
  have hSpec : ((Scheme.Modules.pushforward
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))).obj
      (Scheme.projectiveSpaceOverTwistModule QU (d : ℤ))).IsFinitePresentation :=
    twistedFreeQuot_pushforward_twist_isFinitePresentation_spec
      n r hn l R QU qU d
  let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
  let QUd := Scheme.projectiveSpaceOverTwistModule QU (d : ℤ)
  let M := (Scheme.Modules.pushforward
    (Scheme.projectiveSpaceOverπ n B)).obj Qd
  let eQ : (Scheme.Modules.restrictFunctor m).obj Qd ≅ QUd :=
    (Scheme.Modules.restrictFunctorIsoPullback m).app Qd ≪≫
      Scheme.projectiveSpaceOverTwistModule_pullbackIso_of_isOpenImmersion
        n g Q (d : ℤ)
  let eM : (Scheme.Modules.restrictFunctor g).obj M ≅
      (Scheme.Modules.pushforward
        (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))).obj QUd :=
    Scheme.projectiveSpacePushforwardRestrictIso' n g Qd ≪≫
      (Scheme.Modules.pushforward
        (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))).mapIso eQ
  have hRestrict : ((Scheme.Modules.restrictFunctor g).obj M).IsFinitePresentation :=
    ObjectProperty.prop_of_iso
      (P := SheafOfModules.isFinitePresentation
        (Spec (CommRingCat.of R)).ringCatSheaf) eM.symm hSpec
  have hPull : ((Scheme.Modules.pullback g).obj M).IsFinitePresentation :=
    ObjectProperty.prop_of_iso
      (P := SheafOfModules.isFinitePresentation
        (Spec (CommRingCat.of R)).ringCatSheaf)
      ((Scheme.Modules.restrictFunctorIsoPullback g).app M) hRestrict
  letI : ((Scheme.Modules.pullback g).obj M).IsFinitePresentation := hPull
  have hBack : ((Scheme.Modules.pullback B.isoSpec.hom).obj
      ((Scheme.Modules.pullback g).obj M)).IsFinitePresentation := by
    infer_instance
  let eBack : (Scheme.Modules.pullback B.isoSpec.hom).obj
      ((Scheme.Modules.pullback g).obj M) ≅ M :=
    (Scheme.Modules.pullbackComp B.isoSpec.hom B.isoSpec.inv).app M ≪≫
      (Scheme.Modules.pullbackCongr B.isoSpec.hom_inv_id).app M ≪≫
      (Scheme.Modules.pullbackId B).app M
  exact ObjectProperty.prop_of_iso
    (P := SheafOfModules.isFinitePresentation B.ringCatSheaf) eBack hBack

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 3000000 in
-- Affine-open descent for the projective pushforward has deep instance search.
/-- Over a locally Noetherian base, the pushforward of every twist of a finitely
presented twisted-free quotient is finitely presented. -/
theorem twistedFreeQuot_pushforward_twist_isFinitePresentation
    (n r : ℕ) (hn : 0 < n) (l : ℤ)
    (T : Scheme.{u}) [IsLocallyNoetherian T]
    (Q : (Scheme.projectiveSpaceOver n T).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi q] (d : ℕ) :
    ((Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n T)).obj
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).IsFinitePresentation := by
  let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
  let M := (Scheme.Modules.pushforward
    (Scheme.projectiveSpaceOverπ n T)).obj Qd
  haveI hMQc : M.IsQuasicoherent := by
    dsimp only [M]
    infer_instance
  apply Scheme.Modules.isFinitePresentation_of_affineOpen_pullbacks M
  intro U
  let B := U.1.toScheme
  haveI hBaff : IsAffine B := U.2
  haveI hBnoeth : IsLocallyNoetherian B :=
    isLocallyNoetherian_of_isOpenImmersion U.1.ι
  let mU := Scheme.projectiveSpaceOverMap n U.1.ι
  let QU := (Scheme.Modules.pullback mU).obj Q
  haveI hQUfp : QU.IsFinitePresentation := by
    exact Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation
      mU inferInstance
  let qU := (Scheme.projectiveSpaceOverTwistedFree_pullbackIso
      n r l U.1.ι).inv ≫ (Scheme.Modules.pullback mU).map q
  haveI hqU : Epi qU := epi_comp _ _
  have hU : ((Scheme.Modules.pushforward
      (Scheme.projectiveSpaceOverπ n B)).obj
      (Scheme.projectiveSpaceOverTwistModule QU (d : ℤ))).IsFinitePresentation :=
    twistedFreeQuot_pushforward_twist_isFinitePresentation_of_isAffine
      n r hn l B QU qU d
  let eQ : (Scheme.Modules.restrictFunctor mU).obj Qd ≅
      Scheme.projectiveSpaceOverTwistModule QU (d : ℤ) :=
    (Scheme.Modules.restrictFunctorIsoPullback mU).app Qd ≪≫
      Scheme.projectiveSpaceOverTwistModule_pullbackIso_of_isOpenImmersion
        n U.1.ι Q (d : ℤ)
  let eM : (Scheme.Modules.pullback U.1.ι).obj M ≅
      (Scheme.Modules.pushforward (Scheme.projectiveSpaceOverπ n B)).obj
        (Scheme.projectiveSpaceOverTwistModule QU (d : ℤ)) :=
    ((Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app M).symm ≪≫
      Scheme.projectiveSpacePushforwardRestrictIso n U.1 Qd ≪≫
      (Scheme.Modules.pushforward
        (Scheme.projectiveSpaceOverπ n B)).mapIso eQ
  exact ObjectProperty.prop_of_iso
    (P := SheafOfModules.isFinitePresentation B.ringCatSheaf) eM.symm hU

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

open Modules.QuotientPullbackData

variable {S : Scheme.{u}} {n r m q : ℕ} {l : ℤ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
  {σ : ULift.{u} (Fin m) ≃
    ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- Every twist pushforward of the projective family reconstructed from the
universal free-Grassmannian point is finitely presented over a locally
Noetherian base. -/
theorem freeGrassmannianUniversalReconstructedQuotient_pushforward_isFinitePresentation
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (n r q m : ℕ) (hqm : q ≤ m) (hn : 0 < n)
    (l : ℤ) (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (t : ℕ) :
    (Modules.projectiveTwistedPushforward n
      (freeGrassmannianUniversalReconstructedQuotient
        S n r q m l d e he σ) t).IsFinitePresentation := by
  let G := grassmannianOverRepresentation S q m
  letI : IsLocallyNoetherian G.left :=
    grassmannianOverRepresentation_isLocallyNoetherian S q m hqm
  let Q := freeGrassmannianUniversalReconstructedQuotient
    S n r q m l d e he σ
  let p := freeGrassmannianUniversalReconstructedQuotientMap
    S n r q m l d e he σ
  haveI : Q.IsFinitePresentation := by
    dsimp only [Q, freeGrassmannianUniversalReconstructedQuotient]
    infer_instance
  haveI : Epi p := by
    dsimp only [p, freeGrassmannianUniversalReconstructedQuotientMap]
    infer_instance
  exact ProjectiveSpace.twistedFreeQuot_pushforward_twist_isFinitePresentation
    n r hn l G.left Q p t

/-- On a locally Noetherian base, the universal Grassmannian reconstruction
has a represented immersed flattening locus as soon as the four substantive
one-step comparison and persistence inputs are available.  The adjacent
finite-presentation hypotheses are automatic. -/
noncomputable def freeGrassmannianUniversalProjectiveFlatteningLocusWitness_of_gotzmannGrowthEpi
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (n r q m : ℕ) (hqm : q ≤ m) (hn : 0 < n)
    (l : ℤ) (P : Polynomial ℚ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n))
    (C : Modules.ProjectiveOneStepMultiplicationBaseChangeComparison n
      (freeGrassmannianUniversalReconstructedQuotient
        S n r q m l d e he σ) d)
    (hranks : Modules.ProjectiveOneStepActualRanksAndEpi n
      (freeGrassmannianUniversalReconstructedQuotient
        S n r q m l d e he σ) P d)
    (hgrowth : ∀ A : Over (grassmannianOverRepresentation S q m).left,
      Modules.ProjectiveOneStepFieldGrowthEpi n
        (Modules.projectiveFamilyAt n
          (freeGrassmannianUniversalReconstructedQuotient
            S n r q m l d e he σ) A) P d)
    (hflat : Modules.ProjectiveOneStepFlatnessPersistenceEpi n
      (freeGrassmannianUniversalReconstructedQuotient
        S n r q m l d e he σ) P d) :
    Modules.ProjectiveFlatteningLocusWitness n
      (freeGrassmannianUniversalReconstructedQuotient
        S n r q m l d e he σ) P := by
  let Q := freeGrassmannianUniversalReconstructedQuotient
    S n r q m l d e he σ
  letI : Q.IsQuasicoherent := by
    dsimp only [Q, freeGrassmannianUniversalReconstructedQuotient]
    infer_instance
  have hfp₀ : (Modules.projectiveTwistedPushforward n Q d).IsFinitePresentation :=
    freeGrassmannianUniversalReconstructedQuotient_pushforward_isFinitePresentation
      S n r q m hqm hn l d e he σ d
  have hfp₁ :
      (Modules.projectiveTwistedPushforward n Q (d + 1)).IsFinitePresentation :=
    freeGrassmannianUniversalReconstructedQuotient_pushforward_isFinitePresentation
      S n r q m hqm hn l d e he σ (d + 1)
  exact Modules.ProjectiveFlatteningLocusWitness.ofFiniteRankPresentation n Q P
    (Modules.projectiveFlatteningHasFiniteRankPresentation_of_gotzmannGrowthEpi
      hfp₀ hfp₁ C hranks hgrowth hflat)

/-- The universal reconstructed family used by the eventual twisted-free Quot
construction, with its canonical monomial indexing and Hilbert rank. -/
noncomputable abbrev twistedFreeQuotUniversalReconstructedQuotient
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    (projectiveSpaceOver n
      (grassmannianOverRepresentation S (P.hilbertNatValue d)
        (r * (n + e).choose n)).left).Modules :=
  freeGrassmannianUniversalReconstructedQuotient S n r
    (P.hilbertNatValue d) (r * (n + e).choose n) l d e he
    (twistedFreeMonomialIndexEquiv r ((n + e).choose n))

/-- The four one-step geometric inputs which remain after finite presentation
of the universal Grassmannian reconstruction and its adjacent pushforwards
have been established. -/
structure TwistedFreeQuotUniversalOneStepFlatteningGeometry
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) : Type (u + 1) where
  /-- Base change for the two adjacent pushforwards and their multiplication. -/
  multiplicationBaseChange :
    Modules.ProjectiveOneStepMultiplicationBaseChangeComparison n
      (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) d
  /-- Forward rank and multiplication-surjectivity in the flat Hilbert locus. -/
  actualRanksAndEpi : Modules.ProjectiveOneStepActualRanksAndEpi n
    (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) P d
  /-- Field-valued exact Hilbert-function growth after every base change. -/
  fieldGrowth :
    ∀ A : Over (grassmannianOverRepresentation S (P.hilbertNatValue d)
      (r * (n + e).choose n)).left,
      Modules.ProjectiveOneStepFieldGrowthEpi n
        (Modules.projectiveFamilyAt n
          (twistedFreeQuotUniversalReconstructedQuotient
            n S l r P d e he) A) P d
  /-- Relative flatness persistence from the one-step rank conditions. -/
  flatnessPersistence : Modules.ProjectiveOneStepFlatnessPersistenceEpi n
    (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) P d

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

open Modules.QuotientPullbackData

/-- Canonical Quot-to-Grassmannian rank data in degrees `d` and `d+1`
supplies both rank assertions in the forward one-step package.  Thus only
surjectivity of degree-one multiplication remains from relative regularity. -/
theorem twistedFreeQuotUniversal_actualRanksAndEpi_of_canonicalInputs
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (I₀ : TwistedFreeQuotGrassmannianCanonicalInputs n S l r P d e he
      (r * (n + e).choose n) (P.hilbertNatValue d)
      (twistedFreeMonomialIndexEquiv r ((n + e).choose n)))
    (I₁ : TwistedFreeQuotGrassmannianCanonicalInputs n S l r P
      (d + 1) (e + 1) (by omega)
      (r * (n + (e + 1)).choose n) (P.hilbertNatValue (d + 1))
      (twistedFreeMonomialIndexEquiv r ((n + (e + 1)).choose n)))
    (hmul : ∀ A : Over (grassmannianOverRepresentation S
      (P.hilbertNatValue d) (r * (n + e).choose n)).left,
      let QA := Modules.projectiveFamilyAt n
        (twistedFreeQuotUniversalReconstructedQuotient
          n S l r P d e he) A
      QA.FlatOver (projectiveSpaceOverπ n A.left) ∧
          HasFiberwiseHilbertPolynomial QA P →
        Epi (Modules.projectiveTwistedPushforwardMul n QA d)) :
    Modules.ProjectiveOneStepActualRanksAndEpi n
      (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he)
      P d := by
  intro A hfamily
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
  haveI : QA.IsQuasicoherent := by
    dsimp only [QA, Modules.projectiveFamilyAt]
    infer_instance
  haveI : QA.IsFinitePresentation := by
    dsimp only [QA, Modules.projectiveFamilyAt]
    infer_instance
  haveI : Epi pA := by
    dsimp only [pA]
    infer_instance
  let b := Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace
    (n := n) (r := r) (l := l) T QA (by infer_instance) hfamily.1 pA
  let hPb :=
    ofTwistedFreeQuotientOnProjectiveSpace_hasFiberwiseHilbertPolynomial
      T QA (by infer_instance) hfamily.1 pA P hfamily.2
  let E := ofTwistedFreeQuotientOnProjectiveSpace_quotDataIso
      (n := n) (r := r) (l := l) T QA (by infer_instance) hfamily.1 pA
  let E₀ := (Modules.pushforward (projectiveSpaceOverπ n A.left)).mapIso
    (Modules.tensorLeftIso E
      (projectiveSpaceOverTwist n A.left (d : ℤ)))
  let E₁ := (Modules.pushforward (projectiveSpaceOverπ n A.left)).mapIso
    (Modules.tensorLeftIso E
      (projectiveSpaceOverTwist n A.left ((d + 1 : ℕ) : ℤ)))
  have h₀ : Modules.IsProjectiveOfRank (P.hilbertNatValue d)
      (Modules.projectiveTwistedPushforward n QA d) :=
    (I₀.isProjectiveOfRank T b hPb).of_iso E₀
  have h₁ : Modules.IsProjectiveOfRank (P.hilbertNatValue (d + 1))
      (Modules.projectiveTwistedPushforward n QA (d + 1)) :=
    (I₁.isProjectiveOfRank T b hPb).of_iso E₁
  exact ⟨h₀, h₁, hmul A hfamily⟩

/-- Eventual canonical inputs reduce the eventual forward one-step package to
the usual uniform multiplication-surjectivity theorem. -/
theorem exists_eventual_twistedFreeQuotUniversal_actualRanksAndEpi
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hinputs : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotGrassmannianCanonicalInputs
          n S l r P d e he (r * (n + e).choose n)
            (P.hilbertNatValue d)
            (twistedFreeMonomialIndexEquiv r ((n + e).choose n))))
    (hmul : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
        (A : Over (grassmannianOverRepresentation S
          (P.hilbertNatValue d) (r * (n + e).choose n)).left),
        let QA := Modules.projectiveFamilyAt n
          (twistedFreeQuotUniversalReconstructedQuotient
            n S l r P d e he) A
        QA.FlatOver (projectiveSpaceOverπ n A.left) ∧
            HasFiberwiseHilbertPolynomial QA P →
          Epi (Modules.projectiveTwistedPushforwardMul n QA d)) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Modules.ProjectiveOneStepActualRanksAndEpi n
          (twistedFreeQuotUniversalReconstructedQuotient
            n S l r P d e he) P d := by
  obtain ⟨DI, hI⟩ := hinputs
  obtain ⟨DM, hM⟩ := hmul
  refine ⟨max DI DM, ?_⟩
  intro d hd e he
  have hdI : DI ≤ d := le_trans (le_max_left DI DM) hd
  have hdM : DM ≤ d := le_trans (le_max_right DI DM) hd
  obtain ⟨I₀⟩ := hI d hdI e he
  obtain ⟨I₁⟩ := hI (d + 1) (by omega) (e + 1) (by omega)
  exact twistedFreeQuotUniversal_actualRanksAndEpi_of_canonicalInputs
    n S l r P d e he I₀ I₁ (hM d hdM e he)

/-- The one-step universal geometry after removing the adjacent-rank assertions
which are already forced by canonical inputs in degrees `d` and `d+1`. -/
structure TwistedFreeQuotUniversalReducedOneStepFlatteningGeometry
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) : Type (u + 1) where
  /-- Base change for the two adjacent pushforwards and their multiplication. -/
  multiplicationBaseChange :
    Modules.ProjectiveOneStepMultiplicationBaseChangeComparison n
      (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) d
  /-- Surjectivity of degree-one multiplication on every flat fixed-polynomial
  base change. -/
  multiplicationEpi :
    ∀ A : Over (grassmannianOverRepresentation S (P.hilbertNatValue d)
      (r * (n + e).choose n)).left,
      let QA := Modules.projectiveFamilyAt n
        (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) A
      QA.FlatOver (projectiveSpaceOverπ n A.left) ∧
          HasFiberwiseHilbertPolynomial QA P →
        Epi (Modules.projectiveTwistedPushforwardMul n QA d)
  /-- Field-valued exact Hilbert-function growth after every base change. -/
  fieldGrowth :
    ∀ A : Over (grassmannianOverRepresentation S (P.hilbertNatValue d)
      (r * (n + e).choose n)).left,
      Modules.ProjectiveOneStepFieldGrowthEpi n
        (Modules.projectiveFamilyAt n
          (twistedFreeQuotUniversalReconstructedQuotient
            n S l r P d e he) A) P d
  /-- Relative flatness persistence from the one-step rank conditions. -/
  flatnessPersistence : Modules.ProjectiveOneStepFlatnessPersistenceEpi n
    (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) P d

/-- Canonical inputs in two adjacent degrees fill the only omitted field of the
reduced one-step universal geometry. -/
noncomputable def
    TwistedFreeQuotUniversalReducedOneStepFlatteningGeometry.toGeometry
    {n : ℕ} {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
    {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
    (G : TwistedFreeQuotUniversalReducedOneStepFlatteningGeometry
      n S l r P d e he)
    (I₀ : TwistedFreeQuotGrassmannianCanonicalInputs n S l r P d e he
      (r * (n + e).choose n) (P.hilbertNatValue d)
      (twistedFreeMonomialIndexEquiv r ((n + e).choose n)))
    (I₁ : TwistedFreeQuotGrassmannianCanonicalInputs n S l r P
      (d + 1) (e + 1) (by omega)
      (r * (n + (e + 1)).choose n) (P.hilbertNatValue (d + 1))
      (twistedFreeMonomialIndexEquiv r ((n + (e + 1)).choose n))) :
    TwistedFreeQuotUniversalOneStepFlatteningGeometry
      n S l r P d e he where
  multiplicationBaseChange := G.multiplicationBaseChange
  actualRanksAndEpi :=
    twistedFreeQuotUniversal_actualRanksAndEpi_of_canonicalInputs
      n S l r P d e he I₀ I₁ G.multiplicationEpi
  fieldGrowth := G.fieldGrowth
  flatnessPersistence := G.flatnessPersistence

/-- Canonical fixed-degree Quot-to-Grassmannian inputs and the four remaining
one-step geometric assertions produce the universal flattening witness.  The
numerical `rank_le` field is exactly what makes the universal Grassmannian
locally Noetherian. -/
noncomputable def TwistedFreeQuotUniversalOneStepFlatteningGeometry.toWitness
    (S : Scheme.{u}) [IsLocallyNoetherian S] (n : ℕ) (hn : 0 < n)
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ))
    (I : TwistedFreeQuotGrassmannianCanonicalInputs n S l r P d e he
      (r * (n + e).choose n) (P.hilbertNatValue d)
      (twistedFreeMonomialIndexEquiv r ((n + e).choose n)))
    (G : TwistedFreeQuotUniversalOneStepFlatteningGeometry
      n S l r P d e he) :
    Modules.ProjectiveFlatteningLocusWitness n
      (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) P :=
  freeGrassmannianUniversalProjectiveFlatteningLocusWitness_of_gotzmannGrowthEpi
    S n r (P.hilbertNatValue d) (r * (n + e).choose n) I.rank_le hn
      l P d e he (twistedFreeMonomialIndexEquiv r ((n + e).choose n))
      G.multiplicationBaseChange G.actualRanksAndEpi G.fieldGrowth
      G.flatnessPersistence

/-- Eventual canonical fixed-degree inputs and eventual one-step geometry
supply exactly the universal flattening-witness hypothesis consumed by the
eventual Quot-to-Grassmannian immersion package. -/
theorem exists_eventual_twistedFreeQuotUniversalFlatteningLocusWitness
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S] (hn : 0 < n)
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hinputs : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotGrassmannianCanonicalInputs
          n S l r P d e he (r * (n + e).choose n)
            (P.hilbertNatValue d)
            (twistedFreeMonomialIndexEquiv r ((n + e).choose n))))
    (hgeometry : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotUniversalOneStepFlatteningGeometry
          n S l r P d e he)) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (Modules.ProjectiveFlatteningLocusWitness n
          (grassmannianPointReconstructedQuotient
            (n := n) (r := r) (q := P.hilbertNatValue d) (l := l)
              (d := d) (e := e) (he := he)
              (σ := twistedFreeMonomialIndexEquiv r ((n + e).choose n))
              (grassmannianOverRepresentation S (P.hilbertNatValue d)
                (r * (n + e).choose n))
              (freeGrassmannianUniversalPoint S (P.hilbertNatValue d)
                (r * (n + e).choose n))) P) := by
  obtain ⟨DI, hI⟩ := hinputs
  obtain ⟨DG, hG⟩ := hgeometry
  refine ⟨max DI DG, ?_⟩
  intro d hd e he
  obtain ⟨I⟩ := hI d (le_trans (le_max_left DI DG) hd) e he
  obtain ⟨G⟩ := hG d (le_trans (le_max_right DI DG) hd) e he
  exact ⟨G.toWitness S n hn l r P d e he I⟩

/-- Eventual canonical inputs and reduced one-step geometry supply the
universal flattening witnesses, with adjacent ranks reconstructed rather than
assumed. -/
theorem
    exists_eventual_twistedFreeQuotUniversalFlatteningLocusWitness_of_reducedGeometry
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S] (hn : 0 < n)
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hinputs : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotGrassmannianCanonicalInputs
          n S l r P d e he (r * (n + e).choose n)
            (P.hilbertNatValue d)
            (twistedFreeMonomialIndexEquiv r ((n + e).choose n))))
    (hgeometry : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (TwistedFreeQuotUniversalReducedOneStepFlatteningGeometry
          n S l r P d e he)) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ)),
        Nonempty (Modules.ProjectiveFlatteningLocusWitness n
          (grassmannianPointReconstructedQuotient
            (n := n) (r := r) (q := P.hilbertNatValue d) (l := l)
              (d := d) (e := e) (he := he)
              (σ := twistedFreeMonomialIndexEquiv r ((n + e).choose n))
              (grassmannianOverRepresentation S (P.hilbertNatValue d)
                (r * (n + e).choose n))
              (freeGrassmannianUniversalPoint S (P.hilbertNatValue d)
                (r * (n + e).choose n))) P) := by
  obtain ⟨DI, hI⟩ := hinputs
  obtain ⟨DG, hG⟩ := hgeometry
  refine ⟨max DI DG, ?_⟩
  intro d hd e he
  have hdI : DI ≤ d := le_trans (le_max_left DI DG) hd
  obtain ⟨I₀⟩ := hI d hdI e he
  obtain ⟨I₁⟩ := hI (d + 1) (by omega) (e + 1) (by omega)
  obtain ⟨G⟩ := hG d (le_trans (le_max_right DI DG) hd) e he
  exact ⟨(G.toGeometry I₀ I₁).toWitness S n hn l r P d e he I₀⟩

end AlgebraicGeometry.Scheme

end

end
