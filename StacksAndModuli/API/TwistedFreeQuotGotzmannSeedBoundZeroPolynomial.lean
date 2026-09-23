module

public import StacksAndModuli.API.TwistedFreeQuotGotzmannSeedBoundZeroAmbient
public import StacksAndModuli.API.ProjectiveGradedGlobalGeneration
public import StacksAndModuli.API.ProjGammaStarTwistedFreeAmbient
public import StacksAndModuli.API.PullbackPushforwardCounitIsoTransport
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianReflection

/-!
# The zero-polynomial projective-line Gotzmann seed bound

If the prescribed Hilbert polynomial is zero, the degree-`d` coefficient sheaf
in the affine Gotzmann seed problem has rank zero and is therefore a zero
object.  The reconstruction is then the cokernel of the full ambient monomial
evaluation map.  This file proves that this monomial map is an epimorphism over
an affine base and consequently that the reconstruction is zero.

This gives a genuine proper-quotient boundary case of the missing projective-line
Gotzmann theorem, for every ambient rank and generating twist.  Unlike the
zero-ambient case, the source sheaf need not vanish: the proof uses generation
of the twisted-free ambient sheaf by its degree-`e` monomials.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.twistedFreeMonomialMap_epi_of_affine`;
* `AlgebraicGeometry.Scheme.reconstructedQuotient'_isZero_of_target_isZero_of_affine`;
* `AlgebraicGeometry.Scheme.Modules.
  twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_zeroPolynomial`;
* `AlgebraicGeometry.Scheme.Modules.
  twistedFreeQuotProjectiveLineGotzmannSeedBound_zeroPolynomial`;
* `AlgebraicGeometry.Scheme.Modules.
  twistedFreeQuotNextDegreeGotzmannPersistence_zeroPolynomial`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {R : Type u} [CommRing R] {n : ℕ}

/-- If a graded module is generated from degree `d` in degree `e`, then any
finite power of it is generated in the same degrees. -/
lemma pow_mulSpan_eq_top (M : GradedModule R n) (r : ℕ) (d e : ℤ)
    (h : M.mulSpan d e = ⊤) :
    (M.pow r).mulSpan d e = ⊤ := by
  apply top_unique
  intro x _
  have hx : x = ∑ t : Fin r, ((M.powCoord r t).app e).hom (x t) :=
    (Finset.univ_sum_single x).symm
  rw [hx]
  refine Submodule.sum_mem _ fun t _ ↦ ?_
  refine mulSpan_map_le (M.powCoord r t) d e ⟨x t, ?_, rfl⟩
  rw [h]
  trivial

/-- The degreewise Čech augmentation, packaged as a morphism of graded
modules. -/
noncomputable def cechAugHom (M : GradedModule R n) : M ⟶ M.cechHgr 0 where
  app d := M.cechAug d
  comm i d := by
    simpa only [mulX'_rfl] using
      M.cechAug_comp_mulX' i d (d + 1) rfl

end AlgebraicGeometry.ProjectiveSpace.GradedModule

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Over an affine base, the pullback--pushforward evaluation of a nonnegative
twist of a finite twisted-free ambient sheaf is an epimorphism in positive
projective dimension. -/
theorem projectiveSpaceOverTwistedFreeTwist_counit_epi_of_spec
    (n : ℕ) (R : Type u) [CommRing R] (hn : 0 < n)
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    Epi ((pullbackPushforwardAdjunction
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))).counit.app
        (Scheme.projectiveSpaceOverTwistModule
          (∐ fun _ : ULift.{u} (Fin r) ↦
            Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l))
          (d : ℤ))) := by
  let X := Scheme.projectiveSpaceOver n (Spec (.of R))
  let p := Scheme.projectiveSpaceOverπ n (Spec (.of R))
  let F : X.Modules := ∐ fun _ : ULift.{u} (Fin r) ↦
    Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)
  let M := Scheme.projectiveSpaceOverTwistModule F (d : ℤ)
  let i := ProjectiveSpace.projectiveSpaceOverSpecIso n R |>.inv
  let 𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  let π := ProjectiveSpace.projSpecπ n R
  let F' := (pullback i).obj F
  haveI hFfp : F.IsFinitePresentation :=
    projectiveSpaceOverTwistCoproduct_isFinitePresentation
      (ULift.{u} (Fin r)) n (Spec (.of R)) (-l)
  haveI hF'fp : F'.IsFinitePresentation :=
    isFinitePresentation_pullback_of_isFinitePresentation i inferInstance
  haveI hF'twistQc : ∀ a : ℤ,
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F' a).IsQuasicoherent :=
    fun a ↦ ProjectiveSpace.twistModule_std_isQuasicoherent F' a
  have hmul : ∀ q : ℤ, (d : ℤ) ≤ q →
      ((Proj.gammaStar 𝒜 π F' (ProjectiveSpace.stdVars n R)).cechHgr 0).mulSpan
        (d : ℤ) q = ⊤ := by
    intro q hdq
    let G := ((ProjectiveSpace.GradedModule.structureModule R n).twist (-l)).pow r
    have hstructure : (ProjectiveSpace.GradedModule.structureModule R n).mulSpan
        ((d : ℤ) + -l) (q + -l) = ⊤ := by
      apply ProjectiveSpace.GradedModule.mulSpan_top_of_gen
      · intro a ha
        exact ProjectiveSpace.GradedModule.structureModule_mulSpan_succ a (by omega)
      · omega
    have htwist : ((ProjectiveSpace.GradedModule.structureModule R n).twist (-l)).mulSpan
        (d : ℤ) q = ⊤ := by
      rw [ProjectiveSpace.GradedModule.twist_mulSpan]
      exact hstructure
    have hpow : G.mulSpan (d : ℤ) q = ⊤ :=
      ProjectiveSpace.GradedModule.pow_mulSpan_eq_top _ r _ _ htwist
    let E := ProjectiveSpace.gammaStarPullTwistedFreeIso n R hn (-l) r
    have hgamma : (Proj.gammaStar 𝒜 π F'
        (ProjectiveSpace.stdVars n R)).mulSpan (d : ℤ) q = ⊤ :=
      ProjectiveSpace.GradedModule.mulSpan_eq_top_of_iso E.symm _ _ hpow
    exact ProjectiveSpace.GradedModule.mulSpan_eq_top_of_surjective
      (ProjectiveSpace.GradedModule.cechAugHom
        (Proj.gammaStar 𝒜 π F' (ProjectiveSpace.stdVars n R)))
      (fun a ↦ (ProjectiveSpace.bijective_gammaStar_cechAug_std π F' a).2)
      (d : ℤ) q hgamma
  haveI hpoly : Epi ((pullbackPushforwardAdjunction π).counit.app
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F' (d : ℤ))) :=
    Proj.pullbackPushforwardCounit_epi_of_cechHgr_mulSpan F' (d : ℤ) hmul
  let EM : (pullback i).obj M ≅
      ProjectiveSpectrum.Twist.twistModule 𝒜 F' (d : ℤ) :=
    ProjectiveSpace.projectiveSpaceOverTwistModulePullbackIso F (d : ℤ)
  haveI hpulled : Epi ((pullbackPushforwardAdjunction π).counit.app
      ((pullback i).obj M)) :=
    CategoryTheory.Adjunction.epi_counit_of_iso
      (pullbackPushforwardAdjunction π) EM
  haveI hcomposite : Epi ((pullbackPushforwardAdjunction (i ≫ p)).counit.app
      ((pullback i).obj M)) := by
    rw [show i ≫ p = π by
      exact ProjectiveSpace.projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R]
    infer_instance
  exact epi_pullbackPushforwardCounit_of_comp_of_isIso i p M

/-- Over the spectrum of a ring, the full degree-`e` monomial evaluation onto
a twisted-free ambient sheaf is an epimorphism in positive projective
dimension. -/
theorem twistedFreeMonomialMap_epi_of_spec
    (n : ℕ) (R : Type u) [CommRing R] (hn : 0 < n)
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    Epi (Scheme.twistedFreeMonomialMap n (Spec (.of R)) l r d e he) := by
  let T := Spec (.of R)
  let p := Scheme.projectiveSpaceOverπ n T
  let A : T.Modules := SheafOfModules.free (R := T.ringCatSheaf)
    (ULift.{u} (Fin r) × Fin ((n + e).choose n))
  let B := Scheme.projectiveSpaceOverTwistModule
    (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) (d : ℤ)
  let k := (pullbackFreeIso p
      (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
    Scheme.twistedFreeMonomialMap n T l r d e he
  haveI hcounit : Epi ((pullbackPushforwardAdjunction p).counit.app B) :=
    projectiveSpaceOverTwistedFreeTwist_counit_epi_of_spec
      n R hn l r d e he
  haveI hadjunct : IsIso
      ((pullbackPushforwardAdjunction p).homEquiv A B k) := by
    rw [show (pullbackPushforwardAdjunction p).homEquiv A B k =
      Scheme.twistedFreeMonomialPushforwardMap n T l r d e he by
        exact Scheme.twistedFreeMonomialPushforwardMap_adjunct
          n T l r d e he]
    dsimp only [T]
    exact Scheme.twistedFreeMonomialPushforwardMap_isIso
      n (Spec (.of R)) l r d e he
  haveI hk : Epi k :=
    epi_of_isIso_pullbackPushforwardAdjunct_of_counit_epi p k
  exact epi_of_epi_fac (rfl :
    (pullbackFreeIso p
      (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
        Scheme.twistedFreeMonomialMap n T l r d e he = k)

/-- The full degree-`e` monomial evaluation onto a twisted-free ambient sheaf
is an epimorphism over every affine base in positive projective dimension. -/
theorem twistedFreeMonomialMap_epi_of_affine
    (n : ℕ) (T : Scheme.{u}) [IsAffine T] (hn : 0 < n)
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) :
    Epi (Scheme.twistedFreeMonomialMap n T l r d e he) := by
  let f := T.isoSpec.inv
  let m := Scheme.projectiveSpaceOverMap n f
  haveI hf : IsIso f := by dsimp only [f]; infer_instance
  haveI hm : IsIso m := by dsimp only [m]; infer_instance
  haveI hspec : Epi (Scheme.twistedFreeMonomialMap n
      (Spec (.of Γ(T, ⊤))) l r d e he) :=
    twistedFreeMonomialMap_epi_of_spec n Γ(T, ⊤) hn l r d e he
  have hbc := Scheme.twistedFreeMonomialMap_baseChange_comp
    n r l f d e he
  haveI hcomp : Epi
      ((pullback m).map (Scheme.twistedFreeMonomialMap n T l r d e he) ≫
        (Scheme.reconstructedTwistedTargetPullbackIso n r l f d).hom) := by
    rw [hbc]
    infer_instance
  haveI hmapped : Epi
      ((pullback m).map (Scheme.twistedFreeMonomialMap n T l r d e he)) :=
    (epi_comp_iff_of_isIso _
      (Scheme.reconstructedTwistedTargetPullbackIso n r l f d).hom).mp
        inferInstance
  exact (pullback m).epi_of_epi_map inferInstance

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Over an affine base in positive projective dimension, reconstruction from a
zero coefficient target is zero in its positively twisted presentation. -/
theorem reconstructedTwisted_isZero_of_target_isZero_of_affine
    (n : ℕ) (T : Scheme.{u}) [IsAffine T] (hn : 0 < n)
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hE : IsZero E) :
    IsZero (reconstructedTwisted n T l r d e he u) := by
  have hu : u = 0 := hE.eq_zero_of_tgt u
  letI : IsIso (kernel.ι u) := kernel.ι_of_zero hu
  letI : Epi (twistedFreeMonomialMap n T l r d e he) :=
    Modules.twistedFreeMonomialMap_epi_of_affine n T hn l r d e he
  let f := (Modules.pullback (projectiveSpaceOverπ n T)).map (kernel.ι u) ≫
    (Modules.pullbackFreeIso (projectiveSpaceOverπ n T)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n))).hom ≫
    twistedFreeMonomialMap n T l r d e he
  haveI : Epi f := by
    dsimp only [f]
    infer_instance
  change IsZero (cokernel f)
  exact isZero_cokernel_of_epi f

/-- Over an affine base in positive projective dimension, the untwisted
reconstruction from a zero coefficient target is a zero object. -/
theorem reconstructedQuotient'_isZero_of_target_isZero_of_affine
    (n : ℕ) (T : Scheme.{u}) [IsAffine T] (hn : 0 < n)
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (hE : IsZero E) :
    IsZero (reconstructedQuotient' n T l r d e he u) := by
  have htwisted : IsZero (reconstructedTwisted n T l r d e he u) :=
    reconstructedTwisted_isZero_of_target_isZero_of_affine
      n T hn l r d e he u hE
  have hquotient : IsZero (reconstructedQuotient n T l r d e he u) :=
    Modules.tensor_isZero_of_left_isZero _ _ htwisted
  exact hquotient.of_iso
    (reconstructedQuotientIsoReconstructedQuotient'
      n T l r d e he u
        (twistedFreeAmbientReconstructionCompatibility n T l r d e he)).symm

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- For the zero Hilbert polynomial, the affine projective-line Gotzmann seed
bound is `0`, for every ambient rank and generating twist. -/
noncomputable def
    twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_zeroPolynomial
    (r : ℕ) (l : ℤ) :
    TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound.{u}
      r l (0 : Polynomial ℚ) where
  bound := 0
  affineSeedRanks T _ d e he E _ u _ _ hE _ := by
    have hEzeroRank : IsProjectiveOfRank 0 E := by
      simpa [Polynomial.hilbertNatValue] using hE
    have hEzero : IsZero E :=
      isZero_of_isProjectiveOfRank_zero E hEzeroRank
    let Q := Scheme.reconstructedQuotient' 1 T l r d e he u
    have hQ : IsZero Q :=
      Scheme.reconstructedQuotient'_isZero_of_target_isZero_of_affine
        1 T (by omega) l r d e he u hEzero
    have hQd : IsZero (projectiveTwistedPushforward 1 Q d) :=
      projectiveTwistedPushforward_isZero 1 Q d hQ
    have hQnext : IsZero (projectiveTwistedPushforward 1 Q (d + 1)) :=
      projectiveTwistedPushforward_isZero 1 Q (d + 1) hQ
    constructor
    · intro _
      simpa [Polynomial.hilbertNatValue] using
        isProjectiveOfRank_zero_of_isZero
          (projectiveTwistedPushforward 1 Q d) hQd
    · intro _
      simpa [Polynomial.hilbertNatValue] using
        isProjectiveOfRank_zero_of_isZero
          (projectiveTwistedPushforward 1 Q (d + 1)) hQnext

/-- The affine zero-polynomial Gotzmann seed endpoint is inhabited for every
ambient rank and generating twist. -/
theorem
    nonempty_twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_zeroPolynomial
    (r : ℕ) (l : ℤ) :
    Nonempty (TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound.{u}
      r l (0 : Polynomial ℚ)) :=
  ⟨twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_zeroPolynomial r l⟩

/-- The zero-polynomial affine seed bound formally upgrades to the seed
comparison after arbitrary base change. -/
noncomputable def
    twistedFreeQuotProjectiveLineGotzmannSeedBound_zeroPolynomial
    (r : ℕ) (l : ℤ) :
    TwistedFreeQuotProjectiveLineGotzmannSeedBound.{u}
      r l (0 : Polynomial ℚ) :=
  (twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_zeroPolynomial r l
    ).toGotzmannSeedBound

/-- The arbitrary-base-change zero-polynomial seed endpoint is inhabited for
every ambient rank and generating twist. -/
theorem
    nonempty_twistedFreeQuotProjectiveLineGotzmannSeedBound_zeroPolynomial
    (r : ℕ) (l : ℤ) :
    Nonempty (TwistedFreeQuotProjectiveLineGotzmannSeedBound.{u}
      r l (0 : Polynomial ℚ)) :=
  ⟨twistedFreeQuotProjectiveLineGotzmannSeedBound_zeroPolynomial r l⟩

/-- For a quotient of twisted-free monomials on the projective line, the two
expected algebraic ranks for the zero polynomial force the reconstructed
family to be zero, hence flat with zero fibrewise Hilbert polynomial.  This
holds over an arbitrary base and in every normalized degree. -/
theorem twistedFreeQuotNextDegreeGotzmannPersistence_zeroPolynomial
    (T : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E) [Epi u] :
    TwistedFreeQuotNextDegreeGotzmannPersistence
      1 T l r (0 : Polynomial ℚ) d e he u := by
  exact
    (twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_zeroPolynomial r l
      ).gotzmannPersistence
        (by simp [twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_zeroPolynomial])
        (by omega) (by simp) (by simp) (by simp)

end AlgebraicGeometry.Scheme.Modules

end

end
