module

public import StacksAndModuli.API.ProjGammaStarKernelVanishing
public import StacksAndModuli.API.ProjectiveGradedRelativeGlobGen
public import StacksAndModuli.API.ProjectiveGradedGlobalGeneration
public import StacksAndModuli.API.PullbackPushforwardCounitIsoTransport
public import StacksAndModuli.API.ProjectiveSpaceTwistExact
public import StacksAndModuli.API.ProjectiveSpaceTwistProjComparison
public import StacksAndModuli.API.ProjectiveTwistedFreePresentation


/-!
# Uniform global generation of twisted-free Quot kernels

Supporting API for Proposition 2.4.1.  The uniform higher-cohomology bound for the kernel
of a twisted-free Quot presentation is shifted by the projective dimension to obtain a
uniform Castelnuovo--Mumford regularity bound.  Fibrewise multiplication surjectivity,
cochain-flat Cohomology and Base Change, and Nakayama then give a multiplication-span
statement over every noetherian affine base.  Finally this span is converted into the
epimorphic pullback--pushforward evaluation map for the twisted kernel.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry ProjectiveSpectrum.Twist

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

open GradedModule

set_option synthInstance.maxHeartbeats 1000000 in
-- The proof keeps the full Čech, fibre-regularity, and Nakayama instance towers in scope.
set_option maxHeartbeats 2000000 in
/-- Uniform eventual multiplication generation for the graded Čech `H⁰` of a
twisted-free Quot kernel over a noetherian affine base. -/
theorem exists_bound_mulSpan_cechHgr_gammaStar_kernel
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
      (_ : Q.IsFinitePresentation)
      (_ : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)).IsFinitePresentation)
      (p : projAmbient n r l (R := R) ⟶
        (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
      (_ : Epi p)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d e : ℤ), d₀ ≤ d → d ≤ e →
      ((Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) (kernel p) (stdVars n R)).cechHgr 0).mulSpan d e = ⊤ := by
  obtain ⟨d₁, hd₁0, hK⟩ :=
    exists_bound_subsingleton_cechHgr_gammaStar_kernel n r l P
  let d₀ : ℤ := d₁ + n
  refine ⟨d₀, by dsimp [d₀]; omega, ?_⟩
  intro R _ _ Q hQfp hAmbfp p hp hflat hHP
  haveI := hQfp
  haveI := hAmbfp
  haveI := hp
  haveI hE : (projAmbient n r l (R := R)).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hQ' : ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
      Q).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (projAmbient n r l (R := R)) a).IsQuasicoherent :=
    fun a ↦ twistModule_std_isQuasicoherent _ a
  haveI : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
      a).IsQuasicoherent := fun a ↦ twistModule_std_isQuasicoherent _ a
  haveI hKfp : (kernel p).IsFinitePresentation :=
    Scheme.Modules.kernel_isFinitePresentation p
  haveI : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) a).IsQuasicoherent := fun a ↦ twistModule_std_isQuasicoherent _ a
  have hflat' : ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
      Q).FlatOver (projSpecπ n R) :=
    Scheme.Modules.FlatOver.pullback_isIso (projectiveSpaceOverSpecIso n R).inv Q
      (projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R) hflat
  let Kγ := Proj.gammaStar
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (projSpecπ n R) (kernel p) (stdVars n R)
  have hEflat : GradedModule.IsFlat (Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (projSpecπ n R)
      (projAmbient n r l (R := R)) (stdVars n R)) :=
    isFlat_gammaStarPullTwistedFree n R hn (-l) r
  have hEfg : GradedModule.IsFG (Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (projSpecπ n R)
      (projAmbient n r l (R := R)) (stdVars n R)) :=
    isFG_gammaStarPullTwistedFree n R hn (-l) r
  have hKfg : GradedModule.IsFG Kγ :=
    GradedModule.IsFG.of_injective _
      (fun e ↦ Proj.injective_gammaStarMap_kernel_ι
        (Fin (n + 1)) (projSpecπ n R) (stdVars n R) p e) hEfg
  have hflatC : ∀ (e : ℤ) (q : ℕ), Module.Flat R ((Kγ.cechComplex e).X q) := by
    intro e q
    refine GradedModule.flat_cechCochain_of_flat_loc _ (fun a ↦ ?_) q e
    refine GradedModule.IsFlat.of_shortExact
      (GradedModule.loc_shortExact _ (l := [a])
        (Proj.shortExact_gammaStar_toCoker_kernel (projSpecπ n R) p))
      (fun t ↦ hEflat.flat_loc [a] t)
      (Proj.isFlat_loc_kernelQuotientModule p a hflat')
  have hvanFrom : ∀ (κ : Type u) [Field κ] [Algebra R κ]
      (e : ℤ), d₁ ≤ e → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (((Kγ.baseChange κ).cechHgr i).obj e) := by
    intro κ _ _ e he i hi
    apply GradedModule.subsingleton_cechHgr_baseChange_of_flatCochain
      Kγ e κ (hflatC e) _ i hi
    intro j hj
    exact hK R Q hQfp hAmbfp p hp hflat hHP j hj e he
  have hreg : ∀ (κ : Type u) [Field κ] [Algebra R κ],
      (Cohomology.cech κ).IsMRegular (Kγ.baseChange κ) d₀ := by
    intro κ _ _ i hi
    by_cases hni : i ≤ n
    · exact hvanFrom κ (d₀ - i) (by dsimp [d₀]; omega) i hi
    · exact GradedModule.subsingleton_cechHgr _ i (by omega) _
  intro d e hd hde
  exact GradedModule.mulSpan_eq_top_of_fibres_cech' hKfg
    (fun e _ ↦ hflatC e)
    (fun κ _ _ e he i hi ↦
      hvanFrom κ e (by dsimp [d₀] at hd; omega) i hi)
    (fun κ _ _ e he ↦
      (Cohomology.cech κ).mulSpan_eq_top_of_field
        (hKfg.baseChange κ) (Cohomology.hasInfiniteBaseChange_cech κ)
        (hreg κ) hd he)
    e hde

set_option synthInstance.maxHeartbeats 1000000 in
-- Elaborating the evaluation counit retains the graded generation instance tower.
set_option maxHeartbeats 2000000 in
/-- Uniform eventual epimorphic evaluation for the intrinsic polynomial-`Proj` kernel. -/
theorem exists_bound_pullbackPushforwardCounit_epi_gammaStar_kernel
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
      (_ : Q.IsFinitePresentation)
      (_ : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)).IsFinitePresentation)
      (p : projAmbient n r l (R := R) ⟶
        (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
      (_ : Epi p)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℤ), d₀ ≤ d →
      Epi ((Scheme.Modules.pullbackPushforwardAdjunction
        (projSpecπ n R)).counit.app
          (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
            (kernel p) d)) := by
  obtain ⟨d₀, hd₀, hmul⟩ :=
    exists_bound_mulSpan_cechHgr_gammaStar_kernel n r hn l P
  refine ⟨d₀, hd₀, ?_⟩
  intro R _ _ Q hQfp hAmbfp p hp hflat hHP d hd
  haveI := hQfp
  haveI := hAmbfp
  haveI := hp
  haveI : (projAmbient n r l (R := R)).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI : ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
      Q).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI : (kernel p).IsFinitePresentation :=
    Scheme.Modules.kernel_isFinitePresentation p
  haveI : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) a).IsQuasicoherent := fun a ↦ twistModule_std_isQuasicoherent _ a
  exact Proj.pullbackPushforwardCounit_epi_of_cechHgr_mulSpan
    (kernel p) d (fun e hde ↦
      hmul R Q hQfp hAmbfp p hp hflat hHP d e hd hde)

set_option synthInstance.maxHeartbeats 1000000 in
-- Transporting the kernel, tensor twist, and two adjunction counits is instance-heavy.
set_option maxHeartbeats 2000000 in
/-- The uniform noetherian-affine global-generation bound, transported from polynomial
`Proj` to the actual twisted kernel on relative projective space. -/
theorem exists_bound_pullbackPushforwardCounit_epi_twistedFreeQuotKernel_noetherian_affine
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P),
      Epi ((Scheme.Modules.pullbackPushforwardAdjunction
        (Scheme.projectiveSpaceOverπ n (Spec (.of R)))).counit.app
          (kernel (Scheme.Modules.tensorMapLeft q
            (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ))))) := by
  obtain ⟨d₀, hd₀, hgen⟩ :=
    exists_bound_pullbackPushforwardCounit_epi_gammaStar_kernel n r hn l P
  let D := d₀.toNat
  have hD : (D : ℤ) = d₀ := by
    dsimp [D]
    exact Int.toNat_of_nonneg hd₀
  refine ⟨D, ?_⟩
  intro d hDd R _ _ Q hQfp q hq hflat hHP
  haveI := hQfp
  haveI := hq
  let i := (projectiveSpaceOverSpecIso n R).inv
  let p : projAmbient n r l (R := R) ⟶
      (Scheme.Modules.pullback i).obj Q :=
    (Scheme.Modules.pullback i).map q
  haveI hp : Epi p := Functor.map_epi _ q
  haveI hAmbfp : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)).IsFinitePresentation :=
    Scheme.Modules.projectiveSpaceOverTwistCoproduct_isFinitePresentation
      (ULift.{u} (Fin r)) n (Spec (.of R)) (-l)
  have hd₀d : d₀ ≤ (d : ℤ) := by
    rw [← hD]
    exact_mod_cast hDd
  have hgen' := hgen R Q hQfp hAmbfp p hp hflat hHP (d : ℤ) hd₀d
  let M := kernel (Scheme.Modules.tensorMapLeft q
    (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (d : ℤ)))
  let eK : (Scheme.Modules.pullback i).obj (kernel q) ≅ kernel p :=
    PreservesKernel.iso (Scheme.Modules.pullback i) q
  let eM : (Scheme.Modules.pullback i).obj M ≅
      twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (kernel p) (d : ℤ) :=
    (Scheme.Modules.pullback i).mapIso
        (Scheme.projectiveSpaceOverTwistTensorKernelIso
          n (Spec (.of R)) q (d : ℤ)).symm ≪≫
      projectiveSpaceOverTwistModulePullbackIso (kernel q) (d : ℤ) ≪≫
      Scheme.Modules.tensorLeftIso eK
        (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ))
  haveI hProjTarget : Epi ((Scheme.Modules.pullbackPushforwardAdjunction
      (projSpecπ n R)).counit.app
        (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (kernel p) (d : ℤ))) := hgen'
  haveI hProjSource : Epi ((Scheme.Modules.pullbackPushforwardAdjunction
      (projSpecπ n R)).counit.app ((Scheme.Modules.pullback i).obj M)) :=
    CategoryTheory.Adjunction.epi_counit_of_iso _ eM
  haveI hComposite : Epi ((Scheme.Modules.pullbackPushforwardAdjunction
      (i ≫ Scheme.projectiveSpaceOverπ n (Spec (.of R)))).counit.app
        ((Scheme.Modules.pullback i).obj M)) := by
    rw [show i ≫ Scheme.projectiveSpaceOverπ n (Spec (.of R)) = projSpecπ n R by
      exact projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R]
    infer_instance
  exact Scheme.Modules.epi_pullbackPushforwardCounit_of_comp_of_isIso
    i (Scheme.projectiveSpaceOverπ n (Spec (.of R))) M

end AlgebraicGeometry.ProjectiveSpace

end

end
