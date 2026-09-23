module

public import StacksAndModuli.API.TwistedFreeQuotNoetherianCechModel
public import StacksAndModuli.API.TwistedFreeQuotPushforwardRank

/-!
# Noetherian Čech models on a noetherian affine base

The noetherian-model interface used by the arbitrary-base Quot construction is automatic
when the coefficient ring is already noetherian.  In that case the kernel-quotient graded
module is its own model: finite generation, flatness of the fixed-degree Čech cochains, and
uniform positive-cohomology vanishing are all available from the twisted-free quotient API.

This is the noetherian-affine endpoint of the approximation argument.  Passing from an
arbitrary coefficient ring to such a model is the remaining relative flat-spreading theorem.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
-- The construction combines the Čech, finite-presentation, and flatness instance towers.
set_option maxHeartbeats 3000000 in
/-- On a noetherian affine base, every sufficiently positive fixed-degree Čech model of a
flat twisted-free Quot family has a noetherian model: namely, itself. -/
theorem exists_bound_noetherianCechComplexModel_kernelQuotientModule
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (R : Type u) [CommRing R] [IsNoetherianRing R]
      (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℕ), d₀ ≤ (d : ℤ) →
      let p := (Scheme.Modules.pullback
        (projectiveSpaceOverSpecIso n R).inv).map q
      let M := Proj.kernelQuotientModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) (stdVars n R) p
      Nonempty (GradedModule.NoetherianCechComplexModel M (d : ℤ)) := by
  obtain ⟨d₀, hd₀0, hd₀⟩ :=
    exists_bound_subsingleton_cechHgr_kernelQuotientModule_baseChange_arbitrary
      n r hn l P
  refine ⟨d₀, hd₀0, ?_⟩
  intro R _ _ Q hQfp q hq hflat hHP d hd
  haveI := hQfp
  haveI := hq
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
  haveI hEqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  haveI hGqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) G e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent _ e
  have hKqc0 : (kernel p).IsQuasicoherent :=
    Scheme.Modules.kernel_isQuasicoherent p
  letI hKqc0' : (kernel p).IsQuasicoherent := hKqc0
  haveI hKqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent_of_isQuasicoherent n _ e
  let M := Proj.kernelQuotientModule
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (projSpecπ n R) (stdVars n R) p
  have hGflat : G.FlatOver (projSpecπ n R) :=
    Scheme.Modules.FlatOver.pullback_isIso
      (projectiveSpaceOverSpecIso n R).inv Q
      (projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R) hflat
  have hMfg : GradedModule.IsFG M :=
    isFG_kernelQuotientModule_twistedFree_arbitrary n r hn l R Q q
  have hMflatC : ∀ s : ℕ, Module.Flat R ((M.cechComplex (d : ℤ)).X s) := by
    intro s
    exact GradedModule.flat_cechCochain_of_flat_loc _
      (fun a ↦ Proj.isFlat_loc_kernelQuotientModule_arbitrary p a hGflat)
      s (d : ℤ)
  exact ⟨(GradedModule.NoetherianCechModel.self M (d : ℤ) hMfg hMflatC
    (hd₀ R Q hQfp q hq hflat hHP d hd)).toCechComplexModel⟩

set_option synthInstance.maxHeartbeats 1000000 in
-- Restriction to every affine chart creates nested scheme-pullback instance towers.
set_option maxHeartbeats 3000000 in
/-- On a locally noetherian base, the kernel-quotient Čech complex of every sufficiently
positive twisted-free Quot family has a noetherian model on each affine chart. -/
theorem
    exists_bound_hasAffineNoetherianTwistedFreeQuotCechModel_of_isLocallyNoetherian
    (n r : ℕ) (hn : 0 < n) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₀ : ℤ, 0 ≤ d₀ ∧ ∀ (T : Scheme.{u}) [IsLocallyNoetherian T]
      (Q : (Scheme.projectiveSpaceOver n T).Modules)
      (_ : Q.IsFinitePresentation)
      (q : (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q)
      (_ : Epi q)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n T))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℕ), d₀ ≤ (d : ℤ) →
      HasAffineNoetherianTwistedFreeQuotCechModel n r l Q q d := by
  obtain ⟨d₀, hd₀0, hd₀⟩ :=
    exists_bound_noetherianCechComplexModel_kernelQuotientModule n r hn l P
  refine ⟨d₀, hd₀0, ?_⟩
  intro T _ Q hQfp q hq hflat hHP d hd
  haveI := hQfp
  haveI := hq
  intro U
  haveI hUaff : IsAffine U.1.toScheme := U.2
  let R := Γ(U.1.toScheme, ⊤)
  letI : IsNoetherianRing Γ(T, U.1) :=
    IsLocallyNoetherian.component_noetherian U
  haveI hR : IsNoetherianRing R :=
    isNoetherianRing_of_ringEquiv Γ(T, U.1)
      U.1.topIso.symm.commRingCatIsoToRingEquiv
  let gU : Spec (CommRingCat.of R) ⟶ T := U.1.toScheme.isoSpec.inv ≫ U.1.ι
  let mU := Scheme.projectiveSpaceOverMap n gU
  haveI : IsOpenImmersion gU := inferInstance
  haveI : IsOpenImmersion mU := inferInstance
  let QU := (Scheme.Modules.pullback mU).obj Q
  haveI hQUfp : QU.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  let qU := (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l gU).inv ≫
    (Scheme.Modules.pullback mU).map q
  haveI hqU : Epi qU := epi_comp _ _
  have hflatU : QU.FlatOver
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R))) :=
    Scheme.Modules.FlatOver.pullback_of_isPullback mU
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))
      (Scheme.projectiveSpaceOverπ n T) gU
      (Scheme.isPullback_projectiveSpaceOverMap n gU).flip Q hflat
  have hHPU : Scheme.HasFiberwiseHilbertPolynomial QU P :=
    Scheme.HasFiberwiseHilbertPolynomial.pullback gU hHP
  exact hd₀ R QU hQUfp qU hqU hflatU hHPU d hd

end AlgebraicGeometry.ProjectiveSpace

end

end
