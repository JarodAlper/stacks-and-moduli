module

public import StacksAndModuli.API.ProjTwistModuleQuasicoherent
public import StacksAndModuli.API.ProjectiveSpaceStandardCover
public import StacksAndModuli.«Section2.1-Intro».«part2.1.2-the-grassmannian-functor»

/-!
# Quasicoherence of twists of quasicoherent modules on `Proj`

If degree-one basic opens cover `Proj 𝒜`, tensoring a quasicoherent module sheaf with
the twisting sheaf preserves quasicoherence.  On each basic open the twisting sheaf is
trivial, so the restricted tensor product is isomorphic to the restricted original
module; quasicoherence then descends from the open cover.

This removes the finite-presentation hypothesis from the quasicoherence half of
`ProjTwistModuleQuasicoherent.lean`.  Finite presentation is still needed there for the
separate finite-presentation conclusion.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace ProjectiveSpectrum.Twist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Twisting a quasicoherent module on `Proj 𝒜` preserves quasicoherence when degree-one
basic opens cover `Proj 𝒜`. -/
theorem twistModule_isQuasicoherent_of_isQuasicoherent
    {J : Type u} (y : J → A) (hy : ∀ j, y j ∈ 𝒜 1)
    (hcover : ⨆ j, AlgebraicGeometry.Proj.basicOpen 𝒜 (y j) = ⊤)
    (F : (AlgebraicGeometry.Proj 𝒜).Modules) [F.IsQuasicoherent] (d : ℤ) :
    (twistModule 𝒜 F d).IsQuasicoherent := by
  let X := AlgebraicGeometry.Proj 𝒜
  let U (j : J) : X.Opens := AlgebraicGeometry.Proj.basicOpen 𝒜 (y j)
  have hU : IsOpenCover U := by
    simpa only [U, IsOpenCover] using hcover
  let 𝒰 : Scheme.OpenCover.{u} X := X.openCoverOfIsOpenCover U hU
  let _ (j : 𝒰.I₀) :
      ((Scheme.Modules.restrictFunctor (𝒰.f j)).obj
        (twistModule 𝒜 F d)).IsQuasicoherent := by
    change ((Scheme.Modules.restrictFunctor (U j).ι).obj
      (Scheme.Modules.tensor F (twist 𝒜 d))).IsQuasicoherent
    let Fj := (Scheme.Modules.restrictFunctor (U j).ι).obj F
    let Lj := (Scheme.Modules.restrictFunctor (U j).ι).obj (twist 𝒜 d)
    letI : Fj.IsQuasicoherent := by
      dsimp only [Fj]
      infer_instance
    let eL : Lj ≅ SheafOfModules.unit (U j).toScheme.ringCatSheaf := by
      dsimp only [Lj, U]
      exact restrictTwistIsoUnit (hy j) d
    have hTensor : (Scheme.Modules.tensor Fj Lj).IsQuasicoherent :=
      Scheme.Modules.tensor_isQuasicoherent_of_iso_unit Fj Lj eL
    exact (SheafOfModules.isQuasicoherent (U j).toScheme.ringCatSheaf).prop_of_iso
      (Scheme.Modules.restrictTensorIso (U j).ι F (twist 𝒜 d)).symm hTensor
  exact Scheme.Modules.isQuasicoherent_of_openCover_restrict _ 𝒰

end ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 800000 in
-- Inferring quasicoherence through the standard cover unfolds the graded polynomial ring.
/-- Every twist of a quasicoherent module on standard polynomial projective space is
quasicoherent, without a finite-presentation hypothesis. -/
theorem twistModule_std_isQuasicoherent_of_isQuasicoherent
    {R : Type u} [CommRing R] (n : ℕ)
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    [F.IsQuasicoherent] (d : ℤ) :
    (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d).IsQuasicoherent :=
  ProjectiveSpectrum.Twist.twistModule_isQuasicoherent_of_isQuasicoherent _
    (fun k : ULift.{u} (Fin (n + 1)) =>
      (MvPolynomial.X k.down : MvPolynomial (Fin (n + 1)) R))
    (fun k => X_mem_homogeneousSubmodule R n k.down)
    (by rw [iSup_ulift]; exact iSup_basicOpen_X_eq_top R n) F d

end AlgebraicGeometry.ProjectiveSpace

end

end
