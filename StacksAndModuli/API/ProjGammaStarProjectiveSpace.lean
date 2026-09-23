module

public import StacksAndModuli.API.ProjGammaStarChart
public import StacksAndModuli.API.ProjectiveSpaceStandardCover
public import StacksAndModuli.API.ProjTwistModuleQuasicoherent

/-!
# The `H⁰` comparison on `ℙⁿ`

`StacksAndModuli/API/ProjGammaStarChart.lean` proves, for an arbitrary graded ring `𝒜` and a
quasicoherent sheaf `F` on `Proj 𝒜` covered by degree-one charts, that the Čech augmentation

`Γ(Proj 𝒜, F(d)) ⟶ H⁰(Čech complex of Γ_*(F) in degree d)`

is bijective.  This file instantiates it at `𝒜 = R[x₀, …, xₙ]` with the standard homogeneous
coordinates, where the cover hypothesis is
`AlgebraicGeometry.ProjectiveSpace.iSup_basicOpen_X_eq_top`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The standard homogeneous coordinates on `ℙⁿ_R`, as elements of degree one. -/
noncomputable def stdVars : Fin (n + 1) → MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1 :=
  fun i ↦ ⟨MvPolynomial.X i, X_mem_homogeneousSubmodule R n i⟩

@[simp] theorem stdVars_coe (i : Fin (n + 1)) :
    ((stdVars n R i : MvPolynomial (Fin (n + 1)) R)) = MvPolynomial.X i := rfl

/-- The standard charts cover `Proj R[x₀, …, xₙ]`, in the form the `H⁰` comparison wants. -/
theorem top_le_iSup_basicOpen_stdVars :
    (⊤ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Opens)
      ≤ ⨆ i : Fin (n + 1),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          ((stdVars n R i : MvPolynomial (Fin (n + 1)) R)) :=
  le_of_eq (iSup_basicOpen_X_eq_top R n).symm

variable {n R}

/-- **The `H⁰` comparison on `ℙⁿ_R`.**  For a sheaf `F` on `Proj R[x₀, …, xₙ]` all of whose
twists are quasicoherent, the Čech augmentation from the global sections of `F(d)` into the
degree-`d` part of `H⁰` of the Čech complex of `Γ_*(F)` is bijective. -/
theorem bijective_gammaStar_cechAug_std
    (π : Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ⟶ Spec (CommRingCat.of R))
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F e).IsQuasicoherent] (d : ℤ) :
    Function.Bijective
      (((Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) π F
        (stdVars n R)).cechAug d).hom) :=
  Proj.bijective_gammaStar_cechAug _ π F (stdVars n R)
    (top_le_iSup_basicOpen_stdVars n R) d

/-- The `H⁰` comparison on `ℙⁿ_R`, as an `R`-linear equivalence. -/
noncomputable def cechHgrZeroEquivStd
    (π : Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ⟶ Spec (CommRingCat.of R))
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F e).IsQuasicoherent] (d : ℤ) :
    ((Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) π F
        (stdVars n R)).cechHgr 0).obj d
      ≃ₗ[CommRingCat.of R]
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) π F
        (stdVars n R)).obj d :=
  Proj.cechHgrZeroEquiv _ π F (stdVars n R) (top_le_iSup_basicOpen_stdVars n R) d

set_option synthInstance.maxHeartbeats 800000 in
/-- **Every twist of a finitely presented sheaf on `ℙⁿ_R` is quasicoherent.**  This discharges
the hypothesis that every result of the `H⁰` chain carries. -/
theorem twistModule_std_isQuasicoherent
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    [F.IsFinitePresentation] (d : ℤ) :
    (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d).IsQuasicoherent :=
  ProjectiveSpectrum.Twist.twistModule_isQuasicoherent _
    (fun k : ULift.{u} (Fin (n + 1)) ↦
      (MvPolynomial.X k.down : MvPolynomial (Fin (n + 1)) R))
    (fun k ↦ X_mem_homogeneousSubmodule R n k.down)
    (by rw [iSup_ulift]; exact iSup_basicOpen_X_eq_top R n) F d

set_option synthInstance.maxHeartbeats 800000 in
/-- **The `H⁰` comparison on `ℙⁿ_R`, for a finitely presented sheaf.**  The quasicoherence of the
twists is now supplied rather than assumed. -/
theorem bijective_gammaStar_cechAug_of_isFinitePresentation
    (π : Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ⟶ Spec (CommRingCat.of R))
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    [F.IsFinitePresentation] (d : ℤ) :
    Function.Bijective
      (((Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) π F
        (stdVars n R)).cechAug d).hom) := by
  letI : ∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent F e
  exact bijective_gammaStar_cechAug_std π F d

set_option synthInstance.maxHeartbeats 800000 in
/-- The `H⁰` comparison on `ℙⁿ_R` for a finitely presented sheaf, as an `R`-linear
equivalence. -/
noncomputable def cechHgrZeroEquivOfIsFinitePresentation
    (π : Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ⟶ Spec (CommRingCat.of R))
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    [F.IsFinitePresentation] (d : ℤ) :
    ((Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) π F
        (stdVars n R)).cechHgr 0).obj d
      ≃ₗ[CommRingCat.of R]
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) π F
        (stdVars n R)).obj d :=
  (LinearEquiv.ofBijective
    ((Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) π F
      (stdVars n R)).cechAug d).hom
    (bijective_gammaStar_cechAug_of_isFinitePresentation π F d)).symm

end AlgebraicGeometry.ProjectiveSpace
