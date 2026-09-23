module

public import StacksAndModuli.API.ProjGammaStar
public import StacksAndModuli.API.ProjectiveTwistExact
public import StacksAndModuli.API.SchemeModulesKernelSections
public import StacksAndModuli.API.OpenCoverQuotient

/-!
# `Γ_*` is left exact

Twisting by `𝒪(d)` on polynomial projective spectrum is exact
(`ProjectiveSpectrum.Twist.polynomialTensorKernelIso`), and global sections are left exact
(`Scheme.Modules.exact_kernel_ι_app`).  Composing the two, `Γ_*` carries the kernel of a
morphism of sheaves to the kernel of the induced morphism of graded modules, degreewise.

This is the identification `Γ_*(K) = ker(Γ_*(E) → Γ_*(Q))` used by the kernel route to
`RelativeCohomology.IsCoherent` and `RelativeCohomology.IsFlat`: it makes `Γ_*(K)` a graded
submodule of `Γ_*(E)`, which for `E = 𝒪(-l)^{⊕r}` is finitely generated over the polynomial
ring,
and it exhibits `Γ_*(E) ⧸ Γ_*(K)` as a submodule of `Γ_*(Q)`, which over a DVR is
torsion-free as soon as `Q` is flat (`GradedModule.IsFlat.coker_of_exact`).

Main declarations:

* `AlgebraicGeometry.Proj.polynomialTensorKernelIso_inv_twistModuleMap`;
* `AlgebraicGeometry.Proj.injective_gammaStarMap_kernel_ι`;
* `AlgebraicGeometry.Proj.exact_gammaStarMap_kernel`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (i : Type) {R : Type u} [CommRing R] {n : ℕ}
variable {R₀ : CommRingCat.{u}}
variable (π : Proj (MvPolynomial.homogeneousSubmodule i R) ⟶ Spec R₀)
variable {F F' : (Proj (MvPolynomial.homogeneousSubmodule i R)).Modules}
variable (x : Fin (n + 1) → MvPolynomial.homogeneousSubmodule i R 1)

/-- **The twist of a kernel inclusion is the inclusion of the kernel of the twist**, in the
form supplied by `PreservesKernel.iso_inv_ι`. -/
theorem polynomialTensorKernelIso_inv_twistModuleMap (f : F ⟶ F') (d : ℤ) :
    (ProjectiveSpectrum.Twist.polynomialTensorKernelIso i f d).inv ≫
        ProjectiveSpectrum.Twist.twistModuleMap
          (MvPolynomial.homogeneousSubmodule i R) (kernel.ι f) d
      = kernel.ι (ProjectiveSpectrum.Twist.twistModuleMap
          (MvPolynomial.homogeneousSubmodule i R) f d) :=
  PreservesKernel.iso_inv_ι _ f

/-- **`Γ_*` of a kernel inclusion is injective in every degree.** -/
theorem injective_gammaStarMap_kernel_ι (f : F ⟶ F') (d : ℤ) :
    Function.Injective ((gammaStarMap (MvPolynomial.homogeneousSubmodule i R)
      π (kernel.ι f) x).app d).hom := by
  haveI : Mono (ProjectiveSpectrum.Twist.twistModuleMap
      (MvPolynomial.homogeneousSubmodule i R) (kernel.ι f) d) :=
    ProjectiveSpectrum.Twist.polynomial_tensorMapLeft_mono i (kernel.ι f) d
  intro a b hab
  exact Scheme.Modules.app_injective_of_mono
    (ProjectiveSpectrum.Twist.twistModuleMap
      (MvPolynomial.homogeneousSubmodule i R) (kernel.ι f) d) ⊤ hab

/-- **`Γ_*` is left exact.**  In every degree, the sections of `Γ_*(F)` killed by `f` are
exactly those coming from `Γ_*(ker f)`. -/
theorem exact_gammaStarMap_kernel (f : F ⟶ F') (d : ℤ) :
    Function.Exact ((gammaStarMap (MvPolynomial.homogeneousSubmodule i R)
        π (kernel.ι f) x).app d).hom
      ((gammaStarMap (MvPolynomial.homogeneousSubmodule i R) π f x).app d).hom := by
  intro s
  refine (Scheme.Modules.exact_kernel_ι_app
    (ProjectiveSpectrum.Twist.twistModuleMap
      (MvPolynomial.homogeneousSubmodule i R) f d) ⊤ s).trans ?_
  have hfac : ∀ y, ((kernel.ι (ProjectiveSpectrum.Twist.twistModuleMap
        (MvPolynomial.homogeneousSubmodule i R) f d)).app ⊤).hom y
      = ((ProjectiveSpectrum.Twist.twistModuleMap
          (MvPolynomial.homogeneousSubmodule i R) (kernel.ι f) d).app ⊤).hom
        (((ProjectiveSpectrum.Twist.polynomialTensorKernelIso i f d).inv.app ⊤).hom y) :=
    fun y ↦ (congrArg (fun ψ ↦ (ψ.app ⊤).hom y)
      (polynomialTensorKernelIso_inv_twistModuleMap i f d)).symm
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨_, (hfac y).symm.trans hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨((ProjectiveSpectrum.Twist.polynomialTensorKernelIso i f d).hom.app ⊤).hom y, ?_⟩
    rw [hfac]
    have hyy : ((ProjectiveSpectrum.Twist.polynomialTensorKernelIso i f d).inv.app ⊤).hom
        (((ProjectiveSpectrum.Twist.polynomialTensorKernelIso i f d).hom.app ⊤).hom y) = y :=
      congrArg (fun ψ ↦ (ψ.app ⊤).hom y)
        (ProjectiveSpectrum.Twist.polynomialTensorKernelIso i f d).hom_inv_id
    rw [hyy]
    exact hy

end AlgebraicGeometry.Proj

end

end
