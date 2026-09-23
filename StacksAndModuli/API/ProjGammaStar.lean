module

public import StacksAndModuli.API.ProjTwistMulHom
public import StacksAndModuli.API.HilbertPolynomialProj
public import StacksAndModuli.API.ProjectiveGradedModule
public import StacksAndModuli.API.SchemeModulesPullbackTensor

/-!
# `Γ_*` of a sheaf on `Proj` as a graded module

For a sheaf of modules `F` on `Proj 𝒜` and a choice of `n+1` degree-one elements `x₀, …, xₙ` of
`𝒜` (the variables), the global sections of the twists

`Γ_*(F)_d := Γ(Proj 𝒜, F(d))`

form an object of `AlgebraicGeometry.ProjectiveSpace.GradedModule (𝒜 0) n`: the degree-raising
maps are multiplication by the `xᵢ` (`ProjectiveSpectrum.Twist.twistModuleMulHom`), and they
commute because the `xᵢ` do.

This is the object that the graded Čech machinery of §2.3 consumes.  Identifying its localization
at `xᵢ` with `Γ(D₊(xᵢ), F(d))` is the remaining content of Hartshorne II.5.14/II.5.15; see
`PLAN-hilbert-quot.md`.

## Main definitions

* `AlgebraicGeometry.Proj.gammaStar`: `Γ_*(F)` as a graded module;
* `AlgebraicGeometry.Proj.gammaStarMap`: its functoriality in the sheaf.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **`Γ_*(F)` as a graded module** over a base ring `R`, for a chosen structure morphism
`f : Proj 𝒜 ⟶ Spec R` and `n+1` degree-one elements `x` of `𝒜`.

Taking `R = 𝒜 0` and `f = Proj.toSpecZero 𝒜` gives the intrinsic version; the extra generality
costs nothing and matches the situation on `ℙⁿ_R`, where the base ring is given. -/
noncomputable def gammaStar {n : ℕ} {R : CommRingCat.{u}} (f : Proj 𝒜 ⟶ Spec R)
    (F : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1) :
    AlgebraicGeometry.ProjectiveSpace.GradedModule R n :=
  letI (d : ℤ) : Module R Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, ⊤) :=
    Scheme.Modules.globalSectionsModule f (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
  { obj := fun d ↦ ModuleCat.of R Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, ⊤)
    mulX := fun i d ↦ ModuleCat.ofHom
      (Scheme.Modules.globalSectionsLinearMap f
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (x i) d (d + 1) (by norm_num)))
    mulX_comm := fun i j d ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
      have h := ProjectiveSpectrum.Twist.twistModuleMulHom_comm 𝒜 F (x i) (x j) d (d + 1)
        (d + 1 + 1) (by norm_num) (by norm_num)
      exact congrArg
        (fun ψ : ProjectiveSpectrum.Twist.twistModule 𝒜 F d ⟶
            ProjectiveSpectrum.Twist.twistModule 𝒜 F (d + 1 + 1) ↦
          (PresheafOfModules.Hom.app ψ.val (op ⊤)).hom s) h }

@[simp]
theorem gammaStar_mulX_apply {n : ℕ} {R : CommRingCat.{u}} (f : Proj 𝒜 ⟶ Spec R)
    (F : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1) (i : Fin (n + 1)) (d : ℤ)
    (s : (gammaStar 𝒜 f F x).obj d) :
    ((gammaStar 𝒜 f F x).mulX i d).hom s
      = (PresheafOfModules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (x i) d (d + 1)
            (by norm_num)).val (op ⊤)).hom s := rfl

@[simp]
theorem gammaStar_mulX_app_apply {n : ℕ} {R : CommRingCat.{u}} (f : Proj 𝒜 ⟶ Spec R)
    (F : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1) (i : Fin (n + 1)) (d : ℤ)
    (s : (gammaStar 𝒜 f F x).obj d) :
    ((gammaStar 𝒜 f F x).mulX i d).hom s
      = (Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F (x i) d (d + 1)
            (by norm_num)) ⊤).hom s := rfl

/-- **`Γ_*` is functorial in the sheaf.**  A morphism `φ : F ⟶ F'` of sheaves of modules on
`Proj 𝒜` induces a morphism `Γ_*(F) ⟶ Γ_*(F')` of graded modules over the base ring.

The compatibility with multiplication by the variables is the exchange law
`Scheme.Modules.tensorMap_exchange`: `twistModuleMap` tensors on the left and
`twistModuleMulHom` on the right, and the two commute. -/
noncomputable def gammaStarMap {n : ℕ} {R : CommRingCat.{u}} (f : Proj 𝒜 ⟶ Spec R)
    {F F' : (Proj 𝒜).Modules} (φ : F ⟶ F') (x : Fin (n + 1) → 𝒜 1) :
    gammaStar 𝒜 f F x ⟶ gammaStar 𝒜 f F' x :=
  letI (d : ℤ) : Module R Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, ⊤) :=
    Scheme.Modules.globalSectionsModule f (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
  letI (d : ℤ) : Module R Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F' d, ⊤) :=
    Scheme.Modules.globalSectionsModule f (ProjectiveSpectrum.Twist.twistModule 𝒜 F' d)
  { app := fun d ↦ ModuleCat.ofHom
      (Scheme.Modules.globalSectionsLinearMap f
        (ProjectiveSpectrum.Twist.twistModuleMap 𝒜 φ d))
    comm := fun i d ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
      have hex := Scheme.Modules.tensorMap_exchange (X := Proj 𝒜) φ
        (ProjectiveSpectrum.Twist.mulHom 𝒜 (x i) d (d + 1) (by norm_num))
      exact congrArg
        (fun ψ : ProjectiveSpectrum.Twist.twistModule 𝒜 F d ⟶
            ProjectiveSpectrum.Twist.twistModule 𝒜 F' (d + 1) ↦
          (PresheafOfModules.Hom.app ψ.val (op ⊤)).hom s) hex.symm }

end AlgebraicGeometry.Proj
