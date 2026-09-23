module

public import StacksAndModuli.API.ProjGammaStarKernel
public import StacksAndModuli.API.ProjGammaStarTwistedFreeAmbient

/-!
# The kernel-route graded model of a quotient sheaf

For a presentation `E ⟶ Q` of a sheaf on `Proj 𝒜` with kernel `K`, the kernel route of
`PLAN-hilbert-quot.md` models `Q` by the graded module

`N := Γ_*(E) ⧸ Γ_*(K)`,

which is finitely generated as soon as `Γ_*(E)` is (`GradedModule.IsFG.coker`) and flat over a
DVR as soon as `Q` is (`GradedModule.IsFlat.coker_of_exact`).  This file builds the comparison
`N ⟶ Γ_*(Q)` and shows it is **degreewise injective**, so `N` really is a graded submodule of
`Γ_*(Q)` — the statement the flatness argument uses, and half of the identification `Ñ ≅ Q`.

Three small pieces of ambient API are supplied on the way:

* `GradedModule.cokerDesc`, the universal property of `GradedModule.coker` (only `coker` and
  `toCoker` existed);
* `ProjectiveSpectrum.Twist.twistModuleMap_zero`, immediate from additivity of
  `Scheme.Modules.tensorRightFunctor` — note that `GradedModule` is **not** registered as a
  preadditive category, so there is no zero morphism of graded modules and the vanishing of
  the composite `Γ_*(K) → Γ_*(E) → Γ_*(Q)` has to be stated pointwise
  (`gammaStarMap_kernel_ι_app_apply`);
* `AlgebraicGeometry.Proj.gammaStarMap_kernel_ι_app_apply` itself.

Injectivity is left-exactness of `Γ_*` (`AlgebraicGeometry.Proj.exact_gammaStarMap_kernel`,
`API/ProjGammaStarKernel.lean`) read through `Submodule.ker_liftQ_eq_bot`; it is stated for
polynomial `Proj`, where the twists are locally free, since that is where left-exactness of
`Γ_*` is available.

What is **not** proved here is surjectivity in large degrees, equivalently `Ñ ≅ Q`; that is
the remaining geometric input of the kernel route and needs the chart comparison
(`AlgebraicGeometry.Proj.bijective_locMap_app_iff_bijective_comp`).

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.GradedModule.cokerDesc`;
* `AlgebraicGeometry.Proj.gammaStarMap_kernel_ι_app_apply`;
* `AlgebraicGeometry.Proj.kernelQuotientModule` and `kernelQuotientToGammaStar`;
* `AlgebraicGeometry.Proj.injective_kernelQuotientToGammaStar`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {k : Type u} [CommRing k] {n : ℕ}

/-- The universal property of the degreewise cokernel. -/
noncomputable def cokerDesc {A B C : GradedModule k n} (f : A ⟶ B) (g : B ⟶ C)
    (h : ∀ (d : ℤ) (a : A.obj d), (g.app d).hom ((f.app d).hom a) = 0) :
    coker f ⟶ C where
  app d := ModuleCat.ofHom
    (Submodule.liftQ _ (g.app d).hom (by rintro _ ⟨a, rfl⟩; exact h d a))
  comm i d := by
    refine ModuleCat.hom_ext (LinearMap.ext ?_)
    rintro ⟨x⟩
    exact congrArg (fun ψ : B.obj d ⟶ C.obj (d + 1) ↦ ψ.hom x) (g.comm i d)

@[simp] theorem toCoker_cokerDesc {A B C : GradedModule k n} (f : A ⟶ B) (g : B ⟶ C)
    (h : ∀ (d : ℤ) (a : A.obj d), (g.app d).hom ((f.app d).hom a) = 0) :
    toCoker f ≫ cokerDesc f g h = g := rfl

end AlgebraicGeometry.ProjectiveSpace.GradedModule
namespace ProjectiveSpectrum.Twist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]

/-- Twisting the zero morphism gives the zero morphism. -/
theorem twistModuleMap_zero (𝒜 : ℕ → σ) [GradedRing 𝒜] (F F' : (Proj 𝒜).Modules) (d : ℤ) :
    twistModuleMap 𝒜 (0 : F ⟶ F') d = 0 :=
  (Scheme.Modules.tensorRightFunctor (twist 𝒜 d)).map_zero F F'

end ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {n : ℕ} {R : CommRingCat.{u}} (f : Proj 𝒜 ⟶ Spec R) (x : Fin (n + 1) → 𝒜 1)

/-- **`Γ_*` kills the composite `K → E → Q`.**  This is the condition that lets the kernel
route factor `Γ_*(E) ⟶ Γ_*(Q)` through the cokernel of `Γ_*(K) ⟶ Γ_*(E)`. -/
theorem gammaStarMap_kernel_ι_app_apply {F F' : (Proj 𝒜).Modules} (p : F ⟶ F') (d : ℤ)
    (s : (gammaStar 𝒜 f (kernel p) x).obj d) :
    ((gammaStarMap 𝒜 f p x).app d).hom
        (((gammaStarMap 𝒜 f (kernel.ι p) x).app d).hom s) = 0 := by
  have hcomp : twistModuleMap 𝒜 (kernel.ι p) d ≫ twistModuleMap 𝒜 p d = 0 := by
    rw [← twistModuleMap_comp, kernel.condition, twistModuleMap_zero]
  exact congrArg (fun ψ : twistModule 𝒜 (kernel p) d ⟶ twistModule 𝒜 F' d ↦
    (PresheafOfModules.Hom.app ψ.val (op ⊤)).hom s) hcomp

/-- **The kernel-route graded model of a quotient sheaf**: `Γ_*(E) ⧸ Γ_*(K)`, where
`K = ker(E ⟶ Q)`. -/
noncomputable abbrev kernelQuotientModule {F F' : (Proj 𝒜).Modules} (p : F ⟶ F') :
    ProjectiveSpace.GradedModule R n :=
  ProjectiveSpace.GradedModule.coker (gammaStarMap 𝒜 f (kernel.ι p) x)

/-- **The comparison `Γ_*(E) ⧸ Γ_*(K) ⟶ Γ_*(Q)`.** -/
noncomputable def kernelQuotientToGammaStar {F F' : (Proj 𝒜).Modules} (p : F ⟶ F') :
    kernelQuotientModule 𝒜 f x p ⟶ gammaStar 𝒜 f F' x :=
  ProjectiveSpace.GradedModule.cokerDesc _ (gammaStarMap 𝒜 f p x)
    (gammaStarMap_kernel_ι_app_apply 𝒜 f x p)

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist

attribute [local instance] MvPolynomial.gradedAlgebra

variable (i : Type) {R : Type u} [CommRing R] {n : ℕ} {R₀ : CommRingCat.{u}}
variable (π : Proj (MvPolynomial.homogeneousSubmodule i R) ⟶ Spec R₀)
variable (x : Fin (n + 1) → MvPolynomial.homogeneousSubmodule i R 1)

/-- **The kernel-route comparison is degreewise injective**, so `Γ_*(E) ⧸ Γ_*(K)` is a graded
submodule of `Γ_*(Q)`.  This is left-exactness of `Γ_*` (`exact_gammaStarMap_kernel`) read
through the universal property of the cokernel. -/
theorem injective_kernelQuotientToGammaStar
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule i R)).Modules} (p : F ⟶ F') (d : ℤ) :
    Function.Injective
      ((kernelQuotientToGammaStar (MvPolynomial.homogeneousSubmodule i R) π x p).app d).hom := by
  have hex := exact_gammaStarMap_kernel i π x p d
  rw [LinearMap.ker_eq_bot.symm]
  refine Submodule.ker_liftQ_eq_bot _ _ _ ?_
  intro y hy
  exact (hex y).mp hy

end AlgebraicGeometry.Proj

end

end
