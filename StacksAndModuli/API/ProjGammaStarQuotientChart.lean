module

public import StacksAndModuli.API.ProjGammaStarChartNaturality
public import StacksAndModuli.API.ProjGammaStarQuotientModel
public import StacksAndModuli.API.ProjectiveGradedCechLocalIso
public import StacksAndModuli.API.ProjectiveGradedLocalizationPair
public import StacksAndModuli.API.PolynomialProjChartNoetherian
public import StacksAndModuli.API.ProjectiveTwistExact

/-!
# The kernel-route graded model computes the quotient sheaf

`API/ProjGammaStarQuotientModel.lean` builds, for a presentation `p : E ↠ Q` with kernel `K` on
polynomial `Proj`, the graded module `N := Γ_*(E) ⧸ Γ_*(K)` together with a degreewise
**injective** comparison `N ⟶ Γ_*(Q)`.  It is not degreewise surjective — `Γ_*` is only left
exact — and it does not need to be:

**On every chart `D₊(xᵢ)` the comparison is bijective**, because the chart is affine and
sections of a short exact sequence of quasicoherent sheaves are exact
(`ProjectiveSpace.surjective_app_polynomialBasicOpen_of_shortExact`).  So `N` and `Γ_*(Q)` have
the same localizations, hence the same graded Čech cohomology in degree zero — which is all
that `RelativeCohomology.SchemeGlobalSectionsComparison` consumes.

The overlap hypothesis of the Čech criterion costs nothing extra:
`GradedModule.injective_locMap_pair_app` derives it from the chart statement.

Main declarations:

* `AlgebraicGeometry.Proj.shortExact_twistModule_kernel`;
* `AlgebraicGeometry.Proj.surjective_app_twistModuleMap_basicOpen`;
* `AlgebraicGeometry.Proj.bijective_locMap_kernelQuotientToGammaStar`;
* `AlgebraicGeometry.Proj.isIso_cechHgrMap_kernelQuotientToGammaStar`.
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
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {R : Type u} [CommRing R] {R₀ : CommRingCat.{u}}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

variable (π : Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ⟶ Spec R₀)

/-- The canonical short exact sequence of an epimorphism, twisted. -/
theorem shortExact_twistModule_kernel
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : F ⟶ F') [Epi p] (d : ℤ) :
    (ShortComplex.mk (twistModuleMap 𝒜 (kernel.ι p) d) (twistModuleMap 𝒜 p d)
      (by rw [← twistModuleMap_comp, kernel.condition, twistModuleMap_zero])).ShortExact := by
  have hS : (ShortComplex.mk (kernel.ι p) p (kernel.condition p)).ShortExact :=
    { exact := CategoryTheory.ShortComplex.exact_kernel p
      mono_f := inferInstance
      epi_g := inferInstance }
  exact ProjectiveSpectrum.Twist.polynomial_shortExact_tensorRightFunctor (Fin (n + 1)) hS d

/-- **On a standard chart, a surjection of sheaves is surjective on twisted sections.** -/
theorem surjective_app_twistModuleMap_basicOpen
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : F ⟶ F') [Epi p] (d : ℤ)
    [(twistModule 𝒜 (kernel p) d).IsQuasicoherent]
    [(twistModule 𝒜 F d).IsQuasicoherent] (i : Fin (n + 1)) :
    Function.Surjective (Scheme.Modules.Hom.app (twistModuleMap 𝒜 p d)
      (Proj.basicOpen 𝒜 (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))) := by
  have h := ProjectiveSpace.surjective_app_polynomialBasicOpen_of_shortExact n R i
    (shortExact_twistModule_kernel p d)
  exact h

/-- **The kernel-route model computes the quotient sheaf on every chart.** -/
theorem bijective_locMap_kernelQuotientToGammaStar
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : F ⟶ F') [Epi p] (i : Fin (n + 1)) (d : ℤ)
    [∀ e : ℤ, (twistModule 𝒜 F e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 F' e).IsQuasicoherent]
    [(twistModule 𝒜 (kernel p) d).IsQuasicoherent] :
    Function.Bijective
      (((GradedModule.locMap [i]
        (kernelQuotientToGammaStar 𝒜 π (ProjectiveSpace.stdVars n R) p)).app d).hom) := by
  have hcover := ProjectiveSpace.top_le_iSup_basicOpen_stdVars n R
  constructor
  · refine GradedModule.injective_locMap_app_of_injective _ [i] _ d fun t => ?_
    exact injective_kernelQuotientToGammaStar (Fin (n + 1)) π (ProjectiveSpace.stdVars n R) p _
  · intro z
    obtain ⟨t, ht⟩ := surjective_app_twistModuleMap_basicOpen p d i
      (chartColimitMap 𝒜 π F' (ProjectiveSpace.stdVars n R) i d z)
    obtain ⟨v, hv⟩ :=
      (bijective_chartColimitMap 𝒜 π F (ProjectiveSpace.stdVars n R) i hcover d).2 t
    refine ⟨((GradedModule.locMap [i]
      (GradedModule.toCoker
        (gammaStarMap 𝒜 π (kernel.ι p) (ProjectiveSpace.stdVars n R)))).app d).hom v, ?_⟩
    have hcomp : GradedModule.locMap [i]
          (GradedModule.toCoker
            (gammaStarMap 𝒜 π (kernel.ι p) (ProjectiveSpace.stdVars n R))) ≫
        GradedModule.locMap [i]
          (kernelQuotientToGammaStar 𝒜 π (ProjectiveSpace.stdVars n R) p)
        = GradedModule.locMap [i] (gammaStarMap 𝒜 π p (ProjectiveSpace.stdVars n R)) := by
      rw [← GradedModule.locMap_comp]
      rfl
    have key := congrArg
      (fun χ : GradedModule.loc _ [i] ⟶ GradedModule.loc _ [i] ↦ ((χ.app d).hom v)) hcomp
    simp only [GradedModule.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at key
    rw [key]
    refine (bijective_chartColimitMap 𝒜 π F' (ProjectiveSpace.stdVars n R) i hcover d).1 ?_
    rw [chartColimitMap_gammaStarMap, hv]
    exact ht

/-- **The kernel-route model has the same degree-zero graded Čech cohomology as `Γ_*(Q)`.** -/
theorem isIso_cechHgrMap_kernelQuotientToGammaStar
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : F ⟶ F') [Epi p] (d : ℤ)
    [∀ e : ℤ, (twistModule 𝒜 F e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 F' e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 (kernel p) e).IsQuasicoherent] :
    IsIso ((GradedModule.cechHgrMap
      (kernelQuotientToGammaStar 𝒜 π (ProjectiveSpace.stdVars n R) p) 0).app d) := by
  refine GradedModule.isIso_cechHgrMap_app_zero_of_injective _ _ (fun τ => ?_) (fun τ => ?_)
  · obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (by simpa using τ.length_eq)
    exact GradedModule.bijective_locMap_app_of_list_eq _ ha _
      (bijective_locMap_kernelQuotientToGammaStar π p a d)
  · obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (by simpa using τ.length_eq)
    refine GradedModule.injective_locMap_app_of_list_eq _ hab _ ?_
    exact GradedModule.injective_locMap_pair_app _ a b _ fun t =>
      bijective_locMap_kernelQuotientToGammaStar π p a (d + (t : ℤ))

end AlgebraicGeometry.Proj

end

end
