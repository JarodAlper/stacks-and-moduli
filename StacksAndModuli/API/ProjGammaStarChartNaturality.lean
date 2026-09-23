module

public import StacksAndModuli.API.ProjGammaStarChartComparison

/-!
# The chart comparison is natural in the sheaf

`AlgebraicGeometry.Proj.chartColimitMap` compares `Γ_*(F)[1/xᵢ]` in degree `d` with the sections
of `F(d)` on the chart `D₊(xᵢ)`, and `Proj.bijective_chartColimitMap` (Hartshorne II.5.14) says
it is bijective.  `Proj.chartColimitMap_locMap` records its naturality in a morphism *into*
`Γ_*(F)`; this file records the other naturality, in the sheaf `F` itself.

It is what a *quotient* model needs.  For a presentation `E ↠ Q` the comparison
`Γ_*(E)/Γ_*(K) ⟶ Γ_*(Q)` is only known to be injective, and the way to see that it becomes
bijective after localizing at `xᵢ` is to push the whole square onto the chart, where `Γ` is
exact (`ProjectiveSpace.surjective_app_polynomialBasicOpen_of_shortExact`).

The proof is the tensor interchange law `Scheme.Modules.tensorMap_exchange`: `twistModuleMap`
tensors on the left, `twistModuleMulHom` on the right.

Main declarations:

* `AlgebraicGeometry.Proj.twistModuleMulHom_comp_twistModuleMap`;
* `AlgebraicGeometry.Proj.chartTwistLinearEquiv_symm_twistModuleMap`;
* `AlgebraicGeometry.Proj.chartStageMap_gammaStarMap`;
* `AlgebraicGeometry.Proj.chartColimitMap_gammaStarMap`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {n : ℕ} {R : CommRingCat.{u}} (π : Proj 𝒜 ⟶ Spec R)
variable (x : Fin (n + 1) → 𝒜 1) (i : Fin (n + 1))

/-- Multiplication by `xᵢ^k` on the chart is natural in the sheaf. -/
theorem twistModuleMulHom_comp_twistModuleMap {F F' : (Proj 𝒜).Modules} (p : F ⟶ F')
    {m : ℕ} (c : 𝒜 m) (d ec : ℤ) (hec : ec = d + (m : ℤ)) :
    twistModuleMulHom 𝒜 F c d ec hec ≫ twistModuleMap 𝒜 p ec
      = twistModuleMap 𝒜 p d ≫ twistModuleMulHom 𝒜 F' c d ec hec :=
  Scheme.Modules.tensorMap_exchange p (mulHom 𝒜 c d ec hec)

/-- The chart trivialization is natural in the sheaf. -/
theorem chartTwistLinearEquiv_symm_twistModuleMap {F F' : (Proj 𝒜).Modules} (p : F ⟶ F')
    (d : ℤ) (k : ℕ) (ec : ℤ) (hec : ec = d + (k : ℤ))
    (v : Γ(twistModule 𝒜 F ec, basicOpen 𝒜 ((x i : A)))) :
    (chartTwistLinearEquiv 𝒜 π F' x i d k ec hec).symm
        (Scheme.Modules.Hom.app (twistModuleMap 𝒜 p ec) (basicOpen 𝒜 ((x i : A))) v)
      = Scheme.Modules.Hom.app (twistModuleMap 𝒜 p d) (basicOpen 𝒜 ((x i : A)))
          ((chartTwistLinearEquiv 𝒜 π F x i d k ec hec).symm v) := by
  set w := (chartTwistLinearEquiv 𝒜 π F x i d k ec hec).symm v with hw
  have hv : Scheme.Modules.Hom.app
      (twistModuleMulHom 𝒜 F (⟨((x i : A)) ^ k, pow_var_mem 𝒜 x i k⟩ : 𝒜 k) d ec hec)
      (basicOpen 𝒜 ((x i : A))) w = v := by
    rw [hw, ← chartTwistLinearEquiv_apply 𝒜 π F x i d k ec hec]
    exact (chartTwistLinearEquiv 𝒜 π F x i d k ec hec).apply_symm_apply v
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  rw [chartTwistLinearEquiv_apply, ← hv]
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app,
    ← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app]
  rw [twistModuleMulHom_comp_twistModuleMap]

/-- **The chart stage map is natural in the sheaf.** -/
theorem chartStageMap_gammaStarMap (F : (Proj 𝒜).Modules) {F' : (Proj 𝒜).Modules} (p : F ⟶ F')
    (d : ℤ) (j : ℕ) (z : (gammaStar 𝒜 π F x).obj (GradedModule.locDeg [i] d j)) :
    chartStageMap 𝒜 π F' x i d j
        (((gammaStarMap 𝒜 π p x).app (GradedModule.locDeg [i] d j)).hom z)
      = Scheme.Modules.Hom.app (twistModuleMap 𝒜 p d) (basicOpen 𝒜 ((x i : A)))
          (chartStageMap 𝒜 π F x i d j z) := by
  rw [chartStageMap_apply, chartStageMap_apply]
  have hres : (twistModule 𝒜 F' (GradedModule.locDeg [i] d j)).presheaf.map
        (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ≤ ⊤)).op
        (Scheme.Modules.Hom.app
          (twistModuleMap 𝒜 p (GradedModule.locDeg [i] d j)) ⊤ z)
      = Scheme.Modules.Hom.app (twistModuleMap 𝒜 p (GradedModule.locDeg [i] d j))
          (basicOpen 𝒜 ((x i : A)))
          ((twistModule 𝒜 F (GradedModule.locDeg [i] d j)).presheaf.map
            (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ≤ ⊤)).op z) := by
    have h := CategoryTheory.congr_fun
      ((twistModuleMap 𝒜 p (GradedModule.locDeg [i] d j)).mapPresheaf.naturality
        (homOfLE (le_top : basicOpen 𝒜 ((x i : A)) ≤ ⊤)).op) z
    simp only [CategoryTheory.comp_apply] at h
    exact h.symm
  rw [show ((gammaStarMap 𝒜 π p x).app (GradedModule.locDeg [i] d j)).hom z
      = Scheme.Modules.Hom.app (twistModuleMap 𝒜 p (GradedModule.locDeg [i] d j)) ⊤ z from rfl,
    hres, chartTwistLinearEquiv_symm_twistModuleMap]

/-- **The chart comparison is natural in the sheaf.** -/
theorem chartColimitMap_gammaStarMap (F : (Proj 𝒜).Modules) {F' : (Proj 𝒜).Modules}
    (p : F ⟶ F') (d : ℤ) (w : ((gammaStar 𝒜 π F x).loc [i]).obj d) :
    chartColimitMap 𝒜 π F' x i d
        (((GradedModule.locMap [i] (gammaStarMap 𝒜 π p x)).app d).hom w)
      = Scheme.Modules.Hom.app (twistModuleMap 𝒜 p d) (basicOpen 𝒜 ((x i : A)))
          (chartColimitMap 𝒜 π F x i d w) := by
  obtain ⟨j, z, rfl⟩ := GradedModule.locIncl_exists (gammaStar 𝒜 π F x) [i] d w
  have hof : chartColimitMap 𝒜 π F x i d
      ((((gammaStar 𝒜 π F x).locIncl [i] d j)).hom z)
      = chartStageMap 𝒜 π F x i d j z := chartColimitMap_of 𝒜 π F x i d j z
  rw [chartColimitMap_locMap 𝒜 π F' x i (gammaStarMap 𝒜 π p x) d j z, hof,
    chartStageMap_gammaStarMap]

end AlgebraicGeometry.Proj

end

end
