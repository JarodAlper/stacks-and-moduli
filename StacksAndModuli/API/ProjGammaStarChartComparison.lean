module

public import StacksAndModuli.API.ProjGammaStarChart

/-!
# Comparing a graded module with `Γ_*` chart by chart

Three separate obligations of Chapter 2 have the same shape: a morphism of graded modules
`φ : M ⟶ Γ_*(F)` is to be shown bijective after localizing at a coordinate `xᵢ`.  They are

* `Γ_*(F).baseChange S ⟶ Γ_*(F_S)` (the fibre half of the `H⁰` bridge, `hcbc`);
* `structureModule ⟶ Γ_*(𝒪)` (Hartshorne II.5.13, needed for `GradedModule.IsFG` of a
  twisted-free `Γ_*`);
* `N ⟶ Γ_*(Q)` for the finitely generated model `N` of the kernel route.

This file isolates what they share.  Since `Proj.chartColimitMap` is bijective
(`Proj.bijective_chartColimitMap`, Hartshorne II.5.14), `(locMap [i] φ).app d` is bijective
exactly when its composite with the chart comparison is, and that composite is computed on
the stage inclusions by `Proj.chartColimitMap_locMap`: it is simply
`chartStageMap ∘ φ.app`.  So each of the three obligations reduces to an explicit
computation at one tower stage, with no colimit bookkeeping.

Main declarations:

* `AlgebraicGeometry.Proj.chartColimitMap_locMap`;
* `AlgebraicGeometry.Proj.bijective_locMap_app_iff_bijective_comp`.
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

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {n : ℕ} {R : CommRingCat.{u}} (π : Proj 𝒜 ⟶ Spec R)
variable (F : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1) (i : Fin (n + 1))

/-- **The chart comparison of a morphism into `Γ_*` is its stage map.**  Composing
`GradedModule.locMap` with `Proj.chartColimitMap` turns the stage inclusion at level `j`
into `Proj.chartStageMap` applied to the degree-`(d + j)` component of `φ`. -/
theorem chartColimitMap_locMap {M : ProjectiveSpace.GradedModule R n}
    (φ : M ⟶ gammaStar 𝒜 π F x) (d : ℤ) (j : ℕ)
    (z : M.obj (ProjectiveSpace.GradedModule.locDeg [i] d j)) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
    chartColimitMap 𝒜 π F x i d
        (((ProjectiveSpace.GradedModule.locMap [i] φ).app d).hom
          ((M.locIncl [i] d j).hom z))
      = chartStageMap 𝒜 π F x i d j
        ((φ.app (ProjectiveSpace.GradedModule.locDeg [i] d j)).hom z) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
  rw [ProjectiveSpace.GradedModule.locMap_locIncl_apply]
  exact chartColimitMap_of 𝒜 π F x i d j _

/-- Bijectivity of a localized comparison is bijectivity of its composite with the chart
comparison, since the latter is an isomorphism (Hartshorne II.5.14). -/
theorem bijective_locMap_app_iff_bijective_comp
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent]
    {M : ProjectiveSpace.GradedModule R n}
    (φ : M ⟶ gammaStar 𝒜 π F x) (d : ℤ) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
    Function.Bijective (((ProjectiveSpace.GradedModule.locMap [i] φ).app d).hom) ↔
      Function.Bijective (fun w : (M.loc [i]).obj d ↦
        chartColimitMap 𝒜 π F x i d
          (((ProjectiveSpace.GradedModule.locMap [i] φ).app d).hom w)) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d) (basicOpen 𝒜 ((x i : A)))
  have hchart := bijective_chartColimitMap 𝒜 π F x i hcover d
  constructor
  · intro h
    exact hchart.comp h
  · intro h
    have hcomp : Function.Bijective
        ((chartColimitMap 𝒜 π F x i d) ∘
          (((ProjectiveSpace.GradedModule.locMap [i] φ).app d).hom)) := h
    refine ⟨fun a b hab ↦ hcomp.1 (by simp only [Function.comp_apply, hab]), fun c ↦ ?_⟩
    obtain ⟨w, hw⟩ := hcomp.2 (chartColimitMap 𝒜 π F x i d c)
    exact ⟨w, hchart.1 hw⟩

/-- **The overlap comparison of a morphism into `Γ_*` is its pair stage map.**  The two-variable
analogue of `chartColimitMap_locMap`. -/
theorem pairColimitMap_locMap (j : Fin (n + 1)) {M : ProjectiveSpace.GradedModule R n}
    (φ : M ⟶ gammaStar 𝒜 π F x) (d : ℤ) (t : ℕ)
    (z : M.obj (ProjectiveSpace.GradedModule.locDeg [i, j] d t)) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
      (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
    pairColimitMap 𝒜 π F x i j d
        (((ProjectiveSpace.GradedModule.locMap [i, j] φ).app d).hom
          ((M.locIncl [i, j] d t).hom z))
      = pairStageMap 𝒜 π F x i j d t
        ((φ.app (ProjectiveSpace.GradedModule.locDeg [i, j] d t)).hom z) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
    (basicOpen 𝒜 ((x i : A)) ⊓ basicOpen 𝒜 ((x j : A)))
  rw [ProjectiveSpace.GradedModule.locMap_locIncl_apply]
  exact pairColimitMap_of 𝒜 π F x i j d t _

end AlgebraicGeometry.Proj

end

end
