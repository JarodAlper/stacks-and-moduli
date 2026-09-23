module

public import StacksAndModuli.API.ProjGammaStarQuotientSurjectivity
public import StacksAndModuli.API.ProjGammaStarChartBaseChange
public import StacksAndModuli.API.ProjGammaStarCechBaseChange
public import StacksAndModuli.API.ProjGammaStarTwistedFreeAmbient
public import StacksAndModuli.API.SchemeModulesKernelFinitePresentation

/-!
# The fibre of `Γ_*` of the kernel of a presentation

For a presentation `p : E ⟶ Q` on `ℙⁿ_{Spec R}` and a ring map `R → S`, the base change
`Γ_*(ker p) ⊗_R S` does **not** compute `Γ_*` of the kernel of the base-changed presentation
in each degree — `Γ_*` is only left exact.  It does after localizing at any variable, as soon
as `Q` is flat over the base: on a chart the sections of the short exact sequence
`0 → K → E → Q → 0` stay short exact, base change kills no kernel because the chart sections
of `Q` are flat, and the chart sections of everything base change along affine charts.

This file builds the comparison

`kernelFibreCompare : (Γ_*(ker p)).baseChange S ⟶ Γ_*(ker p_S)`,   `p_S := g^* p`,

proves it is bijective in nonnegative degrees after localizing at any single variable
(a four-lemma argument against the base-change comparisons of the ambient sheaf and of the
kernel-route quotient model, both already known bijective there), and concludes that it
induces an isomorphism on graded Čech cohomology in every cohomological degree
(`isIso_cechHgrMap_app_of_singleton_bijective`).

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.kernelPullbackCompare`;
* `AlgebraicGeometry.ProjectiveSpace.kernelFibreCompare`;
* `AlgebraicGeometry.ProjectiveSpace.kernelFibreCompare_gammaStarMap_kernel_ι` and
  `…gammaStarBaseChangeHom_gammaStarMap` — the two commuting squares;
* `AlgebraicGeometry.ProjectiveSpace.bijective_locMap_kernelFibreCompare_app`;
* `AlgebraicGeometry.ProjectiveSpace.isIso_cechHgrMap_kernelFibreCompare_app`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry ProjectiveSpectrum.Twist

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜S" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S
local notation "πR" => Proj.polynomialToSpec (Fin (n + 1)) R
local notation "πS" => Proj.polynomialToSpec (Fin (n + 1)) S

variable {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
variable (p : F ⟶ F')

/-- The comparison from the pullback of the kernel to the kernel of the pullback. -/
def kernelPullbackCompare :
    (Scheme.Modules.pullback (coeffMap n φ)).obj (kernel p) ⟶
      kernel ((Scheme.Modules.pullback (coeffMap n φ)).map p) :=
  kernel.lift _ ((Scheme.Modules.pullback (coeffMap n φ)).map (kernel.ι p))
    (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero])

/-- **The fibre comparison for `Γ_*` of the kernel**: base change `Γ_*(ker p)`, compare into
`Γ_*` of the pulled-back kernel, then map into the kernel of the pulled-back
presentation. -/
def kernelFibreCompare :
    letI : Algebra R S := φ.toAlgebra
    ((Proj.gammaStar 𝒜R πR (kernel p) (stdVars n R)).baseChange S) ⟶
      Proj.gammaStar 𝒜S πS (kernel ((Scheme.Modules.pullback (coeffMap n φ)).map p))
        (stdVars n S) :=
  gammaStarBaseChangeHom n φ (kernel p) ≫
    Proj.gammaStarMap 𝒜S πS (kernelPullbackCompare n φ p) (stdVars n S)

/-- **The kernel square**: the fibre comparison intertwines the base change of
`Γ_*(ker p) ⟶ Γ_*(E)` with `Γ_*(ker p_S) ⟶ Γ_*(E_S)`. -/
theorem kernelFibreCompare_gammaStarMap_kernel_ι :
    letI : Algebra R S := φ.toAlgebra
    GradedModule.baseChangeMap
        (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R)) S ≫
      gammaStarBaseChangeHom n φ F
    = kernelFibreCompare n φ p ≫
      Proj.gammaStarMap 𝒜S πS
        (kernel.ι ((Scheme.Modules.pullback (coeffMap n φ)).map p)) (stdVars n S) := by
  rw [gammaStarBaseChangeHom_naturality n φ (kernel.ι p)]
  rw [kernelFibreCompare, Category.assoc, ← Proj.gammaStarMap_comp]
  rw [show kernelPullbackCompare n φ p ≫
      kernel.ι ((Scheme.Modules.pullback (coeffMap n φ)).map p) =
    (Scheme.Modules.pullback (coeffMap n φ)).map (kernel.ι p) from kernel.lift_ι _ _ _]

/-- **The presentation square**: the base-change comparisons intertwine the base change of
`Γ_*(E) ⟶ Γ_*(Q)` with `Γ_*(E_S) ⟶ Γ_*(Q_S)`. -/
theorem gammaStarBaseChangeHom_gammaStarMap :
    letI : Algebra R S := φ.toAlgebra
    GradedModule.baseChangeMap
        (Proj.gammaStarMap 𝒜R πR p (stdVars n R)) S ≫
      gammaStarBaseChangeHom n φ F'
    = gammaStarBaseChangeHom n φ F ≫
      Proj.gammaStarMap 𝒜S πS
        ((Scheme.Modules.pullback (coeffMap n φ)).map p) (stdVars n S) :=
  gammaStarBaseChangeHom_naturality n φ p

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search
-- slow, and the four-lemma chase mixes the two spellings of the base-changed maps, whose
-- defeq checks are expensive; see the root INSIGHTS.md entry on
-- `(sheafToPresheaf …).IsRightAdjoint`.
/-- **The kernel fibre comparison is bijective on each chart, in nonnegative degrees.**

A four-lemma chase: the comparisons for the ambient sheaf and for the quotient are bijective
there (`bijective_locMap_gammaStarBaseChangeHom_app`), the bottom row is left exact because
`Γ_*` is, and the top row is exact because localizing the kernel-route short exact sequence
gives flat chart sections for the quotient model, so base change preserves the sequence. -/
theorem bijective_locMap_kernelFibreCompare_app
    [IsNoetherianRing R] [F.IsFinitePresentation] [F'.IsFinitePresentation] [Epi p]
    (hflat : F'.FlatOver (projSpecπ n R)) (a : Fin (n + 1)) (dN : ℕ) :
    letI : Algebra R S := φ.toAlgebra
    Function.Bijective
      (((GradedModule.locMap [a] (kernelFibreCompare n φ p)).app (dN : ℤ)).hom) := by
  letI : Algebra R S := φ.toAlgebra
  -- instances
  haveI hKfp : (kernel p).IsFinitePresentation := Scheme.Modules.kernel_isFinitePresentation p
  haveI : ∀ e : ℤ, (twistModule 𝒜R F e).IsQuasicoherent :=
    fun e => twistModule_std_isQuasicoherent F e
  haveI : ∀ e : ℤ, (twistModule 𝒜R F' e).IsQuasicoherent :=
    fun e => twistModule_std_isQuasicoherent F' e
  haveI : ∀ e : ℤ, (twistModule 𝒜R (kernel p) e).IsQuasicoherent :=
    fun e => twistModule_std_isQuasicoherent (kernel p) e
  set pS : (Scheme.Modules.pullback (coeffMap n φ)).obj F ⟶
      (Scheme.Modules.pullback (coeffMap n φ)).obj F' :=
    (Scheme.Modules.pullback (coeffMap n φ)).map p with hpS
  -- the three vertical comparisons
  have hβ : Function.Bijective
      (((GradedModule.locMap [a] (gammaStarBaseChangeHom n φ F)).app (dN : ℤ)).hom) :=
    bijective_locMap_gammaStarBaseChangeHom_app n φ F a dN
  have hγ : Function.Bijective
      (((GradedModule.locMap [a] (gammaStarBaseChangeHom n φ F')).app (dN : ℤ)).hom) :=
    bijective_locMap_gammaStarBaseChangeHom_app n φ F' a dN
  -- the bottom row is left exact
  have hι'inj : Function.Injective
      (((GradedModule.locMap [a]
        (Proj.gammaStarMap 𝒜S πS (kernel.ι pS) (stdVars n S))).app (dN : ℤ)).hom) :=
    GradedModule.injective_locMap_app_of_injective _ [a] _ (dN : ℤ) (fun t =>
      Proj.injective_gammaStarMap_kernel_ι (Fin (n + 1)) πS (stdVars n S) pS _)
  have hexact' : Function.Exact
      (((GradedModule.locMap [a]
        (Proj.gammaStarMap 𝒜S πS (kernel.ι pS) (stdVars n S))).app (dN : ℤ)).hom)
      (((GradedModule.locMap [a]
        (Proj.gammaStarMap 𝒜S πS pS (stdVars n S))).app (dN : ℤ)).hom) :=
    GradedModule.exact_locMap_app [a] _ _ (dN : ℤ) (fun t =>
      Proj.exact_gammaStarMap_kernel (Fin (n + 1)) πS (stdVars n S) pS _)
  -- the localized kernel-route short exact sequence over `R`, base changed to `S`
  have hSEloc := GradedModule.loc_shortExact (l := [a]) _
    (Proj.shortExact_gammaStar_toCoker_kernel πR p)
  have hSEbc := GradedModule.shortExact_baseChangeMap hSEloc
    (Proj.isFlat_loc_kernelQuotientModule p a hflat) S
  -- names for the localization/base-change interchange equivalences
  have hbK := GradedModule.bijective_locBaseChangeToTensor S
    (Proj.gammaStar 𝒜R πR (kernel p) (stdVars n R)) [a] (dN : ℤ)
  have hbE := GradedModule.bijective_locBaseChangeToTensor S
    (Proj.gammaStar 𝒜R πR F (stdVars n R)) [a] (dN : ℤ)
  have hbN := GradedModule.bijective_locBaseChangeToTensor S
    (Proj.kernelQuotientModule 𝒜R πR (stdVars n R) p) [a] (dN : ℤ)
  -- the interchange squares, as function identities
  have hswι := congrArg ModuleCat.Hom.hom
    (GradedModule.locBaseChangeToTensor_locMap S
      (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R)) [a] (dN : ℤ))
  simp only [ModuleCat.hom_comp] at hswι
  have hswc := congrArg ModuleCat.Hom.hom
    (GradedModule.locBaseChangeToTensor_locMap S
      (GradedModule.toCoker
        (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R))) [a] (dN : ℤ))
  simp only [ModuleCat.hom_comp] at hswc
  -- injectivity of the localized base change of the kernel inclusion
  have htιinj : Function.Injective
      (((GradedModule.locMap [a] (GradedModule.baseChangeMap
        (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R)) S)).app (dN : ℤ)).hom) := by
    intro u v huv
    refine hbK.1 ?_
    have h1 : Function.Injective (ModuleCat.ofHom (LinearMap.baseChange S
        (((GradedModule.locMap [a]
          (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R))).app (dN : ℤ)).hom))).hom :=
      hSEbc.injective (dN : ℤ)
    refine h1 ?_
    have hu := LinearMap.congr_fun hswι u
    have hv := LinearMap.congr_fun hswι v
    simp only [LinearMap.comp_apply] at hu hv
    exact hu.symm.trans (by rw [huv, hv])
  -- exactness of the top row at the middle spot
  have htexact : ∀ b, (((GradedModule.locMap [a] (GradedModule.baseChangeMap
        (Proj.gammaStarMap 𝒜R πR p (stdVars n R)) S)).app (dN : ℤ)).hom b = 0) →
      ∃ a₀, (((GradedModule.locMap [a] (GradedModule.baseChangeMap
        (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R)) S)).app (dN : ℤ)).hom a₀ = b) := by
    intro b hb
    -- factor the presentation map through the kernel-route quotient model
    have hfac : GradedModule.baseChangeMap
        (Proj.gammaStarMap 𝒜R πR p (stdVars n R)) S =
      GradedModule.baseChangeMap
          (GradedModule.toCoker
            (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R))) S ≫
        GradedModule.baseChangeMap
          (Proj.kernelQuotientToGammaStar 𝒜R πR (stdVars n R) p) S := by
      rw [← GradedModule.baseChangeMap_comp]
      rfl
    have hkQinj : Function.Injective
        (((GradedModule.locMap [a] (GradedModule.baseChangeMap
          (Proj.kernelQuotientToGammaStar 𝒜R πR (stdVars n R) p) S)).app (dN : ℤ)).hom) :=
      (GradedModule.bijective_locMap_baseChangeMap_app S _ [a] (dN : ℤ)
        (Proj.bijective_locMap_kernelQuotientToGammaStar πR p a (dN : ℤ))).1
    have hcb : (((GradedModule.locMap [a] (GradedModule.baseChangeMap
        (GradedModule.toCoker
          (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R))) S)).app (dN : ℤ)).hom b)
        = 0 := by
      refine hkQinj ?_
      rw [map_zero]
      have hb' := hb
      rw [hfac, GradedModule.locMap_comp] at hb'
      exact hb'
    -- move across the interchange and use the base-changed short exact sequence
    have hcb2 : (ModuleCat.ofHom (LinearMap.baseChange S
        (((GradedModule.locMap [a] (GradedModule.toCoker
          (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R)))).app (dN : ℤ)).hom))).hom
        ((GradedModule.locBaseChangeToTensor S
          (Proj.gammaStar 𝒜R πR F (stdVars n R)) [a] (dN : ℤ)).hom b) = 0 := by
      have hsw := LinearMap.congr_fun hswc b
      simp only [LinearMap.comp_apply] at hsw
      refine hsw.symm.trans ?_
      refine (congrArg (fun z => (GradedModule.locBaseChangeToTensor S
        (GradedModule.coker
          (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R))) [a] (dN : ℤ)).hom z)
        hcb).trans ?_
      exact map_zero _
    have hmem : ((GradedModule.locBaseChangeToTensor S
        (Proj.gammaStar 𝒜R πR F (stdVars n R)) [a] (dN : ℤ)).hom b) ∈
        LinearMap.range ((GradedModule.baseChangeMap (GradedModule.locMap [a]
          (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R))) S).app (dN : ℤ)).hom :=
      (hSEbc.exact (dN : ℤ)).symm.le (LinearMap.mem_ker.mpr hcb2)
    obtain ⟨w, hw⟩ := hmem
    obtain ⟨a₀, ha₀⟩ := hbK.2 w
    refine ⟨a₀, hbE.1 ?_⟩
    have hsw2 : (GradedModule.locBaseChangeToTensor S
        (Proj.gammaStar 𝒜R πR F (stdVars n R)) [a] (dN : ℤ)).hom
        (((GradedModule.locMap [a] (GradedModule.baseChangeMap
          (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R)) S)).app (dN : ℤ)).hom a₀)
      = (ModuleCat.ofHom (LinearMap.baseChange S
          (((GradedModule.locMap [a]
            (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R))).app (dN : ℤ)).hom))).hom
        ((GradedModule.locBaseChangeToTensor S
          (Proj.gammaStar 𝒜R πR (kernel p) (stdVars n R)) [a] (dN : ℤ)).hom a₀) :=
      LinearMap.congr_fun hswι a₀
    have hw' : (ModuleCat.ofHom (LinearMap.baseChange S
          (((GradedModule.locMap [a]
            (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R))).app (dN : ℤ)).hom))).hom w
        = (GradedModule.locBaseChangeToTensor S
          (Proj.gammaStar 𝒜R πR F (stdVars n R)) [a] (dN : ℤ)).hom b := hw
    refine hsw2.trans ?_
    refine Eq.trans ?_ hw'
    exact congrArg (fun z => (ModuleCat.ofHom (LinearMap.baseChange S
          (((GradedModule.locMap [a]
            (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R))).app (dN : ℤ)).hom))).hom z)
        ha₀
  -- the two commuting squares, localized
  have hsq1 := congrArg (fun ψ => (ψ.app (dN : ℤ)).hom)
    (show GradedModule.locMap [a] (GradedModule.baseChangeMap
          (Proj.gammaStarMap 𝒜R πR (kernel.ι p) (stdVars n R)) S) ≫
        GradedModule.locMap [a] (gammaStarBaseChangeHom n φ F)
      = GradedModule.locMap [a] (kernelFibreCompare n φ p) ≫
        GradedModule.locMap [a]
          (Proj.gammaStarMap 𝒜S πS (kernel.ι pS) (stdVars n S)) from by
      rw [← GradedModule.locMap_comp, ← GradedModule.locMap_comp,
        kernelFibreCompare_gammaStarMap_kernel_ι n φ p])
  simp only [GradedModule.comp_app, ModuleCat.hom_comp] at hsq1
  have hsq2 := congrArg (fun ψ => (ψ.app (dN : ℤ)).hom)
    (show GradedModule.locMap [a] (GradedModule.baseChangeMap
          (Proj.gammaStarMap 𝒜R πR p (stdVars n R)) S) ≫
        GradedModule.locMap [a] (gammaStarBaseChangeHom n φ F')
      = GradedModule.locMap [a] (gammaStarBaseChangeHom n φ F) ≫
        GradedModule.locMap [a]
          (Proj.gammaStarMap 𝒜S πS pS (stdVars n S)) from by
      rw [← GradedModule.locMap_comp, ← GradedModule.locMap_comp,
        gammaStarBaseChangeHom_gammaStarMap n φ p])
  simp only [GradedModule.comp_app, ModuleCat.hom_comp] at hsq2
  -- the four-lemma chase
  constructor
  · intro u v huv
    refine htιinj ?_
    refine hβ.1 ?_
    have hu := LinearMap.congr_fun hsq1 u
    have hv := LinearMap.congr_fun hsq1 v
    simp only [LinearMap.comp_apply] at hu hv
    rw [hu, hv, huv]
  · intro y'
    obtain ⟨b, hb⟩ := hβ.2
      (((GradedModule.locMap [a]
        (Proj.gammaStarMap 𝒜S πS (kernel.ι pS) (stdVars n S))).app (dN : ℤ)).hom y')
    have hker : (((GradedModule.locMap [a] (GradedModule.baseChangeMap
        (Proj.gammaStarMap 𝒜R πR p (stdVars n R)) S)).app (dN : ℤ)).hom b) = 0 := by
      refine hγ.1 ?_
      have hs := LinearMap.congr_fun hsq2 b
      simp only [LinearMap.comp_apply] at hs
      rw [hs, hb, map_zero]
      exact hexact'.apply_apply_eq_zero y'
    obtain ⟨a₀, ha₀⟩ := htexact b hker
    refine ⟨a₀, hι'inj ?_⟩
    have hs := LinearMap.congr_fun hsq1 a₀
    simp only [LinearMap.comp_apply] at hs
    rw [← hs, ha₀, hb]

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search
-- slow; see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
/-- **The kernel fibre comparison is an isomorphism on graded Čech cohomology in every
cohomological degree**, in nonnegative twists.  Consequently the fibrewise cohomology of
`Γ_*(ker p)` is computed by `Γ_*` of the kernel of the base-changed presentation. -/
theorem isIso_cechHgrMap_kernelFibreCompare_app
    [IsNoetherianRing R] [F.IsFinitePresentation] [F'.IsFinitePresentation] [Epi p]
    (hflat : F'.FlatOver (projSpecπ n R)) (q : ℕ) (dN : ℕ) :
    letI : Algebra R S := φ.toAlgebra
    IsIso ((GradedModule.cechHgrMap (kernelFibreCompare n φ p) q).app (dN : ℤ)) := by
  letI : Algebra R S := φ.toAlgebra
  refine GradedModule.isIso_cechHgrMap_app_of_singleton_bijective _ q (dN : ℤ)
    (fun a t => ?_)
  refine GradedModule.bijective_locMap_app_of_eq _ [a]
    (show (dN : ℤ) + (t : ℤ) = ((dN + t : ℕ) : ℤ) by push_cast; ring) ?_
  exact bijective_locMap_kernelFibreCompare_app n φ p hflat a (dN + t)

end AlgebraicGeometry.ProjectiveSpace

end
