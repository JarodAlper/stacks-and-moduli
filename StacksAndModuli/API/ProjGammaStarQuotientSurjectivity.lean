module

public import StacksAndModuli.API.ProjGammaStarQuotientFlat

/-!
# Surjectivity of `Γ_*` of a quotient presentation in a fixed twist

For a presentation `p : E ↠ Q` of sheaves on `ℙⁿ_{Spec R}` and a twist `d` in which the
graded Čech `H¹` of `Γ_*(ker p)` vanishes, the induced map on twisted global sections
`Γ(E(d)) ⟶ Γ(Q(d))` is surjective.

The argument is the long exact sequence of the degreewise short exact sequence

`0 ⟶ Γ_*(K) ⟶ Γ_*(E) ⟶ Γ_*(E) ⧸ Γ_*(K) ⟶ 0`,

read through the Čech augmentations: the augmentation of `Γ_*` of a quasicoherent sheaf is
bijective in every degree (`bijective_gammaStar_cechAug_std`), the augmentation square
commutes (`GradedModule.cechAug_naturality`), the vanishing of `Hᵍʳ¹(Γ_*(K))_d` makes
`Hᵍʳ⁰` of the quotient map surjective, and the kernel-route comparison
`Γ_*(E) ⧸ Γ_*(K) ⟶ Γ_*(Q)` is an isomorphism on `Hᵍʳ⁰`
(`isIso_cechHgrMap_kernelQuotientToGammaStar`).

Main declarations:

* `AlgebraicGeometry.Proj.shortExact_gammaStar_toCoker_kernel`;
* `AlgebraicGeometry.Proj.surjective_cechAug_kernelQuotientModule_of_subsingleton`;
* `AlgebraicGeometry.Proj.surjective_app_kernelQuotientToGammaStar_of_subsingleton`;
* `AlgebraicGeometry.Proj.surjective_app_gammaStarMap_of_subsingleton` — the endpoint:
  vanishing of `Hᵍʳ¹(Γ_*(K))_d` gives surjectivity of `Γ(E(d)) ⟶ Γ(Q(d))`.
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

variable {n : ℕ} {R : Type u} [CommRing R] [IsNoetherianRing R]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

variable (π : Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ⟶
  Spec (CommRingCat.of R))

set_option synthInstance.maxHeartbeats 1000000 in
omit [IsNoetherianRing R] in
/-- **The kernel-route short exact sequence of graded modules**:
`0 ⟶ Γ_*(K) ⟶ Γ_*(E) ⟶ Γ_*(E) ⧸ Γ_*(K) ⟶ 0`. -/
theorem shortExact_gammaStar_toCoker_kernel
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : F ⟶ F') :
    GradedModule.ShortExact
      (gammaStarMap 𝒜 π (kernel.ι p) (ProjectiveSpace.stdVars n R))
      (GradedModule.toCoker
        (gammaStarMap 𝒜 π (kernel.ι p) (ProjectiveSpace.stdVars n R))) :=
  GradedModule.shortExact_toCoker _
    (fun d => injective_gammaStarMap_kernel_ι (Fin (n + 1)) π
      (ProjectiveSpace.stdVars n R) p d)

set_option synthInstance.maxHeartbeats 1000000 in
omit [IsNoetherianRing R] in
/-- **The augmentation of the kernel-route model is surjective** in a twist where the graded
Čech `H¹` of `Γ_*(K)` vanishes. -/
theorem surjective_cechAug_kernelQuotientModule_of_subsingleton
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : F ⟶ F') (d : ℤ)
    [∀ e : ℤ, (twistModule 𝒜 F e).IsQuasicoherent]
    (hvan : Subsingleton
      (((gammaStar 𝒜 π (kernel p) (ProjectiveSpace.stdVars n R)).cechHgr 1).obj d)) :
    Function.Surjective
      (((kernelQuotientModule 𝒜 π (ProjectiveSpace.stdVars n R) p).cechAug d).hom) := by
  have hSE := shortExact_gammaStar_toCoker_kernel π p
  -- `Hᵍʳ⁰` of the quotient map is surjective, by the long exact sequence and the vanishing.
  have hsurj0 : Function.Surjective
      ((GradedModule.cechHgrMap (GradedModule.toCoker
        (gammaStarMap 𝒜 π (kernel.ι p) (ProjectiveSpace.stdVars n R))) 0).app d).hom := by
    intro y
    exact (GradedModule.cech_exact_map_δ hSE 0 d y).mp (Subsingleton.elim _ _)
  -- the augmentation of the ambient sheaf is bijective, by quasicoherence.
  have haugF : Function.Bijective
      (((gammaStar 𝒜 π F (ProjectiveSpace.stdVars n R)).cechAug d).hom) :=
    ProjectiveSpace.bijective_gammaStar_cechAug_std π F d
  -- read the augmentation square.
  have hnat := GradedModule.cechAug_naturality
    (GradedModule.toCoker (gammaStarMap 𝒜 π (kernel.ι p) (ProjectiveSpace.stdVars n R))) d
  intro z
  obtain ⟨w, hw⟩ := hsurj0 z
  obtain ⟨v, hv⟩ := haugF.2 w
  refine ⟨((GradedModule.toCoker
    (gammaStarMap 𝒜 π (kernel.ι p) (ProjectiveSpace.stdVars n R))).app d).hom v, ?_⟩
  have hcomm := congrArg (fun ψ :
      (gammaStar 𝒜 π F (ProjectiveSpace.stdVars n R)).obj d ⟶
        ((kernelQuotientModule 𝒜 π (ProjectiveSpace.stdVars n R) p).cechHgr 0).obj d =>
    ψ.hom v) hnat
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  rw [← hcomm, hv, hw]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **The kernel-route comparison is degreewise surjective** in a twist where the graded Čech
`H¹` of `Γ_*(K)` vanishes.  Combined with `injective_kernelQuotientToGammaStar`, the model
`Γ_*(E) ⧸ Γ_*(K)` computes `Γ(Q(d))` exactly in such twists. -/
theorem surjective_app_kernelQuotientToGammaStar_of_subsingleton
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : F ⟶ F') [Epi p] (d : ℤ)
    [∀ e : ℤ, (twistModule 𝒜 F e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 F' e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 (kernel p) e).IsQuasicoherent]
    (hvan : Subsingleton
      (((gammaStar 𝒜 π (kernel p) (ProjectiveSpace.stdVars n R)).cechHgr 1).obj d)) :
    Function.Surjective
      (((kernelQuotientToGammaStar 𝒜 π (ProjectiveSpace.stdVars n R) p).app d).hom) := by
  have haugN := surjective_cechAug_kernelQuotientModule_of_subsingleton π p d hvan
  have haugF' : Function.Bijective
      (((gammaStar 𝒜 π F' (ProjectiveSpace.stdVars n R)).cechAug d).hom) :=
    ProjectiveSpace.bijective_gammaStar_cechAug_std π F' d
  haveI := isIso_cechHgrMap_kernelQuotientToGammaStar π p d
  have hiso : Function.Surjective
      ((GradedModule.cechHgrMap
        (kernelQuotientToGammaStar 𝒜 π (ProjectiveSpace.stdVars n R) p) 0).app d).hom := by
    intro y
    exact ⟨(inv ((GradedModule.cechHgrMap
        (kernelQuotientToGammaStar 𝒜 π (ProjectiveSpace.stdVars n R) p) 0).app d)).hom y,
      congrArg (fun ψ : ((gammaStar 𝒜 π F' (ProjectiveSpace.stdVars n R)).cechHgr 0).obj d ⟶
          ((gammaStar 𝒜 π F' (ProjectiveSpace.stdVars n R)).cechHgr 0).obj d => ψ.hom y)
        (IsIso.inv_hom_id ((GradedModule.cechHgrMap
          (kernelQuotientToGammaStar 𝒜 π (ProjectiveSpace.stdVars n R) p) 0).app d))⟩
  have hnat := GradedModule.cechAug_naturality
    (kernelQuotientToGammaStar 𝒜 π (ProjectiveSpace.stdVars n R) p) d
  intro y
  obtain ⟨w, hw⟩ := hiso (((gammaStar 𝒜 π F' (ProjectiveSpace.stdVars n R)).cechAug d).hom y)
  obtain ⟨v, hv⟩ := haugN w
  refine ⟨v, haugF'.1 ?_⟩
  have hcomm := congrArg (fun ψ :
      (kernelQuotientModule 𝒜 π (ProjectiveSpace.stdVars n R) p).obj d ⟶
        ((gammaStar 𝒜 π F' (ProjectiveSpace.stdVars n R)).cechHgr 0).obj d =>
    ψ.hom v) hnat
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  rw [← hcomm, hv]
  exact hw

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Surjectivity of twisted global sections of a presentation.**  If the graded Čech `H¹`
of `Γ_*(ker p)` vanishes in the twist `d`, then `Γ(E(d)) ⟶ Γ(Q(d))` is surjective. -/
theorem surjective_app_gammaStarMap_of_subsingleton
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : F ⟶ F') [Epi p] (d : ℤ)
    [∀ e : ℤ, (twistModule 𝒜 F e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 F' e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 (kernel p) e).IsQuasicoherent]
    (hvan : Subsingleton
      (((gammaStar 𝒜 π (kernel p) (ProjectiveSpace.stdVars n R)).cechHgr 1).obj d)) :
    Function.Surjective
      ((gammaStarMap 𝒜 π p (ProjectiveSpace.stdVars n R)).app d).hom := by
  have hfac : gammaStarMap 𝒜 π p (ProjectiveSpace.stdVars n R) =
      GradedModule.toCoker
          (gammaStarMap 𝒜 π (kernel.ι p) (ProjectiveSpace.stdVars n R)) ≫
        kernelQuotientToGammaStar 𝒜 π (ProjectiveSpace.stdVars n R) p := rfl
  rw [hfac]
  exact (surjective_app_kernelQuotientToGammaStar_of_subsingleton π p d hvan).comp
    ((shortExact_gammaStar_toCoker_kernel π p).surjective d)

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search
-- slow; see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
/-- **The single-variable localizations of `Γ_*(ker p)` are degreewise flat** when both the
ambient sheaf and the quotient are flat over the base.  Localize the kernel-route short exact
sequence once and apply `Module.Flat.of_shortExact` at each degree: the chart sections of the
ambient sheaf are flat, and so are those of the kernel-route model
(`isFlat_loc_kernelQuotientModule`). -/
theorem isFlat_loc_gammaStar_kernel
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : F ⟶ F') [Epi p] (i : Fin (n + 1))
    [∀ e : ℤ, (twistModule 𝒜 F e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 F' e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 (kernel p) e).IsQuasicoherent]
    (hflatF : F.FlatOver (projSpecπ n R))
    (hflatF' : F'.FlatOver (projSpecπ n R)) :
    GradedModule.IsFlat
      ((gammaStar 𝒜 (projSpecπ n R) (kernel p) (ProjectiveSpace.stdVars n R)).loc [i]) :=
  GradedModule.IsFlat.of_shortExact
    (GradedModule.loc_shortExact _ (l := [i])
      (shortExact_gammaStar_toCoker_kernel (projSpecπ n R) p))
    (isFlat_loc_gammaStar_of_flatOver F i hflatF)
    (isFlat_loc_kernelQuotientModule p i hflatF')

/-- **The Čech cochain groups of `Γ_*(ker p)` are flat over the base** when both the ambient
sheaf and the quotient are flat over the base. -/
theorem flat_cechCochain_gammaStar_kernel
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : F ⟶ F') [Epi p]
    [∀ e : ℤ, (twistModule 𝒜 F e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 F' e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 (kernel p) e).IsQuasicoherent]
    (hflatF : F.FlatOver (projSpecπ n R))
    (hflatF' : F'.FlatOver (projSpecπ n R)) (q : ℕ) (d : ℤ) :
    Module.Flat R
      ((gammaStar 𝒜 (projSpecπ n R) (kernel p)
        (ProjectiveSpace.stdVars n R)).cechCochain q d) :=
  GradedModule.flat_cechCochain_of_flat_loc _
    (fun a => isFlat_loc_gammaStar_kernel p a hflatF hflatF') q d

end AlgebraicGeometry.Proj

end
