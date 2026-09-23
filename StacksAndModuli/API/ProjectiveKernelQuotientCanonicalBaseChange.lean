module

public import StacksAndModuli.API.ProjectiveGradedCanonicalBaseChange
public import StacksAndModuli.API.ProjGammaStarQuotientSurjectivity

/-!
# Canonical base change from the kernel-quotient model

For a quotient `E → Q` on polynomial projective space, the full graded module
`Gamma_*(Q)` need not be finitely generated because its negative tail may be infinite.
The finitely generated replacement used in the Quot construction is

`Gamma_*(E) / Gamma_*(ker(E → Q))`.

This file proves eventual bijectivity of the literal canonical global-sections
base-change map from finite generation of that kernel-quotient model and of
`Gamma_*(ker(E → Q))`.  The latter hypothesis supplies the eventual surjectivity of
the comparison with `Gamma_*(Q)`.

Main declaration:

* `AlgebraicGeometry.ProjectiveSpace.`
  `exists_bound_bijective_gammaStarBaseChangeApp_of_kernelQuotient`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open ProjectiveSpectrum.Twist

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

set_option synthInstance.maxHeartbeats 800000 in
-- Polynomial `Proj` quotient comparisons carry three quantified twist instances.
set_option maxHeartbeats 1000000 in
/-- A finitely generated kernel-quotient model gives the literal canonical
global-sections base-change isomorphism in every sufficiently large nonnegative twist.

Finite generation of `Gamma_*(ker p)` is used only to make the comparison from the
kernel-quotient model to `Gamma_*(Q)` degreewise surjective in large degree. -/
theorem exists_bound_bijective_gammaStarBaseChangeApp_of_kernelQuotient
    (E Q : (Proj 𝒜).Modules) [Q.IsFinitePresentation]
    (p : E ⟶ Q) [Epi p]
    [∀ e : ℤ, (twistModule 𝒜 E e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 Q e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 (kernel p) e).IsQuasicoherent]
    (hM : GradedModule.IsFG
      (Proj.kernelQuotientModule 𝒜 (projSpecπ n R) (stdVars n R) p))
    (hK : GradedModule.IsFG
      (Proj.gammaStar 𝒜 (projSpecπ n R) (kernel p) (stdVars n R)))
    (hflat : Q.FlatOver (projSpecπ n R)) :
    ∃ d₀ : ℕ, ∀ (A : Type u) [CommRing A] (f : R →+* A) (d : ℕ), d₀ ≤ d →
      Function.Bijective (gammaStarBaseChangeApp n f Q (d : ℤ)) := by
  let M := Proj.kernelQuotientModule 𝒜 (projSpecπ n R) (stdVars n R) p
  let K := Proj.gammaStar 𝒜 (projSpecπ n R) (kernel p) (stdVars n R)
  let ι := Proj.kernelQuotientToGammaStar 𝒜 (projSpecπ n R) (stdVars n R) p
  change GradedModule.IsFG M at hM
  change GradedModule.IsFG K at hK
  have hflatC : ∀ (e : ℤ) (q : ℕ), Module.Flat R ((M.cechComplex e).X q) := by
    intro e q
    exact GradedModule.flat_cechCochain_of_flat_loc M
      (fun a ↦ Proj.isFlat_loc_kernelQuotientModule p a hflat) q e
  obtain ⟨dM, hdM⟩ :=
    GradedModule.exists_uniform_subsingleton_cechHgr_baseChange' hM hflatC
  obtain ⟨dK, hdK⟩ := GradedModule.exists_uniform_subsingleton_cechHgr K hK
  refine ⟨max dM.toNat dK.toNat, ?_⟩
  intro A _ f d hd
  letI : Algebra R A := f.toAlgebra
  have hdM' : dM ≤ (d : ℤ) := le_trans (Int.self_le_toNat dM)
    (by exact_mod_cast le_trans (le_max_left dM.toNat dK.toNat) hd)
  have hdK' : dK ≤ (d : ℤ) := le_trans (Int.self_le_toNat dK)
    (by exact_mod_cast le_trans (le_max_right dM.toNat dK.toNat) hd)
  have hι : Function.Bijective ((ι.app (d : ℤ)).hom) := by
    constructor
    · exact Proj.injective_kernelQuotientToGammaStar
        (Fin (n + 1)) (projSpecπ n R) (stdVars n R) p (d : ℤ)
    · exact Proj.surjective_app_kernelQuotientToGammaStar_of_subsingleton
        (projSpecπ n R) p (d : ℤ) (hdK 1 (by omega) (d : ℤ) hdK')
  haveI : IsIso ((GradedModule.cechHgrMap ι 0).app (d : ℤ)) :=
    Proj.isIso_cechHgrMap_kernelQuotientToGammaStar
      (projSpecπ n R) p (d : ℤ)
  let N := Proj.gammaStar 𝒜 (projSpecπ n R) Q (stdVars n R)
  have hNcyc : Function.Bijective
      (GradedModule.cechAugCocycles N (d : ℤ)) := by
    constructor
    · intro x y hxy
      apply Proj.injective_gammaStar_cechAug₀ 𝒜 (projSpecπ n R) Q
        (stdVars n R) (top_le_iSup_basicOpen_stdVars n R) (d : ℤ)
      exact congrArg Subtype.val hxy
    · intro z
      obtain ⟨x, hx⟩ := Proj.exists_gammaStar_cechAug₀_eq 𝒜
        (projSpecπ n R) Q (stdVars n R)
        (top_le_iSup_basicOpen_stdVars n R) (d : ℤ) z.1 (by
          change (N.cechD 0 (d : ℤ)).hom z.1 = 0
          exact z.2)
      exact ⟨x, Subtype.ext hx⟩
  have hMcyc : Function.Bijective
      (GradedModule.cechAugCocycles M (d : ℤ)) :=
    GradedModule.bijective_cechAugCocycles_of_morphism M ι (d : ℤ) hι hNcyc
  have hex : ∀ i : ℕ, CochainComplex.ExactAtSucc (M.cechComplex (d : ℤ)) i :=
    GradedModule.exactAtSucc_cechComplex_of_fibrewise' M (d : ℤ) hM
      (hflatC (d : ℤ))
      (fun κ _ _ i hi ↦ hdM κ i hi (d : ℤ) hdM')
  have haugM : Function.Bijective (((M.baseChange A).cechAug (d : ℤ)).hom) :=
    GradedModule.bijective_cechAug_baseChange M (d : ℤ)
      (hflatC (d : ℤ)) (N := n)
      (fun q hq ↦ GradedModule.subsingleton_cechComplex_X M (d : ℤ) hq)
      hex hMcyc
  let ιA := GradedModule.baseChangeMap ι A
  have hιA : Function.Bijective ((ιA.app (d : ℤ)).hom) := by
    let e := LinearEquiv.ofBijective ((ι.app (d : ℤ)).hom) hι
    change Function.Bijective (LinearMap.baseChange A ((ι.app (d : ℤ)).hom))
    exact (e.baseChange R A).bijective
  haveI : IsIso ((GradedModule.cechHgrMap ιA 0).app (d : ℤ)) :=
    isIso_cechHgrMap_baseChangeMap_kernelQuotientToGammaStar
      n R p A (d : ℤ)
  have hHιA : Function.Bijective
      (((GradedModule.cechHgrMap ιA 0).app (d : ℤ)).hom) :=
    ConcreteCategory.bijective_of_isIso _
  have hnatιA := GradedModule.cechAug_naturality ιA (d : ℤ)
  have haugN : Function.Bijective (((N.baseChange A).cechAug (d : ℤ)).hom) := by
    have hcomp : Function.Bijective
        (((N.baseChange A).cechAug (d : ℤ)).hom.comp
          ((ιA.app (d : ℤ)).hom)) := by
      have hEq := congrArg ModuleCat.Hom.hom hnatιA
      simp only [ModuleCat.hom_comp] at hEq
      rw [← hEq]
      exact hHιA.comp haugM
    exact (Function.Bijective.of_comp_iff
      ((N.baseChange A).cechAug (d : ℤ)).hom hιA).mp (by
        simpa only [LinearMap.coe_comp] using hcomp)
  let N' := Proj.gammaStar
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
    (projSpecπ n A) ((Scheme.Modules.pullback (coeffMap n f)).obj Q) (stdVars n A)
  have haugN' : Function.Bijective ((N'.cechAug (d : ℤ)).hom) :=
    bijective_gammaStar_cechAug_of_isFinitePresentation
      (projSpecπ n A) ((Scheme.Modules.pullback (coeffMap n f)).obj Q) (d : ℤ)
  let ψ := gammaStarBaseChangeHom n f Q
  haveI : IsIso ((GradedModule.cechHgrMap ψ 0).app (d : ℤ)) :=
    isIso_cechHgrMap_gammaStarBaseChangeHom_app n f Q d
  have hHψ : Function.Bijective
      (((GradedModule.cechHgrMap ψ 0).app (d : ℤ)).hom) :=
    ConcreteCategory.bijective_of_isIso _
  have hnatψ := GradedModule.cechAug_naturality ψ (d : ℤ)
  have hcompψ : Function.Bijective
      ((N'.cechAug (d : ℤ)).hom.comp ((ψ.app (d : ℤ)).hom)) := by
    have hEq := congrArg ModuleCat.Hom.hom hnatψ
    simp only [ModuleCat.hom_comp] at hEq
    rw [← hEq]
    exact hHψ.comp haugN
  have hψ : Function.Bijective ((ψ.app (d : ℤ)).hom) := by
    apply (haugN'.of_comp_iff' ((ψ.app (d : ℤ)).hom)).mp
    simpa only [LinearMap.coe_comp] using hcompψ
  change Function.Bijective ((gammaStarBaseChangeHomApp n f Q (d : ℤ)).hom)
  simpa only [ψ, gammaStarBaseChangeHom] using hψ

end AlgebraicGeometry.ProjectiveSpace

end

end
