module

public import StacksAndModuli.API.ProjectiveKernelQuotientCanonicalBaseChange
public import StacksAndModuli.API.ProjectiveTwistedVanishingModel
public import StacksAndModuli.API.TwistedFreeMonomialSpan

/-!
# Eventual canonical global-sections base change on polynomial projective space

The graded Čech calculation gives the canonical comparison on the intrinsic polynomial
base-change model.  The finite vanishing-model API instead uses the raw categorical
pullback of the structure morphism.  These two cartesian models are canonically isomorphic.
This file proves that their literal global-sections comparison maps are conjugate through
that isomorphism and packages the resulting arbitrary-ring comparison together with
eventual finite projectivity.

Main declarations:

* `AlgebraicGeometry.Proj.rawBaseChange_bijective_of_gammaStarBaseChangeApp`;
* `AlgebraicGeometry.Proj.`
  `hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_of_isFG_of_flatOver`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits TensorProduct Opposite
open AlgebraicGeometry ProjectiveSpectrum.Twist

universe u

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {R A : Type u} [CommRing R] [CommRing A]

local notation "𝒜ᴿ" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜ᴬ" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

/-- Evaluation of the global-sections linear equivalence induced by pullback along a
scheme isomorphism and a sheaf isomorphism. -/
lemma pullbackGlobalSectionsViaIsoLinearEquiv'_apply
    {X Y : Scheme.{u}} {B : CommRingCat.{u}}
    (j : X ⟶ Y) [IsIso j] (pY : Y ⟶ Spec B) (pX : X ⟶ Spec B)
    (hp : j ≫ pY = pX) (M : Y.Modules) {N : X.Modules}
    (e : (Scheme.Modules.pullback j).obj M ≅ N) (m : Γ(M, ⊤)) :
    letI := Scheme.Modules.globalSectionsModule pY M
    letI := Scheme.Modules.globalSectionsModule pX N
    Scheme.Modules.pullbackGlobalSectionsViaIsoLinearEquiv'
        j pY pX hp M e m =
      e.hom.app ⊤ (Scheme.Modules.pullbackGlobalSections j M m) := by
  subst hp
  rfl

/-- Bijectivity of the canonical polynomial-projective comparison implies bijectivity of
the canonical comparison on the raw categorical pullback used by the finite vanishing-model
interface. -/
theorem rawBaseChange_bijective_of_gammaStarBaseChangeApp
    (F : (Proj 𝒜ᴿ).Modules) (d : ℕ) (f : R →+* A)
    (hbij : Function.Bijective
      (ProjectiveSpace.gammaStarBaseChangeApp n f F (d : ℤ))) :
    let φ := CommRingCat.ofHom f
    let pR := Proj.polynomialToSpec (Fin (n + 1)) R
    let Y := Limits.pullback (Spec.map φ) pR
    let g : Y ⟶ Proj 𝒜ᴿ := Limits.pullback.snd (Spec.map φ) pR
    let pY : Y ⟶ Spec (.of A) := Limits.pullback.fst (Spec.map φ) pR
    letI : Algebra R A := f.toAlgebra
    Function.Bijective
      (Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
        φ g pR pY Limits.pullback.condition.symm
        (twistModule 𝒜ᴿ F (d : ℤ))) := by
  let φ := CommRingCat.ofHom f
  let pR := Proj.polynomialToSpec (Fin (n + 1)) R
  let pA := Proj.polynomialToSpec (Fin (n + 1)) A
  let Y := Limits.pullback (Spec.map φ) pR
  let g : Y ⟶ Proj 𝒜ᴿ := Limits.pullback.snd (Spec.map φ) pR
  let pY : Y ⟶ Spec (.of A) := Limits.pullback.fst (Spec.map φ) pR
  let gP := Proj.polynomialMap (Fin (n + 1)) f
  let M := twistModule 𝒜ᴿ F (d : ℤ)
  let Nraw := (Scheme.Modules.pullback g).obj M
  let NT := twistModule 𝒜ᴬ ((Scheme.Modules.pullback gP).obj F) (d : ℤ)
  letI : Algebra R A := f.toAlgebra
  let e : Proj 𝒜ᴬ ≅ Y :=
    (Proj.polynomialBaseChangeIso (Fin (n + 1)) R f).symm ≪≫
      Limits.pullbackSymmetry pR (Spec.map φ)
  have heg : e.hom ≫ g = gP := by
    dsimp only [e, g, gP, φ]
    simp
    exact (Iso.inv_comp_eq
      (Proj.polynomialBaseChangeIso (Fin (n + 1)) R f)).2
      (Proj.polynomialBaseChangeIso_hom_polynomialMap
        (Fin (n + 1)) R f).symm
  have hep : e.hom ≫ pY = pA := by
    dsimp only [e, pY, pA, φ]
    simp
    exact (Iso.inv_comp_eq
      (Proj.polynomialBaseChangeIso (Fin (n + 1)) R f)).2
      (Proj.polynomialBaseChangeIso_hom_toSpec
        (Fin (n + 1)) R f).symm
  let ePre : (Scheme.Modules.pullback e.hom).obj Nraw ≅
      (Scheme.Modules.pullback gP).obj M :=
    (Scheme.Modules.pullbackComp e.hom g).app M ≪≫
      (Scheme.Modules.pullbackCongr heg).app M
  let α := twistModulePolynomialPullbackHom (Fin (n + 1)) f F (d : ℤ)
  let eSheaf : (Scheme.Modules.pullback e.hom).obj Nraw ≅ NT :=
    ePre ≪≫ asIso α
  letI : Module R Γ(M, ⊤) := Scheme.Modules.globalSectionsModule pR M
  letI : Module A Γ(Nraw, ⊤) := Scheme.Modules.globalSectionsModule pY Nraw
  letI : Module A Γ(NT, ⊤) := Scheme.Modules.globalSectionsModule pA NT
  let cRaw := Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
    φ g pR pY Limits.pullback.condition.symm M
  let eΓ := Scheme.Modules.pullbackGlobalSectionsViaIsoLinearEquiv'
    e.hom pY pA hep Nraw eSheaf
  have hEq : eΓ.toLinearMap.comp cRaw =
      ProjectiveSpace.gammaStarBaseChangeApp n f F (d : ℤ) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
        rw [LinearMap.comp_apply]
        rw [Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_tmul]
        rw [ProjectiveSpace.gammaStarBaseChangeApp_tmul]
        rw [map_smul]
        congr 1
        dsimp only [eΓ]
        have hΓ := pullbackGlobalSectionsViaIsoLinearEquiv'_apply
          e.hom pY pA hep Nraw eSheaf
          (Scheme.Modules.pullbackGlobalSections g M m)
        refine hΓ.trans ?_
        change Scheme.Modules.Hom.app eSheaf.hom ⊤
            (Scheme.Modules.pullbackGlobalSections e.hom Nraw
              (Scheme.Modules.pullbackGlobalSections g M m)) =
          α.app ⊤ (Scheme.Modules.pullbackGlobalSections gP M m)
        change α.app ⊤ (Scheme.Modules.Hom.app ePre.hom ⊤
            (Scheme.Modules.pullbackGlobalSections e.hom Nraw
              (Scheme.Modules.pullbackGlobalSections g M m))) = _
        exact congrArg (α.app ⊤)
          (Scheme.Modules.pullbackGlobalSections_comp_congr
            e.hom g gP heg M m)
  have hcomp : Function.Bijective (eΓ.toLinearMap.comp cRaw) := by
    rw [hEq]
    exact hbij
  exact (eΓ.bijective.of_comp_iff' cRaw).mp (by
    change Function.Bijective (eΓ.toLinearMap.comp cRaw)
    exact hcomp)

set_option synthInstance.maxHeartbeats 800000 in
-- Finitely presented polynomial-`Proj` sheaves carry expensive quantified twist instances.
set_option maxHeartbeats 1000000 in
/-- A flat finitely presented sheaf on polynomial projective space with finitely generated
`Γ_*` has eventual finite-projective global sections whose literal canonical comparison is
bijective after every coefficient-ring change. -/
noncomputable def
    hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_of_isFG_of_flatOver
    [IsNoetherianRing R]
    (F : (Proj 𝒜ᴿ).Modules) [F.IsFinitePresentation]
    (hFG : ProjectiveSpace.GradedModule.IsFG
      (Proj.gammaStar 𝒜ᴿ (Proj.polynomialToSpec (Fin (n + 1)) R)
        F (ProjectiveSpace.stdVars n R)))
    (hflat : F.FlatOver (Proj.polynomialToSpec (Fin (n + 1)) R)) :
    HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange F := by
  classical
  letI hqc : ∀ e : ℤ, (twistModule 𝒜ᴿ F e).IsQuasicoherent :=
    fun e ↦ ProjectiveSpace.twistModule_std_isQuasicoherent F e
  let M := Proj.gammaStar 𝒜ᴿ
    (Proj.polynomialToSpec (Fin (n + 1)) R) F
    (ProjectiveSpace.stdVars n R)
  change ProjectiveSpace.GradedModule.IsFG M at hFG
  have hflatC : ∀ (e : ℤ) (p : ℕ), Module.Flat R ((M.cechComplex e).X p) := by
    intro e p
    exact ProjectiveSpace.GradedModule.flat_cechCochain_of_flat_loc M
      (fun a ↦ Proj.isFlat_loc_gammaStar_of_flatOver F a hflat) p e
  let dV := Classical.choose
    (ProjectiveSpace.GradedModule.exists_uniform_subsingleton_cechHgr_baseChange'
      hFG hflatC)
  have hdVanish := Classical.choose_spec
    (ProjectiveSpace.GradedModule.exists_uniform_subsingleton_cechHgr_baseChange'
      hFG hflatC)
  let dC := Classical.choose
    (ProjectiveSpace.exists_bound_bijective_gammaStarBaseChangeApp_of_isFG_of_flatOver
      F hFG hflat)
  have hdCanonical := Classical.choose_spec
    (ProjectiveSpace.exists_bound_bijective_gammaStarBaseChangeApp_of_isFG_of_flatOver
      F hFG hflat)
  refine
    { bound := max dV.toNat dC
      fixedDegree := ?_ }
  intro d hd
  have hdV : dV ≤ (d : ℤ) := by
    apply le_trans (Int.self_le_toNat dV)
    exact_mod_cast le_trans (le_max_left dV.toNat dC) hd
  have hdC : dC ≤ d := le_trans (le_max_right dV.toNat dC) hd
  letI : Module R Γ(twistModule 𝒜ᴿ F (d : ℤ), ⊤) :=
    Scheme.Modules.globalSectionsModule
      (Proj.polynomialToSpec (Fin (n + 1)) R)
      (twistModule 𝒜ᴿ F (d : ℤ))
  refine
    { finite := ?_
      projective := ?_
      baseChange_bijective := ?_ }
  · haveI : Module.Finite R ((M.cechHgr 0).obj (d : ℤ)) :=
      ProjectiveSpace.GradedModule.finiteDimensional_cechHgr_of_isFG
        M hFG 0 (d : ℤ)
    exact Module.Finite.equiv
      (ProjectiveSpace.cechHgrZeroEquivOfIsFinitePresentation
        (Proj.polynomialToSpec (Fin (n + 1)) R) F (d : ℤ))
  · haveI : Module.Projective R ((M.cechHgr 0).obj (d : ℤ)) :=
      ProjectiveSpace.GradedModule.projective_cechHgr_zero' hFG
        (hflatC (d : ℤ))
        (fun κ _ _ i hi ↦ hdVanish κ i hi (d : ℤ) hdV)
    exact Module.Projective.of_equiv
      (ProjectiveSpace.cechHgrZeroEquivOfIsFinitePresentation
        (Proj.polynomialToSpec (Fin (n + 1)) R) F (d : ℤ))
  · intro A _ f
    exact rawBaseChange_bijective_of_gammaStarBaseChangeApp F d f
      (hdCanonical A f d hdC)

set_option synthInstance.maxHeartbeats 800000 in
-- Polynomial `Proj` quotient comparisons carry three quantified twist instances.
set_option maxHeartbeats 1000000 in
/-- A flat finitely presented quotient on polynomial projective space has eventual
finite-projective global sections with literal canonical arbitrary-ring base change,
provided its kernel-quotient model and the graded sections of its kernel are finitely
generated. -/
noncomputable def
    hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_of_kernelQuotient
    [IsNoetherianRing R]
    (E F : (Proj 𝒜ᴿ).Modules) [F.IsFinitePresentation]
    (p : E ⟶ F) [Epi p]
    [∀ e : ℤ, (twistModule 𝒜ᴿ E e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜ᴿ F e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜ᴿ (kernel p) e).IsQuasicoherent]
    (hM : ProjectiveSpace.GradedModule.IsFG
      (kernelQuotientModule 𝒜ᴿ (polynomialToSpec (Fin (n + 1)) R)
        (ProjectiveSpace.stdVars n R) p))
    (hK : ProjectiveSpace.GradedModule.IsFG
      (gammaStar 𝒜ᴿ (polynomialToSpec (Fin (n + 1)) R)
        (kernel p) (ProjectiveSpace.stdVars n R)))
    (hflat : F.FlatOver (polynomialToSpec (Fin (n + 1)) R)) :
    HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange F := by
  classical
  let M := kernelQuotientModule 𝒜ᴿ
    (polynomialToSpec (Fin (n + 1)) R) (ProjectiveSpace.stdVars n R) p
  change ProjectiveSpace.GradedModule.IsFG M at hM
  have hflatC : ∀ (e : ℤ) (q : ℕ), Module.Flat R ((M.cechComplex e).X q) := by
    intro e q
    exact ProjectiveSpace.GradedModule.flat_cechCochain_of_flat_loc M
      (fun a ↦ isFlat_loc_kernelQuotientModule p a hflat) q e
  let dV := Classical.choose
    (ProjectiveSpace.GradedModule.exists_uniform_subsingleton_cechHgr_baseChange'
      hM hflatC)
  have hdVanish := Classical.choose_spec
    (ProjectiveSpace.GradedModule.exists_uniform_subsingleton_cechHgr_baseChange'
      hM hflatC)
  let dC := Classical.choose
    (ProjectiveSpace.exists_bound_bijective_gammaStarBaseChangeApp_of_kernelQuotient
      E F p hM hK hflat)
  have hdCanonical := Classical.choose_spec
    (ProjectiveSpace.exists_bound_bijective_gammaStarBaseChangeApp_of_kernelQuotient
      E F p hM hK hflat)
  refine
    { bound := max dV.toNat dC
      fixedDegree := ?_ }
  intro d hd
  have hdV : dV ≤ (d : ℤ) := by
    apply le_trans (Int.self_le_toNat dV)
    exact_mod_cast le_trans (le_max_left dV.toNat dC) hd
  have hdC : dC ≤ d := le_trans (le_max_right dV.toNat dC) hd
  letI : Module R Γ(twistModule 𝒜ᴿ F (d : ℤ), ⊤) :=
    Scheme.Modules.globalSectionsModule
      (polynomialToSpec (Fin (n + 1)) R)
      (twistModule 𝒜ᴿ F (d : ℤ))
  haveI : IsIso ((ProjectiveSpace.GradedModule.cechHgrMap
      (kernelQuotientToGammaStar 𝒜ᴿ
        (polynomialToSpec (Fin (n + 1)) R)
        (ProjectiveSpace.stdVars n R) p) 0).app (d : ℤ)) :=
    isIso_cechHgrMap_kernelQuotientToGammaStar
      (polynomialToSpec (Fin (n + 1)) R) p (d : ℤ)
  let eΓ : ((M.cechHgr 0).obj (d : ℤ)) ≃ₗ[R]
      Γ(twistModule 𝒜ᴿ F (d : ℤ), ⊤) :=
    (asIso ((ProjectiveSpace.GradedModule.cechHgrMap
      (kernelQuotientToGammaStar 𝒜ᴿ
        (polynomialToSpec (Fin (n + 1)) R)
        (ProjectiveSpace.stdVars n R) p) 0).app (d : ℤ))).toLinearEquiv.trans
      (ProjectiveSpace.cechHgrZeroEquivOfIsFinitePresentation
        (polynomialToSpec (Fin (n + 1)) R) F (d : ℤ))
  refine
    { finite := ?_
      projective := ?_
      baseChange_bijective := ?_ }
  · haveI : Module.Finite R ((M.cechHgr 0).obj (d : ℤ)) :=
      ProjectiveSpace.GradedModule.finiteDimensional_cechHgr_of_isFG
        M hM 0 (d : ℤ)
    exact Module.Finite.equiv eΓ
  · haveI : Module.Projective R ((M.cechHgr 0).obj (d : ℤ)) :=
      ProjectiveSpace.GradedModule.projective_cechHgr_zero' hM
        (hflatC (d : ℤ))
        (fun κ _ _ i hi ↦ hdVanish κ i hi (d : ℤ) hdV)
    exact Module.Projective.of_equiv eΓ
  · intro A _ f
    exact rawBaseChange_bijective_of_gammaStarBaseChangeApp F d f
      (hdCanonical A f d hdC)

end AlgebraicGeometry.Proj

end

end
