module

public import StacksAndModuli.API.ProjGammaStarKernelVanishing
public import StacksAndModuli.API.ProjectiveSpaceTwistProjComparison

/-!
# Surjectivity of twisted global sections at the scheme level

The uniform surjectivity theorem `exists_bound_surjective_gammaStarMap` lives on polynomial
`Proj`; the Grassmannian map of §2.4 consumes it on relative projective space over
`Spec R`.  This file provides the conjugation: the global-sections comparison
`projectiveSpaceTwistedGlobalSectionsEquiv` intertwines the scheme-level twisted map
`ψ ⊗ 𝒪(d)` with the `Proj`-level `gammaStarMap` of the pullback of `ψ`, so surjectivity
transfers.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.projectiveSpaceOverTwistModulePullbackIso_naturality`;
* `AlgebraicGeometry.ProjectiveSpace.surjective_app_top_twist_of_gammaStarMap`;
* `AlgebraicGeometry.ProjectiveSpace.exists_bound_surjective_twistedGlobalSections` — the
  scheme-level uniform surjectivity over an affine noetherian base.
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

variable {n : ℕ} {R : Type u} [CommRing R]

/-- API lemma for the Quot-to-Grassmannian construction in Proposition 2.4.1: the twist-pullback
comparison is natural in the sheaf. -/
theorem projectiveSpaceOverTwistModulePullbackIso_naturality
    {F' Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules}
    (ψ : F' ⟶ Q) (d : ℤ) :
    (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map
        (Scheme.Modules.tensorMapLeft ψ
          (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) d)) ≫
      (projectiveSpaceOverTwistModulePullbackIso Q d).hom
    = (projectiveSpaceOverTwistModulePullbackIso F' d).hom ≫
      twistModuleMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map ψ) d := by
  dsimp only [projectiveSpaceOverTwistModulePullbackIso, Iso.trans_hom]
  rw [← Category.assoc,
    Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion_naturality_left]
  simp only [Category.assoc]
  congr 1
  dsimp only [Scheme.Modules.tensorRightIso]
  exact (Scheme.Modules.tensorMap_exchange _ _).symm

/-- Reduction lemma for the Quot-to-Grassmannian construction in Proposition 2.4.1: surjectivity of
twisted global sections descends from `Proj`. If the `Γ_*`-level map of the pulled-back
presentation is surjective in degree `d`, the scheme-level twisted map is surjective on
global sections. -/
theorem surjective_app_top_twist_of_gammaStarMap
    {F' Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules}
    (ψ : F' ⟶ Q) (d : ℤ)
    (h : Function.Surjective ((Proj.gammaStarMap
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (projSpecπ n R)
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map ψ)
      (stdVars n R)).app d).hom) :
    Function.Surjective (Scheme.Modules.Hom.app
      (Scheme.Modules.tensorMapLeft ψ
        (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) d)) ⊤) := by
  intro y
  set eF := Scheme.Modules.pullbackGlobalSectionsViaIsoAddEquiv
    (projectiveSpaceOverSpecIso n R).inv
    (Scheme.projectiveSpaceOverTwistModule F' d)
    (projectiveSpaceOverTwistModulePullbackIso F' d) with heF
  set eQ := Scheme.Modules.pullbackGlobalSectionsViaIsoAddEquiv
    (projectiveSpaceOverSpecIso n R).inv
    (Scheme.projectiveSpaceOverTwistModule Q d)
    (projectiveSpaceOverTwistModulePullbackIso Q d) with heQ
  obtain ⟨x', hx'⟩ := h (eQ y)
  refine ⟨eF.symm x', ?_⟩
  refine eQ.injective ?_
  -- the equivalence is the pullback of global sections followed by the twist-pullback
  -- comparison
  have hfun : ∀ (M : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
      (e : (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
          (Scheme.projectiveSpaceOverTwistModule M d) ≅
        twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj M) d)
      (z : Γ(Scheme.projectiveSpaceOverTwistModule M d, ⊤)),
      (Scheme.Modules.pullbackGlobalSectionsViaIsoAddEquiv
          (projectiveSpaceOverSpecIso n R).inv
          (Scheme.projectiveSpaceOverTwistModule M d) e) z
        = Scheme.Modules.Hom.app e.hom ⊤
          (Scheme.Modules.pullbackGlobalSections (projectiveSpaceOverSpecIso n R).inv
            (Scheme.projectiveSpaceOverTwistModule M d) z) := fun M e z => rfl
  rw [hfun Q]
  have hnat1 : (Scheme.Modules.pullbackGlobalSections (projectiveSpaceOverSpecIso n R).inv
        (Scheme.projectiveSpaceOverTwistModule Q d))
        ((ConcreteCategory.hom (Scheme.Modules.Hom.app
          (Scheme.Modules.tensorMapLeft ψ
            (Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) d)) ⊤))
          (eF.symm x'))
      = (ConcreteCategory.hom (Scheme.Modules.Hom.app
          ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map
            (Scheme.Modules.tensorMapLeft ψ
              (Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) d))) ⊤))
          ((Scheme.Modules.pullbackGlobalSections (projectiveSpaceOverSpecIso n R).inv
            (Scheme.projectiveSpaceOverTwistModule F' d)) (eF.symm x')) :=
    (Scheme.Modules.pullbackGlobalSections_naturality
      ((projectiveSpaceOverSpecIso n R).inv)
      (Scheme.Modules.tensorMapLeft ψ
        (Scheme.projectiveSpaceOverTwist n (Spec (.of R)) d)) (eF.symm x')).symm
  refine (congrArg (fun z => (ConcreteCategory.hom (Scheme.Modules.Hom.app
      (projectiveSpaceOverTwistModulePullbackIso Q d).hom ⊤)) z) hnat1).trans ?_
  have hnat2 : (ConcreteCategory.hom (Scheme.Modules.Hom.app
      (projectiveSpaceOverTwistModulePullbackIso Q d).hom ⊤))
      ((ConcreteCategory.hom (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map
          (Scheme.Modules.tensorMapLeft ψ
            (Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) d))) ⊤))
        ((Scheme.Modules.pullbackGlobalSections (projectiveSpaceOverSpecIso n R).inv
          (Scheme.projectiveSpaceOverTwistModule F' d)) (eF.symm x')))
      = (ConcreteCategory.hom (Scheme.Modules.Hom.app
        (twistModuleMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map ψ) d) ⊤))
        ((ConcreteCategory.hom (Scheme.Modules.Hom.app
          (projectiveSpaceOverTwistModulePullbackIso F' d).hom ⊤))
          ((Scheme.Modules.pullbackGlobalSections (projectiveSpaceOverSpecIso n R).inv
            (Scheme.projectiveSpaceOverTwistModule F' d)) (eF.symm x'))) :=
    congrArg (fun χ => (PresheafOfModules.Hom.app χ.val (op ⊤)).hom
        ((Scheme.Modules.pullbackGlobalSections (projectiveSpaceOverSpecIso n R).inv
          (Scheme.projectiveSpaceOverTwistModule F' d)) (eF.symm x')))
      (projectiveSpaceOverTwistModulePullbackIso_naturality ψ d)
  refine hnat2.trans ?_
  have hx'' : Scheme.Modules.Hom.app
      (projectiveSpaceOverTwistModulePullbackIso F' d).hom ⊤
      (Scheme.Modules.pullbackGlobalSections (projectiveSpaceOverSpecIso n R).inv
        (Scheme.projectiveSpaceOverTwistModule F' d) (eF.symm x'))
      = x' := by
    have h1 := hfun F' (projectiveSpaceOverTwistModulePullbackIso F' d) (eF.symm x')
    rw [← h1, heF]
    exact eF.apply_symm_apply x'
  have hfinal : (ConcreteCategory.hom (Scheme.Modules.Hom.app
      (twistModuleMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map ψ) d) ⊤))
      (Scheme.Modules.Hom.app
        (projectiveSpaceOverTwistModulePullbackIso F' d).hom ⊤
        (Scheme.Modules.pullbackGlobalSections (projectiveSpaceOverSpecIso n R).inv
          (Scheme.projectiveSpaceOverTwistModule F' d) (eF.symm x')))
      = (ConcreteCategory.hom (Scheme.Modules.Hom.app
        (twistModuleMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map ψ) d) ⊤))
        x' := by rw [hx'']
  refine hfinal.trans ?_
  exact hx'

set_option synthInstance.maxHeartbeats 1000000 in
-- Same instance-search burden as the `Proj`-side uniform surjectivity.
/-- Supporting API for the Quot-to-Grassmannian construction in Proposition 2.4.1: uniform
surjectivity of twisted global sections at the scheme level. For the twisted-free
presentation of a flat family with fibrewise Hilbert polynomial `P` over an affine
noetherian base, `Γ(F(d)) ⟶ Γ(Q(d))` is surjective for every `d ≥ d₁(n, l, r, P)`. -/
theorem exists_bound_surjective_twistedGlobalSections (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₁ : ℤ, 0 ≤ d₁ ∧ ∀ (R' : Type u) [CommRing R'] [IsNoetherianRing R']
      (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R'))).Modules)
      (_ : Q.IsFinitePresentation)
      (_ : (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n (Spec (.of R')) (-l)).IsFinitePresentation)
      (ψ : (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n (Spec (.of R')) (-l)) ⟶ Q)
      (_ : Epi ψ)
      (_ : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R'))))
      (_ : Scheme.HasFiberwiseHilbertPolynomial Q P)
      (d : ℤ), d₁ ≤ d →
      Function.Surjective (Scheme.Modules.Hom.app
        (Scheme.Modules.tensorMapLeft ψ
          (Scheme.projectiveSpaceOverTwist n (Spec (.of R')) d)) ⊤) := by
  obtain ⟨d₁, hd₁0, hd₁⟩ := exists_bound_surjective_gammaStarMap.{u} n r l P
  refine ⟨d₁, hd₁0, ?_⟩
  intro R' _ _ Q hQfp hAmbfp ψ hψ hflat hHP d hd
  haveI := hQfp
  haveI := hAmbfp
  haveI := hψ
  refine surjective_app_top_twist_of_gammaStarMap ψ d ?_
  exact hd₁ R' Q hQfp hAmbfp
    ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R').inv).map ψ)
    inferInstance hflat hHP d hd

end AlgebraicGeometry.ProjectiveSpace

end
