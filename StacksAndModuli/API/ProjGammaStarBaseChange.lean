module

public import StacksAndModuli.API.ProjGammaStar
public import StacksAndModuli.API.ProjGammaStarProjectiveSpace
public import StacksAndModuli.API.ProjectiveTwistModuleBaseChange
public import StacksAndModuli.API.CanonicalAffineGlobalSectionsBaseChange
public import StacksAndModuli.API.FlatGlobalSectionsBaseChange
public import StacksAndModuli.API.ProjectiveGradedFamilies

/-!
# The comparison `Γ_*(F) ⊗ S ⟶ Γ_*(F_S)` for a change of coefficients

For a map of coefficient rings `φ : R → S` and a sheaf `F` on `Proj R[x₀, …, xₙ]`,
extension of scalars on global sections followed by the twist comparison gives a morphism
of graded modules over `S`

`(Γ_*(F)).baseChange S ⟶ Γ_*(g^* F)`,

where `g = Proj.polynomialMap` is the coefficient change.  Its degree-raising compatibility
is `ProjectiveSpectrum.Twist.pullback_map_twistModuleMulHom_comp_twistModulePolynomialPullbackHom`
together with naturality of the pullback adjunction unit on global sections.

This is the comparison whose bijectivity on the localizations at the coordinates is
`AlgebraicGeometry.ProjectiveSpace.HasGammaStarBaseChangeCechHgrZero`; on a chart it is
ordinary affine base change, for which
`Scheme.Modules.pullbackOpenSectionsBaseChangeLinearMap_bijective_of_isPullback` is available
with no flatness hypothesis.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.gradedImage_stdVars`;
* `AlgebraicGeometry.ProjectiveSpace.gammaStarBaseChangeApp`;
* `AlgebraicGeometry.ProjectiveSpace.gammaStarBaseChangeHom`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Coefficient change fixes the standard homogeneous coordinates. -/
theorem gradedImage_stdVars (i : Fin (n + 1)) :
    ProjectiveSpectrum.Twist.gradedImage
        (MvPolynomial.mapGradedRingHom (ι := Fin (n + 1)) φ) (stdVars n R i) =
      stdVars n S i :=
  Subtype.ext (MvPolynomial.mapGradedRingHom_X φ i)

/-- The coefficient-change morphism of polynomial projective spectra. -/
noncomputable abbrev coeffMap :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S) ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) :=
  Proj.polynomialMap (Fin (n + 1)) φ

/-- The cartesian square exhibiting `Proj S[x]` as the base change of `Proj R[x]`. -/
theorem coeffMap_w :
    coeffMap n φ ≫ Proj.polynomialToSpec (Fin (n + 1)) R =
      Proj.polynomialToSpec (Fin (n + 1)) S ≫ Spec.map (CommRingCat.ofHom φ) :=
  (Proj.polynomialMap_isPullback (Fin (n + 1)) R φ).w

variable (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)

/-- The degree-`d` component of the comparison `Γ_*(F) ⊗ S ⟶ Γ_*(F_S)`. -/
noncomputable def gammaStarBaseChangeApp (d : ℤ) :
    letI : Algebra R S := φ.toAlgebra
    letI := Scheme.Modules.globalSectionsModule (Proj.polynomialToSpec (Fin (n + 1)) R)
      (ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d)
    letI := Scheme.Modules.globalSectionsModule (Proj.polynomialToSpec (Fin (n + 1)) S)
      (ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
        ((Scheme.Modules.pullback (coeffMap n φ)).obj F) d)
    S ⊗[R] Γ(ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d, ⊤) →ₗ[S]
      Γ(ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
        ((Scheme.Modules.pullback (coeffMap n φ)).obj F) d, ⊤) := by
  letI : Algebra R S := φ.toAlgebra
  letI := Scheme.Modules.globalSectionsModule (Proj.polynomialToSpec (Fin (n + 1)) S)
    ((Scheme.Modules.pullback (coeffMap n φ)).obj
      (ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d))
  exact (Scheme.Modules.globalSectionsLinearMap (Proj.polynomialToSpec (Fin (n + 1)) S)
      (ProjectiveSpectrum.Twist.twistModulePolynomialPullbackHom
        (Fin (n + 1)) φ F d)).comp
    (Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
      (CommRingCat.ofHom φ) (coeffMap n φ)
      (Proj.polynomialToSpec (Fin (n + 1)) R) (Proj.polynomialToSpec (Fin (n + 1)) S)
      (coeffMap_w n φ)
      (ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d))

/-- The degree-`d` component of the comparison, as a morphism of `ModuleCat S`. -/
noncomputable def gammaStarBaseChangeHomApp (d : ℤ) :
    letI : Algebra R S := φ.toAlgebra
    ((Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (Proj.polynomialToSpec (Fin (n + 1)) R) F (stdVars n R)).baseChange S).obj d ⟶
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
        (Proj.polynomialToSpec (Fin (n + 1)) S)
        ((Scheme.Modules.pullback (coeffMap n φ)).obj F) (stdVars n S)).obj d := by
  letI : Algebra R S := φ.toAlgebra
  letI := Scheme.Modules.globalSectionsModule (Proj.polynomialToSpec (Fin (n + 1)) R)
    (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d)
  letI := Scheme.Modules.globalSectionsModule (Proj.polynomialToSpec (Fin (n + 1)) S)
    (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
      ((Scheme.Modules.pullback (coeffMap n φ)).obj F) d)
  exact ModuleCat.ofHom (gammaStarBaseChangeApp n φ F d)

/-- Value of the degree-`d` component on a pure tensor. -/
theorem gammaStarBaseChangeApp_tmul (d : ℤ) (a : S)
    (m : Γ(ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d, ⊤)) :
    letI : Algebra R S := φ.toAlgebra
    letI := Scheme.Modules.globalSectionsModule (Proj.polynomialToSpec (Fin (n + 1)) R)
      (ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d)
    letI := Scheme.Modules.globalSectionsModule (Proj.polynomialToSpec (Fin (n + 1)) S)
      (ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
        ((Scheme.Modules.pullback (coeffMap n φ)).obj F) d)
    gammaStarBaseChangeApp n φ F d (a ⊗ₜ[R] m)
      = a • (ProjectiveSpectrum.Twist.twistModulePolynomialPullbackHom
            (Fin (n + 1)) φ F d).app ⊤
          (Scheme.Modules.pullbackGlobalSections (coeffMap n φ) _ m) := by
  letI : Algebra R S := φ.toAlgebra
  letI := Scheme.Modules.globalSectionsModule (Proj.polynomialToSpec (Fin (n + 1)) R)
    (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d)
  letI := Scheme.Modules.globalSectionsModule (Proj.polynomialToSpec (Fin (n + 1)) S)
    ((Scheme.Modules.pullback (coeffMap n φ)).obj
      (ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d))
  letI := Scheme.Modules.globalSectionsModule (Proj.polynomialToSpec (Fin (n + 1)) S)
    (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
      ((Scheme.Modules.pullback (coeffMap n φ)).obj F) d)
  change (Scheme.Modules.globalSectionsLinearMap (Proj.polynomialToSpec (Fin (n + 1)) S)
      (ProjectiveSpectrum.Twist.twistModulePolynomialPullbackHom
        (Fin (n + 1)) φ F d))
      (Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap
        (CommRingCat.ofHom φ) (coeffMap n φ) (Proj.polynomialToSpec (Fin (n + 1)) R)
        (Proj.polynomialToSpec (Fin (n + 1)) S) (coeffMap_w n φ)
        (ProjectiveSpectrum.Twist.twistModule
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d) (a ⊗ₜ[R] m)) = _
  rw [Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_tmul]
  exact map_smul _ a _

/-- Value of the degree-`d` component on a pure tensor, at the level of `ModuleCat`. -/
theorem gammaStarBaseChangeHomApp_tmul (d : ℤ) (a : S)
    (m : (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (Proj.polynomialToSpec (Fin (n + 1)) R) F (stdVars n R)).obj d) :
    letI : Algebra R S := φ.toAlgebra
    (gammaStarBaseChangeHomApp n φ F d).hom (a ⊗ₜ[R] m)
      = a • (show (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
            (Proj.polynomialToSpec (Fin (n + 1)) S)
            ((Scheme.Modules.pullback (coeffMap n φ)).obj F) (stdVars n S)).obj d from
          (ProjectiveSpectrum.Twist.twistModulePolynomialPullbackHom
            (Fin (n + 1)) φ F d).app ⊤
            (Scheme.Modules.pullbackGlobalSections (coeffMap n φ)
              (ProjectiveSpectrum.Twist.twistModule
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d) m)) :=
  gammaStarBaseChangeApp_tmul n φ F d a m

open ProjectiveSpectrum.Twist in
/-- **The comparison `Γ_*(F) ⊗ S ⟶ Γ_*(F_S)` for a change of coefficients.**

Degreewise it is extension of scalars on global sections followed by the twist comparison;
the degree-raising compatibility is
`ProjectiveSpectrum.Twist.pullback_map_twistModuleMulHom_comp_twistModulePolynomialPullbackHom`
combined with naturality of the pullback adjunction unit
(`Scheme.Modules.pullbackGlobalSections_naturality`). -/
noncomputable def gammaStarBaseChangeHom :
    letI : Algebra R S := φ.toAlgebra
    ((Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (Proj.polynomialToSpec (Fin (n + 1)) R) F (stdVars n R)).baseChange S) ⟶
      Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
        (Proj.polynomialToSpec (Fin (n + 1)) S)
        ((Scheme.Modules.pullback (coeffMap n φ)).obj F) (stdVars n S) := by
  letI : Algebra R S := φ.toAlgebra
  refine
    { app := fun d ↦ gammaStarBaseChangeHomApp n φ F d
      comm := fun i d ↦ ?_ }
  refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a m =>
      have hcomp :=
        pullback_map_twistModuleMulHom_comp_twistModulePolynomialPullbackHom
          (Fin (n + 1)) φ F (stdVars n R i) d (d + 1) (by norm_num)
      rw [gradedImage_stdVars] at hcomp
      have hkey := congrArg
        (fun ψ : (Scheme.Modules.pullback (coeffMap n φ)).obj
            (ProjectiveSpectrum.Twist.twistModule
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d) ⟶
            ProjectiveSpectrum.Twist.twistModule
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
              ((Scheme.Modules.pullback (coeffMap n φ)).obj F) (d + 1) ↦
          (ψ.app ⊤)
            (Scheme.Modules.pullbackGlobalSections (coeffMap n φ) _ m)) hcomp
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      have hbc : (((Proj.gammaStar
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
            (Proj.polynomialToSpec (Fin (n + 1)) R) F (stdVars n R)).baseChange S).mulX
              i d).hom (a ⊗ₜ[R] m)
          = a ⊗ₜ[R] (((Proj.gammaStar
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
            (Proj.polynomialToSpec (Fin (n + 1)) R) F (stdVars n R)).mulX i d).hom m) := rfl
      rw [gammaStarBaseChangeHomApp_tmul n φ F d a m, hbc,
        gammaStarBaseChangeHomApp_tmul n φ F (d + 1) a _, map_smul]
      congr 1
      rw [Proj.gammaStar_mulX_app_apply, Proj.gammaStar_mulX_app_apply,
        ← Scheme.Modules.pullbackGlobalSections_naturality]
      exact hkey.symm

/-- **The base-change comparison `Γ_*(F) ⊗ S ⟶ Γ_*(F_S)` is natural in the sheaf.** -/
theorem gammaStarBaseChangeHom_naturality
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (v : F ⟶ F') :
    letI : Algebra R S := φ.toAlgebra
    GradedModule.baseChangeMap
        (Proj.gammaStarMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (Proj.polynomialToSpec (Fin (n + 1)) R) v (stdVars n R)) S ≫
      gammaStarBaseChangeHom n φ F'
    = gammaStarBaseChangeHom n φ F ≫
      Proj.gammaStarMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
        (Proj.polynomialToSpec (Fin (n + 1)) S)
        ((Scheme.Modules.pullback (coeffMap n φ)).map v) (stdVars n S) := by
  letI : Algebra R S := φ.toAlgebra
  refine GradedModule.hom_ext fun d ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a m =>
      have hkey := congrArg
        (fun ψ : (Scheme.Modules.pullback (coeffMap n φ)).obj
            (ProjectiveSpectrum.Twist.twistModule
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F d) ⟶
            ProjectiveSpectrum.Twist.twistModule
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
              ((Scheme.Modules.pullback (coeffMap n φ)).obj F') d ↦
          (ψ.app ⊤)
            (Scheme.Modules.pullbackGlobalSections (coeffMap n φ) _ m))
        (ProjectiveSpectrum.Twist.pullback_map_twistModuleMap_comp_twistModulePolynomialPullbackHom
          (Fin (n + 1)) φ v d)
      have hbcm : ((GradedModule.baseChangeMap
            (Proj.gammaStarMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
              (Proj.polynomialToSpec (Fin (n + 1)) R) v (stdVars n R)) S).app d).hom
            (a ⊗ₜ[R] m)
          = a ⊗ₜ[R] (((Proj.gammaStarMap
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
              (Proj.polynomialToSpec (Fin (n + 1)) R) v (stdVars n R)).app d).hom m) := rfl
      show (gammaStarBaseChangeHomApp n φ F' d).hom
          (((GradedModule.baseChangeMap _ S).app d).hom (a ⊗ₜ[R] m)) = _
      rw [hbcm, gammaStarBaseChangeHomApp_tmul n φ F' d a _]
      have hrhs : ((gammaStarBaseChangeHom n φ F ≫
            Proj.gammaStarMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
              (Proj.polynomialToSpec (Fin (n + 1)) S)
              ((Scheme.Modules.pullback (coeffMap n φ)).map v) (stdVars n S)).app d).hom
            (a ⊗ₜ[R] m)
          = ((Proj.gammaStarMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
              (Proj.polynomialToSpec (Fin (n + 1)) S)
              ((Scheme.Modules.pullback (coeffMap n φ)).map v) (stdVars n S)).app d).hom
            ((gammaStarBaseChangeHomApp n φ F d).hom (a ⊗ₜ[R] m)) := rfl
      rw [hrhs, gammaStarBaseChangeHomApp_tmul n φ F d a m, map_smul]
      congr 1
      have hnat := Scheme.Modules.pullbackGlobalSections_naturality (coeffMap n φ)
        (ProjectiveSpectrum.Twist.twistModuleMap
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) v d) m
      have hgoal : (ProjectiveSpectrum.Twist.twistModulePolynomialPullbackHom
            (Fin (n + 1)) φ F' d).app ⊤
            (Scheme.Modules.pullbackGlobalSections (coeffMap n φ) _
              ((ProjectiveSpectrum.Twist.twistModuleMap
                (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) v d).app ⊤ m))
          = (ProjectiveSpectrum.Twist.twistModuleMap
              (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
              ((Scheme.Modules.pullback (coeffMap n φ)).map v) d).app ⊤
            ((ProjectiveSpectrum.Twist.twistModulePolynomialPullbackHom
              (Fin (n + 1)) φ F d).app ⊤
              (Scheme.Modules.pullbackGlobalSections (coeffMap n φ) _ m)) := by
        rw [← hnat]
        exact hkey
      exact hgoal

end AlgebraicGeometry.ProjectiveSpace

end

end
