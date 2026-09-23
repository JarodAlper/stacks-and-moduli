module

public import StacksAndModuli.API.ProjGammaStarQuotientChart
public import StacksAndModuli.API.ProjGammaStarBaseChangeObligation
public import StacksAndModuli.API.ProjectiveGradedFlatTorsionFree
public import StacksAndModuli.API.ProjectiveGradedRelativeExists

/-!
# The scheme-level `H⁰` comparison for a presented sheaf

`RelativeCohomology.SchemeGlobalSectionsComparison Crel M Q` is what turns the graded Čech
theory into the scheme-level package
`Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange` that §2.4 consumes.  It
does **not** have to be built with `M = Γ_*(Q)`: any graded module with the same `Hᵍʳ 0` will
do, and for a quotient sheaf the natural choice is the kernel-route model

`N := Γ_*(E) ⧸ Γ_*(K)`,   `K = ker(E ↠ Q)`,

because `N` is finitely generated as soon as `Γ_*(E)` is, whereas finite generation of
`Γ_*(Q)` is Serre's theorem.  `API/ProjGammaStarQuotientChart.lean` shows `N` and `Γ_*(Q)` have
the same localizations, hence the same `Hᵍʳ 0`; this file turns that into the comparison
structure and then into the scheme-level package.

The fibre half needs the same statement after base change to a field, and that is
`GradedModule.bijective_locMap_baseChangeMap_app` (base change of a localized isomorphism is
one) chained with `hasGammaStarBaseChangeCechHgrZero_of_isFinitePresentation`.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.cechHgrZeroQuotientModelGlobalSectionsEquiv`;
* `AlgebraicGeometry.ProjectiveSpace.isIso_cechHgrMap_baseChangeMap_kernelQuotientToGammaStar`;
* `AlgebraicGeometry.ProjectiveSpace.schemeGlobalSectionsComparisonQuotientModel`;
* `AlgebraicGeometry.ProjectiveSpace.`
  `hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_presentation`.
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

namespace AlgebraicGeometry.ProjectiveSpace

open ProjectiveSpectrum.Twist

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) (R : Type u) [CommRing R] [IsNoetherianRing R]

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search
-- slow; see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
/-- The kernel-route model computes the global sections of `Q(d)` on `ℙⁿ_{Spec R}`. -/
def cechHgrZeroQuotientModelGlobalSectionsEquiv
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    [Q.IsFinitePresentation]
    {E : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : E ⟶ (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) [Epi p]
    [∀ e : ℤ,
      (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) e).IsQuasicoherent]
    (d : ℤ) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q d)
    (((Proj.kernelQuotientModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) (stdVars n R) p).cechHgr 0).obj d) ≃ₗ[CommRingCat.of R]
      Γ(Scheme.projectiveSpaceOverTwistModule Q d, ⊤) := by
  haveI := Proj.isIso_cechHgrMap_kernelQuotientToGammaStar (projSpecπ n R) p d
  exact (asIso ((GradedModule.cechHgrMap
        (Proj.kernelQuotientToGammaStar _ (projSpecπ n R) (stdVars n R) p)
        0).app d)).toLinearEquiv.trans
    (cechHgrZeroGlobalSectionsEquiv Q d)

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search
-- slow; see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
/-- The base change of the kernel-route comparison is still an isomorphism on `Hᵍʳ 0`. -/
theorem isIso_cechHgrMap_baseChangeMap_kernelQuotientToGammaStar
    {E : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    {G : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : E ⟶ G) [Epi p]
    [∀ e : ℤ,
      (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E e).IsQuasicoherent]
    [∀ e : ℤ,
      (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) G e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) e).IsQuasicoherent]
    (K : Type u) [CommRing K] [Algebra R K] (d : ℤ) :
    IsIso ((GradedModule.cechHgrMap (GradedModule.baseChangeMap
      (Proj.kernelQuotientToGammaStar _ (projSpecπ n R) (stdVars n R) p) K) 0).app d) := by
  refine GradedModule.isIso_cechHgrMap_app_zero_of_injective _ _ (fun τ => ?_) (fun τ => ?_)
  · obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (by simpa using τ.length_eq)
    exact GradedModule.bijective_locMap_app_of_list_eq _ ha _
      (GradedModule.bijective_locMap_baseChangeMap_app K _ [a] d
        (Proj.bijective_locMap_kernelQuotientToGammaStar (projSpecπ n R) p a d))
  · obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (by simpa using τ.length_eq)
    refine GradedModule.injective_locMap_app_of_list_eq _ hab _ ?_
    exact GradedModule.injective_locMap_pair_app _ a b _ fun t =>
      GradedModule.bijective_locMap_baseChangeMap_app K _ [a] (d + (t : ℤ))
        (Proj.bijective_locMap_kernelQuotientToGammaStar (projSpecπ n R) p a (d + (t : ℤ)))

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search
-- slow; see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
/-- **The scheme-level `H⁰` comparison for the kernel-route graded model.** -/
def schemeGlobalSectionsComparisonQuotientModel
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    [Q.IsFinitePresentation]
    {E : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : E ⟶ (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) [Epi p]
    [∀ e : ℤ,
      (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) e).IsQuasicoherent] :
    (RelativeCohomology.cech R).SchemeGlobalSectionsComparison
      (Proj.kernelQuotientModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) (stdVars n R) p) Q where
  bound := 0
  globalSectionsIso d _ := cechHgrZeroQuotientModelGlobalSectionsEquiv n R Q p (d : ℤ)
  fibreGlobalSectionsIso K _ f d _ := by
    letI : Algebra R K := f.toAlgebra
    haveI := isIso_cechHgrMap_baseChangeMap_kernelQuotientToGammaStar n R p K (d : ℤ)
    haveI : (Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f).IsFinitePresentation :=
      Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
    exact (asIso ((GradedModule.cechHgrMap (GradedModule.baseChangeMap
        (Proj.kernelQuotientToGammaStar _ (projSpecπ n R) (stdVars n R) p) K)
        0).app (d : ℤ))).toLinearEquiv.trans
      ((hasGammaStarBaseChangeCechHgrZero_of_isFinitePresentation n R Q K f d).some.trans
        (cechHgrZeroGlobalSectionsEquiv
          (Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f) (d : ℤ)))

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search
-- slow; see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
set_option linter.overlappingInstances false in
/-- **Relative Serre vanishing and Cohomology & Base Change, at the scheme level, for a
presented flat sheaf on `ℙⁿ_{Spec R}`.** -/
def hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_presentation
    [IsDedekindDomain R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    [Q.IsFinitePresentation]
    {E : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : E ⟶ (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) [Epi p]
    [∀ e : ℤ,
      (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) e).IsQuasicoherent]
    (hFG : GradedModule.IsFG
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) E (stdVars n R)))
    (hflat : (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
        (stdVars n R)).IsFlat) :
    Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q :=
  (schemeGlobalSectionsComparisonQuotientModel n R Q
      p).toHasEventualFiniteProjectiveGlobalSectionsBaseChange
    (GradedModule.IsFG.coker _ hFG)
    (GradedModule.IsFlat.coker_of_exact _
      (Proj.gammaStarMap (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) p (stdVars n R))
      (fun d => Proj.exact_gammaStarMap_kernel (Fin (n + 1)) (projSpecπ n R) (stdVars n R) p d)
      hflat)

end AlgebraicGeometry.ProjectiveSpace

end

end
