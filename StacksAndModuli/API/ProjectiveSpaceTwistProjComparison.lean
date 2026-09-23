module

public import StacksAndModuli.API.ProjGammaStarProjectiveSpace
public import StacksAndModuli.API.ProjectiveSpaceOverSpecComparison
public import StacksAndModuli.API.SchemeModulesPullbackTensor
public import StacksAndModuli.API.SchemeModulesTensorQuasicoherent
public import StacksAndModuli.API.ProjectiveTwistBaseChange
public import StacksAndModuli.API.ProjectiveGradedSchemeComparison
public import StacksAndModuli.API.ProjectiveGradedRelativeExists
public import StacksAndModuli.API.ProjectiveTwistedFreeGlobalSectionsFinite

/-!
# Relative twists on `ℙⁿ_R` are the intrinsic twists on polynomial `Proj`

`API/ProjectiveSpaceOverSpecComparison.lean` identifies `ℙⁿ_{Spec R}` with
`Proj R[x₀, …, xₙ]` and, for the *unit* sheaf, its twisting sheaves with the intrinsic ones.
This file upgrades that to an arbitrary sheaf: for every `Q` on `ℙⁿ_{Spec R}` and every
`d : ℤ`, pulling `Q(d)` across the comparison gives the intrinsic twist of the pullback of
`Q`.  Both twists are `Scheme.Modules.tensor · (twist d)`, so the upgrade is the unit case
plus the fact that pullback along an open immersion — in particular along an isomorphism —
commutes with tensor products.

Transporting global sections across that isomorphism then identifies
`Γ(ℙⁿ_R, Q(d))` with the degree-`d` piece of `Γ_*` of the pullback, `R`-linearly.  Composed
with the `H⁰` comparison of `API/ProjGammaStarProjectiveSpace.lean`, this is the field
`globalSectionsIso` of
`AlgebraicGeometry.ProjectiveSpace.RelativeCohomology.SchemeGlobalSectionsComparison`.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.projSpecπ`;
* `AlgebraicGeometry.ProjectiveSpace.projectiveSpaceOverTwistModulePullbackIso`;
* `AlgebraicGeometry.ProjectiveSpace.projectiveSpaceTwistedGlobalSectionsEquiv`;
* `AlgebraicGeometry.ProjectiveSpace.cechHgrZeroGlobalSectionsEquiv`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The structure morphism of polynomial `Proj` to `Spec R`.

`AlgebraicGeometry.ProjectiveSpace.projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ`
identifies it with the transport of the structure morphism of `ℙⁿ_{Spec R}` along the
comparison isomorphism, which is what makes the graded module `Proj.gammaStar` carry exactly
the `R`-module structure that the scheme side uses.  It is also the morphism that
`API/ProjectiveStandardCoverBaseChange.lean` uses, so coefficient-change squares apply
directly. -/
noncomputable abbrev projSpecπ :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) ⟶ Spec (CommRingCat.of R) :=
  Proj.polynomialToSpec (Fin (n + 1)) R

variable {n R}

/-- Pulling a twisted sheaf `Q(d)` on `ℙⁿ_{Spec R}` across the comparison isomorphism gives
the intrinsic twist of the pullback of `Q`. -/
noncomputable def projectiveSpaceOverTwistModulePullbackIso
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules) (d : ℤ) :
    (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
        (Scheme.projectiveSpaceOverTwistModule Q d) ≅
      ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) d :=
  Scheme.Modules.pullbackTensorIsoOfIsOpenImmersion
      (projectiveSpaceOverSpecIso n R).inv Q _ ≪≫
    Scheme.Modules.tensorRightIso _ (projectiveSpaceOverTwistPullbackIso n R d)

/-- **Global sections of a relative twist are the graded piece of `Γ_*`.**  Transporting
across the comparison isomorphism identifies `Γ(ℙⁿ_R, Q(d))` with the degree-`d` piece of
`Γ_*` of the pullback of `Q`, `R`-linearly. -/
noncomputable def projectiveSpaceTwistedGlobalSectionsEquiv
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules) (d : ℤ) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q d)
    letI := Scheme.Modules.globalSectionsModule (projSpecπ n R)
      (ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) d)
    Γ(Scheme.projectiveSpaceOverTwistModule Q d, ⊤) ≃ₗ[CommRingCat.of R]
      Γ(ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) d, ⊤) :=
  Scheme.Modules.pullbackGlobalSectionsViaIsoLinearEquiv'
    (projectiveSpaceOverSpecIso n R).inv
    (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))
    (projSpecπ n R)
    (projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R)
    (Scheme.projectiveSpaceOverTwistModule Q d)
    (projectiveSpaceOverTwistModulePullbackIso Q d)

/-- The pullback of a finitely presented sheaf across the comparison isomorphism is finitely
presented. -/
instance projectiveSpaceOverSpecIso_pullback_isFinitePresentation
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    [Q.IsFinitePresentation] :
    ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
      Q).IsFinitePresentation :=
  Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _
    inferInstance

/-- **The `H⁰` comparison, in the form the scheme-level interface wants.**  For a finitely
presented sheaf `Q` on `ℙⁿ_{Spec R}`, the degree-`d` piece of the graded Čech `H⁰` of
`Γ_*` of the pullback of `Q` is `R`-linearly isomorphic to `Γ(ℙⁿ_R, Q(d))`.

This is the field `globalSectionsIso` of
`RelativeCohomology.SchemeGlobalSectionsComparison` for the Čech model
`RelativeCohomology.cech R`, whose `Hgr M 0` is by definition `M.cechHgr 0`. -/
noncomputable def cechHgrZeroGlobalSectionsEquiv
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    [Q.IsFinitePresentation] (d : ℤ) :
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q d)
    (((Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
        (stdVars n R)).cechHgr 0).obj d) ≃ₗ[CommRingCat.of R]
      Γ(Scheme.projectiveSpaceOverTwistModule Q d, ⊤) :=
  (cechHgrZeroEquivOfIsFinitePresentation (projSpecπ n R)
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) d).trans
    (projectiveSpaceTwistedGlobalSectionsEquiv Q d).symm

variable (n R)

/-- **The remaining half of the `H⁰` bridge**: base changing the graded module `Γ_*(F)` to a
field computes the same degree-zero Čech cohomology as `Γ_*` of the base-changed sheaf.

This is the exact statement that `Γ_*` commutes with field base change *after* taking Čech
`H⁰`; it is weaker than commutation of `Γ_*` itself, because Čech cohomology only sees the
localizations at the coordinates (`GradedModule.isIso_cechHgrMap_app`).  Everything else in
`RelativeCohomology.SchemeGlobalSectionsComparison` is supplied by
`cechHgrZeroGlobalSectionsEquiv`.

Only **non-negative** degrees are asked for.  That is all `schemeGlobalSectionsComparison`
consumes (`fibreGlobalSectionsIso` is indexed by `d : ℕ`), and it is all the chart argument
of `isIso_cechHgrMap_gammaStarBaseChangeHom_app` can supply, since the twist-pullback
comparison is known to be an isomorphism only for non-negative twists. -/
def HasGammaStarBaseChangeCechHgrZero
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules) : Prop :=
  ∀ (K : Type u) [Field K] (f : R →+* K) (d : ℕ),
    letI : Algebra R K := f.toAlgebra
    Nonempty
      (((((Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
              (projSpecπ n R)
              ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
              (stdVars n R)).baseChange K).cechHgr 0).obj (d : ℤ)) ≃ₗ[K]
        ((((Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
              (projSpecπ n K)
              ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n K).inv).obj
                (Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f))
              (stdVars n K)).cechHgr 0).obj (d : ℤ))))

variable {n R}

/-- **The scheme-level `H⁰` comparison of §2.3/§2.4, modulo one base-change statement.**

For a finitely presented sheaf `Q` on `ℙⁿ_{Spec R}` over a noetherian ring, the graded Čech
model computes `Γ(ℙⁿ_R, Q(d))` in every degree, and it does so on every field fibre as soon
as `HasGammaStarBaseChangeCechHgrZero` holds.  Feeding the result to
`RelativeCohomology.SchemeGlobalSectionsComparison.toHasEventualFiniteProjectiveGlobalSectionsBaseChange`
turns relative Serre vanishing and Cohomology and Base Change in the graded model into the
scheme-level package used by §2.4. -/
noncomputable def schemeGlobalSectionsComparison [IsNoetherianRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    [Q.IsFinitePresentation]
    (h : HasGammaStarBaseChangeCechHgrZero n R Q) :
    (RelativeCohomology.cech R).SchemeGlobalSectionsComparison
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
        (stdVars n R)) Q where
  bound := 0
  globalSectionsIso d _ := cechHgrZeroGlobalSectionsEquiv Q (d : ℤ)
  fibreGlobalSectionsIso K _ f d _ := by
    letI : Algebra R K := f.toAlgebra
    haveI : (Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f).IsFinitePresentation :=
      Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
    exact (h K f d).some.trans
      (cechHgrZeroGlobalSectionsEquiv
        (Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f) (d : ℤ))

end AlgebraicGeometry.ProjectiveSpace

end

end
