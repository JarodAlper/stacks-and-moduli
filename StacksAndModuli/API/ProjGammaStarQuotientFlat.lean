module

public import StacksAndModuli.API.ProjGammaStarFlat
public import StacksAndModuli.API.ProjGammaStarProjectiveSpace
public import StacksAndModuli.API.ProjectiveSpaceTwistProjComparison
public import StacksAndModuli.API.ProjectiveTwistedFreeGlobalSectionsFinite
public import StacksAndModuli.API.ProjGammaStarQuotientComparison
public import StacksAndModuli.API.ProjGammaStarQuotientChart
public import StacksAndModuli.API.ProjectiveGradedSchemeComparisonFlatCochain

/-!
# The base-change package from a geometric flatness hypothesis

`API/ProjGammaStarQuotientComparison.lean` produces
`Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange` from a presentation of `Q`
together with the *graded* hypothesis `GradedModule.IsFlat (Γ_*(Q))`.  What §2.4 actually
carries is the *geometric* one, `Scheme.Modules.FlatOver` — the flatness clause of a
`Scheme.Modules.QuotientPullbackData`.  This file converts one into the other:

* `isFlat_gammaStarPull_of_flatOver` — transport `FlatOver` across `ℙⁿ_{Spec R} ≅ Proj R[x]`
  (`Scheme.Modules.FlatOver.pullback_isIso` with
  `projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ`), then apply
  `Proj.isFlat_gammaStar_of_flatOver`;
* `hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_flatOver` — the resulting statement.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.isFlat_gammaStarPull_of_flatOver`;
* `AlgebraicGeometry.ProjectiveSpace.`
  `hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_flatOver`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {n : ℕ} {R : Type u} [CommRing R] [IsNoetherianRing R]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search
-- slow; see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
/-- **The single-variable localization of the kernel-route model is degreewise flat.** -/
theorem isFlat_loc_kernelQuotientModule
    {F F' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : F ⟶ F') [Epi p] (i : Fin (n + 1))
    [∀ e : ℤ, (twistModule 𝒜 F e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 F' e).IsQuasicoherent]
    [∀ e : ℤ, (twistModule 𝒜 (kernel p) e).IsQuasicoherent]
    (hflat : F'.FlatOver (projSpecπ n R)) :
    GradedModule.IsFlat
      ((kernelQuotientModule 𝒜 (projSpecπ n R) (ProjectiveSpace.stdVars n R) p).loc [i]) := by
  intro e
  have hcover := ProjectiveSpace.top_le_iSup_basicOpen_stdVars n R
  letI := Scheme.Modules.openSectionsModuleOver (projSpecπ n R) (twistModule 𝒜 F' e)
    (basicOpen 𝒜 ((ProjectiveSpace.stdVars n R i : MvPolynomial (Fin (n + 1)) R)))
  letI := Scheme.Modules.openSectionsModuleOver (projSpecπ n R) F'
    (basicOpen 𝒜 ((ProjectiveSpace.stdVars n R i : MvPolynomial (Fin (n + 1)) R)))
  haveI hF : Module.Flat R
      Γ(F', basicOpen 𝒜 ((ProjectiveSpace.stdVars n R i : MvPolynomial (Fin (n + 1)) R))) :=
    Scheme.Modules.flat_openSections_of_flatOver (projSpecπ n R) F' hflat
      ⟨basicOpen 𝒜 _, isAffineOpen_basicOpen 𝒜 _ (ProjectiveSpace.stdVars n R i).2 Nat.one_pos⟩
  haveI hT : Module.Flat R
      Γ(twistModule 𝒜 F' e,
        basicOpen 𝒜 ((ProjectiveSpace.stdVars n R i : MvPolynomial (Fin (n + 1)) R))) :=
    flat_openSections_twistModule_basicOpen 𝒜 (projSpecπ n R) F'
      (ProjectiveSpace.stdVars n R) i e hF
  refine Module.Flat.of_linearEquiv
    ((LinearEquiv.ofBijective _
      (bijective_locMap_kernelQuotientToGammaStar (projSpecπ n R) p i e)).trans
      (LinearEquiv.ofBijective (chartColimitMap 𝒜 (projSpecπ n R) F'
        (ProjectiveSpace.stdVars n R) i e)
        (bijective_chartColimitMap 𝒜 (projSpecπ n R) F' (ProjectiveSpace.stdVars n R) i
          hcover e)))

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search
-- slow; see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
omit [IsNoetherianRing R] in
/-- **The chart localizations of `Γ_*(F)` are degreewise flat when `F` is flat over the base.**
On `D₊(xᵢ)` the localization is the chart sections of `F(e)`, and every twist is trivial
there. -/
theorem isFlat_loc_gammaStar_of_flatOver
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    [∀ e : ℤ, (twistModule 𝒜 F e).IsQuasicoherent] (i : Fin (n + 1))
    (hflat : F.FlatOver (projSpecπ n R)) :
    GradedModule.IsFlat
      ((gammaStar 𝒜 (projSpecπ n R) F (ProjectiveSpace.stdVars n R)).loc [i]) := by
  intro e
  have hcover := ProjectiveSpace.top_le_iSup_basicOpen_stdVars n R
  letI := Scheme.Modules.openSectionsModuleOver (projSpecπ n R) (twistModule 𝒜 F e)
    (basicOpen 𝒜 ((ProjectiveSpace.stdVars n R i : MvPolynomial (Fin (n + 1)) R)))
  letI := Scheme.Modules.openSectionsModuleOver (projSpecπ n R) F
    (basicOpen 𝒜 ((ProjectiveSpace.stdVars n R i : MvPolynomial (Fin (n + 1)) R)))
  haveI hF : Module.Flat R
      Γ(F, basicOpen 𝒜 ((ProjectiveSpace.stdVars n R i : MvPolynomial (Fin (n + 1)) R))) :=
    Scheme.Modules.flat_openSections_of_flatOver (projSpecπ n R) F hflat
      ⟨basicOpen 𝒜 _, isAffineOpen_basicOpen 𝒜 _ (ProjectiveSpace.stdVars n R i).2 Nat.one_pos⟩
  haveI hT : Module.Flat R
      Γ(twistModule 𝒜 F e,
        basicOpen 𝒜 ((ProjectiveSpace.stdVars n R i : MvPolynomial (Fin (n + 1)) R))) :=
    flat_openSections_twistModule_basicOpen 𝒜 (projSpecπ n R) F
      (ProjectiveSpace.stdVars n R) i e hF
  exact Module.Flat.of_linearEquiv
    (LinearEquiv.ofBijective (chartColimitMap 𝒜 (projSpecπ n R) F
      (ProjectiveSpace.stdVars n R) i e)
      (bijective_chartColimitMap 𝒜 (projSpecπ n R) F (ProjectiveSpace.stdVars n R) i
        hcover e))

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **`Γ_*` of a flat family on `ℙⁿ_{Spec R}` is degreewise flat**, over a Dedekind base. -/
theorem isFlat_gammaStarPull_of_flatOver
    (n : ℕ) (R : Type u) [CommRing R] [IsDedekindDomain R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))) :
    (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (projSpecπ n R)
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
      (stdVars n R)).IsFlat :=
  Proj.isFlat_gammaStar_of_flatOver _ (projSpecπ n R) _ (stdVars n R)
    (top_le_iSup_basicOpen_stdVars n R)
    (Scheme.Modules.FlatOver.pullback_isIso (projectiveSpaceOverSpecIso n R).inv Q
      (projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R) hflat)

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search slow;
-- see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
/-- **Relative Serre vanishing and Cohomology & Base Change from a geometric flatness
hypothesis.**  The graded flatness hypothesis of
`hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_presentation` is replaced by
`Scheme.Modules.FlatOver`, the condition the Quot functor actually carries. -/
def hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_flatOver
    (n : ℕ) (R : Type u) [CommRing R] [IsDedekindDomain R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    [Q.IsFinitePresentation]
    {E : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : E ⟶ (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) [Epi p]
    [∀ e : ℤ,
      (ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E e).IsQuasicoherent]
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) e).IsQuasicoherent]
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (CategoryTheory.Limits.kernel p) e).IsQuasicoherent]
    (hFG : GradedModule.IsFG
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) E (stdVars n R)))
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))) :
    Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q :=
  hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_presentation n R Q p hFG
    (isFlat_gammaStarPull_of_flatOver n R Q hflat)

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search slow;
-- see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
/-- **Relative Serre vanishing and Cohomology & Base Change over an arbitrary noetherian base.**

The Dedekind hypothesis of
`hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_flatOver` is gone.  It was there only to
make the graded model `Γ_*(E) ⧸ Γ_*(K)` *degreewise* flat, and Cohomology and Base Change does
not need that: it needs the Čech cochain groups to be flat, and on `Proj` those are sections on
the affine charts, hence flat as soon as the sheaf is flat over the base
(`Proj.isFlat_loc_kernelQuotientModule` and `GradedModule.flat_cechCochain_of_flat_loc`). -/
def hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_flatOver'
    (n : ℕ) (R : Type u) [CommRing R] [IsNoetherianRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    [Q.IsFinitePresentation]
    {E : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules}
    (p : E ⟶ (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) [Epi p]
    [∀ e : ℤ,
      (ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E e).IsQuasicoherent]
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) e).IsQuasicoherent]
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (CategoryTheory.Limits.kernel p) e).IsQuasicoherent]
    (hFG : GradedModule.IsFG
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R) E (stdVars n R)))
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))) :
    Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q := by
  have hflat' : ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q).FlatOver
      (projSpecπ n R) :=
    Scheme.Modules.FlatOver.pullback_isIso (projectiveSpaceOverSpecIso n R).inv Q
      (projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R) hflat
  refine toHasEventualFiniteProjectiveGlobalSectionsBaseChange'
    (schemeGlobalSectionsComparisonQuotientModel n R Q p)
    (GradedModule.IsFG.coker _ hFG) (fun d q => ?_)
  exact GradedModule.flat_cechCochain_of_flat_loc _
    (fun a => Proj.isFlat_loc_kernelQuotientModule p a hflat') q d

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search slow;
-- see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
set_option maxHeartbeats 1000000 in
-- Same cause: elaborating `flat_cechCochain_of_flat_loc` at `Γ_*` is instance-heavy.
/-- **Relative Serre vanishing and Cohomology & Base Change for `Γ_*(Q)` itself.**

No presentation is needed — only Serre finiteness of `Γ_*(Q)` as a graded module, and flatness
of `Q` over the base.  With a twisted-free presentation the finiteness hypothesis is supplied by
`isFG_gammaStarPullTwistedFree` and `GradedModule.IsFG.coker`
(`hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_flatOver'`); this version is the one to
use once Serre's finiteness theorem is available for `Γ_*`. -/
def hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_isFG
    (n : ℕ) (R : Type u) [CommRing R] [IsNoetherianRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    [Q.IsFinitePresentation]
    (hFG : GradedModule.IsFG
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) (stdVars n R)))
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))) :
    Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q := by
  have hflat' : ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q).FlatOver
      (projSpecπ n R) :=
    Scheme.Modules.FlatOver.pullback_isIso (projectiveSpaceOverSpecIso n R).inv Q
      (projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R) hflat
  haveI : ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
      Q).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI : ∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
      e).IsQuasicoherent := fun e => twistModule_std_isQuasicoherent _ e
  have hC : ∀ (d : ℤ) (q : ℕ), Module.Flat R
      (((Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
        (stdVars n R)).cechComplex d).X q) := fun d q =>
    GradedModule.flat_cechCochain_of_flat_loc _
      (fun a => Proj.isFlat_loc_gammaStar_of_flatOver _ a hflat') q d
  exact toHasEventualFiniteProjectiveGlobalSectionsBaseChange'
    (schemeGlobalSectionsComparisonOfIsFinitePresentation n R Q) hFG hC

end AlgebraicGeometry.ProjectiveSpace

end

end
