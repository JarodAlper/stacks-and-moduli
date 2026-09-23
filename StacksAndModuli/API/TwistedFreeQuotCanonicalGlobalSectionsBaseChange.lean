module

public import StacksAndModuli.API.ProjectiveCanonicalGlobalSectionsBaseChange
public import StacksAndModuli.API.TwistedFreeQuotArbitraryBase
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNatTrans

/-!
# Canonical global-sections base change for twisted-free quotients

A twisted-free quotient on projective space has a finitely generated kernel-quotient
graded model.  Over a noetherian affine base, the kernel graded module is finitely
generated as a submodule of the twisted-free ambient graded module.  The generic
kernel-quotient canonical-base-change theorem therefore supplies the literal comparison
required by finite-free vanishing models.

Main declaration:

* `AlgebraicGeometry.ProjectiveSpace.`
  `hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_twistedFreeQuotient`.
* `AlgebraicGeometry.Scheme.Modules.QuotientPullbackData.`
  `hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_twistedFree`.
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

set_option synthInstance.maxHeartbeats 1000000 in
-- Normalizing the twisted-free source creates quantified pullback/twist instances.
set_option maxHeartbeats 2000000 in
/-- A flat finitely presented quotient of a finite twisted-free sheaf over a noetherian
affine base has eventual finite-projective global sections with literal canonical
arbitrary-ring base change. -/
noncomputable def
    hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_twistedFreeQuotient
    (n r : ℕ) (hn : 0 < n) (l : ℤ)
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) ⟶ Q)
    [Epi q]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R)))) :
    Proj.HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) := by
  haveI hAmbfp : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)).IsFinitePresentation :=
    Scheme.twistedFreeAmbient_isFinitePresentation n (Spec (.of R)) l r
  let E := projAmbient n r l (R := R)
  let F := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q
  let p : E ⟶ F :=
    (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map q
  haveI hEfp : E.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hFfp : F.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hp : Epi p := inferInstance
  haveI hEqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) E e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent E e
  haveI hFqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent F e
  haveI hKfp : (kernel p).IsFinitePresentation :=
    Scheme.Modules.kernel_isFinitePresentation p
  haveI hKqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (kernel p) e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent (kernel p) e
  have hM : GradedModule.IsFG (Proj.kernelQuotientModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (projSpecπ n R) (stdVars n R) p) :=
    isFG_kernelQuotientModule_twistedFree_arbitrary n r hn l R Q q
  have hEfg : GradedModule.IsFG (Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (projSpecπ n R) E (stdVars n R)) :=
    isFG_gammaStarPullTwistedFree n R hn (-l) r
  have hK : GradedModule.IsFG (Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (projSpecπ n R) (kernel p) (stdVars n R)) :=
    GradedModule.IsFG.of_injective _
      (fun e ↦ Proj.injective_gammaStarMap_kernel_ι (Fin (n + 1))
        (projSpecπ n R) (stdVars n R) p e) hEfg
  have hflat' : F.FlatOver (projSpecπ n R) :=
    Scheme.Modules.FlatOver.pullback_isIso
      (projectiveSpaceOverSpecIso n R).inv Q
      (projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ n R) hflat
  exact
    Proj.hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_of_kernelQuotient
      E F p hM hK hflat'

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.Modules.QuotientPullbackData

open ProjectiveSpectrum.Twist
open AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
-- Normalizing the relative quotient datum creates quantified pullback/twist instances.
set_option maxHeartbeats 2000000 in
/-- A twisted-free Quot datum over an affine noetherian base has eventual
finite-projective global sections with literal canonical arbitrary-ring base change after
normalization to polynomial `Proj`. -/
noncomputable def
    hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_twistedFree
    {S : Scheme.{u}} (n r : ℕ) (hn : 0 < n) (l : ℤ)
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (sigma : Spec (.of R) ⟶ S)
    (y : Scheme.Modules.QuotientPullbackData
      (twistedFreeAmbient (n := n) (r := r) (l := l))
      (Scheme.projectiveSpaceOverπ n S) (Over.mk sigma)) :
    Proj.HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange
      ((Scheme.Modules.pullback
        (ProjectiveSpace.projectiveSpaceOverSpecIso n R).inv).obj
          (quotDataOnProjectiveSpace
            (n := n) (S := S) (T := Over.mk sigma)
            (twistedFreeAmbient (n := n) (r := r) (l := l)) y)) := by
  let T : Over S := Over.mk sigma
  let Q := quotDataOnProjectiveSpace
    (n := n) (S := S) (T := T)
    (twistedFreeAmbient (n := n) (r := r) (l := l)) y
  let q := twistedFreeQuotientOnProjectiveSpaceOver T y
  haveI hQfp : Q.IsFinitePresentation :=
    quotDataOnProjectiveSpace_isFinitePresentation_over T y
  haveI hq : Epi q := twistedFreeQuotientOnProjectiveSpaceOver_epi T y
  have hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (.of R))) :=
    quotDataOnProjectiveSpace_flatOver_over T y
  exact
    hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_twistedFreeQuotient
      n r hn l R Q q hflat

end AlgebraicGeometry.Scheme.Modules.QuotientPullbackData

end

end
