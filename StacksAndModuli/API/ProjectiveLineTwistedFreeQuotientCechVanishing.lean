module

public import StacksAndModuli.API.ProjectiveLineGradedAugmentationKoszul
public import StacksAndModuli.API.ProjectiveLineGradedKoszulSurjectivity
public import StacksAndModuli.API.TwistedFreeQuotPushforwardRank

/-!
# Cech vanishing for twisted-free quotients on the projective line

On the projective line, a quotient of a finite sum of copies of `O(-l)` has vanishing
first Cech cohomology in every graded degree at least `l - 1`, over an arbitrary
coefficient ring.  The proof uses the long exact Cech sequence for the kernel-route
graded quotient: the ambient first cohomology vanishes in this range and the kernel's
second cohomology vanishes by dimension.

The resulting vanishing supplies the surjectivity hypothesis in the projective-line
Koszul recurrence on zeroth Cech cohomology.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A twisted-free quotient on the projective line has vanishing first graded Cech
cohomology in every degree at least one below the source twist. -/
theorem subsingleton_cechHgr_one_gammaStar_twistedFreeQuotient
    (r : ℕ) (R : Type u) [CommRing R] (l d : ℤ) (hd : l - 1 ≤ d)
    (Q : (Scheme.projectiveSpaceOver 1 (Spec (.of R))).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) (-l)) ⟶ Q)
    [Epi q] :
    let G := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso 1 R).inv).obj Q
    Subsingleton (((Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin 2) R) (projSpecπ 1 R) G
      (stdVars 1 R)).cechHgr 1).obj d) := by
  let E := projAmbient 1 r l (R := R)
  let G := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso 1 R).inv).obj Q
  let p := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso 1 R).inv).map q
  haveI hp : Epi p := inferInstance
  haveI hAmbientFp : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) (-l)).IsFinitePresentation :=
    Scheme.twistedFreeAmbient_isFinitePresentation 1 (Spec (.of R)) l r
  haveI hEfp : E.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hGfp : G.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hEqc : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin 2) R) E a).IsQuasicoherent :=
    fun a ↦ twistModule_std_isQuasicoherent _ a
  haveI hGqc : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin 2) R) G a).IsQuasicoherent :=
    fun a ↦ twistModule_std_isQuasicoherent _ a
  haveI hKqc : (kernel p).IsQuasicoherent := Scheme.Modules.kernel_isQuasicoherent p
  haveI hKtwistQc : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin 2) R) (kernel p) a).IsQuasicoherent :=
    fun a ↦ twistModule_std_isQuasicoherent_of_isQuasicoherent 1 _ a
  haveI hEone : Subsingleton (((Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin 2) R) (projSpecπ 1 R) E
      (stdVars 1 R)).cechHgr 1).obj d) := by
    haveI : Subsingleton (((((GradedModule.structureModule R 1).twist (-l)).pow r
      ).cechHgr 1).obj d) :=
      GradedModule.subsingleton_cechHgr_free (-l) r 1 (by omega) d (by omega)
    exact (GradedModule.isoApp (GradedModule.cechHgrIso
      (gammaStarPullTwistedFreeIso 1 R (by omega) (-l) r) 1) d
        ).toLinearEquiv.toEquiv.subsingleton
  haveI hKtwo : Subsingleton (((Proj.gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin 2) R) (projSpecπ 1 R) (kernel p)
      (stdVars 1 R)).cechHgr 2).obj d) :=
    GradedModule.subsingleton_cechHgr _ 2 (by omega) d
  let M := Proj.kernelQuotientModule
    (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (projSpecπ 1 R) (stdVars 1 R) p
  haveI hMone : Subsingleton ((M.cechHgr 1).obj d) :=
    GradedModule.subsingleton_of_exact _ _
      (GradedModule.cech_exact_map_δ
        (Proj.shortExact_gammaStar_toCoker_kernel (projSpecπ 1 R) p) 1 d)
  haveI := Proj.isIso_cechHgrMap_kernelQuotientToGammaStar_all
    (projSpecπ 1 R) p 1 d
  exact (asIso ((GradedModule.cechHgrMap
    (Proj.kernelQuotientToGammaStar _ (projSpecπ 1 R) (stdVars 1 R) p) 1).app d)
      ).symm.toLinearEquiv.toEquiv.subsingleton

/-- The preceding quotient vanishing makes the projective-line Koszul recurrence on
zeroth Cech cohomology right exact in every degree at least `l - 1`. -/
theorem lineKoszulG_cechHgr_zero_surjective_gammaStar_twistedFreeQuotient
    (r : ℕ) (R : Type u) [CommRing R] (l d : ℤ) (hd : l - 1 ≤ d)
    (Q : (Scheme.projectiveSpaceOver 1 (Spec (.of R))).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) (-l)) ⟶ Q)
    [Epi q] :
    let G := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso 1 R).inv).obj Q
    Function.Surjective (GradedModule.lineKoszulG
      ((Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin 2) R) (projSpecπ 1 R) G
        (stdVars 1 R)).cechHgr 0) d) := by
  dsimp only
  letI := subsingleton_cechHgr_one_gammaStar_twistedFreeQuotient r R l d hd Q q
  exact GradedModule.lineKoszulG_cechHgr_zero_surjective_of_subsingleton_one _ d

/-- Tail form of the projective-line right-exact recurrence, ready for an induction
starting in degree `D`. -/
theorem lineKoszulG_cechHgr_zero_surjective_gammaStar_twistedFreeQuotient_tail
    (r : ℕ) (R : Type u) [CommRing R] (l D : ℤ) (hD : l - 1 ≤ D)
    (Q : (Scheme.projectiveSpaceOver 1 (Spec (.of R))).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) (-l)) ⟶ Q)
    [Epi q] (t : ℕ) :
    let G := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso 1 R).inv).obj Q
    Function.Surjective (GradedModule.lineKoszulG
      ((Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin 2) R) (projSpecπ 1 R) G
        (stdVars 1 R)).cechHgr 0) (D + t)) := by
  exact lineKoszulG_cechHgr_zero_surjective_gammaStar_twistedFreeQuotient
    r R l (D + t) (by omega) Q q

/-- The right-exact recurrence on Čech `H⁰` transports through the canonical
augmentation, giving the same surjectivity statement on the graded module of twisted
global sections itself. -/
theorem lineKoszulG_gammaStar_twistedFreeQuotient_surjective
    (r : ℕ) (R : Type u) [CommRing R] (l d : ℤ) (hd : l - 1 ≤ d)
    (Q : (Scheme.projectiveSpaceOver 1 (Spec (.of R))).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) (-l)) ⟶ Q)
    [Epi q] :
    let G := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso 1 R).inv).obj Q
    Function.Surjective (GradedModule.lineKoszulG
      (Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin 2) R) (projSpecπ 1 R) G
        (stdVars 1 R)) d) := by
  let G := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso 1 R).inv).obj Q
  haveI hGfp : G.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  apply GradedModule.surjective_lineKoszulG_of_bijective_cechAug
  · exact bijective_gammaStar_cechAug_of_isFinitePresentation
      (projSpecπ 1 R) G (d + 1)
  · exact bijective_gammaStar_cechAug_of_isFinitePresentation
      (projSpecπ 1 R) G ((d + 1) + 1)
  · exact lineKoszulG_cechHgr_zero_surjective_gammaStar_twistedFreeQuotient
      r R l d hd Q q

/-- Tail form of the right-exact recurrence on twisted global sections. -/
theorem lineKoszulG_gammaStar_twistedFreeQuotient_surjective_tail
    (r : ℕ) (R : Type u) [CommRing R] (l D : ℤ) (hD : l - 1 ≤ D)
    (Q : (Scheme.projectiveSpaceOver 1 (Spec (.of R))).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) (-l)) ⟶ Q)
    [Epi q] (t : ℕ) :
    let G := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso 1 R).inv).obj Q
    Function.Surjective (GradedModule.lineKoszulG
      (Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin 2) R) (projSpecπ 1 R) G
        (stdVars 1 R)) (D + t)) := by
  exact lineKoszulG_gammaStar_twistedFreeQuotient_surjective
    r R l (D + t) (by omega) Q q

end AlgebraicGeometry.ProjectiveSpace

end

end
