module

public import StacksAndModuli.API.ProjectiveCanonicalGlobalSectionsBaseChange
public import StacksAndModuli.API.ProjectiveSpaceZeroGlobalSectionsRank
public import StacksAndModuli.API.ProjectiveTwistedVanishingModel

/-!
# Canonical global-sections base change on polynomial projective zero-space

Polynomial `Proj` in one variable is isomorphic to the affine base.  Consequently every
flat finitely presented quasicoherent module on it has finite projective global sections,
and the literal scalar-extension comparison is bijective after arbitrary coefficient
change.  Since every twist on projective zero-space is trivial, these packages are
available in every degree with bound zero.

The eventual package is the zero-dimensional input to the universal finite-free
vanishing models used in the projectivity proof for general Quot schemes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

/-- Twisting preserves relative flatness on intrinsic polynomial projective zero-space.
This is transported from the relative-projective statement through the affine
polynomial-`Proj` comparison. -/
theorem twistModule_flatOver_zero
    (R : Type u) [CommRing R]
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin 1) R)).Modules)
    [F.IsQuasicoherent]
    (hflat : F.FlatOver (Proj.polynomialToSpec (Fin 1) R)) (d : ℤ) :
    (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin 1) R) F d).FlatOver
        (Proj.polynomialToSpec (Fin 1) R) := by
  let X := Proj (MvPolynomial.homogeneousSubmodule (Fin 1) R)
  let Xrel := Scheme.projectiveSpaceOver 0 (Spec (.of R))
  let p : X ⟶ Spec (.of R) := Proj.polynomialToSpec (Fin 1) R
  let prel : Xrel ⟶ Spec (.of R) :=
    Scheme.projectiveSpaceOverπ 0 (Spec (.of R))
  let e : Xrel ≅ X := ProjectiveSpace.projectiveSpaceOverSpecIso 0 R
  let Q := (Scheme.Modules.pullback e.hom).obj F
  have he : e.hom ≫ p = prel := by
    apply (cancel_epi e.inv).1
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
    exact ProjectiveSpace.projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ 0 R
      |>.symm
  have hQ : Q.FlatOver prel :=
    Scheme.Modules.FlatOver.pullback_isIso e.hom F he hflat
  have hQd : (Scheme.projectiveSpaceOverTwistModule Q d).FlatOver prel :=
    hQ.projectiveSpaceOverTwistModule 0 (Spec (.of R)) Q d
  have hback :
      ((Scheme.Modules.pullback e.inv).obj
        (Scheme.projectiveSpaceOverTwistModule Q d)).FlatOver p :=
    Scheme.Modules.FlatOver.pullback_isIso e.inv
      (Scheme.projectiveSpaceOverTwistModule Q d)
      (ProjectiveSpace.projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ 0 R)
      hQd
  let eQ : (Scheme.Modules.pullback e.inv).obj Q ≅ F :=
    (Scheme.Modules.pullbackComp e.inv e.hom).app F ≪≫
      (Scheme.Modules.pullbackCongr e.inv_hom_id).app F ≪≫
      (Scheme.Modules.pullbackId X).app F
  let eTw :
      (Scheme.Modules.pullback e.inv).obj
          (Scheme.projectiveSpaceOverTwistModule Q d) ≅
        ProjectiveSpectrum.Twist.twistModule
          (MvPolynomial.homogeneousSubmodule (Fin 1) R) F d :=
    ProjectiveSpace.projectiveSpaceOverTwistModulePullbackIso Q d ≪≫
      Scheme.Modules.tensorLeftIso eQ
        (ProjectiveSpectrum.Twist.twist
          (MvPolynomial.homogeneousSubmodule (Fin 1) R) d)
  exact Scheme.Modules.FlatOver.of_iso eTw hback

/-- On polynomial projective zero-space, a flat finitely presented quasicoherent module
has finite projective global sections and its canonical global-sections comparison is
bijective after every affine base change. -/
noncomputable def hasFiniteProjectiveGlobalSectionsBaseChange_zero
    (R : Type u) [CommRing R]
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin 1) R)).Modules)
    [F.IsQuasicoherent] (hfp : F.IsFinitePresentation)
    (hflat : F.FlatOver (Proj.polynomialToSpec (Fin 1) R)) :
    Scheme.Modules.HasFiniteProjectiveGlobalSectionsBaseChange
      (Proj.polynomialToSpec (Fin 1) R) F := by
  let X := Proj (MvPolynomial.homogeneousSubmodule (Fin 1) R)
  let p : X ⟶ Spec (.of R) := Proj.polynomialToSpec (Fin 1) R
  letI hp : IsIso p := by
    haveI : IsIso
        (Scheme.projectiveSpaceOverπ 0 (Spec (CommRingCat.of R))) := by
      rw [← Scheme.projectiveSpaceOverZeroIso_hom]
      infer_instance
    dsimp only [p, X]
    rw [← ProjectiveSpace.projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ 0 R]
    infer_instance
  let e : X ≅ Spec (.of R) := asIso p
  let N := (Scheme.Modules.pullback e.inv).obj F
  haveI hNqc : N.IsQuasicoherent := by
    dsimp only [N]
    infer_instance
  have hNfp : N.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation e.inv hfp
  have hNflat : N.FlatOver (𝟙 (Spec (.of R))) :=
    Scheme.Modules.FlatOver.pullback_isIso e.inv F e.inv_hom_id hflat
  have hNloc : Scheme.Modules.IsFiniteLocallyFree N :=
    Scheme.Modules.isFiniteLocallyFree_of_isFinitePresentation_flatOver_id N hNfp hNflat
  have hcoord :=
    Scheme.Modules.moduleSpecΓFunctor_finite_projective_of_isFiniteLocallyFree N hNloc
  have hcomp : e.inv ≫ p = 𝟙 (Spec (.of R)) := e.inv_hom_id
  have hNfin :
      letI := Scheme.Modules.globalSectionsModule (e.inv ≫ p) N
      Module.Finite R Γ(N, ⊤) := by
    rw [hcomp]
    change Module.Finite R
      ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj N)
    exact hcoord.1
  have hNproj :
      letI := Scheme.Modules.globalSectionsModule (e.inv ≫ p) N
      Module.Projective R Γ(N, ⊤) := by
    rw [hcomp]
    change Module.Projective R
      ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj N)
    exact hcoord.2
  letI : Module R Γ(F, ⊤) := Scheme.Modules.globalSectionsModule p F
  letI : Module R Γ(N, ⊤) := Scheme.Modules.globalSectionsModule (e.inv ≫ p) N
  letI : Module.Finite R Γ(N, ⊤) := hNfin
  letI : Module.Projective R Γ(N, ⊤) := hNproj
  let eΓ := Scheme.Modules.pullbackGlobalSectionsViaIsoLinearEquiv
    e.inv p F (Iso.refl N)
  refine {
    finite := Module.Finite.equiv eΓ.symm
    projective := Module.Projective.of_equiv' eΓ.symm
    baseChange_bijective := ?_ }
  intro A _ f
  let φ : CommRingCat.of R ⟶ CommRingCat.of A := CommRingCat.ofHom f
  let Y := Limits.pullback (Spec.map φ) p
  let g : Y ⟶ X := Limits.pullback.snd (Spec.map φ) p
  let pY : Y ⟶ Spec (.of A) := Limits.pullback.fst (Spec.map φ) p
  letI : IsAffine X := IsAffine.of_isIso p
  have hpb : IsPullback pY g (Spec.map φ) p :=
    IsPullback.of_hasPullback (Spec.map φ) p
  letI : IsIso pY := hpb.isIso_fst_of_isIso
  letI : IsAffine Y := IsAffine.of_isIso pY
  exact Scheme.Modules.pullbackGlobalSectionsBaseChangeLinearMap_bijective_of_isPullback
    φ g p pY hpb.flip F

/-- Every nonnegative twist of a flat finitely presented quasicoherent module on
polynomial projective zero-space has the canonical finite-projective base-change
package; the uniform bound is zero. -/
noncomputable def
    hasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange_zero
    (R : Type u) [CommRing R]
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin 1) R)).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (hflat : F.FlatOver (Proj.polynomialToSpec (Fin 1) R)) :
    HasEventualFiniteProjectiveCanonicalGlobalSectionsBaseChange F := by
  refine { bound := 0, fixedDegree := ?_ }
  intro d _
  let Fd := ProjectiveSpectrum.Twist.twistModule
    (MvPolynomial.homogeneousSubmodule (Fin 1) R) F (d : ℤ)
  letI : Fd.IsQuasicoherent :=
    ProjectiveSpace.twistModule_std_isQuasicoherent_of_isQuasicoherent 0 F (d : ℤ)
  have hFdfp : Fd.IsFinitePresentation :=
    ProjectiveSpectrum.Twist.twistModule_isFinitePresentation
      (MvPolynomial.homogeneousSubmodule (Fin 1) R)
      (fun k : ULift.{u} (Fin 1) ↦
        (MvPolynomial.X k.down : MvPolynomial (Fin 1) R))
      (fun k ↦ MvPolynomial.X_mem_homogeneousSubmodule_one 0 R k.down)
      (by rw [iSup_ulift]; exact ProjectiveSpace.iSup_basicOpen_X_eq_top R 0)
      F (d : ℤ)
  exact hasFiniteProjectiveGlobalSectionsBaseChange_zero R Fd hFdfp
    (twistModule_flatOver_zero R F hflat (d : ℤ))

end AlgebraicGeometry.Proj

end
