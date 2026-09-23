module

public import StacksAndModuli.API.TwistedFreeMonomialSpan
public import StacksAndModuli.API.PushforwardProjectiveRank

/-!
# Rank of the twisted-free ambient pushforward

For a natural twist `d` with `d - l = e`, the pushforward of
`O(-l)^{\oplus r}(d)` from relative projective space is finite locally free of rank
`r * choose (n + e) n`.  The proof is affine-local.  On an affine base the existing
homogeneous-sections equivalence identifies its global sections with `r` copies of the
degree-`e` homogeneous polynomials, and on an arbitrary base the standard projective-space
restriction comparison transports this calculation to every affine open.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
-- The explicit polynomial `Proj` twists make the homogeneous-basis instances expensive.
/-- Over an affine base, the global sections of a twisted-free ambient sheaf in normalized
degree `e` are finite projective of rank `r * choose (n + e) n`. -/
theorem twistedFreeTwistGlobalSections_finite_projective_rank
    (n : ℕ) (R : Type u) [CommRing R] (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) :
    let A := Scheme.projectiveSpaceOverTwistModule
      (∐ fun _ : ULift.{u} (Fin r) ↦
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) (d : ℤ)
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R))) A
    Module.Finite R Γ(A, ⊤) ∧
      Module.Projective R Γ(A, ⊤) ∧
      ∀ p : PrimeSpectrum R,
        Module.rankAtStalk Γ(A, ⊤) p = r * (n + e).choose n := by
  let A := Scheme.projectiveSpaceOverTwistModule
    (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) (d : ℤ)
  letI : Module R Γ(A, ⊤) := Scheme.Modules.globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (.of R))) A
  let H := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R e
  let E := twistedFreeTwistGlobalSectionsHomogeneousEquiv
    (J := ULift.{u} (Fin r)) n R l d e he.symm
  let E' : Γ(A, ⊤) ≃ₗ[R]
      (ULift.{u} (Fin r) → H) := E
  let bH := MvPolynomial.homogeneousSubmoduleFinBasis n R e
  let b := Pi.basis (fun _ : ULift.{u} (Fin r) ↦ bH)
  letI : Module.Free R (ULift.{u} (Fin r) → H) := Module.Free.of_basis b
  letI : Module.Finite R (ULift.{u} (Fin r) → H) := Module.Finite.of_basis b
  have hfin : Module.Finite R Γ(A, ⊤) := Module.Finite.equiv E'.symm
  have hproj : Module.Projective R Γ(A, ⊤) :=
    Module.Projective.of_equiv' E'.symm
  refine ⟨hfin, hproj, fun p ↦ ?_⟩
  let _ := p.nontrivial
  calc
    Module.rankAtStalk Γ(A, ⊤) p =
        Module.rankAtStalk (ULift.{u} (Fin r) → H) p :=
      congrFun (Module.rankAtStalk_eq_of_equiv E') p
    _ = Module.finrank R (ULift.{u} (Fin r) → H) :=
      congrFun (Module.rankAtStalk_eq_finrank_of_free
        (R := R) (M := ULift.{u} (Fin r) → H)) p
    _ = r * (n + e).choose n := by
      rw [Module.finrank_eq_card_basis b]
      simp only [Fintype.card_sigma, Fintype.card_ulift, Fintype.card_fin,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rfl

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Restricting a twist to the spectrum of an affine base open agrees with
twisting after the single composite pullback.  This low-dependency copy keeps
the ambient rank theorem independent of fixed-polynomial Quot cohomology. -/
noncomputable def projectiveSpaceRestrictSpecTwistIso_for_ambientRank
    (n : ℕ) {T : Scheme.{u}} (U : T.affineOpens)
    (Q : (projectiveSpaceOver n T).Modules) (d : ℤ) :
    projectiveSpaceRestrictSpec n U (projectiveSpaceOverTwistModule Q d) ≅
      projectiveSpaceOverTwistModule
        ((Modules.pullback (projectiveSpaceOverMap n
          (U.1.toScheme.isoSpec.inv ≫ U.1.ι))).obj Q) d := by
  letI : IsAffine U.1.toScheme := U.2
  let j := projectiveSpaceOverMap n U.1.ι
  let e := projectiveSpaceOverMap n U.1.toScheme.isoSpec.inv
  let g := U.1.toScheme.isoSpec.inv ≫ U.1.ι
  haveI : IsOpenImmersion j := inferInstance
  haveI : IsOpenImmersion e := inferInstance
  haveI : IsOpenImmersion g := inferInstance
  exact (Modules.restrictFunctorIsoPullback e).app
      ((Modules.restrictFunctor j).obj (projectiveSpaceOverTwistModule Q d)) ≪≫
    (Modules.pullback e).mapIso ((Modules.restrictFunctorIsoPullback j).app _) ≪≫
    (Modules.pullbackComp e j).app _ ≪≫
    (Modules.pullbackCongr
      (projectiveSpaceOverMap_comp n U.1.toScheme.isoSpec.inv U.1.ι)).app _ ≪≫
    projectiveSpaceOverTwistModule_pullbackIso_of_isOpenImmersion n g Q d

set_option synthInstance.maxHeartbeats 1000000 in
-- The affine-open restriction comparison creates many nested pullback instances.
set_option maxHeartbeats 2000000 in
-- Assembling the local rank calculation elaborates the full projective-space comparison.
/-- The pushforward of the normalized natural twist of a twisted-free ambient sheaf is
finite locally free of the monomial rank on every base scheme. -/
theorem twistedFreeTwistPushforward_isProjectiveOfRank
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) :
    Modules.IsProjectiveOfRank (r * (n + e).choose n)
      ((Modules.pushforward (projectiveSpaceOverπ n T)).obj
        (projectiveSpaceOverTwistModule
          (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l))
          (d : ℤ))) := by
  let F := ∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)
  let Fd := projectiveSpaceOverTwistModule F (d : ℤ)
  have hlocal : ∀ U : T.affineOpens,
      letI := Modules.globalSectionsModule
        (projectiveSpaceOverπ n (Spec Γ(U.1.toScheme, ⊤)))
        (projectiveSpaceRestrictSpec n U Fd)
      Module.Finite Γ(U.1.toScheme, ⊤)
          Γ(projectiveSpaceRestrictSpec n U Fd, ⊤) ∧
        Module.Projective Γ(U.1.toScheme, ⊤)
          Γ(projectiveSpaceRestrictSpec n U Fd, ⊤) ∧
        ∀ p : PrimeSpectrum Γ(U.1.toScheme, ⊤),
          Module.rankAtStalk Γ(projectiveSpaceRestrictSpec n U Fd, ⊤) p =
            r * (n + e).choose n := by
    intro U
    haveI : IsAffine U.1.toScheme := U.2
    let R := Γ(U.1.toScheme, ⊤)
    let g : Spec (CommRingCat.of R) ⟶ T := U.1.toScheme.isoSpec.inv ≫ U.1.ι
    let FU := (Modules.pullback (projectiveSpaceOverMap n g)).obj F
    let FUd := projectiveSpaceOverTwistModule FU (d : ℤ)
    let Fstd := ∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) (-l)
    let Fstdd := projectiveSpaceOverTwistModule Fstd (d : ℤ)
    let eF : FU ≅ Fstd := projectiveSpaceOverTwistedFree_pullbackIso n r l g
    let eTw : FUd ≅ Fstdd := Modules.tensorLeftIso eF
      (projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) (d : ℤ))
    let eQ : projectiveSpaceRestrictSpec n U Fd ≅ Fstdd :=
      projectiveSpaceRestrictSpecTwistIso_for_ambientRank n U F (d : ℤ) ≪≫ eTw
    letI := Modules.globalSectionsModule
      (projectiveSpaceOverπ n (Spec (CommRingCat.of R)))
      (projectiveSpaceRestrictSpec n U Fd)
    letI := Modules.globalSectionsModule
      (projectiveSpaceOverπ n (Spec (CommRingCat.of R))) Fstdd
    let eΓ := Modules.globalSectionsLinearEquivOfIso
      (projectiveSpaceOverπ n (Spec (CommRingCat.of R))) eQ
    obtain ⟨hfin, hproj, hrank⟩ :=
      ProjectiveSpace.twistedFreeTwistGlobalSections_finite_projective_rank
        n R l r d e he
    letI : Module.Finite R Γ(Fstdd, ⊤) := hfin
    letI : Module.Projective R Γ(Fstdd, ⊤) := hproj
    exact ⟨Module.Finite.equiv eΓ.symm, Module.Projective.of_equiv' eΓ.symm,
      fun p ↦ (congrFun (Module.rankAtStalk_eq_of_equiv eΓ) p).trans (hrank p)⟩
  exact isProjectiveOfRank_pushforward_of_globalSections n Fd
    (r * (n + e).choose n) (fun U ↦ (hlocal U).1)
      (fun U ↦ (hlocal U).2.1) (fun U ↦ (hlocal U).2.2)

end AlgebraicGeometry.Scheme

end

end
