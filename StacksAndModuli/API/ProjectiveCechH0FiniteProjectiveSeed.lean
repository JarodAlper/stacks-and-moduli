module

public import StacksAndModuli.API.ProjectiveFlatteningFiniteDegree
public import StacksAndModuli.API.ProjectiveSpaceTwistProjComparison
public import StacksAndModuli.API.QuasicoherentVectorBundles
public import StacksAndModuli.API.SheafCohomologyPushforwardZero

/-!
# Finite-projective affine seeds from twisted pushforward rank

On an affine base, projective rank of a twisted pushforward makes its coordinate module
finite projective.  Global sections commute with that pushforward, while the standard
projective-space comparison identifies those sections with degree-zero graded Cech
cohomology of gamma-star.  Composing the two comparisons transfers finite projectivity to
the graded Cech term.

This is the affine initial-degree input for the projective-line two-step Koszul recurrence.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The degree-`d` Cech `H^0` of gamma-star is canonically the top sections of the
corresponding twisted pushforward on the affine base. -/
noncomputable def cechHgrZeroProjectiveTwistedPushforwardSectionsEquiv
    {R : Type u} [CommRing R] (n : ℕ)
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
    [Q.IsFinitePresentation] (d : ℕ) :
    letI := Scheme.Modules.globalSectionsModule
      (𝟙 (Spec (.of R)))
      (Scheme.Modules.projectiveTwistedPushforward n Q d)
    (((Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R)
        ((Scheme.Modules.pullback
          (projectiveSpaceOverSpecIso n R).inv).obj Q)
        (stdVars n R)).cechHgr 0).obj (d : ℤ)) ≃ₗ[R]
      Γ(Scheme.Modules.projectiveTwistedPushforward n Q d, ⊤) := by
  let π := Scheme.projectiveSpaceOverπ n (Spec (.of R))
  let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
  let P := Scheme.Modules.projectiveTwistedPushforward n Q d
  letI : Module R Γ(P, ⊤) :=
    Scheme.Modules.globalSectionsModule (𝟙 (Spec (.of R))) P
  letI : Module R Γ(Qd, ⊤) :=
    Scheme.Modules.globalSectionsModule π Qd
  exact (cechHgrZeroGlobalSectionsEquiv Q (d : ℤ)).trans
    (Scheme.Modules.pushforwardGlobalSectionsLinearEquiv
      π π (𝟙 (Spec (.of R))) (by simp) Qd).symm

/-- Projective rank of the twisted pushforward makes its top sections over the affine base
a finite projective module over the coefficient ring. -/
theorem finite_projective_top_projectiveTwistedPushforward_of_isProjectiveOfRank
    {R : Type u} [CommRing R] (n q : ℕ)
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
    [Q.IsQuasicoherent] (d : ℕ)
    (h : Scheme.Modules.IsProjectiveOfRank q
      (Scheme.Modules.projectiveTwistedPushforward n Q d)) :
    letI := Scheme.Modules.globalSectionsModule
      (𝟙 (Spec (.of R)))
      (Scheme.Modules.projectiveTwistedPushforward n Q d)
    Module.Finite R
        Γ(Scheme.Modules.projectiveTwistedPushforward n Q d, ⊤) ∧
      Module.Projective R
        Γ(Scheme.Modules.projectiveTwistedPushforward n Q d, ⊤) := by
  let P := Scheme.Modules.projectiveTwistedPushforward n Q d
  haveI hPqc : P.IsQuasicoherent := by
    dsimp only [P]
    infer_instance
  have hcoord :=
    Scheme.Modules.moduleSpecΓFunctor_finite_projective_of_isFiniteLocallyFree
      P h.isFiniteLocallyFree
  letI : Module R Γ(P, ⊤) :=
    Scheme.Modules.globalSectionsModule (𝟙 (Spec (.of R))) P
  constructor
  · change Module.Finite R
      ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj P)
    exact hcoord.1
  · change Module.Projective R
      ((moduleSpecΓFunctor (R := CommRingCat.of R)).obj P)
    exact hcoord.2

/-- Projective rank of the degree-`d` twisted pushforward supplies the finite-projective
affine seed for the degree-`d` Cech `H^0` of gamma-star. -/
theorem
    finite_projective_cechHgr_zero_gammaStar_of_projectiveTwistedPushforward_isProjectiveOfRank
    {R : Type u} [CommRing R] (n q : ℕ)
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
    [Q.IsQuasicoherent] [Q.IsFinitePresentation] (d : ℕ)
    (h : Scheme.Modules.IsProjectiveOfRank q
      (Scheme.Modules.projectiveTwistedPushforward n Q d)) :
    Module.Finite R
        (((Proj.gammaStar
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (projSpecπ n R)
          ((Scheme.Modules.pullback
            (projectiveSpaceOverSpecIso n R).inv).obj Q)
          (stdVars n R)).cechHgr 0).obj (d : ℤ)) ∧
      Module.Projective R
        (((Proj.gammaStar
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (projSpecπ n R)
          ((Scheme.Modules.pullback
            (projectiveSpaceOverSpecIso n R).inv).obj Q)
          (stdVars n R)).cechHgr 0).obj (d : ℤ)) := by
  let π := Scheme.projectiveSpaceOverπ n (Spec (.of R))
  let Qd := Scheme.projectiveSpaceOverTwistModule Q (d : ℤ)
  let P := Scheme.Modules.projectiveTwistedPushforward n Q d
  letI : Module R Γ(P, ⊤) :=
    Scheme.Modules.globalSectionsModule (𝟙 (Spec (.of R))) P
  letI : Module R Γ(Qd, ⊤) :=
    Scheme.Modules.globalSectionsModule π Qd
  obtain ⟨hPfin, hPproj⟩ :=
    finite_projective_top_projectiveTwistedPushforward_of_isProjectiveOfRank
      n q Q d h
  let e := cechHgrZeroProjectiveTwistedPushforwardSectionsEquiv n Q d
  letI : Module.Finite R Γ(P, ⊤) := hPfin
  letI : Module.Projective R Γ(P, ⊤) := hPproj
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩

end AlgebraicGeometry.ProjectiveSpace

end

end
