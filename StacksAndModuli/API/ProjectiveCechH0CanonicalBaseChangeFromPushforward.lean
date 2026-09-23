module

public import StacksAndModuli.API.ProjectiveCechH0FiniteProjectiveSeed
public import StacksAndModuli.API.ProjectiveGradedCechH0FiniteDimensionalBaseChange
public import StacksAndModuli.API.ProjectiveOneStepCanonicalBaseChange
public import StacksAndModuli.API.CanonicalAffineGlobalSectionsBaseChange
public import StacksAndModuli.API.ProjGammaStarBaseChangeObligation

/-!
# Canonical Cech H-zero base change from twisted pushforward base change

For a sheaf on the projective line over an affine base, projective rank of one twisted
pushforward makes the corresponding Cech `H^0` finite projective.  If the canonical
twisted-pushforward base-change morphism to a field is invertible, affine global-sections
base change and the projective Cech comparisons give an arbitrary linear equivalence
between the source and target of the raw Cech `H^0` base-change map.  Their finite
dimensions are therefore equal.  Vanishing of Cech `H^1` makes the raw map surjective,
so equal dimensions make it bijective.

This argument needs no identification of the raw Cech map with the sheaf-level
base-change morphism.

Main declaration:

* `AlgebraicGeometry.ProjectiveSpace.
    cechHgrZeroCanonicalBaseChangeHom_bijective_of_projectiveTwistedPushforward_iso`;
* `AlgebraicGeometry.ProjectiveSpace.
    cechHgrZeroCanonicalBaseChangeHom_bijective_of_projectiveTwistedPushforward`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory TensorProduct
open AlgebraicGeometry ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On the projective line, fixed-rank projectivity and an isomorphism between the pulled
back twisted pushforward and the twisted pushforward after coefficient change make the raw
Cech `H^0` coefficient-change map to a field bijective, provided the first Cech cohomology
in that degree vanishes.  The isomorphism need not be the canonical base-change morphism. -/
theorem
    cechHgrZeroCanonicalBaseChangeHom_bijective_of_projectiveTwistedPushforward_iso
    {R K : Type u} [CommRing R] [Field K] (f : R →+* K)
    (Q : (Scheme.projectiveSpaceOver 1 (Spec (.of R))).Modules)
    [Q.IsQuasicoherent] [Q.IsFinitePresentation] (q d : ℕ)
    (hRank : Scheme.Modules.IsProjectiveOfRank q
      (Scheme.Modules.projectiveTwistedPushforward 1 Q d))
    (e :
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom f))).obj
          (Scheme.Modules.projectiveTwistedPushforward 1 Q d) ≅
        Scheme.Modules.projectiveTwistedPushforward 1
          (Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f) d)
    [Subsingleton
      (((Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin 2) R)
        (projSpecπ 1 R)
        ((Scheme.Modules.pullback
          (projectiveSpaceOverSpecIso 1 R).inv).obj Q)
        (stdVars 1 R)).cechHgr 1).obj (d : ℤ))] :
    letI : Algebra R K := f.toAlgebra
    Function.Bijective
      (GradedModule.cechHgrZeroCanonicalBaseChangeHom
        (A := K)
        (Proj.gammaStar
          (MvPolynomial.homogeneousSubmodule (Fin 2) R)
          (projSpecπ 1 R)
          ((Scheme.Modules.pullback
            (projectiveSpaceOverSpecIso 1 R).inv).obj Q)
          (stdVars 1 R))
        (d : ℤ)) := by
  letI : Algebra R K := f.toAlgebra
  let φ := CommRingCat.ofHom f
  let M := Proj.gammaStar
    (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (projSpecπ 1 R)
    ((Scheme.Modules.pullback
      (projectiveSpaceOverSpecIso 1 R).inv).obj Q)
    (stdVars 1 R)
  let P := Scheme.Modules.projectiveTwistedPushforward 1 Q d
  let QK := Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f
  let PK := Scheme.Modules.projectiveTwistedPushforward 1 QK d
  haveI hQKfp : QK.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  obtain ⟨hfinite, -⟩ :=
    finite_projective_cechHgr_zero_gammaStar_of_projectiveTwistedPushforward_isProjectiveOfRank
      1 q Q d hRank
  letI hfiniteM : Module.Finite R ((M.cechHgr 0).obj (d : ℤ)) := hfinite
  letI : Module R Γ(P, ⊤) :=
    Scheme.Modules.globalSectionsModule (𝟙 (Spec (.of R))) P
  letI : Module K Γ((Scheme.Modules.pullback (Spec.map φ)).obj P, ⊤) :=
    Scheme.Modules.globalSectionsModule (𝟙 (Spec (.of K)))
      ((Scheme.Modules.pullback (Spec.map φ)).obj P)
  letI : Module K Γ(PK, ⊤) :=
    Scheme.Modules.globalSectionsModule (𝟙 (Spec (.of K))) PK
  let eR := cechHgrZeroProjectiveTwistedPushforwardSectionsEquiv 1 Q d
  let eK :=
    (hasGammaStarBaseChangeCechHgrZero_of_isFinitePresentation 1 R Q K f d).some.trans
      (cechHgrZeroProjectiveTwistedPushforwardSectionsEquiv 1 QK d)
  let eSheaf : K ⊗[R] Γ(P, ⊤) ≃ₗ[K] Γ(PK, ⊤) :=
    (specPullbackSectionsBaseChangeLinearEquiv φ P).trans
      (Scheme.Modules.globalSectionsLinearEquivOfIso
        (𝟙 (Spec (.of K))) e)
  let eTotal : K ⊗[R] ((M.cechHgr 0).obj (d : ℤ)) ≃ₗ[K]
      (((M.baseChange K).cechHgr 0).obj (d : ℤ)) :=
    (eR.baseChange R K).trans (eSheaf.trans eK.symm)
  letI : FiniteDimensional K (K ⊗[R] ((M.cechHgr 0).obj (d : ℤ))) := inferInstance
  letI : FiniteDimensional K (((M.baseChange K).cechHgr 0).obj (d : ℤ)) :=
    eTotal.finiteDimensional
  exact
    GradedModule.cechHgrZeroCanonicalBaseChangeHom_bijective_of_subsingleton_one_of_finrank_eq
      (A := K) M (d : ℤ) eTotal.finrank_eq

/-- The preceding criterion applied to the canonical twisted-pushforward base-change
morphism. -/
theorem
    cechHgrZeroCanonicalBaseChangeHom_bijective_of_projectiveTwistedPushforward
    {R K : Type u} [CommRing R] [Field K] (f : R →+* K)
    (Q : (Scheme.projectiveSpaceOver 1 (Spec (.of R))).Modules)
    [Q.IsQuasicoherent] [Q.IsFinitePresentation] (q d : ℕ)
    (hRank : Scheme.Modules.IsProjectiveOfRank q
      (Scheme.Modules.projectiveTwistedPushforward 1 Q d))
    [Subsingleton
      (((Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin 2) R)
        (projSpecπ 1 R)
        ((Scheme.Modules.pullback
          (projectiveSpaceOverSpecIso 1 R).inv).obj Q)
        (stdVars 1 R)).cechHgr 1).obj (d : ℤ))]
    [IsIso (Scheme.Modules.projectiveTwistedPushforwardBaseChangeHom
      1 Q d (Over.mk (Spec.map (CommRingCat.ofHom f))))] :
    letI : Algebra R K := f.toAlgebra
    Function.Bijective
      (GradedModule.cechHgrZeroCanonicalBaseChangeHom
        (A := K)
        (Proj.gammaStar
          (MvPolynomial.homogeneousSubmodule (Fin 2) R)
          (projSpecπ 1 R)
          ((Scheme.Modules.pullback
            (projectiveSpaceOverSpecIso 1 R).inv).obj Q)
          (stdVars 1 R))
        (d : ℤ)) := by
  apply
    cechHgrZeroCanonicalBaseChangeHom_bijective_of_projectiveTwistedPushforward_iso
      f Q q d hRank
  exact asIso (Scheme.Modules.projectiveTwistedPushforwardBaseChangeHom
    1 Q d (Over.mk (Spec.map (CommRingCat.ofHom f))))

end AlgebraicGeometry.ProjectiveSpace

end

end
