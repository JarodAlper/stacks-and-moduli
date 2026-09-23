module

public import StacksAndModuli.API.ProjGammaStarCechBaseChange
public import StacksAndModuli.API.ProjGammaStarTwistedFreeAmbient
public import StacksAndModuli.API.ProjectiveSpaceOverMapIso

/-!
# The base-change obligation, for every finitely presented sheaf

`AlgebraicGeometry.ProjectiveSpace.HasGammaStarBaseChangeCechHgrZero` is the single named
obligation on which `RelativeCohomology.SchemeGlobalSectionsComparison` rests
(`API/ProjectiveSpaceTwistProjComparison.lean`).  For a twisted-free ambient sheaf it was
discharged without any chart argument, by identifying `Γ_*` with the free graded module
(`hasGammaStarBaseChangeCechHgrZero_of_freeIso`).  Here it is discharged for **every** finitely
presented sheaf on `ℙⁿ_{Spec R}`, so that no hypothesis of that shape has to be carried around
any longer.

The two ingredients are:

* `isIso_cechHgrMap_gammaStarBaseChangeHom_app` — the intrinsic statement on polynomial `Proj`:
  `Γ_*(F) ⊗_R K ⟶ Γ_*(F_K)` is an isomorphism on graded Čech `H⁰` in non-negative degrees;
* `pullbackPolynomialTransportIso` — the transport across the comparison
  `ℙⁿ_{Spec R} ≅ Proj R[x₀,…,xₙ]`, which turns the pullback along `coeffMap` into the pullback
  of the relative base change `Q ↦ Q_K`.

With it, `schemeGlobalSectionsComparison` needs no hypothesis beyond finite presentation:
`schemeGlobalSectionsComparisonOfIsFinitePresentation`.  What still stands between that and
`Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange` is
`RelativeCohomology.IsCoherent` (Serre finiteness for `Γ_*`) and `RelativeCohomology.IsFlat`,
which are properties of the sheaf, not of base change.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.hasGammaStarBaseChangeCechHgrZero_of_isFinitePresentation`;
* `AlgebraicGeometry.ProjectiveSpace.schemeGlobalSectionsComparisonOfIsFinitePresentation`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

open GradedModule

/-- **The base-change obligation holds for every finitely presented sheaf.**  Composing the
intrinsic chart statement on polynomial `Proj` with the transport across
`ℙⁿ_{Spec R} ≅ Proj R[x₀,…,xₙ]`. -/
theorem hasGammaStarBaseChangeCechHgrZero_of_isFinitePresentation
    (n : ℕ) (R : Type u) [CommRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    [Q.IsFinitePresentation] :
    HasGammaStarBaseChangeCechHgrZero n R Q := by
  intro K _ f d
  letI : Algebra R K := f.toAlgebra
  haveI : ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
      Q).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  refine ⟨(cechHgrZeroGammaStarBaseChangeLinearEquiv n f
      ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q) d).trans
    (appIso (cechHgrMapIso (Proj.gammaStarMapIso _ (projSpecπ n K) (stdVars n K)
      (pullbackPolynomialTransportIso n f Q)) 0) (d : ℤ)).toLinearEquiv⟩

/-- **The scheme-level `H⁰` comparison, with no side condition.**  Every finitely presented
sheaf on `ℙⁿ_{Spec R}` over a noetherian ring is computed in every non-negative degree, and on
every field fibre, by the graded Čech model of `Γ_*`. -/
def schemeGlobalSectionsComparisonOfIsFinitePresentation
    (n : ℕ) (R : Type u) [CommRing R] [IsNoetherianRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)
    [Q.IsFinitePresentation] :
    (RelativeCohomology.cech R).SchemeGlobalSectionsComparison
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (projSpecπ n R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
        (stdVars n R)) Q :=
  schemeGlobalSectionsComparison Q
    (hasGammaStarBaseChangeCechHgrZero_of_isFinitePresentation n R Q)

end AlgebraicGeometry.ProjectiveSpace

end

end
