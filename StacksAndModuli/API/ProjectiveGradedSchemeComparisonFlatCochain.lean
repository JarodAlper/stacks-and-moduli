module

public import StacksAndModuli.API.ProjectiveGradedRelativeExists
public import StacksAndModuli.API.ProjectiveGradedSchemeComparison
public import StacksAndModuli.API.ProjectiveGradedLocalizationPair

/-!
# The scheme-level transfer, with cochain flatness instead of degreewise flatness

The generic transfer to
`Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange` asks for `Crel.IsFlat M`,
which for the Čech model is flatness of *every* graded piece.  That is
too strong for the graded model of a quotient sheaf: `Γ_*(E) ⧸ Γ_*(K)` is not degreewise flat
over a general noetherian base, only in large degrees.

But Cohomology and Base Change never uses degreewise flatness directly — it uses it *only*
through `flat_cechComplex_X`, i.e. flatness of the Čech cochain groups
`M[1/x_I]_d`.  This file records the transfer with that hypothesis in place of `IsFlat`, using
the primed statements of `API/ProjectiveGradedRelativeCBC.lean`.

On `Proj` the cochain groups are sections on the affine charts `D₊(x_I)`, so they are flat as
soon as the *sheaf* is flat over the base — with no condition on the base beyond noetherian.
`GradedModule.flat_cechCochain_of_flat_loc` reduces that to the single-variable localizations.

Main declaration:

* `AlgebraicGeometry.ProjectiveSpace.`
  `toHasEventualFiniteProjectiveGlobalSectionsBaseChange'`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory TensorProduct
open AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable {M : GradedModule R n}
variable {Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules}

/-- **The transfer to the scheme-level interface, with cochain flatness.** -/
noncomputable def toHasEventualFiniteProjectiveGlobalSectionsBaseChange'
    (E : (RelativeCohomology.cech R).SchemeGlobalSectionsComparison M Q)
    (hM : GradedModule.IsFG M)
    (hflatC : ∀ (d : ℤ) (p : ℕ), Module.Flat R ((M.cechComplex d).X p)) :
    Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q := by
  let d₀ := Classical.choose
    (GradedModule.exists_uniform_subsingleton_cechHgr_baseChange' hM hflatC)
  have hd₀ := Classical.choose_spec
    (GradedModule.exists_uniform_subsingleton_cechHgr_baseChange' hM hflatC)
  refine
    { bound := max d₀.toNat E.bound
      finite := ?_
      projective := ?_
      baseChangeIso := ?_ }
  · intro d hd
    have hd1 : d₀.toNat ≤ d := le_trans (le_max_left _ _) hd
    have hdE : E.bound ≤ d := le_trans (le_max_right _ _) hd
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    haveI : Module.Finite R (((RelativeCohomology.cech R).Hgr M 0).obj (d : ℤ)) :=
      GradedModule.finiteDimensional_cechHgr_of_isFG M hM 0 (d : ℤ)
    exact Module.Finite.equiv (E.globalSectionsIso d hdE)
  · intro d hd
    have hd1 : d₀.toNat ≤ d := le_trans (le_max_left _ _) hd
    have hdE : E.bound ≤ d := le_trans (le_max_right _ _) hd
    have hd' : d₀ ≤ (d : ℤ) := by omega
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    haveI : Module.Projective R (((RelativeCohomology.cech R).Hgr M 0).obj (d : ℤ)) :=
      GradedModule.projective_cechHgr_zero' hM (hflatC (d : ℤ))
        (fun κ _ _ i hi => hd₀ κ i hi (d : ℤ) hd')
    exact Module.Projective.of_equiv (E.globalSectionsIso d hdE)
  · intro K _ f d hd
    have hd1 : d₀.toNat ≤ d := le_trans (le_max_left _ _) hd
    have hdE : E.bound ≤ d := le_trans (le_max_right _ _) hd
    have hd' : d₀ ≤ (d : ℤ) := by omega
    letI : Algebra R K := f.toAlgebra
    let QK := Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q f
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of R)))
      (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
    letI := Scheme.Modules.globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of K)))
      (Scheme.projectiveSpaceOverTwistModule QK (d : ℤ))
    exact
      ((E.globalSectionsIso d hdE).symm.baseChange R K).trans
        ((GradedModule.cechHgrZeroBaseChangeEquiv' hM (hflatC (d : ℤ))
          (fun κ _ _ i hi => hd₀ κ i hi (d : ℤ) hd') K).trans
          (E.fibreGlobalSectionsIso K f d hdE))

end AlgebraicGeometry.ProjectiveSpace

end

end
