module

public import StacksAndModuli.API.ProjGammaStarQuotientFlat
public import StacksAndModuli.API.ProjGammaStarTwistedFreeAmbient
public import StacksAndModuli.API.SchemeModulesKernelFinitePresentation
public import StacksAndModuli.API.ProjectiveDVRQuotientPullbackSerre

/-!
# The base-change package for a twisted-free presentation

Relative Serre vanishing and Cohomology & Base Change at the scheme level, for a sheaf `Q` on
`ℙⁿ_{Spec R}` presented by a finite twisted-free sheaf:

```lean
hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_twistedFreeEpi
    (n R) [IsNoetherianRing R] (hn : 0 < n) (l r) (Q) [Q.IsQuasicoherent] [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift (Fin r) => 𝒪(-l)) ⟶ Q) [Epi q]
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))) :
    Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q
```

The graded model of `Q` is the kernel-route quotient `Γ_*(𝒪(-l)^{⊕r}) ⧸ Γ_*(K)`
(`API/ProjGammaStarQuotientComparison.lean`).  Its finite generation is
`isFG_gammaStarPullTwistedFree` — **this is where `0 < n` is used**, and it is essential: on
`ℙ⁰`, `Γ_*(𝒪)` is `k` in every degree of `ℤ` and is not a finitely generated graded module.
The flatness input is *not* degreewise flatness of the model (which fails over a general
noetherian base) but flatness of its Čech cochain groups, i.e. of the chart sections of a flat
sheaf — see `hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_flatOver'`.  So the base
needs only to be noetherian.

The instantiation at a Quot datum — and with it the DVR obligation
`Scheme.CanonicalDVRQuotientExtensionsHaveEventualGlobalSectionsBaseChange` — is in
`Section2.4-Projectivity/part2.4.1-valuative-criteria.lean`, which is where that predicate is
defined.

Main declaration:

* `AlgebraicGeometry.ProjectiveSpace.`
  `hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_twistedFreeEpi`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) (R : Type u) [CommRing R] [IsNoetherianRing R] (l : ℤ) (r : ℕ)
variable (Q : (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of R))).Modules)

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsQuasicoherent` binders over an explicit polynomial `Proj` make instance search slow;
-- see the root INSIGHTS.md entry on `(sheafToPresheaf …).IsRightAdjoint`.
/-- **The base-change package for a twisted-free presentation.** -/
def hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_twistedFreeEpi
    (hn : 0 < n)
    [Q.IsQuasicoherent] [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) =>
      Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) (-l)) ⟶ Q) [Epi q]
    (hAmb : (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) (-l)).IsFinitePresentation)
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n (Spec (CommRingCat.of R)))) :
    Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q := by
  haveI := hAmb
  letI EE := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj
    (∐ fun _ : ULift.{u} (Fin r) =>
      Scheme.projectiveSpaceOverTwist n (Spec (CommRingCat.of R)) (-l))
  letI QQ := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q
  letI pp := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).map q
  haveI hE : EE.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hQ : QQ.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hK : (kernel pp).IsFinitePresentation := Scheme.Modules.kernel_isFinitePresentation pp
  haveI : ∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) EE e).IsQuasicoherent :=
    fun e => twistModule_std_isQuasicoherent _ e
  haveI : ∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) QQ e).IsQuasicoherent :=
    fun e => twistModule_std_isQuasicoherent _ e
  haveI : ∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (kernel pp) e).IsQuasicoherent :=
    fun e => twistModule_std_isQuasicoherent _ e
  exact hasEventualFiniteProjectiveGlobalSectionsBaseChange_of_flatOver' n R Q pp
    (isFG_gammaStarPullTwistedFree n R hn (-l) r) hflat

end AlgebraicGeometry.ProjectiveSpace

end

end
