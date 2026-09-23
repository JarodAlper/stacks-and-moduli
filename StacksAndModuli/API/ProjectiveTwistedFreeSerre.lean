module

public import StacksAndModuli.API.ProjectiveSpaceSerreVanishing
public import StacksAndModuli.API.ProjectiveTwistedFreeCohomology
public import StacksAndModuli.API.ProjectiveTwistedFreeGlobalSectionsFinite
public import StacksAndModuli.API.ProjectiveTwistedFreePresentation
public import StacksAndModuli.API.SchemeModulesKernelFinitePresentation

/-!
# Serre consequences for twisted-free quotients

This file combines the concrete finite-global-sections computation for a finite
twisted-free sheaf with scheme-level Serre vanishing and the cohomology long exact
sequence of a quotient.

For an epimorphism `O(-l)⁽ᴶ⁾ ⟶ Q`, finite `H⁰(Q(d))` and vanishing `H¹(Q(d))`
are automatic for all sufficiently large natural `d`, provided the fixed kernel is
finitely presented and quasicoherent and projective space satisfies scheme-level
Serre vanishing.  Over a Noetherian affine base, the second endpoint derives the
kernel properties automatically.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A twisted-free quotient has finite global sections and vanishing first
cohomology after every sufficiently positive twist, assuming scheme-level Serre
vanishing for the fixed presentation kernel. -/
theorem eventually_finite_globalSections_and_H_one_of_twistedFree_epi_of_serre
    {J : Type u} [Finite J] (n : ℕ) (R : CommRingCat.{u}) (l : ℤ)
    {Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules}
    (q : (∐ fun _ : J ↦
      Scheme.projectiveSpaceOverTwist n (Spec R) (-l)) ⟶ Q)
    [Epi q]
    (hkerqc : (kernel q).IsQuasicoherent)
    (hkerfp : (kernel q).IsFinitePresentation)
    (hserre : Scheme.ProjectiveSpaceHasSerreVanishing n (Spec R)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      (letI := globalSectionsModule
         (Scheme.projectiveSpaceOverπ n (Spec R))
         (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
       Module.Finite R
         Γ(Scheme.projectiveSpaceOverTwistModule Q (d : ℤ), ⊤)) ∧
        Subsingleton
          (((SheafOfModules.toSheaf _).obj
            (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).H 1) := by
  have hfinite :=
    Scheme.eventually_projectiveSpaceOverNegativeTwist_coproduct_twist_globalSections_finite
      (J := J) n R l
  have hO₁ :=
    hserre.eventually_subsingleton_H_projectiveSpaceOverTwist_sub l 1 (by omega)
  have hM₁ :=
    eventually_subsingleton_H_projectiveSpaceOverNegativeTwist_coproduct_twist
      (J := J) n (Spec R) l 1 hO₁
  have hker₁ := hserre.eventually_subsingleton_H
    (kernel q) hkerqc hkerfp 1 (by omega)
  have hker₂ := hserre.eventually_subsingleton_H
    (kernel q) hkerqc hkerfp 2 (by omega)
  exact eventually_finite_globalSections_and_H_one_of_epi_twist
    n (Spec R) (Scheme.projectiveSpaceOverπ n (Spec R)) q
      hfinite hM₁ hker₁ hker₂

/-- Over a Noetherian affine base, scheme-level Serre vanishing makes finite
global sections and first-cohomology vanishing automatic for a twisted-free
quotient: the presentation kernel is automatically quasicoherent and finitely
presented. -/
theorem eventually_finite_globalSections_and_H_one_of_twistedFree_epi_of_serre_of_noetherian
    {J : Type u} [Finite J] (n : ℕ) (R : CommRingCat.{u}) [IsNoetherianRing R]
    (l : ℤ)
    {Q : (Scheme.projectiveSpaceOver n (Spec R)).Modules}
    (q : (∐ fun _ : J ↦
      Scheme.projectiveSpaceOverTwist n (Spec R) (-l)) ⟶ Q)
    [Epi q] [Q.IsQuasicoherent]
    (hserre : Scheme.ProjectiveSpaceHasSerreVanishing n (Spec R)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      (letI := globalSectionsModule
         (Scheme.projectiveSpaceOverπ n (Spec R))
         (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
       Module.Finite R
         Γ(Scheme.projectiveSpaceOverTwistModule Q (d : ℤ), ⊤)) ∧
        Subsingleton
          (((SheafOfModules.toSheaf _).obj
            (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).H 1) := by
  letI : IsLocallyNoetherian (Scheme.projectiveSpaceOver n (Spec R)) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Scheme.projectiveSpaceOverπ n (Spec R))
  have hsourceqc : (∐ fun _ : J ↦
      Scheme.projectiveSpaceOverTwist n (Spec R) (-l)).IsQuasicoherent :=
    projectiveSpaceOverTwistCoproduct_isQuasicoherent
      J n (Spec R) (-l)
  letI : (∐ fun _ : J ↦
      Scheme.projectiveSpaceOverTwist n (Spec R) (-l)).IsQuasicoherent :=
    hsourceqc
  have hsourcefp : (∐ fun _ : J ↦
      Scheme.projectiveSpaceOverTwist n (Spec R) (-l)).IsFinitePresentation :=
    projectiveSpaceOverTwistCoproduct_isFinitePresentation
      J n (Spec R) (-l)
  letI : (∐ fun _ : J ↦
      Scheme.projectiveSpaceOverTwist n (Spec R) (-l)).IsFinitePresentation :=
    hsourcefp
  have hkerqc : (kernel q).IsQuasicoherent := kernel_isQuasicoherent q
  letI : (kernel q).IsQuasicoherent := hkerqc
  have hkerfp : (kernel q).IsFinitePresentation :=
    kernel_isFinitePresentation q
  exact eventually_finite_globalSections_and_H_one_of_twistedFree_epi_of_serre
    n R l q hkerqc hkerfp hserre

end AlgebraicGeometry.Scheme.Modules

end
