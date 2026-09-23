module

public import StacksAndModuli.API.ProjectiveSpaceTwistExact
public import StacksAndModuli.API.SheafCohomologyLES
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Cohomology of twisted quotients on relative projective space

Let `q : M ⟶ Q` be an epimorphism of module sheaves on relative projective space.
Exactness of tensoring by `O(d)` gives the short exact sequence

`0 → (kernel q)(d) → M(d) → Q(d) → 0`.

This file combines that sequence with the cohomology long exact sequence.  It states
the two consequences needed in the DVR argument directly in terms of
`projectiveSpaceOverTwistModule`:

* finite generation of `H⁰(M(d))` and vanishing of `H¹((kernel q)(d))` imply finite
  generation of `H⁰(Q(d))`;
* vanishing of `H¹(M(d))` and `H²((kernel q)(d))` imply vanishing of `H¹(Q(d))`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensoring the canonical kernel sequence of an epimorphism on relative projective
space by `O(d)` gives a short exact sequence. -/
theorem shortExact_kernel_projectiveSpaceOverTwistModule
    (n : ℕ) (S : Scheme.{u})
    {M Q : (Scheme.projectiveSpaceOver n S).Modules}
    (q : M ⟶ Q) [Epi q] (d : ℤ) :
    ((ShortComplex.mk (kernel.ι q) q (kernel.condition q)).map
      (tensorRightFunctor (Scheme.projectiveSpaceOverTwist n S d))).ShortExact := by
  exact Scheme.projectiveSpaceOverTwist_shortExact_tensorRightFunctor n S
    ({ exact := ShortComplex.exact_kernel q } :
      (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact) d

/-- If `H⁰(M(d))` is finite over the base and `H¹((kernel q)(d))` vanishes, then
`H⁰(Q(d))` is finite over the base. -/
theorem finite_globalSections_projectiveSpaceOverTwistModule_of_epi
    {R : CommRingCat.{u}} (n : ℕ) (S : Scheme.{u})
    (p : Scheme.projectiveSpaceOver n S ⟶ Spec R)
    {M Q : (Scheme.projectiveSpaceOver n S).Modules}
    (q : M ⟶ Q) [Epi q] (d : ℤ)
    (hfinite :
      letI := globalSectionsModule p
        (Scheme.projectiveSpaceOverTwistModule M d)
      Module.Finite R
        Γ(Scheme.projectiveSpaceOverTwistModule M d, ⊤))
    (hker₁ : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule (kernel q) d)).H 1)) :
    letI := globalSectionsModule p
      (Scheme.projectiveSpaceOverTwistModule Q d)
    Module.Finite R
      Γ(Scheme.projectiveSpaceOverTwistModule Q d, ⊤) := by
  let C := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  let Cd := C.map
    (tensorRightFunctor (Scheme.projectiveSpaceOverTwist n S d))
  have hCd : Cd.ShortExact :=
    shortExact_kernel_projectiveSpaceOverTwistModule n S q d
  exact finite_globalSections_of_shortExact_of_subsingleton_H_one
    p hCd hfinite hker₁

/-- If `H¹(M(d))` and `H²((kernel q)(d))` vanish, then `H¹(Q(d))` vanishes. -/
theorem subsingleton_H_one_projectiveSpaceOverTwistModule_of_epi
    (n : ℕ) (S : Scheme.{u})
    {M Q : (Scheme.projectiveSpaceOver n S).Modules}
    (q : M ⟶ Q) [Epi q] (d : ℤ)
    (hM₁ : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule M d)).H 1))
    (hker₂ : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule (kernel q) d)).H 2)) :
    Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule Q d)).H 1) := by
  let C := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  let Cd := C.map
    (tensorRightFunctor (Scheme.projectiveSpaceOverTwist n S d))
  have hCd : Cd.ShortExact :=
    shortExact_kernel_projectiveSpaceOverTwistModule n S q d
  exact subsingleton_H_of_shortExact_right hCd rfl hM₁ hker₂

/-- The finite-`H⁰` and `H¹`-vanishing consequences for a twisted quotient,
packaged together. -/
theorem finite_globalSections_and_subsingleton_H_one_projectiveSpaceOverTwistModule_of_epi
    {R : CommRingCat.{u}} (n : ℕ) (S : Scheme.{u})
    (p : Scheme.projectiveSpaceOver n S ⟶ Spec R)
    {M Q : (Scheme.projectiveSpaceOver n S).Modules}
    (q : M ⟶ Q) [Epi q] (d : ℤ)
    (hfinite :
      letI := globalSectionsModule p
        (Scheme.projectiveSpaceOverTwistModule M d)
      Module.Finite R
        Γ(Scheme.projectiveSpaceOverTwistModule M d, ⊤))
    (hM₁ : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule M d)).H 1))
    (hker₁ : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule (kernel q) d)).H 1))
    (hker₂ : Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule (kernel q) d)).H 2)) :
    (letI := globalSectionsModule p
       (Scheme.projectiveSpaceOverTwistModule Q d)
     Module.Finite R
       Γ(Scheme.projectiveSpaceOverTwistModule Q d, ⊤)) ∧
      Subsingleton
        (((SheafOfModules.toSheaf _).obj
          (Scheme.projectiveSpaceOverTwistModule Q d)).H 1) := by
  exact
    ⟨finite_globalSections_projectiveSpaceOverTwistModule_of_epi
        n S p q d hfinite hker₁,
      subsingleton_H_one_projectiveSpaceOverTwistModule_of_epi
        n S q d hM₁ hker₂⟩

/-- Eventual finite generation of `H⁰(M(d))`, together with eventual vanishing of
`H¹(M(d))`, `H¹((kernel q)(d))`, and `H²((kernel q)(d))`, gives the finite-`H⁰`
and `H¹`-vanishing conclusions for `Q(d)` in every sufficiently large degree. -/
theorem eventually_finite_globalSections_and_H_one_of_epi_twist
    {R : CommRingCat.{u}} (n : ℕ) (S : Scheme.{u})
    (p : Scheme.projectiveSpaceOver n S ⟶ Spec R)
    {M Q : (Scheme.projectiveSpaceOver n S).Modules}
    (q : M ⟶ Q) [Epi q]
    (hfinite : ∀ᶠ d : ℕ in Filter.atTop,
      letI := globalSectionsModule p
        (Scheme.projectiveSpaceOverTwistModule M (d : ℤ))
      Module.Finite R
        Γ(Scheme.projectiveSpaceOverTwistModule M (d : ℤ), ⊤))
    (hM₁ : ∀ᶠ d : ℕ in Filter.atTop, Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule M (d : ℤ))).H 1))
    (hker₁ : ∀ᶠ d : ℕ in Filter.atTop, Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule (kernel q) (d : ℤ))).H 1))
    (hker₂ : ∀ᶠ d : ℕ in Filter.atTop, Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (Scheme.projectiveSpaceOverTwistModule (kernel q) (d : ℤ))).H 2)) :
    ∀ᶠ d : ℕ in Filter.atTop,
      (letI := globalSectionsModule p
         (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))
       Module.Finite R
         Γ(Scheme.projectiveSpaceOverTwistModule Q (d : ℤ), ⊤)) ∧
        Subsingleton
          (((SheafOfModules.toSheaf _).obj
            (Scheme.projectiveSpaceOverTwistModule Q (d : ℤ))).H 1) := by
  filter_upwards [hfinite, hM₁, hker₁, hker₂] with d hdfinite hdM₁ hdker₁ hdker₂
  exact
    finite_globalSections_and_subsingleton_H_one_projectiveSpaceOverTwistModule_of_epi
      n S p q (d : ℤ) hdfinite hdM₁ hdker₁ hdker₂

end AlgebraicGeometry.Scheme.Modules

end
