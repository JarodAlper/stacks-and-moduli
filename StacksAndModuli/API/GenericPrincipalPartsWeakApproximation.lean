module

public import StacksAndModuli.API.GenericPrincipalPartsFiniteSupport
public import StacksAndModuli.API.GenericPrincipalPartsStalk

/-!
# Weak approximation for generic principal parts

For an integral scheme, finite local weak approximation means that finitely many
rational functions can be matched modulo the corresponding local rings by one rational
function which is regular away from those points.  This file turns that ring-theoretic
condition into surjectivity onto global sections of the generic principal-parts sheaf.
On a Noetherian scheme of dimension at most one, it therefore implies
`H¹(X, 𝒪_X) = 0`.

## Main results

* `AlgebraicGeometry.Scheme.HasFiniteLocalWeakApproximation`;
* `AlgebraicGeometry.Scheme.mem_range_functionFieldToGenericPrincipalParts_of_finiteSupport`;
* `AlgebraicGeometry.Scheme.subsingleton_H_one_structureModule_of_weakApproximation`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- Finite local weak approximation in the function field of an integral scheme.

The first clause matches each prescribed rational function modulo the local ring at its
chosen point.  The second clause requires the approximating rational function to be
regular at every other point. -/
def HasFiniteLocalWeakApproximation : Prop :=
  ∀ (s : Finset X) (z : s → X.functionField),
    ∃ r : X.functionField,
      (∀ x : s, ∃ a : X.presheaf.stalk x.1,
        algebraMap (X.presheaf.stalk x.1) X.functionField a = z x - r) ∧
      ∀ x : X, x ∉ s → ∃ a : X.presheaf.stalk x,
        algebraMap (X.presheaf.stalk x) X.functionField a = r

/-- Finite local weak approximation represents every finitely supported global generic
principal part by one rational function. -/
theorem mem_range_functionFieldToGenericPrincipalParts_of_finiteSupport
    (happrox : X.HasFiniteLocalWeakApproximation)
    (q : Γ(X.genericPrincipalPartsModule, ⊤))
    (hq : (TopCat.Presheaf.topSectionSupport
      X.genericPrincipalPartsAddSheaf.presheaf q).Finite) :
    q ∈ Set.range X.functionFieldToGenericPrincipalPartsGlobalSections := by
  classical
  let s : Finset X := hq.toFinset
  choose z hz using fun x : s ↦
    X.exists_functionField_germ_principalParts_eq x.1
      (X.genericPrincipalPartsAddSheaf.presheaf.germ ⊤ x.1
        (Set.mem_univ x.1) q)
  obtain ⟨r, hmatch, hregular⟩ := happrox s z
  refine ⟨r, ?_⟩
  apply TopCat.Presheaf.section_ext
    X.genericPrincipalPartsAddSheaf ⊤ _ _
  intro x _
  by_cases hxs : x ∈ s
  · let xs : s := ⟨x, hxs⟩
    obtain ⟨a, ha⟩ := hmatch xs
    have hzero :=
      (X.germ_functionFieldToGenericPrincipalParts_eq_zero_iff x (z xs - r)).mpr
        ⟨a, ha⟩
    have hsub :
        X.genericPrincipalPartsAddSheaf.presheaf.germ ⊤ x
            (Set.mem_univ x)
            (X.functionFieldToGenericPrincipalPartsGlobalSections (z xs) -
              X.functionFieldToGenericPrincipalPartsGlobalSections r) = 0 := by
      rw [← map_sub]
      exact hzero
    rw [map_sub] at hsub
    have hzrx :
        X.genericPrincipalPartsAddSheaf.presheaf.germ ⊤ x
            (Set.mem_univ x)
            (X.functionFieldToGenericPrincipalPartsGlobalSections (z xs)) =
          X.genericPrincipalPartsAddSheaf.presheaf.germ ⊤ x
            (Set.mem_univ x)
            (X.functionFieldToGenericPrincipalPartsGlobalSections r) :=
      sub_eq_zero.mp hsub
    exact hzrx.symm.trans (hz xs)
  · have hxSupport : x ∉ TopCat.Presheaf.topSectionSupport
        X.genericPrincipalPartsAddSheaf.presheaf q := by
      simpa [s] using hxs
    have hqzero :
        X.genericPrincipalPartsAddSheaf.presheaf.germ ⊤ x
          (Set.mem_univ x) q = 0 := by
      simpa [TopCat.Presheaf.topSectionSupport] using hxSupport
    obtain ⟨a, ha⟩ := hregular x hxs
    have hrzero :=
      (X.germ_functionFieldToGenericPrincipalParts_eq_zero_iff x r).mpr
        ⟨a, ha⟩
    exact hrzero.trans hqzero.symm

/-- On an integral Noetherian scheme of dimension at most one, finite local weak
approximation makes the global function-field-to-principal-parts map surjective. -/
theorem surjective_functionFieldToGenericPrincipalParts_of_weakApproximation
    [IsNoetherian X] (hdim : topologicalKrullDim X ≤ 1)
    (happrox : X.HasFiniteLocalWeakApproximation) :
    Function.Surjective
      X.functionFieldToGenericPrincipalPartsGlobalSections :=
  X.surjective_functionFieldToGenericPrincipalParts_of_finiteSupport hdim
    fun q hq ↦
      X.mem_range_functionFieldToGenericPrincipalParts_of_finiteSupport
        happrox q hq

/-- On an integral Noetherian scheme of dimension at most one, finite local weak
approximation implies `H¹(X, 𝒪_X) = 0`. -/
theorem subsingleton_H_one_structureModule_of_weakApproximation
    [IsNoetherian X] (hdim : topologicalKrullDim X ≤ 1)
    (happrox : X.HasFiniteLocalWeakApproximation) :
    Subsingleton (Modules.H (structureModule X) 1) :=
  X.subsingleton_H_one_structureModule_of_surjective_genericPrincipalParts
    (X.surjective_functionFieldToGenericPrincipalParts_of_weakApproximation
      hdim happrox)

end AlgebraicGeometry.Scheme
