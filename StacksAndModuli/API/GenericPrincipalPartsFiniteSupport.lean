module

public import StacksAndModuli.API.GenericFunctionFieldLocalSections
public import StacksAndModuli.API.SheafOfModulesColimits
public import StacksAndModuli.API.SheafSectionSupport

/-!
# Finite support for generic principal parts on curves

Let `X` be an integral Noetherian scheme of topological dimension at most one.  Every
global section of the generic principal-parts sheaf can be modified by one rational
function so that its germ support is finite.  Indeed, the quotient map from rational
functions to principal parts is locally surjective.  A lift near the generic point
extends uniquely to a global rational function, and subtracting it kills the germ at
the generic point.  The remaining support is closed, avoids the dense generic point,
and is therefore finite.

This reduces global weak approximation, and hence vanishing of `H¹(X, 𝒪_X)`, to
the corresponding approximation statement for finitely supported principal parts.

## Main results

* `AlgebraicGeometry.Scheme.exists_functionField_sub_with_finite_principalPartsSupport`:
  a principal part becomes finitely supported after subtracting a rational function.
* `AlgebraicGeometry.Scheme.surjective_functionFieldToGenericPrincipalParts_of_finiteSupport`:
  approximation for finitely supported principal parts implies global approximation.
* `subsingleton_H_one_structureModule_of_finiteSupport_genericPrincipalParts`:
  the same finite-support input implies `H¹(X, 𝒪_X) = 0`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- On an integral Noetherian scheme of topological dimension at most one, every
global generic principal part differs from one rational function by a section with
finite germ support. -/
theorem exists_functionField_sub_with_finite_principalPartsSupport
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (q : Γ(X.genericPrincipalPartsModule, ⊤)) :
    ∃ r : X.functionField,
      (TopCat.Presheaf.topSectionSupport
        X.genericPrincipalPartsAddSheaf.presheaf
        (q - X.functionFieldToGenericPrincipalPartsGlobalSections r)).Finite := by
  have hloc : TopCat.Presheaf.IsLocallySurjective
      X.genericPrincipalPartsProjectionAdd.hom := by
    have hprojection : Epi X.genericPrincipalPartsProjection := by
      dsimp [genericPrincipalPartsProjection]
      infer_instance
    let _ : Epi X.genericPrincipalPartsProjectionAdd :=
      @Functor.map_epi _ _ _ _
        (SheafOfModules.toSheaf X.ringCatSheaf) _ _ _
          X.genericPrincipalPartsProjection hprojection
    exact (TopCat.Sheaf.isLocallySurjective_iff_epi
      X.genericPrincipalPartsProjectionAdd).mpr inferInstance
  obtain ⟨U, hUtop, ⟨s, hs⟩, hηU⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff
      X.genericPrincipalPartsProjectionAdd.hom).mp hloc
      ⊤ q (genericPoint X) (Set.mem_univ _)
  let sTop : Γ(X.genericFunctionFieldModule, ⊤) :=
    (X.genericFunctionFieldRestrictTopAddEquiv U hηU).symm s
  let r : X.functionField :=
    X.genericFunctionFieldGlobalSectionsAddEquiv sTop
  refine ⟨r, ?_⟩
  apply TopCat.Presheaf.finite_topSectionSupport_of_dense_singleton
    X.genericPrincipalPartsAddSheaf.presheaf _ (genericPoint X)
  · rw [dense_iff_closure_eq]
    exact genericPoint_spec X
  · exact hdim
  · let ρF := X.genericFunctionFieldModule.presheaf.map
        (homOfLE hUtop).op
    let ρQ := X.genericPrincipalPartsModule.presheaf.map
        (homOfLE hUtop).op
    have hsTop : ρF sTop = s :=
      (X.genericFunctionFieldRestrictTopAddEquiv U hηU).apply_symm_apply s
    have hnaturality :
        X.genericPrincipalPartsProjectionAdd.hom.app (op U) (ρF sTop) =
          ρQ (X.genericPrincipalPartsProjectionAdd.hom.app (op ⊤) sTop) := by
      exact ConcreteCategory.congr_hom
        (X.genericPrincipalPartsProjectionAdd.hom.naturality
          (homOfLE hUtop).op) sTop
    have hfunction :
        X.functionFieldToGenericPrincipalPartsGlobalSections r =
          X.genericPrincipalPartsProjectionAdd.hom.app (op ⊤) sTop := by
      change X.genericPrincipalPartsProjectionAdd.hom.app (op ⊤)
        (X.genericFunctionFieldGlobalSectionsAddEquiv.symm r) = _
      rw [show X.genericFunctionFieldGlobalSectionsAddEquiv.symm r = sTop from
        X.genericFunctionFieldGlobalSectionsAddEquiv.symm_apply_apply sTop]
    have hs' : X.genericPrincipalPartsProjectionAdd.hom.app (op U) s =
        ρQ q := hs
    have hrestrict : ρQ
        (q - X.functionFieldToGenericPrincipalPartsGlobalSections r) = 0 := by
      rw [map_sub, hfunction, ← hnaturality, hsTop, hs', sub_self]
    calc
      X.genericPrincipalPartsAddSheaf.presheaf.germ ⊤
          (genericPoint X) (Set.mem_univ _)
          (q - X.functionFieldToGenericPrincipalPartsGlobalSections r) =
          X.genericPrincipalPartsAddSheaf.presheaf.germ U
            (genericPoint X) hηU
            (ρQ (q -
              X.functionFieldToGenericPrincipalPartsGlobalSections r)) := by
        symm
        exact X.genericPrincipalPartsAddSheaf.presheaf.germ_res_apply
          (homOfLE (show U ≤ ⊤ from le_top)) (genericPoint X) hηU _
      _ = X.genericPrincipalPartsAddSheaf.presheaf.germ U
          (genericPoint X) hηU 0 := congrArg _ hrestrict
      _ = 0 := map_zero _

/-- If every finitely supported generic principal part is represented by a rational
function, then every global generic principal part is so represented. -/
theorem surjective_functionFieldToGenericPrincipalParts_of_finiteSupport
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hfinite : ∀ q : Γ(X.genericPrincipalPartsModule, ⊤),
      (TopCat.Presheaf.topSectionSupport
        X.genericPrincipalPartsAddSheaf.presheaf q).Finite →
      q ∈ Set.range X.functionFieldToGenericPrincipalPartsGlobalSections) :
    Function.Surjective
      X.functionFieldToGenericPrincipalPartsGlobalSections := by
  intro q
  obtain ⟨r₀, hsupport⟩ :=
    X.exists_functionField_sub_with_finite_principalPartsSupport hdim q
  obtain ⟨r₁, hr₁⟩ := hfinite
    (q - X.functionFieldToGenericPrincipalPartsGlobalSections r₀) hsupport
  refine ⟨r₀ + r₁, ?_⟩
  rw [map_add, hr₁]
  abel

/-- Approximation for finitely supported generic principal parts implies vanishing of
the first cohomology of the structure sheaf. -/
theorem subsingleton_H_one_structureModule_of_finiteSupport_genericPrincipalParts
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hfinite : ∀ q : Γ(X.genericPrincipalPartsModule, ⊤),
      (TopCat.Presheaf.topSectionSupport
        X.genericPrincipalPartsAddSheaf.presheaf q).Finite →
      q ∈ Set.range X.functionFieldToGenericPrincipalPartsGlobalSections) :
    Subsingleton (Modules.H (structureModule X) 1) :=
  X.subsingleton_H_one_structureModule_of_surjective_genericPrincipalParts
    (X.surjective_functionFieldToGenericPrincipalParts_of_finiteSupport
      hdim hfinite)

end AlgebraicGeometry.Scheme
