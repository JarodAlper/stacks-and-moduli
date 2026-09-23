module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Detecting isomorphisms of sheaves of modules on sections

A morphism of sheaves of modules on a scheme is an isomorphism as soon as every one of its
section maps is, because `SheafOfModules.forget ⋙ PresheafOfModules.toPresheaf` reflects
isomorphisms.  Combined with `Scheme.Modules.restrictFunctor`, whose section maps over `U` are
literally the section maps of the original over `j ''ᵁ U`, this gives a criterion for a morphism
to become an isomorphism after restriction to an open subscheme — the shape needed to say that
multiplication by a degree-one `f` trivializes the twisting sheaves on `D₊(f)`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_of_isIso_app`
* `AlgebraicGeometry.Scheme.Modules.isIso_restrictFunctor_map_of_bijective`
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism of sheaves of modules whose section maps are all isomorphisms is an
isomorphism. -/
theorem isIso_of_isIso_app {X : Scheme.{u}} {M N : X.Modules} (ψ : M ⟶ N)
    (h : ∀ U : (X.Opens)ᵒᵖ, IsIso (ψ.val.app U)) : IsIso ψ := by
  let e : M.val ≅ N.val :=
    PresheafOfModules.isoMk (fun U ↦ @asIso _ _ _ _ (ψ.val.app U) (h U))
      (fun {_ _} f ↦ ψ.val.naturality f)
  have he : e.hom = ψ.val := rfl
  refine ⟨⟨e.inv⟩, ?_, ?_⟩
  · refine SheafOfModules.hom_ext ?_
    change ψ.val ≫ e.inv = 𝟙 M.val
    rw [← he]
    exact e.hom_inv_id
  · refine SheafOfModules.hom_ext ?_
    change e.inv ≫ ψ.val = 𝟙 N.val
    rw [← he]
    exact e.inv_hom_id

/-- If every section map of `ψ` over an open in the image of `j` is bijective, then `ψ` becomes
an isomorphism after restriction along the open immersion `j`. -/
theorem isIso_restrictFunctor_map_of_bijective {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {M N : Y.Modules} (ψ : M ⟶ N)
    (h : ∀ U : X.Opens, Function.Bijective ((ψ.val.app (op (j ''ᵁ U))).hom)) :
    IsIso ((restrictFunctor j).map ψ) := by
  refine isIso_of_isIso_app _ fun U ↦ ?_
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ?_
  exact h U.unop

/-- Each section map of an isomorphism of sheaves of modules is an isomorphism. -/
theorem isIso_app_of_isIso {X : Scheme.{u}} {M N : X.Modules} (ψ : M ⟶ N) [IsIso ψ]
    (U : (X.Opens)ᵒᵖ) : IsIso (ψ.val.app U) := by
  refine ⟨(inv ψ).val.app U, ?_, ?_⟩
  · exact congrArg (fun θ : M ⟶ M ↦ θ.val.app U) (IsIso.hom_inv_id ψ)
  · exact congrArg (fun θ : N ⟶ N ↦ θ.val.app U) (IsIso.inv_hom_id ψ)

end AlgebraicGeometry.Scheme.Modules
