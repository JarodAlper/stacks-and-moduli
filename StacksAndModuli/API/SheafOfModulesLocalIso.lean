module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Isomorphisms of sheaves of modules are a local condition

A morphism of sheaves of modules on a scheme is an isomorphism as soon as it is *locally*
bijective. This is the standard way to prove that a globally defined comparison map — a
multiplication map of twisting sheaves, a base-change comparison, a trivialization — is an
isomorphism: exhibit a cover on which both sides are visibly the same and the map matches
generators.

Mathlib has both halves but does not put them together:
`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso` says a locally bijective morphism of
sheaves valued in a concrete category with reflecting forgetful functor is an isomorphism,
and `SheafOfModules.toSheaf` reflects isomorphisms. Composing them gives the statement in
the form actually used.

## Implementation note

`isIso_of_reflects_iso` does not find the `ReflectsIsomorphisms` instance for
`SheafOfModules.toSheaf` when it appears in an inferred position, although the instance is
present; it is supplied explicitly below. This is the discrimination-key issue described in
the root INSIGHTS.md.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isIso_of_locallyBijective`: a locally bijective morphism
  of sheaves of modules on a scheme is an isomorphism.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A morphism of sheaves of modules on a scheme which is locally injective and locally
surjective is an isomorphism.

Locality is measured after forgetting to sheaves of abelian groups, which is where
`Sheaf.IsLocallyInjective` and `Sheaf.IsLocallySurjective` live; the module structure comes
back for free because `SheafOfModules.toSheaf` reflects isomorphisms. -/
theorem isIso_of_locallyBijective {F G : X.Modules} (φ : F ⟶ G)
    (hinj : Sheaf.IsLocallyInjective ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ))
    (hsurj : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ)) :
    IsIso φ := by
  have hiso : IsIso ((SheafOfModules.toSheaf.{u} X.ringCatSheaf).map φ) :=
    (Sheaf.isLocallyBijective_iff_isIso _).mp ⟨hinj, hsurj⟩
  haveI : (SheafOfModules.toSheaf.{u} X.ringCatSheaf).ReflectsIsomorphisms :=
    inferInstance
  exact isIso_of_reflects_iso φ (SheafOfModules.toSheaf.{u} X.ringCatSheaf)

end AlgebraicGeometry.Scheme.Modules
