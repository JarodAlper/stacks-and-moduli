module

public import StacksAndModuli.API.GlobalSectionsField

/-!
# Global constants of a proper integral scheme

This file packages the finiteness half of the standard fact that the global
constants of a proper integral scheme over a field form a finite field
extension. Mathlib proves finiteness for the map on global sections attached
directly to the structure morphism. The API here transports that result across
the canonical `Γ(Spec k, ᵊ) ≅ k` isomorphism to the `k`-algebra structure on
`Γ(X, ᵊ_X)` used throughout StacksAndModuli.

## Main results

* `AlgebraicGeometry.Scheme.finite_baseRingHom_of_isIntegral_of_universallyClosed`:
  the canonical map `k → Γ(X, ᵊ_X)` is finite.
* `AlgebraicGeometry.Scheme.moduleFinite_globalSections_of_isIntegral_of_proper`:
  the global constants of a proper integral scheme are a finite `k`-module.
* `AlgebraicGeometry.Scheme.finiteDimensional_globalSections_of_isIntegral_of_proper`:
  the corresponding finite-dimensionality statement over a field.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- If an integral scheme is universally closed and locally of finite type over
`Spec k`, then its canonical base-ring map `k → Γ(X, ᵊ_X)` is finite.

Mathlib's `finite_appTop_of_universallyClosed` gives the result before identifying
global functions on `Spec k` with `k`; finiteness is preserved under composition
with that isomorphism. -/
theorem finite_baseRingHom_of_isIntegral_of_universallyClosed
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] :
    (X.baseRingHom (CommRingCat.of k)).Finite := by
  rw [baseRingHom_eq]
  exact (finite_appTop_of_universallyClosed k
    (X ↘ Spec (CommRingCat.of k))).comp
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)

/-- The global constants of an integral scheme universally closed and locally of
finite type over a field form a finite module over that field. -/
theorem moduleFinite_globalSections_of_isIntegral_of_universallyClosed
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] :
    Module.Finite k Γ(X, ⊤) := by
  rw [← RingHom.finite_algebraMap, algebraMap_globalSections_eq]
  exact finite_baseRingHom_of_isIntegral_of_universallyClosed k X

/-- The global constants of a proper integral scheme form a finite module over
the ground field. -/
theorem moduleFinite_globalSections_of_isIntegral_of_proper
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
    [IsProper (X ↘ Spec (CommRingCat.of k))] :
    Module.Finite k Γ(X, ⊤) :=
  moduleFinite_globalSections_of_isIntegral_of_universallyClosed k X

/-- The global constants of a proper integral scheme are finite-dimensional over
the ground field. -/
theorem finiteDimensional_globalSections_of_isIntegral_of_proper
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
    [IsProper (X ↘ Spec (CommRingCat.of k))] :
    FiniteDimensional k Γ(X, ⊤) :=
  moduleFinite_globalSections_of_isIntegral_of_proper k X

end AlgebraicGeometry.Scheme
