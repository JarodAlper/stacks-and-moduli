module

public import StacksAndModuli.API.ReducedSchemeNormalization

/-!
# Normalization of integral schemes

This file specializes the normalization of a reduced scheme to an integral scheme.  An
integral scheme has a unique irreducible component, so the component-generic scheme used
to construct its normalization is a single spectrum of a field.  It is therefore integral,
and Mathlib's relative-normalization API transfers integrality to the normalization.

## Main results

* `AlgebraicGeometry.Scheme.irreducibleComponents_finite_of_isIntegral`: an integral
  scheme has finitely many irreducible components.
* `AlgebraicGeometry.Scheme.componentGenericScheme_isIntegral`: the component-generic
  scheme of an integral scheme is integral.
* `AlgebraicGeometry.Scheme.normalization_isIntegral`: the normalization of an integral
  scheme is integral.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- An integral scheme has a finite type of irreducible components. -/
noncomputable instance irreducibleComponents_finite_of_isIntegral
    (X : Scheme.{u}) [IsIntegral X] : Finite (irreducibleComponents X) := by
  rw [irreducibleComponents_eq_singleton]
  exact (Set.finite_singleton Set.univ).to_subtype

/-- The component-generic scheme of an integral scheme is integral.

Indeed, the indexing type of irreducible components is a singleton and its unique summand
is the spectrum of the field at the generic point. -/
noncomputable instance componentGenericScheme_isIntegral
    (X : Scheme.{u}) [IsIntegral X] : IsIntegral X.componentGenericScheme := by
  let Z : irreducibleComponents X := ⟨Set.univ, by
    rw [irreducibleComponents_eq_singleton]
    exact Set.mem_singleton Set.univ⟩
  let _ : Unique (irreducibleComponents X) :=
    { default := Z
      uniq W := by
        apply Subtype.ext
        have hW : W.1 ∈ ({Set.univ} : Set (Set X)) := by
          rw [← irreducibleComponents_eq_singleton]
          exact W.2
        exact (Set.mem_singleton_iff.mp hW).trans rfl.symm }
  exact IsIntegral.of_isIso
    (coproductUniqueIso (fun W : irreducibleComponents X =>
      Spec (X.presheaf.stalk W.property.1.genericPoint))).inv

/-- The normalization of an integral scheme is integral. -/
noncomputable instance normalization_isIntegral
    (X : Scheme.{u}) [IsIntegral X] : IsIntegral X.normalization := by
  infer_instance

end AlgebraicGeometry.Scheme
