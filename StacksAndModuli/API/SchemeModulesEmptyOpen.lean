module

public import StacksAndModuli.API.OpenCoverModuleMorphismZero

/-!
# Sections of module sheaves on the empty open

This file records the basic sheaf consequence that sections over the empty open are
unique.  It is useful when constructing module sheaves and quotient data on empty
schemes.

Main declaration:
- `AlgebraicGeometry.Scheme.Modules.subsingleton_sections_bot`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Sections of a sheaf of modules over the empty open form a subsingleton. -/
lemma subsingleton_sections_bot {X : Scheme.{u}} (N : X.Modules) :
    Subsingleton Γ(N, ⊥) := by
  refine ⟨fun a b ↦ ?_⟩
  apply (AlgebraicGeometry.Scheme.Modules.abSheaf N).eq_of_locally_eq'
    (fun i : PEmpty.{u + 1} ↦ ⊥) ⊥
    (fun _ ↦ homOfLE le_rfl) ?_ a b (fun i ↦ i.elim)
  intro x hx
  exact absurd hx (by simp)

end AlgebraicGeometry.Scheme.Modules
