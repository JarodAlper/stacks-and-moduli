module

public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing lifts through a monomorphism

A factorization through a monomorphism can be checked on an open cover of the source:
the local lifts agree on overlaps automatically and hence glue.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Lifting along a monomorphism is local on the source.  If `p : X ⟶ Y` factors
through a monomorphism `ι : Z ⟶ Y` on every member of an open cover of `X`, then it
factors through `ι`. -/
theorem exists_lift_of_openCover {X Z Y : Scheme.{u}} (ι : Z ⟶ Y) [Mono ι]
    (p : X ⟶ Y) (𝒰 : X.OpenCover)
    (h : ∀ i, ∃ k : 𝒰.X i ⟶ Z, k ≫ ι = 𝒰.f i ≫ p) :
    ∃ k : X ⟶ Z, k ≫ ι = p := by
  choose k hk using h
  refine ⟨𝒰.glueMorphisms k ?_, ?_⟩
  · intro x y
    rw [← cancel_mono ι, Category.assoc, Category.assoc, hk, hk,
      ← Category.assoc, ← Category.assoc, pullback.condition]
  · apply 𝒰.hom_ext
    intro x
    rw [← Category.assoc, 𝒰.ι_glueMorphisms, hk]

end AlgebraicGeometry.Scheme

