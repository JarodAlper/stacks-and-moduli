module

public import StacksProject.MoreOnMorphisms.SlicingSmooth.«lemma-etale-nbhd-dominates-smooth»
public import Mathlib.AlgebraicGeometry.Cover.Sigma

/-!
# Étale refinements of smooth surjections

This file packages the pointwise étale-local sections of a smooth surjection into one
surjective étale morphism.  The refining scheme is the disjoint union of the pointwise
étale neighbourhoods.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A smooth surjection of schemes is refined by a single surjective étale morphism.
The refinement morphism still factors through the original smooth surjection. -/
theorem exists_etale_surjective_refinement_of_smooth {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Smooth f] [Surjective f] :
    ∃ (Y' : Scheme.{u}) (p : Y' ⟶ Y), Etale p ∧ Surjective p ∧
      ∃ s : Y' ⟶ X, s ≫ f = p := by
  classical
  choose Z p hp hy s hs using hasEtaleLocalSections_of_smooth' f
  let cover : Y.Cover (Scheme.precoverage (@Etale)) :=
    Scheme.Cover.mkOfCovers Y Z p
      (fun y ↦ by
        obtain ⟨z, hz⟩ := hy y
        exact ⟨y, z, hz⟩)
      hp
  let Y' : Scheme.{u} := ∐ cover.X
  let q : Y' ⟶ Y := Sigma.desc cover.f
  let lift : Y' ⟶ X := Sigma.desc s
  refine ⟨Y', q, ?_, ?_, lift, ?_⟩
  · exact IsZariskiLocalAtSource.sigmaDesc cover.map_prop
  · dsimp only [q, Y']
    infer_instance
  · apply Sigma.hom_ext
    intro y
    simp only [lift, q, ← Category.assoc, Sigma.ι_desc]
    simpa [cover] using hs y

end AlgebraicGeometry.Scheme.Hom
