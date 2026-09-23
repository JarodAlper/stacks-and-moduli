module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»

/-!
# Étale-local algebraic spaces over a scheme

This file records the elementary atlas-composition argument that an étale sheaf over a
scheme is an algebraic space when it becomes one after a surjective étale base change.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- Let `X → S` be an étale sheaf over a scheme.  If `X` becomes an algebraic space
after a surjective étale base change `S' → S`, then `X` is an algebraic space.

An étale presentation of the base change, followed by its projection to `X`, is an
étale presentation of `X`. -/
theorem IsAlgebraicSpace.of_etale_surjective_base_change
    {X : Scheme.{u}ᵒᵖ ⥤ Type u} (hX : Presieve.IsSheaf Scheme.etaleTopology X)
    {S S' : Scheme.{u}} (π : X ⟶ yoneda.obj S) (p : S' ⟶ S)
    [Etale p] [Surjective p]
    [IsAlgebraicSpace (pullback π (yoneda.map p))] : IsAlgebraicSpace X := by
  refine ⟨hX, ?_⟩
  obtain ⟨U, q, hq⟩ :=
    IsAlgebraicSpace.exists_presentation (X := pullback π (yoneda.map p))
  refine ⟨U, q ≫ pullback.fst π (yoneda.map p), ?_⟩
  let P : MorphismProperty Scheme.{u} := @Surjective ⊓ @Etale
  have hp : P.presheaf (yoneda.map p) :=
    MorphismProperty.relative_map ⟨inferInstance, inferInstance⟩
  have hfst : P.presheaf (pullback.fst π (yoneda.map p)) :=
    (MorphismProperty.relative_isStableUnderBaseChange P).of_isPullback
      (IsPullback.of_hasPullback π (yoneda.map p)).flip hp
  exact MorphismProperty.comp_mem _ _ _ hq hfst

end AlgebraicGeometry
