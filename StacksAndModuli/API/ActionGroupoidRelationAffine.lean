module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# The relation map of an affine group action is affine

For a group scheme `πG : G ⟶ S` acting on `πU : U₀ ⟶ S`, the relation map of the action
groupoid is the pair `(σ, pr₂) : G ×_S U₀ ⟶ U₀ ⨯ U₀` of the action and the projection,
valued in the absolute product. This file proves that a morphism property `P` that is
multiplicative, stable under base change, and contains closed immersions holds for this
pair as soon as `P πG` and `P (pullback.diagonal πU)` hold and `S` is affine — the
scheme-level input for the quotient-stack diagonal (Lemma 4.3.14 of *Stacks and
Moduli*).

The two reusable pieces are the graph-factorization cancellation
`CategoryTheory.MorphismProperty.of_comp_of_diagonal` — `P (f ≫ g)` and
`P (pullback.diagonal g)` imply `P f` — and the diagonal computation
`AlgebraicGeometry.MorphismProperty.diagonal_prod_snd` for the second projection of an
absolute product.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory.MorphismProperty

variable {C : Type*} [Category C] [HasPullbacks C] {P : MorphismProperty C}

/-- Graph-factorization cancellation: if `P (f ≫ g)` and the diagonal of `g` has `P`,
then `f` has `P`. `f` is the composition of its graph — a base change of the diagonal
of `g` — with a base change of `f ≫ g`. -/
theorem of_comp_of_diagonal [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hdiag : P (pullback.diagonal g)) (hcomp : P (f ≫ g)) : P f := by
  have hf : f = pullback.lift (𝟙 X) f (by simp) ≫ pullback.snd (f ≫ g) g :=
    (pullback.lift_snd _ _ _).symm
  rw [hf]
  apply P.comp_mem
  · exact P.of_isPullback (pullback_lift_diagonal_isPullback f g) hdiag
  · exact P.pullback_snd _ _ hcomp

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry.MorphismProperty

open CategoryTheory.MorphismProperty

variable {P : MorphismProperty Scheme.{u}}

/-- A property containing closed immersions holds for the diagonal of the structural
morphism of an affine scheme. -/
theorem diagonal_terminalFrom_of_isAffine [P.RespectsIso]
    (hcl : (@IsClosedImmersion : MorphismProperty Scheme.{u}) ≤ P)
    (S : Scheme.{u}) [IsAffine S] :
    P (pullback.diagonal (terminal.from S)) := by
  have : IsAffineHom (terminal.from S) := inferInstance
  have : IsSeparated (terminal.from S) := inferInstance
  apply hcl
  exact IsSeparated.isClosedImmersion_diagonal (f := terminal.from S)

/-- The diagonal of the second projection of an absolute product of schemes has `P`
as soon as the diagonal of `πU : U₀ ⟶ S` has `P`, the base `S` is affine, and `P` is
multiplicative, stable under base change, and contains closed immersions. -/
theorem diagonal_prod_snd [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    [P.RespectsIso]
    (hcl : (@IsClosedImmersion : MorphismProperty Scheme.{u}) ≤ P)
    {S U₀ : Scheme.{u}} [IsAffine S] (πU : U₀ ⟶ S)
    (hU : P (pullback.diagonal πU)) :
    P (pullback.diagonal (Limits.prod.snd : U₀ ⨯ U₀ ⟶ U₀)) := by
  have habs : P.diagonal (terminal.from U₀) := by
    rw [← terminal.comp_from πU]
    exact P.diagonal.comp_mem _ _ (MorphismProperty.diagonal_iff.mpr hU)
      (MorphismProperty.diagonal_iff.mpr
        (diagonal_terminalFrom_of_isAffine hcl S))
  have hsquare : IsPullback (Limits.prod.fst : U₀ ⨯ U₀ ⟶ U₀)
      (Limits.prod.snd : U₀ ⨯ U₀ ⟶ U₀)
      (terminal.from U₀) (terminal.from U₀) :=
    IsPullback.of_is_product (prodIsProd U₀ U₀) terminalIsTerminal
  exact MorphismProperty.diagonal_iff.mp (P.diagonal.of_isPullback hsquare habs)

/-- The relation map of an affine group action: for `πG : G ⟶ S` with `P πG`, any
`σ : G ×_S U₀ ⟶ U₀`, an affine base `S`, and `P` on the diagonal of `πU`, the pair
`(σ, pr₂) : G ×_S U₀ ⟶ U₀ ⨯ U₀` has `P`. -/
theorem prodLift_actionPair [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    [P.RespectsIso]
    (hcl : (@IsClosedImmersion : MorphismProperty Scheme.{u}) ≤ P)
    {S G U₀ : Scheme.{u}} [IsAffine S] {πG : G ⟶ S} (πU : U₀ ⟶ S)
    (hπG : P πG) (hU : P (pullback.diagonal πU))
    (σ : pullback πG πU ⟶ U₀) :
    P (Limits.prod.lift σ (pullback.snd πG πU)) := by
  apply CategoryTheory.MorphismProperty.of_comp_of_diagonal
    (g := (Limits.prod.snd : U₀ ⨯ U₀ ⟶ U₀))
  · exact diagonal_prod_snd hcl πU hU
  · rw [Limits.prod.lift_snd]
    exact P.pullback_snd _ _ hπG

end AlgebraicGeometry.MorphismProperty
