module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal

/-!
# A reduction for the diagonal of an algebraic space

This file isolates the effective-descent input in the representability of the
diagonal of an algebraic space.  Once monomorphisms from algebraic spaces to schemes
are known to be representable by schemes, every base change of the diagonal is
representable.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite

universe v₂ v₃ u₂ u₃ u

namespace CategoryTheory.MorphismProperty

/-- Products of relatively representable morphisms preserve a property which is
stable under composition. -/
theorem relative_prodMap_of_stableUnderComposition
    {C : Type u₂} {D : Type u₃} [Category.{v₂} C] [Category.{v₃} D]
    {ι : Functor C D} [ι.Faithful] [ι.Full]
    {P : MorphismProperty C} [P.IsStableUnderComposition]
    {W X Y Z : D} [HasBinaryProduct W Y] [HasBinaryProduct X Y]
    [HasBinaryProduct X Z] [HasBinaryProduct Y X] [HasBinaryProduct Z X]
    {f : W ⟶ X} {g : Y ⟶ Z} (hf : P.relative ι f)
    (hg : P.relative ι g) : P.relative ι (prod.map f g) := by
  open Limits in
  have h₁ : P.relative ι (prod.map f (𝟙 Y)) :=
    (relative_isStableUnderBaseChange P).of_isPullback
      (IsPullback.of_prod_fst_with_id f Y) hf
  have h₂ : P.relative ι (prod.map (𝟙 X) g) := by
    have h₂' : P.relative ι (prod.map g (𝟙 X)) :=
      (relative_isStableUnderBaseChange P).of_isPullback
        (IsPullback.of_prod_fst_with_id g X) hg
    exact (arrow_mk_iso_iff (P.relative ι)
      ((CategoryTheory.Arrow.isoMk (prod.braiding Y X) (prod.braiding Z X)
          (by dsimp; ext <;> simp)) :
        CategoryTheory.Arrow.mk (prod.map g (𝟙 X)) ≅
          CategoryTheory.Arrow.mk (prod.map (𝟙 X) g))).1 h₂'
  rw [show prod.map f g = prod.map f (𝟙 Y) ≫ prod.map (𝟙 X) g by
    ext <;> simp]
  exact comp_mem _ _ _ h₁ h₂

/-- Products of morphisms of presheaves represented with a property stable under
composition are represented with the same property. -/
theorem presheaf_prodMap_of_stableUnderComposition
    {C : Type u₂} [Category.{v₂} C] {P : MorphismProperty C}
    [P.IsStableUnderComposition]
    {W X Y Z : Functor Cᵒᵖ (Type v₂)} {f : W ⟶ X} {g : Y ⟶ Z}
    (hf : P.presheaf f) (hg : P.presheaf g) :
    P.presheaf (prod.map f g) :=
  relative_prodMap_of_stableUnderComposition hf hg

end MorphismProperty
end CategoryTheory

namespace AlgebraicGeometry

/-- Binary products of algebraic spaces are algebraic spaces. -/
theorem IsAlgebraicSpace.prod
    (X Y : _root_.AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type u)
    [_root_.AlgebraicGeometry.IsAlgebraicSpace X]
    [_root_.AlgebraicGeometry.IsAlgebraicSpace Y] :
    _root_.AlgebraicGeometry.IsAlgebraicSpace (X ⨯ Y) := by
  refine ⟨?_, ?_⟩
  · rw [← CategoryTheory.isSheaf_iff_isSheaf_of_type]
    refine ObjectProperty.prop_of_isLimit (P := Presheaf.IsSheaf Scheme.etaleTopology)
      (limit.isLimit (pair X Y)) ?_
    rintro ⟨j⟩
    cases j with
    | left =>
        rw [pair_obj_left, CategoryTheory.isSheaf_iff_isSheaf_of_type]
        exact IsAlgebraicSpace.isSheaf (X := X)
    | right =>
        rw [pair_obj_right, CategoryTheory.isSheaf_iff_isSheaf_of_type]
        exact IsAlgebraicSpace.isSheaf (X := Y)
  · obtain ⟨U, p, hp⟩ := IsAlgebraicSpace.exists_presentation (X := X)
    obtain ⟨V, q, hq⟩ := IsAlgebraicSpace.exists_presentation (X := Y)
    let e : yoneda.obj (U ⨯ V) ≅ yoneda.obj U ⨯ yoneda.obj V :=
      preservesLimitIso yoneda (pair U V) ≪≫
        HasLimit.isoOfNatIso (pairComp U V yoneda)
    refine ⟨U ⨯ V, e.hom ≫ prod.map p q, ?_⟩
    exact MorphismProperty.RespectsIso.precomp
      ((@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}).presheaf)
      e.hom _
      (MorphismProperty.presheaf_prodMap_of_stableUnderComposition hp hq)

/-- The diagonal of every algebraic space is representable once monomorphisms from
algebraic spaces to schemes are known to be representable.

The reduction is formal: a base change of the diagonal is again an algebraic space,
and its projection to the test scheme is a monomorphism.  Applying the hypothesis to
that projection and pasting its representing pullback square with the defining
pullback square gives the required representative. -/
theorem IsAlgebraicSpace.relativelyRepresentable_diag_of_monomorphisms
    (hmono : ∀ {Y : Scheme.{u}ᵒᵖ ⥤ Type u} [IsAlgebraicSpace Y]
      {T : Scheme.{u}} (f : Y ⟶ yoneda.obj T), [Mono f] →
        yoneda.relativelyRepresentable f)
    (X : Scheme.{u}ᵒᵖ ⥤ Type u) [IsAlgebraicSpace X] :
    yoneda.relativelyRepresentable (Limits.diag X) := by
  intro T g
  let Q := Limits.pullback (Limits.diag X) g
  let q : Q ⟶ yoneda.obj T := Limits.pullback.snd (Limits.diag X) g
  let _ : IsAlgebraicSpace (X ⨯ X) := IsAlgebraicSpace.prod X X
  let _ : IsAlgebraicSpace Q := IsAlgebraicSpace.pullback (Limits.diag X) g
  let _ : Mono q := by
    dsimp only [q, Q]
    infer_instance
  obtain ⟨S, s, fst, hfst⟩ := hmono q (𝟙 (yoneda.obj T))
  refine ⟨S, s, fst ≫ Limits.pullback.fst (Limits.diag X) g, ?_⟩
  have hQ : IsPullback (Limits.pullback.fst (Limits.diag X) g)
      (Limits.pullback.snd (Limits.diag X) g) (Limits.diag X) g :=
    IsPullback.of_hasPullback _ _
  simpa [q] using hfst.paste_horiz hQ

end AlgebraicGeometry
