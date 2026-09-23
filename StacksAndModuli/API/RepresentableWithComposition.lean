module

public import StacksAndModuli.API.RepresentableWithEtaleEquivalence
public import StacksAndModuli.«Section4.3-Properties».«part4.3.1-properties-of-morphisms»

/-!
# Composition with a relatively representable morphism

This file proves a mixed composition theorem for morphisms of prestacks.  If the first
factor is representable by schemes with property `Q`, the second factor is representable
by algebraic spaces with property `P`, `Q ≤ P`, and `P` is stable under composition, then
their composite is representable with `P`.  The proof constructs a scheme model of every
fiber by composing the two chosen fiber models.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {X : BasedCategory.{v₁, u₁} Scheme.{u}}
  {Y : BasedCategory.{v₂, u₂} Scheme.{u}}
  {Z : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- A morphism representable by schemes with `Q`, followed by a morphism representable
with `P`, is representable with `P` when `Q ≤ P`, `P` is composition-stable, and `P` is
étale-local on the source.

The locality hypothesis is stated in the exact form consumed by
`RepresentableWith.of_exists_good_chart`, so this lemma does not impose a bundled
locality structure on either property. -/
theorem RelativelyRepresentableWith.comp_representableWith
    {P Q : MorphismProperty Scheme.{u}} [P.IsStableUnderComposition]
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    [Z.p.IsFiberedInGroupoids]
    {F : BasedFunctor X Y} {G : BasedFunctor Y Z}
    (hQP : Q ≤ P) (hF : F.RelativelyRepresentableWith Q)
    (hG : RepresentableWith P G)
    (hlocal : ∀ ⦃S' S T : Scheme.{u}⦄ (p : S' ⟶ S) (f : S ⟶ T),
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) p →
        (P f ↔ P (p ≫ f))) :
    RepresentableWith P (F.comp G) := by
  have hrepF : Representable F :=
    representable_of_relativelyRepresentable hF.1
  have hrep : Representable (F.comp G) := hrepF.comp hG.1
  apply RepresentableWith.of_exists_good_chart hrep hlocal
  intro T g
  obtain ⟨A, hA, E, hE⟩ := hG.1 T g
  let _ : IsAlgebraicSpace A := hA
  let _ : E.toFunctor.IsEquivalence := hE
  obtain ⟨V, r, hr⟩ := IsAlgebraicSpace.exists_presentation (X := A)
  let p₀ : BasedFunctor (overBased V) (fiberProduct G g) :=
    (overBasedToOfPresheafYoneda V).comp ((ofPresheaf.map r).comp E)
  have hp₀rel : p₀.RelativelyRepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
    ((relativelyRepresentableWith_ofPresheaf_map hr).comp_of_isEquivalence
      (overBasedToOfPresheafYoneda V)).comp_target_isEquivalence E
  have hp₀ : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) p₀ :=
    RelativelyRepresentableWith.representableWith le_rfl hp₀rel
  let a := p₀.comp (fiberProductFst G g)
  obtain ⟨W, H, hH⟩ := hF.1 V a
  let _ : H.toFunctor.IsEquivalence := hH
  let R := fiberProductRightMap F (fiberProductFst G g) p₀
  let K := (H.comp R).comp (pasteFwd F G g)
  let π := fiberProductSnd F (fiberProductFst G g)
  let L := (fiberProductAssocInv F (fiberProductFst G g) p₀).comp
    (fiberProductSymm π p₀)
  have hL : L.toFunctor.IsEquivalence := by
    let _ : (fiberProductAssocInv F (fiberProductFst G g) p₀).toFunctor.IsEquivalence :=
      isEquivalence_fiberProductAssocInv F (fiberProductFst G g) p₀
    exact Functor.isEquivalence_trans
      (fiberProductAssocInv F (fiberProductFst G g) p₀).toFunctor
      (fiberProductSymm π p₀).toFunctor
  let _ : L.toFunctor.IsEquivalence := hL
  have hR : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) R := by
    have hbase := hp₀rel.fiberProductSnd π
    have hbase' : RepresentableWith
        (@_root_.AlgebraicGeometry.Surjective ⊓
          @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})
        (fiberProductSnd p₀ π) :=
      RelativelyRepresentableWith.representableWith le_rfl hbase
    have hcomp := hbase'.comp_source_isEquivalence L
    have hLR : L.comp (fiberProductSnd p₀ π) = R :=
      CategoryTheory.BasedFunctor.ext_of_toFunctor_eq rfl
    have hcomp' : RepresentableWith
        (@_root_.AlgebraicGeometry.Surjective ⊓
          @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) R := by
      rwa [hLR] at hcomp
    exact hcomp'
  have hHR : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) (H.comp R) :=
    hR.comp_source_isEquivalence H
  have hK : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) K :=
    hHR.comp_target_isEquivalence (pasteFwd F G g)
  refine ⟨W, K, hK, ?_⟩
  have hQ : Q (H.comp (fiberProductSnd F a)).overHom :=
    hF.2 V a W H hH
  have hPleft : P (H.comp (fiberProductSnd F a)).overHom := hQP _ hQ
  have hPright : P (p₀.comp (fiberProductSnd G g)).overHom := by
    simpa only [p₀, CategoryTheory.BasedFunctor.comp_assoc] using
      hG.2 T g A hA E hE V r hr
  have hPcomp : P ((H.comp (fiberProductSnd F a)).overHom ≫
      (p₀.comp (fiberProductSnd G g)).overHom) :=
    P.comp_mem _ _ hPleft hPright
  have hright : R.comp (fiberProductSnd F (fiberProductFst G g)) =
      (fiberProductSnd F a).comp p₀ := by
    rfl
  have hstruct : K.comp (fiberProductSnd (F.comp G) g) =
      (H.comp (fiberProductSnd F a)).comp
        (p₀.comp (fiberProductSnd G g)) := by
    dsimp only [K]
    rw [CategoryTheory.BasedFunctor.comp_assoc, pasteFwd_comp_snd]
    rw [CategoryTheory.BasedFunctor.comp_assoc H R]
    rw [← CategoryTheory.BasedFunctor.comp_assoc R, hright]
    simp only [CategoryTheory.BasedFunctor.comp_assoc]
  rw [hstruct, CategoryTheory.BasedFunctor.overHom_comp]
  exact hPcomp

end AlgebraicGeometry.BasedFunctor
