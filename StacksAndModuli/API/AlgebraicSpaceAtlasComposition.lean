module

public import StacksAndModuli.API.RepresentableComposition
public import StacksAndModuli.API.RepresentableWithCharts

/-!
# Composition with an algebraic-space atlas

This file records two composition tools for representable morphisms of prestacks.  First,
relative representability by schemes with a composition-stable morphism property is stable
under composition.  Second, precomposing a representable morphism out of an algebraic
space by one of its surjective étale scheme atlases preserves any property that is étale
local on the source.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace CategoryTheory.BasedFunctor

variable {C : Type u₁} [Category.{v₁} C]
  {A : BasedCategory.{v₂, u₂} C}
  {B : BasedCategory.{v₃, u₃} C}
  {D : BasedCategory.{v₄, u₄} C}

/-- Relative representability by objects of the base, with a composition-stable
morphism property, is stable under composition. -/
theorem RelativelyRepresentableWith.comp
    {P : MorphismProperty C} [P.IsStableUnderComposition]
    [A.p.IsFiberedInGroupoids] [B.p.IsFiberedInGroupoids]
    [D.p.IsFiberedInGroupoids]
    {F : BasedFunctor A B} {G : BasedFunctor B D}
    (hF : F.RelativelyRepresentableWith P)
    (hG : G.RelativelyRepresentableWith P) :
    (F.comp G).RelativelyRepresentableWith P := by
  refine ⟨?_, ?_⟩
  · intro S g
    obtain ⟨T, E, hE⟩ := hG.1 S g
    let _ : E.toFunctor.IsEquivalence := hE
    let a := E.comp (fiberProductFst G g)
    obtain ⟨U, H, hH⟩ := hF.1 T a
    let _ : H.toFunctor.IsEquivalence := hH
    let R₀ := fiberProductRightMap F (fiberProductFst G g) E
    let _ : R₀.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductRightMap F (fiberProductFst G g) E
    let K := (H.comp R₀).comp
      (pasteFwd F G g)
    refine ⟨U, K, ?_⟩
    let _ : (H.comp R₀).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans H.toFunctor R₀.toFunctor
    exact Functor.isEquivalence_trans
      (H.comp R₀).toFunctor
      (pasteFwd F G g).toFunctor
  · intro S g U R hR
    let _ : R.toFunctor.IsEquivalence := hR
    obtain ⟨T, E, hE⟩ := hG.1 S g
    let _ : E.toFunctor.IsEquivalence := hE
    let a := E.comp (fiberProductFst G g)
    let K₀ := fiberProductRightMap F (fiberProductFst G g) E
    let _ : K₀.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductRightMap F (fiberProductFst G g) E
    let K₁ := pasteFwd F G g
    let _ : K₁.toFunctor.IsEquivalence := inferInstance
    obtain ⟨L₁, ⟨α₁⟩, ⟨β₁⟩⟩ := exists_inverse_of_toFunctor K₁
    obtain ⟨L₀, ⟨α₀⟩, ⟨β₀⟩⟩ := exists_inverse_of_toFunctor K₀
    have hL₁ : L₁.toFunctor.IsEquivalence :=
      Functor.IsEquivalence.mk' K₁.toFunctor
        ((BasedNatTrans.forgetful _ _).mapIso β₁).symm
        ((BasedNatTrans.forgetful _ _).mapIso α₁)
    have hL₀ : L₀.toFunctor.IsEquivalence :=
      Functor.IsEquivalence.mk' K₀.toFunctor
        ((BasedNatTrans.forgetful _ _).mapIso β₀).symm
        ((BasedNatTrans.forgetful _ _).mapIso α₀)
    let _ : L₁.toFunctor.IsEquivalence := hL₁
    let _ : L₀.toFunctor.IsEquivalence := hL₀
    let H := (R.comp L₁).comp L₀
    let _ : (R.comp L₁).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans R.toFunctor L₁.toFunctor
    have hH : H.toFunctor.IsEquivalence := by
      exact Functor.isEquivalence_trans (R.comp L₁).toFunctor L₀.toFunctor
    have hFT : P (H.comp (BasedCategory.fiberProductSnd F a)).overHom :=
      hF.2 T a U H hH
    have hGS : P (E.comp (BasedCategory.fiberProductSnd G g)).overHom :=
      hG.2 S g T E hE
    have hcomp : P ((H.comp (BasedCategory.fiberProductSnd F a)).overHom ≫
        (E.comp (BasedCategory.fiberProductSnd G g)).overHom) :=
      P.comp_mem _ _ hFT hGS
    have hright : K₀.comp (BasedCategory.fiberProductSnd F (fiberProductFst G g)) =
        (BasedCategory.fiberProductSnd F a).comp E := by
      rfl
    let η₀ : L₀.comp ((BasedCategory.fiberProductSnd F a).comp E) ≅
        BasedCategory.fiberProductSnd F (fiberProductFst G g) :=
      (eqToIso (congrArg (L₀.comp ·) hright.symm)).trans
        ((isoWhiskerRight β₀
          (BasedCategory.fiberProductSnd F (fiberProductFst G g))).trans
          (eqToIso (id_comp _)))
    let η₁ : L₁.comp
          ((BasedCategory.fiberProductSnd F (fiberProductFst G g)).comp
            (BasedCategory.fiberProductSnd G g)) ≅
        BasedCategory.fiberProductSnd (F.comp G) g :=
      (eqToIso (congrArg (L₁.comp ·) (pasteFwd_comp_snd F G g).symm)).trans
        ((isoWhiskerRight β₁ (BasedCategory.fiberProductSnd (F.comp G) g)).trans
          (eqToIso (id_comp _)))
    let η₀' := isoWhiskerRight (isoWhiskerLeft (R.comp L₁) η₀)
      (BasedCategory.fiberProductSnd G g)
    let η₁' := isoWhiskerLeft R η₁
    let η : (H.comp (BasedCategory.fiberProductSnd F a)).comp
          (E.comp (BasedCategory.fiberProductSnd G g)) ≅
        R.comp (BasedCategory.fiberProductSnd (F.comp G) g) := by
      simpa only [H, comp_assoc] using η₀'.trans η₁'
    have hover := overHom_eq_of_iso η
    rw [overHom_comp] at hover
    rwa [hover] at hcomp

end CategoryTheory.BasedFunctor

namespace AlgebraicGeometry.BasedFunctor

open CategoryTheory.BasedFunctor

variable {Xcat : BasedCategory.{v₁, u₁} Scheme.{u}}
  {Xcat' : BasedCategory.{v₂, u₂} Scheme.{u}}
  {Ycat : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- Precomposing a representable morphism by an equivalence of source prestacks
preserves representability. -/
theorem Representable.comp_source_isEquivalence
    [Xcat.p.IsFiberedInGroupoids] [Xcat'.p.IsFiberedInGroupoids]
    [Ycat.p.IsFiberedInGroupoids]
    {F : BasedFunctor Xcat Ycat} (hF : Representable F)
    (E : BasedFunctor Xcat' Xcat) [E.toFunctor.IsEquivalence] :
    Representable (E.comp F) := by
  intro T g
  obtain ⟨Z, hZ, R, hR⟩ := hF T g
  let _ : R.toFunctor.IsEquivalence := hR
  let K := fiberProductLeftMap F g E
  let _ : K.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductLeftMap F g E
  obtain ⟨L, ⟨α⟩, ⟨β⟩⟩ :=
    CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor K
  have hL : L.toFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk' K.toFunctor
      ((BasedNatTrans.forgetful _ _).mapIso β).symm
      ((BasedNatTrans.forgetful _ _).mapIso α)
  exact ⟨Z, hZ, R.comp L,
    Functor.isEquivalence_trans R.toFunctor L.toFunctor⟩

variable {Y : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- Precomposing a representable morphism out of an algebraic space by a surjective
étale scheme presentation preserves any morphism property that is étale-local on the
source. -/
theorem RepresentableWith.comp_algebraicSpacePresentation
    {P : MorphismProperty Scheme.{u}}
    {X : Scheme.{u}ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X]
    [Y.p.IsFiberedInGroupoids]
    {F : BasedFunctor (ofPresheaf X) Y} (hF : RepresentableWith P F)
    {U : Scheme.{u}} {q : yoneda.obj U ⟶ X}
    (hq : MorphismProperty.presheaf
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) q)
    (hlocal : ∀ ⦃S' S T : Scheme.{u}⦄ (p : S' ⟶ S) (f : S ⟶ T),
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p →
        (P f ↔ P (p ≫ f))) :
    RepresentableWith P
      ((overBasedToOfPresheafYoneda U).comp ((ofPresheaf.map q).comp F)) := by
  let i := (overBasedToOfPresheafYoneda U).comp (ofPresheaf.map q)
  have hi : i.RelativelyRepresentableWith
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) :=
    (relativelyRepresentableWith_ofPresheaf_map hq).comp_of_isEquivalence
      (overBasedToOfPresheafYoneda U)
  have hiFRep : Representable ((ofPresheaf.map q).comp F) :=
    hF.representable.comp_ofPresheafMap q
  have hrep : Representable (i.comp F) :=
    hiFRep.comp_source_isEquivalence (overBasedToOfPresheafYoneda U)
  have hmain : RepresentableWith P (i.comp F) := by
    apply RepresentableWith.of_exists_good_chart hrep hlocal
    intro T g
    obtain ⟨A, hA, E, hE⟩ := hF.representable T g
    let _ : E.toFunctor.IsEquivalence := hE
    obtain ⟨V, r, hr⟩ := IsAlgebraicSpace.exists_presentation (X := A)
    let p₀ : BasedFunctor (overBased V) (fiberProduct F g) :=
      (overBasedToOfPresheafYoneda V).comp ((ofPresheaf.map r).comp E)
    have hp₀rel : p₀.RelativelyRepresentableWith
        (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) :=
      ((relativelyRepresentableWith_ofPresheaf_map hr).comp_of_isEquivalence
        (overBasedToOfPresheafYoneda V)).comp_target_isEquivalence E
    have hp₀ : RepresentableWith
        (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p₀ :=
      RelativelyRepresentableWith.representableWith le_rfl hp₀rel
    have hP₀ : P (p₀.comp (BasedCategory.fiberProductSnd F g)).overHom := by
      simpa only [p₀, CategoryTheory.BasedFunctor.comp_assoc] using
        hF.2 T g A hA E hE V r hr
    obtain ⟨B, hB, R, hR⟩ := hrep T g
    let _ : R.toFunctor.IsEquivalence := hR
    obtain ⟨W, s, hs⟩ := IsAlgebraicSpace.exists_presentation (X := B)
    let p : BasedFunctor (overBased W) (fiberProduct (i.comp F) g) :=
      (overBasedToOfPresheafYoneda W).comp ((ofPresheaf.map s).comp R)
    have hprel : p.RelativelyRepresentableWith
        (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) :=
      ((relativelyRepresentableWith_ofPresheaf_map hs).comp_of_isEquivalence
        (overBasedToOfPresheafYoneda W)).comp_target_isEquivalence R
    have hp : RepresentableWith
        (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p :=
      RelativelyRepresentableWith.representableWith le_rfl hprel
    refine ⟨W, p, hp, ?_⟩
    let π := BasedCategory.fiberProductSnd i (fiberProductFst F g)
    have hπ : π.RelativelyRepresentableWith
        (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) :=
      hi.fiberProductSnd (fiberProductFst F g)
    let K₁ := pasteFwd i F g
    let _ : K₁.toFunctor.IsEquivalence := inferInstance
    obtain ⟨L, ⟨α⟩, ⟨β⟩⟩ :=
      CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor K₁
    have hL : L.toFunctor.IsEquivalence :=
      Functor.IsEquivalence.mk' K₁.toFunctor
        ((BasedNatTrans.forgetful _ _).mapIso β).symm
        ((BasedNatTrans.forgetful _ _).mapIso α)
    let _ : L.toFunctor.IsEquivalence := hL
    let K := L.comp π
    have hK : K.RelativelyRepresentableWith
        (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) :=
      hπ.comp_of_isEquivalence L
    let pK := p.comp K
    have hpKrel : pK.RelativelyRepresentableWith
        (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) :=
      hprel.comp hK
    have hpK : RepresentableWith
        (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) pK :=
      RelativelyRepresentableWith.representableWith le_rfl hpKrel
    obtain ⟨W', a₀, a, ha₀, ha, ⟨e⟩⟩ :=
      AlgebraicGeometry.exists_common_cover_iso hp₀ hpK
    let e' := isoWhiskerRight e (BasedCategory.fiberProductSnd F g)
    have key : a₀ ≫ (p₀.comp (BasedCategory.fiberProductSnd F g)).overHom =
        a ≫ (pK.comp (BasedCategory.fiberProductSnd F g)).overHom := by
      have heq := overHom_eq_of_iso e'
      simpa only [CategoryTheory.BasedFunctor.comp_assoc,
        overHom_comp, overHom_map] using heq
    have hPa₀ : P (a₀ ≫
        (p₀.comp (BasedCategory.fiberProductSnd F g)).overHom) :=
      (hlocal a₀ _ ha₀).mp hP₀
    have hPa : P (a ≫
        (pK.comp (BasedCategory.fiberProductSnd F g)).overHom) :=
      key ▸ hPa₀
    have hPK : P (pK.comp (BasedCategory.fiberProductSnd F g)).overHom :=
      (hlocal a _ ha).mpr hPa
    let ηK : K.comp (BasedCategory.fiberProductSnd F g) ≅
        BasedCategory.fiberProductSnd (i.comp F) g := by
      simpa only [K, K₁, π, CategoryTheory.BasedFunctor.comp_assoc,
        pasteFwd_comp_snd, id_comp] using
        isoWhiskerRight β (BasedCategory.fiberProductSnd (i.comp F) g)
    let ηp : pK.comp (BasedCategory.fiberProductSnd F g) ≅
        p.comp (BasedCategory.fiberProductSnd (i.comp F) g) := by
      simpa only [pK, CategoryTheory.BasedFunctor.comp_assoc] using
        isoWhiskerLeft p ηK
    have hproj := overHom_eq_of_iso ηp
    exact hproj ▸ hPK
  simpa only [i, CategoryTheory.BasedFunctor.comp_assoc] using hmain

end AlgebraicGeometry.BasedFunctor
