module

public import StacksAndModuli.API.RepresentableComposition
public import StacksAndModuli.API.RepresentableWithCharts

/-!
# Products of representable morphisms with properties

This file constructs a projection-compatible algebraic-space realization of the base
change of a product morphism. It then uses products of étale charts over the test
scheme to show that `RepresentableWith P` is closed under products whenever `P` is
étale-local on the source and stable under base change and composition.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ u

namespace AlgebraicGeometry.BasedFunctor

variable {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}}
  {Ycat : BasedCategory.{v₃, u₃} Scheme.{u}}
  {Xcat' : BasedCategory.{v₄, u₄} Scheme.{u}}
  {Ycat' : BasedCategory.{v₅, u₅} Scheme.{u}}

/-- The canonical algebraic-space realization of a base change of a product map,
built from chosen realizations of the two component base changes. -/
noncomputable def prodMapRepresentationEquivalence
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    [Xcat'.p.IsFiberedInGroupoids] [Ycat'.p.IsFiberedInGroupoids]
    (F : BasedFunctor Xcat Ycat) (G : BasedFunctor Xcat' Ycat')
    (T : Scheme.{u}) (g : BasedFunctor (overBased T) (prod Ycat Ycat'))
    (A B : Functor Scheme.{u}ᵒᵖ (Type u))
    (E₁ : BasedFunctor (ofPresheaf A)
      (fiberProduct F (g.comp (fiberProductFst Ycat.toBase Ycat'.toBase))))
    (E₂ : BasedFunctor (ofPresheaf B)
      (fiberProduct G (g.comp (fiberProductSnd Ycat.toBase Ycat'.toBase))))
    [E₁.toFunctor.IsEquivalence] [E₂.toFunctor.IsEquivalence] :
    let a := g.comp (fiberProductFst Ycat.toBase Ycat'.toBase)
    let b := g.comp (fiberProductSnd Ycat.toBase Ycat'.toBase)
    let H₁ := E₁.comp (fiberProductSnd F a)
    let H₂ := E₂.comp (fiberProductSnd G b)
    let K₁ := H₁.comp (overBasedToOfPresheafYoneda T)
    let K₂ := H₂.comp (overBasedToOfPresheafYoneda T)
    let ψ₁ := ofPresheafMapOfBasedFunctor K₁
    let ψ₂ := ofPresheafMapOfBasedFunctor K₂
    BasedFunctor (ofPresheaf (Limits.pullback ψ₁ ψ₂))
      (fiberProduct (prodMap F G) g) := by
  dsimp only
  let a := g.comp (fiberProductFst Ycat.toBase Ycat'.toBase)
  let b := g.comp (fiberProductSnd Ycat.toBase Ycat'.toBase)
  let q₁ := fiberProductSnd F a
  let q₂ := fiberProductSnd G b
  let H₁ := E₁.comp q₁
  let H₂ := E₂.comp q₂
  let O := overBasedToOfPresheafYoneda T
  let I := ofPresheafYonedaToOverBased T
  let K₁ := H₁.comp O
  let K₂ := H₂.comp O
  let ψ₁ := ofPresheafMapOfBasedFunctor K₁
  let ψ₂ := ofPresheafMapOfBasedFunctor K₂
  let L := ofPresheafMapPullbackLift (φ := ψ₁) (ψ := ψ₂)
  let η₁ := ofPresheafMapOfBasedFunctorIso K₁
  let η₂ := ofPresheafMapOfBasedFunctorIso K₂
  let θ₁ : (ofPresheaf.map ψ₁).comp I ≅ H₁ :=
    (whiskerRightIso η₁ I).trans
      (whiskerLeftIso H₁ (overBasedYonedaCounitIso T))
  let θ₂ : (ofPresheaf.map ψ₂).comp I ≅ H₂ :=
    (whiskerRightIso η₂ I).trans
      (whiskerLeftIso H₂ (overBasedYonedaCounitIso T))
  let R₀ := fiberProductPostcomp (ofPresheaf.map ψ₁)
    (ofPresheaf.map ψ₂) I
  let R₁ := fiberProductMapLeftIso θ₁ ((ofPresheaf.map ψ₂).comp I)
  let R₂ := fiberProductMapRightIso H₁ θ₂
  let R₃ := fiberProductRightMap H₁ q₂ E₂
  let R₄ := fiberProductSymm H₁ q₂
  let R₅ := fiberProductRightMap q₂ q₁ E₁
  let R₆ := fiberProductSymm q₂ q₁
  let R₇ := fiberProductAssoc F a q₂
  let R₈ := iteratedToProdMapPullback F G a b
  let ρ := prodLiftProjectionsIso g
  let R₉ := fiberProductMapRightIso (prodMap F G) ρ
  exact (((((((((L.comp R₀).comp R₁).comp R₂).comp R₃).comp R₄).comp
    R₅).comp R₆).comp R₇).comp R₈).comp R₉

/-- The canonical product realization is an equivalence of prestacks. -/
theorem isEquivalence_prodMapRepresentationEquivalence
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    [Xcat'.p.IsFiberedInGroupoids] [Ycat'.p.IsFiberedInGroupoids]
    (F : BasedFunctor Xcat Ycat) (G : BasedFunctor Xcat' Ycat')
    (T : Scheme.{u}) (g : BasedFunctor (overBased T) (prod Ycat Ycat'))
    (A B : Functor Scheme.{u}ᵒᵖ (Type u))
    (E₁ : BasedFunctor (ofPresheaf A)
      (fiberProduct F (g.comp (fiberProductFst Ycat.toBase Ycat'.toBase))))
    (E₂ : BasedFunctor (ofPresheaf B)
      (fiberProduct G (g.comp (fiberProductSnd Ycat.toBase Ycat'.toBase))))
    [E₁.toFunctor.IsEquivalence] [E₂.toFunctor.IsEquivalence] :
    (prodMapRepresentationEquivalence F G T g A B E₁ E₂).toFunctor.IsEquivalence := by
  let a := g.comp (fiberProductFst Ycat.toBase Ycat'.toBase)
  let b := g.comp (fiberProductSnd Ycat.toBase Ycat'.toBase)
  let q₁ := fiberProductSnd F a
  let q₂ := fiberProductSnd G b
  let H₁ := E₁.comp q₁
  let H₂ := E₂.comp q₂
  let O := overBasedToOfPresheafYoneda T
  let I := ofPresheafYonedaToOverBased T
  let K₁ := H₁.comp O
  let K₂ := H₂.comp O
  let ψ₁ := ofPresheafMapOfBasedFunctor K₁
  let ψ₂ := ofPresheafMapOfBasedFunctor K₂
  let L := ofPresheafMapPullbackLift (φ := ψ₁) (ψ := ψ₂)
  let η₁ := ofPresheafMapOfBasedFunctorIso K₁
  let η₂ := ofPresheafMapOfBasedFunctorIso K₂
  let θ₁ : (ofPresheaf.map ψ₁).comp I ≅ H₁ :=
    (whiskerRightIso η₁ I).trans
      (whiskerLeftIso H₁ (overBasedYonedaCounitIso T))
  let θ₂ : (ofPresheaf.map ψ₂).comp I ≅ H₂ :=
    (whiskerRightIso η₂ I).trans
      (whiskerLeftIso H₂ (overBasedYonedaCounitIso T))
  let R₀ := fiberProductPostcomp (ofPresheaf.map ψ₁)
    (ofPresheaf.map ψ₂) I
  let R₁ := fiberProductMapLeftIso θ₁ ((ofPresheaf.map ψ₂).comp I)
  let R₂ := fiberProductMapRightIso H₁ θ₂
  let R₃ := fiberProductRightMap H₁ q₂ E₂
  let R₄ := fiberProductSymm H₁ q₂
  let R₅ := fiberProductRightMap q₂ q₁ E₁
  let R₆ := fiberProductSymm q₂ q₁
  let R₇ := fiberProductAssoc F a q₂
  let R₈ := iteratedToProdMapPullback F G a b
  let ρ := prodLiftProjectionsIso g
  let R₉ := fiberProductMapRightIso (prodMap F G) ρ
  have hL : L.toFunctor.IsEquivalence :=
    isEquivalence_ofPresheafMapPullbackLift
  have hR₀ : R₀.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductPostcomp _ _ _
  have hR₁ : R₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapLeftIso _ _
  have hR₂ : R₂.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso _ _
  have hR₃ : R₃.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap H₁ q₂ E₂
  have hR₄ : R₄.toFunctor.IsEquivalence := inferInstance
  have hR₅ : R₅.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap q₂ q₁ E₁
  have hR₆ : R₆.toFunctor.IsEquivalence := inferInstance
  have hR₇ : R₇.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductAssoc F a q₂
  have hR₈ : R₈.toFunctor.IsEquivalence :=
    isEquivalence_iteratedToProdMapPullback F G a b
  have hR₉ : R₉.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso _ _
  let C₀ := L.comp R₀
  have hC₀ : C₀.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans L.toFunctor R₀.toFunctor
  let C₁ := C₀.comp R₁
  have hC₁ : C₁.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₀.toFunctor R₁.toFunctor
  let C₂ := C₁.comp R₂
  have hC₂ : C₂.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₁.toFunctor R₂.toFunctor
  let C₃ := C₂.comp R₃
  have hC₃ : C₃.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₂.toFunctor R₃.toFunctor
  let C₄ := C₃.comp R₄
  have hC₄ : C₄.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₃.toFunctor R₄.toFunctor
  let C₅ := C₄.comp R₅
  have hC₅ : C₅.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₄.toFunctor R₅.toFunctor
  let C₆ := C₅.comp R₆
  have hC₆ : C₆.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₅.toFunctor R₆.toFunctor
  let C₇ := C₆.comp R₇
  have hC₇ : C₇.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₆.toFunctor R₇.toFunctor
  let C₈ := C₇.comp R₈
  have hC₈ : C₈.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans C₇.toFunctor R₈.toFunctor
  change (C₈.comp R₉).toFunctor.IsEquivalence
  exact Functor.isEquivalence_trans C₈.toFunctor R₉.toFunctor

/-- The product realization preserves the projection to the test scheme on the
nose. -/
lemma prodMapRepresentationEquivalence_comp_snd
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    [Xcat'.p.IsFiberedInGroupoids] [Ycat'.p.IsFiberedInGroupoids]
    (F : BasedFunctor Xcat Ycat) (G : BasedFunctor Xcat' Ycat')
    (T : Scheme.{u}) (g : BasedFunctor (overBased T) (prod Ycat Ycat'))
    (A B : Functor Scheme.{u}ᵒᵖ (Type u))
    (E₁ : BasedFunctor (ofPresheaf A)
      (fiberProduct F (g.comp (fiberProductFst Ycat.toBase Ycat'.toBase))))
    (E₂ : BasedFunctor (ofPresheaf B)
      (fiberProduct G (g.comp (fiberProductSnd Ycat.toBase Ycat'.toBase))))
    [E₁.toFunctor.IsEquivalence] [E₂.toFunctor.IsEquivalence] :
    let a := g.comp (fiberProductFst Ycat.toBase Ycat'.toBase)
    let b := g.comp (fiberProductSnd Ycat.toBase Ycat'.toBase)
    let H₂ := E₂.comp (fiberProductSnd G b)
    let K₁ := (E₁.comp (fiberProductSnd F a)).comp
      (overBasedToOfPresheafYoneda T)
    let K₂ := H₂.comp (overBasedToOfPresheafYoneda T)
    let ψ₁ := ofPresheafMapOfBasedFunctor K₁
    let ψ₂ := ofPresheafMapOfBasedFunctor K₂
    (prodMapRepresentationEquivalence F G T g A B E₁ E₂).comp
        (fiberProductSnd (prodMap F G) g) =
      (ofPresheaf.map (Limits.pullback.snd ψ₁ ψ₂)).comp H₂ := by
  rfl

/-- Products preserve a morphism property that is stable under base change and
composition and can be checked after a surjective étale cover of the source. -/
theorem RepresentableWith.prodMap {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] [P.IsStableUnderComposition]
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    [Xcat'.p.IsFiberedInGroupoids] [Ycat'.p.IsFiberedInGroupoids]
    {F : BasedFunctor Xcat Ycat} {G : BasedFunctor Xcat' Ycat'}
    (hF : RepresentableWith P F) (hG : RepresentableWith P G)
    (hlocal : ∀ ⦃S' S T : Scheme.{u}⦄ (p : S' ⟶ S) (f : S ⟶ T),
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) p →
        (P f ↔ P (p ≫ f))) :
    RepresentableWith P (BasedCategory.prodMap F G) := by
  apply RepresentableWith.of_exists_good_chart
    (hF.representable.prodMap hG.representable) hlocal
  intro T g
  let p₁ := BasedCategory.fiberProductFst Ycat.toBase Ycat'.toBase
  let p₂ := BasedCategory.fiberProductSnd Ycat.toBase Ycat'.toBase
  let a := g.comp p₁
  let b := g.comp p₂
  obtain ⟨A, hA, E₁, hE₁⟩ := hF.1 T a
  obtain ⟨B, hB, E₂, hE₂⟩ := hG.1 T b
  let _ : E₁.toFunctor.IsEquivalence := hE₁
  let _ : E₂.toFunctor.IsEquivalence := hE₂
  let q₁ := BasedCategory.fiberProductSnd F a
  let q₂ := BasedCategory.fiberProductSnd G b
  let H₁ := E₁.comp q₁
  let H₂ := E₂.comp q₂
  let O := overBasedToOfPresheafYoneda T
  let K₁ := H₁.comp O
  let K₂ := H₂.comp O
  let ψ₁ := ofPresheafMapOfBasedFunctor K₁
  let ψ₂ := ofPresheafMapOfBasedFunctor K₂
  obtain ⟨U, qU, hqU⟩ := IsAlgebraicSpace.exists_presentation (X := A)
  obtain ⟨V, qV, hqV⟩ := IsAlgebraicSpace.exists_presentation (X := B)
  let fU := ((overBasedToOfPresheafYoneda U).comp
    ((ofPresheaf.map qU).comp H₁)).overHom
  let fV := ((overBasedToOfPresheafYoneda V).comp
    ((ofPresheaf.map qV).comp H₂)).overHom
  have hfU : P fU := by
    simpa [fU, H₁, q₁] using hF.2 T a A hA E₁ hE₁ U qU hqU
  have hfV : P fV := by
    simpa [fV, H₂, q₂] using hG.2 T b B hB E₂ hE₂ V qV hqV
  have hfUmap : yoneda.map fU = qU ≫ ψ₁ := by
    exact chart_map_eq_classified H₁ qU
  have hfVmap : yoneda.map fV = qV ≫ ψ₂ := by
    exact chart_map_eq_classified H₂ qV
  let W := Limits.pullback fU fV
  let sU : W ⟶ U := Limits.pullback.fst fU fV
  let sV : W ⟶ V := Limits.pullback.snd fU fV
  let SqW : IsPullback (yoneda.map sU) (yoneda.map sV)
      (yoneda.map fU) (yoneda.map fV) :=
    (IsPullback.of_hasPullback fU fV).map yoneda
  let eW := SqW.isoPullback
  let m := Limits.pullback.map (yoneda.map fU) (yoneda.map fV)
    ψ₁ ψ₂ qU qV (𝟙 _)
      ((Category.comp_id _).trans hfUmap)
      ((Category.comp_id _).trans hfVmap)
  let qW : yoneda.obj W ⟶ Limits.pullback ψ₁ ψ₂ := eW.hom ≫ m
  have hs : MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have he : MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have hse : MorphismProperty.IsStableUnderComposition
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
    @MorphismProperty.IsStableUnderComposition.inf Scheme _ _ _ hs he
  let _ := hse
  have hsIso : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u}) := inferInstance
  have heIso : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hseIso : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
    @MorphismProperty.RespectsIso.inf Scheme _ _ _ hsIso heIso
  let _ := hseIso
  have hbc : MorphismProperty.IsStableUnderBaseChange
      ((@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}).presheaf) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  let _ := hbc
  have hm : MorphismProperty.presheaf
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) m := by
    simpa [m] using MorphismProperty.pullbackMap
      (P := (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale :
          MorphismProperty Scheme.{u}).presheaf)
      hqU hqV hfUmap hfVmap
  have hqW : MorphismProperty.presheaf
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) qW := by
    exact MorphismProperty.RespectsIso.precomp _ eW.hom m hm
  let E := prodMapRepresentationEquivalence F G T g A B E₁ E₂
  have hE : E.toFunctor.IsEquivalence :=
    isEquivalence_prodMapRepresentationEquivalence F G T g A B E₁ E₂
  let _ : E.toFunctor.IsEquivalence := hE
  let p : BasedFunctor (overBased W)
      (fiberProduct (BasedCategory.prodMap F G) g) :=
    (overBasedToOfPresheafYoneda W).comp ((ofPresheaf.map qW).comp E)
  have hqrel := relativelyRepresentableWith_ofPresheaf_map hqW
  have hp₁ := hqrel.comp_of_isEquivalence (overBasedToOfPresheafYoneda W)
  have hp₂ := hp₁.comp_target_isEquivalence E
  have hp : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) p :=
    RelativelyRepresentableWith.representableWith le_rfl hp₂
  refine ⟨W, p, hp, ?_⟩
  let pr₂ := Limits.pullback.snd ψ₁ ψ₂
  let qB : yoneda.obj W ⟶ B := qW ≫ pr₂
  have hm_snd : m ≫ pr₂ =
      Limits.pullback.snd (yoneda.map fU) (yoneda.map fV) ≫ qV := by
    change Limits.pullback.lift _ _ _ ≫ _ = _
    exact Limits.pullback.lift_snd _ _ _
  have heW_snd : eW.hom ≫
      Limits.pullback.snd (yoneda.map fU) (yoneda.map fV) =
      yoneda.map sV := by
    exact SqW.isoPullback_hom_snd
  have hqB : qB = yoneda.map sV ≫ qV := by
    simp only [qB, qW, Category.assoc]
    rw [hm_snd, ← Category.assoc, heW_snd]
  let fB := ((overBasedToOfPresheafYoneda W).comp
    ((ofPresheaf.map qB).comp H₂)).overHom
  have hfB : fB = sV ≫ fV := by
    have h := atlas_overHom_eq H₂ qV qB sV (𝟙 W) (by
      simpa using hqB.symm)
    simpa [fB, fV] using h.symm
  have hsV : P sV := by
    exact MorphismProperty.pullback_snd fU fV hfU
  have hcomp : P (sV ≫ fV) := MorphismProperty.comp_mem P sV fV hsV hfV
  have hp_proj : p.comp (BasedCategory.fiberProductSnd
      (BasedCategory.prodMap F G) g) =
      (overBasedToOfPresheafYoneda W).comp
        ((ofPresheaf.map qB).comp H₂) := by
    rfl
  rw [hp_proj]
  change P fB
  rw [hfB]
  exact hcomp

end AlgebraicGeometry.BasedFunctor
