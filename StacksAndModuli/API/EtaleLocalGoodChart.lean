module

public import StacksAndModuli.API.PresentationBaseChange
public import StacksAndModuli.API.QuotientStackPresentation

/-!
# Descent from a good étale-local chart

Suppose every scheme-valued fiber of a prestack morphism has a small sheaf
representation which becomes an algebraic space after one surjective étale base change.
If that local fiber has a scheme presentation whose structural map has a property `P`,
then `P` descends to a global atlas of the original fiber.  This packages the chart
comparison needed by quotient-stack presentations without treating a local chart as a
global presentation.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe v₂ v₃ u₂ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}}
  {Ycat : BasedCategory.{v₃, u₃} Scheme.{u}}
  (F : BasedFunctor Xcat Ycat)

/-- A good scheme chart after the chosen surjective étale base change of every fiber
implies representability with `P` globally. -/
theorem RepresentableWith.of_etaleLocalFiberRepresentations_and_goodLocalCharts
    {P : MorphismProperty Scheme.{u}}
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    (hF : ∀ (T : Scheme.{u}) (g : BasedFunctor (overBased T) Ycat),
      EtaleLocalFiberRepresentation F T g)
    [P.IsStableUnderComposition]
    (hle : (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) ≤ P)
    (hlocal : ∀ ⦃S' S T : Scheme.{u}⦄ (p : S' ⟶ S) (f : S ⟶ T),
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p →
        (P f ↔ P (p ≫ f)))
    (hgood : ∀ (T : Scheme.{u}) (g : BasedFunctor (overBased T) Ycat),
      let D := hF T g
      ∃ (W : Scheme.{u})
        (K : BasedFunctor (overBased W)
          (fiberProduct F ((overBased.map D.localMap).comp g))),
        RepresentableWith
          (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) K ∧
        P (K.comp (BasedCategory.fiberProductSnd F
          ((overBased.map D.localMap).comp g))).overHom) :
    RepresentableWith P F := by
  apply RepresentableWith.of_exists_good_chart
    (Representable.of_etaleLocalFiberRepresentations F hF) hlocal
  intro T g
  let D := hF T g
  let _ : D.representation.toFunctor.IsEquivalence :=
    D.representation_isEquivalence
  let _ : Etale D.localMap := D.localMap_etale
  let _ : Surjective D.localMap := D.localMap_surjective
  let _ : IsAlgebraicSpace
      (pullback (representedFiberSecondBaseMap F g D.representation)
        (yoneda.map D.localMap)) := D.localIsAlgebraicSpace
  have hX : IsAlgebraicSpace D.X :=
    IsAlgebraicSpace.of_etale_surjective_base_change D.isSheaf
      (representedFiberSecondBaseMap F g D.representation) D.localMap
  obtain ⟨U, q, hq⟩ := IsAlgebraicSpace.exists_presentation (X := D.X)
  let Q : BasedFunctor (overBased U) (fiberProduct F g) :=
    (overBasedToOfPresheafYoneda U).comp
      ((ofPresheaf.map q).comp D.representation)
  let _ : MorphismProperty.IsStableUnderComposition
      (@Surjective : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  let _ : MorphismProperty.IsStableUnderComposition
      (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  let _ : MorphismProperty.IsStableUnderComposition
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderComposition.inf
  let _ : MorphismProperty.RespectsIso
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition
      (fun _ _ f hIso ↦ by
        let _ : IsIso f := hIso
        exact ⟨inferInstance, inferInstance⟩)
  have hqrel := relativelyRepresentableWith_ofPresheaf_map hq
  have hQ₁ := hqrel.comp_of_isEquivalence
    (overBasedToOfPresheafYoneda U)
  have hQ₂ := hQ₁.comp_target_isEquivalence D.representation
  have hQ : RepresentableWith
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) Q :=
    RelativelyRepresentableWith.representableWith le_rfl hQ₂
  obtain ⟨Q', hQ', hQ'struct⟩ :=
    hQ.exists_baseChange_presentation D.localMap
  obtain ⟨W, K, hK, hPK⟩ := hgood T g
  obtain ⟨V, aK, aQ, haK, haQ, ⟨e⟩⟩ :=
    AlgebraicGeometry.exists_common_cover_iso hK hQ'
  let Hlocal := BasedCategory.fiberProductSnd F
    ((overBased.map D.localMap).comp g)
  have e' : (overBased.map aK).comp (K.comp Hlocal) ≅
      (overBased.map aQ).comp (Q'.comp Hlocal) :=
    isoWhiskerRight e Hlocal
  have hstruct : aK ≫ (K.comp Hlocal).overHom =
      aQ ≫ (Q'.comp Hlocal).overHom := by
    have heq := CategoryTheory.BasedFunctor.overHom_eq_of_iso e'
    rwa [CategoryTheory.BasedFunctor.overHom_comp,
      CategoryTheory.BasedFunctor.overHom_comp,
      CategoryTheory.BasedFunctor.overHom_map,
      CategoryTheory.BasedFunctor.overHom_map] at heq
  have hPaK : P (aK ≫ (K.comp Hlocal).overHom) :=
    (hlocal aK (K.comp Hlocal).overHom haK).mp hPK
  have hPaQ : P (aQ ≫ (Q'.comp Hlocal).overHom) :=
    hstruct ▸ hPaK
  have hPQ' : P (Q'.comp Hlocal).overHom :=
    (hlocal aQ (Q'.comp Hlocal).overHom haQ).mpr hPaQ
  let f := (Q.comp (BasedCategory.fiberProductSnd F g)).overHom
  have hPQ'pullback : P (pullback.snd f D.localMap) := by
    rw [← hQ'struct]
    exact hPQ'
  let c := pullback.fst f D.localMap
  have hc : (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) c := by
    constructor <;> infer_instance
  have hp : P D.localMap := hle _ ⟨D.localMap_surjective, D.localMap_etale⟩
  have hPcomp : P (pullback.snd f D.localMap ≫ D.localMap) :=
    P.comp_mem _ _ hPQ'pullback hp
  have hcf : c ≫ f = pullback.snd f D.localMap ≫ D.localMap :=
    pullback.condition
  have hPcf : P (c ≫ f) := hcf ▸ hPcomp
  exact ⟨U, Q, hQ, (hlocal c f hc).mpr hPcf⟩

end AlgebraicGeometry.BasedFunctor
