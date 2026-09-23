module

public import StacksAndModuli.API.DeligneMumfordDiagonal

/-!
# Finite type charts for diagonals of algebraic stacks

This file isolates the finite-type half of the local-chart construction for the
diagonal of an algebraic stack. Formal unramifiedness of a Deligne--Mumford diagonal
needs an étale presentation, but local finite type only uses that the chosen presentation
is smooth. Consequently this construction applies to every algebraic stack.

## Main result

* `IsAlgebraicStack.representableWith_locallyOfFiniteType_diag_of_presentation`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry

/-- Compatible global and etale-local chart data for a scheme-valued fiber of the
diagonal of an algebraic stack. -/
structure AlgebraicStackDiagonalFiniteTypeFiberChart
    (X : BasedCategory.{v₂, u₂} Scheme.{u}) [IsAlgebraicStack X]
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ prod X X) where
  /-- A global algebraic-space representation and the chosen etale local base. -/
  fiber : BasedFunctor.EtaleLocalFiberRepresentation (diag X) T g
  /-- The scheme furnishing the good local chart. -/
  W : Scheme.{u}
  /-- The chart of the diagonal fiber after the chosen local base change. -/
  chart : overBased W ⥤ᵇ
    fiberProduct (diag X) ((overBased.map fiber.localMap).comp g)
  /-- The local chart is a surjective etale presentation. -/
  chart_presentation : BasedFunctor.RepresentableWith
    (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) chart
  /-- The structural map of the local chart is locally of finite type. -/
  chart_locallyOfFiniteType :
    LocallyOfFiniteType
      (chart.comp (fiberProductSnd (diag X)
        ((overBased.map fiber.localMap).comp g))).overHom

/-- Every scheme-valued fiber of the diagonal of an algebraic stack admits compatible
global algebraic-space and good etale-local chart data whose structural map is locally
of finite type. -/
theorem nonempty_algebraicStackDiagonalFiniteTypeFiberChart
    (X : BasedCategory.{v₂, u₂} Scheme.{u}) [IsAlgebraicStack X]
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ prod X X) :
    Nonempty (AlgebraicStackDiagonalFiniteTypeFiberChart X T g) := by
  let a := (twoYonedaEval (𝒳 := X) T).obj
    (g.comp (fiberProductFst X.toBase X.toBase))
  let b := (twoYonedaEval (𝒳 := X) T).obj
    (g.comp (fiberProductSnd X.toBase X.toBase))
  obtain ⟨U, P, hP⟩ := IsAlgebraicStack.exists_presentation (𝒳 := X)
  obtain ⟨S, p, hpEtale, hpSurjective, liftA, liftB, ⟨eA⟩, ⟨eB⟩⟩ :=
    hP.exists_etale_surjective_pair_lift
      (twoYonedaPullback T a) (twoYonedaPullback T b)
  let _ : Etale p := hpEtale
  let _ : Surjective p := hpSurjective
  let pairLift := prodLift liftA liftB
  let pairIso₀ : pairLift.comp (prodMap P P) ≅
      (overBased.map p).comp (isomPairMap a b) := by
    change (prodLift liftA liftB).comp (prodMap P P) ≅
      (overBased.map p).comp
        (prodLift (twoYonedaPullback T a) (twoYonedaPullback T b))
    rw [prodLift_comp_prodMap, comp_prodLift]
    exact prodLiftIso eA eB
  let pairIso : pairLift.comp (prodMap P P) ≅ (overBased.map p).comp g :=
    pairIso₀ ≪≫ isoWhiskerLeft (overBased.map p)
      (IsAlgebraicStack.isomPairMapIso g)
  obtain ⟨R, hR, ER, hER⟩ := hP.representable U P
  let _ : IsAlgebraicSpace R := hR
  let _ : ER.toFunctor.IsEquivalence := hER
  obtain ⟨V, q, hq⟩ := IsAlgebraicSpace.exists_presentation (X := R)
  let Rchart : overBased V ⥤ᵇ fiberProduct P P :=
    (overBasedToOfPresheafYoneda V).comp ((ofPresheaf.map q).comp ER)
  have hRchart : BasedFunctor.RepresentableWith
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) Rchart := by
    let hqrel := BasedFunctor.relativelyRepresentableWith_ofPresheaf_map hq
    let h₁ := hqrel.comp_of_isEquivalence (overBasedToOfPresheafYoneda V)
    let h₂ := h₁.comp_target_isEquivalence ER
    exact BasedFunctor.RelativelyRepresentableWith.representableWith le_rfl h₂
  let rPair := fiberProductPairMap P P
  let HR := Rchart.comp rPair
  let prodFst := fiberProductFst (overBased U).toBase (overBased U).toBase
  let prodSnd := fiberProductSnd (overBased U).toBase (overBased U).toBase
  let r₁ := HR.comp prodFst
  let r₂ := HR.comp prodSnd
  let r := Limits.prod.lift r₁.overHom r₂.overHom
  let Er := overBasedProdLiftIso r₁ r₂ ≪≫ prodLiftProjectionsIso HR
  let s₁ := pairLift.comp prodFst
  let s₂ := pairLift.comp prodSnd
  let s := Limits.prod.lift s₁.overHom s₂.overHom
  let Es := overBasedProdLiftIso s₁ s₂ ≪≫ prodLiftProjectionsIso pairLift
  let Eprod := overBasedProdComparison U U
  let W := pullback r s
  let K₀ := BasedFunctor.overBasedFiberPullbackEquivalence (overBased.map r) s
  let K₁ := fiberProductPostcomp (overBased.map r) (overBased.map s) Eprod
  let K₂ := fiberProductMapLeftIso Er ((overBased.map s).comp Eprod)
  let Es' : (overBased.map s).comp Eprod ≅
      (BasedFunctor.id (overBased S)).comp pairLift :=
    Es ≪≫ eqToIso (BasedFunctor.id_comp pairLift).symm
  let K₃ := fiberProductMapRightIso HR Es'
  let Kpre := ((K₀.comp K₁).comp K₂).comp K₃
  let K₄ := fiberProductPresentationMap rPair pairLift Rchart
    (BasedFunctor.id (overBased S))
  let Erel := fiberProductToProdMapDiag P P
  let D₀ := fiberProductSymm rPair pairLift
  let D₁ := fiberProductRightMap pairLift
    (fiberProductFst (prodMap P P) (diag X)) Erel
  let D₂ := pasteFwd pairLift (prodMap P P) (diag X)
  let D₃ := fiberProductSymm (pairLift.comp (prodMap P P)) (diag X)
  let D₄ := fiberProductMapRightIso (diag X) pairIso
  let D := (((D₀.comp D₁).comp D₂).comp D₃).comp D₄
  let K := (Kpre.comp K₄).comp D
  have hKpre : Kpre.toFunctor.IsEquivalence := by
    let _ : Eprod.toFunctor.IsEquivalence :=
      isEquivalence_overBasedProdComparison U U
    let _ : K₀.toFunctor.IsEquivalence :=
      BasedFunctor.isEquivalence_overBasedFiberPullbackEquivalence (overBased.map r) s
    let _ : K₁.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductPostcomp (overBased.map r) (overBased.map s) Eprod
    let _ : K₂.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductMapLeftIso Er ((overBased.map s).comp Eprod)
    let _ : K₃.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductMapRightIso HR Es'
    let _ : (K₀.comp K₁).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans K₀.toFunctor K₁.toFunctor
    let _ : ((K₀.comp K₁).comp K₂).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans (K₀.comp K₁).toFunctor K₂.toFunctor
    exact Functor.isEquivalence_trans
      ((K₀.comp K₁).comp K₂).toFunctor K₃.toFunctor
  have hD : D.toFunctor.IsEquivalence := by
    let _ : Erel.toFunctor.IsEquivalence := isEquivalence_fiberProductToProdMapDiag P P
    let _ : D₁.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductRightMap pairLift
        (fiberProductFst (prodMap P P) (diag X)) Erel
    let _ : D₄.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductMapRightIso (diag X) pairIso
    let _ : (D₀.comp D₁).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans D₀.toFunctor D₁.toFunctor
    let _ : ((D₀.comp D₁).comp D₂).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans (D₀.comp D₁).toFunctor D₂.toFunctor
    let _ : (((D₀.comp D₁).comp D₂).comp D₃).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans ((D₀.comp D₁).comp D₂).toFunctor D₃.toFunctor
    exact Functor.isEquivalence_trans
      (((D₀.comp D₁).comp D₂).comp D₃).toFunctor D₄.toFunctor
  have hK₄ : BasedFunctor.RepresentableWith
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) K₄ := by
    let _ : (BasedFunctor.id (overBased S)).toFunctor.IsEquivalence := by
      change (Functor.id (Over S)).IsEquivalence
      infer_instance
    have hId : BasedFunctor.RepresentableWith
        (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u})
        (BasedFunctor.id (overBased S)) :=
      BasedFunctor.RepresentableWith.surjectiveEtale_of_isEquivalence
        (BasedFunctor.id (overBased S))
    have hlocal := fun ⦃S' S₀ T₀⦄ f h hf ↦
      surjectiveEtale_iff_comp_of_surjectiveEtale
        (X' := S') (X := S₀) (Y := T₀) f h hf
    have hprod := hRchart.prodMap hId hlocal
    exact hprod.fiberProductPresentationMap_of_prodMap
  have hK : BasedFunctor.RepresentableWith
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) K := by
    let _ : Kpre.toFunctor.IsEquivalence := hKpre
    let _ : D.toFunctor.IsEquivalence := hD
    exact (hK₄.comp_source_isEquivalence Kpre).comp_target_isEquivalence D
  obtain ⟨A, hA, EA, hEA⟩ :=
    IsAlgebraicStack.representable_diag_of_presentation X T g
  let _ : IsAlgebraicSpace A := hA
  let _ : EA.toFunctor.IsEquivalence := hEA
  let fiber : BasedFunctor.EtaleLocalFiberRepresentation (diag X) T g :=
    { X := A
      isSheaf := IsAlgebraicSpace.isSheaf
      representation := EA
      representation_isEquivalence := hEA
      localBase := S
      localMap := p
      localMap_etale := hpEtale
      localMap_surjective := hpSurjective
      localIsAlgebraicSpace := IsAlgebraicSpace.pullback _ _ }
  have hKft : LocallyOfFiniteType
      (K.comp (fiberProductSnd (diag X) ((overBased.map p).comp g))).overHom := by
    have hr₂eq : r₂ = Rchart.comp (fiberProductSnd P P) := by
      rfl
    have hr₂prop : (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) r₂.overHom := by
      rw [hr₂eq]
      exact hP.2 U P R hR ER hER V q hq
    have hrsmooth : Smooth (r ≫ (Limits.prod.snd : U ⨯ U ⟶ U)) := by
      rw [show r ≫ (Limits.prod.snd : U ⨯ U ⟶ U) = r₂.overHom by
        change Limits.prod.lift r₁.overHom r₂.overHom ≫ Limits.prod.snd = _
        exact Limits.prod.lift_snd _ _]
      exact hr₂prop.2
    have hrft : LocallyOfFiniteType r := by
      let _ : Smooth (r ≫ (Limits.prod.snd : U ⨯ U ⟶ U)) := hrsmooth
      exact locallyOfFiniteType_of_comp r Limits.prod.snd
    have hpb : LocallyOfFiniteType (pullback.snd r s) := by
      let _ : LocallyOfFiniteType r := hrft
      infer_instance
    have hproj : K.comp
        (fiberProductSnd (diag X) ((overBased.map p).comp g)) =
          overBased.map (pullback.snd r s) := by
      apply BasedFunctor.ext_of_toFunctor_eq
      rfl
    have hover := BasedFunctor.overHom_eq_of_iso (eqToIso hproj)
    have hover' :
        (K.comp (fiberProductSnd (diag X) ((overBased.map p).comp g))).overHom =
          pullback.snd r s :=
      hover.trans (BasedFunctor.overHom_map (pullback.snd r s))
    exact hover' ▸ hpb
  exact ⟨⟨fiber, W, K, hK, hKft⟩⟩

/-- A chosen compatible finite-type chart for each scheme-valued fiber of the
diagonal of an algebraic stack. -/
noncomputable def algebraicStackDiagonalFiniteTypeFiberChart
    (X : BasedCategory.{v₂, u₂} Scheme.{u}) [IsAlgebraicStack X]
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ prod X X) :
    AlgebraicStackDiagonalFiniteTypeFiberChart X T g :=
  Classical.choice (nonempty_algebraicStackDiagonalFiniteTypeFiberChart X T g)

/-- The diagonal of an algebraic stack is representable with the scheme-level
property of being locally of finite type. -/
theorem IsAlgebraicStack.representableWith_locallyOfFiniteType_diag_of_presentation
    (X : BasedCategory.{v₂, u₂} Scheme.{u}) [IsAlgebraicStack X] :
    BasedFunctor.RepresentableWith
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) (diag X) := by
  let D := fun (T : Scheme.{u}) (g : overBased T ⥤ᵇ prod X X) ↦
    algebraicStackDiagonalFiniteTypeFiberChart X T g
  have hle : (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) ≤
      (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) := by
    intro A B f hf
    let _ : Etale f := hf.2
    infer_instance
  have hlocal : ∀ ⦃S' S T : Scheme.{u}⦄ (p : S' ⟶ S) (f : S ⟶ T),
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p →
        (LocallyOfFiniteType f ↔ LocallyOfFiniteType (p ≫ f)) := by
    intro S' S T p f hp
    let _ : Surjective p := hp.1
    let _ : Etale p := hp.2
    let _ : Smooth p := inferInstance
    constructor
    · intro hf
      let _ : LocallyOfFiniteType f := hf
      infer_instance
    · intro hpf
      exact locallyOfFiniteType_of_comp_of_smooth_surjective p f hpf
  apply BasedFunctor.RepresentableWith.of_etaleLocalFiberRepresentations_and_goodLocalCharts
    (diag X) (fun T g ↦ (D T g).fiber) hle hlocal
  intro T g
  let d := D T g
  exact ⟨d.W, d.chart, d.chart_presentation, d.chart_locallyOfFiniteType⟩

end AlgebraicGeometry
