module

public import StacksAndModuli.API.AlgebraicStackDiagonal
public import StacksAndModuli.API.EtaleLocalGoodChart
public import StacksAndModuli.API.FiberProductPresentationProperty
public import StacksAndModuli.API.FiniteTypeSourceLocal
public import StacksAndModuli.API.FormallyUnramifiedSourceLocal
public import StacksAndModuli.API.PresentationBaseChange
public import StacksAndModuli.API.RepresentableWithProdMap
public import StacksAndModuli.API.SurjectiveEtaleSourceLocal

/-!
# The diagonal of a Deligne–Mumford stack

This file constructs the local charts used to prove that the diagonal of a
Deligne–Mumford stack is unramified.  Given two scheme-valued objects, an étale
presentation supplies simultaneous local lifts to its presentation scheme.  A scheme
atlas of the presentation's self-intersection is then pulled back along the pair of
lifts.  The resulting scheme chart is surjective étale over the diagonal fiber, while
its structural map is formally unramified and locally of finite type.

The categorical comparison is assembled from the magic-square and fiber-product
pasting equivalences.  `DeligneMumfordDiagonalFiberChart` keeps the chosen local base
change, the global algebraic-space representation, and the compatible good chart
together so that `RepresentableWith.of_etaleLocalFiberRepresentations_and_goodLocalCharts`
can descend the local calculation.

## Main result

* `IsDeligneMumfordStack.representableWith_unramified_diag_of_presentation`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry

/-- A pair of maps between representable prestacks is classified by their product
map, compatibly with the canonical comparison between the product scheme and the
product of representable prestacks. -/
noncomputable def overBasedProdLiftIso {V U : Scheme.{u}}
    (A B : overBased V ⥤ᵇ overBased U) :
    (overBased.map (Limits.prod.lift A.overHom B.overHom)).comp
        (overBasedProdComparison U U) ≅ prodLift A B := by
  let eA := Classical.choice (BasedFunctor.nonempty_iso_overBased_map A)
  let eB := Classical.choice (BasedFunctor.nonempty_iso_overBased_map B)
  let r := Limits.prod.lift A.overHom B.overHom
  let L := (overBased.map r).comp (overBasedProdComparison U U)
  let p₁ := fiberProductFst (overBased U).toBase (overBased U).toBase
  let p₂ := fiberProductSnd (overBased U).toBase (overBased U).toBase
  have h₁ : L.comp p₁ = overBased.map A.overHom := by
    rw [show L.comp p₁ = (overBased.map r).comp (overBased.map Limits.prod.fst) by
      change ((overBased.map r).comp (overBasedProdComparison U U)).comp p₁ = _
      rw [BasedFunctor.comp_assoc]
      congr 1]
    rw [← overBased.map_comp]
    change overBased.map (Limits.prod.lift A.overHom B.overHom ≫ Limits.prod.fst) = _
    rw [Limits.prod.lift_fst]
  have h₂ : L.comp p₂ = overBased.map B.overHom := by
    rw [show L.comp p₂ = (overBased.map r).comp (overBased.map Limits.prod.snd) by
      change ((overBased.map r).comp (overBasedProdComparison U U)).comp p₂ = _
      rw [BasedFunctor.comp_assoc]
      congr 1]
    rw [← overBased.map_comp]
    change overBased.map (Limits.prod.lift A.overHom B.overHom ≫ Limits.prod.snd) = _
    rw [Limits.prod.lift_snd]
  exact (prodLiftProjectionsIso L).symm ≪≫
    prodLiftIso ((eqToIso h₁).trans eA.symm) ((eqToIso h₂).trans eB.symm)

/-- Compatible global and étale-local chart data for a scheme-valued fiber of the
diagonal of a Deligne–Mumford stack. -/
structure DeligneMumfordDiagonalFiberChart
    (X : BasedCategory.{v₂, u₂} Scheme.{u}) [IsDeligneMumfordStack X]
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ prod X X) where
  /-- A global algebraic-space representation and the chosen étale local base. -/
  fiber : BasedFunctor.EtaleLocalFiberRepresentation (diag X) T g
  /-- The scheme furnishing the good local chart. -/
  W : Scheme.{u}
  /-- The chart of the diagonal fiber after the chosen local base change. -/
  chart : overBased W ⥤ᵇ
    fiberProduct (diag X) ((overBased.map fiber.localMap).comp g)
  /-- The local chart is a surjective étale presentation. -/
  chart_presentation : BasedFunctor.RepresentableWith
    (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) chart
  /-- The structural map of the local chart is unramified. -/
  chart_unramified :
    (@FormallyUnramified ⊓ @LocallyOfFiniteType : MorphismProperty Scheme.{u})
      (chart.comp (fiberProductSnd (diag X)
        ((overBased.map fiber.localMap).comp g))).overHom

/-- Every scheme-valued fiber of a Deligne–Mumford diagonal admits compatible global
algebraic-space and good étale-local chart data. -/
theorem nonempty_deligneMumfordDiagonalFiberChart
    (X : BasedCategory.{v₂, u₂} Scheme.{u}) [IsDeligneMumfordStack X]
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ prod X X) :
    Nonempty (DeligneMumfordDiagonalFiberChart X T g) := by
  let a := (twoYonedaEval (𝒳 := X) T).obj
    (g.comp (fiberProductFst X.toBase X.toBase))
  let b := (twoYonedaEval (𝒳 := X) T).obj
    (g.comp (fiberProductSnd X.toBase X.toBase))
  obtain ⟨U, P, hP⟩ := IsDeligneMumfordStack.exists_presentation (𝒳 := X)
  have hPsmooth := hP.mono (inf_le_inf le_rfl etale_le_smooth)
  obtain ⟨S, p, hpEtale, hpSurjective, liftA, liftB, ⟨eA⟩, ⟨eB⟩⟩ :=
    hPsmooth.exists_etale_surjective_pair_lift
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
  have hKunram :
      (@FormallyUnramified ⊓ @LocallyOfFiniteType : MorphismProperty Scheme.{u})
        (K.comp (fiberProductSnd (diag X) ((overBased.map p).comp g))).overHom := by
    have hr₂eq : r₂ = Rchart.comp (fiberProductSnd P P) := by
      rfl
    have hr₂prop : (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) r₂.overHom := by
      rw [hr₂eq]
      exact hP.2 U P R hR ER hER V q hq
    have hret : Etale (r ≫ (Limits.prod.snd : U ⨯ U ⟶ U)) := by
      rw [show r ≫ (Limits.prod.snd : U ⨯ U ⟶ U) = r₂.overHom by
        change Limits.prod.lift r₁.overHom r₂.overHom ≫ Limits.prod.snd = _
        exact Limits.prod.lift_snd _ _]
      exact hr₂prop.2
    have hrfu : FormallyUnramified r := by
      let _ : Etale (r ≫ (Limits.prod.snd : U ⨯ U ⟶ U)) := hret
      exact FormallyUnramified.of_comp r Limits.prod.snd
    have hrft : LocallyOfFiniteType r := by
      let _ : Etale (r ≫ (Limits.prod.snd : U ⨯ U ⟶ U)) := hret
      exact locallyOfFiniteType_of_comp r Limits.prod.snd
    have hpb :
        (@FormallyUnramified ⊓ @LocallyOfFiniteType : MorphismProperty Scheme.{u})
          (pullback.snd r s) := by
      let _ : FormallyUnramified r := hrfu
      let _ : LocallyOfFiniteType r := hrft
      exact ⟨MorphismProperty.pullback_snd r s hrfu, inferInstance⟩
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
  exact ⟨⟨fiber, W, K, hK, hKunram⟩⟩

/-- A chosen compatible chart for each scheme-valued fiber of a Deligne–Mumford
diagonal. -/
noncomputable def deligneMumfordDiagonalFiberChart
    (X : BasedCategory.{v₂, u₂} Scheme.{u}) [IsDeligneMumfordStack X]
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ prod X X) :
    DeligneMumfordDiagonalFiberChart X T g :=
  Classical.choice (nonempty_deligneMumfordDiagonalFiberChart X T g)

/-- The diagonal of a Deligne–Mumford stack is representable with the scheme-level
property "formally unramified and locally of finite type". -/
theorem IsDeligneMumfordStack.representableWith_unramified_diag_of_presentation
    (X : BasedCategory.{v₂, u₂} Scheme.{u}) [IsDeligneMumfordStack X] :
    BasedFunctor.RepresentableWith
      (@FormallyUnramified ⊓ @LocallyOfFiniteType : MorphismProperty Scheme.{u})
      (diag X) := by
  let P := (@FormallyUnramified ⊓ @LocallyOfFiniteType :
    MorphismProperty Scheme.{u})
  let D := fun (T : Scheme.{u}) (g : overBased T ⥤ᵇ prod X X) ↦
    deligneMumfordDiagonalFiberChart X T g
  have hle : (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) ≤ P := by
    intro A B f hf
    let _ : Etale f := hf.2
    exact ⟨inferInstance, inferInstance⟩
  have hlocal : ∀ ⦃S' S T : Scheme.{u}⦄ (p : S' ⟶ S) (f : S ⟶ T),
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p →
        (P f ↔ P (p ≫ f)) := by
    intro S' S T p f hp
    let _ : Surjective p := hp.1
    let _ : Etale p := hp.2
    let _ : Smooth p := inferInstance
    constructor
    · intro hf
      let _ : FormallyUnramified f := hf.1
      let _ : LocallyOfFiniteType f := hf.2
      exact ⟨MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hf.1,
        inferInstance⟩
    · intro hpf
      exact ⟨formallyUnramified_of_comp_of_smooth_surjective p f hpf.1,
        locallyOfFiniteType_of_comp_of_smooth_surjective p f hpf.2⟩
  apply BasedFunctor.RepresentableWith.of_etaleLocalFiberRepresentations_and_goodLocalCharts
    (diag X) (fun T g ↦ (D T g).fiber) hle hlocal
  intro T g
  let d := D T g
  exact ⟨d.W, d.chart, d.chart_presentation, d.chart_unramified⟩

end AlgebraicGeometry
