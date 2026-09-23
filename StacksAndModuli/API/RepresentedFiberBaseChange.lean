module

public import StacksAndModuli.API.FiberProductEquivalence
public import StacksAndModuli.API.FiberProductLegIso
public import StacksAndModuli.API.FiberProductPostcomp
public import StacksAndModuli.API.PresheafOverComparison
public import StacksAndModuli.API.PresheafPrestackMapPullback

/-!
# Base change of a presheaf representation of a prestack fiber

If a presheaf represents a 2-fiber product whose first leg is a representable
prestack `C/T`, its projection to `C/T` classifies a canonical morphism to the
Yoneda presheaf of `T`.  Ordinary pullback of that morphism along `S → T` then
represents the corresponding base change of the original 2-fiber product.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {Ycat : BasedCategory.{v₂, u₂} C}
  {Zcat : BasedCategory.{v₃, u₃} C}
  {X : Functor Cᵒᵖ (Type v₁)} {S T : C}
  {F : BasedFunctor (overBased T) Ycat}
  {G : BasedFunctor Zcat Ycat}

/-- The morphism from a representing presheaf to the base scheme, classified by
the first projection of its representing equivalence. -/
noncomputable def representedFiberBaseMap
    (E : BasedFunctor (ofPresheaf X) (fiberProduct F G))
    [E.toFunctor.IsEquivalence] : X ⟶ yoneda.obj T :=
  ofPresheaf.comparison (ofPresheafYonedaToOverBased T)
    (E.comp (fiberProductFst F G))

/-- Pulling back a representing presheaf along a morphism of base objects represents
the corresponding base change of the original 2-fiber product. -/
theorem isRepresentedByPresheaf_fiber_baseChange
    [(fiberProduct F G).p.IsFiberedInGroupoids]
    (E : BasedFunctor (ofPresheaf X) (fiberProduct F G))
    [E.toFunctor.IsEquivalence] (p : S ⟶ T) :
    (fiberProduct ((overBased.map p).comp F) G).IsRepresentedByPresheaf
      (Limits.pullback (representedFiberBaseMap E) (yoneda.map p)) := by
  let π := representedFiberBaseMap E
  let H := E.comp (fiberProductFst F G)
  let L₀ := ofPresheafMapPullbackLift
    (φ := π) (ψ := yoneda.map p)
  let _ : L₀.toFunctor.IsEquivalence :=
    isEquivalence_ofPresheafMapPullbackLift
  let Q := ofPresheafYonedaToOverBased T
  let L₁ := fiberProductPostcomp (ofPresheaf.map π)
    (ofPresheaf.map (yoneda.map p)) Q
  let _ : L₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductPostcomp
      (ofPresheaf.map π) (ofPresheaf.map (yoneda.map p)) Q
  let η := ofPresheaf.comparisonOverMapIso
    (ofPresheafYonedaToOverBased T) H
  let L₂ := fiberProductMapLeftIso η
    ((ofPresheaf.map (yoneda.map p)).comp Q)
  let _ : L₂.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapLeftIso η
      ((ofPresheaf.map (yoneda.map p)).comp Q)
  let hright :
      (ofPresheaf.map (yoneda.map p)).comp Q =
        (ofPresheafYonedaToOverBased S).comp (overBased.map p) :=
    ofPresheaf_map_yoneda_comp_toOver p
  let L₃ := fiberProductMapRightIso H (eqToIso hright)
  let _ : L₃.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso H (eqToIso hright)
  let L₄ := fiberProductRightMap H (overBased.map p)
    (ofPresheafYonedaToOverBased S)
  let _ : L₄.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap H (overBased.map p)
      (ofPresheafYonedaToOverBased S)
  let L₅ := fiberProductSymm H (overBased.map p)
  let L₆ := fiberProductRightMap (overBased.map p)
    (fiberProductFst F G) E
  let _ : L₆.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap (overBased.map p)
      (fiberProductFst F G) E
  let L₇ := pasteFwd (overBased.map p) F G
  let K := ((((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).comp
    L₅).comp L₆).comp L₇
  refine ⟨K, ?_⟩
  let _ : (L₀.comp L₁).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans L₀.toFunctor L₁.toFunctor
  let _ : ((L₀.comp L₁).comp L₂).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans (L₀.comp L₁).toFunctor L₂.toFunctor
  let _ : (((L₀.comp L₁).comp L₂).comp L₃).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans ((L₀.comp L₁).comp L₂).toFunctor
      L₃.toFunctor
  let _ : ((((L₀.comp L₁).comp L₂).comp L₃).comp
      L₄).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans
      (((L₀.comp L₁).comp L₂).comp L₃).toFunctor L₄.toFunctor
  let _ : (((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).comp
      L₅).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans
      ((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).toFunctor
      L₅.toFunctor
  let _ : ((((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).comp
      L₅).comp L₆).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans
      (((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).comp
        L₅).toFunctor L₆.toFunctor
  exact Functor.isEquivalence_trans
    ((((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).comp
      L₅).comp L₆).toFunctor L₇.toFunctor

end CategoryTheory.BasedCategory
