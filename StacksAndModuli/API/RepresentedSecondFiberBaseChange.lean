module

public import StacksAndModuli.API.PresheafComparisonFunctoriality
public import StacksAndModuli.API.RepresentedFiberBaseChange

/-!
# Base change of a representation along the second fiber-product projection

The base-change API for a represented 2-fiber product is stated with the
representable prestack as the first leg.  This file supplies the symmetric
version used when a morphism is tested by pulling back its target along a
scheme-valued point.  It also records compatibility of the resulting base map
with a scheme representation of the base-changed fiber.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {Xcat : BasedCategory.{v₂, u₂} C}
  {Ycat : BasedCategory.{v₃, u₃} C}
  {X Y : Cᵒᵖ ⥤ Type v₁} {S T W : C}
  (F : Xcat ⥤ᵇ Ycat) (g : overBased T ⥤ᵇ Ycat)

section FirstLeg

variable {F₀ : overBased T ⥤ᵇ Ycat} {G : Xcat ⥤ᵇ Ycat}

/-- The explicit equivalence used to represent the base change of a represented
fiber product along its first, representable leg. -/
noncomputable def representedFiberBaseChangeRepresentation
    [(fiberProduct F₀ G).p.IsFiberedInGroupoids]
    (E : ofPresheaf X ⥤ᵇ fiberProduct F₀ G)
    [E.toFunctor.IsEquivalence] (p : S ⟶ T) :
    ofPresheaf (pullback (representedFiberBaseMap E) (yoneda.map p)) ⥤ᵇ
      fiberProduct ((overBased.map p).comp F₀) G := by
  let π := representedFiberBaseMap E
  let H := E.comp (fiberProductFst F₀ G)
  let L₀ := ofPresheafMapPullbackLift
    (φ := π) (ψ := yoneda.map p)
  let Q := ofPresheafYonedaToOverBased T
  let L₁ := fiberProductPostcomp (ofPresheaf.map π)
    (ofPresheaf.map (yoneda.map p)) Q
  let η := ofPresheaf.comparisonOverMapIso
    (ofPresheafYonedaToOverBased T) H
  let L₂ := fiberProductMapLeftIso η
    ((ofPresheaf.map (yoneda.map p)).comp Q)
  let hright :
      (ofPresheaf.map (yoneda.map p)).comp Q =
        (ofPresheafYonedaToOverBased S).comp (overBased.map p) :=
    ofPresheaf_map_yoneda_comp_toOver p
  let L₃ := fiberProductMapRightIso H (eqToIso hright)
  let L₄ := fiberProductRightMap H (overBased.map p)
    (ofPresheafYonedaToOverBased S)
  let L₅ := fiberProductSymm H (overBased.map p)
  let L₆ := fiberProductRightMap (overBased.map p)
    (fiberProductFst F₀ G) E
  let L₇ := pasteFwd (overBased.map p) F₀ G
  exact ((((((L₀.comp L₁).comp L₂).comp L₃).comp L₄).comp
    L₅).comp L₆).comp L₇

/-- The explicit first-leg base-change representation is an equivalence. -/
theorem isEquivalence_representedFiberBaseChangeRepresentation
    [(fiberProduct F₀ G).p.IsFiberedInGroupoids]
    (E : ofPresheaf X ⥤ᵇ fiberProduct F₀ G)
    [E.toFunctor.IsEquivalence] (p : S ⟶ T) :
    (representedFiberBaseChangeRepresentation E p).toFunctor.IsEquivalence := by
  let π := representedFiberBaseMap E
  let H := E.comp (fiberProductFst F₀ G)
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
    (fiberProductFst F₀ G) E
  let _ : L₆.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap (overBased.map p)
      (fiberProductFst F₀ G) E
  let L₇ := pasteFwd (overBased.map p) F₀ G
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

/-- The explicit first-leg base-change representation commutes strictly with
the projection to the new base. -/
theorem representedFiberBaseChangeRepresentation_comp_fst
    [(fiberProduct F₀ G).p.IsFiberedInGroupoids]
    (E : ofPresheaf X ⥤ᵇ fiberProduct F₀ G)
    [E.toFunctor.IsEquivalence] (p : S ⟶ T) :
    (representedFiberBaseChangeRepresentation E p).comp
      (fiberProductFst ((overBased.map p).comp F₀) G) =
      (ofPresheaf.map (pullback.snd
        (representedFiberBaseMap E) (yoneda.map p))).comp
        (ofPresheafYonedaToOverBased S) := by
  apply BasedFunctor.ext_of_toFunctor_eq
  rfl

end FirstLeg

/-- The map to the base classified by the second projection of a represented
fiber product. -/
noncomputable def representedFiberSecondBaseMap
    (E : ofPresheaf X ⥤ᵇ fiberProduct F g)
    [E.toFunctor.IsEquivalence] : X ⟶ yoneda.obj T := by
  let L := fiberProductSymm F g
  let _ : L.toFunctor.IsEquivalence := inferInstance
  let _ : (E.comp L).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans E.toFunctor L.toFunctor
  exact representedFiberBaseMap (E.comp L)

/-- The explicit equivalence representing the base change along the second,
representable leg of a represented fiber product. -/
noncomputable def representedFiberSecondBaseChangeRepresentation
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    (E : ofPresheaf X ⥤ᵇ fiberProduct F g)
    [E.toFunctor.IsEquivalence] (p : S ⟶ T) :
    ofPresheaf
        (pullback (representedFiberSecondBaseMap F g E) (yoneda.map p)) ⥤ᵇ
      fiberProduct F ((overBased.map p).comp g) := by
  let L₀ := fiberProductSymm F g
  let E₀ := E.comp L₀
  let _ : E₀.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans E.toFunctor L₀.toFunctor
  let K := representedFiberBaseChangeRepresentation E₀ p
  let L₁ := fiberProductSymm ((overBased.map p).comp g) F
  exact K.comp L₁

/-- The explicit second-leg base-change representation is an equivalence. -/
theorem isEquivalence_representedFiberSecondBaseChangeRepresentation
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    (E : ofPresheaf X ⥤ᵇ fiberProduct F g)
    [E.toFunctor.IsEquivalence] (p : S ⟶ T) :
    (representedFiberSecondBaseChangeRepresentation F g E p).toFunctor.IsEquivalence := by
  let L₀ := fiberProductSymm F g
  let E₀ := E.comp L₀
  let _ : E₀.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans E.toFunctor L₀.toFunctor
  let K := representedFiberBaseChangeRepresentation E₀ p
  let _ : K.toFunctor.IsEquivalence :=
    isEquivalence_representedFiberBaseChangeRepresentation E₀ p
  let L₁ := fiberProductSymm ((overBased.map p).comp g) F
  exact Functor.isEquivalence_trans K.toFunctor L₁.toFunctor

noncomputable instance instIsEquivalenceRepresentedFiberSecondBaseChangeRepresentation
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    (E : ofPresheaf X ⥤ᵇ fiberProduct F g)
    [E.toFunctor.IsEquivalence] (p : S ⟶ T) :
    (representedFiberSecondBaseChangeRepresentation F g E p).toFunctor.IsEquivalence :=
  isEquivalence_representedFiberSecondBaseChangeRepresentation F g E p

/-- The explicit second-leg base-change representation commutes strictly with
the projection to the new base. -/
theorem representedFiberSecondBaseChangeRepresentation_comp_snd
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    (E : ofPresheaf X ⥤ᵇ fiberProduct F g)
    [E.toFunctor.IsEquivalence] (p : S ⟶ T) :
    (representedFiberSecondBaseChangeRepresentation F g E p).comp
      (fiberProductSnd F ((overBased.map p).comp g)) =
      (ofPresheaf.map (pullback.snd
        (representedFiberSecondBaseMap F g E) (yoneda.map p))).comp
        (ofPresheafYonedaToOverBased S) := by
  let L₀ := fiberProductSymm F g
  let E₀ := E.comp L₀
  let _ : E₀.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans E.toFunctor L₀.toFunctor
  simpa only [representedFiberSecondBaseChangeRepresentation,
    representedFiberSecondBaseMap, BasedFunctor.comp_assoc,
    fiberProductSymm_comp_snd] using
      (representedFiberBaseChangeRepresentation_comp_fst E₀ p)

/-- The structural map classified by the explicit second-leg base-change
representation is the ordinary pullback projection. -/
theorem representedFiberSecondBaseMap_baseChangeRepresentation
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    (E : ofPresheaf X ⥤ᵇ fiberProduct F g)
    [E.toFunctor.IsEquivalence] (p : S ⟶ T) :
    representedFiberSecondBaseMap F ((overBased.map p).comp g)
      (representedFiberSecondBaseChangeRepresentation F g E p) =
      pullback.snd (representedFiberSecondBaseMap F g E) (yoneda.map p) := by
  let L := representedFiberSecondBaseChangeRepresentation F g E p
  let μ := pullback.snd (representedFiberSecondBaseMap F g E) (yoneda.map p)
  simp only [representedFiberSecondBaseMap, representedFiberBaseMap,
    BasedFunctor.comp_assoc, fiberProductSymm_comp_fst,
    representedFiberSecondBaseChangeRepresentation_comp_snd]
  exact ofPresheaf.comparison_map_toOver μ

/-- Pulling a representation back along a morphism of base objects represents
the corresponding fiber product with the base-changed second leg. -/
theorem isRepresentedByPresheaf_fiber_secondBaseChange
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    (E : ofPresheaf X ⥤ᵇ fiberProduct F g)
    [E.toFunctor.IsEquivalence] (p : S ⟶ T) :
    (fiberProduct F ((overBased.map p).comp g)).IsRepresentedByPresheaf
      (pullback (representedFiberSecondBaseMap F g E) (yoneda.map p)) := by
  exact ⟨representedFiberSecondBaseChangeRepresentation F g E p,
    isEquivalence_representedFiberSecondBaseChangeRepresentation F g E p⟩

/-- The comparison isomorphism from the pullback presheaf representation to a
scheme representation commutes with their maps to the base. -/
theorem comparisonIso_hom_comp_representedFiberSecondBaseMap
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    (L : ofPresheaf Y ⥤ᵇ fiberProduct F g)
    [L.toFunctor.IsEquivalence]
    (K : overBased W ⥤ᵇ fiberProduct F g)
    [K.toFunctor.IsEquivalence] :
    let K' := (ofPresheafYonedaToOverBased W).comp K
    let _ : K'.toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans
        (ofPresheafYonedaToOverBased W).toFunctor K.toFunctor
    let e := ofPresheaf.comparisonIso L K'
    e.hom ≫ representedFiberSecondBaseMap F g L =
      yoneda.map (K.comp (fiberProductSnd F g)).overHom := by
  dsimp only
  simp only [ofPresheaf.comparisonIso,
    representedFiberSecondBaseMap, representedFiberBaseMap,
    BasedFunctor.comp_assoc, fiberProductSymm_comp_fst]
  let Z := fiberProduct F g
  let q := fiberProductSnd F g
  let Q := ofPresheafYonedaToOverBased T
  let QW := ofPresheafYonedaToOverBased W
  let K' := QW.comp K
  let c := ofPresheaf.comparison L K'
  letI : Z.p.Faithful := by
    apply Z.p.faithful_of_comp_essSurj L.toFunctor
    intro x y φ ψ h
    obtain ⟨φ', hφ⟩ := L.toFunctor.map_surjective φ
    obtain ⟨ψ', hψ⟩ := L.toFunctor.map_surjective ψ
    rw [← hφ, ← hψ]
    apply congrArg L.toFunctor.map
    apply (ofPresheaf Y).p.map_injective
    have hwφ := Functor.congr_hom L.w φ'
    have hwψ := Functor.congr_hom L.w ψ'
    simp only [Functor.comp_map] at hwφ hwψ
    rw [hφ] at hwφ
    rw [hψ] at hwψ
    rw [hwφ, hwψ] at h
    simpa only [cancel_epi, cancel_mono] using h
  let η := ofPresheaf.comparisonFaithfulIso L K'
  let ηq : (ofPresheaf.map c).comp (L.comp q) ≅ K'.comp q :=
    (eqToIso (BasedFunctor.comp_assoc
      (ofPresheaf.map c) L q).symm).trans (isoWhiskerRight η q)
  calc
    c ≫ ofPresheaf.comparison Q (L.comp q) =
        ofPresheaf.comparison Q
          ((ofPresheaf.map c).comp (L.comp q)) :=
      (ofPresheaf.comparison_precomp Q c (L.comp q)).symm
    _ = ofPresheaf.comparison Q (K'.comp q) :=
      ofPresheaf.comparison_yoneda_eq_of_iso _ _ ηq
    _ = ofPresheaf.comparison Q (QW.comp (K.comp q)) := by
      change ofPresheaf.comparison Q ((QW.comp K).comp q) = _
      exact congrArg (ofPresheaf.comparison Q)
        (BasedFunctor.comp_assoc QW K q)
    _ = yoneda.map (K.comp q).overHom :=
      ofPresheaf.comparison_representable (K.comp q)

end CategoryTheory.BasedCategory
