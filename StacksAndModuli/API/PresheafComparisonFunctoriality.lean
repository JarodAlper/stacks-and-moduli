module

public import StacksAndModuli.API.PresheafPrestackComparisonFaithful
public import StacksAndModuli.API.PresheafOverComparison

/-!
# Functoriality of presheaf presentation comparisons

The canonical comparison between two presheaves presenting the same based
category is compatible with precomposition and with maps to representable
prestacks.  In particular, isomorphic maps from a representable presheaf into
a representable prestack have the same classifying map.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]

/-- Classifying a morphism between representable prestacks recovers its
underlying morphism under Yoneda. -/
theorem ofPresheaf.comparison_representable {S W : C}
    (A : overBased W ⥤ᵇ overBased S) :
    ofPresheaf.comparison (ofPresheafYonedaToOverBased S)
      ((ofPresheafYonedaToOverBased W).comp A) =
      yoneda.map A.overHom := by
  let Q := ofPresheafYonedaToOverBased S
  let H := (ofPresheafYonedaToOverBased W).comp A
  let c := ofPresheaf.comparison Q H
  let η := ofPresheaf.comparisonOverMapIso Q H
  let RW := overBasedToOfPresheafYoneda W
  let RS := overBasedToOfPresheafYoneda S
  let QW := ofPresheafYonedaToOverBased W
  let f : W ⟶ S := yonedaEquiv c
  have hc : yoneda.map f = c := yoneda_map_yonedaEquiv c
  have hnat : RW.comp (ofPresheaf.map c) =
      (overBased.map f).comp RS := by
    rw [← hc]
    exact overBasedToOfPresheafYoneda_comp_map f
  let e₀ : (RW.comp (ofPresheaf.map c)).comp Q ≅ RW.comp H :=
    (eqToIso (BasedFunctor.comp_assoc RW
      (ofPresheaf.map c) Q)).trans (isoWhiskerLeft RW η)
  let eLeft : (RW.comp (ofPresheaf.map c)).comp Q ≅
      overBased.map f :=
    (eqToIso (congrArg (fun L ↦ L.comp Q) hnat)).trans
      ((eqToIso (BasedFunctor.comp_assoc
        (overBased.map f) RS Q)).trans
        ((isoWhiskerLeft (overBased.map f)
          (overBasedYonedaCounitIso S)).trans
          (eqToIso (BasedFunctor.comp_id (overBased.map f)))))
  let eRight : RW.comp H ≅ A :=
    (eqToIso (BasedFunctor.comp_assoc RW QW A).symm).trans
      ((isoWhiskerRight (overBasedYonedaCounitIso W) A).trans
        (eqToIso (BasedFunctor.id_comp A)))
  let e : overBased.map f ≅ A := eLeft.symm.trans (e₀.trans eRight)
  have hf : f = A.overHom := by
    simpa only [BasedFunctor.overHom_map] using
      BasedFunctor.overHom_eq_of_iso e
  rw [← hf, hc]

/-- Isomorphic maps from a representable presheaf prestack to a representable
prestack have equal classifying maps of presheaves. -/
theorem ofPresheaf.comparison_yoneda_eq_of_iso {S W : C}
    (H K : ofPresheaf (yoneda.obj W) ⥤ᵇ overBased S)
    (e : H ≅ K) :
    ofPresheaf.comparison (ofPresheafYonedaToOverBased S) H =
      ofPresheaf.comparison (ofPresheafYonedaToOverBased S) K := by
  let Q := ofPresheafYonedaToOverBased S
  let RW := overBasedToOfPresheafYoneda W
  let RS := overBasedToOfPresheafYoneda S
  let cH := ofPresheaf.comparison Q H
  let cK := ofPresheaf.comparison Q K
  let fH : W ⟶ S := yonedaEquiv cH
  let fK : W ⟶ S := yonedaEquiv cK
  have hnatH : RW.comp (ofPresheaf.map cH) =
      (overBased.map fH).comp RS := by
    rw [← yoneda_map_yonedaEquiv cH]
    exact overBasedToOfPresheafYoneda_comp_map fH
  have hnatK : RW.comp (ofPresheaf.map cK) =
      (overBased.map fK).comp RS := by
    rw [← yoneda_map_yonedaEquiv cK]
    exact overBasedToOfPresheafYoneda_comp_map fK
  let eH₀ : (RW.comp (ofPresheaf.map cH)).comp Q ≅ RW.comp H :=
    (eqToIso (BasedFunctor.comp_assoc RW
      (ofPresheaf.map cH) Q)).trans
      (isoWhiskerLeft RW (ofPresheaf.comparisonOverMapIso Q H))
  let eK₀ : (RW.comp (ofPresheaf.map cK)).comp Q ≅ RW.comp K :=
    (eqToIso (BasedFunctor.comp_assoc RW
      (ofPresheaf.map cK) Q)).trans
      (isoWhiskerLeft RW (ofPresheaf.comparisonOverMapIso Q K))
  let eHLeft : (RW.comp (ofPresheaf.map cH)).comp Q ≅
      overBased.map fH :=
    (eqToIso (congrArg (fun L ↦ L.comp Q) hnatH)).trans
      ((eqToIso (BasedFunctor.comp_assoc
        (overBased.map fH) RS Q)).trans
        ((isoWhiskerLeft (overBased.map fH)
          (overBasedYonedaCounitIso S)).trans
          (eqToIso (BasedFunctor.comp_id (overBased.map fH)))))
  let eKLeft : (RW.comp (ofPresheaf.map cK)).comp Q ≅
      overBased.map fK :=
    (eqToIso (congrArg (fun L ↦ L.comp Q) hnatK)).trans
      ((eqToIso (BasedFunctor.comp_assoc
        (overBased.map fK) RS Q)).trans
        ((isoWhiskerLeft (overBased.map fK)
          (overBasedYonedaCounitIso S)).trans
          (eqToIso (BasedFunctor.comp_id (overBased.map fK)))))
  let eMaps : overBased.map fH ≅ overBased.map fK :=
    eHLeft.symm.trans
      (eH₀.trans ((isoWhiskerLeft RW e).trans
        (eK₀.symm.trans eKLeft)))
  have hf : fH = fK := by
    simpa only [BasedFunctor.overHom_map] using
      BasedFunctor.overHom_eq_of_iso eMaps
  calc
    cH = yoneda.map fH := (yoneda_map_yonedaEquiv cH).symm
    _ = yoneda.map fK := congrArg yoneda.map hf
    _ = cK := yoneda_map_yonedaEquiv cK

variable {X Y Y' : Cᵒᵖ ⥤ Type v₁}
  {Z : BasedCategory.{v₂, u₂} C}

/-- Comparison of presheaf presentations is compatible with precomposition by
a morphism of presheaves. -/
theorem ofPresheaf.comparison_precomp
    (Q : ofPresheaf X ⥤ᵇ Z) [Q.toFunctor.IsEquivalence]
    (c : Y' ⟶ Y) (H : ofPresheaf Y ⥤ᵇ Z) :
    ofPresheaf.comparison Q ((ofPresheaf.map c).comp H) =
      c ≫ ofPresheaf.comparison Q H := by
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro x
  simp only [ofPresheaf.comparison, Opposite.op_unop,
    ofPresheaf.comparisonHom, ofPresheaf.map,
    ofPresheaf.ptObj_hom, TypeCat.hom_ofHom, TypeCat.Fun.coe_mk,
    NatTrans.comp_app, comp_apply, EmbeddingLike.apply_eq_iff_eq]
  simp [BasedFunctor.comp, CostructuredArrow.map_mk]
  rw [← yonedaEquiv_symm_naturality_right V.unop c x]

/-- The canonical Yoneda presentation compared with itself gives the identity
map of the representable presheaf. -/
theorem ofPresheaf.comparison_yoneda_self {S : C} :
    ofPresheaf.comparison (ofPresheafYonedaToOverBased S)
      (ofPresheafYonedaToOverBased S) = 𝟙 (yoneda.obj S) := by
  simpa only [BasedFunctor.comp_id, BasedFunctor.overHom_id,
    Functor.map_id] using
    (ofPresheaf.comparison_representable
      (BasedFunctor.id (overBased S)))

/-- Classifying a presheaf map into a representable prestack recovers the
original presheaf map. -/
theorem ofPresheaf.comparison_map_toOver {S : C}
    {A : Cᵒᵖ ⥤ Type v₁} (f : A ⟶ yoneda.obj S) :
    ofPresheaf.comparison (ofPresheafYonedaToOverBased S)
      ((ofPresheaf.map f).comp (ofPresheafYonedaToOverBased S)) = f := by
  rw [ofPresheaf.comparison_precomp,
    ofPresheaf.comparison_yoneda_self, Category.comp_id]

end CategoryTheory.BasedCategory
