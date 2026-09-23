module

public import StacksAndModuli.API.OverBasedYonedaEquivalence
public import StacksAndModuli.API.PresheafPrestackComparison

/-!
# Classifying maps from presheaves to representable prestacks

An equivalence from a presheaf prestack to a representable prestack `C/T` lets every
map from another presheaf prestack into `C/T` be classified by a map of presheaves.
This file records the accompanying based natural isomorphism and the covariance of
the canonical Yoneda-to-slice equivalence.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v u

namespace CategoryTheory.BasedCategory

variable {C : Type u} [Category.{v} C]
  {X Y : Functor Cᵒᵖ (Type v)} {S T : C}

/-- The pointwise formula for the presheaf map classified by a morphism into a
representable prestack. -/
lemma ofPresheaf.comparison_over_app
    (E : BasedFunctor (ofPresheaf X) (overBased T)) [E.toFunctor.IsEquivalence]
    (H : BasedFunctor (ofPresheaf Y) (overBased T)) (d : (ofPresheaf Y).obj) :
    d.hom ≫ ofPresheaf.comparison E H =
      ofPresheaf.comparisonHom E H d.hom := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  simp [ofPresheaf.comparison]

/-- The object produced by the classified map is the canonical point attached to
the image object. -/
lemma ofPresheaf.map_comparison_over_obj_eq_ptObj
    (E : BasedFunctor (ofPresheaf X) (overBased T)) [E.toFunctor.IsEquivalence]
    (H : BasedFunctor (ofPresheaf Y) (overBased T)) (d : (ofPresheaf Y).obj) :
    (ofPresheaf.map (ofPresheaf.comparison E H)).obj d =
      ofPresheaf.ptObj E (H.obj d) (H.w_obj d).symm := by
  refine CostructuredArrow.obj_ext _ _ rfl ?_
  simp only [ofPresheaf.ptObj_hom, ofPresheaf.map,
    CostructuredArrow.map_obj_hom, CostructuredArrow.map_obj_left,
    ofPresheaf.ptObj_left, eqToHom_refl, Functor.map_id, Over.forget_obj,
    Category.id_comp]
  change ofPresheaf.comparisonHom E H d.hom =
    d.hom ≫ ofPresheaf.comparison E H
  exact (ofPresheaf.comparison_over_app E H d).symm

/-- The component of the comparison between a classified map and the original map
into a representable prestack. -/
noncomputable def ofPresheaf.comparisonOverMapIsoApp
    (E : BasedFunctor (ofPresheaf X) (overBased T)) [E.toFunctor.IsEquivalence]
    (H : BasedFunctor (ofPresheaf Y) (overBased T)) (d : (ofPresheaf Y).obj) :
    ((ofPresheaf.map (ofPresheaf.comparison E H)).comp E).obj d ≅ H.obj d :=
  E.toFunctor.mapIso
      (eqToIso (ofPresheaf.map_comparison_over_obj_eq_ptObj E H d)) ≪≫
    ofPresheaf.ptObjIso E (H.obj d) (H.w_obj d).symm

/-- The comparison component lies over the identity of the base. -/
lemma ofPresheaf.comparisonOverMapIsoApp_isHomLift
    (E : BasedFunctor (ofPresheaf X) (overBased T)) [E.toFunctor.IsEquivalence]
    (H : BasedFunctor (ofPresheaf Y) (overBased T)) (d : (ofPresheaf Y).obj) :
    IsHomLift (overBased T).p (𝟙 ((ofPresheaf Y).p.obj d))
      (ofPresheaf.comparisonOverMapIsoApp E H d).hom := by
  apply IsHomLift.of_fac' (overBased T).p
    (𝟙 ((ofPresheaf Y).p.obj d)) _
    (((ofPresheaf.map (ofPresheaf.comparison E H)).comp E).w_obj d)
    (H.w_obj d)
  let hobj := ofPresheaf.map_comparison_over_obj_eq_ptObj E H d
  change (overBased T).p.map
      (E.map (eqToHom hobj) ≫
        (ofPresheaf.ptObjIso E (H.obj d) (H.w_obj d).symm).hom) = _
  rw [Functor.map_comp,
    ofPresheaf.ptObjIso_base E (H.obj d) (H.w_obj d).symm]
  have hmap := Functor.congr_hom E.w (eqToHom hobj)
  simp only [Functor.comp_map] at hmap
  rw [hmap, eqToHom_map]
  simp

/-- A classified presheaf map recovers the original morphism into a representable
prestack after composing with the chosen representing equivalence. -/
noncomputable def ofPresheaf.comparisonOverMapIso
    (E : BasedFunctor (ofPresheaf X) (overBased T)) [E.toFunctor.IsEquivalence]
    (H : BasedFunctor (ofPresheaf Y) (overBased T)) :
    (ofPresheaf.map (ofPresheaf.comparison E H)).comp E ≅ H :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun d ↦ ofPresheaf.comparisonOverMapIsoApp E H d)
      (fun {d e} q ↦ by
        apply Over.OverMorphism.ext
        let A := (ofPresheaf.map (ofPresheaf.comparison E H)).comp E
        let _ : IsHomLift (ofPresheaf Y).p ((ofPresheaf Y).p.map q) q :=
          IsHomLift.map (ofPresheaf Y).p q
        let _ : IsHomLift (overBased T).p ((ofPresheaf Y).p.map q)
            (A.map q) := A.preserves_isHomLift _ q
        let _ : IsHomLift (overBased T).p
            (𝟙 ((ofPresheaf Y).p.obj e))
            (ofPresheaf.comparisonOverMapIsoApp E H e).hom :=
          ofPresheaf.comparisonOverMapIsoApp_isHomLift E H e
        let _ : IsHomLift (overBased T).p ((ofPresheaf Y).p.map q)
            (A.map q ≫ (ofPresheaf.comparisonOverMapIsoApp E H e).hom) := by
          infer_instance
        let _ : IsHomLift (overBased T).p
            (𝟙 ((ofPresheaf Y).p.obj d))
            (ofPresheaf.comparisonOverMapIsoApp E H d).hom :=
          ofPresheaf.comparisonOverMapIsoApp_isHomLift E H d
        let _ : IsHomLift (overBased T).p ((ofPresheaf Y).p.map q)
            (H.map q) := H.preserves_isHomLift _ q
        let _ : IsHomLift (overBased T).p ((ofPresheaf Y).p.map q)
            ((ofPresheaf.comparisonOverMapIsoApp E H d).hom ≫ H.map q) := by
          infer_instance
        have hleft := IsHomLift.fac' (overBased T).p
          ((ofPresheaf Y).p.map q)
          (A.map q ≫ (ofPresheaf.comparisonOverMapIsoApp E H e).hom)
        have hright := IsHomLift.fac' (overBased T).p
          ((ofPresheaf Y).p.map q)
          ((ofPresheaf.comparisonOverMapIsoApp E H d).hom ≫ H.map q)
        exact hleft.trans hright.symm))
    (fun d ↦ ofPresheaf.comparisonOverMapIsoApp_isHomLift E H d)

/-- The canonical equivalence from a Yoneda presheaf prestack to a slice category
commutes with a morphism of representing objects. -/
lemma ofPresheaf_map_yoneda_comp_toOver (p : S ⟶ T) :
    (ofPresheaf.map (yoneda.map p)).comp (ofPresheafYonedaToOverBased T) =
      (ofPresheafYonedaToOverBased S).comp (overBased.map p) := by
  apply CategoryTheory.BasedFunctor.ext_of_toFunctor_eq
  refine CategoryTheory.Functor.ext (fun d ↦ ?_) (fun _ _ _ ↦ ?_)
  · change Over.mk (yonedaEquiv (d.hom ≫ yoneda.map p)) =
      Over.mk (yonedaEquiv d.hom ≫ p)
    apply congrArg Over.mk
    calc
      yonedaEquiv (d.hom ≫ yoneda.map p) =
          yonedaEquiv (yoneda.map (yonedaEquiv d.hom) ≫ yoneda.map p) := by
            rw [yoneda_map_yonedaEquiv]
      _ = yonedaEquiv d.hom ≫ p := by
        rw [← yoneda.map_comp, yonedaEquiv_yoneda_map]
  · apply Over.OverMorphism.ext
    simp [CategoryTheory.BasedFunctor.comp, ofPresheaf.map,
      ofPresheafYonedaToOverBased, costructuredArrowYonedaToOver,
      overBased.map]

end CategoryTheory.BasedCategory
