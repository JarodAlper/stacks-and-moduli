module

public import StacksAndModuli.API.OverBasedProducts
public import StacksAndModuli.API.PresheafPrestackComparison

/-!
# Classifying maps from presheaves to products of representable prestacks

An equivalence from a representable prestack to a product of two representable
prestacks lets every map from a presheaf prestack into that product be classified by
a map of presheaves.  This file records the accompanying 2-isomorphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v u

namespace CategoryTheory.BasedCategory

variable {C : Type u} [Category.{v} C]
  {X Y : Cᵒᵖ ⥤ Type v} {S T : C}

/-- The pointwise formula for the presheaf map obtained by comparing an equivalence
with an arbitrary map into the same product of representable prestacks. -/
lemma ofPresheaf.comparison_app
    (E : ofPresheaf X ⥤ᵇ prod (overBased S) (overBased T))
    [E.toFunctor.IsEquivalence]
    (H : ofPresheaf Y ⥤ᵇ prod (overBased S) (overBased T))
    (d : (ofPresheaf Y).obj) :
    d.hom ≫ ofPresheaf.comparison E H =
      ofPresheaf.comparisonHom E H d.hom := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  simp [ofPresheaf.comparison]

/-- The object produced by the comparison morphism is the canonical point attached
to the image object, after transporting its base along the based-functor equality. -/
lemma ofPresheaf.map_comparison_obj_eq_ptObj
    (E : ofPresheaf X ⥤ᵇ prod (overBased S) (overBased T))
    [E.toFunctor.IsEquivalence]
    (H : ofPresheaf Y ⥤ᵇ prod (overBased S) (overBased T))
    (d : (ofPresheaf Y).obj) :
    (ofPresheaf.map (ofPresheaf.comparison E H)).obj d =
      ofPresheaf.ptObj E (H.obj d) (H.w_obj d).symm := by
  refine CostructuredArrow.obj_ext _ _ rfl ?_
  simp only [ofPresheaf.ptObj_hom, ofPresheaf.map,
    CostructuredArrow.map_obj_hom]
  simp only [CostructuredArrow.map_obj_left, ofPresheaf.ptObj_left,
    eqToHom_refl, Functor.map_id, Over.forget_obj, Category.id_comp]
  change ofPresheaf.comparisonHom E H d.hom =
    d.hom ≫ ofPresheaf.comparison E H
  exact (ofPresheaf.comparison_app E H d).symm

/-- A morphism in a product of representable prestacks is determined by the
underlying arrow of its first component. -/
lemma prodOver_hom_ext
    {a b : (prod (overBased S) (overBased T)).obj}
    (f g : a ⟶ b) (h : f.fst.left = g.fst.left) : f = g := by
  apply FiberProductHom.ext
  · exact Over.OverMorphism.ext h
  · apply Over.OverMorphism.ext
    have hf := f.w
    have hg := g.w
    change f.fst.left ≫ b.iso.hom = a.iso.hom ≫ f.snd.left at hf
    change g.fst.left ≫ b.iso.hom = a.iso.hom ≫ g.snd.left at hg
    rw [← cancel_epi a.iso.hom]
    rw [← hf, ← hg, h]

/-- The component of the comparison between a classified presheaf map and the
original map into a product of representable prestacks. -/
noncomputable def ofPresheaf.comparisonMapIsoApp
    (E : ofPresheaf X ⥤ᵇ prod (overBased S) (overBased T))
    [E.toFunctor.IsEquivalence]
    (H : ofPresheaf Y ⥤ᵇ prod (overBased S) (overBased T))
    (d : (ofPresheaf Y).obj) :
    ((ofPresheaf.map (ofPresheaf.comparison E H)).comp E).obj d ≅ H.obj d :=
  E.toFunctor.mapIso
      (eqToIso (ofPresheaf.map_comparison_obj_eq_ptObj E H d)) ≪≫
    ofPresheaf.ptObjIso E (H.obj d) (H.w_obj d).symm

/-- The comparison component lies over the identity of the base. -/
lemma ofPresheaf.comparisonMapIsoApp_isHomLift
    (E : ofPresheaf X ⥤ᵇ prod (overBased S) (overBased T))
    [E.toFunctor.IsEquivalence]
    (H : ofPresheaf Y ⥤ᵇ prod (overBased S) (overBased T))
    (d : (ofPresheaf Y).obj) :
    IsHomLift (prod (overBased S) (overBased T)).p
      (𝟙 ((ofPresheaf Y).p.obj d))
      (ofPresheaf.comparisonMapIsoApp E H d).hom := by
  apply IsHomLift.of_fac'
    (prod (overBased S) (overBased T)).p
    (𝟙 ((ofPresheaf Y).p.obj d)) _
    (((ofPresheaf.map (ofPresheaf.comparison E H)).comp E).w_obj d)
    (H.w_obj d)
  let hobj := ofPresheaf.map_comparison_obj_eq_ptObj E H d
  change (prod (overBased S) (overBased T)).p.map
      (E.map (eqToHom hobj) ≫
        (ofPresheaf.ptObjIso E (H.obj d) (H.w_obj d).symm).hom) = _
  rw [Functor.map_comp,
    ofPresheaf.ptObjIso_base E (H.obj d) (H.w_obj d).symm]
  have hmap := Functor.congr_hom E.w (eqToHom hobj)
  simp only [Functor.comp_map] at hmap
  rw [hmap, eqToHom_map]
  simp

/-- The map of presheaves classified by an arbitrary morphism into a product of
representable prestacks recovers that morphism after composing with the chosen
representing equivalence. -/
noncomputable def ofPresheaf.comparisonMapIso
    (E : ofPresheaf X ⥤ᵇ prod (overBased S) (overBased T))
    [E.toFunctor.IsEquivalence]
    (H : ofPresheaf Y ⥤ᵇ prod (overBased S) (overBased T)) :
    (ofPresheaf.map (ofPresheaf.comparison E H)).comp E ≅ H :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun d ↦ ofPresheaf.comparisonMapIsoApp E H d)
      (fun {d e} q ↦ by
        apply prodOver_hom_ext
        let A := (ofPresheaf.map (ofPresheaf.comparison E H)).comp E
        let _ : IsHomLift (ofPresheaf Y).p ((ofPresheaf Y).p.map q) q :=
          IsHomLift.map (ofPresheaf Y).p q
        let _ : IsHomLift (prod (overBased S) (overBased T)).p
            ((ofPresheaf Y).p.map q) (A.map q) :=
          A.preserves_isHomLift _ q
        let _ : IsHomLift (prod (overBased S) (overBased T)).p
            (𝟙 ((ofPresheaf Y).p.obj e))
            (ofPresheaf.comparisonMapIsoApp E H e).hom :=
          ofPresheaf.comparisonMapIsoApp_isHomLift E H e
        let _ : IsHomLift (prod (overBased S) (overBased T)).p
            ((ofPresheaf Y).p.map q)
            (A.map q ≫ (ofPresheaf.comparisonMapIsoApp E H e).hom) := by
          infer_instance
        let _ : IsHomLift (prod (overBased S) (overBased T)).p
            (𝟙 ((ofPresheaf Y).p.obj d))
            (ofPresheaf.comparisonMapIsoApp E H d).hom :=
          ofPresheaf.comparisonMapIsoApp_isHomLift E H d
        let _ : IsHomLift (prod (overBased S) (overBased T)).p
            ((ofPresheaf Y).p.map q) (H.map q) :=
          H.preserves_isHomLift _ q
        let _ : IsHomLift (prod (overBased S) (overBased T)).p
            ((ofPresheaf Y).p.map q)
            ((ofPresheaf.comparisonMapIsoApp E H d).hom ≫ H.map q) := by
          infer_instance
        have hleft := IsHomLift.fac' (prod (overBased S) (overBased T)).p
          ((ofPresheaf Y).p.map q)
          (A.map q ≫ (ofPresheaf.comparisonMapIsoApp E H e).hom)
        have hright := IsHomLift.fac' (prod (overBased S) (overBased T)).p
          ((ofPresheaf Y).p.map q)
          ((ofPresheaf.comparisonMapIsoApp E H d).hom ≫ H.map q)
        exact hleft.trans hright.symm))
    (fun d ↦ ofPresheaf.comparisonMapIsoApp_isHomLift E H d)

end CategoryTheory.BasedCategory
