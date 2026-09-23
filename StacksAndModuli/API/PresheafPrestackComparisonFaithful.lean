module

public import StacksAndModuli.API.PresheafPrestackComparison

/-!
# Comparing presheaf presentations of a faithful prestack

Two presheaf presentations of the same faithful prestack are related not only by
an isomorphism of the presheaves, but by a compatible based natural isomorphism
between the induced presentation morphisms.  Faithfulness of the projection
supplies the naturality equation from equality of the underlying base arrows.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {X Y : Cᵒᵖ ⥤ Type v₁}
  {𝒵 : BasedCategory.{v₂, u₂} C}

/-- The comparison presheaf map sends an object to the canonical point attached
to its image in the common target. -/
lemma ofPresheaf.map_comparison_faithful_obj_eq_ptObj
    (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    (H : ofPresheaf Y ⥤ᵇ 𝒵) (d : (ofPresheaf Y).obj) :
    (ofPresheaf.map (ofPresheaf.comparison E H)).obj d =
      ofPresheaf.ptObj E (H.obj d) (H.w_obj d).symm := by
  refine CostructuredArrow.obj_ext _ _ rfl ?_
  simp only [ofPresheaf.ptObj_hom, ofPresheaf.map,
    CostructuredArrow.map_obj_hom, CostructuredArrow.map_obj_left,
    ofPresheaf.ptObj_left, eqToHom_refl, Functor.map_id,
    Category.id_comp]
  change ofPresheaf.comparisonHom E H d.hom =
    d.hom ≫ ofPresheaf.comparison E H
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp]
  simp [ofPresheaf.comparison]

/-- The component comparing a presentation transported along the comparison
presheaf map with the second presentation. -/
noncomputable def ofPresheaf.comparisonFaithfulIsoApp
    (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    (H : ofPresheaf Y ⥤ᵇ 𝒵) (d : (ofPresheaf Y).obj) :
    ((ofPresheaf.map (ofPresheaf.comparison E H)).comp E).obj d ≅ H.obj d :=
  E.toFunctor.mapIso
      (eqToIso (ofPresheaf.map_comparison_faithful_obj_eq_ptObj E H d)) ≪≫
    ofPresheaf.ptObjIso E (H.obj d) (H.w_obj d).symm

/-- Each component of the comparison lies over the identity of its base object. -/
lemma ofPresheaf.comparisonFaithfulIsoApp_isHomLift
    (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    (H : ofPresheaf Y ⥤ᵇ 𝒵) (d : (ofPresheaf Y).obj) :
    IsHomLift 𝒵.p (𝟙 ((ofPresheaf Y).p.obj d))
      (ofPresheaf.comparisonFaithfulIsoApp E H d).hom := by
  apply IsHomLift.of_fac' 𝒵.p
    (𝟙 ((ofPresheaf Y).p.obj d)) _
    (((ofPresheaf.map (ofPresheaf.comparison E H)).comp E).w_obj d)
    (H.w_obj d)
  let hobj := ofPresheaf.map_comparison_faithful_obj_eq_ptObj E H d
  change 𝒵.p.map
      (E.map (eqToHom hobj) ≫
        (ofPresheaf.ptObjIso E (H.obj d) (H.w_obj d).symm).hom) = _
  rw [Functor.map_comp,
    ofPresheaf.ptObjIso_base E (H.obj d) (H.w_obj d).symm]
  have hmap := Functor.congr_hom E.w (eqToHom hobj)
  simp only [Functor.comp_map] at hmap
  rw [hmap, eqToHom_map]
  simp

/-- For a faithful prestack, the canonical isomorphism between two presheaf
presentations is compatible with their presentation morphisms. -/
noncomputable def ofPresheaf.comparisonFaithfulIso
    (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    (H : ofPresheaf Y ⥤ᵇ 𝒵) [𝒵.p.Faithful] :
    (ofPresheaf.map (ofPresheaf.comparison E H)).comp E ≅ H :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun d ↦ ofPresheaf.comparisonFaithfulIsoApp E H d)
      (fun {d e} q ↦ by
        apply 𝒵.p.map_injective
        let A := (ofPresheaf.map (ofPresheaf.comparison E H)).comp E
        let _ : IsHomLift (ofPresheaf Y).p ((ofPresheaf Y).p.map q) q :=
          IsHomLift.map (ofPresheaf Y).p q
        let _ : IsHomLift 𝒵.p ((ofPresheaf Y).p.map q)
            (A.map q) := A.preserves_isHomLift _ q
        let _ : IsHomLift 𝒵.p
            (𝟙 ((ofPresheaf Y).p.obj e))
            (ofPresheaf.comparisonFaithfulIsoApp E H e).hom :=
          ofPresheaf.comparisonFaithfulIsoApp_isHomLift E H e
        let _ : IsHomLift 𝒵.p ((ofPresheaf Y).p.map q)
            (A.map q ≫ (ofPresheaf.comparisonFaithfulIsoApp E H e).hom) := by
          infer_instance
        let _ : IsHomLift 𝒵.p
            (𝟙 ((ofPresheaf Y).p.obj d))
            (ofPresheaf.comparisonFaithfulIsoApp E H d).hom :=
          ofPresheaf.comparisonFaithfulIsoApp_isHomLift E H d
        let _ : IsHomLift 𝒵.p ((ofPresheaf Y).p.map q)
            (H.map q) := H.preserves_isHomLift _ q
        let _ : IsHomLift 𝒵.p ((ofPresheaf Y).p.map q)
            ((ofPresheaf.comparisonFaithfulIsoApp E H d).hom ≫ H.map q) := by
          infer_instance
        have hleft := IsHomLift.fac' 𝒵.p
          ((ofPresheaf Y).p.map q)
          (A.map q ≫ (ofPresheaf.comparisonFaithfulIsoApp E H e).hom)
        have hright := IsHomLift.fac' 𝒵.p
          ((ofPresheaf Y).p.map q)
          ((ofPresheaf.comparisonFaithfulIsoApp E H d).hom ≫ H.map q)
        exact hleft.trans hright.symm))
    (fun d ↦ ofPresheaf.comparisonFaithfulIsoApp_isHomLift E H d)

end CategoryTheory.BasedCategory
