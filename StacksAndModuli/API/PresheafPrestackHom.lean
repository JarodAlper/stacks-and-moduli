module

public import StacksAndModuli.API.PresheafPrestackComparison
public import StacksAndModuli.API.PrestackProducts

/-!
# Morphisms between prestacks associated to presheaves

A based functor between categories of elements is, up to a based natural isomorphism,
induced by a unique morphism of the underlying presheaves. This file constructs the
underlying presheaf morphism and the comparison isomorphism explicitly.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite

universe v u

namespace CategoryTheory.BasedCategory

variable {C : Type u} [Category.{v} C] {X Y : Cᵒᵖ ⥤ Type v}

/-- The morphism of presheaves classified by a based functor between the associated
prestacks. -/
noncomputable def ofPresheafMapOfBasedFunctor
    (H : ofPresheaf X ⥤ᵇ ofPresheaf Y) : X ⟶ Y :=
  let E := CategoryTheory.BasedFunctor.id (ofPresheaf Y)
  let _ : E.toFunctor.IsEquivalence := by
    change CategoryTheory.Functor.IsEquivalence
      (CategoryTheory.Functor.id (ofPresheaf Y).obj)
    infer_instance
  ofPresheaf.comparison E H

/-- On a point of `X`, the classified presheaf morphism agrees with the image under the
based functor, after transport along its equality of base functors. -/
lemma ofPresheafMapOfBasedFunctor_app
    (H : ofPresheaf X ⥤ᵇ ofPresheaf Y) (d : (ofPresheaf X).obj) :
    d.hom ≫ ofPresheafMapOfBasedFunctor H =
      yoneda.map (eqToHom (H.w_obj d).symm) ≫ (H.obj d).hom := by
  let u := d.hom
  have hd : d = CostructuredArrow.mk u := CostructuredArrow.eq_mk d
  rw [hd]
  change u ≫ ofPresheafMapOfBasedFunctor H = _
  let E := CategoryTheory.BasedFunctor.id (ofPresheaf Y)
  let _ : E.toFunctor.IsEquivalence := by
    change CategoryTheory.Functor.IsEquivalence
      (CategoryTheory.Functor.id (ofPresheaf Y).obj)
    infer_instance
  have hcomp : u ≫ ofPresheafMapOfBasedFunctor H =
      ofPresheaf.comparisonHom E H u := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp]
    simp [ofPresheafMapOfBasedFunctor, ofPresheaf.comparison]
    rfl
  rw [hcomp, ofPresheaf.comparisonHom, ofPresheaf.ptObj_hom,
    ofPresheaf.pt_eq E (Iso.refl (H.obj (CostructuredArrow.mk u)))]
  simp only [ofPresheaf.baseIso, eqToIso_refl, Iso.refl_symm, Iso.trans_inv,
    Functor.mapIso_inv, Iso.refl_inv, CostructuredArrow.proj_map,
    CostructuredArrow.id_left, Category.comp_id, E]
  erw [Functor.map_id]
  simp

/-- Every based functor between prestacks associated to presheaves is isomorphic to the
functor induced by its classified morphism of presheaves. -/
noncomputable def ofPresheafMapOfBasedFunctorIso
    (H : ofPresheaf X ⥤ᵇ ofPresheaf Y) :
    ofPresheaf.map (ofPresheafMapOfBasedFunctor H) ≅ H :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun d ↦ CostructuredArrow.isoMk (eqToIso (H.w_obj d).symm)
        (ofPresheafMapOfBasedFunctor_app H d).symm)
      (fun {d e} q ↦ by
        apply CostructuredArrow.hom_ext
        have h := Functor.congr_hom H.w q
        have h' : (H.map q).left = eqToHom (H.w_obj d) ≫ q.left ≫
            eqToHom (H.w_obj e).symm := by
          simpa only [Functor.comp_map, CostructuredArrow.proj_map] using h
        change q.left ≫ eqToHom (H.w_obj e).symm =
          eqToHom (H.w_obj d).symm ≫ (H.map q).left
        rw [h']
        simp))
    (fun d ↦ by
      apply IsHomLift.of_fac' (ofPresheaf Y).p
        (𝟙 ((ofPresheaf X).p.obj d)) _ rfl (H.w_obj d)
      simp)

end CategoryTheory.BasedCategory
