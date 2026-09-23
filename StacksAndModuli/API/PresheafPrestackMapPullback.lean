module

public import StacksAndModuli.API.PresheafPrestackPullback

/-!
# Pullbacks of morphisms between prestacks of presheaves

The prestack associated to an ordinary pullback of presheaves is equivalent to the
prestack 2-fiber product of the corresponding morphisms. This is the two-presheaf-leg
version of `PresheafPrestackPullback` and does not impose any representability
hypothesis on either morphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite

universe v u

namespace CategoryTheory.BasedCategory

variable {C : Type u} [Category.{v} C] {X Y Z : Cᵒᵖ ⥤ Type v}
  {φ : X ⟶ Y} {ψ : Z ⟶ Y}

/-- The ordinary presheaf pullback of `φ` and `ψ`. -/
noncomputable abbrev ofPresheafMapPullback : Cᵒᵖ ⥤ Type v :=
  Limits.pullback φ ψ

/-- The underlying base map of the gluing isomorphism in a fiber product of two
presheaf-induced prestack maps is the canonical equality transport. -/
lemma FiberProductObj.ofPresheafMaps_iso_hom_left
    (a : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map ψ)) :
    a.iso.hom.left = eqToHom a.over_eq.symm := by
  have := a.isHomLift
  have h := IsHomLift.fac' (ofPresheaf Y).p
    (𝟙 ((ofPresheaf X).p.obj a.fst)) a.iso.hom
  simpa using h

/-- The base map of the right component of a morphism in a fiber product of two
presheaf-induced prestack maps is determined by its left component. -/
lemma FiberProductHom.ofPresheafMaps_snd_left
    {a b : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map ψ)} (q : a ⟶ b) :
    q.snd.left = eqToHom a.over_eq ≫ q.fst.left ≫ eqToHom b.over_eq.symm := by
  have := q.isHomLift
  have h := IsHomLift.fac' (ofPresheaf Z).p
    ((ofPresheaf X).p.map q.fst) q.snd
  simpa using h

/-- The point of the ordinary presheaf pullback classified by an object of the prestack
fiber product. -/
noncomputable def ofPresheafMapPullbackLeftMap
    (a : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map ψ)) :
    yoneda.obj a.fst.left ⟶ ofPresheafMapPullback (φ := φ) (ψ := ψ) :=
  Limits.pullback.lift a.fst.hom
    (yoneda.map (eqToHom a.over_eq.symm) ≫ a.snd.hom)
    (by
      have hw := CostructuredArrow.w a.iso.hom
      rw [FiberProductObj.ofPresheafMaps_iso_hom_left a] at hw
      simpa only [ofPresheaf.map, CostructuredArrow.map_obj_hom,
        Category.assoc] using hw.symm)

/-- The first projection of the point classified by a fiber-product object. -/
@[reassoc]
lemma ofPresheafMapPullbackLeftMap_fst
    (a : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map ψ)) :
    ofPresheafMapPullbackLeftMap a ≫ Limits.pullback.fst φ ψ = a.fst.hom :=
  Limits.pullback.lift_fst _ _ _

/-- The second projection of the point classified by a fiber-product object. -/
@[reassoc]
lemma ofPresheafMapPullbackLeftMap_snd
    (a : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map ψ)) :
    ofPresheafMapPullbackLeftMap a ≫ Limits.pullback.snd φ ψ =
      yoneda.map (eqToHom a.over_eq.symm) ≫ a.snd.hom :=
  Limits.pullback.lift_snd _ _ _

/-- The point of the ordinary presheaf pullback classified by a fiber-product object is
natural in that object. -/
lemma ofPresheafMapPullbackLeftMap_naturality
    {a b : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map ψ)} (q : a ⟶ b) :
    yoneda.map q.fst.left ≫ ofPresheafMapPullbackLeftMap b =
      ofPresheafMapPullbackLeftMap a := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, ofPresheafMapPullbackLeftMap_fst,
      ofPresheafMapPullbackLeftMap_fst]
    exact CostructuredArrow.w q.fst
  · rw [Category.assoc, ofPresheafMapPullbackLeftMap_snd,
      ofPresheafMapPullbackLeftMap_snd]
    have hw := CostructuredArrow.w q.snd
    have hsnd := FiberProductHom.ofPresheafMaps_snd_left q
    have hbase : q.fst.left ≫ eqToHom b.over_eq.symm =
        eqToHom a.over_eq.symm ≫ q.snd.left := by
      rw [hsnd]
      simp
    rw [← Category.assoc, ← Functor.map_comp, hbase, Functor.map_comp,
      Category.assoc, hw]

/-- The projection from the prestack fiber product to the prestack of the ordinary
presheaf pullback. -/
noncomputable def ofPresheafMapPullbackProj :
    fiberProduct (ofPresheaf.map φ) (ofPresheaf.map ψ) ⥤ᵇ
      ofPresheaf (ofPresheafMapPullback (φ := φ) (ψ := ψ)) where
  obj a := CostructuredArrow.mk (ofPresheafMapPullbackLeftMap a)
  map q := CostructuredArrow.homMk q.fst.left
    (ofPresheafMapPullbackLeftMap_naturality q)
  map_id a := by apply CostructuredArrow.hom_ext; simp
  map_comp q r := by apply CostructuredArrow.hom_ext; simp
  w := rfl

/-- The canonical gluing isomorphism attached to a point of the ordinary presheaf
pullback. -/
noncomputable def ofPresheafMapPullbackLiftIso
    (w : (ofPresheaf (ofPresheafMapPullback (φ := φ) (ψ := ψ))).obj) :
    (ofPresheaf.map φ).obj
        (CostructuredArrow.mk (w.hom ≫ Limits.pullback.fst φ ψ)) ≅
      (ofPresheaf.map ψ).obj
        (CostructuredArrow.mk (w.hom ≫ Limits.pullback.snd φ ψ)) :=
  CostructuredArrow.isoMk (Iso.refl _)
    (by
      simp only [ofPresheaf.map, CostructuredArrow.map_obj_hom,
        CostructuredArrow.map_obj_left, CostructuredArrow.mk_left,
        Iso.refl_hom, Functor.map_id, Category.id_comp]
      change (w.hom ≫ Limits.pullback.snd φ ψ) ≫ ψ =
        (w.hom ≫ Limits.pullback.fst φ ψ) ≫ φ
      simpa only [Category.assoc] using congrArg (fun k ↦ w.hom ≫ k)
        (Limits.pullback.condition (f := φ) (g := ψ)).symm)

/-- The gluing isomorphism attached to a point of the ordinary pullback lies over the
identity. -/
@[simp]
lemma ofPresheafMapPullbackLiftIso_hom_left
    (w : (ofPresheaf (ofPresheafMapPullback (φ := φ) (ψ := ψ))).obj) :
    (ofPresheafMapPullbackLiftIso w).hom.left = 𝟙 _ :=
  CostructuredArrow.isoMk_hom_left _ _

set_option backward.defeqAttrib.useBackward true in
/-- The lift from the prestack of the ordinary presheaf pullback to the prestack fiber
product. -/
noncomputable def ofPresheafMapPullbackLift :
    ofPresheaf (ofPresheafMapPullback (φ := φ) (ψ := ψ)) ⥤ᵇ
      fiberProduct (ofPresheaf.map φ) (ofPresheaf.map ψ) where
  obj w :=
    { fst := CostructuredArrow.mk (w.hom ≫ Limits.pullback.fst φ ψ)
      snd := CostructuredArrow.mk (w.hom ≫ Limits.pullback.snd φ ψ)
      over_eq := rfl
      iso := ofPresheafMapPullbackLiftIso w
      isHomLift := IsHomLift.of_fac' _ _ _ rfl rfl
        (by simp [ofPresheafMapPullbackLiftIso]) }
  map {w w'} t :=
    { fst := CostructuredArrow.homMk t.left (by
        change yoneda.map t.left ≫
            (w'.hom ≫ Limits.pullback.fst φ ψ) =
          w.hom ≫ Limits.pullback.fst φ ψ
        rw [← Category.assoc, CostructuredArrow.w t])
      snd := CostructuredArrow.homMk t.left (by
        change yoneda.map t.left ≫
            (w'.hom ≫ Limits.pullback.snd φ ψ) =
          w.hom ≫ Limits.pullback.snd φ ψ
        rw [← Category.assoc, CostructuredArrow.w t])
      isHomLift := IsHomLift.of_fac' _ _ _ rfl rfl (by simp)
      w := by
        apply CostructuredArrow.hom_ext
        simp [ofPresheafMapPullbackLiftIso, ofPresheaf.map] }
  map_id w := by
    apply FiberProductHom.ext <;> apply CostructuredArrow.hom_ext <;> simp
  map_comp t t' := by
    apply FiberProductHom.ext <;> apply CostructuredArrow.hom_ext <;> simp
  w := rfl

/-- Classifying a lifted point recovers the original point of the ordinary presheaf
pullback. -/
lemma ofPresheafMapPullbackLeftMap_lift_obj
    (w : (ofPresheaf (ofPresheafMapPullback (φ := φ) (ψ := ψ))).obj) :
    ofPresheafMapPullbackLeftMap
      ((ofPresheafMapPullbackLift (φ := φ) (ψ := ψ)).obj w) = w.hom := by
  apply Limits.pullback.hom_ext
  · rw [ofPresheafMapPullbackLeftMap_fst]
    rfl
  · rw [ofPresheafMapPullbackLeftMap_snd]
    simp [ofPresheafMapPullbackLift]

/-- The unit isomorphism for the comparison between the ordinary presheaf pullback and
the prestack fiber product. -/
noncomputable def ofPresheafMapPullbackUnitIso :
    Functor.id (ofPresheaf (ofPresheafMapPullback (φ := φ) (ψ := ψ))).obj ≅
      ((ofPresheafMapPullbackLift (φ := φ) (ψ := ψ)).toFunctor ⋙
        (ofPresheafMapPullbackProj (φ := φ) (ψ := ψ)).toFunctor : _ ⥤ _) :=
  NatIso.ofComponents
    (fun w ↦ CostructuredArrow.isoMk (Iso.refl _)
      (by simp [ofPresheafMapPullbackProj,
        ofPresheafMapPullbackLeftMap_lift_obj]))
    (fun t ↦ by
      apply CostructuredArrow.hom_ext
      simp [ofPresheafMapPullbackProj, ofPresheafMapPullbackLift])

set_option backward.defeqAttrib.useBackward true in
/-- The component of the counit isomorphism for the comparison between the ordinary
presheaf pullback and the prestack fiber product. -/
noncomputable def ofPresheafMapPullbackCounitIsoApp
    (a : FiberProductObj (ofPresheaf.map φ) (ofPresheaf.map ψ)) :
    (ofPresheafMapPullbackLift (φ := φ) (ψ := ψ)).obj
      ((ofPresheafMapPullbackProj (φ := φ) (ψ := ψ)).obj a) ≅ a :=
  FiberProductObj.isoMk
    (CostructuredArrow.isoMk (Iso.refl _)
      (by simpa [ofPresheafMapPullbackLift, ofPresheafMapPullbackProj] using
        (ofPresheafMapPullbackLeftMap_fst a).symm))
    (CostructuredArrow.isoMk (eqToIso a.over_eq.symm)
      (by simpa [ofPresheafMapPullbackLift, ofPresheafMapPullbackProj] using
        (ofPresheafMapPullbackLeftMap_snd a).symm))
    (IsHomLift.of_fac' _ _ _ rfl a.over_eq
      (by simp [ofPresheafMapPullbackLift, ofPresheafMapPullbackProj]))
    (by
      apply CostructuredArrow.hom_ext
      simp [ofPresheafMapPullbackLift, ofPresheafMapPullbackProj,
        ofPresheaf.map, FiberProductObj.ofPresheafMaps_iso_hom_left])

/-- The counit isomorphism for the comparison between the ordinary presheaf pullback and
the prestack fiber product. -/
noncomputable def ofPresheafMapPullbackCounitIso :
    ((ofPresheafMapPullbackProj (φ := φ) (ψ := ψ)).toFunctor ⋙
        (ofPresheafMapPullbackLift (φ := φ) (ψ := ψ)).toFunctor : _ ⥤ _) ≅
      Functor.id (fiberProduct (ofPresheaf.map φ) (ofPresheaf.map ψ)).obj :=
  NatIso.ofComponents (fun a ↦ ofPresheafMapPullbackCounitIsoApp a)
    (fun q ↦ by
      apply FiberProductHom.ext
      · apply CostructuredArrow.hom_ext
        simp [ofPresheafMapPullbackCounitIsoApp, ofPresheafMapPullbackLift,
          ofPresheafMapPullbackProj]
      · apply CostructuredArrow.hom_ext
        simp [ofPresheafMapPullbackCounitIsoApp, ofPresheafMapPullbackLift,
          ofPresheafMapPullbackProj,
          FiberProductHom.ofPresheafMaps_snd_left q])

/-- The prestack of an ordinary presheaf pullback is equivalent to the corresponding
prestack 2-fiber product. -/
noncomputable def ofPresheafMapPullbackEquivalence :
    (ofPresheaf (ofPresheafMapPullback (φ := φ) (ψ := ψ))).obj ≌
      (fiberProduct (ofPresheaf.map φ) (ofPresheaf.map ψ)).obj :=
  Equivalence.mk (ofPresheafMapPullbackLift (φ := φ) (ψ := ψ)).toFunctor
    (ofPresheafMapPullbackProj (φ := φ) (ψ := ψ)).toFunctor
    (ofPresheafMapPullbackUnitIso (φ := φ) (ψ := ψ))
    (ofPresheafMapPullbackCounitIso (φ := φ) (ψ := ψ))

/-- The canonical lift from the prestack of the ordinary presheaf pullback is an
equivalence. -/
lemma isEquivalence_ofPresheafMapPullbackLift :
    (ofPresheafMapPullbackLift (φ := φ) (ψ := ψ)).toFunctor.IsEquivalence :=
  (ofPresheafMapPullbackEquivalence (φ := φ) (ψ := ψ)).isEquivalence_functor

/-- The prestack fiber product of two maps of presheaves is represented by their
ordinary presheaf pullback. -/
lemma isRepresentedByPresheaf_ofPresheafMapPullback :
    (fiberProduct (ofPresheaf.map φ) (ofPresheaf.map ψ)).IsRepresentedByPresheaf
      (ofPresheafMapPullback (φ := φ) (ψ := ψ)) :=
  ⟨ofPresheafMapPullbackLift (φ := φ) (ψ := ψ),
    isEquivalence_ofPresheafMapPullbackLift⟩

end CategoryTheory.BasedCategory
