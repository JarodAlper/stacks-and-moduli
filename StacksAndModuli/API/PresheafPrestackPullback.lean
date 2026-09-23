module

public import StacksAndModuli.API.PresheafFiberProduct

/-!
# Presheaf pullbacks as prestack fiber products

For an arbitrary morphism of presheaves `φ : X ⟶ Y` and a morphism
`g : 𝒸/S ⟶ᵇ ofPresheaf Y`, this file identifies the prestack fiber product of
`ofPresheaf.map φ` and `g` with the prestack associated to the ordinary presheaf
pullback of `φ` and the element classified by `g`.

Unlike `PresheafFiberProduct`, no representability hypothesis is imposed on `φ`:
the representing object here is a presheaf rather than necessarily a scheme.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite

universe v u

namespace CategoryTheory.BasedCategory

open CategoryTheory.BasedFunctor

variable {C : Type u} [Category.{v} C] {X Y : Cᵒᵖ ⥤ Type v}
  {φ : X ⟶ Y} {S : C} (g : overBased S ⥤ᵇ ofPresheaf Y)

/-- The presheaf pullback classified by `g`. -/
noncomputable abbrev ofPresheafPullback : Cᵒᵖ ⥤ Type v :=
  Limits.pullback φ (BasedFunctor.ofPresheafHom g)

/-- The universal map from the Yoneda presheaf of an object of the prestack fiber
product to its classifying presheaf pullback. -/
noncomputable def ofPresheafPullbackLeftMap
    (a : FiberProductObj (ofPresheaf.map φ) g) :
    yoneda.obj a.fst.left ⟶ ofPresheafPullback (φ := φ) g :=
  Limits.pullback.lift a.fst.hom
    (yoneda.map (eqToHom a.over_eq.symm ≫ a.snd.hom))
    (FiberProductObj.ofPresheafMap_w g a)

@[reassoc]
lemma ofPresheafPullbackLeftMap_fst
    (a : FiberProductObj (ofPresheaf.map φ) g) :
    ofPresheafPullbackLeftMap g a ≫ Limits.pullback.fst φ (BasedFunctor.ofPresheafHom g) =
      a.fst.hom :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
lemma ofPresheafPullbackLeftMap_snd
    (a : FiberProductObj (ofPresheaf.map φ) g) :
    ofPresheafPullbackLeftMap g a ≫ Limits.pullback.snd φ (BasedFunctor.ofPresheafHom g) =
      yoneda.map (eqToHom a.over_eq.symm ≫ a.snd.hom) :=
  Limits.pullback.lift_snd _ _ _

lemma ofPresheafPullbackLeftMap_naturality
    {a b : FiberProductObj (ofPresheaf.map φ) g} (q : a ⟶ b) :
    yoneda.map q.fst.left ≫ ofPresheafPullbackLeftMap g b =
      ofPresheafPullbackLeftMap g a := by
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, ofPresheafPullbackLeftMap_fst,
      ofPresheafPullbackLeftMap_fst]
    exact CostructuredArrow.w q.fst
  · rw [Category.assoc, ofPresheafPullbackLeftMap_snd,
      ofPresheafPullbackLeftMap_snd]
    have hw : q.snd.left ≫ b.snd.hom = a.snd.hom := Over.w q.snd
    rw [FiberProductHom.ofPresheafMap_snd_left g (b := b) q] at hw
    have h := congrArg (fun t ↦ eqToHom a.over_eq.symm ≫ t) hw
    have hcancel : eqToHom a.over_eq.symm ≫ eqToHom a.over_eq = 𝟙 _ := by
      simp
    have hscheme : q.fst.left ≫ eqToHom b.over_eq.symm ≫ b.snd.hom =
        eqToHom a.over_eq.symm ≫ a.snd.hom := by
      calc
        q.fst.left ≫ eqToHom b.over_eq.symm ≫ b.snd.hom =
            (eqToHom a.over_eq.symm ≫ eqToHom a.over_eq) ≫
              (q.fst.left ≫ eqToHom b.over_eq.symm ≫ b.snd.hom) := by
                rw [hcancel, Category.id_comp]
        _ = eqToHom a.over_eq.symm ≫
              ((eqToHom a.over_eq ≫ q.fst.left ≫ eqToHom b.over_eq.symm) ≫
                b.snd.hom) := by simp only [Category.assoc]
        _ = eqToHom a.over_eq.symm ≫ a.snd.hom := h
    simpa only [← Functor.map_comp] using congrArg yoneda.map hscheme

/-- The projection from the prestack fiber product to the prestack of the ordinary
presheaf pullback. -/
noncomputable def ofPresheafPullbackProj :
    fiberProduct (ofPresheaf.map φ) g ⥤ᵇ
      ofPresheaf (ofPresheafPullback (φ := φ) g) where
  obj a := CostructuredArrow.mk (ofPresheafPullbackLeftMap g a)
  map q := CostructuredArrow.homMk q.fst.left
    (ofPresheafPullbackLeftMap_naturality g q)
  map_id a := by apply CostructuredArrow.hom_ext; simp
  map_comp q r := by apply CostructuredArrow.hom_ext; simp
  w := rfl

/-- The structural morphism to `S` classified by a point of the presheaf pullback. -/
noncomputable def ofPresheafPullbackRightMap
    (w : (ofPresheaf (ofPresheafPullback (φ := φ) g)).obj) : w.left ⟶ S :=
  Yoneda.fullyFaithful.preimage
    (w.hom ≫ Limits.pullback.snd φ (BasedFunctor.ofPresheafHom g))

lemma yoneda_map_ofPresheafPullbackRightMap
    (w : (ofPresheaf (ofPresheafPullback (φ := φ) g)).obj) :
    yoneda.map (ofPresheafPullbackRightMap g w) =
      w.hom ≫ Limits.pullback.snd φ (BasedFunctor.ofPresheafHom g) :=
  Yoneda.fullyFaithful.map_preimage _

/-- The comparison isomorphism that equips a point of the presheaf pullback with an
object of the prestack fiber product. -/
noncomputable def ofPresheafPullbackLiftIso
    (w : (ofPresheaf (ofPresheafPullback (φ := φ) g)).obj) :
    (ofPresheaf.map φ).obj
        (CostructuredArrow.mk
          (w.hom ≫ Limits.pullback.fst φ (BasedFunctor.ofPresheafHom g))) ≅
      g.obj (Over.mk (ofPresheafPullbackRightMap g w)) :=
  CostructuredArrow.isoMk
    (eqToIso (show
      ((ofPresheaf.map φ).obj
        (CostructuredArrow.mk
          (w.hom ≫ Limits.pullback.fst φ (BasedFunctor.ofPresheafHom g)))).left =
        (g.obj (Over.mk (ofPresheafPullbackRightMap g w))).left
      from (g.w_obj (Over.mk (ofPresheafPullbackRightMap g w))).symm))
    (by
      change yoneda.map
          (eqToHom (g.w_obj (Over.mk (ofPresheafPullbackRightMap g w))).symm) ≫
          (g.obj (Over.mk (ofPresheafPullbackRightMap g w))).hom =
        (w.hom ≫ Limits.pullback.fst φ (BasedFunctor.ofPresheafHom g)) ≫ φ
      rw [BasedFunctor.obj_hom_eq_ofPresheafHom g]
      calc
        yoneda.map (eqToHom (g.w_obj (Over.mk
              (ofPresheafPullbackRightMap g w))).symm) ≫
              (yoneda.map (eqToHom (g.w_obj (Over.mk
                (ofPresheafPullbackRightMap g w))) ≫
                ofPresheafPullbackRightMap g w) ≫
                BasedFunctor.ofPresheafHom g) =
            yoneda.map (ofPresheafPullbackRightMap g w) ≫
              BasedFunctor.ofPresheafHom g := by
                simp only [← Category.assoc, ← Functor.map_comp]
                simp
        _ = (w.hom ≫ Limits.pullback.snd φ
              (BasedFunctor.ofPresheafHom g)) ≫
              BasedFunctor.ofPresheafHom g := by
                rw [yoneda_map_ofPresheafPullbackRightMap]
        _ = w.hom ≫ (Limits.pullback.snd φ
              (BasedFunctor.ofPresheafHom g) ≫
              BasedFunctor.ofPresheafHom g) := Category.assoc _ _ _
        _ = w.hom ≫ (Limits.pullback.fst φ
              (BasedFunctor.ofPresheafHom g) ≫ φ) := by
                rw [Limits.pullback.condition]
        _ = (w.hom ≫ Limits.pullback.fst φ
              (BasedFunctor.ofPresheafHom g)) ≫ φ :=
                (Category.assoc _ _ _).symm)

/-- The lift from the prestack of the ordinary presheaf pullback to the prestack fiber
product. -/
noncomputable def ofPresheafPullbackLift :
    ofPresheaf (ofPresheafPullback (φ := φ) g) ⥤ᵇ
      fiberProduct (ofPresheaf.map φ) g where
  obj w :=
    { fst := CostructuredArrow.mk
        (w.hom ≫ Limits.pullback.fst φ (BasedFunctor.ofPresheafHom g))
      snd := Over.mk (ofPresheafPullbackRightMap g w)
      over_eq := rfl
      iso := ofPresheafPullbackLiftIso g w
      isHomLift := IsHomLift.of_fac' _ _ _ rfl (g.w_obj _)
        (by simp [ofPresheafPullbackLiftIso]) }
  map {w w'} t :=
    { fst := CostructuredArrow.homMk t.left (by
        change yoneda.map t.left ≫
            (w'.hom ≫ Limits.pullback.fst φ (BasedFunctor.ofPresheafHom g)) =
          w.hom ≫ Limits.pullback.fst φ (BasedFunctor.ofPresheafHom g)
        rw [← Category.assoc, CostructuredArrow.w t])
      snd := Over.homMk t.left (by
        change t.left ≫ ofPresheafPullbackRightMap g w' =
          ofPresheafPullbackRightMap g w
        apply Yoneda.fullyFaithful.map_injective
        rw [Functor.map_comp, yoneda_map_ofPresheafPullbackRightMap,
          yoneda_map_ofPresheafPullbackRightMap]
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun k ↦ k ≫ Limits.pullback.snd φ
            (BasedFunctor.ofPresheafHom g)) (CostructuredArrow.w t)))
      isHomLift := IsHomLift.of_fac' _ _ _ rfl rfl (by simp)
      w := by
        apply CostructuredArrow.hom_ext
        simp [ofPresheafPullbackLiftIso, BasedFunctor.toOfPresheaf_map_left g,
          ofPresheaf.map] }
  map_id w := by
    apply FiberProductHom.ext
    · apply CostructuredArrow.hom_ext
      simp
    · apply Over.OverMorphism.ext
      simp
  map_comp t t' := by
    apply FiberProductHom.ext
    · apply CostructuredArrow.hom_ext
      simp
    · apply Over.OverMorphism.ext
      simp
  w := rfl

lemma ofPresheafPullbackLeftMap_lift_obj
    (w : (ofPresheaf (ofPresheafPullback (φ := φ) g)).obj) :
    ofPresheafPullbackLeftMap g
      ((ofPresheafPullbackLift (φ := φ) g).obj w) = w.hom := by
  apply Limits.pullback.hom_ext
  · rw [ofPresheafPullbackLeftMap_fst]
    rfl
  · rw [ofPresheafPullbackLeftMap_snd]
    simpa [ofPresheafPullbackLift] using
      yoneda_map_ofPresheafPullbackRightMap g w

/-- The unit isomorphism for the presheaf-pullback comparison equivalence. -/
noncomputable def ofPresheafPullbackUnitIso :
    Functor.id (ofPresheaf (ofPresheafPullback (φ := φ) g)).obj ≅
      ((ofPresheafPullbackLift (φ := φ) g).toFunctor ⋙
        (ofPresheafPullbackProj (φ := φ) g).toFunctor : _ ⥤ _) :=
  NatIso.ofComponents
    (fun w ↦ CostructuredArrow.isoMk (Iso.refl _)
      (by simp [ofPresheafPullbackProj, ofPresheafPullbackLeftMap_lift_obj]))
    (fun t ↦ by
      apply CostructuredArrow.hom_ext
      simp [ofPresheafPullbackProj, ofPresheafPullbackLift])

lemma ofPresheafPullbackRightMap_proj_obj
    (a : FiberProductObj (ofPresheaf.map φ) g) :
    ofPresheafPullbackRightMap g
      ((ofPresheafPullbackProj (φ := φ) g).obj a) =
      eqToHom a.over_eq.symm ≫ a.snd.hom := by
  apply Yoneda.fullyFaithful.map_injective
  rw [yoneda_map_ofPresheafPullbackRightMap]
  change ofPresheafPullbackLeftMap g a ≫
      Limits.pullback.snd φ (BasedFunctor.ofPresheafHom g) =
    yoneda.map (eqToHom a.over_eq.symm ≫ a.snd.hom)
  exact ofPresheafPullbackLeftMap_snd g a

/-- The component of the counit isomorphism for the presheaf-pullback comparison. -/
noncomputable def ofPresheafPullbackCounitIsoApp
    (a : FiberProductObj (ofPresheaf.map φ) g) :
    (ofPresheafPullbackLift (φ := φ) g).obj
      ((ofPresheafPullbackProj (φ := φ) g).obj a) ≅ a :=
  FiberProductObj.isoMk
    (CostructuredArrow.isoMk (Iso.refl _)
      (by simpa [ofPresheafPullbackLift, ofPresheafPullbackProj] using
        (ofPresheafPullbackLeftMap_fst g a).symm))
    (Over.isoMk (eqToIso a.over_eq.symm)
      (ofPresheafPullbackRightMap_proj_obj g a).symm)
    (IsHomLift.of_fac' _ _ _ rfl a.over_eq
      (by
        simp only [Over.forget_obj, Over.forget_map, Over.isoMk_hom_left,
          eqToIso.hom, eqToHom_refl, CostructuredArrow.proj_map,
          CostructuredArrow.isoMk_hom_left, Iso.refl_hom, Category.id_comp]
        exact (Category.id_comp _).symm))
    (by
      apply CostructuredArrow.hom_ext
      simp [ofPresheafPullbackLift, ofPresheafPullbackProj,
        ofPresheafPullbackLiftIso, BasedFunctor.toOfPresheaf_map_left g,
        ofPresheaf.map, FiberProductObj.ofPresheafMap_iso_hom_left g a])

/-- The counit isomorphism for the presheaf-pullback comparison equivalence. -/
noncomputable def ofPresheafPullbackCounitIso :
    ((ofPresheafPullbackProj (φ := φ) g).toFunctor ⋙
        (ofPresheafPullbackLift (φ := φ) g).toFunctor : _ ⥤ _) ≅
      Functor.id (fiberProduct (ofPresheaf.map φ) g).obj :=
  NatIso.ofComponents (fun a ↦ ofPresheafPullbackCounitIsoApp (φ := φ) g a)
    (fun q ↦ by
      apply FiberProductHom.ext
      · apply CostructuredArrow.hom_ext
        simp [ofPresheafPullbackCounitIsoApp, ofPresheafPullbackLift,
          ofPresheafPullbackProj]
      · apply Over.OverMorphism.ext
        simp [ofPresheafPullbackCounitIsoApp, ofPresheafPullbackLift,
          ofPresheafPullbackProj, FiberProductHom.ofPresheafMap_snd_left g q])

/-- The prestack fiber product of a morphism between prestacks of presheaves against
a scheme point is the prestack of the corresponding ordinary presheaf pullback. -/
noncomputable def ofPresheafPullbackEquivalence :
    (ofPresheaf (ofPresheafPullback (φ := φ) g)).obj ≌
      (fiberProduct (ofPresheaf.map φ) g).obj :=
  Equivalence.mk (ofPresheafPullbackLift (φ := φ) g).toFunctor
    (ofPresheafPullbackProj (φ := φ) g).toFunctor
    (ofPresheafPullbackUnitIso (φ := φ) g)
    (ofPresheafPullbackCounitIso (φ := φ) g)

/-- The lift from the presheaf pullback is an equivalence. -/
lemma isEquivalence_ofPresheafPullbackLift :
    (ofPresheafPullbackLift (φ := φ) g).toFunctor.IsEquivalence :=
  (ofPresheafPullbackEquivalence (φ := φ) g).isEquivalence_functor

/-- The projection to the presheaf pullback is an equivalence. -/
lemma isEquivalence_ofPresheafPullbackProj :
    (ofPresheafPullbackProj (φ := φ) g).toFunctor.IsEquivalence :=
  (ofPresheafPullbackEquivalence (φ := φ) g).isEquivalence_inverse

/-- The prestack fiber product is represented by its ordinary presheaf pullback. -/
lemma isRepresentedByPresheaf_ofPresheafPullback :
    (fiberProduct (ofPresheaf.map φ) g).IsRepresentedByPresheaf
      (ofPresheafPullback (φ := φ) g) :=
  ⟨ofPresheafPullbackLift (φ := φ) g,
    isEquivalence_ofPresheafPullbackLift (φ := φ) g⟩

end CategoryTheory.BasedCategory
