module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»
public import StacksAndModuli.API.PrestackProducts

/-!
# Fiber products of prestacks of presheaves

The prestack fiber product `𝒳_X ×_{𝒳_Y} 𝒮/S` of a morphism `ofPresheaf.map φ` of prestacks
of presheaves against a morphism from a representable prestack is represented by the object
representing the *presheaf* pullback of `φ` along the classifying morphism of `g`. Both
directions of that equivalence are constructed here — the projection direction is the one
that matters, because a statement quantifying over *every* representation of a fiber
product cannot be discharged by inverting a based functor (there is no based inverse:
`BasedFunctor.w` is an equality of functors).

Main results:
- `CategoryTheory.BasedFunctor.ofPresheafHom`: the 2-Yoneda classifying morphism
  `yoneda.obj S ⟶ Y` of a morphism `𝒮/S ⥤ᵇ ofPresheaf Y`, the `ofPresheaf` analogue of
  `BasedFunctor.overHom`, with `obj_hom_eq_ofPresheafHom`;
- `CategoryTheory.BasedCategory.ofPresheafFiberProductLift` and
  `ofPresheafFiberProductProj`, the two comparison morphisms, each an equivalence;
- `CategoryTheory.BasedCategory.isRepresentedBy_fiberProduct_ofPresheafMap`;
- `CategoryTheory.BasedCategory.overHom_comp_ofPresheafFiberProductProj`, which needs no
  equivalence hypothesis and is what lets a universally-quantified representation be
  compared with the canonical one.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section PresheafFiberProduct

open CategoryTheory Functor Limits Opposite CategoryTheory.BasedCategory

universe v₁ u₁ u

namespace CategoryTheory.BasedFunctor

open CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- The element of `Y(S)` classified by a morphism of prestacks `g : 𝒮/S ⥤ᵇ 𝒳_Y` into the
prestack associated to a presheaf `Y`: the value of `g` at the identity `𝟙 S`, read
through the Yoneda lemma as a morphism of presheaves `Mor(-, S) ⟶ Y`.

This is the analogue for `ofPresheaf` targets of
`CategoryTheory.BasedFunctor.overHom`, and like it is a bijection from 2-isomorphism
classes onto `Y(S)` by the 2-Yoneda lemma. -/
def ofPresheafHom {S : 𝒮} {Y : 𝒮ᵒᵖ ⥤ Type v₁} (g : overBased S ⥤ᵇ ofPresheaf Y) :
    yoneda.obj S ⟶ Y :=
  yoneda.map (eqToHom (g.w_obj (Over.mk (𝟙 S))).symm) ≫ (g.obj (Over.mk (𝟙 S))).hom

/-- The value of `g : 𝒮/S ⥤ᵇ 𝒳_Y` at an object `s : 𝒮/S` is the element of `Y` obtained by
pulling back the classified element `ĝ ∈ Y(S)` along the structure morphism of `s`. This
is the `ofPresheaf` analogue of
`CategoryTheory.BasedFunctor.obj_hom_eq_overHom`, and is proved the same way: evaluate
`g` on the canonical morphism `s ⟶ 𝟙 S` and transport with `Functor.congr_hom g.w`. -/
lemma obj_hom_eq_ofPresheafHom {S : 𝒮} {Y : 𝒮ᵒᵖ ⥤ Type v₁}
    (g : overBased S ⥤ᵇ ofPresheaf Y) (s : Over S) :
    (g.obj s).hom = yoneda.map (eqToHom (g.w_obj s) ≫ s.hom) ≫ ofPresheafHom g := by
  have h₁ := CostructuredArrow.w (g.map (Over.homMk s.hom : s ⟶ Over.mk (𝟙 S)))
  have h₂ : (g.map (Over.homMk s.hom : s ⟶ Over.mk (𝟙 S))).left =
      eqToHom (g.w_obj s) ≫ s.hom ≫ eqToHom (g.w_obj (Over.mk (𝟙 S))).symm := by
    have h₀ := Functor.congr_hom g.w (Over.homMk s.hom : s ⟶ Over.mk (𝟙 S))
    simp only [Functor.comp_map] at h₀
    exact h₀
  rw [← h₁, h₂]
  simp [ofPresheafHom]

/-- The underlying morphism of `𝒮` of the image of a morphism of `𝒮/S` under a morphism of
prestacks `𝒮/S ⥤ᵇ 𝒳_Y`, expressed through the identification of the bases. (The `w` field
of a morphism of based categories, read on morphisms.) -/
lemma toOfPresheaf_map_left {S : 𝒮} {Y : 𝒮ᵒᵖ ⥤ Type v₁}
    (g : overBased S ⥤ᵇ ofPresheaf Y) {s s' : Over S} (ψ : s ⟶ s') :
    (g.map ψ).left = eqToHom (g.w_obj s) ≫ ψ.left ≫ eqToHom (g.w_obj s').symm := by
  have h := Functor.congr_hom g.w ψ
  simp only [Functor.comp_map] at h
  exact h

end CategoryTheory.BasedFunctor

namespace CategoryTheory.BasedCategory

open CategoryTheory.BasedFunctor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {X Y : 𝒮ᵒᵖ ⥤ Type v₁} {φ : X ⟶ Y} {S : 𝒮}
  (g : overBased S ⥤ᵇ ofPresheaf Y)

/-- The comparison isomorphism of an object of the fiber product `𝒳_X ×_{𝒳_Y} 𝒮/S` lies
over the identity, so on underlying objects of `𝒮` it is the canonical identification of
the two components. -/
lemma FiberProductObj.ofPresheafMap_iso_hom_left (a : FiberProductObj (ofPresheaf.map φ) g) :
    a.iso.hom.left = eqToHom (a.over_eq.symm.trans (g.w_obj a.snd).symm) := by
  have := a.isHomLift
  have h := IsHomLift.fac' (ofPresheaf Y).p (𝟙 ((ofPresheaf X).p.obj a.fst)) a.iso.hom
  simpa using h

/-- An object of the fiber product `𝒳_X ×_{𝒳_Y} 𝒮/S` is precisely a commutative square: a
`T`-point of `X`, a morphism `T ⟶ S`, and the identification of their images in `Y`. -/
lemma FiberProductObj.ofPresheafMap_w (a : FiberProductObj (ofPresheaf.map φ) g) :
    a.fst.hom ≫ φ = yoneda.map (eqToHom a.over_eq.symm ≫ a.snd.hom) ≫ ofPresheafHom g := by
  have h1 := CostructuredArrow.w a.iso.hom
  rw [obj_hom_eq_ofPresheafHom g a.snd, FiberProductObj.ofPresheafMap_iso_hom_left g a] at h1
  simp only [ofPresheaf.map, CostructuredArrow.map_obj_hom] at h1
  rw [← h1]
  simp

/-- The second component of a morphism of the fiber product `𝒳_X ×_{𝒳_Y} 𝒮/S` induces, on
underlying objects of `𝒮`, the same morphism as the first component. -/
lemma FiberProductHom.ofPresheafMap_snd_left {a b : FiberProductObj (ofPresheaf.map φ) g}
    (ψ : a ⟶ b) :
    (FiberProductHom.snd ψ).left =
      eqToHom a.over_eq ≫ (FiberProductHom.fst ψ).left ≫ eqToHom b.over_eq.symm := by
  have := ψ.isHomLift
  have h := IsHomLift.fac' (overBased S).p ((ofPresheaf X).p.map (FiberProductHom.fst ψ))
    (FiberProductHom.snd ψ)
  simpa using h

variable (hφ : yoneda.relativelyRepresentable φ)

/-- The morphism `T ⟶ W` classified by an object of the fiber product
`𝒳_X ×_{𝒳_Y} 𝒮/S` over `T`, where `W` is the object of `𝒮` representing the presheaf
pullback `X ×_Y Mor(-,S)`: the universal property of the pullback applied to the
commutative square `FiberProductObj.ofPresheafMap_w`. -/
noncomputable def ofPresheafFiberProductLeftMap (a : FiberProductObj (ofPresheaf.map φ) g) :
    a.fst.left ⟶ hφ.pullback (ofPresheafHom g) :=
  hφ.lift a.fst.hom (eqToHom a.over_eq.symm ≫ a.snd.hom)
    (FiberProductObj.ofPresheafMap_w g a)

/-- The classified morphism `T ⟶ W` recovers the first component of the object. -/
lemma ofPresheafFiberProductLeftMap_fst (a : FiberProductObj (ofPresheaf.map φ) g) :
    yoneda.map (ofPresheafFiberProductLeftMap g hφ a) ≫ hφ.fst (ofPresheafHom g) = a.fst.hom :=
  hφ.lift_fst _ _ _

/-- The classified morphism `T ⟶ W` recovers the second component of the object. -/
lemma ofPresheafFiberProductLeftMap_snd (a : FiberProductObj (ofPresheaf.map φ) g) :
    ofPresheafFiberProductLeftMap g hφ a ≫ hφ.snd (ofPresheafHom g) =
      eqToHom a.over_eq.symm ≫ a.snd.hom :=
  hφ.lift_snd _ _ _

/-- The classified morphisms `T ⟶ W` are natural in the object of the fiber product. -/
lemma ofPresheafFiberProductLeftMap_naturality
    {a b : FiberProductObj (ofPresheaf.map φ) g} (ψ : a ⟶ b) :
    (FiberProductHom.fst ψ).left ≫ ofPresheafFiberProductLeftMap g hφ b =
      ofPresheafFiberProductLeftMap g hφ a := by
  refine hφ.hom_ext ?_ ?_
  · rw [Functor.map_comp, Category.assoc, ofPresheafFiberProductLeftMap_fst,
      ofPresheafFiberProductLeftMap_fst]
    exact CostructuredArrow.w (FiberProductHom.fst ψ)
  · rw [Category.assoc, ofPresheafFiberProductLeftMap_snd, ofPresheafFiberProductLeftMap_snd]
    have hw : (FiberProductHom.snd ψ).left ≫ (b.snd).hom = (a.snd).hom := Over.w _
    rw [FiberProductHom.ofPresheafMap_snd_left g (b := b) ψ] at hw
    have h3 := congrArg (fun t => eqToHom a.over_eq.symm ≫ t) hw
    simpa using h3

/-- The projection `𝒳_X ×_{𝒳_Y} 𝒮/S ⥤ᵇ 𝒮/W` of prestacks over `𝒮`, sending an object of the
fiber product to the morphism it classifies into the object `W` representing the presheaf
pullback. It is an equivalence
(`isEquivalence_ofPresheafFiberProductProj`), quasi-inverse to
`ofPresheafFiberProductLift`; it has to be written out by hand because a quasi-inverse of
a morphism of based categories is not a morphism of based categories. -/
noncomputable def ofPresheafFiberProductProj :
    fiberProduct (ofPresheaf.map φ) g ⥤ᵇ overBased (hφ.pullback (ofPresheafHom g)) where
  toFunctor :=
    { obj := fun a => Over.mk (ofPresheafFiberProductLeftMap g hφ a)
      map := fun {a b} ψ => Over.homMk (FiberProductHom.fst ψ).left
        (ofPresheafFiberProductLeftMap_naturality g hφ ψ)
      map_id := fun a => by ext; simp
      map_comp := fun ψ χ => by ext; simp }
  w := rfl

@[simp]
lemma ofPresheafFiberProductProj_obj (a : FiberProductObj (ofPresheaf.map φ) g) :
    (ofPresheafFiberProductProj g hφ).obj a = Over.mk (ofPresheafFiberProductLeftMap g hφ a) :=
  rfl

@[simp]
lemma ofPresheafFiberProductProj_map_left {a b : FiberProductObj (ofPresheaf.map φ) g}
    (ψ : a ⟶ b) :
    ((ofPresheafFiberProductProj g hφ).map ψ).left = (FiberProductHom.fst ψ).left :=
  rfl

/-- The comparison isomorphism attached to a morphism `T ⟶ W`: the two composites
`Mor(-,T) ⟶ X ⟶ Y` and `Mor(-,T) ⟶ Mor(-,S) ⟶ Y` agree, because the square defining `W`
commutes. -/
noncomputable def ofPresheafFiberProductLiftIso (w : Over (hφ.pullback (ofPresheafHom g))) :
    (ofPresheaf.map φ).obj
        (CostructuredArrow.mk (yoneda.map w.hom ≫ hφ.fst (ofPresheafHom g))) ≅
      g.obj (Over.mk (w.hom ≫ hφ.snd (ofPresheafHom g))) :=
  CostructuredArrow.isoMk
    (eqToIso (g.w_obj (Over.mk (w.hom ≫ hφ.snd (ofPresheafHom g)))).symm)
    (by
      rw [obj_hom_eq_ofPresheafHom g]
      simp only [ofPresheaf.map, CostructuredArrow.map_obj_hom, CostructuredArrow.mk_hom_eq_self,
        Over.mk_hom, eqToIso.hom, Category.assoc, hφ.w (ofPresheafHom g)]
      simp only [← Category.assoc, ← Functor.map_comp]
      simp)

/-- The morphism of prestacks `𝒮/W ⥤ᵇ 𝒳_X ×_{𝒳_Y} 𝒮/S` exhibiting the fiber product as
represented by the object `W` representing the presheaf pullback `X ×_Y Mor(-,S)`: a
morphism `T ⟶ W` is sent to the pair of its composites with the two projections of the
pullback, together with the comparison isomorphism
`ofPresheafFiberProductLiftIso`. -/
noncomputable def ofPresheafFiberProductLift :
    overBased (hφ.pullback (ofPresheafHom g)) ⥤ᵇ fiberProduct (ofPresheaf.map φ) g where
  toFunctor :=
    { obj := fun w =>
        { fst := CostructuredArrow.mk (yoneda.map w.hom ≫ hφ.fst (ofPresheafHom g))
          snd := Over.mk (w.hom ≫ hφ.snd (ofPresheafHom g))
          over_eq := rfl
          iso := ofPresheafFiberProductLiftIso g hφ w
          isHomLift := IsHomLift.of_fac' _ _ _ rfl (g.w_obj _)
            (by simp [ofPresheafFiberProductLiftIso]) }
      map := fun {w w'} t =>
        { fst := CostructuredArrow.homMk t.left
            (show yoneda.map t.left ≫ yoneda.map w'.hom ≫ hφ.fst (ofPresheafHom g) =
                yoneda.map w.hom ≫ hφ.fst (ofPresheafHom g) by
              rw [← Category.assoc, ← Functor.map_comp, Over.w t])
          snd := Over.homMk t.left
            (show t.left ≫ w'.hom ≫ hφ.snd (ofPresheafHom g) =
                w.hom ≫ hφ.snd (ofPresheafHom g) by
              rw [← Category.assoc, Over.w t])
          isHomLift := IsHomLift.of_fac' _ _ _ rfl rfl (by simp)
          w := by
            apply CostructuredArrow.hom_ext
            simp [ofPresheafFiberProductLiftIso, toOfPresheaf_map_left g, ofPresheaf.map] }
      map_id := fun w =>
        FiberProductHom.ext (by apply CostructuredArrow.hom_ext; simp) (by ext; simp)
      map_comp := fun t t' =>
        FiberProductHom.ext (by apply CostructuredArrow.hom_ext; simp) (by ext; simp) }
  w := rfl

@[simp]
lemma ofPresheafFiberProductLift_obj_fst (w : Over (hφ.pullback (ofPresheafHom g))) :
    ((ofPresheafFiberProductLift g hφ).obj w).fst =
      CostructuredArrow.mk (yoneda.map w.hom ≫ hφ.fst (ofPresheafHom g)) :=
  rfl

@[simp]
lemma ofPresheafFiberProductLift_obj_snd (w : Over (hφ.pullback (ofPresheafHom g))) :
    ((ofPresheafFiberProductLift g hφ).obj w).snd =
      Over.mk (w.hom ≫ hφ.snd (ofPresheafHom g)) :=
  rfl

@[simp]
lemma ofPresheafFiberProductLift_obj_iso (w : Over (hφ.pullback (ofPresheafHom g))) :
    ((ofPresheafFiberProductLift g hφ).obj w).iso = ofPresheafFiberProductLiftIso g hφ w :=
  rfl

@[simp]
lemma ofPresheafFiberProductLift_map_fst_left
    {w w' : Over (hφ.pullback (ofPresheafHom g))} (t : w ⟶ w') :
    (FiberProductHom.fst ((ofPresheafFiberProductLift g hφ).map t)).left = t.left :=
  rfl

@[simp]
lemma ofPresheafFiberProductLift_map_snd_left
    {w w' : Over (hφ.pullback (ofPresheafHom g))} (t : w ⟶ w') :
    (FiberProductHom.snd ((ofPresheafFiberProductLift g hφ).map t)).left = t.left :=
  rfl

/-- The morphism `T ⟶ W` classified by the object of the fiber product attached to a
morphism `T ⟶ W` is that morphism itself. -/
lemma ofPresheafFiberProductLeftMap_lift_obj (w : Over (hφ.pullback (ofPresheafHom g))) :
    ofPresheafFiberProductLeftMap g hφ ((ofPresheafFiberProductLift g hφ).obj w) = w.hom := by
  refine hφ.hom_ext ?_ ?_
  · rw [ofPresheafFiberProductLeftMap_fst]
    rfl
  · rw [ofPresheafFiberProductLeftMap_snd]
    simp

/-- The unit of the equivalence `𝒮/W ≌ 𝒳_X ×_{𝒳_Y} 𝒮/S`: the composite
`𝒮/W → 𝒳_X ×_{𝒳_Y} 𝒮/S → 𝒮/W` is the identity, by
`ofPresheafFiberProductLeftMap_lift_obj`. -/
noncomputable def ofPresheafFiberProductUnitIso :
    𝟭 (Over (hφ.pullback (ofPresheafHom g))) ≅
      (ofPresheafFiberProductLift g hφ).toFunctor ⋙ (ofPresheafFiberProductProj g hφ).toFunctor :=
  NatIso.ofComponents
    (fun w => Over.isoMk (Iso.refl _)
      (by simp [ofPresheafFiberProductProj, ofPresheafFiberProductLeftMap_lift_obj]))
    (fun t => by ext; simp [ofPresheafFiberProductProj, ofPresheafFiberProductLift])

/-- The counit of the equivalence `𝒮/W ≌ 𝒳_X ×_{𝒳_Y} 𝒮/S` at an object: an object of the
fiber product is recovered from the morphism `T ⟶ W` it classifies. -/
noncomputable def ofPresheafFiberProductCounitIsoApp
    (a : FiberProductObj (ofPresheaf.map φ) g) :
    (ofPresheafFiberProductLift g hφ).obj ((ofPresheafFiberProductProj g hφ).obj a) ≅ a :=
  FiberProductObj.isoMk
    (CostructuredArrow.isoMk (Iso.refl _) (by simp [ofPresheafFiberProductLeftMap_fst]))
    (Over.isoMk (eqToIso a.over_eq.symm) (by simp [ofPresheafFiberProductLeftMap_snd]))
    (IsHomLift.of_fac' _ _ _ rfl a.over_eq (by simp; exact (Category.id_comp _).symm))
    (by
      apply CostructuredArrow.hom_ext
      simp [ofPresheafFiberProductLiftIso, toOfPresheaf_map_left g, ofPresheaf.map,
        FiberProductObj.ofPresheafMap_iso_hom_left g a])

/-- The counit of the equivalence `𝒮/W ≌ 𝒳_X ×_{𝒳_Y} 𝒮/S`. -/
noncomputable def ofPresheafFiberProductCounitIso :
    (ofPresheafFiberProductProj g hφ).toFunctor ⋙ (ofPresheafFiberProductLift g hφ).toFunctor ≅
      𝟭 (fiberProduct (ofPresheaf.map φ) g).obj :=
  NatIso.ofComponents (fun a => ofPresheafFiberProductCounitIsoApp g hφ a)
    (fun ψ => by
      apply FiberProductHom.ext
      · simp [ofPresheafFiberProductCounitIsoApp, ofPresheafFiberProductLift,
          ofPresheafFiberProductProj]
      · apply Over.OverMorphism.ext
        simp [ofPresheafFiberProductCounitIsoApp, ofPresheafFiberProductLift,
          ofPresheafFiberProductProj, FiberProductHom.ofPresheafMap_snd_left g ψ])

/-- The fiber product `𝒳_X ×_{𝒳_Y} 𝒮/S` of prestacks is equivalent to the representable
prestack `𝒮/W`, where `W` is the object of `𝒮` representing the presheaf pullback
`X ×_Y Mor(-,S)`. -/
noncomputable def ofPresheafFiberProductEquivalence :
    Over (hφ.pullback (ofPresheafHom g)) ≌ (fiberProduct (ofPresheaf.map φ) g).obj :=
  Equivalence.mk (ofPresheafFiberProductLift g hφ).toFunctor
    (ofPresheafFiberProductProj g hφ).toFunctor
    (ofPresheafFiberProductUnitIso g hφ) (ofPresheafFiberProductCounitIso g hφ)

/-- The morphism of prestacks `𝒮/W ⥤ᵇ 𝒳_X ×_{𝒳_Y} 𝒮/S` is an equivalence. -/
lemma isEquivalence_ofPresheafFiberProductLift :
    (ofPresheafFiberProductLift g hφ).toFunctor.IsEquivalence :=
  (ofPresheafFiberProductEquivalence g hφ).isEquivalence_functor

/-- The projection `𝒳_X ×_{𝒳_Y} 𝒮/S ⥤ᵇ 𝒮/W` is an equivalence. -/
lemma isEquivalence_ofPresheafFiberProductProj :
    (ofPresheafFiberProductProj g hφ).toFunctor.IsEquivalence :=
  (ofPresheafFiberProductEquivalence g hφ).isEquivalence_inverse

/-- The fiber product of the prestack morphism attached to a morphism of presheaves
representable by objects of `𝒮`, along a morphism from a representable prestack, is
represented by the object of `𝒮` representing the corresponding pullback of presheaves. -/
lemma isRepresentedBy_fiberProduct_ofPresheafMap :
    (fiberProduct (ofPresheaf.map φ) g).IsRepresentedBy (hφ.pullback (ofPresheafHom g)) :=
  ⟨ofPresheafFiberProductLift g hφ, isEquivalence_ofPresheafFiberProductLift g hφ⟩

/-- The morphism of `𝒮` classified by a representation of the fiber product followed by the
second projection factors through the object `W` representing the presheaf pullback: it is
the morphism classified by the representation followed by
`ofPresheafFiberProductProj`, composed with the pullback projection `W ⟶ S`. -/
lemma overHom_comp_ofPresheafFiberProductProj {S' : 𝒮}
    (E : overBased S' ⥤ᵇ fiberProduct (ofPresheaf.map φ) g) :
    (E.comp (fiberProductSnd (ofPresheaf.map φ) g)).overHom =
      (E.comp (ofPresheafFiberProductProj g hφ)).overHom ≫ hφ.snd (ofPresheafHom g) := by
  simp only [BasedFunctor.overHom, Category.assoc]
  rw [show ((E.comp (ofPresheafFiberProductProj g hφ)).obj (Over.mk (𝟙 S'))).hom =
      ofPresheafFiberProductLeftMap g hφ (E.obj (Over.mk (𝟙 S'))) from rfl,
    ofPresheafFiberProductLeftMap_snd]
  simp
  rfl

end CategoryTheory.BasedCategory

end PresheafFiberProduct
