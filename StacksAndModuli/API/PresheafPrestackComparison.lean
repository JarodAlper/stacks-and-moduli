module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»

/-!
# Comparing two presheaves that present the same prestack

The prestack `ofPresheaf X` of a presheaf `X` on a category `𝒮` remembers `X`: if two
presheaves `X` and `Y` have equivalent associated prestacks *over `𝒮`*, then `X ≅ Y`. This
file proves that, in the form used by the representability theory of §4.1: given a based
category `𝒵` and based functors `ofPresheaf X ⥤ᵇ 𝒵` and `ofPresheaf Y ⥤ᵇ 𝒵` whose
underlying functors are equivalences, `X` and `Y` are isomorphic
(`CategoryTheory.BasedCategory.ofPresheaf.comparisonIso`).

The construction never inverts a based functor — impossible, since `BasedFunctor.w` is an
*equality* of functors. Instead it uses that `ofPresheaf X → 𝒮` is a discrete fibration:
an object `w` of `𝒵` determines, through an equivalence `E : ofPresheaf X ⥤ᵇ 𝒵`, a
canonical `𝒵.p.obj w`-point `ofPresheaf.pt E w` of `X`, independent of every choice made
(`ofPresheaf.pt_eq`) and natural in `w` (`ofPresheaf.pt_naturality`). Reading the points of
`X` and of `Y` attached to the same objects of `𝒵` gives mutually inverse morphisms of
presheaves.

Main results:
- `CategoryTheory.BasedCategory.ofPresheaf.pt`: the point of `X` over `𝒵.p.obj w`
  attached to an object `w` of `𝒵` by an equivalence `ofPresheaf X ⥤ᵇ 𝒵`, with its
  characterization `ofPresheaf.pt_eq` and naturality `ofPresheaf.pt_naturality`;
- `CategoryTheory.BasedCategory.ofPresheaf.comparison` and
  `CategoryTheory.BasedCategory.ofPresheaf.comparisonIso`: the induced morphism `Y ⟶ X`
  and the isomorphism `Y ≅ X` for two presentations of the same based category;
- `CategoryTheory.BasedCategory.ofPresheaf.isEquivalence_map`: the prestack morphism
  induced by an isomorphism of presheaves is an equivalence;
- `CategoryTheory.BasedCategory.overBasedToOfPresheafYoneda_comp_map`: the comparison
  `𝒮/S ≃ ofPresheaf (Mor(-, S))` is natural in `S`.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false



section OfPresheafComparison

open CategoryTheory Functor Limits Opposite CategoryTheory.BasedCategory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {X Y : 𝒮ᵒᵖ ⥤ Type v₁}
  {𝒵 : BasedCategory.{v₂, u₂} 𝒮}

/-- An isomorphism `E(d) ≅ w` in `𝒵`, for `E : ofPresheaf X ⥤ᵇ 𝒵` a morphism of based
categories and `d` an object of `ofPresheaf X`, projects to an isomorphism between the base
object `d.left` of `d` and the base object of `w`. -/
def ofPresheaf.baseIso (E : ofPresheaf X ⥤ᵇ 𝒵) {d : (ofPresheaf X).obj} {w : 𝒵.obj}
    (α : E.obj d ≅ w) : d.left ≅ 𝒵.p.obj w :=
  (eqToIso (E.w_obj d)).symm ≪≫ 𝒵.p.mapIso α

/-- Let `E : ofPresheaf X ⥤ᵇ 𝒵` be a morphism of based categories over `𝒮` whose underlying
functor is an equivalence, and let `w` be an object of `𝒵`. Then `ofPresheaf.pt E w` is the
point of `X` over `𝒵.p.obj w` corresponding to `w`: transport along `E` of any preimage of
`w` in the category of elements of `X`. It does not depend on the choice of preimage
(`ofPresheaf.pt_eq`). -/
noncomputable def ofPresheaf.pt (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    (w : 𝒵.obj) : yoneda.obj (𝒵.p.obj w) ⟶ X :=
  yoneda.map (ofPresheaf.baseIso E (E.toFunctor.objObjPreimageIso w)).inv ≫
    (E.toFunctor.objPreimage w).hom

/-- The point `ofPresheaf.pt E w` is computed by *any* object `d` of the category of
elements of `X` together with *any* isomorphism `E(d) ≅ w`: the choices made in the
definition are irrelevant, because `E` is fully faithful. -/
lemma ofPresheaf.pt_eq (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    {d : (ofPresheaf X).obj} {w : 𝒵.obj} (α : E.obj d ≅ w) :
    ofPresheaf.pt E w = yoneda.map (ofPresheaf.baseIso E α).inv ≫ d.hom := by
  set d₀ := E.toFunctor.objPreimage w with hd₀
  set α₀ := E.toFunctor.objObjPreimageIso w with hα₀
  set φ : d₀ ⟶ d := E.toFunctor.preimage (α₀.hom ≫ α.inv) with hφ
  have hmap : E.map φ = α₀.hom ≫ α.inv := E.toFunctor.map_preimage _
  have hleft : φ.left = (ofPresheaf.baseIso E α₀).hom ≫ (ofPresheaf.baseIso E α).inv := by
    have h1 := Functor.congr_hom E.w φ
    simp only [Functor.comp_map] at h1
    rw [hmap] at h1
    simp only [Functor.map_comp] at h1
    simp only [ofPresheaf.baseIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, eqToIso.inv,
      Functor.mapIso_hom, Functor.mapIso_inv, eqToIso.hom, Iso.symm_inv, Category.assoc]
    have h2 : φ.left = eqToHom (E.w_obj d₀).symm ≫ (𝒵.p.map α₀.hom ≫ 𝒵.p.map α.inv) ≫
        eqToHom (E.w_obj d) := by
      rw [h1]; simp
    rw [h2]; simp
  have hw : yoneda.map φ.left ≫ d.hom = d₀.hom := CostructuredArrow.w φ
  rw [ofPresheaf.pt, ← hw, hleft]
  simp

/-- The point attached to the image `E(d)` of an object `d` of the category of elements of
`X` is `d` itself. -/
lemma ofPresheaf.pt_obj (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    (d : (ofPresheaf X).obj) :
    ofPresheaf.pt E (E.obj d) = yoneda.map (eqToHom (E.w_obj d)) ≫ d.hom := by
  rw [ofPresheaf.pt_eq E (Iso.refl (E.obj d))]
  simp [ofPresheaf.baseIso]

/-- The points `ofPresheaf.pt E w` are natural in `w`: a morphism `ψ : w ⟶ w'` of `𝒵`
pulls the point attached to `w'` back to the point attached to `w`, along the morphism
`𝒵.p.map ψ` of base objects. -/
lemma ofPresheaf.pt_naturality (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    {w w' : 𝒵.obj} (ψ : w ⟶ w') :
    yoneda.map (𝒵.p.map ψ) ≫ ofPresheaf.pt E w' = ofPresheaf.pt E w := by
  set d := E.toFunctor.objPreimage w with hd
  set α := E.toFunctor.objObjPreimageIso w with hα
  set d' := E.toFunctor.objPreimage w' with hd'
  set α' := E.toFunctor.objObjPreimageIso w' with hα'
  set φ : d ⟶ d' := E.toFunctor.preimage (α.hom ≫ ψ ≫ α'.inv) with hφ
  have hmap : E.map φ = α.hom ≫ ψ ≫ α'.inv := E.toFunctor.map_preimage _
  have h1 := Functor.congr_hom E.w φ
  simp only [Functor.comp_map] at h1
  rw [hmap] at h1
  simp only [Functor.map_comp] at h1
  have hleft : eqToHom (E.w_obj d) ≫ φ.left =
      (𝒵.p.map α.hom ≫ 𝒵.p.map ψ ≫ 𝒵.p.map α'.inv) ≫ eqToHom (E.w_obj d') := by
    rw [h1]; simp
  have hw : yoneda.map φ.left ≫ d'.hom = d.hom := CostructuredArrow.w φ
  have key : 𝒵.p.map ψ ≫ (ofPresheaf.baseIso E α').inv =
      (ofPresheaf.baseIso E α).inv ≫ φ.left := by
    simp only [ofPresheaf.baseIso, Iso.trans_inv, Iso.symm_inv, eqToIso.hom,
      Functor.mapIso_inv, Category.assoc]
    rw [hleft]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Category.id_comp]
  rw [ofPresheaf.pt_eq E α, ofPresheaf.pt_eq E α', ← hw, ← Category.assoc,
    ← Functor.map_comp, ← Category.assoc, ← Functor.map_comp, key]

/-- The object of the category of elements of `X` over a chosen base object `V`
attached to an object `w` of `𝒵` with `V = 𝒵.p.obj w`, namely `ofPresheaf.pt E w` read as a
`V`-point of `X`. -/
noncomputable def ofPresheaf.ptObj (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    {V : 𝒮} (w : 𝒵.obj) (h : V = 𝒵.p.obj w) : (ofPresheaf X).obj :=
  CostructuredArrow.mk (yoneda.map (eqToHom h) ≫ ofPresheaf.pt E w)

@[simp] lemma ofPresheaf.ptObj_left (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    {V : 𝒮} (w : 𝒵.obj) (h : V = 𝒵.p.obj w) : (ofPresheaf.ptObj E w h).left = V := rfl

@[simp] lemma ofPresheaf.ptObj_hom (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    {V : 𝒮} (w : 𝒵.obj) (h : V = 𝒵.p.obj w) :
    (ofPresheaf.ptObj E w h).hom = yoneda.map (eqToHom h) ≫ ofPresheaf.pt E w := rfl

/-- The comparison of `ofPresheaf.ptObj E w h` with the chosen preimage of `w` under `E`. -/
noncomputable def ofPresheaf.ptObjHomIso (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    {V : 𝒮} (w : 𝒵.obj) (h : V = 𝒵.p.obj w) :
    ofPresheaf.ptObj E w h ≅ E.toFunctor.objPreimage w :=
  CostructuredArrow.isoMk
    (eqToIso h ≪≫ (ofPresheaf.baseIso E (E.toFunctor.objObjPreimageIso w)).symm)
    (by simp [ofPresheaf.ptObj, ofPresheaf.pt])

lemma ofPresheaf.ptObjHomIso_hom_left (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    {V : 𝒮} (w : 𝒵.obj) (h : V = 𝒵.p.obj w) :
    (ofPresheaf.ptObjHomIso E w h).hom.left =
      eqToHom h ≫ (ofPresheaf.baseIso E (E.toFunctor.objObjPreimageIso w)).inv := by
  simp [ofPresheaf.ptObjHomIso]

/-- The object `ofPresheaf.ptObj E w h` of the category of elements of `X` is carried by `E`
to an object isomorphic to `w`; the isomorphism lies over the identity
(`ofPresheaf.ptObjIso_base`). -/
noncomputable def ofPresheaf.ptObjIso (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    {V : 𝒮} (w : 𝒵.obj) (h : V = 𝒵.p.obj w) : E.obj (ofPresheaf.ptObj E w h) ≅ w :=
  E.toFunctor.mapIso (ofPresheaf.ptObjHomIso E w h) ≪≫ E.toFunctor.objObjPreimageIso w

/-- The comparison isomorphism `E(ptObj E w h) ≅ w` lies over the identity of the base. -/
lemma ofPresheaf.ptObjIso_base (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    {V : 𝒮} (w : 𝒵.obj) (h : V = 𝒵.p.obj w) :
    𝒵.p.map (ofPresheaf.ptObjIso E w h).hom =
      eqToHom ((E.w_obj (ofPresheaf.ptObj E w h)).trans h) := by
  have h1 := Functor.congr_hom E.w (ofPresheaf.ptObjHomIso E w h).hom
  simp only [Functor.comp_map] at h1
  rw [ofPresheaf.ptObjIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
  rw [h1]
  simp only [CostructuredArrow.proj_map, ofPresheaf.ptObjHomIso_hom_left, ofPresheaf.baseIso,
    Iso.trans_inv, Iso.symm_inv, eqToIso.hom, Functor.mapIso_inv, Category.assoc,
    eqToHom_trans, eqToHom_trans_assoc]
  simp [← Functor.map_comp]

/-- Equal objects of the category of elements of `X` have equal points, up to the induced
identification of their base objects. -/
lemma ofPresheaf.hom_eq_of_obj_eq {a b : (ofPresheaf X).obj} (hab : a = b) :
    a.hom = yoneda.map (eqToHom (congrArg CostructuredArrow.left hab)) ≫ b.hom := by
  subst hab; simp

/-- Conversely to `ofPresheaf.ptObjIso`: an object `d` of the category of elements of `X`
whose image `E(d)` is isomorphic to `w` over the identity of the base *is* the object
attached to `w`. -/
lemma ofPresheaf.ptObj_eq_of_iso (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    {d : (ofPresheaf X).obj} {w : 𝒵.obj} (h : d.left = 𝒵.p.obj w) (α : E.obj d ≅ w)
    (hα : 𝒵.p.map α.hom = eqToHom ((E.w_obj d).trans h)) : ofPresheaf.ptObj E w h = d := by
  have hiso : 𝒵.p.mapIso α = eqToIso ((E.w_obj d).trans h) := Iso.ext hα
  rw [ofPresheaf.ptObj, ofPresheaf.pt_eq E α, ofPresheaf.baseIso, hiso]
  simp only [Iso.trans_inv, Iso.symm_inv, eqToIso.inv, eqToIso.hom, ← Category.assoc,
    ← Functor.map_comp, eqToHom_trans, eqToHom_refl]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact (CostructuredArrow.eq_mk d).symm

/-- Let `E : ofPresheaf X ⥤ᵇ 𝒵` be an equivalence and `E' : ofPresheaf Y ⥤ᵇ 𝒵` a morphism
of based categories. Reading a `V`-point of `Y` as an object of `𝒵` through `E'` and then
as a `V`-point of `X` through `E` gives the comparison map on `V`-points. -/
noncomputable def ofPresheaf.comparisonHom (E : ofPresheaf X ⥤ᵇ 𝒵)
    [E.toFunctor.IsEquivalence] (E' : ofPresheaf Y ⥤ᵇ 𝒵) {V : 𝒮} (u : yoneda.obj V ⟶ Y) :
    yoneda.obj V ⟶ X :=
  (ofPresheaf.ptObj E (E'.obj (CostructuredArrow.mk u))
    (E'.w_obj (CostructuredArrow.mk u)).symm).hom

/-- The comparison map on points is natural: it commutes with restriction along a morphism
`V' ⟶ V` of the base. -/
lemma ofPresheaf.comparisonHom_naturality (E : ofPresheaf X ⥤ᵇ 𝒵)
    [E.toFunctor.IsEquivalence] (E' : ofPresheaf Y ⥤ᵇ 𝒵) {V V' : 𝒮} (g : V' ⟶ V)
    (u : yoneda.obj V ⟶ Y) :
    ofPresheaf.comparisonHom E E' (yoneda.map g ≫ u) =
      yoneda.map g ≫ ofPresheaf.comparisonHom E E' u := by
  let ψ : (CostructuredArrow.mk (yoneda.map g ≫ u) : (ofPresheaf Y).obj) ⟶
      CostructuredArrow.mk u := CostructuredArrow.homMk g rfl
  have hψl : ψ.left = g := rfl
  have h1 := Functor.congr_hom E'.w ψ
  simp only [Functor.comp_map] at h1
  have h2 := ofPresheaf.pt_naturality E (E'.map ψ)
  rw [h1] at h2
  rw [ofPresheaf.comparisonHom, ofPresheaf.comparisonHom, ofPresheaf.ptObj_hom,
    ofPresheaf.ptObj_hom, ← h2]
  simp only [CostructuredArrow.proj_map, hψl, ← Category.assoc, ← Functor.map_comp,
    eqToHom_trans, eqToHom_refl, Category.id_comp]

/-- The two comparison maps on points attached to two presentations `ofPresheaf X ⥤ᵇ 𝒵` and
`ofPresheaf Y ⥤ᵇ 𝒵` of the same based category are mutually inverse. -/
lemma ofPresheaf.comparisonHom_comparisonHom (E : ofPresheaf X ⥤ᵇ 𝒵)
    [E.toFunctor.IsEquivalence] (E' : ofPresheaf Y ⥤ᵇ 𝒵) [E'.toFunctor.IsEquivalence]
    {V : 𝒮} (u : yoneda.obj V ⟶ Y) :
    ofPresheaf.comparisonHom E' E (ofPresheaf.comparisonHom E E' u) = u := by
  have hb := ofPresheaf.ptObjIso_base E (E'.obj (CostructuredArrow.mk u))
    (E'.w_obj (CostructuredArrow.mk u)).symm
  have hiso : 𝒵.p.mapIso (ofPresheaf.ptObjIso E (E'.obj (CostructuredArrow.mk u))
      (E'.w_obj (CostructuredArrow.mk u)).symm) =
      eqToIso ((E.w_obj (ofPresheaf.ptObj E (E'.obj (CostructuredArrow.mk u))
        (E'.w_obj (CostructuredArrow.mk u)).symm)).trans
        (E'.w_obj (CostructuredArrow.mk u)).symm) := Iso.ext hb
  have key : ofPresheaf.ptObj E'
      (E.obj (CostructuredArrow.mk (ofPresheaf.comparisonHom E E' u)))
      (E.w_obj (CostructuredArrow.mk (ofPresheaf.comparisonHom E E' u))).symm =
      CostructuredArrow.mk u := by
    refine ofPresheaf.ptObj_eq_of_iso E' _ (ofPresheaf.ptObjIso E _ _).symm ?_
    simp only [Iso.symm_hom, ← Functor.mapIso_inv, hiso, eqToIso.inv]
  rw [ofPresheaf.comparisonHom, ofPresheaf.hom_eq_of_obj_eq key]
  simp

/-- Let `E : ofPresheaf X ⥤ᵇ 𝒵` and `E' : ofPresheaf Y ⥤ᵇ 𝒵` be morphisms of based
categories over `𝒮`, with `E` an equivalence. The comparison maps on points assemble into a
morphism of presheaves `Y ⟶ X`. -/
noncomputable def ofPresheaf.comparison (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    (E' : ofPresheaf Y ⥤ᵇ 𝒵) : Y ⟶ X where
  app := fun V => ↾fun y => yonedaEquiv (ofPresheaf.comparisonHom E E' (yonedaEquiv.symm y))
  naturality := by
    intro V V' f
    apply ConcreteCategory.hom_ext
    intro y
    simp only [types_comp_apply, TypeCat.ofHom_apply]
    rw [yonedaEquiv_symm_map, ofPresheaf.comparisonHom_naturality, ← yonedaEquiv_naturality']

/-- The comparison morphisms attached to two presentations of the same based category
compose to the identity. -/
lemma ofPresheaf.comparison_comp (E : ofPresheaf X ⥤ᵇ 𝒵) [E.toFunctor.IsEquivalence]
    (E' : ofPresheaf Y ⥤ᵇ 𝒵) [E'.toFunctor.IsEquivalence] :
    ofPresheaf.comparison E E' ≫ ofPresheaf.comparison E' E = 𝟙 Y := by
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro y
  simp only [NatTrans.comp_app, types_comp_apply, ofPresheaf.comparison, TypeCat.ofHom_apply,
    NatTrans.id_app, types_id_apply, Equiv.symm_apply_apply]
  rw [ofPresheaf.comparisonHom_comparisonHom]
  simp

/-- **The prestack of a presheaf remembers the presheaf.** If the prestacks `ofPresheaf X`
and `ofPresheaf Y` associated to two presheaves on `𝒮` both present, over `𝒮`, the same
based category `𝒵` — that is, admit morphisms of based categories to `𝒵` whose underlying
functors are equivalences — then `X` and `Y` are isomorphic. -/
noncomputable def ofPresheaf.comparisonIso (E : ofPresheaf X ⥤ᵇ 𝒵)
    [E.toFunctor.IsEquivalence] (E' : ofPresheaf Y ⥤ᵇ 𝒵) [E'.toFunctor.IsEquivalence] :
    Y ≅ X where
  hom := ofPresheaf.comparison E E'
  inv := ofPresheaf.comparison E' E
  hom_inv_id := ofPresheaf.comparison_comp E E'
  inv_hom_id := ofPresheaf.comparison_comp E' E

/-- An isomorphism of presheaves induces an equivalence of the associated prestacks. -/
instance ofPresheaf.isEquivalence_map (φ : X ⟶ Y) [IsIso φ] :
    (ofPresheaf.map φ).toFunctor.IsEquivalence :=
  inferInstanceAs (CostructuredArrow.mapIso (S := yoneda) (asIso φ)).functor.IsEquivalence

/-- The equivalence `𝒮/S ≃ ofPresheaf (Mor(-, S))` is natural in `S`: composing it with the
morphism of prestacks induced by `Mor(-, f)` is the same as composing `f` first. -/
lemma overBasedToOfPresheafYoneda_comp_map {S T : 𝒮} (f : S ⟶ T) :
    (overBasedToOfPresheafYoneda S).comp (ofPresheaf.map (yoneda.map f)) =
      (overBased.map f).comp (overBasedToOfPresheafYoneda T) := by
  apply CategoryTheory.BasedFunctor.ext_of_toFunctor_eq
  refine CategoryTheory.Functor.ext (fun c => ?_) (fun c c' φ => ?_)
  · refine CostructuredArrow.obj_ext _ _ rfl ?_
    simp [CategoryTheory.BasedFunctor.comp, overBasedToOfPresheafYoneda, overBased.map,
      ofPresheaf.map, overToCostructuredArrowYoneda]
  · apply CostructuredArrow.hom_ext
    simp [CategoryTheory.BasedFunctor.comp, overBasedToOfPresheafYoneda, overBased.map,
      ofPresheaf.map, overToCostructuredArrowYoneda]

end CategoryTheory.BasedCategory

end OfPresheafComparison
