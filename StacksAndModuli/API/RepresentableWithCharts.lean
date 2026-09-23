module

public import StacksAndModuli.API.BasedFunctorEquivalence
public import StacksAndModuli.API.CommonCover
public import StacksAndModuli.API.FiberProductLegIso
public import StacksAndModuli.API.FiberProductPostcomp
public import StacksAndModuli.API.PresheafPrestackHom
public import StacksAndModuli.API.RelativelyRepresentableSourceEquivalence

/-!
# Chart criteria for representable morphisms of prestacks

This file packages two forms of independence from a chosen étale presentation. The first
compares two atlas morphisms of one algebraic-space realization directly. The second lets
one prove `RepresentableWith P` by constructing a single good chart of every base change.

It also records invariance of `RelativelyRepresentableWith` under an equivalence of target
prestacks, including universe-heterogeneous targets.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {X : Functor Cᵒᵖ (Type v₁)} {U₀ U W T : C}

/-- The structural morphism of a chart into a representable prestack is classified
by the composite of the chart map with the presheaf map classified by the target
functor. -/
lemma chart_map_eq_classified
    (H : BasedFunctor (ofPresheaf X) (overBased T))
    (q : yoneda.obj U ⟶ X) :
    yoneda.map (((overBasedToOfPresheafYoneda U).comp
      ((ofPresheaf.map q).comp H)).overHom) =
      q ≫ ofPresheafMapOfBasedFunctor
        (H.comp (overBasedToOfPresheafYoneda T)) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_yoneda_map]
  let K := H.comp (overBasedToOfPresheafYoneda T)
  let A := (overBasedToOfPresheafYoneda U).comp (ofPresheaf.map q)
  let d : (ofPresheaf X).obj := A.obj (Over.mk (𝟙 U))
  have h := ofPresheafMapOfBasedFunctor_app K d
  change d.hom ≫ ofPresheafMapOfBasedFunctor K =
    yoneda.map (eqToHom (K.w_obj d).symm) ≫ (K.obj d).hom at h
  have h' := congrArg
    (fun z : yoneda.obj U ⟶ yoneda.obj T ↦ yonedaEquiv z) h
  have hr := yonedaEquiv_comp
    (yoneda.map (eqToHom (K.w_obj d).symm)) (K.obj d).hom
  rw [yonedaEquiv_yoneda_map] at hr
  have h'' := h'.trans hr
  have hactual :
      ((overBasedToOfPresheafYoneda U).comp
        ((ofPresheaf.map q).comp H)).overHom =
      (K.obj d).hom.app (Opposite.op ((ofPresheaf X).p.obj d))
        (eqToHom (K.w_obj d).symm) := by
    rfl
  have hd : d.hom = q := by
    simp [d, A, BasedFunctor.comp, ofPresheaf.map,
      overBasedToOfPresheafYoneda, overToCostructuredArrowYoneda]
  have hc : d.hom ≫ ofPresheafMapOfBasedFunctor K =
      q ≫ ofPresheafMapOfBasedFunctor K :=
    congrArg (fun z ↦ z ≫ ofPresheafMapOfBasedFunctor K) hd
  have hy := congrArg yonedaEquiv hc
  exact hactual.trans (h''.symm.trans hy)

/-- Compatible maps from two representable charts into a presheaf induce the same map
of their common source to a representable target. -/
lemma atlas_overHom_eq (H : BasedFunctor (ofPresheaf X) (overBased T))
    (q₀ : yoneda.obj U₀ ⟶ X) (q : yoneda.obj U ⟶ X)
    (a₀ : W ⟶ U₀) (a : W ⟶ U)
    (h : yoneda.map a₀ ≫ q₀ = yoneda.map a ≫ q) :
    a₀ ≫ ((overBasedToOfPresheafYoneda U₀).comp
      ((ofPresheaf.map q₀).comp H)).overHom =
      a ≫ ((overBasedToOfPresheafYoneda U).comp
        ((ofPresheaf.map q).comp H)).overHom := by
  rw [← BasedFunctor.overHom_map a₀,
    ← BasedFunctor.overHom_map a]
  rw [← BasedFunctor.overHom_comp (overBased.map a₀)]
  rw [← BasedFunctor.overHom_comp (overBased.map a)]
  apply BasedFunctor.overHom_eq_of_iso
  rw [← BasedFunctor.comp_assoc (overBased.map a₀)
    (overBasedToOfPresheafYoneda U₀)]
  rw [← overBasedToOfPresheafYoneda_comp_map a₀]
  rw [← BasedFunctor.comp_assoc
    ((overBasedToOfPresheafYoneda W).comp
      (ofPresheaf.map (yoneda.map a₀))) (ofPresheaf.map q₀) H]
  rw [← BasedFunctor.comp_assoc (overBased.map a)
    (overBasedToOfPresheafYoneda U)]
  rw [← overBasedToOfPresheafYoneda_comp_map a]
  rw [← BasedFunctor.comp_assoc
    ((overBasedToOfPresheafYoneda W).comp
      (ofPresheaf.map (yoneda.map a))) (ofPresheaf.map q) H]
  apply eqToIso
  congr 1
  apply BasedFunctor.ext_of_toFunctor_eq
  fapply Functor.ext
  · intro d
    refine CostructuredArrow.obj_ext _ _ rfl ?_
    simpa [BasedFunctor.comp, overBasedToOfPresheafYoneda,
      overToCostructuredArrowYoneda, ofPresheaf.map, Category.assoc] using
      (congrArg (yoneda.map d.hom ≫ ·) h).symm
  · intro d e f
    apply CostructuredArrow.hom_ext
    simp [BasedFunctor.comp, overBasedToOfPresheafYoneda,
      overToCostructuredArrowYoneda, ofPresheaf.map]

end CategoryTheory.BasedCategory

namespace CategoryTheory.BasedFunctor

variable {C : Type u₁} [Category.{v₁} C]
  {Acat : BasedCategory.{v₂, u₂} C}
  {Bcat : BasedCategory.{v₃, u₃} C}
  {Bcat' : BasedCategory.{v₄, u₄} C}

/-- Relative representability with a morphism property is invariant under a based
natural isomorphism. -/
theorem RelativelyRepresentableWith.of_iso
    {P : MorphismProperty C} {F G : Acat ⥤ᵇ Bcat}
    (hF : F.RelativelyRepresentableWith P) (e : F ≅ G)
    [Acat.p.IsFiberedInGroupoids] [Bcat.p.IsFiberedInGroupoids] :
    G.RelativelyRepresentableWith P := by
  refine ⟨?_, ?_⟩
  · intro S g
    obtain ⟨S', E, hE⟩ := hF.1 S g
    let K := BasedCategory.fiberProductMapLeftIso e g
    let _ : E.toFunctor.IsEquivalence := hE
    let _ : K.toFunctor.IsEquivalence :=
      BasedCategory.isEquivalence_fiberProductMapLeftIso e g
    have hEK : (E.comp K).toFunctor.IsEquivalence := by
      change (E.toFunctor ⋙ K.toFunctor).IsEquivalence
      exact Functor.isEquivalence_trans E.toFunctor K.toFunctor
    exact ⟨S', E.comp K, hEK⟩
  · intro S g S' E hE
    let K := BasedCategory.fiberProductMapLeftIso e.symm g
    let _ : E.toFunctor.IsEquivalence := hE
    let _ : K.toFunctor.IsEquivalence :=
      BasedCategory.isEquivalence_fiberProductMapLeftIso e.symm g
    have hEK : (E.comp K).toFunctor.IsEquivalence := by
      change (E.toFunctor ⋙ K.toFunctor).IsEquivalence
      exact Functor.isEquivalence_trans E.toFunctor K.toFunctor
    have hP := hF.2 S g S' (E.comp K) hEK
    have hproj : K.comp (BasedCategory.fiberProductSnd F g) =
        BasedCategory.fiberProductSnd G g :=
      ext_of_toFunctor_eq rfl
    simpa [comp_assoc, hproj] using hP

/-- Relative representability with a morphism property may be cancelled across an
equivalence of source prestacks. -/
theorem RelativelyRepresentableWith.of_comp_isEquivalence
    {P : MorphismProperty C} {F : BasedFunctor Acat Bcat}
    (E : BasedFunctor Bcat' Acat)
    [Bcat'.p.IsFiberedInGroupoids] [Acat.p.IsFiberedInGroupoids]
    [Bcat.p.IsFiberedInGroupoids] [E.toFunctor.IsEquivalence]
    (hEF : (E.comp F).RelativelyRepresentableWith P) :
    F.RelativelyRepresentableWith P := by
  obtain ⟨J, ⟨α⟩, ⟨β⟩⟩ := exists_inverse_of_toFunctor E
  have hJ : J.toFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk' E.toFunctor
      ((BasedNatTrans.forgetful _ _).mapIso β).symm
      ((BasedNatTrans.forgetful _ _).mapIso α)
  let _ : J.toFunctor.IsEquivalence := hJ
  have hcomp := hEF.comp_of_isEquivalence J
  let e : J.comp (E.comp F) ≅ F :=
    (eqToIso (comp_assoc J E F).symm).trans
      ((BasedCategory.isoWhiskerRight β F).trans
        (eqToIso (comp_id F)))
  exact hcomp.of_iso e

/-- Postcomposing by an equivalence of target prestacks preserves relative
representability with a morphism property. -/
theorem RelativelyRepresentableWith.comp_target_isEquivalence
    {P : MorphismProperty C} {F : BasedFunctor Acat Bcat}
    (hF : F.RelativelyRepresentableWith P)
    (E : BasedFunctor Bcat Bcat')
    [Acat.p.IsFiberedInGroupoids] [Bcat.p.IsFiberedInGroupoids]
    [Bcat'.p.IsFiberedInGroupoids] [E.toFunctor.IsEquivalence] :
    (F.comp E).RelativelyRepresentableWith P := by
  classical
  refine ⟨?_, ?_⟩
  · intro S g
    obtain ⟨L, ⟨α⟩, ⟨β⟩⟩ := exists_inverse_of_toFunctor E
    let η : (g.comp L).comp E ≅ g :=
      (eqToIso (comp_assoc g L E)).trans
        ((BasedCategory.isoWhiskerLeft g β).trans
          (eqToIso (comp_id g)))
    let K₀ := BasedCategory.fiberProductPostcomp F (g.comp L) E
    let K₁ := BasedCategory.fiberProductMapRightIso (F.comp E) η
    let K := K₀.comp K₁
    have hK₀ : K₀.toFunctor.IsEquivalence :=
      BasedCategory.isEquivalence_fiberProductPostcomp F (g.comp L) E
    have hK₁ : K₁.toFunctor.IsEquivalence :=
      BasedCategory.isEquivalence_fiberProductMapRightIso (F.comp E) η
    have hK : K.toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans K₀.toFunctor K₁.toFunctor
    obtain ⟨S', R, hR⟩ := hF.1 S (g.comp L)
    exact ⟨S', R.comp K,
      Functor.isEquivalence_trans R.toFunctor K.toFunctor⟩
  · intro S g S' R hR
    obtain ⟨L, ⟨α⟩, ⟨β⟩⟩ := exists_inverse_of_toFunctor E
    let η : (g.comp L).comp E ≅ g :=
      (eqToIso (comp_assoc g L E)).trans
        ((BasedCategory.isoWhiskerLeft g β).trans
          (eqToIso (comp_id g)))
    let K₀ := BasedCategory.fiberProductPostcomp F (g.comp L) E
    let K₁ := BasedCategory.fiberProductMapRightIso (F.comp E) η
    let K := K₀.comp K₁
    have hK₀ : K₀.toFunctor.IsEquivalence :=
      BasedCategory.isEquivalence_fiberProductPostcomp F (g.comp L) E
    have hK₁ : K₁.toFunctor.IsEquivalence :=
      BasedCategory.isEquivalence_fiberProductMapRightIso (F.comp E) η
    have hK : K.toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans K₀.toFunctor K₁.toFunctor
    let _ : K.toFunctor.IsEquivalence := hK
    obtain ⟨J, ⟨γ⟩, ⟨δ⟩⟩ := exists_inverse_of_toFunctor K
    have hJ : J.toFunctor.IsEquivalence :=
      Functor.IsEquivalence.mk' K.toFunctor
        ((BasedNatTrans.forgetful _ _).mapIso δ).symm
        ((BasedNatTrans.forgetful _ _).mapIso γ)
    have hP := hF.2 S (g.comp L) S' (R.comp J)
      (Functor.isEquivalence_trans R.toFunctor J.toFunctor)
    have hK_snd : K.comp
        (BasedCategory.fiberProductSnd (F.comp E) g) =
        BasedCategory.fiberProductSnd F (g.comp L) := by
      rfl
    have eproj : J.comp (BasedCategory.fiberProductSnd F (g.comp L)) ≅
        BasedCategory.fiberProductSnd (F.comp E) g := by
      rw [← hK_snd, ← comp_assoc]
      exact (BasedCategory.isoWhiskerRight δ
        (BasedCategory.fiberProductSnd (F.comp E) g)).trans
        (eqToIso (id_comp _))
    have eprojR := BasedCategory.isoWhiskerLeft R eproj
    rw [comp_assoc] at hP
    rwa [overHom_eq_of_iso eprojR] at hP

/-- Relative representability with a property may be cancelled across an equivalence
of target prestacks. -/
theorem RelativelyRepresentableWith.of_comp_target_isEquivalence
    [Acat.p.IsFiberedInGroupoids] [Bcat.p.IsFiberedInGroupoids]
    [Bcat'.p.IsFiberedInGroupoids]
    {F : Acat ⥤ᵇ Bcat} {E : Bcat ⥤ᵇ Bcat'}
    (hE : E.toFunctor.IsEquivalence) {P : MorphismProperty C}
    (h : (F.comp E).RelativelyRepresentableWith P) :
    F.RelativelyRepresentableWith P := by
  let _ : E.toFunctor.IsEquivalence := hE
  obtain ⟨J, ⟨α⟩, ⟨β⟩⟩ := exists_inverse_of_toFunctor E
  have hJ : J.toFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk' E.toFunctor
      ((BasedNatTrans.forgetful _ _).mapIso β).symm
      ((BasedNatTrans.forgetful _ _).mapIso α)
  let _ : J.toFunctor.IsEquivalence := hJ
  have h' := h.comp_target_isEquivalence J
  let e : (F.comp E).comp J ≅ F :=
    (eqToIso (comp_assoc F E J)).trans
      ((BasedCategory.isoWhiskerLeft F α).trans
        (eqToIso (comp_id F)))
  exact h'.of_iso e

end CategoryTheory.BasedFunctor

namespace AlgebraicGeometry.BasedFunctor

variable {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}}
  {Ycat : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- To prove `RepresentableWith P`, it suffices to produce one étale presentation with
property `P` in every algebraic-space realization, provided `P` is étale-local on the
source. -/
theorem RepresentableWith.of_exists_presentation
    {P : MorphismProperty Scheme.{u}} {F : BasedFunctor Xcat Ycat}
    (hF : Representable F)
    (hlocal : ∀ ⦃S' S T : Scheme.{u}⦄ (p : S' ⟶ S) (f : S ⟶ T),
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p →
        (P f ↔ P (p ≫ f)))
    (hgood : ∀ (T : Scheme.{u})
      (g : BasedFunctor (overBased T) Ycat)
      (X : Functor Scheme.{u}ᵒᵖ (Type u)), IsAlgebraicSpace X →
      ∀ (E : BasedFunctor (ofPresheaf X)
        (BasedCategory.fiberProduct F g)),
        E.toFunctor.IsEquivalence →
        ∃ (U : Scheme.{u}) (q : yoneda.obj U ⟶ X),
          MorphismProperty.presheaf
            (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) q ∧
          P ((overBasedToOfPresheafYoneda U).comp
            ((ofPresheaf.map q).comp
              (E.comp (BasedCategory.fiberProductSnd F g)))).overHom) :
    RepresentableWith P F := by
  refine ⟨hF, ?_⟩
  intro T g X hX E hE U q hq
  obtain ⟨U₀, q₀, hq₀, hP₀⟩ := hgood T g X hX E hE
  let W := hq₀.rep.pullback q
  let a₀ : W ⟶ U₀ := hq₀.rep.fst' q
  let a : W ⟶ U := hq₀.rep.snd q
  have ha : (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) a :=
    hq₀.property_snd q
  have ha₀ : (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) a₀ :=
    hq.property q₀ (yoneda.map a) a₀ (hq₀.rep.isPullback' q).flip
  let H := E.comp (BasedCategory.fiberProductSnd F g)
  let f₀ := ((overBasedToOfPresheafYoneda U₀).comp
    ((ofPresheaf.map q₀).comp H)).overHom
  let f := ((overBasedToOfPresheafYoneda U).comp
    ((ofPresheaf.map q).comp H)).overHom
  have hcomp : a₀ ≫ f₀ = a ≫ f :=
    BasedCategory.atlas_overHom_eq H q₀ q a₀ a
      (hq₀.rep.isPullback' q).w
  have hPa₀ : P (a₀ ≫ f₀) := (hlocal a₀ f₀ ha₀).mp hP₀
  exact (hlocal a f ha).mpr (hcomp ▸ hPa₀)

/-- To prove `RepresentableWith P`, it suffices to construct one surjective étale
scheme chart with property `P` for every base change. The chart need not be tied to a
particular algebraic-space realization. -/
theorem RepresentableWith.of_exists_good_chart
    {P : MorphismProperty Scheme.{u}} {F : BasedFunctor Xcat Ycat}
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    (hF : Representable F)
    (hlocal : ∀ ⦃S' S T : Scheme.{u}⦄ (p : S' ⟶ S) (f : S ⟶ T),
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p →
        (P f ↔ P (p ≫ f)))
    (hgood : ∀ (T : Scheme.{u})
      (g : BasedFunctor (overBased T) Ycat),
      ∃ (U : Scheme.{u})
        (p : BasedFunctor (overBased U) (BasedCategory.fiberProduct F g)),
        RepresentableWith
          (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p ∧
        P (p.comp (BasedCategory.fiberProductSnd F g)).overHom) :
    RepresentableWith P F := by
  refine ⟨hF, ?_⟩
  intro T g X hX E hE U q hq
  let p : BasedFunctor (overBased U) (BasedCategory.fiberProduct F g) :=
    (overBasedToOfPresheafYoneda U).comp ((ofPresheaf.map q).comp E)
  have hqrel := relativelyRepresentableWith_ofPresheaf_map hq
  have hp₁ := hqrel.comp_of_isEquivalence
    (overBasedToOfPresheafYoneda U)
  have hp₂ := hp₁.comp_target_isEquivalence E
  have hp : RepresentableWith
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p :=
    RelativelyRepresentableWith.representableWith le_rfl hp₂
  obtain ⟨U₀, p₀, hp₀, hP₀⟩ := hgood T g
  obtain ⟨W, a₀, a, ha₀, ha, ⟨e⟩⟩ :=
    AlgebraicGeometry.exists_common_cover_iso hp₀ hp
  let H := BasedCategory.fiberProductSnd F g
  have e' : (overBased.map a₀).comp (p₀.comp H) ≅
      (overBased.map a).comp (p.comp H) :=
    BasedCategory.isoWhiskerRight e H
  have key : a₀ ≫ (p₀.comp H).overHom =
      a ≫ (p.comp H).overHom := by
    have heq := CategoryTheory.BasedFunctor.overHom_eq_of_iso e'
    rwa [CategoryTheory.BasedFunctor.overHom_comp,
      CategoryTheory.BasedFunctor.overHom_comp,
      CategoryTheory.BasedFunctor.overHom_map,
      CategoryTheory.BasedFunctor.overHom_map] at heq
  have hPa₀ : P (a₀ ≫ (p₀.comp H).overHom) :=
    (hlocal a₀ (p₀.comp H).overHom ha₀).mp hP₀
  have hPa : P (a ≫ (p.comp H).overHom) := key ▸ hPa₀
  exact (hlocal a (p.comp H).overHom ha).mpr hPa

end AlgebraicGeometry.BasedFunctor
