module

public import StacksAndModuli.API.PrestackProducts

/-!
# Pulling back a product morphism of prestacks

This file compares the base change of a product morphism along a pair with an
iterated fiber product. It is the prestack analogue of the canonical equivalence

`(X × X') ×_(Y × Y') T ≃ X ×_Y (X' ×_Y' T)`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory.BasedCategory

variable {S : Type u₁} [Category.{v₁} S]
  {X : BasedCategory.{v₂, u₂} S} {Y : BasedCategory.{v₃, u₃} S}
  {X' : BasedCategory.{v₄, u₄} S} {Y' : BasedCategory.{v₅, u₅} S}
  {T : BasedCategory.{v₆, u₆} S}

/-- The canonical comparison from the pullback of a product map along a pair to the
corresponding iterated fiber product. -/
def prodMapPullbackToIterated (F : BasedFunctor X Y) (G : BasedFunctor X' Y')
    (a : BasedFunctor T Y) (b : BasedFunctor T Y') :
    BasedFunctor (fiberProduct (prodMap F G) (prodLift a b))
      (fiberProduct F ((fiberProductSnd G b).comp a)) where
  obj d :=
    { fst := d.fst.fst
      snd :=
        { fst := d.fst.snd
          snd := d.snd
          over_eq := d.over_eq.trans d.fst.over_eq.symm
          iso := (fiberProductSnd Y.toBase Y'.toBase).toFunctor.mapIso d.iso
          isHomLift := by
            have h := FiberProductHom.isHomLift_snd d.iso.hom
              (𝟙 (X.p.obj d.fst.fst)) d.isHomLift
            rw [d.fst.over_eq]
            exact h }
      over_eq := d.fst.over_eq
      iso := (fiberProductFst Y.toBase Y'.toBase).toFunctor.mapIso d.iso
      isHomLift := FiberProductHom.isHomLift_fst d.iso.hom
        (𝟙 (X.p.obj d.fst.fst)) d.isHomLift }
  map {d e} q :=
    { fst := q.fst.fst
      snd :=
        { fst := q.fst.snd
          snd := q.snd
          isHomLift := isHomLift_map_of_common_lift
            (X.p.map q.fst.fst) q.fst.snd q.snd q.fst.isHomLift q.isHomLift
          w := by
            have h := congrArg FiberProductHom.snd q.w
            exact h }
      isHomLift := FiberProductHom.isHomLift_of_fst _
        (X.p.map q.fst.fst) q.fst.isHomLift
      w := by
        have h := congrArg FiberProductHom.fst q.w
        exact h }
  map_id d := by
    apply FiberProductHom.ext
    · rfl
    · apply FiberProductHom.ext <;> rfl
  map_comp q r := by
    apply FiberProductHom.ext
    · rfl
    · apply FiberProductHom.ext <;> rfl
  w := rfl

/-- The product-pullback comparison is faithful. -/
lemma prodMapPullbackToIterated_faithful (F : BasedFunctor X Y) (G : BasedFunctor X' Y')
    (a : BasedFunctor T Y) (b : BasedFunctor T Y') :
    (prodMapPullbackToIterated F G a b).toFunctor.Faithful := by
  constructor
  intro d e q r h
  apply FiberProductHom.ext
  · apply FiberProductHom.ext
    · exact congrArg (fun k ↦ k.fst) h
    · exact congrArg (fun k ↦ k.snd.fst) h
  · exact congrArg (fun k ↦ k.snd.snd) h

/-- The product-pullback comparison is full. -/
lemma prodMapPullbackToIterated_full (F : BasedFunctor X Y) (G : BasedFunctor X' Y')
    (a : BasedFunctor T Y) (b : BasedFunctor T Y') :
    (prodMapPullbackToIterated F G a b).toFunctor.Full := by
  constructor
  intro d e r
  let q : d ⟶ e :=
    { fst :=
        { fst := r.fst
          snd := r.snd.fst
          isHomLift := FiberProductHom.isHomLift_fst r.snd
            (X.p.map r.fst) r.isHomLift
          w := by
            let _ : IsHomLift (base S).p (X.p.map r.fst)
                (X.toBase.map r.fst) := by infer_instance
            let _ : IsHomLift (base S).p (𝟙 (X.p.obj e.fst.fst))
                e.fst.iso.hom := e.fst.isHomLift
            let _ : IsHomLift (base S).p (X.p.map r.fst)
                (X.toBase.map r.fst ≫ e.fst.iso.hom) :=
              IsHomLift.comp_lift_id_right' (base S).p
                (X.p.map r.fst) (X.toBase.map r.fst)
                (X.p.obj e.fst.fst) e.fst.iso.hom
            let _ : IsHomLift X'.p (X.p.map r.fst) r.snd.fst :=
              FiberProductHom.isHomLift_fst r.snd
                (X.p.map r.fst) r.isHomLift
            let _ : IsHomLift (base S).p (X.p.map r.fst)
                (X'.toBase.map r.snd.fst) := by infer_instance
            let _ : IsHomLift (base S).p (𝟙 (X.p.obj d.fst.fst))
                d.fst.iso.hom := d.fst.isHomLift
            let _ : IsHomLift (base S).p (X.p.map r.fst)
                (d.fst.iso.hom ≫ X'.toBase.map r.snd.fst) :=
              IsHomLift.comp_lift_id_left' (base S).p
                (X.p.obj d.fst.fst) d.fst.iso.hom
                (X.p.map r.fst) (X'.toBase.map r.snd.fst)
            exact base_hom_ext_of_lift (X.p.map r.fst) _ _ }
      snd := r.snd.snd
      isHomLift := FiberProductHom.isHomLift_snd r.snd
        (X.p.map r.fst) r.isHomLift
      w := by
        apply FiberProductHom.ext
        · exact r.w
        · exact r.snd.w }
  refine ⟨q, ?_⟩
  apply FiberProductHom.ext
  · rfl
  · apply FiberProductHom.ext <;> rfl

/-- An explicit preimage in the pullback of a product map of an object of the
corresponding iterated fiber product. -/
def iteratedToProdMapPullbackObj (F : BasedFunctor X Y) (G : BasedFunctor X' Y')
    (a : BasedFunctor T Y) (b : BasedFunctor T Y')
    (y : (fiberProduct F ((fiberProductSnd G b).comp a)).obj) :
    (fiberProduct (prodMap F G) (prodLift a b)).obj where
  fst :=
    { fst := y.fst
      snd := y.snd.fst
      over_eq := y.over_eq
      iso := eqToIso y.over_eq.symm
      isHomLift := IsHomLift.eqToHom_domain_lift_id y.over_eq.symm rfl }
  snd := y.snd.snd
  over_eq := y.snd.over_eq.trans y.over_eq
  iso := by
    apply FiberProductObj.isoMk y.iso y.snd.iso
    · have hy₂ : IsHomLift Y'.p (𝟙 (X.p.obj y.fst)) y.snd.iso.hom := by
        rw [← y.over_eq]
        exact y.snd.isHomLift
      exact isHomLift_map_of_common_lift (𝟙 (X.p.obj y.fst))
        y.iso.hom y.snd.iso.hom y.isHomLift hy₂
    · let _ : IsHomLift (base S).p (𝟙 (X.p.obj y.fst))
          (Y.toBase.map y.iso.hom) := by infer_instance
      let _ : IsHomLift (base S).p
          (𝟙 (Y.p.obj (a.obj y.snd.snd)))
          ((prodLift a b).obj y.snd.snd).iso.hom := by
        exact ((prodLift a b).obj y.snd.snd).isHomLift
      let _ : IsHomLift (base S).p (𝟙 (X.p.obj y.fst))
          (Y.toBase.map y.iso.hom ≫ ((prodLift a b).obj y.snd.snd).iso.hom) :=
        base_isHomLift_comp (S := X.p.obj y.fst)
          (T := Y.p.obj (a.obj y.snd.snd)) _ _
      let _ : IsHomLift (base S).p
          (𝟙 (X'.p.obj y.snd.fst))
          (Y'.toBase.map y.snd.iso.hom) := by infer_instance
      let _ : IsHomLift (base S).p
          (𝟙 (Y.p.obj (F.obj y.fst)))
          ((prodMap F G).obj
            { fst := y.fst
              snd := y.snd.fst
              over_eq := y.over_eq
              iso := eqToIso y.over_eq.symm
              isHomLift := IsHomLift.eqToHom_domain_lift_id y.over_eq.symm rfl }).iso.hom :=
        ((prodMap F G).obj
          { fst := y.fst
            snd := y.snd.fst
            over_eq := y.over_eq
            iso := eqToIso y.over_eq.symm
            isHomLift := IsHomLift.eqToHom_domain_lift_id y.over_eq.symm rfl }).isHomLift
      let _ : IsHomLift (base S).p
          (𝟙 (Y.p.obj (F.obj y.fst)))
          (((prodMap F G).obj
              { fst := y.fst
                snd := y.snd.fst
                over_eq := y.over_eq
                iso := eqToIso y.over_eq.symm
                isHomLift := IsHomLift.eqToHom_domain_lift_id y.over_eq.symm rfl }).iso.hom ≫
            Y'.toBase.map y.snd.iso.hom) :=
        base_isHomLift_comp (S := Y.p.obj (F.obj y.fst))
          (T := X'.p.obj y.snd.fst) _ _
      exact base_hom_ext
        (S := X.p.obj y.fst) (T := Y.p.obj (F.obj y.fst)) _ _
  isHomLift := by
    apply FiberProductHom.isHomLift_of_fst _ (𝟙 (X.p.obj y.fst))
    change IsHomLift Y.p (𝟙 (X.p.obj y.fst)) y.iso.hom
    exact y.isHomLift

/-- The forward comparison sends its explicit preimage to the original iterated
fiber-product object, up to canonical isomorphism. -/
def iteratedToProdMapPullbackRoundTripIsoApp (F : BasedFunctor X Y) (G : BasedFunctor X' Y')
    (a : BasedFunctor T Y) (b : BasedFunctor T Y')
    (y : (fiberProduct F ((fiberProductSnd G b).comp a)).obj) :
    (prodMapPullbackToIterated F G a b).obj (iteratedToProdMapPullbackObj F G a b y) ≅ y := by
  let e₂ : ((prodMapPullbackToIterated F G a b).obj
      (iteratedToProdMapPullbackObj F G a b y)).snd ≅ y.snd := by
    apply FiberProductObj.isoMk (Iso.refl _) (Iso.refl _)
    · change IsHomLift T.p (X'.p.map (𝟙 y.snd.fst)) (𝟙 y.snd.snd)
      rw [X'.p.map_id]
      exact IsHomLift.id y.snd.over_eq
    · simp [prodMapPullbackToIterated, iteratedToProdMapPullbackObj]
  apply FiberProductObj.isoMk (Iso.refl _) e₂
  · change IsHomLift (fiberProduct G b).p (X.p.map (𝟙 y.fst)) e₂.hom
    rw [X.p.map_id]
    apply FiberProductHom.isHomLift_of_fst _ (𝟙 (X.p.obj y.fst))
    change IsHomLift X'.p (𝟙 (X.p.obj y.fst)) (𝟙 y.snd.fst)
    rw [← y.over_eq]
    exact IsHomLift.id rfl
  · change F.map (𝟙 y.fst) ≫ y.iso.hom =
      y.iso.hom ≫ a.map e₂.hom.snd
    have ha : a.map e₂.hom.snd = 𝟙 (a.obj y.snd.snd) := by
      change a.map (𝟙 y.snd.snd) = 𝟙 (a.obj y.snd.snd)
      exact a.toFunctor.map_id y.snd.snd
    rw [F.toFunctor.map_id, ha, Category.id_comp]
    exact (Category.comp_id y.iso.hom).symm

/-- The inverse-direction comparison from an iterated fiber product to the pullback
of the corresponding product map. -/
def iteratedToProdMapPullback (F : BasedFunctor X Y) (G : BasedFunctor X' Y')
    (a : BasedFunctor T Y) (b : BasedFunctor T Y') :
    BasedFunctor (fiberProduct F ((fiberProductSnd G b).comp a))
      (fiberProduct (prodMap F G) (prodLift a b)) where
  obj := iteratedToProdMapPullbackObj F G a b
  map {y z} r :=
    { fst :=
        { fst := r.fst
          snd := r.snd.fst
          isHomLift := FiberProductHom.isHomLift_fst r.snd
            (X.p.map r.fst) r.isHomLift
          w := by
            let _ : IsHomLift (base S).p (X.p.map r.fst)
                (X.toBase.map r.fst) := by infer_instance
            let _ : IsHomLift (base S).p (𝟙 (X.p.obj z.fst))
                ((iteratedToProdMapPullbackObj F G a b z).fst.iso.hom) :=
              (iteratedToProdMapPullbackObj F G a b z).fst.isHomLift
            let _ : IsHomLift (base S).p (X.p.map r.fst)
                (X.toBase.map r.fst ≫ (iteratedToProdMapPullbackObj F G a b z).fst.iso.hom) :=
              IsHomLift.comp_lift_id_right' (base S).p
                (X.p.map r.fst) (X.toBase.map r.fst)
                (X.p.obj z.fst) (iteratedToProdMapPullbackObj F G a b z).fst.iso.hom
            let _ : IsHomLift X'.p (X.p.map r.fst) r.snd.fst :=
              FiberProductHom.isHomLift_fst r.snd
                (X.p.map r.fst) r.isHomLift
            let _ : IsHomLift (base S).p (X.p.map r.fst)
                (X'.toBase.map r.snd.fst) := by infer_instance
            let _ : IsHomLift (base S).p (𝟙 (X.p.obj y.fst))
                (iteratedToProdMapPullbackObj F G a b y).fst.iso.hom :=
              (iteratedToProdMapPullbackObj F G a b y).fst.isHomLift
            let _ : IsHomLift (base S).p (X.p.map r.fst)
                ((iteratedToProdMapPullbackObj F G a b y).fst.iso.hom ≫
                  X'.toBase.map r.snd.fst) :=
              IsHomLift.comp_lift_id_left' (base S).p
                (X.p.obj y.fst) (iteratedToProdMapPullbackObj F G a b y).fst.iso.hom
                (X.p.map r.fst) (X'.toBase.map r.snd.fst)
            exact base_hom_ext_of_lift (X.p.map r.fst) _ _ }
      snd := r.snd.snd
      isHomLift := FiberProductHom.isHomLift_snd r.snd
        (X.p.map r.fst) r.isHomLift
      w := by
        apply FiberProductHom.ext
        · exact r.w
        · exact r.snd.w }
  map_id y := by
    apply FiberProductHom.ext
    · apply FiberProductHom.ext <;> rfl
    · rfl
  map_comp q r := by
    apply FiberProductHom.ext
    · apply FiberProductHom.ext <;> rfl
    · rfl
  w := rfl

/-- The inverse-direction comparison followed by the forward comparison is
naturally isomorphic to the identity. -/
def iteratedToProdMapPullbackRoundTripIso (F : BasedFunctor X Y) (G : BasedFunctor X' Y')
    (a : BasedFunctor T Y) (b : BasedFunctor T Y') :
    (iteratedToProdMapPullback F G a b).toFunctor ⋙
        (prodMapPullbackToIterated F G a b).toFunctor ≅
      Functor.id (fiberProduct F ((fiberProductSnd G b).comp a)).obj :=
  NatIso.ofComponents (iteratedToProdMapPullbackRoundTripIsoApp F G a b) (fun {y z} q ↦ by
    apply FiberProductHom.ext
    · change q.fst ≫ 𝟙 z.fst = 𝟙 y.fst ≫ q.fst
      simp
    · apply FiberProductHom.ext
      · change q.snd.fst ≫ 𝟙 z.snd.fst = 𝟙 y.snd.fst ≫ q.snd.fst
        simp
      · change q.snd.snd ≫ 𝟙 z.snd.snd = 𝟙 y.snd.snd ≫ q.snd.snd
        simp)

/-- The product-pullback comparison is essentially surjective. -/
lemma prodMapPullbackToIterated_essSurj (F : BasedFunctor X Y) (G : BasedFunctor X' Y')
    (a : BasedFunctor T Y) (b : BasedFunctor T Y') :
    (prodMapPullbackToIterated F G a b).toFunctor.EssSurj := by
  constructor
  intro y
  exact ⟨iteratedToProdMapPullbackObj F G a b y,
    ⟨iteratedToProdMapPullbackRoundTripIsoApp F G a b y⟩⟩

/-- Pulling back a product map along a pair is equivalent to the corresponding
iterated fiber product. -/
theorem isEquivalence_prodMapPullbackToIterated (F : BasedFunctor X Y) (G : BasedFunctor X' Y')
    (a : BasedFunctor T Y) (b : BasedFunctor T Y') :
    (prodMapPullbackToIterated F G a b).toFunctor.IsEquivalence :=
  { faithful := prodMapPullbackToIterated_faithful F G a b
    full := prodMapPullbackToIterated_full F G a b
    essSurj := prodMapPullbackToIterated_essSurj F G a b }

/-- The inverse-direction product-pullback comparison is an equivalence. -/
theorem isEquivalence_iteratedToProdMapPullback (F : BasedFunctor X Y) (G : BasedFunctor X' Y')
    (a : BasedFunctor T Y) (b : BasedFunctor T Y') :
    (iteratedToProdMapPullback F G a b).toFunctor.IsEquivalence := by
  let _ : (prodMapPullbackToIterated F G a b).toFunctor.IsEquivalence :=
    isEquivalence_prodMapPullbackToIterated F G a b
  have _ : ((iteratedToProdMapPullback F G a b).toFunctor ⋙
      (prodMapPullbackToIterated F G a b).toFunctor).IsEquivalence :=
    Functor.isEquivalence_of_iso (iteratedToProdMapPullbackRoundTripIso F G a b).symm
  exact Functor.isEquivalence_of_comp_right
    (iteratedToProdMapPullback F G a b).toFunctor (prodMapPullbackToIterated F G a b).toFunctor

end CategoryTheory.BasedCategory
