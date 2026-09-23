module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

/-!
# Transporting descent data along a pseudonatural transformation

This file maps descent data along a strong transformation between category-valued
pseudofunctors. A pointwise fully faithful transformation induces a fully faithful functor
on descent data, and a pointwise equivalence induces an equivalence on descent data.

Main declarations:
- `CategoryTheory.Pseudofunctor.mapDescentData`;
- `CategoryTheory.Pseudofunctor.mapDescentDataFullyFaithful`;
- `CategoryTheory.Pseudofunctor.mapDescentDataIsEquivalence`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory Opposite

universe t v' v u' u

namespace CategoryTheory.Pseudofunctor

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C]
  {F G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  (η : StrongTrans F G)
  {ι : Type t} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)

/-- Map one transition morphism of a descent datum along a strong transformation. -/
noncomputable def mapDescentDataObjHom (D : F.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (G.map f₁.op.toLoc).toFunctor.obj ((η.app (.mk (op (X i₁)))).toFunctor.obj (D.obj i₁)) ⟶
      (G.map f₂.op.toLoc).toFunctor.obj ((η.app (.mk (op (X i₂)))).toFunctor.obj (D.obj i₂)) :=
  (η.naturality f₁.op.toLoc).inv.toNatTrans.app (D.obj i₁) ≫
    (η.app (.mk (op Y))).toFunctor.map (D.hom q f₁ f₂ hf₁ hf₂) ≫
      (η.naturality f₂.op.toLoc).hom.toNatTrans.app (D.obj i₂)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- Map a descent datum along a strong transformation of pseudofunctors. -/
noncomputable def mapDescentDataObj (D : F.DescentData f) : G.DescentData f where
  obj i := (η.app (.mk (op (X i)))).toFunctor.obj (D.obj i)
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ := mapDescentDataObjHom η f D q f₁ f₂ hf₁ hf₂
  pullHom_hom := by
    intros Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    subst q'
    subst gf₁
    subst gf₂
    dsimp [mapDescentDataObjHom, LocallyDiscreteOpToCat.pullHom]
    simp only [Functor.map_comp, Category.assoc]
    have hD := D.pullHom_hom g q (g ≫ q) rfl f₁ f₂ hf₁ hf₂
      (g ≫ f₁) (g ≫ f₂) rfl rfl
    dsimp [LocallyDiscreteOpToCat.pullHom] at hD
    simp only [Pseudofunctor.mapComp'_eq_mapComp] at hD ⊢
    rw [← hD]
    simp only [Functor.map_comp, Category.assoc]
    rw [η.naturality_comp_inv_app_assoc]
    rw [η.naturality_comp_hom_app]
    slice_rhs 4 5 =>
      rw [← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app]
      exact Functor.map_id _ _
    simp only [Category.id_comp, Category.assoc]
    slice_rhs 5 6 =>
      rw [← Functor.map_comp, Cat.Hom.inv_hom_id_toNatTrans_app]
      exact Functor.map_id _ _
    simp only [Category.id_comp, Category.assoc]
    have hη := (η.naturality g.op.toLoc).inv.toNatTrans.naturality
      (D.hom q f₁ f₂ hf₁ hf₂)
    dsimp at hη
    rw [← reassoc_of% hη]
    simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
  hom_self := by
    intros Y q i g hg
    dsimp [mapDescentDataObjHom]
    rw [D.hom_self q g hg]
    simp
  hom_comp := by
    intros Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
    dsimp [mapDescentDataObjHom]
    simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
    slice_lhs 2 3 =>
      rw [← Functor.map_comp, D.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- The functor on descent data induced by a strong transformation of pseudofunctors. -/
noncomputable def mapDescentData : F.DescentData f ⥤ G.DescentData f where
  obj D := mapDescentDataObj η f D
  map {D₁ D₂} φ :=
    { hom := fun i ↦ (η.app (.mk (op (X i)))).toFunctor.map (φ.hom i)
      comm := by
        intros Y q i₁ i₂ f₁ f₂ hf₁ hf₂
        dsimp [mapDescentDataObj, mapDescentDataObjHom]
        simp only [Category.assoc]
        have h₁ := (η.naturality f₁.op.toLoc).inv.toNatTrans.naturality (φ.hom i₁)
        have h₂ := (η.naturality f₂.op.toLoc).hom.toNatTrans.naturality (φ.hom i₂)
        dsimp at h₁ h₂
        rw [reassoc_of% h₁]
        rw [← h₂]
        slice_lhs 2 3 =>
          rw [← Functor.map_comp, φ.comm q f₁ f₂ hf₁ hf₂, Functor.map_comp]
        simp only [Category.assoc] }

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- A pointwise fully faithful strong transformation induces a fully faithful functor on
descent data. -/
noncomputable def mapDescentDataFullyFaithful
    (hη : ∀ a, (η.app a).toFunctor.FullyFaithful) :
    (mapDescentData η f).FullyFaithful where
  preimage {D₁ D₂} ψ :=
    { hom := fun i ↦ (hη (.mk (op (X i)))).preimage (ψ.hom i)
      comm := by
        intros Y q i₁ i₂ f₁ f₂ hf₁ hf₂
        apply (hη (.mk (op Y))).map_injective
        simp only [Functor.map_comp]
        let N₁ := (η.naturality f₁.op.toLoc).inv.toNatTrans
        let N₂ := (η.naturality f₂.op.toLoc).hom.toNatTrans
        rw [← cancel_epi (N₁.app (D₁.obj i₁))]
        rw [← cancel_mono (N₂.app (D₂.obj i₂))]
        simp only [Category.assoc]
        have h₁ := N₁.naturality ((hη (.mk (op (X i₁)))).preimage (ψ.hom i₁))
        have h₂ := N₂.naturality ((hη (.mk (op (X i₂)))).preimage (ψ.hom i₂))
        dsimp [N₁, N₂] at h₁ h₂
        rw [← reassoc_of% h₁]
        rw [h₂]
        have hp₁ : (η.app (.mk (op (X i₁)))).toFunctor.map
            ((hη (.mk (op (X i₁)))).preimage (ψ.hom i₁)) = ψ.hom i₁ := by
          exact (hη (.mk (op (X i₁)))).map_preimage (ψ.hom i₁)
        have hp₂ : (η.app (.mk (op (X i₂)))).toFunctor.map
            ((hη (.mk (op (X i₂)))).preimage (ψ.hom i₂)) = ψ.hom i₂ := by
          exact (hη (.mk (op (X i₂)))).map_preimage (ψ.hom i₂)
        rw [hp₁, hp₂]
        have hψ := ψ.comm q f₁ f₂ hf₁ hf₂
        dsimp [mapDescentData, mapDescentDataObj, mapDescentDataObjHom] at hψ
        simpa only [N₁, N₂, Category.assoc] using hψ }
  map_preimage {D₁ D₂} ψ := by
    apply DescentData.hom_ext
    intro i
    exact (hη (.mk (op (X i)))).map_preimage (ψ.hom i)
  preimage_map {D₁ D₂} φ := by
    apply DescentData.hom_ext
    intro i
    exact (hη (.mk (op (X i)))).preimage_map (φ.hom i)

/-- A transition morphism for the chosen pointwise preimage of a descent datum under a
pointwise equivalence. -/
noncomputable def preimageDescentDataObjHom
    [∀ a, (η.app a).toFunctor.IsEquivalence]
    (E : G.DescentData f)
    ⦃Y : C⦄ (q : Y ⟶ S) ⦃i₁ i₂ : ι⦄ (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂)
    (hf₁ : f₁ ≫ f i₁ = q := by cat_disch) (hf₂ : f₂ ≫ f i₂ = q := by cat_disch) :
    (F.map f₁.op.toLoc).toFunctor.obj
        ((η.app (.mk (op (X i₁)))).toFunctor.objPreimage (E.obj i₁)) ⟶
      (F.map f₂.op.toLoc).toFunctor.obj
        ((η.app (.mk (op (X i₂)))).toFunctor.objPreimage (E.obj i₂)) :=
  (η.app (.mk (op Y))).toFunctor.preimage <|
    (η.naturality f₁.op.toLoc).hom.toNatTrans.app _ ≫
      (G.map f₁.op.toLoc).toFunctor.map
        ((η.app (.mk (op (X i₁)))).toFunctor.objObjPreimageIso (E.obj i₁)).hom ≫
      E.hom q f₁ f₂ hf₁ hf₂ ≫
      (G.map f₂.op.toLoc).toFunctor.map
        ((η.app (.mk (op (X i₂)))).toFunctor.objObjPreimageIso (E.obj i₂)).inv ≫
      (η.naturality f₂.op.toLoc).inv.toNatTrans.app _

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- The chosen preimage of a descent datum under a pointwise equivalence of
pseudofunctors. -/
noncomputable def preimageDescentDataObj
    [∀ a, (η.app a).toFunctor.IsEquivalence]
    (E : G.DescentData f) : F.DescentData f where
  obj i := (η.app (.mk (op (X i)))).toFunctor.objPreimage (E.obj i)
  hom Y q i₁ i₂ f₁ f₂ hf₁ hf₂ :=
    preimageDescentDataObjHom η f E q f₁ f₂ hf₁ hf₂
  pullHom_hom := by
    intros Y' Y g q q' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂
    subst q'
    subst gf₁
    subst gf₂
    apply (η.app _).toFunctor.map_injective
    dsimp [preimageDescentDataObjHom, LocallyDiscreteOpToCat.pullHom]
    simp only [Pseudofunctor.mapComp'_eq_mapComp, Functor.map_comp,
      Functor.map_preimage, Category.assoc]
    rw [η.naturality_comp_hom_app]
    rw [η.naturality_comp_inv_app]
    simp only [Category.assoc]
    rw [cancel_epi]
    have hE := E.pullHom_hom g q (g ≫ q) rfl f₁ f₂ hf₁ hf₂
      (g ≫ f₁) (g ≫ f₂) rfl rfl
    dsimp [LocallyDiscreteOpToCat.pullHom] at hE
    simp only [Pseudofunctor.mapComp'_eq_mapComp] at hE
    rw [← hE]
    let e₁ := (η.app (.mk (op (X i₁)))).toFunctor.objObjPreimageIso (E.obj i₁)
    let e₂ := (η.app (.mk (op (X i₂)))).toFunctor.objObjPreimageIso (E.obj i₂)
    have hc₁ := (G.mapComp f₁.op.toLoc g.op.toLoc).inv.toNatTrans.naturality e₁.hom
    have hc₂ := (G.mapComp f₂.op.toLoc g.op.toLoc).inv.toNatTrans.naturality e₂.inv
    dsimp [e₁, e₂] at hc₁ hc₂
    rw [← reassoc_of% hc₁]
    simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
    rw [← reassoc_of% hc₂]
    simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
    slice_rhs 2 6 =>
      simp only [← Functor.map_comp]
    let k :=
      (η.naturality f₁.op.toLoc).hom.toNatTrans.app
          ((η.app (.mk (op (X i₁)))).toFunctor.objPreimage (E.obj i₁)) ≫
        (G.map f₁.op.toLoc).toFunctor.map e₁.hom ≫
          E.hom q f₁ f₂ hf₁ hf₂ ≫
            (G.map f₂.op.toLoc).toFunctor.map e₂.inv ≫
              (η.naturality f₂.op.toLoc).inv.toNatTrans.app
                ((η.app (.mk (op (X i₂)))).toFunctor.objPreimage (E.obj i₂))
    have hg := (η.naturality g.op.toLoc).hom.toNatTrans.naturality
      ((η.app (.mk (op Y))).toFunctor.preimage k)
    dsimp [k, e₁, e₂] at hg
    rw [Functor.map_preimage] at hg
    simp only [Category.assoc]
    rw [← reassoc_of% hg]
    simp only [Category.assoc, Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  hom_self := by
    intros Y q i g hg
    apply (η.app _).toFunctor.map_injective
    dsimp [preimageDescentDataObjHom]
    rw [Functor.map_preimage, E.hom_self q g hg]
    simp
  hom_comp := by
    intros Y q i₁ i₂ i₃ f₁ f₂ f₃ hf₁ hf₂ hf₃
    apply (η.app _).toFunctor.map_injective
    dsimp [preimageDescentDataObjHom]
    simp only [Functor.map_comp, Functor.map_preimage, Category.assoc]
    simp only [Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
    slice_lhs 4 5 =>
      rw [← Functor.map_comp, Iso.inv_hom_id]
      exact Functor.map_id _ _
    simp only [Category.id_comp, Category.assoc]
    slice_lhs 3 4 =>
      rw [E.hom_comp q f₁ f₂ f₃ hf₁ hf₂ hf₃]
    simp only [Category.assoc]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- Mapping the chosen preimage descent datum recovers the original descent datum. -/
noncomputable def mapPreimageDescentDataObjIso
    [∀ a, (η.app a).toFunctor.IsEquivalence]
    (E : G.DescentData f) :
    (mapDescentData η f).obj (preimageDescentDataObj η f E) ≅ E :=
  DescentData.isoMk
    (fun i ↦ (η.app (.mk (op (X i)))).toFunctor.objObjPreimageIso (E.obj i))
    (by
      intros Y q i₁ i₂ f₁ f₂ hf₁ hf₂
      dsimp [mapDescentData, mapDescentDataObj, mapDescentDataObjHom,
        preimageDescentDataObj, preimageDescentDataObjHom]
      rw [Functor.map_preimage]
      simp only [Category.assoc, Cat.Hom.inv_hom_id_toNatTrans_app_assoc]
      slice_rhs 3 4 =>
        rw [← Functor.map_comp, Iso.inv_hom_id]
        exact Functor.map_id _ _
      simp only [Category.comp_id])

/-- A pointwise equivalence induces an essentially surjective functor on descent data. -/
theorem mapDescentDataEssSurj
    [∀ a, (η.app a).toFunctor.IsEquivalence] :
    (mapDescentData η f).EssSurj where
  mem_essImage E :=
    ⟨preimageDescentDataObj η f E, ⟨mapPreimageDescentDataObjIso η f E⟩⟩

/-- A pointwise equivalence of pseudofunctors induces an equivalence on descent data. -/
theorem mapDescentDataIsEquivalence
    [∀ a, (η.app a).toFunctor.IsEquivalence] :
    (mapDescentData η f).IsEquivalence := by
  let hη : ∀ a, (η.app a).toFunctor.FullyFaithful := fun a ↦
    Functor.FullyFaithful.ofFullyFaithful _
  let hff := mapDescentDataFullyFaithful η f hη
  exact
    { faithful := ⟨hff.map_injective⟩
      full := ⟨hff.map_surjective⟩
      essSurj := mapDescentDataEssSurj η f }

/-- The inverse naturality constraint for a strong transformation, expressed using the
flexible composition isomorphisms `mapComp'`. -/
lemma StrongTrans.naturalityComp'_inv_app
    {a b c : LocallyDiscrete Cᵒᵖ} (p : a ⟶ b) (q : b ⟶ c) (r : a ⟶ c)
    (h : p ≫ q = r) (M : F.obj a) :
    (η.naturality r).inv.toNatTrans.app M =
      (G.mapComp' p q r h).hom.toNatTrans.app ((η.app a).toFunctor.obj M) ≫
        (G.map q).toFunctor.map ((η.naturality p).inv.toNatTrans.app M) ≫
        (η.naturality q).inv.toNatTrans.app ((F.map p).toFunctor.obj M) ≫
        (η.app c).toFunctor.map ((F.mapComp' p q r h).inv.toNatTrans.app M) := by
  subst r
  simpa only [Pseudofunctor.mapComp'_eq_mapComp] using
    η.naturality_comp_inv_app p q M

/-- Cancellation form of `StrongTrans.naturalityComp'_inv_app`. -/
lemma StrongTrans.naturalityComp'_inv_app_cancel
    {a b c : LocallyDiscrete Cᵒᵖ} (p : a ⟶ b) (q : b ⟶ c) (r : a ⟶ c)
    (h : p ≫ q = r) (M : F.obj a) :
    (G.map q).toFunctor.map ((η.naturality p).inv.toNatTrans.app M) ≫
        (η.naturality q).inv.toNatTrans.app ((F.map p).toFunctor.obj M) ≫
        (η.app c).toFunctor.map ((F.mapComp' p q r h).inv.toNatTrans.app M) =
      (G.mapComp' p q r h).inv.toNatTrans.app ((η.app a).toFunctor.obj M) ≫
        (η.naturality r).inv.toNatTrans.app M := by
  rw [← cancel_epi ((G.mapComp' p q r h).hom.toNatTrans.app _)]
  simp only [Cat.Hom.hom_inv_id_toNatTrans_app_assoc]
  exact (η.naturalityComp'_inv_app p q r h M).symm

/-- A mixed inverse/hom cancellation form of
`StrongTrans.naturalityComp'_inv_app`. -/
lemma StrongTrans.naturalityComp'_inv_app_hom
    {a b c : LocallyDiscrete Cᵒᵖ} (p : a ⟶ b) (q : b ⟶ c) (r : a ⟶ c)
    (h : p ≫ q = r) (M : F.obj a) :
    (η.naturality r).inv.toNatTrans.app M ≫
        (η.app c).toFunctor.map ((F.mapComp' p q r h).hom.toNatTrans.app M) ≫
        (η.naturality q).hom.toNatTrans.app ((F.map p).toFunctor.obj M) =
      (G.mapComp' p q r h).hom.toNatTrans.app ((η.app a).toFunctor.obj M) ≫
        (G.map q).toFunctor.map ((η.naturality p).inv.toNatTrans.app M) := by
  rw [η.naturalityComp'_inv_app p q r h M]
  simp only [Category.assoc]
  have hcancel :
      (η.app c).toFunctor.map ((F.mapComp' p q r h).inv.toNatTrans.app M) ≫
          (η.app c).toFunctor.map ((F.mapComp' p q r h).hom.toNatTrans.app M) ≫
        (η.naturality q).hom.toNatTrans.app ((F.map p).toFunctor.obj M) =
      (η.naturality q).hom.toNatTrans.app ((F.map p).toFunctor.obj M) := by
    change
      (η.app c).toFunctor.map
            ((Cat.Hom.toNatIso (F.mapComp' p q r h)).app M).inv ≫
          (η.app c).toFunctor.map
              ((Cat.Hom.toNatIso (F.mapComp' p q r h)).app M).hom ≫
            (η.naturality q).hom.toNatTrans.app ((F.map p).toFunctor.obj M) = _
    exact Iso.map_inv_hom_id_assoc
      ((Cat.Hom.toNatIso (F.mapComp' p q r h)).app M)
      (η.app c).toFunctor
      ((η.naturality q).hom.toNatTrans.app ((F.map p).toFunctor.obj M))
  slice_lhs 4 6 =>
    exact hcancel
  slice_lhs 3 4 =>
    exact Cat.Hom.inv_hom_id_toNatTrans_app _ _
  simpa only [Cat.Hom.comp_toFunctor, Functor.comp_obj, Category.assoc] using
    Category.comp_id
    ((G.mapComp' p q r h).hom.toNatTrans.app ((η.app a).toFunctor.obj M) ≫
      (G.map q).toFunctor.map ((η.naturality p).inv.toNatTrans.app M))

/-- Cancellation form of inverse naturality allowing the source and target `mapComp'`
isomorphisms to carry definitionally different proofs of the same factorization. -/
lemma StrongTrans.naturalityComp'_inv_app_cancel_of_proofs
    {a b c : LocallyDiscrete Cᵒᵖ} (p : a ⟶ b) (q : b ⟶ c) (r : a ⟶ c)
    {hF hG : p ≫ q = r} (M : F.obj a) :
    (G.map q).toFunctor.map ((η.naturality p).inv.toNatTrans.app M) ≫
        (η.naturality q).inv.toNatTrans.app ((F.map p).toFunctor.obj M) ≫
        (η.app c).toFunctor.map ((F.mapComp' p q r hF).inv.toNatTrans.app M) =
      (G.mapComp' p q r hG).inv.toNatTrans.app ((η.app a).toFunctor.obj M) ≫
        (η.naturality r).inv.toNatTrans.app M := by
  have : hG = hF := Subsingleton.elim _ _
  cases this
  exact η.naturalityComp'_inv_app_cancel p q r hF M

/-- Mixed inverse/hom cancellation allowing the source and target `mapComp'`
isomorphisms to carry definitionally different proofs of the same factorization. -/
lemma StrongTrans.naturalityComp'_inv_app_hom_of_proofs
    {a b c : LocallyDiscrete Cᵒᵖ} (p : a ⟶ b) (q : b ⟶ c) (r : a ⟶ c)
    {hF hG : p ≫ q = r} (M : F.obj a) :
    (η.naturality r).inv.toNatTrans.app M ≫
        (η.app c).toFunctor.map ((F.mapComp' p q r hF).hom.toNatTrans.app M) ≫
        (η.naturality q).hom.toNatTrans.app ((F.map p).toFunctor.obj M) =
      (G.mapComp' p q r hG).hom.toNatTrans.app ((η.app a).toFunctor.obj M) ≫
        (G.map q).toFunctor.map ((η.naturality p).inv.toNatTrans.app M) := by
  have : hG = hF := Subsingleton.elim _ _
  cases this
  exact η.naturalityComp'_inv_app_hom p q r hF M

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
/-- The canonical descent functor commutes, up to natural isomorphism, with mapping descent
data along a strong transformation. -/
noncomputable def toDescentDataCompMapDescentDataIso :
    (η.app (.mk (op S))).toFunctor ⋙ G.toDescentData f ≅
      F.toDescentData f ⋙ mapDescentData η f :=
  NatIso.ofComponents
    (fun M ↦ DescentData.isoMk
      (fun i ↦ (Cat.Hom.toNatIso (η.naturality (f i).op.toLoc)).symm.app M)
      (by
        intros Y q i₁ i₂ f₁ f₂ hf₁ hf₂
        dsimp [Pseudofunctor.toDescentData, DescentData.ofObj,
          mapDescentData, mapDescentDataObj, mapDescentDataObjHom]
        simp only [Cat.Hom.toNatIso_inv, Functor.map_comp, Category.assoc]
        slice_lhs 1 3 =>
          rw [η.naturalityComp'_inv_app_cancel_of_proofs
            (f i₁).op.toLoc f₁.op.toLoc q.op.toLoc (hG := by cat_disch) M]
        slice_lhs 2 4 =>
          rw [η.naturalityComp'_inv_app_hom_of_proofs
            (f i₂).op.toLoc f₂.op.toLoc q.op.toLoc
              (hG := by
                change (f₂ ≫ f i₂).op.toLoc = q.op.toLoc
                exact congrArg (fun k ↦ k.op.toLoc) hf₂) M]))
    (by
      intros M N φ
      apply DescentData.hom_ext
      intro i
      dsimp
      exact (η.naturality (f i).op.toLoc).inv.toNatTrans.naturality φ)

/-- A pointwise equivalence of pseudofunctors preserves and reflects whether the canonical
functor to descent data is an equivalence. -/
theorem isEquivalence_toDescentData_iff
    [∀ a, (η.app a).toFunctor.IsEquivalence] :
    (F.toDescentData f).IsEquivalence ↔ (G.toDescentData f).IsEquivalence := by
  constructor
  · intro hF
    let _ : (F.toDescentData f).IsEquivalence := hF
    let _ : (mapDescentData η f).IsEquivalence :=
      mapDescentDataIsEquivalence η f
    let _ : (F.toDescentData f ⋙ mapDescentData η f).IsEquivalence := inferInstance
    let _ : ((η.app (.mk (op S))).toFunctor ⋙ G.toDescentData f).IsEquivalence :=
      Functor.isEquivalence_of_iso (toDescentDataCompMapDescentDataIso η f).symm
    exact Functor.isEquivalence_of_comp_left
      (η.app (.mk (op S))).toFunctor (G.toDescentData f)
  · intro hG
    let _ : (G.toDescentData f).IsEquivalence := hG
    let _ : (mapDescentData η f).IsEquivalence :=
      mapDescentDataIsEquivalence η f
    let _ : ((η.app (.mk (op S))).toFunctor ⋙ G.toDescentData f).IsEquivalence :=
      inferInstance
    let _ : (F.toDescentData f ⋙ mapDescentData η f).IsEquivalence :=
      Functor.isEquivalence_of_iso (toDescentDataCompMapDescentDataIso η f)
    exact Functor.isEquivalence_of_comp_right
      (F.toDescentData f) (mapDescentData η f)

end CategoryTheory.Pseudofunctor
