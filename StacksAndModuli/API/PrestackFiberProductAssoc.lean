module

public import StacksAndModuli.API.PrestackProducts

/-!
# Associativity of fiber products of prestacks

The comparison `(𝒳 ×_𝒴 𝒴') ×_{𝒴'} 𝒵 ≃ 𝒳 ×_𝒴 𝒵` for a morphism `𝒵 ⥤ᵇ 𝒴'`, in both
directions, together with the on-the-nose compatibility of the two second projections.
This is the pasting law that makes representability of a morphism of prestacks stable
under base change (`CategoryTheory.BasedFunctor.RelativelyRepresentable.fiberProductSnd`
in §4.1.1 and `AlgebraicGeometry.BasedFunctor.Representable.fiberProductSnd` in §4.1.2).

Main results:
- `CategoryTheory.BasedCategory.fiberProductAssoc` and `fiberProductAssocInv`, with
  `isEquivalence_fiberProductAssoc` and `isEquivalence_fiberProductAssocInv`;
- `fiberProductAssoc_comp_snd` and `fiberProductAssocInv_comp_snd`, both `rfl`.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section PrestackFiberProductAssoc

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : BasedCategory.{v₂, u₂} 𝒮}
  {𝒴 : BasedCategory.{v₃, u₃} 𝒮} {𝒴' : BasedCategory.{v₄, u₄} 𝒮}
  {𝒵 : BasedCategory.{v₅, u₅} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴) (H : 𝒵 ⥤ᵇ 𝒴')

/-- API construction supporting Construction 3.4.33 (the pasting law,
forward comparison): the canonical morphism
`(𝒳 ×_𝒴 𝒴') ×_{𝒴'} 𝒵 ⥤ᵇ 𝒳 ×_𝒴 𝒵`, sending `((x, y', γ), z, δ)` to
`(x, z, γ ∘ G(δ))`. It exhibits the second projection `𝒳 ×_𝒴 𝒴' → 𝒴'` as the base
change of `𝒳 → 𝒴` along `G`, and is an equivalence
(`isEquivalence_fiberProductAssoc`). -/
def fiberProductAssoc :
    fiberProduct (fiberProductSnd F G) H ⥤ᵇ fiberProduct F (H.comp G) where
  toFunctor :=
    { obj := fun a =>
        { fst := a.fst.fst
          snd := a.snd
          over_eq := a.over_eq
          iso := a.fst.iso ≪≫ G.toFunctor.mapIso a.iso
          isHomLift := by
            have h₁ : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a.fst.fst)) a.fst.iso.hom := a.fst.isHomLift
            have h₂ : IsHomLift 𝒴'.p (𝟙 (𝒳.p.obj a.fst.fst)) a.iso.hom := a.isHomLift
            have h₃ : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj a.fst.fst)) (G.map a.iso.hom) :=
              BasedFunctor.preserves_isHomLift G _ _
            exact IsHomLift.comp_lift_id_left' 𝒴.p (𝒳.p.obj a.fst.fst) a.fst.iso.hom
              (𝟙 (𝒳.p.obj a.fst.fst)) (G.map a.iso.hom) }
      map := fun {a b} φ =>
        { fst := φ.fst.fst
          snd := φ.snd
          isHomLift := φ.isHomLift
          w := by
            have h₁ : F.map φ.fst.fst ≫ b.fst.iso.hom = a.fst.iso.hom ≫ G.map φ.fst.snd :=
              φ.fst.w
            have h₂ : φ.fst.snd ≫ b.iso.hom = a.iso.hom ≫ H.map φ.snd := φ.w
            show F.map φ.fst.fst ≫ (b.fst.iso.hom ≫ G.map b.iso.hom) =
              (a.fst.iso.hom ≫ G.map a.iso.hom) ≫ G.map (H.map φ.snd)
            calc F.map φ.fst.fst ≫ (b.fst.iso.hom ≫ G.map b.iso.hom)
                = (F.map φ.fst.fst ≫ b.fst.iso.hom) ≫ G.map b.iso.hom :=
                  (Category.assoc _ _ _).symm
              _ = (a.fst.iso.hom ≫ G.map φ.fst.snd) ≫ G.map b.iso.hom := by rw [h₁]
              _ = a.fst.iso.hom ≫ G.map (φ.fst.snd ≫ b.iso.hom) := by
                  rw [G.toFunctor.map_comp, Category.assoc]
              _ = a.fst.iso.hom ≫ G.map (a.iso.hom ≫ H.map φ.snd) := by rw [h₂]
              _ = (a.fst.iso.hom ≫ G.map a.iso.hom) ≫ G.map (H.map φ.snd) := by
                  rw [G.toFunctor.map_comp, Category.assoc] }
      map_id := fun a => FiberProductHom.ext rfl rfl
      map_comp := fun φ ψ => FiberProductHom.ext rfl rfl }
  w := rfl

/-- API construction supporting Construction 3.4.33 (the pasting law, inverse
comparison): the canonical morphism `𝒳 ×_𝒴 𝒵 ⥤ᵇ (𝒳 ×_𝒴 𝒴') ×_{𝒴'} 𝒵`, sending
`(x, z, ε)` to `((x, H(z), ε), z, id)`. -/
def fiberProductAssocInv :
    fiberProduct F (H.comp G) ⥤ᵇ fiberProduct (fiberProductSnd F G) H where
  toFunctor :=
    { obj := fun c =>
        { fst :=
            { fst := c.fst
              snd := H.obj c.snd
              over_eq := (H.w_obj c.snd).trans c.over_eq
              iso := c.iso
              isHomLift := c.isHomLift }
          snd := c.snd
          over_eq := c.over_eq
          iso := Iso.refl (H.obj c.snd)
          isHomLift := IsHomLift.id ((H.w_obj c.snd).trans c.over_eq) }
      map := fun {c d} φ =>
        { fst :=
            { fst := φ.fst
              snd := H.map φ.snd
              isHomLift := BasedFunctor.preserves_isHomLift H (𝒳.p.map φ.fst) φ.snd
              w := φ.w }
          snd := φ.snd
          isHomLift := φ.isHomLift
          w := by
            show H.map φ.snd ≫ 𝟙 _ = 𝟙 _ ≫ H.map φ.snd
            rw [Category.comp_id, Category.id_comp] }
      map_id := fun c => by
        apply FiberProductHom.ext
        · exact FiberProductHom.ext rfl (H.toFunctor.map_id c.snd)
        · rfl
      map_comp := fun φ ψ => by
        apply FiberProductHom.ext
        · exact FiberProductHom.ext rfl (H.toFunctor.map_comp _ _)
        · rfl }
  w := rfl

instance : (fiberProductAssocInv F G H).toFunctor.Faithful where
  map_injective {c d} φ ψ h := by
    apply FiberProductHom.ext
    · exact congrArg (fun q => FiberProductHom.fst (FiberProductHom.fst q)) h
    · exact congrArg (fun q : (fiberProductAssocInv F G H).obj c ⟶
        (fiberProductAssocInv F G H).obj d => FiberProductHom.snd q) h

/-- A morphism between objects in the image of `fiberProductAssocInv` has its middle
component determined: it is the image under `H` of its `𝒵`-component. -/
lemma fiberProductAssocInv_hom_snd {c d : FiberProductObj F (H.comp G)}
    (ξ : (fiberProductAssocInv F G H).obj c ⟶ (fiberProductAssocInv F G H).obj d) :
    ξ.fst.snd = H.map ξ.snd := by
  have h : ξ.fst.snd ≫ 𝟙 (H.obj d.snd) = 𝟙 (H.obj c.snd) ≫ H.map ξ.snd := ξ.w
  calc ξ.fst.snd = ξ.fst.snd ≫ 𝟙 (H.obj d.snd) := (Category.comp_id _).symm
    _ = 𝟙 (H.obj c.snd) ≫ H.map ξ.snd := h
    _ = H.map ξ.snd := Category.id_comp _

instance : (fiberProductAssocInv F G H).toFunctor.Full where
  map_surjective {c d} ξ := by
    have hsnd : ξ.fst.snd = H.map ξ.snd := fiberProductAssocInv_hom_snd F G H ξ
    refine ⟨⟨ξ.fst.fst, ξ.snd, ξ.isHomLift, ?_⟩, ?_⟩
    · have h := ξ.fst.w
      rw [hsnd] at h
      exact h
    · apply FiberProductHom.ext
      · exact FiberProductHom.ext rfl hsnd.symm
      · rfl

/-- The unit isomorphism of the pasting-law equivalence: an object of
`(𝒳 ×_𝒴 𝒴') ×_{𝒴'} 𝒵` is recovered from its image in `𝒳 ×_𝒴 𝒵`. -/
def fiberProductAssocUnitObjIso (a : FiberProductObj (fiberProductSnd F G) H) :
    (fiberProductAssocInv F G H).obj ((fiberProductAssoc F G H).obj a) ≅ a := by
  refine FiberProductObj.isoMk
    (FiberProductObj.isoMk (Iso.refl a.fst.fst) a.iso.symm ?_ ?_) (Iso.refl a.snd) ?_ ?_
  · refine isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj a.fst.fst)) (𝟙 a.fst.fst) a.iso.inv
      (IsHomLift.id rfl) ?_
    have h : IsHomLift 𝒴'.p (𝟙 (𝒳.p.obj a.fst.fst)) a.iso.hom := a.isHomLift
    exact IsHomLift.lift_id_inv 𝒴'.p (𝒳.p.obj a.fst.fst) a.iso
  · show F.map (𝟙 a.fst.fst) ≫ a.fst.iso.hom =
      (a.fst.iso.hom ≫ G.map a.iso.hom) ≫ G.map a.iso.inv
    rw [F.toFunctor.map_id, Category.id_comp, Category.assoc, ← G.toFunctor.map_comp,
      Iso.hom_inv_id, G.toFunctor.map_id, Category.comp_id]
  · exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj a.fst.fst)) (𝟙 a.fst.fst) (𝟙 a.snd)
      (IsHomLift.id rfl) (IsHomLift.id a.over_eq)
  · show a.iso.inv ≫ a.iso.hom = 𝟙 (H.obj a.snd) ≫ H.map (𝟙 a.snd)
    rw [Iso.inv_hom_id, H.toFunctor.map_id, Category.comp_id]

instance : (fiberProductAssocInv F G H).toFunctor.EssSurj where
  mem_essImage a := ⟨(fiberProductAssoc F G H).obj a, ⟨fiberProductAssocUnitObjIso F G H a⟩⟩

/-- API equivalence supporting Construction 3.4.33 (the pasting law): the
inverse comparison `𝒳 ×_𝒴 𝒵 → (𝒳 ×_𝒴 𝒴') ×_{𝒴'} 𝒵` is an equivalence. -/
lemma isEquivalence_fiberProductAssocInv :
    (fiberProductAssocInv F G H).toFunctor.IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The middle component of a morphism of `(𝒳 ×_𝒴 𝒴') ×_{𝒴'} 𝒵` is determined by its
outer two components. -/
lemma FiberProductHom.snd_eq_of_assoc {a b : FiberProductObj (fiberProductSnd F G) H}
    (φ : a ⟶ b) : φ.fst.snd = a.iso.hom ≫ H.map φ.snd ≫ b.iso.inv := by
  have h : φ.fst.snd ≫ b.iso.hom = a.iso.hom ≫ H.map φ.snd := φ.w
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

instance : (fiberProductAssoc F G H).toFunctor.Faithful where
  map_injective {a b} φ ψ h := by
    have h1 : φ.fst.fst = ψ.fst.fst :=
      congrArg (fun q : (fiberProductAssoc F G H).obj a ⟶ (fiberProductAssoc F G H).obj b =>
        FiberProductHom.fst q) h
    have h2 : φ.snd = ψ.snd :=
      congrArg (fun q : (fiberProductAssoc F G H).obj a ⟶ (fiberProductAssoc F G H).obj b =>
        FiberProductHom.snd q) h
    refine FiberProductHom.ext (FiberProductHom.ext h1 ?_) h2
    rw [FiberProductHom.snd_eq_of_assoc, FiberProductHom.snd_eq_of_assoc, h2]

instance : (fiberProductAssoc F G H).toFunctor.Full where
  map_surjective {a b} ψ := by
    have hψ : IsHomLift 𝒵.p (𝒳.p.map ψ.fst) ψ.snd := ψ.isHomLift
    have hH : IsHomLift 𝒴'.p (𝒳.p.map ψ.fst) (H.map ψ.snd) :=
      BasedFunctor.preserves_isHomLift H (𝒳.p.map ψ.fst) ψ.snd
    have ha : IsHomLift 𝒴'.p (𝟙 (𝒳.p.obj a.fst.fst)) a.iso.hom := a.isHomLift
    have hb : IsHomLift 𝒴'.p (𝟙 (𝒳.p.obj b.fst.fst)) b.iso.hom := b.isHomLift
    have hbinv : IsHomLift 𝒴'.p (𝟙 (𝒳.p.obj b.fst.fst)) b.iso.inv :=
      IsHomLift.lift_id_inv 𝒴'.p (𝒳.p.obj b.fst.fst) b.iso
    have h1 : IsHomLift 𝒴'.p (𝒳.p.map ψ.fst) (H.map ψ.snd ≫ b.iso.inv) :=
      IsHomLift.comp_lift_id_right' 𝒴'.p (𝒳.p.map ψ.fst) (H.map ψ.snd)
        (𝒳.p.obj b.fst.fst) b.iso.inv
    have h2 : IsHomLift 𝒴'.p (𝒳.p.map ψ.fst) (a.iso.hom ≫ H.map ψ.snd ≫ b.iso.inv) :=
      IsHomLift.comp_lift_id_left' 𝒴'.p (𝒳.p.obj a.fst.fst) a.iso.hom (𝒳.p.map ψ.fst)
        (H.map ψ.snd ≫ b.iso.inv)
    have hw : F.map ψ.fst ≫ (b.fst.iso.hom ≫ G.map b.iso.hom) =
        (a.fst.iso.hom ≫ G.map a.iso.hom) ≫ G.map (H.map ψ.snd) := ψ.w
    have hGbb : G.map b.iso.hom ≫ G.map b.iso.inv = 𝟙 (G.obj b.fst.snd) :=
      (G.toFunctor.mapIso b.iso).hom_inv_id
    have hGs : G.map (a.iso.hom ≫ H.map ψ.snd ≫ b.iso.inv)
        = G.map a.iso.hom ≫ G.map (H.map ψ.snd ≫ b.iso.inv) := G.toFunctor.map_comp _ _
    have hGt : G.map (H.map ψ.snd ≫ b.iso.inv)
        = G.map (H.map ψ.snd) ≫ G.map b.iso.inv := G.toFunctor.map_comp _ _
    refine ⟨⟨⟨ψ.fst, a.iso.hom ≫ H.map ψ.snd ≫ b.iso.inv, h2, ?_⟩, ψ.snd, hψ, ?_⟩, ?_⟩
    · symm
      calc a.fst.iso.hom ≫ G.map (a.iso.hom ≫ H.map ψ.snd ≫ b.iso.inv)
          = a.fst.iso.hom ≫ G.map a.iso.hom ≫ G.map (H.map ψ.snd) ≫ G.map b.iso.inv := by
            rw [hGs, hGt]
        _ = ((a.fst.iso.hom ≫ G.map a.iso.hom) ≫ G.map (H.map ψ.snd)) ≫ G.map b.iso.inv := by
            simp only [Category.assoc]
        _ = (F.map ψ.fst ≫ (b.fst.iso.hom ≫ G.map b.iso.hom)) ≫ G.map b.iso.inv := by
            rw [hw]
        _ = F.map ψ.fst ≫ b.fst.iso.hom ≫ G.map b.iso.hom ≫ G.map b.iso.inv := by
            simp only [Category.assoc]
        _ = F.map ψ.fst ≫ b.fst.iso.hom ≫ 𝟙 (G.obj b.fst.snd) := by rw [hGbb]
        _ = F.map ψ.fst ≫ b.fst.iso.hom := by rw [Category.comp_id]
    · show (a.iso.hom ≫ H.map ψ.snd ≫ b.iso.inv) ≫ b.iso.hom = a.iso.hom ≫ H.map ψ.snd
      rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · exact FiberProductHom.ext rfl rfl

/-- The counit isomorphism of the pasting-law equivalence. -/
def fiberProductAssocCounitObjIso (c : FiberProductObj F (H.comp G)) :
    (fiberProductAssoc F G H).obj ((fiberProductAssocInv F G H).obj c) ≅ c := by
  refine FiberProductObj.isoMk (Iso.refl c.fst) (Iso.refl c.snd) ?_ ?_
  · exact isHomLift_map_of_common_lift (𝟙 (𝒳.p.obj c.fst)) (𝟙 c.fst) (𝟙 c.snd)
      (IsHomLift.id rfl) (IsHomLift.id c.over_eq)
  · have e1 : F.map (𝟙 c.fst) = 𝟙 (F.obj c.fst) := F.toFunctor.map_id _
    have e2 : G.map (𝟙 (H.obj c.snd)) = 𝟙 ((H.comp G).obj c.snd) := G.toFunctor.map_id _
    have e3 : (H.comp G).map (𝟙 c.snd) = 𝟙 ((H.comp G).obj c.snd) :=
      (H.comp G).toFunctor.map_id _
    show F.map (𝟙 c.fst) ≫ c.iso.hom =
      (c.iso.hom ≫ G.map (𝟙 (H.obj c.snd))) ≫ (H.comp G).map (𝟙 c.snd)
    rw [e1, e2, e3, Category.id_comp, Category.comp_id]
    exact (Category.comp_id _).symm

instance : (fiberProductAssoc F G H).toFunctor.EssSurj where
  mem_essImage c :=
    ⟨(fiberProductAssocInv F G H).obj c, ⟨fiberProductAssocCounitObjIso F G H c⟩⟩

/-- API equivalence supporting Construction 3.4.33 (the pasting law): for
morphisms of prestacks `F : 𝒳 → 𝒴`, `G : 𝒴' → 𝒴` and `H : 𝒵 → 𝒴'`, the comparison
`(𝒳 ×_𝒴 𝒴') ×_{𝒴'} 𝒵 → 𝒳 ×_𝒴 𝒵` is an equivalence. Equivalently: the second
projection `𝒳 ×_𝒴 𝒴' → 𝒴'` is the base change of `F` along `G`. -/
lemma isEquivalence_fiberProductAssoc :
    (fiberProductAssoc F G H).toFunctor.IsEquivalence :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- The pasting-law comparison is compatible with the projections to `𝒵`, on the nose. -/
lemma fiberProductAssoc_comp_snd :
    (fiberProductAssoc F G H).comp (fiberProductSnd F (H.comp G)) =
      fiberProductSnd (fiberProductSnd F G) H := rfl

/-- The inverse pasting-law comparison is compatible with the projections to `𝒵`, on
the nose. -/
lemma fiberProductAssocInv_comp_snd :
    (fiberProductAssocInv F G H).comp (fiberProductSnd (fiberProductSnd F G) H) =
      fiberProductSnd F (H.comp G) := rfl

end CategoryTheory.BasedCategory

end PrestackFiberProductAssoc
