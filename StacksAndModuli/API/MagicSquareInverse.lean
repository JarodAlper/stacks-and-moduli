module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.5a-magic-square»

/-!
# An inverse-direction functor for the magic square

The magic-square comparison sends a fiber product to the fiber product of a product
map with the diagonal.  This file constructs a based functor in the reverse direction
and proves that it is an equivalence.  The reverse direction is useful when transporting
a representation of the diagonal fiber product to a representation of the original
fiber product.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  {𝒯 : BasedCategory.{v₂, u₂} 𝒮} {𝒜 : BasedCategory.{v₃, u₃} 𝒮}
  {𝒯' : BasedCategory.{v₄, u₄} 𝒮}

/-- The second component of the inverse of the diagonal comparison isomorphism is
the original comparison isomorphism. -/
@[simp]
lemma magicSquareDiagIso_inv_snd (F : BasedFunctor 𝒯 𝒜)
    (G : BasedFunctor 𝒯' 𝒜) (x : (fiberProduct F G).obj) :
    (magicSquareDiagIso F G x).inv.snd = x.iso.hom := by
  apply (cancel_epi x.iso.inv).mp
  rw [x.iso.inv_hom_id]
  change x.iso.inv ≫ (magicSquareDiagIso F G x).inv.snd =
    𝟙 ((prodMap F G).obj (magicSquarePairObj F G x)).snd
  have h := congrArg FiberProductHom.snd (magicSquareDiagIso F G x).hom_inv_id
  simpa only [FiberProductObj.comp_snd, FiberProductObj.id_snd,
    magicSquareDiagIso_hom_snd] using h

/-- The explicit functor from the fiber product against the diagonal back to the
original fiber product. -/
def prodMapDiagToFiberProduct (F : BasedFunctor 𝒯 𝒜) (G : BasedFunctor 𝒯' 𝒜) :
    BasedFunctor (fiberProduct (prodMap F G) (diag 𝒜)) (fiberProduct F G) where
  obj q := magicSquarePreimageObj F G q
  map {a b} q :=
    { fst := q.fst.fst
      snd := q.fst.snd
      isHomLift := q.fst.isHomLift
      w := by
        have hw₁ := congrArg FiberProductHom.fst q.w
        have hw₂ := congrArg FiberProductHom.snd q.w
        simp only [FiberProductObj.comp_fst, FiberProductObj.comp_snd,
          prodMap_map_fst, prodMap_map_snd, diag_map_fst, diag_map_snd] at hw₁ hw₂
        change F.map q.fst.fst ≫
            ((magicSquareTargetFstIso F G b).hom ≫
              (magicSquareTargetSndIso F G b).inv) =
          ((magicSquareTargetFstIso F G a).hom ≫
              (magicSquareTargetSndIso F G a).inv) ≫ G.map q.fst.snd
        simp only [magicSquareTargetFstIso_hom, magicSquareTargetSndIso_inv]
        have ha : a.iso.inv.snd ≫ a.iso.hom.snd = 𝟙 _ := by
          rw [← FiberProductObj.comp_snd, Iso.inv_hom_id, FiberProductObj.id_snd]
        have hb : b.iso.hom.snd ≫ b.iso.inv.snd = 𝟙 _ := by
          rw [← FiberProductObj.comp_snd, Iso.hom_inv_id, FiberProductObj.id_snd]
        have hinner : q.snd ≫ b.iso.inv.snd = a.iso.inv.snd ≫ G.map q.fst.snd := by
          calc
            q.snd ≫ b.iso.inv.snd =
                (a.iso.inv.snd ≫ a.iso.hom.snd) ≫ q.snd ≫ b.iso.inv.snd := by
              rw [ha, Category.id_comp]
            _ = a.iso.inv.snd ≫ ((a.iso.hom.snd ≫ q.snd) ≫ b.iso.inv.snd) := by
              simp only [Category.assoc]
            _ = a.iso.inv.snd ≫
                ((G.map q.fst.snd ≫ b.iso.hom.snd) ≫ b.iso.inv.snd) := by rw [← hw₂]
            _ = a.iso.inv.snd ≫
                (G.map q.fst.snd ≫ (b.iso.hom.snd ≫ b.iso.inv.snd)) := by
              rw [Category.assoc]
            _ = a.iso.inv.snd ≫ G.map q.fst.snd := by
              rw [hb]
              exact congrArg (fun k ↦ a.iso.inv.snd ≫ k) (Category.comp_id _)
        calc
          F.map q.fst.fst ≫ (b.iso.hom.fst ≫ b.iso.inv.snd) =
              (F.map q.fst.fst ≫ b.iso.hom.fst) ≫ b.iso.inv.snd :=
            (Category.assoc _ _ _).symm
          _ = (a.iso.hom.fst ≫ q.snd) ≫ b.iso.inv.snd := by rw [hw₁]
          _ = a.iso.hom.fst ≫ (q.snd ≫ b.iso.inv.snd) := Category.assoc _ _ _
          _ = a.iso.hom.fst ≫ (a.iso.inv.snd ≫ G.map q.fst.snd) := by rw [hinner]
          _ = (a.iso.hom.fst ≫ a.iso.inv.snd) ≫ G.map q.fst.snd :=
            (Category.assoc _ _ _).symm }
  map_id q := by
    apply FiberProductHom.ext <;> rfl
  map_comp q r := by
    apply FiberProductHom.ext <;> rfl
  w := rfl

/-- The explicit inverse-direction magic-square functor is a left inverse up to a
canonical isomorphism. -/
def prodMapDiagRoundTripIsoApp (F : BasedFunctor 𝒯 𝒜)
    (G : BasedFunctor 𝒯' 𝒜) (x : (fiberProduct F G).obj) :
    (prodMapDiagToFiberProduct F G).obj ((fiberProductToProdMapDiag F G).obj x) ≅ x := by
  let e₁ : ((prodMapDiagToFiberProduct F G).obj
      ((fiberProductToProdMapDiag F G).obj x)).fst ≅ x.fst := eqToIso (by rfl)
  let e₂ : ((prodMapDiagToFiberProduct F G).obj
      ((fiberProductToProdMapDiag F G).obj x)).snd ≅ x.snd := eqToIso (by rfl)
  apply FiberProductObj.isoMk e₁ e₂
  · dsimp [e₁, e₂]
    rw [𝒯.p.map_id]
    exact IsHomLift.id x.over_eq
  · dsimp [e₁, e₂]
    simp [prodMapDiagToFiberProduct, fiberProductToProdMapDiag,
      magicSquarePreimageObj, magicSquareTargetFstIso, magicSquareTargetSndIso]

@[simp]
lemma prodMapDiagRoundTripIsoApp_hom_fst (F : BasedFunctor 𝒯 𝒜)
    (G : BasedFunctor 𝒯' 𝒜) (x : (fiberProduct F G).obj) :
    (prodMapDiagRoundTripIsoApp F G x).hom.fst = 𝟙 x.fst := rfl

@[simp]
lemma prodMapDiagRoundTripIsoApp_hom_snd (F : BasedFunctor 𝒯 𝒜)
    (G : BasedFunctor 𝒯' 𝒜) (x : (fiberProduct F G).obj) :
    (prodMapDiagRoundTripIsoApp F G x).hom.snd = 𝟙 x.snd := rfl

/-- The round trip from the original fiber product through the diagonal fiber
product is naturally isomorphic to the identity. -/
def prodMapDiagRoundTripIso (F : BasedFunctor 𝒯 𝒜)
    (G : BasedFunctor 𝒯' 𝒜) :
    (fiberProductToProdMapDiag F G).toFunctor ⋙
        (prodMapDiagToFiberProduct F G).toFunctor ≅ Functor.id (fiberProduct F G).obj :=
  NatIso.ofComponents (prodMapDiagRoundTripIsoApp F G) (fun {x y} q ↦ by
    apply FiberProductHom.ext
    · change q.fst ≫ 𝟙 _ = 𝟙 _ ≫ q.fst
      simp
    · change q.snd ≫ 𝟙 _ = 𝟙 _ ≫ q.snd
      simp)

/-- The inverse-direction magic-square functor is an equivalence. -/
theorem isEquivalence_prodMapDiagToFiberProduct (F : BasedFunctor 𝒯 𝒜)
    (G : BasedFunctor 𝒯' 𝒜) :
    (prodMapDiagToFiberProduct F G).toFunctor.IsEquivalence := by
  let _ := isEquivalence_fiberProductToProdMapDiag F G
  have _ : ((fiberProductToProdMapDiag F G).toFunctor ⋙
      (prodMapDiagToFiberProduct F G).toFunctor).IsEquivalence := by
    exact Functor.isEquivalence_of_iso (prodMapDiagRoundTripIso F G).symm
  exact Functor.isEquivalence_of_comp_left (fiberProductToProdMapDiag F G).toFunctor
    (prodMapDiagToFiberProduct F G).toFunctor

end CategoryTheory.BasedCategory
