module

public import StacksAndModuli.API.BasedFunctorEquivalence
public import StacksAndModuli.API.FiberProductPresentationMap
public import StacksAndModuli.API.RepresentableComposition

/-!
# Representability of the map induced by two presentation morphisms

The canonical morphism from the fiber product of two presentation sources to the
fiber product of their targets is representable when both presentation morphisms
are representable.  The proof identifies it, up to equivalence and a canonical
2-isomorphism, with the base change of the product of the two presentation maps.

The module also records the source-equivalence, target-equivalence, and
2-isomorphism invariance lemmas for `BasedFunctor.Representable` used in that
comparison.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor
open CategoryTheory.BasedCategory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆ u

namespace AlgebraicGeometry.BasedFunctor

variable {X : BasedCategory.{v₁, u₁} Scheme.{u}}
  {X' : BasedCategory.{v₂, u₂} Scheme.{u}}
  {Y : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- If precomposition by an equivalence is representable, then the original
morphism is representable. -/
theorem Representable.of_comp_isEquivalence
    {F : BasedFunctor X Y} (E : BasedFunctor X' X)
    [X'.p.IsFiberedInGroupoids] [X.p.IsFiberedInGroupoids]
    [Y.p.IsFiberedInGroupoids] [E.toFunctor.IsEquivalence]
    (hEF : Representable (E.comp F)) : Representable F := by
  intro T g
  obtain ⟨Z, hZ, R, hR⟩ := hEF T g
  let _ : R.toFunctor.IsEquivalence := hR
  let K := fiberProductLeftMap F g E
  let _ : K.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductLeftMap F g E
  exact ⟨Z, hZ, R.comp K,
    Functor.isEquivalence_trans R.toFunctor K.toFunctor⟩

/-- Representability is invariant under a based natural isomorphism. -/
theorem Representable.of_iso {F G : BasedFunctor X Y}
    (hF : Representable F) (e : F ≅ G) : Representable G := by
  intro T g
  obtain ⟨Z, hZ, R, hR⟩ := hF T g
  let _ : R.toFunctor.IsEquivalence := hR
  let K := fiberProductMapLeftIso e g
  let _ : K.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapLeftIso e g
  exact ⟨Z, hZ, R.comp K,
    Functor.isEquivalence_trans R.toFunctor K.toFunctor⟩

/-- Postcomposing a representable morphism by an equivalence of target prestacks
preserves representability. -/
theorem Representable.comp_target_isEquivalence
    {Y' : BasedCategory.{v₄, u₄} Scheme.{u}}
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    [Y'.p.IsFiberedInGroupoids]
    {F : BasedFunctor X Y} (hF : Representable F)
    (E : BasedFunctor Y Y') [E.toFunctor.IsEquivalence] :
    Representable (F.comp E) := by
  intro T g
  obtain ⟨L, ⟨α⟩, ⟨β⟩⟩ :=
    CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor E
  let η : (g.comp L).comp E ≅ g :=
    (eqToIso (BasedFunctor.comp_assoc g L E)).trans
      ((BasedCategory.isoWhiskerLeft g β).trans
        (eqToIso (BasedFunctor.comp_id g)))
  let K₀ := fiberProductPostcomp F (g.comp L) E
  let K₁ := fiberProductMapRightIso (F.comp E) η
  let K := K₀.comp K₁
  have hK₀ : K₀.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductPostcomp F (g.comp L) E
  have hK₁ : K₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso (F.comp E) η
  have hK : K.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans K₀.toFunctor K₁.toFunctor
  obtain ⟨Z, hZ, R, hR⟩ := hF T (g.comp L)
  exact ⟨Z, hZ, R.comp K,
    Functor.isEquivalence_trans R.toFunctor K.toFunctor⟩

end AlgebraicGeometry.BasedFunctor

namespace CategoryTheory.BasedCategory

variable {S : Type u₁} [Category.{v₁} S]
  {U : BasedCategory.{v₂, u₂} S} {X : BasedCategory.{v₃, u₃} S}
  {V : BasedCategory.{v₄, u₄} S} {Y' : BasedCategory.{v₅, u₅} S}
  {Y : BasedCategory.{v₆, u₆} S}

/-- Products of based functors respect composition. -/
@[simp]
lemma prodMap_comp_prodMap (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) :
    (prodMap P Q).comp (prodMap F G) =
      prodMap (P.comp F) (Q.comp G) := by
  rw [prodMap, prodLift_comp_prodMap]
  rfl

/-- The first component of an equality-induced based natural isomorphism into a
product is the corresponding equality-induced morphism. -/
lemma basedNatIsoApp_eqToIso_hom_fst
    {A B₁ B₂ : BasedCategory S} {L R : A ⥤ᵇ prod B₁ B₂}
    (h : L = R) (x : A.obj) :
    (basedNatIsoApp (eqToIso h) x).hom.fst =
      eqToHom (congrArg (fun K ↦ (K.obj x).fst) h) := by
  subst h
  rfl

/-- The second inverse component analogue of
`basedNatIsoApp_eqToIso_hom_fst`. -/
lemma basedNatIsoApp_eqToIso_inv_snd
    {A B₁ B₂ : BasedCategory S} {L R : A ⥤ᵇ prod B₁ B₂}
    (h : L = R) (x : A.obj) :
    (basedNatIsoApp (eqToIso h) x).inv.snd =
      eqToHom (congrArg (fun K ↦ (K.obj x).snd) h.symm) := by
  subst h
  rfl

lemma basedNatIsoApp_eqToIso_inv_fst
    {A B₁ B₂ : BasedCategory S} {L R : A ⥤ᵇ prod B₁ B₂}
    (h : L = R) (x : A.obj) :
    (basedNatIsoApp (eqToIso h) x).inv.fst =
      eqToHom (congrArg (fun K ↦ (K.obj x).fst) h.symm) := by
  subst h
  rfl

lemma basedNatIsoApp_eqToIso_hom_snd
    {A B₁ B₂ : BasedCategory S} {L R : A ⥤ᵇ prod B₁ B₂}
    (h : L = R) (x : A.obj) :
    (basedNatIsoApp (eqToIso h) x).hom.snd =
      eqToHom (congrArg (fun K ↦ (K.obj x).snd) h) := by
  subst h
  rfl

@[simp]
lemma prodMapCompIso_app_hom_fst (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (x : (prod U V).obj) :
    (basedNatIsoApp (eqToIso (prodMap_comp_prodMap P Q F G)) x).hom.fst =
      𝟙 ((prodMap (P.comp F) (Q.comp G)).obj x).fst := by
  rw [basedNatIsoApp_eqToIso_hom_fst]
  have hobj : congrArg (fun K ↦ (K.obj x).fst)
      (prodMap_comp_prodMap P Q F G) =
      rfl := Subsingleton.elim _ _
  rw [hobj]
  rfl

@[simp]
lemma prodMapCompIso_app_inv_snd (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (x : (prod U V).obj) :
    (basedNatIsoApp (eqToIso (prodMap_comp_prodMap P Q F G)) x).inv.snd =
      𝟙 (((prodMap P Q).comp (prodMap F G)).obj x).snd := by
  rw [basedNatIsoApp_eqToIso_inv_snd]
  have hobj : congrArg (fun K ↦ (K.obj x).snd)
      (prodMap_comp_prodMap P Q F G).symm = rfl := Subsingleton.elim _ _
  rw [hobj]
  rfl

@[simp]
lemma prodMapCompIso_app_inv_fst (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (x : (prod U V).obj) :
    (basedNatIsoApp (eqToIso (prodMap_comp_prodMap P Q F G)) x).inv.fst =
      𝟙 ((prodMap (P.comp F) (Q.comp G)).obj x).fst := by
  rw [basedNatIsoApp_eqToIso_inv_fst]
  have hobj : congrArg (fun K ↦ (K.obj x).fst)
      (prodMap_comp_prodMap P Q F G).symm = rfl := Subsingleton.elim _ _
  rw [hobj]
  rfl

@[simp]
lemma prodMapCompIso_app_hom_snd (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) (x : (prod U V).obj) :
    (basedNatIsoApp (eqToIso (prodMap_comp_prodMap P Q F G)) x).hom.snd =
      𝟙 (((prodMap P Q).comp (prodMap F G)).obj x).snd := by
  rw [basedNatIsoApp_eqToIso_hom_snd]
  have hobj : congrArg (fun K ↦ (K.obj x).snd)
      (prodMap_comp_prodMap P Q F G) = rfl := Subsingleton.elim _ _
  rw [hobj]
  rfl

/-- The map from a fiber product to the product of its two factors, obtained from
the magic-square comparison. -/
abbrev fiberProductPairMap (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y) :
    fiberProduct F G ⥤ᵇ prod X Y' :=
  (fiberProductToProdMapDiag F G).comp
    (fiberProductFst (prodMap F G) (diag Y))

@[simp]
lemma fiberProductPairMap_obj_fst (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (x : (fiberProduct F G).obj) :
    ((fiberProductPairMap F G).obj x).fst = x.fst :=
  rfl

@[simp]
lemma fiberProductPairMap_obj_snd (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (x : (fiberProduct F G).obj) :
    ((fiberProductPairMap F G).obj x).snd = x.snd :=
  rfl

@[simp]
lemma fiberProductPairMap_map_fst (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    {x y : (fiberProduct F G).obj} (f : x ⟶ y) :
    ((fiberProductPairMap F G).map f).fst = f.fst :=
  rfl

@[simp]
lemma fiberProductPairMap_map_snd (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    {x y : (fiberProduct F G).obj} (f : x ⟶ y) :
    ((fiberProductPairMap F G).map f).snd = f.snd :=
  rfl

/-- The base change of the product of two presentation maps is canonically
equivalent to the fiber product of their composites. -/
def fiberProductPresentationBaseChangeComparison
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y') :
    fiberProduct (prodMap P Q) (fiberProductPairMap F G) ⥤ᵇ
      fiberProduct (P.comp F) (Q.comp G) :=
  (((fiberProductRightMap (prodMap P Q)
      (fiberProductFst (prodMap F G) (diag Y))
      (fiberProductToProdMapDiag F G)).comp
    (pasteFwd (prodMap P Q) (prodMap F G) (diag Y))).comp
      (fiberProductMapLeftIso
        (eqToIso (prodMap_comp_prodMap P Q F G)) (diag Y))).comp
    (prodMapDiagToFiberProduct (P.comp F) (Q.comp G))

/-- The base-change comparison for the product of two presentation maps is an
equivalence. -/
theorem isEquivalence_fiberProductPresentationBaseChangeComparison
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    [X.p.IsFiberedInGroupoids] [Y'.p.IsFiberedInGroupoids]
    [Y.p.IsFiberedInGroupoids] :
    (fiberProductPresentationBaseChangeComparison F G P Q).toFunctor.IsEquivalence := by
  let E₀ := fiberProductToProdMapDiag F G
  let _ : E₀.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductToProdMapDiag F G
  let E₁ := fiberProductRightMap (prodMap P Q)
    (fiberProductFst (prodMap F G) (diag Y)) E₀
  let _ : E₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap (prodMap P Q)
      (fiberProductFst (prodMap F G) (diag Y)) E₀
  let E₂ := pasteFwd (prodMap P Q) (prodMap F G) (diag Y)
  let _ : E₂.toFunctor.IsEquivalence := inferInstance
  let E₃ := fiberProductMapLeftIso
    (eqToIso (prodMap_comp_prodMap P Q F G)) (diag Y)
  let _ : E₃.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapLeftIso _ _
  let E₄ := prodMapDiagToFiberProduct (P.comp F) (Q.comp G)
  let _ : E₄.toFunctor.IsEquivalence :=
    isEquivalence_prodMapDiagToFiberProduct (P.comp F) (Q.comp G)
  let _ : (E₁.comp E₂).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans E₁.toFunctor E₂.toFunctor
  let _ : ((E₁.comp E₂).comp E₃).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans (E₁.comp E₂).toFunctor E₃.toFunctor
  exact Functor.isEquivalence_trans
    ((E₁.comp E₂).comp E₃).toFunctor E₄.toFunctor

@[simp]
lemma fiberProductPresentationBaseChangeComparison_obj_fst
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (c : (fiberProduct (prodMap P Q) (fiberProductPairMap F G)).obj) :
    ((fiberProductPresentationBaseChangeComparison F G P Q).obj c).fst =
      c.fst.fst :=
  rfl

@[simp]
lemma fiberProductPresentationBaseChangeComparison_obj_snd
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (c : (fiberProduct (prodMap P Q) (fiberProductPairMap F G)).obj) :
    ((fiberProductPresentationBaseChangeComparison F G P Q).obj c).snd =
      c.fst.snd :=
  rfl

@[simp]
lemma fiberProductPresentationBaseChangeComparison_map_fst
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    {c d : (fiberProduct (prodMap P Q) (fiberProductPairMap F G)).obj}
    (f : c ⟶ d) :
    ((fiberProductPresentationBaseChangeComparison F G P Q).map f).fst =
      f.fst.fst :=
  rfl

@[simp]
lemma fiberProductPresentationBaseChangeComparison_map_snd
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    {c d : (fiberProduct (prodMap P Q) (fiberProductPairMap F G)).obj}
    (f : c ⟶ d) :
    ((fiberProductPresentationBaseChangeComparison F G P Q).map f).snd =
      f.fst.snd :=
  rfl

@[simp]
lemma magicSquarePreimageObj_iso_hom'
    {A : BasedCategory.{v₂, u₂} S} {B : BasedCategory.{v₃, u₃} S}
    {A' : BasedCategory.{v₄, u₄} S}
    (F : A ⥤ᵇ B) (G : A' ⥤ᵇ B)
    (q : (fiberProduct (prodMap F G) (diag B)).obj) :
    (magicSquarePreimageObj F G q).iso.hom =
      (magicSquareTargetFstIso F G q).hom ≫
      (magicSquareTargetSndIso F G q).inv :=
  rfl

/-- The inverse of the comparison isomorphism used by the forward pasting map. -/
lemma pasteFwd_obj_iso_inv'
    {W A B T : BasedCategory S} (E : W ⥤ᵇ A)
    (g : A ⥤ᵇ B) (h : T ⥤ᵇ B)
    (x : (fiberProduct E (fiberProductFst g h)).obj) :
    ((pasteFwd E g h).obj x).iso.inv =
      x.snd.iso.inv ≫ g.map x.iso.inv := by
  change (g.toFunctor.mapIso x.iso ≪≫ x.snd.iso).inv = _
  rfl

set_option linter.tacticCheckInstances false in
@[simp]
lemma fiberProductPresentationBaseChangeComparison_obj_iso_hom
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (c : (fiberProduct (prodMap P Q) (fiberProductPairMap F G)).obj) :
    ((fiberProductPresentationBaseChangeComparison F G P Q).obj c).iso.hom =
      F.map c.iso.hom.fst ≫ c.snd.iso.hom ≫ G.map c.iso.inv.snd := by
  let E₁ := fiberProductRightMap (prodMap P Q)
    (fiberProductFst (prodMap F G) (diag Y))
    (fiberProductToProdMapDiag F G)
  let E₂ := pasteFwd (prodMap P Q) (prodMap F G) (diag Y)
  let E₃ := fiberProductMapLeftIso
    (eqToIso (prodMap_comp_prodMap P Q F G)) (diag Y)
  let q := E₃.obj (E₂.obj (E₁.obj c))
  change (magicSquarePreimageObj (P.comp F) (Q.comp G) q).iso.hom = _
  rw [magicSquarePreimageObj_iso_hom']
  rw [magicSquareTargetFstIso_hom, magicSquareTargetSndIso_inv]
  dsimp only [q, E₃, fiberProductMapLeftIso, Iso.trans_hom, Iso.trans_inv,
    FiberProductObj.comp_fst, FiberProductObj.comp_snd]
  have hleft := prodMapCompIso_app_inv_fst P Q F G
    (E₂.obj (E₁.obj c)).fst
  have hright := prodMapCompIso_app_hom_snd P Q F G
    (E₂.obj (E₁.obj c)).fst
  have hleft' :
      (basedNatIsoApp (eqToIso (prodMap_comp_prodMap P Q F G))
        (E₂.obj (E₁.obj c)).fst).symm.hom.fst =
        𝟙 ((prodMap (P.comp F) (Q.comp G)).obj
          (E₂.obj (E₁.obj c)).fst).fst := hleft
  have hright' :
      (basedNatIsoApp (eqToIso (prodMap_comp_prodMap P Q F G))
        (E₂.obj (E₁.obj c)).fst).symm.inv.snd =
        𝟙 (((prodMap P Q).comp (prodMap F G)).obj
          (E₂.obj (E₁.obj c)).fst).snd := hright
  rw [hleft', hright', Category.id_comp, Category.comp_id]
  have hfst := congrArg FiberProductHom.fst
    (pasteFwd_obj_iso_hom (prodMap P Q) (prodMap F G) (diag Y)
      (E₁.obj c))
  have hsnd := congrArg FiberProductHom.snd
    (pasteFwd_obj_iso_inv' (prodMap P Q) (prodMap F G) (diag Y)
      (E₁.obj c))
  have hfst' : (E₂.obj (E₁.obj c)).iso.hom.fst =
      F.map c.iso.hom.fst := by
    rw [hfst]
    change F.map c.iso.hom.fst ≫ 𝟙 _ = _
    rw [Category.comp_id]
  have hsnd' : (E₂.obj (E₁.obj c)).iso.inv.snd =
      c.snd.iso.hom ≫ G.map c.iso.inv.snd := by
    rw [hsnd]
    rfl
  rw [hfst', hsnd']

/-- The objectwise isomorphism identifying the composite of the base-change
comparison with the canonical presentation map with the base-change projection. -/
def fiberProductPresentationBaseChangeIsoApp
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (c : (fiberProduct (prodMap P Q) (fiberProductPairMap F G)).obj) :
    (fiberProductPresentationMap F G P Q).obj
      ((fiberProductPresentationBaseChangeComparison F G P Q).obj c) ≅
      c.snd := by
  let e₁' : ((prodMap P Q).obj c.fst).fst ≅
      ((fiberProductPairMap F G).obj c.snd).fst :=
    FiberProductObj.isoFst c.iso
  let e₂' : ((prodMap P Q).obj c.fst).snd ≅
      ((fiberProductPairMap F G).obj c.snd).snd :=
    FiberProductObj.isoSnd c.iso
  let e₁ : ((fiberProductPresentationMap F G P Q).obj
      ((fiberProductPresentationBaseChangeComparison F G P Q).obj c)).fst ≅
      c.snd.fst :=
    eqToIso (by simp) ≪≫ e₁' ≪≫ eqToIso (by simp)
  let e₂ : ((fiberProductPresentationMap F G P Q).obj
      ((fiberProductPresentationBaseChangeComparison F G P Q).obj c)).snd ≅
      c.snd.snd :=
    eqToIso (by simp) ≪≫ e₂' ≪≫ eqToIso (by simp)
  apply FiberProductObj.isoMk (F := F) (G := G) e₁ e₂
  · exact isHomLift_map_of_common_lift
      (𝟙 ((prod U V).p.obj c.fst)) e₁.hom e₂.hom
      (by simpa [e₁, e₁'] using
        FiberProductHom.isHomLift_fst c.iso.hom _ c.isHomLift)
      (by simpa [e₂, e₂'] using
        FiberProductHom.isHomLift_snd c.iso.hom _ c.isHomLift)
  · have he₁ : e₁.hom = c.iso.hom.fst := by
      simp [e₁, e₁']
    have he₂ : e₂.hom = c.iso.hom.snd := by
      simp [e₂, e₂']
    rw [he₁, he₂, fiberProductPresentationMap_obj_iso_hom,
      fiberProductPresentationBaseChangeComparison_obj_iso_hom]
    simp only [Category.assoc]
    have he₂invhom := congrArg FiberProductHom.snd c.iso.inv_hom_id
    simp only [FiberProductObj.comp_snd, FiberProductObj.id_snd] at he₂invhom
    have hmapid := G.toFunctor.map_id
      ((fiberProductPairMap F G).obj c.snd).snd
    rw [← G.toFunctor.map_comp, he₂invhom, hmapid]
    simpa only [fiberProductPairMap_obj_snd] using
      (Category.comp_id (F.map c.iso.hom.fst ≫ c.snd.iso.hom)).symm.trans
        (Category.assoc (F.map c.iso.hom.fst) c.snd.iso.hom
          (𝟙 (G.obj c.snd.snd)))

@[simp]
lemma fiberProductPresentationBaseChangeIsoApp_hom_fst
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (c : (fiberProduct (prodMap P Q) (fiberProductPairMap F G)).obj) :
    (fiberProductPresentationBaseChangeIsoApp F G P Q c).hom.fst =
      c.iso.hom.fst := by
  simp [fiberProductPresentationBaseChangeIsoApp]

@[simp]
lemma fiberProductPresentationBaseChangeIsoApp_hom_snd
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (c : (fiberProduct (prodMap P Q) (fiberProductPairMap F G)).obj) :
    (fiberProductPresentationBaseChangeIsoApp F G P Q c).hom.snd =
      c.iso.hom.snd := by
  simp [fiberProductPresentationBaseChangeIsoApp]

@[simp]
lemma fiberProductPresentationBaseChange_comp_obj_fst
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (c : (fiberProduct (prodMap P Q) (fiberProductPairMap F G)).obj) :
    (((fiberProductPresentationBaseChangeComparison F G P Q).comp
      (fiberProductPresentationMap F G P Q)).obj c).fst = P.obj c.fst.fst :=
  rfl

@[simp]
lemma fiberProductPresentationBaseChange_comp_obj_snd
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    (c : (fiberProduct (prodMap P Q) (fiberProductPairMap F G)).obj) :
    (((fiberProductPresentationBaseChangeComparison F G P Q).comp
      (fiberProductPresentationMap F G P Q)).obj c).snd = Q.obj c.fst.snd :=
  rfl

@[simp]
lemma fiberProductPresentationBaseChange_comp_map_fst
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    {c d : (fiberProduct (prodMap P Q) (fiberProductPairMap F G)).obj}
    (f : c ⟶ d) :
    (((fiberProductPresentationBaseChangeComparison F G P Q).comp
      (fiberProductPresentationMap F G P Q)).map f).fst = P.map f.fst.fst :=
  rfl

@[simp]
lemma fiberProductPresentationBaseChange_comp_map_snd
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y')
    {c d : (fiberProduct (prodMap P Q) (fiberProductPairMap F G)).obj}
    (f : c ⟶ d) :
    (((fiberProductPresentationBaseChangeComparison F G P Q).comp
      (fiberProductPresentationMap F G P Q)).map f).snd = Q.map f.fst.snd :=
  rfl

/-- The base-change comparison followed by the canonical presentation map is
canonically isomorphic to the base-change projection. -/
def fiberProductPresentationBaseChangeIso
    (F : X ⥤ᵇ Y) (G : Y' ⥤ᵇ Y)
    (P : U ⥤ᵇ X) (Q : V ⥤ᵇ Y') :
    (fiberProductPresentationBaseChangeComparison F G P Q).comp
        (fiberProductPresentationMap F G P Q) ≅
      fiberProductSnd (prodMap P Q) (fiberProductPairMap F G) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fiberProductPresentationBaseChangeIsoApp F G P Q)
      (fun {c d} f ↦ by
        apply FiberProductHom.ext
        · have h := congrArg FiberProductHom.fst f.w
          change P.map f.fst.fst ≫ d.iso.hom.fst =
            c.iso.hom.fst ≫ f.snd.fst at h
          simpa using h
        · have h := congrArg FiberProductHom.snd f.w
          change Q.map f.fst.snd ≫ d.iso.hom.snd =
            c.iso.hom.snd ≫ f.snd.snd at h
          simpa using h))
    (fun c ↦ by
      apply FiberProductHom.isHomLift_of_fst _
        (𝟙 ((fiberProduct (prodMap P Q) (fiberProductPairMap F G)).p.obj c))
      simpa using FiberProductHom.isHomLift_fst c.iso.hom _ c.isHomLift)

end CategoryTheory.BasedCategory

namespace AlgebraicGeometry.BasedFunctor

variable {U : BasedCategory.{v₁, u₁} Scheme.{u}}
  {X : BasedCategory.{v₂, u₂} Scheme.{u}}
  {V : BasedCategory.{v₃, u₃} Scheme.{u}}
  {Y' : BasedCategory.{v₄, u₄} Scheme.{u}}
  {Y : BasedCategory.{v₅, u₅} Scheme.{u}}

/-- The canonical map induced on fiber products by two representable presentation
morphisms is representable. -/
theorem Representable.fiberProductPresentationMap
    [U.p.IsFiberedInGroupoids] [X.p.IsFiberedInGroupoids]
    [V.p.IsFiberedInGroupoids] [Y'.p.IsFiberedInGroupoids]
    [Y.p.IsFiberedInGroupoids]
    {F : X ⥤ᵇ Y} {G : Y' ⥤ᵇ Y}
    {P : U ⥤ᵇ X} {Q : V ⥤ᵇ Y'}
    (hP : Representable P) (hQ : Representable Q) :
    Representable
      (CategoryTheory.BasedCategory.fiberProductPresentationMap F G P Q) := by
  let H := fiberProductPairMap F G
  let π := CategoryTheory.BasedCategory.fiberProductSnd
    (CategoryTheory.BasedCategory.prodMap P Q) H
  have hprod : Representable (CategoryTheory.BasedCategory.prodMap P Q) :=
    Representable.prodMap hP hQ
  have hπ : Representable π := hprod.fiberProductSnd H
  let E := fiberProductPresentationBaseChangeComparison F G P Q
  let _ : E.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductPresentationBaseChangeComparison F G P Q
  let η := fiberProductPresentationBaseChangeIso F G P Q
  have hEK : Representable
      (E.comp (CategoryTheory.BasedCategory.fiberProductPresentationMap F G P Q)) :=
    hπ.of_iso η.symm
  exact Representable.of_comp_isEquivalence E hEK

end AlgebraicGeometry.BasedFunctor
