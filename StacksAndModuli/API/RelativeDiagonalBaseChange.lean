module

public import StacksAndModuli.API.PrestackFiberProductAssoc
public import StacksAndModuli.API.FiberProductLegIso
public import StacksAndModuli.API.FiberProductPresentationMap
public import StacksAndModuli.API.PresentationBaseChange
public import StacksAndModuli.API.RelativeDiagonalFiber
public import StacksAndModuli.API.RelativelyRepresentableSourceEquivalence
public import StacksAndModuli.API.RepresentableWithCharts

/-!
# Relative diagonals and base change

The relative diagonal of a base change of a morphism of prestacks is itself the base
change of the original relative diagonal. This file constructs the comparison explicitly
for the strict fiber-product model used by `BasedCategory`, proves that it is an
equivalence, and transfers relative representability with a morphism property across it.
For scheme-valued base changes it also gives both directions between a
`RepresentableWith` property of the original relative diagonal and the corresponding
properties of all base-changed relative diagonals, assuming source-locality for the
reverse direction.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedCategory

variable {S : Type u₁} [Category.{v₁} S]
  {X : BasedCategory.{v₂, u₂} S}
  {Y : BasedCategory.{v₃, u₃} S}
  {Z : BasedCategory.{v₄, u₄} S}

variable (F : X ⥤ᵇ Y) (G : Z ⥤ᵇ Y)

/-- The first projection from the base change of `F` along `G`. -/
abbrev baseChangeFst := fiberProductFst F G

/-- The second projection from the base change of `F` along `G`. -/
abbrev baseChangeSnd := fiberProductSnd F G

/-- The canonical map from the square of a base change to the square of the original
morphism. -/
def baseChangeDiagonalTarget :
    fiberProduct (baseChangeSnd F G) (baseChangeSnd F G) ⥤ᵇ
      fiberProduct F F :=
  ((fiberProductAssoc F G (baseChangeSnd F G)).comp
    (fiberProductMapRightIso F
      (fiberProductIsoComm F G).symm)).comp
    (fiberProductRightMap F F (baseChangeFst F G))

/-- The base change of `F` determined by the first component of a point of the
target of its relative diagonal. -/
abbrev relativeDiagonalBaseChange
    (F : X ⥤ᵇ Y) (g : Z ⥤ᵇ fiberProduct F F) :=
  fiberProduct F ((relativeDiagonalPointFst F g).comp F)

/-- The structural morphism of the base change determined by a point of the
target of a relative diagonal. -/
abbrev relativeDiagonalBaseChangeSnd
    (F : X ⥤ᵇ Y) (g : Z ⥤ᵇ fiberProduct F F) :=
  fiberProductSnd F ((relativeDiagonalPointFst F g).comp F)

/-- The first point underlying `g` as a section of the corresponding base change
of `F`. -/
noncomputable def relativeDiagonalBaseChangeSectionFst
    (F : X ⥤ᵇ Y) (g : Z ⥤ᵇ fiberProduct F F) :
    Z ⥤ᵇ relativeDiagonalBaseChange F g :=
  fiberProductLift (relativeDiagonalPointFst F g) (BasedFunctor.id Z)
    (Iso.refl _)

/-- The second point underlying `g` as a section of the corresponding base change
of `F`; the comparison isomorphism carried by `g` identifies its image with the
chosen base point. -/
noncomputable def relativeDiagonalBaseChangeSectionSnd
    (F : X ⥤ᵇ Y) (g : Z ⥤ᵇ fiberProduct F F) :
    Z ⥤ᵇ relativeDiagonalBaseChange F g :=
  fiberProductLift (relativeDiagonalPointSnd F g) (BasedFunctor.id Z)
    ((whiskerLeftIso g (fiberProductIsoComm F F)).symm)

/-- A point of the target of `F.diag` lifts to the square of the base-changed
morphism determined by its first component. -/
noncomputable def relativeDiagonalTargetLift
    (F : X ⥤ᵇ Y) (g : Z ⥤ᵇ fiberProduct F F) :
    Z ⥤ᵇ fiberProduct (relativeDiagonalBaseChangeSnd F g)
      (relativeDiagonalBaseChangeSnd F g) :=
  fiberProductLift (relativeDiagonalBaseChangeSectionFst F g)
    (relativeDiagonalBaseChangeSectionSnd F g) (Iso.refl _)

/-- The lift of a point of the target of `F.diag`, followed by the canonical map
from the square of the base change to the original square, recovers the point up
to a based natural isomorphism. -/
noncomputable def relativeDiagonalTargetLiftIso
    (F : X ⥤ᵇ Y) (g : Z ⥤ᵇ fiberProduct F F) :
    (relativeDiagonalTargetLift F g).comp
      (baseChangeDiagonalTarget F
        ((relativeDiagonalPointFst F g).comp F)) ≅ g :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun x ↦ by
        let e₁ : ((((relativeDiagonalTargetLift F g).comp
            (baseChangeDiagonalTarget F
              ((relativeDiagonalPointFst F g).comp F))).obj x).fst) ≅
            (g.obj x).fst := eqToIso (by rfl)
        let e₂ : ((((relativeDiagonalTargetLift F g).comp
            (baseChangeDiagonalTarget F
              ((relativeDiagonalPointFst F g).comp F))).obj x).snd) ≅
            (g.obj x).snd := eqToIso (by rfl)
        apply FiberProductObj.isoMk e₁ e₂
        · exact isHomLift_map_of_common_lift
            (𝟙 (X.p.obj (((relativeDiagonalTargetLift F g).comp
              (baseChangeDiagonalTarget F
                ((relativeDiagonalPointFst F g).comp F))).obj x).fst))
            e₁.hom e₂.hom (IsHomLift.id rfl)
            (IsHomLift.id (((relativeDiagonalTargetLift F g).comp
              (baseChangeDiagonalTarget F
                ((relativeDiagonalPointFst F g).comp F))).obj x).over_eq)
        · dsimp [e₁, e₂, relativeDiagonalTargetLift,
            relativeDiagonalBaseChangeSectionFst,
            relativeDiagonalBaseChangeSectionSnd,
            baseChangeDiagonalTarget, relativeDiagonalBaseChangeSnd,
            relativeDiagonalBaseChange, relativeDiagonalPointFst,
            relativeDiagonalPointSnd, fiberProductAssoc,
            fiberProductMapRightIso, fiberProductRightMap,
            basedNatIsoApp, whiskerLeftIso, fiberProductIsoComm,
            fiberProductLift, BasedFunctor.comp, BasedFunctor.diag,
            BasedFunctor.id, BasedNatTrans.id, BasedNatTrans.forgetful,
            BasedNatIso.mkNatIso]
          rw [g.toFunctor.map_id, FiberProductObj.id_fst,
            F.toFunctor.map_id, F.toFunctor.map_id]
          simp only [Category.id_comp, Category.comp_id])
      (fun {x y} k ↦ by
        apply FiberProductHom.ext <;>
          dsimp [FiberProductObj.isoMk, fiberProductObjIsoMk,
            relativeDiagonalTargetLift, relativeDiagonalBaseChangeSectionFst,
            relativeDiagonalBaseChangeSectionSnd,
            baseChangeDiagonalTarget, relativeDiagonalBaseChangeSnd,
            relativeDiagonalBaseChange, relativeDiagonalPointFst,
            relativeDiagonalPointSnd, fiberProductAssoc,
            fiberProductMapRightIso, fiberProductRightMap,
            basedNatIsoApp, whiskerLeftIso, fiberProductIsoComm,
            fiberProductLift, BasedFunctor.comp, BasedFunctor.diag,
            BasedFunctor.id, BasedNatTrans.id, BasedNatTrans.forgetful,
            BasedNatIso.mkNatIso] <;> simp))
    (fun x ↦ by
      apply FiberProductHom.isHomLift_of_fst _ (𝟙 (Z.p.obj x))
      exact IsHomLift.id (((relativeDiagonalTargetLift F g).comp
        (baseChangeDiagonalTarget F
          ((relativeDiagonalPointFst F g).comp F))).w_obj x))

/-- The two composites from a base change to the square of the original morphism are
canonically 2-isomorphic. -/
noncomputable def baseChangeDiagonalIso :
    (baseChangeFst F G).comp F.diag ≅
      (baseChangeSnd F G).diag.comp (baseChangeDiagonalTarget F G) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun w ↦ by
        let e₁ : (((baseChangeFst F G).comp F.diag).obj w).fst ≅
            (((baseChangeSnd F G).diag.comp
              (baseChangeDiagonalTarget F G)).obj w).fst := eqToIso (by rfl)
        let e₂ : (((baseChangeFst F G).comp F.diag).obj w).snd ≅
            (((baseChangeSnd F G).diag.comp
              (baseChangeDiagonalTarget F G)).obj w).snd := eqToIso (by rfl)
        apply FiberProductObj.isoMk e₁ e₂
        · exact isHomLift_map_of_common_lift
            (𝟙 ((fiberProduct F G).p.obj w)) e₁.hom e₂.hom
            (IsHomLift.id rfl) (IsHomLift.id rfl)
        · dsimp [e₁, e₂, baseChangeDiagonalTarget, baseChangeSnd,
            baseChangeFst, fiberProductAssoc, fiberProductMapRightIso,
            fiberProductRightMap, basedNatIsoApp, fiberProductIsoComm,
            fiberProductLift, BasedFunctor.comp, BasedFunctor.diag,
            BasedFunctor.id, BasedNatTrans.id, BasedNatTrans.forgetful,
            BasedNatIso.mkNatIso]
          simp only [F.toFunctor.map_id, G.toFunctor.map_id,
            Category.id_comp, Category.comp_id]
          exact w.iso.hom_inv_id)
      (fun {w w'} k ↦ by
        apply FiberProductHom.ext <;>
          dsimp [baseChangeDiagonalTarget, baseChangeSnd, baseChangeFst,
            fiberProductAssoc, fiberProductMapRightIso,
            fiberProductRightMap, basedNatIsoApp, fiberProductIsoComm,
            fiberProductLift, BasedFunctor.comp, BasedFunctor.diag,
            BasedFunctor.id, BasedNatTrans.id, BasedNatTrans.forgetful,
            BasedNatIso.mkNatIso] <;> simp))
    (fun w ↦ by
      apply FiberProductHom.isHomLift_of_fst _
        (𝟙 ((fiberProduct F G).p.obj w))
      exact IsHomLift.id rfl)

/-- The canonical comparison from a base change of `F` to the base change of `F.diag`. -/
noncomputable def baseChangeDiagonalComparison :
    fiberProduct F G ⥤ᵇ
      fiberProduct F.diag (baseChangeDiagonalTarget F G) :=
  fiberProductLift (baseChangeFst F G) (baseChangeSnd F G).diag
    (baseChangeDiagonalIso F G)

/-- The structural map of the diagonal base-change comparison is the diagonal of the
base-changed morphism. -/
@[simp]
lemma baseChangeDiagonalComparison_comp_snd :
    (baseChangeDiagonalComparison F G).comp
      (fiberProductSnd F.diag (baseChangeDiagonalTarget F G)) =
        (baseChangeSnd F G).diag :=
  fiberProductLift_comp_snd _ _ _

/-- The inverse-direction functor of the diagonal base-change comparison. -/
def baseChangeDiagonalComparisonInv :
    fiberProduct F.diag (baseChangeDiagonalTarget F G) ⥤ᵇ
      fiberProduct F G :=
  (fiberProductSnd F.diag (baseChangeDiagonalTarget F G)).comp
    (fiberProductFst (baseChangeSnd F G) (baseChangeSnd F G))

/-- The diagonal base-change comparison followed by its inverse is the identity. -/
@[simp]
lemma baseChangeDiagonalComparison_comp_inv :
    (baseChangeDiagonalComparison F G).comp
      (baseChangeDiagonalComparisonInv F G) =
        BasedFunctor.id (fiberProduct F G) := by
  rw [baseChangeDiagonalComparisonInv, ← BasedFunctor.comp_assoc,
    baseChangeDiagonalComparison_comp_snd]
  exact fiberProductLift_comp_fst _ _ _

/-- The comparison between the two objects in the base change carried by an object of
the base-changed relative diagonal. -/
noncomputable def baseChangeDiagonalSigma
    (b : (fiberProduct F.diag (baseChangeDiagonalTarget F G)).obj) :
    b.snd.fst ≅ b.snd.snd := by
  let β₁ : b.fst ≅ b.snd.fst.fst := FiberProductObj.isoFst b.iso
  let β₂ : b.fst ≅ b.snd.snd.fst := FiberProductObj.isoSnd b.iso
  let eX : b.snd.fst.fst ≅ b.snd.snd.fst := β₁.symm ≪≫ β₂
  let eZ : b.snd.fst.snd ≅ b.snd.snd.snd := b.snd.iso
  apply FiberProductObj.isoMk eX eZ
  · have hβ₁ : IsHomLift X.p (𝟙 (X.p.obj b.fst)) β₁.hom :=
      FiberProductHom.isHomLift_fst b.iso.hom _ b.isHomLift
    have hβ₁inv : IsHomLift X.p (𝟙 (X.p.obj b.fst)) β₁.inv :=
      IsHomLift.lift_id_inv X.p _ β₁
    have hβ₂ : IsHomLift X.p (𝟙 (X.p.obj b.fst)) β₂.hom :=
      FiberProductHom.isHomLift_snd b.iso.hom _ b.isHomLift
    have heX : IsHomLift X.p (𝟙 (X.p.obj b.fst)) eX.hom := by
      let _ := hβ₁inv
      let _ := hβ₂
      exact IsHomLift.comp_of_lift_id (p := X.p)
        (X.p.obj b.fst) β₁.inv β₂.hom
    have heZ : IsHomLift Z.p (𝟙 (X.p.obj b.fst)) eZ.hom := by
      rw [← b.over_eq]
      exact b.snd.isHomLift
    exact isHomLift_map_of_common_lift (𝟙 (X.p.obj b.fst))
      eX.hom eZ.hom heX heZ
  · have hw := b.iso.hom.w
    have hw' : F.map β₁.hom ≫
          (b.snd.fst.iso.hom ≫ G.map b.snd.iso.hom ≫
            b.snd.snd.iso.inv) = F.map β₂.hom := by
      simpa [β₁, β₂, baseChangeDiagonalTarget,
        fiberProductAssoc, fiberProductMapRightIso,
        fiberProductRightMap, basedNatIsoApp, fiberProductIsoComm,
        fiberProductLift, BasedFunctor.comp, BasedFunctor.diag,
        BasedFunctor.id, BasedNatTrans.id, BasedNatTrans.forgetful,
        BasedNatIso.mkNatIso] using hw
    have hw'' : F.map β₂.hom ≫ b.snd.snd.iso.hom =
        F.map β₁.hom ≫ b.snd.fst.iso.hom ≫
          G.map b.snd.iso.hom := by
      have h := congrArg (fun k ↦ k ≫ b.snd.snd.iso.hom) hw'
      simpa only [Category.assoc, Iso.inv_hom_id,
        Category.comp_id] using h.symm
    change F.map eX.hom ≫ b.snd.snd.iso.hom =
      b.snd.fst.iso.hom ≫ G.map eZ.hom
    dsimp only [eX, eZ, Iso.trans_hom, Iso.symm_hom]
    calc
      F.map (β₁.inv ≫ β₂.hom) ≫ b.snd.snd.iso.hom =
          F.map β₁.inv ≫ (F.map β₂.hom ≫
            b.snd.snd.iso.hom) := by
        rw [F.toFunctor.map_comp, Category.assoc]
      _ = F.map β₁.inv ≫
          (F.map β₁.hom ≫ b.snd.fst.iso.hom ≫
            G.map b.snd.iso.hom) := by rw [hw'']
      _ = b.snd.fst.iso.hom ≫ G.map b.snd.iso.hom := by
        rw [← Category.assoc, ← F.toFunctor.map_comp,
          β₁.inv_hom_id, F.toFunctor.map_id, Category.id_comp]

/-- The diagonal of the base-change projection, evaluated on the first object in a
diagonal fiber, is canonically isomorphic to its second object. -/
noncomputable def baseChangeDiagonalInvSndIso
    (b : (fiberProduct F.diag (baseChangeDiagonalTarget F G)).obj) :
    (baseChangeSnd F G).diag.obj b.snd.fst ≅ b.snd := by
  let e₁ : b.snd.fst ≅ b.snd.fst := Iso.refl _
  let e₂ : b.snd.fst ≅ b.snd.snd := baseChangeDiagonalSigma F G b
  apply FiberProductObj.isoMk
    (a := (baseChangeSnd F G).diag.obj b.snd.fst) (b := b.snd) e₁ e₂
  · exact isHomLift_map_of_common_lift
      (𝟙 ((fiberProduct F G).p.obj b.snd.fst)) e₁.hom e₂.hom
      (IsHomLift.id rfl) (by
        let β₁ : b.fst ≅ b.snd.fst.fst := FiberProductObj.isoFst b.iso
        let β₂ : b.fst ≅ b.snd.snd.fst := FiberProductObj.isoSnd b.iso
        have hβ₁ : IsHomLift X.p (𝟙 (X.p.obj b.fst)) β₁.hom :=
          FiberProductHom.isHomLift_fst b.iso.hom _ b.isHomLift
        have hβ₁inv : IsHomLift X.p (𝟙 (X.p.obj b.fst)) β₁.inv :=
          IsHomLift.lift_id_inv X.p _ β₁
        have hβ₂ : IsHomLift X.p (𝟙 (X.p.obj b.fst)) β₂.hom :=
          FiberProductHom.isHomLift_snd b.iso.hom _ b.isHomLift
        have heX : IsHomLift X.p (𝟙 (X.p.obj b.fst))
            (β₁.inv ≫ β₂.hom) := by
          let _ := hβ₁inv
          let _ := hβ₂
          exact IsHomLift.comp_of_lift_id (p := X.p)
            (X.p.obj b.fst) β₁.inv β₂.hom
        rw [← b.over_eq] at heX
        apply FiberProductHom.isHomLift_of_fst e₂.hom
          (𝟙 ((fiberProduct F G).p.obj b.snd.fst))
        change IsHomLift X.p (𝟙 (X.p.obj b.snd.fst.fst))
          (β₁.inv ≫ β₂.hom)
        exact heX)
  · change (baseChangeSnd F G).map e₁.hom ≫ b.snd.iso.hom =
      _ ≫ (baseChangeSnd F G).map e₂.hom
    dsimp [e₁, e₂, baseChangeDiagonalSigma, baseChangeSnd,
      BasedFunctor.diag, fiberProductLift, BasedFunctor.id,
      BasedFunctor.comp, BasedNatTrans.id, BasedNatTrans.forgetful,
      BasedNatIso.mkNatIso]

/-- The objectwise isomorphism defining the counit of the diagonal base-change
equivalence. -/
noncomputable def baseChangeDiagonalComparisonCounitObjIso
    (b : (fiberProduct F.diag (baseChangeDiagonalTarget F G)).obj) :
    (baseChangeDiagonalComparison F G).obj
      ((baseChangeDiagonalComparisonInv F G).obj b) ≅ b := by
  let β₁ : b.fst ≅ b.snd.fst.fst := FiberProductObj.isoFst b.iso
  let eX : b.snd.fst.fst ≅ b.fst := β₁.symm
  let eA : (baseChangeSnd F G).diag.obj b.snd.fst ≅ b.snd :=
    baseChangeDiagonalInvSndIso F G b
  apply FiberProductObj.isoMk eX eA
  · have heX : IsHomLift X.p (𝟙 (X.p.obj b.fst)) eX.hom := by
      have hβ₁ : IsHomLift X.p (𝟙 (X.p.obj b.fst)) β₁.hom :=
        FiberProductHom.isHomLift_fst b.iso.hom _ b.isHomLift
      let _ := hβ₁
      exact IsHomLift.lift_id_inv X.p _ β₁
    have heA : IsHomLift
        (fiberProduct (baseChangeSnd F G) (baseChangeSnd F G)).p
        (𝟙 (X.p.obj b.fst)) eA.hom := by
      rw [← b.over_eq]
      apply FiberProductHom.isHomLift_of_fst eA.hom
        (𝟙 ((fiberProduct F G).p.obj b.snd.fst))
      exact IsHomLift.id rfl
    exact isHomLift_map_of_common_lift (𝟙 (X.p.obj b.fst))
      eX.hom eA.hom heX heA
  · apply FiberProductHom.ext
    · dsimp [eX, eA, β₁, baseChangeDiagonalComparison,
        baseChangeDiagonalComparisonInv, baseChangeDiagonalInvSndIso,
        baseChangeDiagonalIso, baseChangeDiagonalTarget,
        baseChangeSnd, baseChangeFst, fiberProductAssoc,
        fiberProductMapRightIso, fiberProductRightMap,
        basedNatIsoApp, fiberProductIsoComm, fiberProductLift,
        BasedFunctor.comp, BasedFunctor.diag, BasedFunctor.id,
        BasedNatTrans.id, BasedNatTrans.forgetful, BasedNatIso.mkNatIso]
      have hβ₁hom : b.iso.hom.fst = β₁.hom := rfl
      rw [Category.id_comp, hβ₁hom]
      exact β₁.inv_hom_id
    · dsimp [eX, eA, β₁, baseChangeDiagonalComparison,
        baseChangeDiagonalComparisonInv, baseChangeDiagonalInvSndIso,
        baseChangeDiagonalIso, baseChangeDiagonalTarget,
        baseChangeSnd, baseChangeFst, fiberProductAssoc,
        fiberProductMapRightIso, fiberProductRightMap,
        basedNatIsoApp, fiberProductIsoComm, fiberProductLift,
        BasedFunctor.comp, BasedFunctor.diag, BasedFunctor.id,
        BasedNatTrans.id, BasedNatTrans.forgetful, BasedNatIso.mkNatIso]
      rw [Category.id_comp]
      change β₁.inv ≫ (FiberProductObj.isoSnd b.iso).hom =
        β₁.inv ≫ (FiberProductObj.isoSnd b.iso).hom
      rfl

/-- The counit isomorphism for the explicit diagonal base-change equivalence. -/
noncomputable def baseChangeDiagonalComparisonCounit :
    (baseChangeDiagonalComparisonInv F G).comp
        (baseChangeDiagonalComparison F G) ≅
      BasedFunctor.id
        (fiberProduct F.diag (baseChangeDiagonalTarget F G)) :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (baseChangeDiagonalComparisonCounitObjIso F G)
      (fun {b c} f ↦ by
        let βb₁ : b.fst ≅ b.snd.fst.fst := FiberProductObj.isoFst b.iso
        let βb₂ : b.fst ≅ b.snd.snd.fst := FiberProductObj.isoSnd b.iso
        let βc₁ : c.fst ≅ c.snd.fst.fst := FiberProductObj.isoFst c.iso
        let βc₂ : c.fst ≅ c.snd.snd.fst := FiberProductObj.isoSnd c.iso
        have hw₁ : f.fst ≫ βc₁.hom = βb₁.hom ≫ f.snd.fst.fst := by
          have h := congrArg FiberProductHom.fst f.w
          simpa [βb₁, βc₁, baseChangeDiagonalTarget,
            fiberProductAssoc, fiberProductMapRightIso,
            fiberProductRightMap, basedNatIsoApp, fiberProductIsoComm,
            BasedFunctor.comp, BasedFunctor.diag, fiberProductLift,
            BasedFunctor.id] using h
        have hw₂ : f.fst ≫ βc₂.hom = βb₂.hom ≫ f.snd.snd.fst := by
          have h := congrArg FiberProductHom.snd f.w
          simpa [βb₂, βc₂, baseChangeDiagonalTarget,
            fiberProductAssoc, fiberProductMapRightIso,
            fiberProductRightMap, basedNatIsoApp, fiberProductIsoComm,
            BasedFunctor.comp, BasedFunctor.diag, fiberProductLift,
            BasedFunctor.id] using h
        have hinv₁ : f.snd.fst.fst ≫ βc₁.inv = βb₁.inv ≫ f.fst := by
          rw [← cancel_mono βc₁.hom]
          rw [Category.assoc, βc₁.inv_hom_id, Category.comp_id,
            Category.assoc, hw₁, ← Category.assoc,
            βb₁.inv_hom_id, Category.id_comp]
        apply FiberProductHom.ext
        · dsimp [baseChangeDiagonalComparisonCounitObjIso,
            baseChangeDiagonalComparison, baseChangeDiagonalComparisonInv,
            baseChangeDiagonalInvSndIso, baseChangeDiagonalSigma,
            baseChangeDiagonalIso, baseChangeDiagonalTarget,
            baseChangeSnd, baseChangeFst, fiberProductAssoc,
            fiberProductMapRightIso, fiberProductRightMap,
            basedNatIsoApp, fiberProductIsoComm, fiberProductLift,
            BasedFunctor.comp, BasedFunctor.diag, BasedFunctor.id,
            BasedNatTrans.id, BasedNatTrans.forgetful, BasedNatIso.mkNatIso]
          exact hinv₁
        · apply FiberProductHom.ext
          · dsimp [baseChangeDiagonalComparisonCounitObjIso,
              baseChangeDiagonalComparison, baseChangeDiagonalComparisonInv,
              baseChangeDiagonalInvSndIso, baseChangeDiagonalSigma,
              baseChangeDiagonalIso, baseChangeDiagonalTarget,
              baseChangeSnd, baseChangeFst, fiberProductAssoc,
              fiberProductMapRightIso, fiberProductRightMap,
              basedNatIsoApp, fiberProductIsoComm, fiberProductLift,
              BasedFunctor.comp, BasedFunctor.diag, BasedFunctor.id,
              BasedNatTrans.id, BasedNatTrans.forgetful, BasedNatIso.mkNatIso]
            simp
          · apply FiberProductHom.ext
            · dsimp [baseChangeDiagonalComparisonCounitObjIso,
                baseChangeDiagonalComparison, baseChangeDiagonalComparisonInv,
                baseChangeDiagonalInvSndIso, baseChangeDiagonalSigma,
                baseChangeDiagonalIso, baseChangeDiagonalTarget,
                baseChangeSnd, baseChangeFst, fiberProductAssoc,
                fiberProductMapRightIso, fiberProductRightMap,
                basedNatIsoApp, fiberProductIsoComm, fiberProductLift,
                BasedFunctor.comp, BasedFunctor.diag, BasedFunctor.id,
                BasedNatTrans.id, BasedNatTrans.forgetful, BasedNatIso.mkNatIso]
              calc
                f.snd.fst.fst ≫ (βc₁.inv ≫ βc₂.hom) =
                    (βb₁.inv ≫ f.fst) ≫ βc₂.hom := by
                  rw [← Category.assoc, hinv₁]
                _ = βb₁.inv ≫ (f.fst ≫ βc₂.hom) :=
                  Category.assoc _ _ _
                _ = βb₁.inv ≫
                    (βb₂.hom ≫ f.snd.snd.fst) := by rw [hw₂]
                _ = (βb₁.inv ≫ βb₂.hom) ≫
                    f.snd.snd.fst := (Category.assoc _ _ _).symm
            · dsimp [baseChangeDiagonalComparisonCounitObjIso,
                baseChangeDiagonalComparison, baseChangeDiagonalComparisonInv,
                baseChangeDiagonalInvSndIso, baseChangeDiagonalSigma,
                baseChangeDiagonalIso, baseChangeDiagonalTarget,
                baseChangeSnd, baseChangeFst, fiberProductAssoc,
                fiberProductMapRightIso, fiberProductRightMap,
                basedNatIsoApp, fiberProductIsoComm, fiberProductLift,
                BasedFunctor.comp, BasedFunctor.diag, BasedFunctor.id,
                BasedNatTrans.id, BasedNatTrans.forgetful, BasedNatIso.mkNatIso]
              exact f.snd.w))
    (fun b ↦ by
      apply FiberProductHom.isHomLift_of_fst _
        (𝟙 ((fiberProduct F.diag
          (baseChangeDiagonalTarget F G)).p.obj b))
      have hβ₁ : IsHomLift X.p (𝟙 (X.p.obj b.fst))
          (FiberProductObj.isoFst b.iso).hom :=
        FiberProductHom.isHomLift_fst b.iso.hom _ b.isHomLift
      let _ := hβ₁
      exact IsHomLift.lift_id_inv X.p _ (FiberProductObj.isoFst b.iso))

/-- The canonical diagonal base-change comparison is an equivalence. -/
theorem isEquivalence_baseChangeDiagonalComparison :
    (baseChangeDiagonalComparison F G).toFunctor.IsEquivalence := by
  let e₁ : (baseChangeDiagonalComparison F G).comp
      (baseChangeDiagonalComparisonInv F G) ≅
        BasedFunctor.id (fiberProduct F G) :=
    eqToIso (baseChangeDiagonalComparison_comp_inv F G)
  let e₂ := baseChangeDiagonalComparisonCounit F G
  exact Functor.IsEquivalence.mk'
    (baseChangeDiagonalComparisonInv F G).toFunctor
    ((BasedNatTrans.forgetful _ _).mapIso e₁)
    ((BasedNatTrans.forgetful _ _).mapIso e₂)

/-- The map between the two squares induced by precomposing a morphism with another
morphism. -/
def sourceEquivalenceDiagonalTarget
    {U : BasedCategory.{v₄, u₄} S} (E : U ⥤ᵇ X) (F : X ⥤ᵇ Y) :
    fiberProduct (E.comp F) (E.comp F) ⥤ᵇ fiberProduct F F :=
  fiberProductPresentationMap F F E E

/-- The diagonal after precomposition, followed by the induced map of squares, is the
precomposition of the original diagonal. -/
lemma sourceEquivalenceDiagonal_comp_target
    {U : BasedCategory.{v₄, u₄} S} (E : U ⥤ᵇ X) (F : X ⥤ᵇ Y) :
    (E.comp F).diag.comp (sourceEquivalenceDiagonalTarget E F) =
      E.comp F.diag := by
  apply BasedFunctor.ext_of_toFunctor_eq
  rfl

/-- If the precomposition is an equivalence, then so is the induced map between the
two squares. -/
theorem isEquivalence_sourceEquivalenceDiagonalTarget
    {U : BasedCategory.{v₄, u₄} S} (E : U ⥤ᵇ X) (F : X ⥤ᵇ Y)
    [U.p.IsFiberedInGroupoids] [X.p.IsFiberedInGroupoids]
    [E.toFunctor.IsEquivalence] :
    (sourceEquivalenceDiagonalTarget E F).toFunctor.IsEquivalence := by
  let L := fiberProductLeftMap F (E.comp F) E
  let R := fiberProductRightMap F F E
  have hL : L.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductLeftMap F (E.comp F) E
  have hR : R.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap F F E
  rw [sourceEquivalenceDiagonalTarget,
    fiberProductPresentationMap_eq_leftMap_comp_rightMap]
  exact Functor.isEquivalence_trans L.toFunctor R.toFunctor

/-- The map between the squares of two 2-isomorphic morphisms. -/
def morphismIsoDiagonalTarget {F G : X ⥤ᵇ Y} (e : F ≅ G) :
    fiberProduct F F ⥤ᵇ fiberProduct G G :=
  (fiberProductMapLeftIso e F).comp (fiberProductMapRightIso G e)

/-- The map between the squares of two 2-isomorphic morphisms is an equivalence. -/
theorem isEquivalence_morphismIsoDiagonalTarget {F G : X ⥤ᵇ Y}
    (e : F ≅ G) :
    (morphismIsoDiagonalTarget e).toFunctor.IsEquivalence := by
  let L := fiberProductMapLeftIso e F
  let R := fiberProductMapRightIso G e
  have hL : L.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapLeftIso e F
  have hR : R.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso G e
  exact Functor.isEquivalence_trans L.toFunctor R.toFunctor

/-- Passing between the squares of two 2-isomorphic morphisms identifies their
diagonals. -/
noncomputable def morphismIsoDiagonalIso {F G : X ⥤ᵇ Y} (e : F ≅ G) :
    F.diag.comp (morphismIsoDiagonalTarget e) ≅ G.diag :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun x ↦ by
        let e₁ : ((F.diag.comp (morphismIsoDiagonalTarget e)).obj x).fst ≅
            (G.diag.obj x).fst := eqToIso (by rfl)
        let e₂ : ((F.diag.comp (morphismIsoDiagonalTarget e)).obj x).snd ≅
            (G.diag.obj x).snd := eqToIso (by rfl)
        apply FiberProductObj.isoMk e₁ e₂
        · exact isHomLift_map_of_common_lift (𝟙 (X.p.obj x))
            e₁.hom e₂.hom (IsHomLift.id rfl) (IsHomLift.id rfl)
        · dsimp [e₁, e₂, morphismIsoDiagonalTarget,
            fiberProductMapLeftIso, fiberProductMapRightIso,
            BasedFunctor.comp, BasedFunctor.diag, fiberProductLift,
            BasedFunctor.id, BasedNatTrans.id,
            BasedNatIso.mkNatIso, BasedNatTrans.forgetful]
          simp only [G.toFunctor.map_id, Category.comp_id]
          exact (basedNatIsoApp e x).inv_hom_id.symm)
      (fun {x y} f ↦ by
        apply FiberProductHom.ext <;>
          dsimp [morphismIsoDiagonalTarget, fiberProductMapLeftIso,
            fiberProductMapRightIso, BasedFunctor.comp,
            BasedFunctor.diag, fiberProductLift, BasedFunctor.id,
            BasedNatTrans.id, BasedNatIso.mkNatIso,
            BasedNatTrans.forgetful] <;> simp))
    (fun x ↦ by
      apply FiberProductHom.isHomLift_of_fst _ (𝟙 (X.p.obj x))
      exact IsHomLift.id rfl)

end CategoryTheory.BasedCategory

namespace CategoryTheory.BasedFunctor

open CategoryTheory.BasedCategory

variable {S : Type u₁} [Category.{v₁} S]
  {X : BasedCategory.{v₂, u₂} S}
  {Y : BasedCategory.{v₃, u₃} S}
  {Z : BasedCategory.{v₄, u₄} S}

/-- A property of the relative diagonal is preserved by base change. -/
theorem RelativelyRepresentableWith.diag_fiberProductSnd
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    [Z.p.IsFiberedInGroupoids]
    {P : MorphismProperty S} {F : X ⥤ᵇ Y}
    (h : F.diag.RelativelyRepresentableWith P) (G : Z ⥤ᵇ Y) :
    (BasedCategory.fiberProductSnd F G).diag.RelativelyRepresentableWith P := by
  let K := baseChangeDiagonalTarget F G
  let E := baseChangeDiagonalComparison F G
  let _ : E.toFunctor.IsEquivalence :=
    isEquivalence_baseChangeDiagonalComparison F G
  have hbase := h.fiberProductSnd K
  have hcomp := hbase.comp_of_isEquivalence E
  dsimp only [E, K] at hcomp
  rw [baseChangeDiagonalComparison_comp_snd] at hcomp
  exact hcomp

/-- A property of a relative diagonal is invariant under replacing the source of the
original morphism by an equivalent prestack. -/
theorem RelativelyRepresentableWith.diag_comp_of_isEquivalence
    {U : BasedCategory.{v₄, u₄} S}
    [U.p.IsFiberedInGroupoids] [X.p.IsFiberedInGroupoids]
    [Y.p.IsFiberedInGroupoids]
    {P : MorphismProperty S} {F : X ⥤ᵇ Y}
    (h : F.diag.RelativelyRepresentableWith P) (E : U ⥤ᵇ X)
    [E.toFunctor.IsEquivalence] :
    (E.comp F).diag.RelativelyRepresentableWith P := by
  let K := sourceEquivalenceDiagonalTarget E F
  let _ : K.toFunctor.IsEquivalence :=
    isEquivalence_sourceEquivalenceDiagonalTarget E F
  have hsource := h.comp_of_isEquivalence E
  have hcomp : ((E.comp F).diag.comp K).RelativelyRepresentableWith P := by
    dsimp only [K]
    rw [sourceEquivalenceDiagonal_comp_target]
    exact hsource
  exact hcomp.of_comp_target_isEquivalence
    (isEquivalence_sourceEquivalenceDiagonalTarget E F)

/-- A property of a relative diagonal is invariant under 2-isomorphism of the original
morphisms. -/
theorem RelativelyRepresentableWith.diag_of_iso
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    {P : MorphismProperty S} {F G : X ⥤ᵇ Y}
    (h : F.diag.RelativelyRepresentableWith P) (e : F ≅ G) :
    G.diag.RelativelyRepresentableWith P := by
  let K := morphismIsoDiagonalTarget e
  let _ : K.toFunctor.IsEquivalence :=
    isEquivalence_morphismIsoDiagonalTarget e
  exact (h.comp_target_isEquivalence K).of_iso (morphismIsoDiagonalIso e)

end CategoryTheory.BasedFunctor

namespace AlgebraicGeometry.BasedFunctor

open CategoryTheory.BasedCategory

universe u

variable {X : BasedCategory.{v₁, u₁} Scheme.{u}}
  {Y : BasedCategory.{v₂, u₂} Scheme.{u}}
  {Z : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- A property of a relative diagonal, expressed by `RepresentableWith`, is preserved
by base change. -/
theorem RepresentableWith.diag_fiberProductSnd
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    [Z.p.IsFiberedInGroupoids]
    {P : MorphismProperty Scheme.{u}} {F : X ⥤ᵇ Y}
    (h : RepresentableWith P F.diag) (G : Z ⥤ᵇ Y) :
    RepresentableWith P (BasedCategory.fiberProductSnd F G).diag := by
  let K := baseChangeDiagonalTarget F G
  let E := baseChangeDiagonalComparison F G
  let _ : E.toFunctor.IsEquivalence :=
    isEquivalence_baseChangeDiagonalComparison F G
  have hbase := h.fiberProductSnd K
  have hcomp := hbase.comp_source_isEquivalence E
  dsimp only [E, K] at hcomp
  rw [baseChangeDiagonalComparison_comp_snd] at hcomp
  exact hcomp

/-- A property of a relative diagonal may be checked on the diagonals of all of its
base changes by schemes, provided the property is local on the source for surjective
étale morphisms. -/
theorem RepresentableWith.diag_of_forall_fiberProductSnd
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    {P : MorphismProperty Scheme.{u}} {F : X ⥤ᵇ Y}
    (hlocal : ∀ ⦃S' S T : Scheme.{u}⦄ (p : S' ⟶ S) (f : S ⟶ T),
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) p →
        (P f ↔ P (p ≫ f)))
    (h : ∀ (T : Scheme.{u}) (G : overBased T ⥤ᵇ Y),
      RepresentableWith P (BasedCategory.fiberProductSnd F G).diag) :
    RepresentableWith P F.diag := by
  have hrep : Representable F.diag := by
    intro T g
    let G := (relativeDiagonalPointFst F g).comp F
    let K := baseChangeDiagonalTarget F G
    let E := baseChangeDiagonalComparison F G
    let _ : E.toFunctor.IsEquivalence :=
      isEquivalence_baseChangeDiagonalComparison F G
    let D := BasedCategory.fiberProductSnd F.diag K
    have hcomp : RepresentableWith P (E.comp D) := by
      dsimp only [E, D, K]
      rw [baseChangeDiagonalComparison_comp_snd]
      exact h T G
    have hD : RepresentableWith P D :=
      RepresentableWith.of_comp_isEquivalence E hcomp
    let l := relativeDiagonalTargetLift F g
    let e := relativeDiagonalTargetLiftIso F g
    let L₁ := fiberProductAssoc F.diag K l
    let L₂ := fiberProductMapRightIso F.diag e
    let _ : L₁.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductAssoc F.diag K l
    let _ : L₂.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductMapRightIso F.diag e
    let L := L₁.comp L₂
    have hL : L.toFunctor.IsEquivalence := by
      exact Functor.isEquivalence_trans L₁.toFunctor L₂.toFunctor
    obtain ⟨A, hA, R, hR⟩ := hD.1 T l
    exact ⟨A, hA, R.comp L,
      Functor.isEquivalence_trans R.toFunctor L.toFunctor⟩
  apply RepresentableWith.of_exists_good_chart hrep hlocal
  intro T g
  let G := (relativeDiagonalPointFst F g).comp F
  let K := baseChangeDiagonalTarget F G
  let E := baseChangeDiagonalComparison F G
  let _ : E.toFunctor.IsEquivalence :=
    isEquivalence_baseChangeDiagonalComparison F G
  let D := BasedCategory.fiberProductSnd F.diag K
  have hcomp : RepresentableWith P (E.comp D) := by
    dsimp only [E, D, K]
    rw [baseChangeDiagonalComparison_comp_snd]
    exact h T G
  have hD : RepresentableWith P D :=
    RepresentableWith.of_comp_isEquivalence E hcomp
  let l := relativeDiagonalTargetLift F g
  let e := relativeDiagonalTargetLiftIso F g
  let L₁ := fiberProductAssoc F.diag K l
  let L₂ := fiberProductMapRightIso F.diag e
  let _ : L₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductAssoc F.diag K l
  let _ : L₂.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso F.diag e
  let L := L₁.comp L₂
  let _ : L.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans L₁.toFunctor L₂.toFunctor
  obtain ⟨A, hA, R, hR⟩ := hD.1 T l
  let _ : IsAlgebraicSpace A := hA
  let _ : R.toFunctor.IsEquivalence := hR
  obtain ⟨U, q, hq⟩ := IsAlgebraicSpace.exists_presentation (X := A)
  let p₀ : overBased U ⥤ᵇ fiberProduct D l :=
    (overBasedToOfPresheafYoneda U).comp ((ofPresheaf.map q).comp R)
  have hp₀rel : p₀.RelativelyRepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
    ((relativelyRepresentableWith_ofPresheaf_map hq).comp_of_isEquivalence
      (overBasedToOfPresheafYoneda U)).comp_target_isEquivalence R
  have hp₀ : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) p₀ :=
    RelativelyRepresentableWith.representableWith le_rfl hp₀rel
  let p := p₀.comp L
  have hp : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) p :=
    hp₀.comp_target_isEquivalence L
  refine ⟨U, p, hp, ?_⟩
  have hP₀ : P (p₀.comp (BasedCategory.fiberProductSnd D l)).overHom := by
    simpa only [p₀, CategoryTheory.BasedFunctor.comp_assoc] using
      hD.2 T l A hA R hR U q hq
  have hL₂snd : L₂.comp (BasedCategory.fiberProductSnd F.diag g) =
      BasedCategory.fiberProductSnd F.diag (l.comp K) := by
    apply CategoryTheory.BasedFunctor.ext_of_toFunctor_eq
    rfl
  have hLsnd : L.comp (BasedCategory.fiberProductSnd F.diag g) =
      BasedCategory.fiberProductSnd D l := by
    rw [show L.comp (BasedCategory.fiberProductSnd F.diag g) =
      L₁.comp (L₂.comp (BasedCategory.fiberProductSnd F.diag g)) by
        exact CategoryTheory.BasedFunctor.comp_assoc L₁ L₂ _]
    rw [hL₂snd]
    exact fiberProductAssoc_comp_snd F.diag K l
  simpa only [p, CategoryTheory.BasedFunctor.comp_assoc, hLsnd] using hP₀

end AlgebraicGeometry.BasedFunctor
