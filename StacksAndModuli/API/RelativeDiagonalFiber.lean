module

public import StacksAndModuli.API.FiberProductPostcomp

/-!
# Fibers of relative diagonals as fibers of maps between Isom prestacks

For a morphism of prestacks `F : X ⟶ Y` and a point
`g : T ⟶ X ×_Y X`, the two projections of `g` determine Isom prestacks in
`X` and `Y`.  Postcomposition by `F` gives a morphism between them, while the
2-isomorphism carried by `g` gives a section of the target Isom prestack.

This file packages these two morphisms and the canonical comparison from their
fiber product to the fiber of the relative diagonal of `F` over `g`.  The main
result, `isEquivalence_isomMapFiberToRelativeDiagonalFiber`, proves that comparison
is an equivalence.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedCategory

variable {S : Type u₁} [Category.{v₁} S]
  {X : BasedCategory.{v₂, u₂} S} {Y : BasedCategory.{v₃, u₃} S}
  {T : BasedCategory.{v₄, u₄} S}

/-- The first `X`-valued point underlying a point of `X ×_Y X`. -/
abbrev relativeDiagonalPointFst (F : X ⥤ᵇ Y) (g : T ⥤ᵇ fiberProduct F F) :
    T ⥤ᵇ X :=
  g.comp (fiberProductFst F F)

/-- The second `X`-valued point underlying a point of `X ×_Y X`. -/
abbrev relativeDiagonalPointSnd (F : X ⥤ᵇ Y) (g : T ⥤ᵇ fiberProduct F F) :
    T ⥤ᵇ X :=
  g.comp (fiberProductSnd F F)

/-- Postcomposition by `F` sends isomorphisms between the two `X`-valued points
underlying `g` to isomorphisms between their images in `Y`. -/
abbrev relativeDiagonalIsomMap (F : X ⥤ᵇ Y) (g : T ⥤ᵇ fiberProduct F F) :
    fiberProduct (relativeDiagonalPointFst F g) (relativeDiagonalPointSnd F g) ⥤ᵇ
      fiberProduct ((relativeDiagonalPointFst F g).comp F)
        ((relativeDiagonalPointSnd F g).comp F) :=
  fiberProductPostcomp (relativeDiagonalPointFst F g)
    (relativeDiagonalPointSnd F g) F

/-- The comparison isomorphism carried by `g : T ⟶ X ×_Y X`, regarded as a
section of the Isom prestack between the two induced `Y`-valued points. -/
abbrev relativeDiagonalIsomSection (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F) :
    T ⥤ᵇ fiberProduct ((relativeDiagonalPointFst F g).comp F)
      ((relativeDiagonalPointSnd F g).comp F) :=
  fiberProductLift (BasedFunctor.id T) (BasedFunctor.id T)
    (whiskerLeftIso g (fiberProductIsoComm F F))

/-- The object of the relative-diagonal fiber determined by an object in the
fiber of the map between Isom prestacks. -/
def isomMapFiberToRelativeDiagonalFiberObj (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F)
    (q : (fiberProduct (relativeDiagonalIsomMap F g)
      (relativeDiagonalIsomSection F g)).obj) :
    (fiberProduct F.diag g).obj := by
  let a := relativeDiagonalPointFst F g
  let b := relativeDiagonalPointSnd F g
  let e₁ : a.obj q.fst.fst ≅ (g.obj q.snd).fst :=
    a.toFunctor.mapIso (FiberProductObj.isoFst q.iso)
  let e₂ : a.obj q.fst.fst ≅ (g.obj q.snd).snd :=
    q.fst.iso ≪≫ b.toFunctor.mapIso (FiberProductObj.isoSnd q.iso)
  let e : F.diag.obj (a.obj q.fst.fst) ≅ g.obj q.snd := by
    apply FiberProductObj.isoMk (a := F.diag.obj (a.obj q.fst.fst))
      (b := g.obj q.snd) e₁ e₂
    · haveI hq : IsHomLift
          (fiberProduct ((a).comp F) ((b).comp F)).p
          (𝟙 ((fiberProduct a b).p.obj q.fst)) q.iso.hom := q.isHomLift
      haveI h₁ : IsHomLift T.p (𝟙 ((fiberProduct a b).p.obj q.fst))
          (FiberProductObj.isoFst q.iso).hom :=
        FiberProductHom.isHomLift_fst q.iso.hom _ hq
      haveI h₂ : IsHomLift T.p (𝟙 ((fiberProduct a b).p.obj q.fst))
          (FiberProductObj.isoSnd q.iso).hom :=
        FiberProductHom.isHomLift_snd q.iso.hom _ hq
      haveI hbeta : IsHomLift X.p (𝟙 (T.p.obj q.fst.fst)) q.fst.iso.hom :=
        q.fst.isHomLift
      haveI he₁ : IsHomLift X.p
          (𝟙 ((fiberProduct a b).p.obj q.fst)) e₁.hom := by
        change IsHomLift X.p (𝟙 ((fiberProduct a b).p.obj q.fst))
          (a.map (FiberProductObj.isoFst q.iso).hom)
        exact a.preserves_isHomLift _ _
      haveI hb₂ : IsHomLift X.p
          (𝟙 ((fiberProduct a b).p.obj q.fst))
          (b.map (FiberProductObj.isoSnd q.iso).hom) := by
        exact b.preserves_isHomLift _ _
      haveI he₂ : IsHomLift X.p
          (𝟙 ((fiberProduct a b).p.obj q.fst)) e₂.hom := by
        change IsHomLift X.p (𝟙 ((fiberProduct a b).p.obj q.fst))
          (q.fst.iso.hom ≫ b.map (FiberProductObj.isoSnd q.iso).hom)
        infer_instance
      exact isHomLift_map_of_common_lift
        (𝟙 ((fiberProduct a b).p.obj q.fst)) e₁.hom e₂.hom
        he₁ he₂
    · dsimp only [e₁, e₂, Iso.trans_hom, Functor.mapIso_hom]
      rw [F.toFunctor.map_comp]
      have hdiag : (F.diag.obj (a.obj q.fst.fst)).iso.hom =
          𝟙 (F.obj (a.obj q.fst.fst)) := rfl
      rw [hdiag]
      have hw := q.iso.hom.w
      change F.map (a.map (FiberProductObj.isoFst q.iso).hom) ≫
          (g.obj q.snd).iso.hom =
        F.map q.fst.iso.hom ≫
          F.map (b.map (FiberProductObj.isoSnd q.iso).hom) at hw
      calc
        F.map (a.map (FiberProductObj.isoFst q.iso).hom) ≫
            (g.obj q.snd).iso.hom =
          F.map q.fst.iso.hom ≫
            F.map (b.map (FiberProductObj.isoSnd q.iso).hom) := hw
        _ = 𝟙 (F.obj (a.obj q.fst.fst)) ≫
            F.map q.fst.iso.hom ≫
              F.map (b.map (FiberProductObj.isoSnd q.iso).hom) := by simp
  exact
    { fst := a.obj q.fst.fst
      snd := q.snd
      over_eq := q.over_eq.trans (a.w_obj q.fst.fst).symm
      iso := e
      isHomLift := by
        haveI hq : IsHomLift
            (fiberProduct ((a).comp F) ((b).comp F)).p
            (𝟙 ((fiberProduct a b).p.obj q.fst)) q.iso.hom := q.isHomLift
        haveI h₁ : IsHomLift T.p (𝟙 ((fiberProduct a b).p.obj q.fst))
            (FiberProductObj.isoFst q.iso).hom :=
          FiberProductHom.isHomLift_fst q.iso.hom _ hq
        haveI he₁ : IsHomLift X.p
            (𝟙 ((fiberProduct a b).p.obj q.fst)) e₁.hom := by
          change IsHomLift X.p (𝟙 ((fiberProduct a b).p.obj q.fst))
            (a.map (FiberProductObj.isoFst q.iso).hom)
          exact a.preserves_isHomLift _ _
        rw [a.w_obj]
        exact FiberProductHom.isHomLift_of_fst e.hom _ he₁ }

/-- The canonical comparison from the fiber of the map between Isom prestacks to
the corresponding fiber of the relative diagonal. -/
def isomMapFiberToRelativeDiagonalFiber (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F) :
    fiberProduct (relativeDiagonalIsomMap F g)
        (relativeDiagonalIsomSection F g) ⥤ᵇ
      fiberProduct F.diag g where
  obj := isomMapFiberToRelativeDiagonalFiberObj F g
  map {q r} φ :=
    { fst := (relativeDiagonalPointFst F g).map φ.fst.fst
      snd := φ.snd
      isHomLift := by
        let a := relativeDiagonalPointFst F g
        let b := relativeDiagonalPointSnd F g
        let f := (fiberProduct a b).p.map φ.fst
        haveI hφ : IsHomLift (fiberProduct a b).p f φ.fst :=
          IsHomLift.map _ _
        haveI hφfst : IsHomLift T.p f φ.fst.fst :=
          FiberProductHom.isHomLift_fst φ.fst f hφ
        haveI haφ : IsHomLift X.p f (a.map φ.fst.fst) :=
          a.preserves_isHomLift f φ.fst.fst
        exact isHomLift_map_of_common_lift f (a.map φ.fst.fst) φ.snd
          haφ φ.isHomLift
      w := by
        let a := relativeDiagonalPointFst F g
        let b := relativeDiagonalPointSnd F g
        apply FiberProductHom.ext
        · change a.map φ.fst.fst ≫
              (a.map (FiberProductObj.isoFst r.iso).hom) =
            (a.map (FiberProductObj.isoFst q.iso).hom) ≫
              (g.map φ.snd).fst
          have hfst := congrArg FiberProductHom.fst φ.w
          change φ.fst.fst ≫ (FiberProductObj.isoFst r.iso).hom =
            (FiberProductObj.isoFst q.iso).hom ≫ φ.snd at hfst
          calc
            a.map φ.fst.fst ≫ a.map (FiberProductObj.isoFst r.iso).hom =
                a.map (φ.fst.fst ≫ (FiberProductObj.isoFst r.iso).hom) := by
              rw [a.toFunctor.map_comp]
            _ = a.map ((FiberProductObj.isoFst q.iso).hom ≫ φ.snd) :=
              congrArg a.map hfst
            _ = a.map (FiberProductObj.isoFst q.iso).hom ≫ a.map φ.snd := by
              rw [a.toFunctor.map_comp]
            _ = a.map (FiberProductObj.isoFst q.iso).hom ≫ (g.map φ.snd).fst := rfl
        · change a.map φ.fst.fst ≫
              (r.fst.iso.hom ≫ b.map (FiberProductObj.isoSnd r.iso).hom) =
            (q.fst.iso.hom ≫ b.map (FiberProductObj.isoSnd q.iso).hom) ≫
              (g.map φ.snd).snd
          have hbeta := φ.fst.w
          change a.map φ.fst.fst ≫ r.fst.iso.hom =
            q.fst.iso.hom ≫ b.map φ.fst.snd at hbeta
          have hsnd := congrArg FiberProductHom.snd φ.w
          change φ.fst.snd ≫ (FiberProductObj.isoSnd r.iso).hom =
            (FiberProductObj.isoSnd q.iso).hom ≫ φ.snd at hsnd
          calc
            a.map φ.fst.fst ≫ r.fst.iso.hom ≫
                b.map (FiberProductObj.isoSnd r.iso).hom =
              (q.fst.iso.hom ≫ b.map φ.fst.snd) ≫
                b.map (FiberProductObj.isoSnd r.iso).hom :=
              (Category.assoc _ _ _).symm.trans
                (congrArg
                  (fun k ↦ k ≫ b.map (FiberProductObj.isoSnd r.iso).hom) hbeta)
            _ = q.fst.iso.hom ≫
                (b.map φ.fst.snd ≫ b.map (FiberProductObj.isoSnd r.iso).hom) := by
              rw [Category.assoc]
            _ = q.fst.iso.hom ≫
                b.map (φ.fst.snd ≫ (FiberProductObj.isoSnd r.iso).hom) := by
              rw [b.toFunctor.map_comp]
            _ = q.fst.iso.hom ≫
                b.map ((FiberProductObj.isoSnd q.iso).hom ≫ φ.snd) := by rw [hsnd]
            _ = q.fst.iso.hom ≫
                (b.map (FiberProductObj.isoSnd q.iso).hom ≫ b.map φ.snd) := by
              rw [b.toFunctor.map_comp]
            _ = (q.fst.iso.hom ≫ b.map (FiberProductObj.isoSnd q.iso).hom) ≫
                (g.map φ.snd).snd := by
              change q.fst.iso.hom ≫
                  (b.map (FiberProductObj.isoSnd q.iso).hom ≫ b.map φ.snd) =
                (q.fst.iso.hom ≫ b.map (FiberProductObj.isoSnd q.iso).hom) ≫
                  b.map φ.snd
              rw [Category.assoc] }
  map_id q := by
    apply FiberProductHom.ext
    · exact (relativeDiagonalPointFst F g).toFunctor.map_id _
    · rfl
  map_comp φ ψ := by
    apply FiberProductHom.ext
    · exact (relativeDiagonalPointFst F g).toFunctor.map_comp _ _
    · rfl
  w := by
    let a := relativeDiagonalPointFst F g
    let b := relativeDiagonalPointSnd F g
    let N := relativeDiagonalIsomMap F g
    let H := relativeDiagonalIsomSection F g
    let K := ((fiberProductFst N H).comp (fiberProductFst a b)).comp a
    exact K.w

/-- The relative-diagonal fiber comparison is faithful. -/
lemma isomMapFiberToRelativeDiagonalFiber_faithful (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F) :
    (isomMapFiberToRelativeDiagonalFiber F g).toFunctor.Faithful := by
  constructor
  intro q r φ ψ h
  have hs : φ.snd = ψ.snd :=
    congrArg
      (fun k : (isomMapFiberToRelativeDiagonalFiber F g).obj q ⟶
        (isomMapFiberToRelativeDiagonalFiber F g).obj r ↦ FiberProductHom.snd k) h
  have hφ₁ := congrArg FiberProductHom.fst φ.w
  have hψ₁ := congrArg FiberProductHom.fst ψ.w
  change φ.fst.fst ≫ (FiberProductObj.isoFst r.iso).hom =
    (FiberProductObj.isoFst q.iso).hom ≫ φ.snd at hφ₁
  change ψ.fst.fst ≫ (FiberProductObj.isoFst r.iso).hom =
    (FiberProductObj.isoFst q.iso).hom ≫ ψ.snd at hψ₁
  have h₁ : φ.fst.fst = ψ.fst.fst := by
    rw [← cancel_mono (FiberProductObj.isoFst r.iso).hom]
    rw [hφ₁, hψ₁, hs]
  have hφ₂ := congrArg FiberProductHom.snd φ.w
  have hψ₂ := congrArg FiberProductHom.snd ψ.w
  change φ.fst.snd ≫ (FiberProductObj.isoSnd r.iso).hom =
    (FiberProductObj.isoSnd q.iso).hom ≫ φ.snd at hφ₂
  change ψ.fst.snd ≫ (FiberProductObj.isoSnd r.iso).hom =
    (FiberProductObj.isoSnd q.iso).hom ≫ ψ.snd at hψ₂
  have h₂ : φ.fst.snd = ψ.fst.snd := by
    rw [← cancel_mono (FiberProductObj.isoSnd r.iso).hom]
    rw [hφ₂, hψ₂, hs]
  exact FiberProductHom.ext (FiberProductHom.ext h₁ h₂) hs

/-- The relative-diagonal fiber comparison is full. -/
lemma isomMapFiberToRelativeDiagonalFiber_full (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F) :
    (isomMapFiberToRelativeDiagonalFiber F g).toFunctor.Full := by
  constructor
  intro q r k
  let a := relativeDiagonalPointFst F g
  let b := relativeDiagonalPointSnd F g
  let u₁ : q.fst.fst ⟶ r.fst.fst :=
    (FiberProductObj.isoFst q.iso).hom ≫ k.snd ≫
      (FiberProductObj.isoFst r.iso).inv
  let u₂ : q.fst.snd ⟶ r.fst.snd :=
    (FiberProductObj.isoSnd q.iso).hom ≫ k.snd ≫
      (FiberProductObj.isoSnd r.iso).inv
  have hk₁ := congrArg FiberProductHom.fst k.w
  change k.fst ≫ a.map (FiberProductObj.isoFst r.iso).hom =
    a.map (FiberProductObj.isoFst q.iso).hom ≫ a.map k.snd at hk₁
  have har : a.map (FiberProductObj.isoFst r.iso).hom ≫
      a.map (FiberProductObj.isoFst r.iso).inv = 𝟙 (a.obj r.fst.fst) := by
    exact (a.toFunctor.mapIso (FiberProductObj.isoFst r.iso)).hom_inv_id
  have hu₁ : a.map u₁ = k.fst := by
    dsimp only [u₁]
    rw [a.toFunctor.map_comp, a.toFunctor.map_comp]
    calc
      a.map (FiberProductObj.isoFst q.iso).hom ≫
          a.map k.snd ≫ a.map (FiberProductObj.isoFst r.iso).inv =
        (a.map (FiberProductObj.isoFst q.iso).hom ≫ a.map k.snd) ≫
          a.map (FiberProductObj.isoFst r.iso).inv := (Category.assoc _ _ _).symm
      _ = (k.fst ≫ a.map (FiberProductObj.isoFst r.iso).hom) ≫
          a.map (FiberProductObj.isoFst r.iso).inv :=
        congrArg (fun z ↦ z ≫ a.map (FiberProductObj.isoFst r.iso).inv) hk₁.symm
      _ = k.fst ≫ 𝟙 (a.obj r.fst.fst) := by
        rw [Category.assoc, har]
      _ = k.fst := Category.comp_id _
  have hk₂ := congrArg FiberProductHom.snd k.w
  change k.fst ≫
      (r.fst.iso.hom ≫ b.map (FiberProductObj.isoSnd r.iso).hom) =
    (q.fst.iso.hom ≫ b.map (FiberProductObj.isoSnd q.iso).hom) ≫
      b.map k.snd at hk₂
  have huCompat : a.map u₁ ≫ r.fst.iso.hom =
      q.fst.iso.hom ≫ b.map u₂ := by
    rw [hu₁]
    rw [← cancel_mono (b.toFunctor.mapIso (FiberProductObj.isoSnd r.iso)).hom]
    dsimp only [u₂, Functor.mapIso_hom]
    rw [b.toFunctor.map_comp, b.toFunctor.map_comp]
    simp only [Category.assoc, ← b.toFunctor.map_comp, Iso.inv_hom_id,
      Category.comp_id]
    simpa only [b.toFunctor.map_comp, Category.assoc] using hk₂
  haveI hq : IsHomLift
      (fiberProduct (a.comp F) (b.comp F)).p
      (𝟙 ((fiberProduct a b).p.obj q.fst)) q.iso.hom := q.isHomLift
  haveI hq₁ : IsHomLift T.p (𝟙 ((fiberProduct a b).p.obj q.fst))
      (FiberProductObj.isoFst q.iso).hom :=
    FiberProductHom.isHomLift_fst q.iso.hom _ hq
  haveI hq₂ : IsHomLift T.p (𝟙 ((fiberProduct a b).p.obj q.fst))
      (FiberProductObj.isoSnd q.iso).hom :=
    FiberProductHom.isHomLift_snd q.iso.hom _ hq
  haveI hrHom : IsHomLift
      (fiberProduct (a.comp F) (b.comp F)).p
      (𝟙 ((fiberProduct a b).p.obj r.fst)) r.iso.hom := r.isHomLift
  haveI hrInv : IsHomLift
      (fiberProduct (a.comp F) (b.comp F)).p
      (𝟙 ((fiberProduct a b).p.obj r.fst)) r.iso.inv :=
    IsHomLift.lift_id_inv _ _ r.iso
  haveI hr₁ : IsHomLift T.p (𝟙 ((fiberProduct a b).p.obj r.fst))
      (FiberProductObj.isoFst r.iso).inv :=
    FiberProductHom.isHomLift_fst r.iso.inv _ hrInv
  haveI hr₂ : IsHomLift T.p (𝟙 ((fiberProduct a b).p.obj r.fst))
      (FiberProductObj.isoSnd r.iso).inv :=
    FiberProductHom.isHomLift_snd r.iso.inv _ hrInv
  haveI hu₁Lift : IsHomLift T.p (X.p.map k.fst) u₁ := by
    apply IsHomLift.of_fac' T.p (X.p.map k.fst) u₁
      (a.w_obj q.fst.fst).symm (a.w_obj r.fst.fst).symm
    rw [← hu₁]
    have ha := Functor.congr_hom a.w u₁
    simp only [Functor.comp_map] at ha
    rw [ha]
    simp
  haveI hu₂Lift : IsHomLift T.p (X.p.map k.fst) u₂ := by
    let hdom := q.fst.over_eq.trans (a.w_obj q.fst.fst).symm
    let hcod := r.fst.over_eq.trans (a.w_obj r.fst.fst).symm
    apply IsHomLift.of_fac' T.p (X.p.map k.fst) u₂ hdom hcod
    dsimp only [u₂]
    rw [T.p.map_comp, T.p.map_comp,
      IsHomLift.fac' T.p (𝟙 ((fiberProduct a b).p.obj q.fst))
        (FiberProductObj.isoSnd q.iso).hom,
      IsHomLift.fac' T.p (X.p.map k.fst) k.snd,
      IsHomLift.fac' T.p (𝟙 ((fiberProduct a b).p.obj r.fst))
        (FiberProductObj.isoSnd r.iso).inv]
    simp [hcod]
  let v : q ⟶ r :=
    { fst :=
        { fst := u₁
          snd := u₂
          isHomLift := isHomLift_map_of_common_lift (X.p.map k.fst) u₁ u₂
            hu₁Lift hu₂Lift
          w := huCompat }
      snd := k.snd
      isHomLift := isHomLift_map_of_common_lift (X.p.map k.fst) u₁ k.snd
        hu₁Lift k.isHomLift
      w := by
        apply FiberProductHom.ext
        · change u₁ ≫ (FiberProductObj.isoFst r.iso).hom =
            (FiberProductObj.isoFst q.iso).hom ≫ k.snd
          have hid : (FiberProductObj.isoFst r.iso).inv ≫
              (FiberProductObj.isoFst r.iso).hom = 𝟙 r.snd := by
            have h := congrArg FiberProductHom.fst r.iso.inv_hom_id
            change r.iso.inv.fst ≫ r.iso.hom.fst = 𝟙 r.snd at h
            exact h
          dsimp only [u₁]
          rw [Category.assoc,
            Category.assoc k.snd (FiberProductObj.isoFst r.iso).inv
              (FiberProductObj.isoFst r.iso).hom,
            hid]
          exact congrArg (fun z ↦ (FiberProductObj.isoFst q.iso).hom ≫ z)
            (Category.comp_id k.snd)
        · change u₂ ≫ (FiberProductObj.isoSnd r.iso).hom =
            (FiberProductObj.isoSnd q.iso).hom ≫ k.snd
          have hid : (FiberProductObj.isoSnd r.iso).inv ≫
              (FiberProductObj.isoSnd r.iso).hom = 𝟙 r.snd := by
            have h := congrArg FiberProductHom.snd r.iso.inv_hom_id
            change r.iso.inv.snd ≫ r.iso.hom.snd = 𝟙 r.snd at h
            exact h
          dsimp only [u₂]
          rw [Category.assoc,
            Category.assoc k.snd (FiberProductObj.isoSnd r.iso).inv
              (FiberProductObj.isoSnd r.iso).hom,
            hid]
          exact congrArg (fun z ↦ (FiberProductObj.isoSnd q.iso).hom ≫ z)
            (Category.comp_id k.snd) }
  refine ⟨v, ?_⟩
  apply FiberProductHom.ext
  · exact hu₁
  · rfl

/-- The relative-diagonal fiber comparison is essentially surjective. -/
lemma isomMapFiberToRelativeDiagonalFiber_essSurj (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F) :
    (isomMapFiberToRelativeDiagonalFiber F g).toFunctor.EssSurj := by
  constructor
  intro r
  let a := relativeDiagonalPointFst F g
  let b := relativeDiagonalPointSnd F g
  let e₁ := FiberProductObj.isoFst r.iso
  let e₂ := FiberProductObj.isoSnd r.iso
  let β : a.obj r.snd ≅ b.obj r.snd := e₁.symm ≪≫ e₂
  haveI hr : IsHomLift (fiberProduct F F).p
      (𝟙 (X.p.obj r.fst)) r.iso.hom := r.isHomLift
  haveI hrInv : IsHomLift (fiberProduct F F).p
      (𝟙 (X.p.obj r.fst)) r.iso.inv := IsHomLift.lift_id_inv _ _ r.iso
  haveI he₁ : IsHomLift X.p (𝟙 (X.p.obj r.fst)) e₁.hom :=
    FiberProductHom.isHomLift_fst r.iso.hom _ hr
  haveI he₂ : IsHomLift X.p (𝟙 (X.p.obj r.fst)) e₂.hom :=
    FiberProductHom.isHomLift_snd r.iso.hom _ hr
  haveI he₁Inv : IsHomLift X.p (𝟙 (X.p.obj r.fst)) e₁.inv :=
    FiberProductHom.isHomLift_fst r.iso.inv _ hrInv
  haveI hβ : IsHomLift X.p (𝟙 (X.p.obj r.fst)) β.hom := by
    dsimp only [β, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  let qA : (fiberProduct a b).obj :=
    { fst := r.snd
      snd := r.snd
      over_eq := rfl
      iso := β
      isHomLift := by
        rw [r.over_eq]
        exact hβ }
  have hrw := r.iso.hom.w
  change F.map e₁.hom ≫ (g.obj r.snd).iso.hom =
    (F.diag.obj r.fst).iso.hom ≫ F.map e₂.hom at hrw
  have hrw' : F.map e₁.hom ≫ (g.obj r.snd).iso.hom = F.map e₂.hom := by
    apply hrw.trans
    change (𝟙 (F.obj r.fst)) ≫ F.map e₂.hom = F.map e₂.hom
    exact Category.id_comp _
  have hα : (g.obj r.snd).iso.hom = F.map β.hom := by
    rw [← cancel_epi (F.map e₁.hom)]
    rw [hrw']
    dsimp only [β, Iso.trans_hom, Iso.symm_hom]
    rw [F.toFunctor.map_comp, ← Category.assoc, ← F.toFunctor.map_comp,
      e₁.hom_inv_id, F.toFunctor.map_id, Category.id_comp]
  let qIso : (relativeDiagonalIsomMap F g).obj qA ≅
      (relativeDiagonalIsomSection F g).obj r.snd := by
    apply FiberProductObj.isoMk
      (a := (relativeDiagonalIsomMap F g).obj qA)
      (b := (relativeDiagonalIsomSection F g).obj r.snd)
      (Iso.refl r.snd) (Iso.refl r.snd)
    · change IsHomLift T.p (T.p.map (𝟙 r.snd)) (𝟙 r.snd)
      rw [T.p.map_id]
      exact IsHomLift.id rfl
    · change F.map (a.map (𝟙 r.snd)) ≫ (g.obj r.snd).iso.hom =
        F.map β.hom ≫ F.map (b.map (𝟙 r.snd))
      rw [a.toFunctor.map_id, b.toFunctor.map_id, F.toFunctor.map_id,
        F.toFunctor.map_id, Category.id_comp, Category.comp_id]
      exact hα
  have hqIsoFst : qIso.hom.fst = 𝟙 r.snd := rfl
  let q : (fiberProduct (relativeDiagonalIsomMap F g)
      (relativeDiagonalIsomSection F g)).obj :=
    { fst := qA
      snd := r.snd
      over_eq := rfl
      iso := qIso
      isHomLift := by
        apply FiberProductHom.isHomLift_of_fst qIso.hom (𝟙 (T.p.obj r.snd))
        rw [hqIsoFst]
        exact IsHomLift.id rfl }
  refine ⟨q, ⟨?_⟩⟩
  let d₁ : ((isomMapFiberToRelativeDiagonalFiber F g).obj q).fst ≅ r.fst :=
    e₁.symm
  let d₂ : ((isomMapFiberToRelativeDiagonalFiber F g).obj q).snd ≅ r.snd :=
    Iso.refl r.snd
  apply FiberProductObj.isoMk d₁ d₂
  · haveI hd₁ : IsHomLift X.p (𝟙 (X.p.obj r.fst)) d₁.hom := he₁Inv
    haveI hd₂ : IsHomLift T.p (𝟙 (X.p.obj r.fst)) d₂.hom := by
      dsimp only [d₂, Iso.refl_hom]
      rw [← r.over_eq]
      exact IsHomLift.id rfl
    exact isHomLift_map_of_common_lift (𝟙 (X.p.obj r.fst)) d₁.hom d₂.hom
      hd₁ hd₂
  · apply FiberProductHom.ext
    · change e₁.inv ≫ e₁.hom =
          a.map qIso.hom.fst ≫ (g.map (𝟙 r.snd)).fst
      dsimp only [qIso, FiberProductObj.isoMk, fiberProductObjIsoMk,
        Iso.refl_hom]
      dsimp [qA, a, relativeDiagonalPointFst, BasedFunctor.comp,
        fiberProductFst, BasedFunctor.id]
      rw [e₁.inv_hom_id, g.toFunctor.map_id,
        FiberProductObj.id_fst, Category.comp_id]
    · change e₁.inv ≫ e₂.hom =
          (β.hom ≫ b.map qIso.hom.snd) ≫ (g.map (𝟙 r.snd)).snd
      dsimp only [β, Iso.trans_hom, Iso.symm_hom]
      dsimp only [qIso, FiberProductObj.isoMk, fiberProductObjIsoMk,
        Iso.refl_hom]
      dsimp [qA, b, relativeDiagonalPointSnd, BasedFunctor.comp,
        fiberProductSnd, BasedFunctor.id]
      rw [g.toFunctor.map_id, FiberProductObj.id_snd,
        Category.comp_id, Category.comp_id]

/-- A fiber of a relative diagonal is canonically equivalent to the fiber, over the
chosen comparison isomorphism, of the induced map between Isom prestacks. -/
theorem isEquivalence_isomMapFiberToRelativeDiagonalFiber (F : X ⥤ᵇ Y)
    (g : T ⥤ᵇ fiberProduct F F) :
    (isomMapFiberToRelativeDiagonalFiber F g).toFunctor.IsEquivalence :=
  { faithful := isomMapFiberToRelativeDiagonalFiber_faithful F g
    full := isomMapFiberToRelativeDiagonalFiber_full F g
    essSurj := isomMapFiberToRelativeDiagonalFiber_essSurj F g }

end CategoryTheory.BasedCategory
