module

public import StacksAndModuli.API.PrestackProducts

/-!
# Changing a prestack fiber-product leg by a 2-isomorphism

A based natural isomorphism between two legs of a prestack fiber product induces an
equivalence between the two fiber products. The comparison leaves both component
objects and both component morphisms unchanged and adjusts only the gluing isomorphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {A : BasedCategory.{v₂, u₂} C}
  {B : BasedCategory.{v₃, u₃} C}
  {D : BasedCategory.{v₄, u₄} C}

/-- The component isomorphism of a based natural isomorphism, with its source and target
expressed through the `BasedFunctor` projections. -/
def basedNatIsoApp {F F' : A ⥤ᵇ B} (e : F ≅ F') (x : A.obj) :
    F.obj x ≅ F'.obj x := by
  exact ((BasedNatTrans.forgetful A B).mapIso e).app x

/-- Changing the left leg of a fiber product along a based natural isomorphism. -/
def fiberProductMapLeftIso {F F' : A ⥤ᵇ B} (e : F ≅ F') (G : D ⥤ᵇ B) :
    fiberProduct F G ⥤ᵇ fiberProduct F' G where
  obj x :=
    { fst := x.fst
      snd := x.snd
      over_eq := x.over_eq
      iso := (basedNatIsoApp e x.fst).symm ≪≫ x.iso
      isHomLift := by
        let _ : IsHomLift B.p (𝟙 (A.p.obj x.fst))
            (basedNatIsoApp e x.fst).inv := by
          simpa [basedNatIsoApp] using e.inv.isHomLift' x.fst
        let _ := x.isHomLift
        simpa using IsHomLift.comp B.p (𝟙 _) (𝟙 _)
          (basedNatIsoApp e x.fst).inv x.iso.hom }
  map {x y} q :=
    { fst := q.fst
      snd := q.snd
      isHomLift := q.isHomLift
      w := by
        dsimp only [Iso.trans_hom]
        have hnat : F'.map q.fst ≫ (basedNatIsoApp e y.fst).symm.hom =
            (basedNatIsoApp e x.fst).symm.hom ≫ F.map q.fst := by
          exact e.inv.toNatTrans.naturality q.fst
        rw [← Category.assoc, hnat, Category.assoc, q.w]
        simp only [Category.assoc] }
  map_id x := by
    apply FiberProductHom.ext <;> rfl
  map_comp q r := by
    apply FiberProductHom.ext <;> rfl
  w := rfl

@[simp]
lemma fiberProductMapLeftIso_obj_fst {F F' : A ⥤ᵇ B} (e : F ≅ F') (G : D ⥤ᵇ B)
    (x : (fiberProduct F G).obj) : ((fiberProductMapLeftIso e G).obj x).fst = x.fst :=
  rfl

@[simp]
lemma fiberProductMapLeftIso_obj_snd {F F' : A ⥤ᵇ B} (e : F ≅ F') (G : D ⥤ᵇ B)
    (x : (fiberProduct F G).obj) : ((fiberProductMapLeftIso e G).obj x).snd = x.snd :=
  rfl

@[simp]
lemma fiberProductMapLeftIso_map_fst {F F' : A ⥤ᵇ B} (e : F ≅ F') (G : D ⥤ᵇ B)
    {x y : (fiberProduct F G).obj} (q : x ⟶ y) :
    ((fiberProductMapLeftIso e G).map q).fst = q.fst :=
  rfl

@[simp]
lemma fiberProductMapLeftIso_map_snd {F F' : A ⥤ᵇ B} (e : F ≅ F') (G : D ⥤ᵇ B)
    {x y : (fiberProduct F G).obj} (q : x ⟶ y) :
    ((fiberProductMapLeftIso e G).map q).snd = q.snd :=
  rfl

/-- The left-leg comparison is faithful. -/
lemma fiberProductMapLeftIso_faithful {F F' : A ⥤ᵇ B} (e : F ≅ F')
    (G : D ⥤ᵇ B) : (fiberProductMapLeftIso e G).toFunctor.Faithful := by
  constructor
  intro x y q r h
  apply FiberProductHom.ext
  · exact congrArg (fun k ↦ k.fst) h
  · exact congrArg (fun k ↦ k.snd) h

/-- The left-leg comparison is full. -/
lemma fiberProductMapLeftIso_full {F F' : A ⥤ᵇ B} (e : F ≅ F')
    (G : D ⥤ᵇ B) : (fiberProductMapLeftIso e G).toFunctor.Full := by
  constructor
  intro x y q
  let r : x ⟶ y :=
    { fst := q.fst
      snd := q.snd
      isHomLift := q.isHomLift
      w := by
        have hw := q.w
        change F.map q.fst ≫ y.iso.hom = x.iso.hom ≫ G.map q.snd
        dsimp only [fiberProductMapLeftIso, Iso.trans_hom] at hw
        have hnat : F'.map q.fst ≫ (basedNatIsoApp e y.fst).symm.hom =
            (basedNatIsoApp e x.fst).symm.hom ≫ F.map q.fst := by
          exact e.inv.toNatTrans.naturality q.fst
        rw [← Category.assoc, hnat] at hw
        simp only [Category.assoc] at hw
        rw [← cancel_epi (basedNatIsoApp e x.fst).symm.hom]
        exact hw }
  exact ⟨r, by apply FiberProductHom.ext <;> rfl⟩

/-- The left-leg comparison is essentially surjective. -/
lemma fiberProductMapLeftIso_essSurj {F F' : A ⥤ᵇ B} (e : F ≅ F')
    (G : D ⥤ᵇ B) : (fiberProductMapLeftIso e G).toFunctor.EssSurj := by
  constructor
  intro y
  let x : (fiberProduct F G).obj :=
    { fst := y.fst
      snd := y.snd
      over_eq := y.over_eq
      iso := basedNatIsoApp e y.fst ≪≫ y.iso
      isHomLift := by
        let _ : IsHomLift B.p (𝟙 (A.p.obj y.fst))
            (basedNatIsoApp e y.fst).hom := by
          simpa [basedNatIsoApp] using e.hom.isHomLift' y.fst
        let _ := y.isHomLift
        simpa using IsHomLift.comp B.p (𝟙 _) (𝟙 _)
          (basedNatIsoApp e y.fst).hom y.iso.hom }
  let α : (fiberProductMapLeftIso e G).obj x ≅ y :=
    FiberProductObj.isoMk (Iso.refl _) (Iso.refl _)
      (by
        have hy : D.p.obj y.snd = A.p.obj y.fst := y.over_eq
        apply IsHomLift.of_fac' D.p (A.p.map (𝟙 y.fst)) (𝟙 y.snd)
          hy hy
        simp)
      (by simp [x, fiberProductMapLeftIso, basedNatIsoApp])
  exact ⟨x, ⟨α⟩⟩

/-- Changing a fiber-product leg by a based natural isomorphism gives an equivalence. -/
theorem isEquivalence_fiberProductMapLeftIso {F F' : A ⥤ᵇ B}
    (e : F ≅ F') (G : D ⥤ᵇ B) :
    (fiberProductMapLeftIso e G).toFunctor.IsEquivalence := by
  exact
    { faithful := fiberProductMapLeftIso_faithful e G
      full := fiberProductMapLeftIso_full e G
      essSurj := fiberProductMapLeftIso_essSurj e G }

/-- Changing the right leg of a fiber product along a based natural isomorphism. -/
def fiberProductMapRightIso (F : A ⥤ᵇ B) {G G' : D ⥤ᵇ B} (e : G ≅ G') :
    fiberProduct F G ⥤ᵇ fiberProduct F G' where
  obj x :=
    { fst := x.fst
      snd := x.snd
      over_eq := x.over_eq
      iso := x.iso ≪≫ basedNatIsoApp e x.snd
      isHomLift := by
        let _ := x.isHomLift
        let _ : IsHomLift B.p (𝟙 (A.p.obj x.fst))
            (basedNatIsoApp e x.snd).hom := by
          simpa [basedNatIsoApp] using e.hom.isHomLift x.over_eq
        simpa using IsHomLift.comp B.p (𝟙 _) (𝟙 _)
          x.iso.hom (basedNatIsoApp e x.snd).hom }
  map {x y} q :=
    { fst := q.fst
      snd := q.snd
      isHomLift := q.isHomLift
      w := by
        dsimp only [Iso.trans_hom]
        have hnat : G.map q.snd ≫ (basedNatIsoApp e y.snd).hom =
            (basedNatIsoApp e x.snd).hom ≫ G'.map q.snd := by
          exact e.hom.toNatTrans.naturality q.snd
        rw [← Category.assoc, q.w, Category.assoc, hnat]
        simp only [Category.assoc] }
  map_id x := by
    apply FiberProductHom.ext <;> rfl
  map_comp q r := by
    apply FiberProductHom.ext <;> rfl
  w := rfl

@[simp]
lemma fiberProductMapRightIso_obj_fst (F : A ⥤ᵇ B) {G G' : D ⥤ᵇ B}
    (e : G ≅ G') (x : (fiberProduct F G).obj) :
    ((fiberProductMapRightIso F e).obj x).fst = x.fst :=
  rfl

@[simp]
lemma fiberProductMapRightIso_obj_snd (F : A ⥤ᵇ B) {G G' : D ⥤ᵇ B}
    (e : G ≅ G') (x : (fiberProduct F G).obj) :
    ((fiberProductMapRightIso F e).obj x).snd = x.snd :=
  rfl

@[simp]
lemma fiberProductMapRightIso_map_fst (F : A ⥤ᵇ B) {G G' : D ⥤ᵇ B}
    (e : G ≅ G') {x y : (fiberProduct F G).obj} (q : x ⟶ y) :
    ((fiberProductMapRightIso F e).map q).fst = q.fst :=
  rfl

@[simp]
lemma fiberProductMapRightIso_map_snd (F : A ⥤ᵇ B) {G G' : D ⥤ᵇ B}
    (e : G ≅ G') {x y : (fiberProduct F G).obj} (q : x ⟶ y) :
    ((fiberProductMapRightIso F e).map q).snd = q.snd :=
  rfl

/-- The right-leg comparison is faithful. -/
lemma fiberProductMapRightIso_faithful (F : A ⥤ᵇ B) {G G' : D ⥤ᵇ B}
    (e : G ≅ G') : (fiberProductMapRightIso F e).toFunctor.Faithful := by
  constructor
  intro x y q r h
  apply FiberProductHom.ext
  · exact congrArg (fun k ↦ k.fst) h
  · exact congrArg (fun k ↦ k.snd) h

/-- The right-leg comparison is full. -/
lemma fiberProductMapRightIso_full (F : A ⥤ᵇ B) {G G' : D ⥤ᵇ B}
    (e : G ≅ G') : (fiberProductMapRightIso F e).toFunctor.Full := by
  constructor
  intro x y q
  let r : x ⟶ y :=
    { fst := q.fst
      snd := q.snd
      isHomLift := q.isHomLift
      w := by
        have hw := q.w
        change F.map q.fst ≫ y.iso.hom = x.iso.hom ≫ G.map q.snd
        dsimp only [fiberProductMapRightIso, Iso.trans_hom] at hw
        have hnat : G.map q.snd ≫ (basedNatIsoApp e y.snd).hom =
            (basedNatIsoApp e x.snd).hom ≫ G'.map q.snd := by
          exact e.hom.toNatTrans.naturality q.snd
        simp only [Category.assoc] at hw
        rw [← hnat] at hw
        rw [← cancel_mono (basedNatIsoApp e y.snd).hom]
        simpa only [Category.assoc] using hw }
  exact ⟨r, by apply FiberProductHom.ext <;> rfl⟩

/-- The right-leg comparison is essentially surjective. -/
lemma fiberProductMapRightIso_essSurj (F : A ⥤ᵇ B) {G G' : D ⥤ᵇ B}
    (e : G ≅ G') : (fiberProductMapRightIso F e).toFunctor.EssSurj := by
  constructor
  intro y
  let x : (fiberProduct F G).obj :=
    { fst := y.fst
      snd := y.snd
      over_eq := y.over_eq
      iso := y.iso ≪≫ (basedNatIsoApp e y.snd).symm
      isHomLift := by
        let _ := y.isHomLift
        let _ : IsHomLift B.p (𝟙 (A.p.obj y.fst))
            (basedNatIsoApp e y.snd).inv := by
          simpa [basedNatIsoApp] using e.inv.isHomLift y.over_eq
        simpa using IsHomLift.comp B.p (𝟙 _) (𝟙 _)
          y.iso.hom (basedNatIsoApp e y.snd).inv }
  let α : (fiberProductMapRightIso F e).obj x ≅ y :=
    FiberProductObj.isoMk (Iso.refl _) (Iso.refl _)
      (by
        have hy : D.p.obj y.snd = A.p.obj y.fst := y.over_eq
        apply IsHomLift.of_fac' D.p (A.p.map (𝟙 y.fst)) (𝟙 y.snd) hy hy
        simp)
      (by simp [x, fiberProductMapRightIso, basedNatIsoApp])
  exact ⟨x, ⟨α⟩⟩

/-- Changing the right fiber-product leg by a based natural isomorphism gives an
equivalence. -/
theorem isEquivalence_fiberProductMapRightIso (F : A ⥤ᵇ B) {G G' : D ⥤ᵇ B}
    (e : G ≅ G') : (fiberProductMapRightIso F e).toFunctor.IsEquivalence :=
  { faithful := fiberProductMapRightIso_faithful F e
    full := fiberProductMapRightIso_full F e
    essSurj := fiberProductMapRightIso_essSurj F e }

end CategoryTheory.BasedCategory
