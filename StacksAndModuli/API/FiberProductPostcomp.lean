module

public import StacksAndModuli.API.PrestackProducts

/-!
# Postcomposition equivalences for prestack fiber products

Postcomposing both legs of a cospan of based categories by a fully faithful based
functor does not change its 2-fiber product up to equivalence.  This is the categorical
comparison used when a locally lifted pair of stack-valued points is compared through
a presentation.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.BasedCategory

variable {S : Type u₁} [Category.{v₁} S]
  {X : BasedCategory.{v₂, u₂} S} {Y : BasedCategory.{v₃, u₃} S}
  {Z : BasedCategory.{v₄, u₄} S} {Y' : BasedCategory.{v₅, u₅} S}

/-- Postcomposing both legs of a cospan by a based functor induces a comparison of
their 2-fiber products. -/
def fiberProductPostcomp (F : X ⥤ᵇ Y) (G : Z ⥤ᵇ Y) (E : Y ⥤ᵇ Y') :
    fiberProduct F G ⥤ᵇ fiberProduct (F.comp E) (G.comp E) where
  obj x :=
    { fst := x.fst
      snd := x.snd
      over_eq := x.over_eq
      iso := E.toFunctor.mapIso x.iso
      isHomLift := E.preserves_isHomLift (𝟙 (X.p.obj x.fst)) x.iso.hom }
  map {x y} q :=
    { fst := q.fst
      snd := q.snd
      isHomLift := q.isHomLift
      w := by
        change E.map (F.map q.fst) ≫ E.map y.iso.hom =
          E.map x.iso.hom ≫ E.map (G.map q.snd)
        rw [← E.toFunctor.map_comp, q.w, E.toFunctor.map_comp] }
  map_id x := by
    apply FiberProductHom.ext <;> rfl
  map_comp q r := by
    apply FiberProductHom.ext <;> rfl
  w := rfl

@[simp]
lemma fiberProductPostcomp_obj_fst (F : X ⥤ᵇ Y) (G : Z ⥤ᵇ Y) (E : Y ⥤ᵇ Y')
    (x : (fiberProduct F G).obj) :
    ((fiberProductPostcomp F G E).obj x).fst = x.fst :=
  rfl

@[simp]
lemma fiberProductPostcomp_obj_snd (F : X ⥤ᵇ Y) (G : Z ⥤ᵇ Y) (E : Y ⥤ᵇ Y')
    (x : (fiberProduct F G).obj) :
    ((fiberProductPostcomp F G E).obj x).snd = x.snd :=
  rfl

@[simp]
lemma fiberProductPostcomp_map_fst (F : X ⥤ᵇ Y) (G : Z ⥤ᵇ Y) (E : Y ⥤ᵇ Y')
    {x y : (fiberProduct F G).obj} (q : x ⟶ y) :
    ((fiberProductPostcomp F G E).map q).fst = q.fst :=
  rfl

@[simp]
lemma fiberProductPostcomp_map_snd (F : X ⥤ᵇ Y) (G : Z ⥤ᵇ Y) (E : Y ⥤ᵇ Y')
    {x y : (fiberProduct F G).obj} (q : x ⟶ y) :
    ((fiberProductPostcomp F G E).map q).snd = q.snd :=
  rfl

/-- The postcomposition comparison is faithful. -/
instance fiberProductPostcomp_faithful (F : X ⥤ᵇ Y) (G : Z ⥤ᵇ Y)
    (E : Y ⥤ᵇ Y') : (fiberProductPostcomp F G E).toFunctor.Faithful where
  map_injective {x y} q r h := by
    apply FiberProductHom.ext
    · exact congrArg
        (fun k : (fiberProductPostcomp F G E).obj x ⟶
          (fiberProductPostcomp F G E).obj y ↦ k.fst) h
    · exact congrArg
        (fun k : (fiberProductPostcomp F G E).obj x ⟶
          (fiberProductPostcomp F G E).obj y ↦ k.snd) h

/-- The postcomposition comparison is full when the postcomposing functor is fully
faithful. -/
instance fiberProductPostcomp_full (F : X ⥤ᵇ Y) (G : Z ⥤ᵇ Y)
    (E : Y ⥤ᵇ Y') [E.toFunctor.Full] [E.toFunctor.Faithful] :
    (fiberProductPostcomp F G E).toFunctor.Full where
  map_surjective {x y} q := by
    let r : x ⟶ y :=
      { fst := q.fst
        snd := q.snd
        isHomLift := q.isHomLift
        w := by
          apply E.toFunctor.map_injective
          change E.map (F.map q.fst ≫ y.iso.hom) =
            E.map (x.iso.hom ≫ G.map q.snd)
          rw [E.toFunctor.map_comp, E.toFunctor.map_comp]
          exact q.w }
    refine ⟨r, ?_⟩
    apply FiberProductHom.ext <;> rfl

set_option backward.defeqAttrib.useBackward true in
/-- The postcomposition comparison is essentially surjective when the postcomposing
functor is fully faithful. -/
instance fiberProductPostcomp_essSurj (F : X ⥤ᵇ Y) (G : Z ⥤ᵇ Y)
    (E : Y ⥤ᵇ Y') [E.toFunctor.Full] [E.toFunctor.Faithful] :
    (fiberProductPostcomp F G E).toFunctor.EssSurj where
  mem_essImage x := by
    let e : F.obj x.fst ≅ G.obj x.snd := E.toFunctor.preimageIso x.iso
    have he : IsHomLift Y.p (𝟙 (X.p.obj x.fst)) e.hom := by
      let _ : IsHomLift Y'.p (𝟙 (X.p.obj x.fst)) (E.map e.hom) := by
        simpa [e] using x.isHomLift
      exact E.isHomLift_map (𝟙 (X.p.obj x.fst)) e.hom
    let y : (fiberProduct F G).obj :=
      { fst := x.fst
        snd := x.snd
        over_eq := x.over_eq
        iso := e
        isHomLift := he }
    refine ⟨y, ⟨?_⟩⟩
    apply FiberProductObj.isoMk (F := F.comp E) (G := G.comp E)
      (a := (fiberProductPostcomp F G E).obj y) (b := x)
      (Iso.refl _) (Iso.refl _)
    · change IsHomLift Z.p (X.p.map (𝟙 x.fst)) (𝟙 x.snd)
      rw [X.p.map_id]
      exact IsHomLift.id x.over_eq
    · simp [fiberProductPostcomp, y, e]

/-- Postcomposing both legs of a cospan by a fully faithful based functor preserves
its 2-fiber product up to equivalence. -/
theorem isEquivalence_fiberProductPostcomp (F : X ⥤ᵇ Y) (G : Z ⥤ᵇ Y)
    (E : Y ⥤ᵇ Y') [E.toFunctor.Full] [E.toFunctor.Faithful] :
    (fiberProductPostcomp F G E).toFunctor.IsEquivalence :=
  { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

end CategoryTheory.BasedCategory
