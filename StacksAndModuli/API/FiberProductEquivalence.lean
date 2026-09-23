module

public import StacksAndModuli.API.PrestackProducts
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.3-morphisms-of-prestacks»

/-!
# Changing a leg of a prestack fiber product by an equivalence

This file provides the comparisons from a fiber product formed after precomposing either
leg by a based functor to the original fiber product.  When the precomposing functor is
an equivalence of prestacks, so is the comparison.  This is supporting API for the
representability arguments of §4.2 of *Stacks and Moduli*.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}
  {𝒵 : BasedCategory.{v₄, u₄} 𝒮}

/-- An essentially surjective based functor between possibly universe-heterogeneous
fibered categories is essentially surjective on every fiber. -/
lemma onFiber_essSurj_of_essSurj
    {Zcat : BasedCategory.{v₄, u₄} 𝒮} {Zcat' : BasedCategory.{v₅, u₅} 𝒮}
    (E : BasedFunctor Zcat' Zcat) [Zcat'.p.IsFiberedInGroupoids]
    [Zcat.p.IsFiberedInGroupoids] [E.toFunctor.EssSurj] (S : 𝒮) :
    (E.onFiber S).EssSurj := by
  classical
  constructor
  intro b
  let a₀ : Zcat'.obj := E.toFunctor.objPreimage (Fiber.fiberInclusion.obj b)
  let e₀ : E.obj a₀ ≅ Fiber.fiberInclusion.obj b :=
    E.toFunctor.objObjPreimageIso (Fiber.fiberInclusion.obj b)
  let eBase : Zcat'.p.obj a₀ ≅ S :=
    (eqToIso (E.w_obj a₀)).symm ≪≫ Zcat.p.mapIso e₀ ≪≫ eqToIso b.2
  obtain ⟨a, χ, hχ⟩ :=
    IsFiberedInGroupoids.exists_isHomLift (p := Zcat'.p) (a := a₀) eBase.inv
  let _ := hχ
  have _ : IsIso χ :=
    IsFiberedInGroupoids.isIso_of_isHomLift_isIso (p := Zcat'.p) eBase.inv χ
  let e : E.obj a ≅ Fiber.fiberInclusion.obj b := asIso (E.map χ) ≪≫ e₀
  have ha : Zcat'.p.obj a = S := IsHomLift.domain_eq Zcat'.p eBase.inv χ
  have he : IsHomLift Zcat.p (𝟙 S) e.hom := by
    have he₀ : IsHomLift Zcat.p eBase.hom e₀.hom := by
      apply IsHomLift.of_fac Zcat.p eBase.hom e₀.hom (E.w_obj a₀) b.2
      simp [eBase]
    have hecomp : IsHomLift Zcat.p (eBase.inv ≫ eBase.hom) (E.map χ ≫ e₀.hom) :=
      inferInstance
    simpa [e] using hecomp
  let a' : Zcat'.p.Fiber S := Fiber.mk ha
  let ehom : (E.onFiber S).obj a' ⟶ b := ⟨e.hom, he⟩
  exact ⟨a', ⟨asIso ehom⟩⟩

/-- Precomposing the right leg of a fiber product cospan induces a comparison with the
original fiber product. -/
def fiberProductRightMap (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒵' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒵' 𝒵) :
    BasedFunctor (fiberProduct F (E.comp G)) (fiberProduct F G) where
  obj x :=
    { fst := x.fst
      snd := E.obj x.snd
      over_eq := (E.w_obj x.snd).trans x.over_eq
      iso := x.iso
      isHomLift := x.isHomLift }
  map {x y} q :=
    { fst := q.fst
      snd := E.map q.snd
      isHomLift := E.preserves_isHomLift (𝒳.p.map q.fst) q.snd
      w := q.w }
  map_id x := by
    apply FiberProductHom.ext
    · rfl
    · exact E.toFunctor.map_id x.snd
  map_comp q r := by
    apply FiberProductHom.ext
    · rfl
    · exact E.toFunctor.map_comp q.snd r.snd
  w := rfl

@[simp]
lemma fiberProductRightMap_obj_fst (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒵' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒵' 𝒵)
    (x : (fiberProduct F (E.comp G)).obj) :
    ((fiberProductRightMap F G E).obj x).fst = x.fst :=
  rfl

@[simp]
lemma fiberProductRightMap_obj_snd (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒵' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒵' 𝒵)
    (x : (fiberProduct F (E.comp G)).obj) :
    ((fiberProductRightMap F G E).obj x).snd = E.obj x.snd :=
  rfl

@[simp]
lemma fiberProductRightMap_map_fst (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒵' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒵' 𝒵)
    {x y : (fiberProduct F (E.comp G)).obj} (q : x ⟶ y) :
    ((fiberProductRightMap F G E).map q).fst = q.fst :=
  rfl

@[simp]
lemma fiberProductRightMap_map_snd (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒵' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒵' 𝒵)
    {x y : (fiberProduct F (E.comp G)).obj} (q : x ⟶ y) :
    ((fiberProductRightMap F G E).map q).snd = E.map q.snd :=
  rfl

/-- The right-leg comparison is faithful when the functor changing the leg is
faithful. -/
lemma fiberProductRightMap_faithful (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒵' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒵' 𝒵)
    [E.toFunctor.Faithful] : (fiberProductRightMap F G E).toFunctor.Faithful := by
  constructor
  intro x y q r h
  apply FiberProductHom.ext
  · exact congrArg
      (fun k : (fiberProductRightMap F G E).obj x ⟶
        (fiberProductRightMap F G E).obj y => k.fst) h
  · apply E.toFunctor.map_injective
    exact congrArg
      (fun k : (fiberProductRightMap F G E).obj x ⟶
        (fiberProductRightMap F G E).obj y => k.snd) h

/-- The right-leg comparison is full when the functor changing the leg is fully
faithful. -/
lemma fiberProductRightMap_full (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒵' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒵' 𝒵)
    [E.toFunctor.Full] : (fiberProductRightMap F G E).toFunctor.Full := by
  constructor
  intro x y q
  let r : x.snd ⟶ y.snd := E.toFunctor.preimage q.snd
  have hr : E.map r = q.snd := E.toFunctor.map_preimage q.snd
  let p : x ⟶ y :=
    { fst := q.fst
      snd := r
      isHomLift := by
        have : IsHomLift 𝒵.p (𝒳.p.map q.fst) (E.map r) := by
          rw [hr]
          exact q.isHomLift
        exact E.isHomLift_map (𝒳.p.map q.fst) r
      w := by
        change F.map q.fst ≫ y.iso.hom = x.iso.hom ≫ G.map (E.map r)
        rw [hr]
        exact q.w }
  refine ⟨p, ?_⟩
  apply FiberProductHom.ext
  · rfl
  · exact hr

set_option backward.defeqAttrib.useBackward true in
/-- The right-leg comparison is essentially surjective when the functor changing the
leg is essentially surjective on every fiber. -/
lemma fiberProductRightMap_essSurj (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒵' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒵' 𝒵)
    [𝒵'.p.IsFiberedInGroupoids] [𝒵.p.IsFiberedInGroupoids]
    [E.toFunctor.EssSurj] : (fiberProductRightMap F G E).toFunctor.EssSurj := by
  constructor
  intro x
  let S : 𝒮 := 𝒳.p.obj x.fst
  let x₂ : 𝒵.p.Fiber S := Fiber.mk x.over_eq
  let _ : (E.onFiber S).EssSurj := onFiber_essSurj_of_essSurj E S
  let y₂ : 𝒵'.p.Fiber S := (E.onFiber S).objPreimage x₂
  let e₂ : (E.onFiber S).obj y₂ ≅ x₂ := (E.onFiber S).objObjPreimageIso x₂
  let e : E.obj (Fiber.fiberInclusion.obj y₂) ≅ x.snd :=
    Fiber.fiberInclusion.mapIso e₂
  have he : IsHomLift 𝒵.p (𝟙 S) e.hom := e₂.hom.2
  have heInv : IsHomLift 𝒵.p (𝟙 S) e.inv := e₂.inv.2
  let y : (fiberProduct F (E.comp G)).obj :=
    { fst := x.fst
      snd := Fiber.fiberInclusion.obj y₂
      over_eq := y₂.2
      iso := Iso.trans x.iso (G.toFunctor.mapIso e).symm
      isHomLift := by
        change IsHomLift 𝒴.p (𝟙 S) (x.iso.hom ≫ G.map e.inv)
        have hx : IsHomLift 𝒴.p (𝟙 S) x.iso.hom := x.isHomLift
        have hGeInv : IsHomLift 𝒴.p (𝟙 S) (G.map e.inv) :=
          G.preserves_isHomLift (𝟙 S) e.inv
        infer_instance }
  refine ⟨y, ⟨?_⟩⟩
  let e₁ : ((fiberProductRightMap F G E).obj y).fst ≅ x.fst := Iso.refl x.fst
  apply FiberProductObj.isoMk e₁ e
  · exact isHomLift_map_of_common_lift (𝟙 S) e₁.hom e.hom
      (IsHomLift.id rfl) he
  · have he₁hom : e₁.hom = 𝟙 ((fiberProductRightMap F G E).obj y).fst := rfl
    rw [he₁hom, F.toFunctor.map_id, Category.id_comp]
    have hmapIso : ((fiberProductRightMap F G E).obj y).iso.hom = y.iso.hom := rfl
    rw [hmapIso]
    have hyIso : y.iso.hom = x.iso.hom ≫ G.map e.inv := rfl
    rw [hyIso, Category.assoc, ← G.toFunctor.map_comp, Iso.inv_hom_id,
      G.toFunctor.map_id, Category.comp_id]

/-- Replacing the right leg of a fiber-product cospan by an equivalent prestack does
not change the fiber product up to equivalence. -/
theorem isEquivalence_fiberProductRightMap (F : BasedFunctor 𝒳 𝒴)
    (G : BasedFunctor 𝒵 𝒴) {𝒵' : BasedCategory.{v₅, u₅} 𝒮}
    (E : BasedFunctor 𝒵' 𝒵)
    [𝒵'.p.IsFiberedInGroupoids] [𝒵.p.IsFiberedInGroupoids]
    [E.toFunctor.IsEquivalence] :
    (fiberProductRightMap F G E).toFunctor.IsEquivalence := by
  let : (fiberProductRightMap F G E).toFunctor.Faithful :=
    fiberProductRightMap_faithful F G E
  let : (fiberProductRightMap F G E).toFunctor.Full :=
    fiberProductRightMap_full F G E
  let : (fiberProductRightMap F G E).toFunctor.EssSurj :=
    fiberProductRightMap_essSurj F G E
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- Precomposing the left leg of a fiber product cospan induces a comparison with the
original fiber product. -/
def fiberProductLeftMap (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒳' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒳' 𝒳) :
    BasedFunctor (fiberProduct (E.comp F) G) (fiberProduct F G) where
  obj x :=
    { fst := E.obj x.fst
      snd := x.snd
      over_eq := x.over_eq.trans (E.w_obj x.fst).symm
      iso := x.iso
      isHomLift := (E.w_obj x.fst) ▸ x.isHomLift }
  map {x y} q :=
    { fst := E.map q.fst
      snd := q.snd
      isHomLift := by
        exact isHomLift_map_of_common_lift (𝒳'.p.map q.fst) (E.map q.fst) q.snd
          (E.preserves_isHomLift (𝒳'.p.map q.fst) q.fst) q.isHomLift
      w := q.w }
  map_id x := by
    apply FiberProductHom.ext
    · exact E.toFunctor.map_id x.fst
    · rfl
  map_comp q r := by
    apply FiberProductHom.ext
    · exact E.toFunctor.map_comp q.fst r.fst
    · rfl
  w := by
    refine Functor.ext_of_iso (NatIso.ofComponents (fun x ↦ eqToIso (E.w_obj x.fst)) ?_)
      (fun x ↦ E.w_obj x.fst)
    intro x y q
    have h := IsHomLift.fac' 𝒳.p (𝒳'.p.map q.fst) (E.map q.fst)
    simp only [Functor.comp_map, h]
    simp

@[simp]
lemma fiberProductLeftMap_obj_fst (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒳' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒳' 𝒳)
    (x : (fiberProduct (E.comp F) G).obj) :
    ((fiberProductLeftMap F G E).obj x).fst = E.obj x.fst :=
  rfl

@[simp]
lemma fiberProductLeftMap_obj_snd (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒳' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒳' 𝒳)
    (x : (fiberProduct (E.comp F) G).obj) :
    ((fiberProductLeftMap F G E).obj x).snd = x.snd :=
  rfl

@[simp]
lemma fiberProductLeftMap_map_fst (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒳' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒳' 𝒳)
    {x y : (fiberProduct (E.comp F) G).obj} (q : x ⟶ y) :
    ((fiberProductLeftMap F G E).map q).fst = E.map q.fst :=
  rfl

@[simp]
lemma fiberProductLeftMap_map_snd (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒳' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒳' 𝒳)
    {x y : (fiberProduct (E.comp F) G).obj} (q : x ⟶ y) :
    ((fiberProductLeftMap F G E).map q).snd = q.snd :=
  rfl

/-- The left-leg comparison followed by the unchanged second projection is the
original second projection. -/
@[simp]
lemma fiberProductLeftMap_comp_fiberProductSnd (F : BasedFunctor 𝒳 𝒴)
    (G : BasedFunctor 𝒵 𝒴) {𝒳' : BasedCategory.{v₅, u₅} 𝒮}
    (E : BasedFunctor 𝒳' 𝒳) :
    (fiberProductLeftMap F G E).comp (fiberProductSnd F G) =
      fiberProductSnd (E.comp F) G :=
  BasedFunctor.ext_of_toFunctor_eq rfl

/-- The left-leg comparison is faithful when the functor changing the leg is
faithful. -/
lemma fiberProductLeftMap_faithful (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒳' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒳' 𝒳)
    [E.toFunctor.Faithful] : (fiberProductLeftMap F G E).toFunctor.Faithful := by
  constructor
  intro x y q r h
  apply FiberProductHom.ext
  · apply E.toFunctor.map_injective
    exact congrArg
      (fun k : (fiberProductLeftMap F G E).obj x ⟶
        (fiberProductLeftMap F G E).obj y => k.fst) h
  · exact congrArg
      (fun k : (fiberProductLeftMap F G E).obj x ⟶
        (fiberProductLeftMap F G E).obj y => k.snd) h

/-- The left-leg comparison is full when the functor changing the leg is fully
faithful. -/
lemma fiberProductLeftMap_full (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒳' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒳' 𝒳)
    [E.toFunctor.Full] : (fiberProductLeftMap F G E).toFunctor.Full := by
  constructor
  intro x y q
  let r : x.fst ⟶ y.fst := E.toFunctor.preimage q.fst
  have hr : E.map r = q.fst := E.toFunctor.map_preimage q.fst
  let p : x ⟶ y :=
    { fst := r
      snd := q.snd
      isHomLift := by
        have hEr : IsHomLift 𝒳.p (𝒳.p.map q.fst) (E.map r) := by
          rw [hr]
          infer_instance
        have hrLift : IsHomLift 𝒳'.p (𝒳.p.map q.fst) r := by
          let _ := hEr
          exact E.isHomLift_map (𝒳.p.map q.fst) r
        exact isHomLift_map_of_common_lift (𝒳.p.map q.fst) r q.snd hrLift
          q.isHomLift
      w := by
        change F.map (E.map r) ≫ y.iso.hom = x.iso.hom ≫ G.map q.snd
        rw [hr]
        exact q.w }
  refine ⟨p, ?_⟩
  apply FiberProductHom.ext
  · exact hr
  · rfl

set_option backward.defeqAttrib.useBackward true in
/-- The left-leg comparison is essentially surjective when the functor changing the
leg is essentially surjective on every fiber. -/
lemma fiberProductLeftMap_essSurj (F : BasedFunctor 𝒳 𝒴) (G : BasedFunctor 𝒵 𝒴)
    {𝒳' : BasedCategory.{v₅, u₅} 𝒮} (E : BasedFunctor 𝒳' 𝒳)
    [𝒳'.p.IsFiberedInGroupoids] [𝒳.p.IsFiberedInGroupoids]
    [E.toFunctor.EssSurj] : (fiberProductLeftMap F G E).toFunctor.EssSurj := by
  constructor
  intro x
  let S : 𝒮 := 𝒳.p.obj x.fst
  let x₁ : 𝒳.p.Fiber S := Fiber.mk rfl
  let _ : (E.onFiber S).EssSurj := onFiber_essSurj_of_essSurj E S
  let y₁ : 𝒳'.p.Fiber S := (E.onFiber S).objPreimage x₁
  let e₁ : (E.onFiber S).obj y₁ ≅ x₁ := (E.onFiber S).objObjPreimageIso x₁
  let e : E.obj (Fiber.fiberInclusion.obj y₁) ≅ x.fst :=
    Fiber.fiberInclusion.mapIso e₁
  have he : IsHomLift 𝒳.p (𝟙 S) e.hom := e₁.hom.2
  let y : (fiberProduct (E.comp F) G).obj :=
    { fst := Fiber.fiberInclusion.obj y₁
      snd := x.snd
      over_eq := x.over_eq.trans y₁.2.symm
      iso := (F.toFunctor.mapIso e).trans x.iso
      isHomLift := y₁.2.symm ▸ by
        have hFe : IsHomLift 𝒴.p (𝟙 S) (F.map e.hom) :=
          F.preserves_isHomLift (𝟙 S) e.hom
        let _ := hFe
        have hx : IsHomLift 𝒴.p (𝟙 S) x.iso.hom := x.isHomLift
        let _ := hx
        change IsHomLift 𝒴.p (𝟙 S) (F.map e.hom ≫ x.iso.hom)
        exact inferInstance }
  refine ⟨y, ⟨?_⟩⟩
  apply FiberProductObj.isoMk (a := (fiberProductLeftMap F G E).obj y) (b := x)
    e (Iso.refl x.snd)
  · exact isHomLift_map_of_common_lift (𝟙 S) e.hom (𝟙 x.snd) he
      (IsHomLift.id x.over_eq)
  · have hmapIso : ((fiberProductLeftMap F G E).obj y).iso.hom = y.iso.hom := rfl
    rw [hmapIso]
    have hyIso : y.iso.hom = F.map e.hom ≫ x.iso.hom := rfl
    rw [hyIso]
    exact ((congrArg (fun t ↦ (F.map e.hom ≫ x.iso.hom) ≫ t)
      (G.toFunctor.map_id x.snd)).trans (Category.comp_id _)).symm

/-- Replacing the left leg of a fiber-product cospan by an equivalent prestack does
not change the fiber product up to equivalence. -/
theorem isEquivalence_fiberProductLeftMap (F : BasedFunctor 𝒳 𝒴)
    (G : BasedFunctor 𝒵 𝒴) {𝒳' : BasedCategory.{v₅, u₅} 𝒮}
    (E : BasedFunctor 𝒳' 𝒳)
    [𝒳'.p.IsFiberedInGroupoids] [𝒳.p.IsFiberedInGroupoids]
    [E.toFunctor.IsEquivalence] :
    (fiberProductLeftMap F G E).toFunctor.IsEquivalence := by
  let : (fiberProductLeftMap F G E).toFunctor.Faithful :=
    fiberProductLeftMap_faithful F G E
  let : (fiberProductLeftMap F G E).toFunctor.Full :=
    fiberProductLeftMap_full F G E
  let : (fiberProductLeftMap F G E).toFunctor.EssSurj :=
    fiberProductLeftMap_essSurj F G E
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

end CategoryTheory.BasedCategory
