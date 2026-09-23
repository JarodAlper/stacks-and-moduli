module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.4-two-yoneda-lemma»
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.5-fiber-products-of-prestacks»
public import StacksAndModuli.API.PrestackComponents
public import StacksAndModuli.API.PresheafPrestack
public import StacksAndModuli.API.PrestackProducts
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Endomorphism

/-!
# Isomorphism presheaves

This module formalizes `exer:isom-presheaf` (Exercise 3.4.39)
of §3.4 (Prestacks) of *Stacks and Moduli*,
section label `sec:prestacks`.

For two objects `a, b` of a prestack over `S`, chosen cartesian pullbacks define the
presheaf on `𝒮/S` whose value at `f : T → S` is the set of morphisms
`f* a → f* b` in the fiber over `T`. Restriction is defined by the universal property
of the chosen cartesian arrow for `b`, rather than by inverting that arrow (its base map
need not be an isomorphism).

Main declarations:
- `CategoryTheory.BasedCategory.isomPresheaf`: the `Isom` presheaf of Exercise 3.4.39(a).
- `CategoryTheory.BasedCategory.isEquivalence_isomPrestackComparison`: the cartesian
  diagonal square of Exercise 3.4.39(b).
- `CategoryTheory.BasedCategory.autPresheaf`: the automorphism group presheaf of
  Exercise 3.4.39(c).
- `CategoryTheory.BasedCategory.isEquivalentToPresheaf_iff_diag_full_and_faithful`:
  the characterization of Exercise 3.4.39(d).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section ExerIsomPresheaf

open CategoryTheory Functor Opposite

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  {𝒳 : BasedCategory.{v₂, u₂} 𝒮} [𝒳.p.IsFiberedInGroupoids]
  {S : 𝒮}

/-- Restrict a morphism between two chosen pullbacks along a morphism in `𝒮/S`.
The result is the unique morphism whose composite with the cartesian pullback arrow for
the target object is the evident composite. -/
noncomputable def isomRestriction (a b : 𝒳.p.Fiber S) {f g : Over S} (k : f ⟶ g)
    (phi : pullbackFiberObj a g ⟶ pullbackFiberObj b g) :
    pullbackFiberObj a f ⟶ pullbackFiberObj b f := by
  let u : IsPreFibered.pullbackObj a.2 f.hom ⟶
      IsPreFibered.pullbackObj b.2 f.hom :=
    IsStronglyCartesian.map 𝒳.p k.left (twoYonedaPullbackMap S b k)
      (Category.id_comp k.left).symm
      (twoYonedaPullbackMap S a k ≫ Fiber.fiberInclusion.map phi)
  have hu : IsHomLift 𝒳.p (𝟙 f.left) u :=
    IsStronglyCartesian.map_isHomLift 𝒳.p k.left (twoYonedaPullbackMap S b k)
      (Category.id_comp k.left).symm
      (twoYonedaPullbackMap S a k ≫ Fiber.fiberInclusion.map phi)
  exact Fiber.homMk 𝒳.p f.left u

@[reassoc]
lemma isomRestriction_fac (a b : 𝒳.p.Fiber S) {f g : Over S} (k : f ⟶ g)
    (phi : pullbackFiberObj a g ⟶ pullbackFiberObj b g) :
    Fiber.fiberInclusion.map (isomRestriction a b k phi) ≫
        twoYonedaPullbackMap S b k =
      twoYonedaPullbackMap S a k ≫ Fiber.fiberInclusion.map phi :=
  IsStronglyCartesian.fac 𝒳.p k.left (twoYonedaPullbackMap S b k)
    (Category.id_comp k.left).symm
    (twoYonedaPullbackMap S a k ≫ Fiber.fiberInclusion.map phi)

/-- Restriction of the identity morphism is the identity. -/
lemma isomRestriction_id (a : 𝒳.p.Fiber S) {f g : Over S} (k : f ⟶ g) :
    isomRestriction a a k (𝟙 (pullbackFiberObj a g)) =
      𝟙 (pullbackFiberObj a f) := by
  apply Fiber.hom_ext
  apply IsStronglyCartesian.ext 𝒳.p k.left
    (twoYonedaPullbackMap S a k) (𝟙 f.left)
  rw [isomRestriction_fac]
  simp

/-- Restriction preserves composition of morphisms between chosen pullbacks. -/
lemma isomRestriction_comp (a b c : 𝒳.p.Fiber S) {f g : Over S} (k : f ⟶ g)
    (phi : pullbackFiberObj a g ⟶ pullbackFiberObj b g)
    (psi : pullbackFiberObj b g ⟶ pullbackFiberObj c g) :
    isomRestriction a c k (phi ≫ psi) =
      isomRestriction a b k phi ≫ isomRestriction b c k psi := by
  apply Fiber.hom_ext
  apply IsStronglyCartesian.ext 𝒳.p k.left
    (twoYonedaPullbackMap S c k) (𝟙 f.left)
  rw [Functor.map_comp, isomRestriction_fac, Category.assoc,
    isomRestriction_fac, ← Category.assoc, isomRestriction_fac,
    Functor.map_comp, Category.assoc]

/-- **Exercise 3.4.39** (`exer:isom-presheaf`) (part (a)): for objects `a, b` of a
prestack over `S`, the assignment
`(f : T → S) ↦ Mor_{𝒳(T)}(f* a, f* b)` is a presheaf on `𝒮/S`.
The pullbacks are Mathlib's chosen cartesian pullbacks. -/
noncomputable def isomPresheaf (a b : 𝒳.p.Fiber S) : (Over S)ᵒᵖ ⥤ Type v₂ where
  obj f := pullbackFiberObj a f.unop ⟶ pullbackFiberObj b f.unop
  map {f g} k := ↾fun phi ↦ isomRestriction a b k.unop phi
  map_id f := by
    ext phi
    let k : f.unop ⟶ f.unop := 𝟙 f.unop
    have hk : k = (𝟙 f).unop := rfl
    have hfac := isomRestriction_fac a b k phi
    have ha := (twoYonedaPullback S a).map_id f.unop
    have hb := (twoYonedaPullback S b).map_id f.unop
    change twoYonedaPullbackMap S a k = 𝟙 _ at ha
    change twoYonedaPullbackMap S b k = 𝟙 _ at hb
    change Fiber.fiberInclusion.map (isomRestriction a b k phi) =
      Fiber.fiberInclusion.map phi
    apply IsStronglyCartesian.ext 𝒳.p k.left
      (twoYonedaPullbackMap S b k) (𝟙 f.unop.left)
    rw [hfac, ha, hb]
    simp
  map_comp {f g h} k l := by
    ext phi
    let k' : g.unop ⟶ f.unop := k.unop
    let l' : h.unop ⟶ g.unop := l.unop
    let lk : h.unop ⟶ f.unop := l' ≫ k'
    have hcomp : (k ≫ l).unop = lk := rfl
    have hfac₁ := isomRestriction_fac a b k' phi
    have hfac₂ := isomRestriction_fac a b l' (isomRestriction a b k' phi)
    have hfac := isomRestriction_fac a b lk phi
    have ha := (twoYonedaPullback S a).map_comp l' k'
    have hb := (twoYonedaPullback S b).map_comp l' k'
    change twoYonedaPullbackMap S a lk =
      twoYonedaPullbackMap S a l' ≫ twoYonedaPullbackMap S a k' at ha
    change twoYonedaPullbackMap S b lk =
      twoYonedaPullbackMap S b l' ≫ twoYonedaPullbackMap S b k' at hb
    change Fiber.fiberInclusion.map (isomRestriction a b lk phi) =
      Fiber.fiberInclusion.map (isomRestriction a b l' (isomRestriction a b k' phi))
    apply IsStronglyCartesian.ext 𝒳.p lk.left
      (twoYonedaPullbackMap S b lk) (𝟙 h.unop.left)
    rw [hfac, hb, ← Category.assoc, hfac₂, Category.assoc, hfac₁,
      ← Category.assoc, ← ha]

/-- Background construction for Exercise 3.4.39 (part (b),
definition): the `Isom(a,b)` presheaf of part (a), totalized as a prestack over
`𝒮` through its category of elements over `𝒮/S`. -/
noncomputable abbrev isomPrestack (a b : 𝒳.p.Fiber S) :
    BasedCategory.{v₁, max u₁ v₁ v₂} 𝒮 where
  obj := (isomPresheaf a b).Elementsᵒᵖ
  p := (CategoryOfElements.π (isomPresheaf a b)).leftOp ⋙ Over.forget S

noncomputable def isomPrestackToOverBased (a b : 𝒳.p.Fiber S) :
    isomPrestack a b ⥤ᵇ overBased S where
  toFunctor := (CategoryOfElements.π (isomPresheaf a b)).leftOp
  w := rfl

noncomputable abbrev isomPairMap (a b : 𝒳.p.Fiber S) : overBased S ⥤ᵇ prod 𝒳 𝒳 :=
  prodLift (twoYonedaPullback S a) (twoYonedaPullback S b)

noncomputable abbrev isomPrestackObjOver (a b : 𝒳.p.Fiber S)
    (x : (isomPrestack a b).obj) : Over S :=
  x.unop.1.unop

noncomputable abbrev isomPrestackObjHom (a b : 𝒳.p.Fiber S)
    (x : (isomPrestack a b).obj) :
    pullbackFiberObj a (isomPrestackObjOver a b x) ⟶
      pullbackFiberObj b (isomPrestackObjOver a b x) :=
  x.unop.2

noncomputable abbrev isomPrestackObjPullback (a b : 𝒳.p.Fiber S)
    (x : (isomPrestack a b).obj) : 𝒳.obj :=
  Fiber.fiberInclusion.obj (pullbackFiberObj a (isomPrestackObjOver a b x))

noncomputable def isomPrestackDiagIso (a b : 𝒳.p.Fiber S)
    (x : (isomPrestack a b).obj) :
    (isomPairMap a b).obj (isomPrestackObjOver a b x) ≅
      (diag 𝒳).obj (isomPrestackObjPullback a b x) := by
  let e₁ : ((isomPairMap a b).obj (isomPrestackObjOver a b x)).fst ≅
      ((diag 𝒳).obj (isomPrestackObjPullback a b x)).fst :=
    Iso.refl _
  let e₂ : ((isomPairMap a b).obj (isomPrestackObjOver a b x)).snd ≅
      ((diag 𝒳).obj (isomPrestackObjPullback a b x)).snd :=
    Fiber.fiberInclusion.mapIso (asIso (isomPrestackObjHom a b x)).symm
  have he₁ : IsHomLift 𝒳.p (𝟙 (isomPrestackObjOver a b x).left) e₁.hom := by
    dsimp [e₁]
    exact IsHomLift.id (IsPreFibered.pullbackObj_proj a.2
      (isomPrestackObjOver a b x).hom)
  have he₂ : IsHomLift 𝒳.p (𝟙 (isomPrestackObjOver a b x).left) e₂.hom := by
    dsimp [e₂]
    infer_instance
  apply FiberProductObj.isoMk e₁ e₂
  · exact isHomLift_map_of_common_lift (𝟙 (isomPrestackObjOver a b x).left)
      e₁.hom e₂.hom he₁ he₂
  · haveI he₁' := he₁
    haveI he₂' := he₂
    haveI htarget : IsHomLift (base 𝒮).p
        (𝟙 (𝒳.p.obj ((diag 𝒳).obj (isomPrestackObjPullback a b x)).fst))
        ((diag 𝒳).obj (isomPrestackObjPullback a b x)).iso.hom := by
      exact ((diag 𝒳).obj (isomPrestackObjPullback a b x)).isHomLift
    haveI hsource : IsHomLift (base 𝒮).p
        (𝟙 (𝒳.p.obj ((isomPairMap a b).obj (isomPrestackObjOver a b x)).fst))
        ((isomPairMap a b).obj (isomPrestackObjOver a b x)).iso.hom := by
      exact ((isomPairMap a b).obj (isomPrestackObjOver a b x)).isHomLift
    haveI hleft := base_isHomLift_comp
      (S := (isomPrestackObjOver a b x).left)
      (T := 𝒳.p.obj ((diag 𝒳).obj (isomPrestackObjPullback a b x)).fst)
      (𝒳.toBase.map e₁.hom) (((diag 𝒳).obj (isomPrestackObjPullback a b x)).iso.hom)
    haveI hright := base_isHomLift_comp
      (S := 𝒳.p.obj ((isomPairMap a b).obj (isomPrestackObjOver a b x)).fst)
      (T := (isomPrestackObjOver a b x).left)
      (((isomPairMap a b).obj (isomPrestackObjOver a b x)).iso.hom)
      (𝒳.toBase.map e₂.hom)
    exact base_hom_ext
      (S := (isomPrestackObjOver a b x).left)
      (T := 𝒳.p.obj ((isomPairMap a b).obj (isomPrestackObjOver a b x)).fst) _ _

@[simp]
lemma isomPrestackDiagIso_hom_fst (a b : 𝒳.p.Fiber S)
    (x : (isomPrestack a b).obj) :
    (isomPrestackDiagIso a b x).hom.fst = 𝟙 _ := by
  simp [isomPrestackDiagIso]

@[simp]
lemma isomPrestackDiagIso_hom_snd (a b : 𝒳.p.Fiber S)
    (x : (isomPrestack a b).obj) :
    (isomPrestackDiagIso a b x).hom.snd =
      Fiber.fiberInclusion.map (asIso (isomPrestackObjHom a b x)).inv := by
  simp [isomPrestackDiagIso]

/-- Background comparison functor for Exercise 3.4.39 (part (b)):
the canonical map from the totalized `Isom(a,b)` presheaf to the base change of
the diagonal along `(a,b) : S → 𝒳 × 𝒳`. -/
noncomputable def isomPrestackComparison (a b : 𝒳.p.Fiber S) :
    isomPrestack a b ⥤ᵇ fiberProduct (isomPairMap a b) (diag 𝒳) where
  obj x :=
    { fst := isomPrestackObjOver a b x
      snd := isomPrestackObjPullback a b x
      over_eq := IsPreFibered.pullbackObj_proj a.2 (isomPrestackObjOver a b x).hom
      iso := isomPrestackDiagIso a b x
      isHomLift := by
        apply FiberProductHom.isHomLift_of_fst _ (𝟙 _)
        rw [isomPrestackDiagIso_hom_fst]
        exact IsHomLift.id (IsPreFibered.pullbackObj_proj a.2
          (isomPrestackObjOver a b x).hom) }
  map {x y} q :=
    { fst := q.unop.val.unop
      snd := twoYonedaPullbackMap S a q.unop.val.unop
      isHomLift := twoYonedaPullbackMap_isHomLift S a q.unop.val.unop
      w := by
        apply FiberProductHom.ext
        · simp only [FiberProductObj.comp_fst, fiberProductLift_map_fst,
            isomPrestackDiagIso_hom_fst, diag_map_fst, Category.comp_id,
            Category.id_comp]
          rfl
        · simp only [FiberProductObj.comp_snd, fiberProductLift_map_snd,
            isomPrestackDiagIso_hom_snd, diag_map_snd]
          change twoYonedaPullbackMap S b q.unop.val.unop ≫
              Fiber.fiberInclusion.map (asIso (isomPrestackObjHom a b y)).inv =
            Fiber.fiberInclusion.map (asIso (isomPrestackObjHom a b x)).inv ≫
              twoYonedaPullbackMap S a q.unop.val.unop
          have hrest : isomRestriction a b q.unop.val.unop
              (isomPrestackObjHom a b y) = isomPrestackObjHom a b x :=
            CategoryOfElements.map_snd q.unop
          have hx : (asIso (isomPrestackObjHom a b x)).hom =
              isomPrestackObjHom a b x := rfl
          have hy : (asIso (isomPrestackObjHom a b y)).hom =
              isomPrestackObjHom a b y := rfl
          have hfac := isomRestriction_fac a b q.unop.val.unop
            (isomPrestackObjHom a b y)
          rw [hrest] at hfac
          rw [← hx, ← hy] at hfac
          rw [← cancel_mono (Fiber.fiberInclusion.map
            (asIso (isomPrestackObjHom a b y)).hom)]
          calc
            (twoYonedaPullbackMap S b q.unop.val.unop ≫
                  Fiber.fiberInclusion.map
                    (asIso (isomPrestackObjHom a b y)).inv) ≫
                Fiber.fiberInclusion.map
                  (asIso (isomPrestackObjHom a b y)).hom =
              twoYonedaPullbackMap S b q.unop.val.unop := by
                rw [Category.assoc, ← Fiber.fiberInclusion.map_comp,
                  Iso.inv_hom_id, Fiber.fiberInclusion.map_id]
                exact Category.comp_id _
            _ = Fiber.fiberInclusion.map
                  (asIso (isomPrestackObjHom a b x)).inv ≫
                (Fiber.fiberInclusion.map
                    (asIso (isomPrestackObjHom a b x)).hom ≫
                  twoYonedaPullbackMap S b q.unop.val.unop) := by
                rw [← Category.assoc, ← Fiber.fiberInclusion.map_comp,
                  Iso.inv_hom_id, Fiber.fiberInclusion.map_id]
                exact (Category.id_comp _).symm
            _ = Fiber.fiberInclusion.map
                  (asIso (isomPrestackObjHom a b x)).inv ≫
                (twoYonedaPullbackMap S a q.unop.val.unop ≫
                  Fiber.fiberInclusion.map
                    (asIso (isomPrestackObjHom a b y)).hom) := by
                rw [hfac]
            _ = (Fiber.fiberInclusion.map
                    (asIso (isomPrestackObjHom a b x)).inv ≫
                  twoYonedaPullbackMap S a q.unop.val.unop) ≫
                Fiber.fiberInclusion.map
                  (asIso (isomPrestackObjHom a b y)).hom := by
                rw [Category.assoc] }
  map_id x := by
    apply FiberProductHom.ext
    · apply Over.OverMorphism.ext
      rfl
    · exact (twoYonedaPullback S a).toFunctor.map_id _
  map_comp q r := by
    apply FiberProductHom.ext
    · apply Over.OverMorphism.ext
      rfl
    · exact (twoYonedaPullback S a).toFunctor.map_comp _ _
  w := rfl

@[simp]
lemma isomPrestackComparison_map_fst (a b : 𝒳.p.Fiber S)
    {x y : (isomPrestack a b).obj} (q : x ⟶ y) :
    ((isomPrestackComparison a b).map q).fst = q.unop.val.unop := rfl

@[simp]
lemma isomPrestackComparison_map_snd (a b : 𝒳.p.Fiber S)
    {x y : (isomPrestack a b).obj} (q : x ⟶ y) :
    ((isomPrestackComparison a b).map q).snd =
      twoYonedaPullbackMap S a q.unop.val.unop := rfl

@[simp]
lemma isomPrestackComparison_obj_iso_hom_fst (a b : 𝒳.p.Fiber S)
    (x : (isomPrestack a b).obj) :
    ((isomPrestackComparison a b).obj x).iso.hom.fst = 𝟙 _ := by
  simp [isomPrestackComparison]

@[simp]
lemma isomPrestackComparison_obj_fst (a b : 𝒳.p.Fiber S)
    (x : (isomPrestack a b).obj) :
    ((isomPrestackComparison a b).obj x).fst = isomPrestackObjOver a b x := rfl

@[simp]
lemma isomPrestackComparison_obj_snd (a b : 𝒳.p.Fiber S)
    (x : (isomPrestack a b).obj) :
    ((isomPrestackComparison a b).obj x).snd = isomPrestackObjPullback a b x := rfl

@[simp]
lemma isomPrestackComparison_obj_iso_hom_snd (a b : 𝒳.p.Fiber S)
    (x : (isomPrestack a b).obj) :
    ((isomPrestackComparison a b).obj x).iso.hom.snd =
      Fiber.fiberInclusion.map (asIso (isomPrestackObjHom a b x)).inv := by
  simp [isomPrestackComparison]

lemma isomPrestackComparison_faithful (a b : 𝒳.p.Fiber S) :
    (isomPrestackComparison a b).toFunctor.Faithful := by
  constructor
  intro x y q r h
  apply Quiver.Hom.unop_inj
  apply CategoryOfElements.ext
  apply Quiver.Hom.unop_inj
  exact congrArg FiberProductHom.fst h

lemma isomPrestackComparison_full (a b : 𝒳.p.Fiber S) :
    (isomPrestackComparison a b).toFunctor.Full := by
  constructor
  intro x y q
  have hw₁ := congrArg FiberProductHom.fst q.w
  have hw₂ := congrArg FiberProductHom.snd q.w
  simp only [FiberProductObj.comp_fst, FiberProductObj.comp_snd,
    fiberProductLift_map_fst, fiberProductLift_map_snd,
    isomPrestackComparison_obj_fst, isomPrestackComparison_obj_snd,
    isomPrestackComparison_obj_iso_hom_fst,
    isomPrestackComparison_obj_iso_hom_snd,
    diag_map_fst, diag_map_snd, Category.comp_id, Category.id_comp] at hw₁ hw₂
  dsimp only [twoYonedaPullback, BasedFunctor.id] at hw₁ hw₂
  simp only [Functor.id_map] at hw₁ hw₂
  have hcompat : Fiber.fiberInclusion.map (isomPrestackObjHom a b x) ≫
        twoYonedaPullbackMap S b q.fst =
      twoYonedaPullbackMap S a q.fst ≫
        Fiber.fiberInclusion.map (isomPrestackObjHom a b y) := by
    have hx : (asIso (isomPrestackObjHom a b x)).hom =
        isomPrestackObjHom a b x := rfl
    have hy : (asIso (isomPrestackObjHom a b y)).hom =
        isomPrestackObjHom a b y := rfl
    rw [← hx, ← hy, ← cancel_mono
      (Fiber.fiberInclusion.map (asIso (isomPrestackObjHom a b y)).inv)]
    calc
      (Fiber.fiberInclusion.map (asIso (isomPrestackObjHom a b x)).hom ≫
            twoYonedaPullbackMap S b q.fst) ≫
          Fiber.fiberInclusion.map (asIso (isomPrestackObjHom a b y)).inv =
        Fiber.fiberInclusion.map (asIso (isomPrestackObjHom a b x)).hom ≫
          (twoYonedaPullbackMap S b q.fst ≫
            Fiber.fiberInclusion.map (asIso (isomPrestackObjHom a b y)).inv) :=
        Category.assoc _ _ _
      _ = Fiber.fiberInclusion.map (asIso (isomPrestackObjHom a b x)).hom ≫
          (Fiber.fiberInclusion.map (asIso (isomPrestackObjHom a b x)).inv ≫ q.snd) := by
        rw [hw₂]
      _ = q.snd := by
        rw [← Category.assoc, ← Fiber.fiberInclusion.map_comp,
          Iso.hom_inv_id, Fiber.fiberInclusion.map_id]
        exact Category.id_comp _
      _ = twoYonedaPullbackMap S a q.fst := hw₁.symm
      _ = (twoYonedaPullbackMap S a q.fst ≫
            Fiber.fiberInclusion.map (asIso (isomPrestackObjHom a b y)).hom) ≫
          Fiber.fiberInclusion.map (asIso (isomPrestackObjHom a b y)).inv := by
        rw [Category.assoc, ← Fiber.fiberInclusion.map_comp,
          Iso.hom_inv_id, Fiber.fiberInclusion.map_id]
        exact (Category.comp_id _).symm
  have hrestrict : isomRestriction a b q.fst (isomPrestackObjHom a b y) =
      isomPrestackObjHom a b x := by
    apply Fiber.hom_ext
    apply IsStronglyCartesian.ext 𝒳.p q.fst.left
      (twoYonedaPullbackMap S b q.fst)
      (𝟙 (isomPrestackObjOver a b x).left)
    rw [isomRestriction_fac, hcompat]
  let p : x ⟶ y :=
    (CategoryOfElements.homMk _ _ q.fst.op hrestrict).op
  refine ⟨p, ?_⟩
  apply FiberProductHom.ext
  · apply Over.OverMorphism.ext
    rfl
  · change twoYonedaPullbackMap S a q.fst = q.snd
    exact hw₁

noncomputable abbrev isomPrestackTargetFstIso (a b : 𝒳.p.Fiber S)
    (q : (fiberProduct (isomPairMap a b) (diag 𝒳)).obj) :
    Fiber.fiberInclusion.obj (pullbackFiberObj a q.fst) ≅ q.snd :=
  (fiberProductFst 𝒳.toBase 𝒳.toBase).toFunctor.mapIso q.iso

noncomputable abbrev isomPrestackTargetSndIso (a b : 𝒳.p.Fiber S)
    (q : (fiberProduct (isomPairMap a b) (diag 𝒳)).obj) :
    Fiber.fiberInclusion.obj (pullbackFiberObj b q.fst) ≅ q.snd :=
  (fiberProductSnd 𝒳.toBase 𝒳.toBase).toFunctor.mapIso q.iso

@[simp]
lemma isomPrestackTargetFstIso_hom (a b : 𝒳.p.Fiber S)
    (q : (fiberProduct (isomPairMap a b) (diag 𝒳)).obj) :
    (isomPrestackTargetFstIso a b q).hom = q.iso.hom.fst := rfl

@[simp]
lemma isomPrestackTargetFstIso_inv (a b : 𝒳.p.Fiber S)
    (q : (fiberProduct (isomPairMap a b) (diag 𝒳)).obj) :
    (isomPrestackTargetFstIso a b q).inv = q.iso.inv.fst := rfl

@[simp]
lemma isomPrestackTargetSndIso_hom (a b : 𝒳.p.Fiber S)
    (q : (fiberProduct (isomPairMap a b) (diag 𝒳)).obj) :
    (isomPrestackTargetSndIso a b q).hom = q.iso.hom.snd := rfl

noncomputable def isomPrestackPreimageHom (a b : 𝒳.p.Fiber S)
    (q : (fiberProduct (isomPairMap a b) (diag 𝒳)).obj) :
    pullbackFiberObj a q.fst ⟶ pullbackFiberObj b q.fst := by
  let e₁ := isomPrestackTargetFstIso a b q
  let e₂ := isomPrestackTargetSndIso a b q
  haveI he₁ : IsHomLift 𝒳.p (𝟙 q.fst.left) e₁.hom := by
    exact FiberProductHom.isHomLift_fst q.iso.hom (𝟙 q.fst.left) q.isHomLift
  haveI he₂ : IsHomLift 𝒳.p (𝟙 q.fst.left) e₂.hom := by
    exact FiberProductHom.isHomLift_snd (F := 𝒳.toBase) (G := 𝒳.toBase)
      q.iso.hom (𝟙 q.fst.left) q.isHomLift
  haveI he₂inv : IsHomLift 𝒳.p (𝟙 q.fst.left) e₂.inv := by
    infer_instance
  exact Fiber.homMk 𝒳.p q.fst.left (e₁.hom ≫ e₂.inv)

lemma isomPrestackPreimageHom_val (a b : 𝒳.p.Fiber S)
    (q : (fiberProduct (isomPairMap a b) (diag 𝒳)).obj) :
    Fiber.fiberInclusion.map (isomPrestackPreimageHom a b q) =
      (isomPrestackTargetFstIso a b q).hom ≫
        (isomPrestackTargetSndIso a b q).inv := rfl

noncomputable abbrev isomPrestackPreimageObj (a b : 𝒳.p.Fiber S)
    (q : (fiberProduct (isomPairMap a b) (diag 𝒳)).obj) :
    (isomPrestack a b).obj :=
  op ⟨op q.fst, isomPrestackPreimageHom a b q⟩

@[simp]
lemma isomPrestackPreimageObj_over (a b : 𝒳.p.Fiber S)
    (q : (fiberProduct (isomPairMap a b) (diag 𝒳)).obj) :
    isomPrestackObjOver a b (isomPrestackPreimageObj a b q) = q.fst := rfl

lemma isomPrestackPreimageHom_inv_val (a b : 𝒳.p.Fiber S)
    (q : (fiberProduct (isomPairMap a b) (diag 𝒳)).obj) :
    Fiber.fiberInclusion.map (asIso (isomPrestackPreimageHom a b q)).inv =
      (isomPrestackTargetSndIso a b q).hom ≫
        (isomPrestackTargetFstIso a b q).inv := by
  rw [← cancel_mono (Fiber.fiberInclusion.map
    (asIso (isomPrestackPreimageHom a b q)).hom)]
  calc
    Fiber.fiberInclusion.map (asIso (isomPrestackPreimageHom a b q)).inv ≫
        Fiber.fiberInclusion.map (asIso (isomPrestackPreimageHom a b q)).hom =
      𝟙 _ := by
        rw [← Fiber.fiberInclusion.map_comp, Iso.inv_hom_id,
          Fiber.fiberInclusion.map_id]
    _ = ((isomPrestackTargetSndIso a b q).hom ≫
          (isomPrestackTargetFstIso a b q).inv) ≫
        ((isomPrestackTargetFstIso a b q).hom ≫
          (isomPrestackTargetSndIso a b q).inv) := by
        rw [Category.assoc, Iso.inv_hom_id_assoc,
          Iso.hom_inv_id]
    _ = ((isomPrestackTargetSndIso a b q).hom ≫
          (isomPrestackTargetFstIso a b q).inv) ≫
        Fiber.fiberInclusion.map
          (asIso (isomPrestackPreimageHom a b q)).hom := by
        have hhom : (asIso (isomPrestackPreimageHom a b q)).hom =
            isomPrestackPreimageHom a b q := rfl
        rw [hhom, isomPrestackPreimageHom_val]

noncomputable def isomPrestackPreimageIso (a b : 𝒳.p.Fiber S)
    (q : (fiberProduct (isomPairMap a b) (diag 𝒳)).obj) :
    (isomPrestackComparison a b).obj (isomPrestackPreimageObj a b q) ≅ q := by
  let e₁ : ((isomPrestackComparison a b).obj
      (isomPrestackPreimageObj a b q)).fst ≅ q.fst := Iso.refl _
  let e₂ : ((isomPrestackComparison a b).obj
      (isomPrestackPreimageObj a b q)).snd ≅ q.snd :=
    isomPrestackTargetFstIso a b q
  have he₁ : IsHomLift (overBased S).p (𝟙 q.fst.left) e₁.hom := by
    exact IsHomLift.id rfl
  have he₂ : IsHomLift 𝒳.p (𝟙 q.fst.left) e₂.hom := by
    exact FiberProductHom.isHomLift_fst q.iso.hom (𝟙 q.fst.left) q.isHomLift
  apply FiberProductObj.isoMk e₁ e₂
  · exact isHomLift_map_of_common_lift (𝟙 q.fst.left) e₁.hom e₂.hom he₁ he₂
  · apply FiberProductHom.ext
    · simp only [FiberProductObj.comp_fst, fiberProductLift_map_fst,
        isomPrestackComparison_obj_iso_hom_fst, diag_map_fst,
        isomPrestackTargetFstIso_hom]
      dsimp [e₁, e₂]
      rw [(twoYonedaPullback S a).toFunctor.map_id]
      dsimp only [BasedFunctor.id]
      rw [Functor.id_map, Category.id_comp]
    · simp only [FiberProductObj.comp_snd, fiberProductLift_map_snd,
        isomPrestackComparison_obj_iso_hom_snd, diag_map_snd,
        isomPrestackTargetSndIso_hom]
      rw [isomPrestackPreimageHom_inv_val]
      dsimp [e₁, e₂]
      dsimp only [BasedFunctor.id]
      rw [Functor.id_map, (twoYonedaPullback S b).toFunctor.map_id,
        Category.id_comp]
      rw [← isomPrestackTargetFstIso_inv a b q,
        ← isomPrestackTargetFstIso_hom a b q,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma isomPrestackComparison_essSurj (a b : 𝒳.p.Fiber S) :
    (isomPrestackComparison a b).toFunctor.EssSurj := by
  constructor
  intro q
  exact ⟨isomPrestackPreimageObj a b q, ⟨isomPrestackPreimageIso a b q⟩⟩

/-- **Exercise 3.4.39** (`exer:isom-presheaf`) (part (b)): the square formed by
`Isom(a,b) → S`, `(a,b) : S → 𝒳 × 𝒳`, and the diagonal `𝒳 → 𝒳 × 𝒳` is
cartesian: its canonical comparison with the fiber product is an equivalence. -/
theorem isEquivalence_isomPrestackComparison (a b : 𝒳.p.Fiber S) :
    (isomPrestackComparison a b).toFunctor.IsEquivalence := by
  letI : (isomPrestackComparison a b).toFunctor.Faithful :=
    isomPrestackComparison_faithful a b
  letI : (isomPrestackComparison a b).toFunctor.Full :=
    isomPrestackComparison_full a b
  letI : (isomPrestackComparison a b).toFunctor.EssSurj :=
    isomPrestackComparison_essSurj a b
  exact { faithful := inferInstance, full := inferInstance, essSurj := inferInstance }

/-- **Exercise 3.4.39** (`exer:isom-presheaf`) (part (c)): for an object `a` of a
prestack over `S`, its automorphisms after pullback form a presheaf of groups on
`𝒮/S`. Multiplication is composition in the conventional automorphism-group order. -/
noncomputable def autPresheaf (a : 𝒳.p.Fiber S) : (Over S)ᵒᵖ ⥤ GrpCat.{v₂} where
  obj f := GrpCat.of (End (pullbackFiberObj a f.unop))
  map {f g} k := GrpCat.ofHom
    { toFun := isomRestriction a a k.unop
      map_one' := isomRestriction_id a k.unop
      map_mul' := by
        intro phi psi
        change isomRestriction a a k.unop (psi ≫ phi) =
          isomRestriction a a k.unop psi ≫ isomRestriction a a k.unop phi
        exact isomRestriction_comp a a a k.unop psi phi }
  map_id f := by
    ext phi
    exact congrArg (fun q ↦ q phi) ((isomPresheaf a a).map_id f)
  map_comp {f g h} k l := by
    ext phi
    exact congrArg (fun q ↦ q phi) ((isomPresheaf a a).map_comp k l)


/-- **Exercise 3.4.39** (`exer:isom-presheaf`) (part (d)): a prestack is
equivalent to a presheaf if and only if its diagonal is fully faithful. -/
theorem isEquivalentToPresheaf_iff_diag_full_and_faithful :
    IsEquivalentToPresheaf (𝒳 := 𝒳) ↔
      (diag 𝒳).toFunctor.Full ∧ (diag 𝒳).toFunctor.Faithful := by
  constructor
  · rintro ⟨F, E, hE⟩
    letI := hE
    letI : 𝒳.p.Faithful :=
      projection_faithful_of_equivalence_from_elements E
    exact ⟨diag_full_of_projection_faithful (𝒳 := 𝒳),
      diag_faithful (𝒳 := 𝒳)⟩
  · intro hdiag
    have hp : 𝒳.p.Faithful :=
      diag_isMonomorphism_iff_projection_faithful.mp hdiag
    letI := hp
    exact ⟨fiberComponents (𝒳 := 𝒳),
      componentPrestackComparison (𝒳 := 𝒳),
      isEquivalence_componentPrestackComparison (𝒳 := 𝒳)⟩


end CategoryTheory.BasedCategory

end ExerIsomPresheaf
