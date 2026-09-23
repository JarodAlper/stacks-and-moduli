module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.3-morphisms-of-prestacks»
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.2-examples»

/-!
# The 2-Yoneda lemma

This module formalizes `lem:2-yoneda` of §3.4 (Prestacks) of *Stacks and Moduli*,
section label `sec:prestacks` (the subsection "The
2-Yoneda Lemma" carries no label).

For a prestack `𝒳` over `𝒮` and an object `S : 𝒮`, evaluation at the identity
`𝟙 S ∈ 𝒮/S` defines a functor from the category `MOR(𝒮/S, 𝒳)` of morphisms of prestacks
to the fiber category `𝒳(S)`; the 2-Yoneda lemma asserts that it is an equivalence.

Main declarations:
- `CategoryTheory.BasedCategory.overBased`: the representable prestack `𝒮/S` as a based
  category;
- `CategoryTheory.BasedCategory.isEquivalence_twoYonedaEval`: the 2-Yoneda lemma.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section Lem2Yoneda

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.BasedCategory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/-- Background abbreviation for Example 3.4.8, repackaged as a based category:
the prestack represented by an object `S : 𝒮` — the restricted category `𝒮/S` with its
projection, as a based category over `𝒮`. -/
abbrev overBased (S : 𝒮) : BasedCategory 𝒮 where
  obj := Over S
  p := Over.forget S

instance (S : 𝒮) : (overBased S).p.IsFiberedInGroupoids :=
  inferInstanceAs (Over.forget S).IsFiberedInGroupoids

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} (S : 𝒮)

/-- Background definition for Lemma 3.4.21 (the evaluation
functor): evaluation at the identity — the functor `MOR(𝒮/S, 𝒳) ⥤ 𝒳(S)` sending a
morphism of prestacks `f : 𝒮/S → 𝒳` to `f_S(𝟙 S)` in the fiber category of `𝒳` over `S`,
and a 2-morphism to its component at `𝟙 S`. -/
@[simps]
def twoYonedaEval : (overBased S ⥤ᵇ 𝒳) ⥤ 𝒳.p.Fiber S where
  obj f := Fiber.mk (show 𝒳.p.obj (f.obj (Over.mk (𝟙 S))) = S from
    (Functor.congr_obj f.w (Over.mk (𝟙 S))))
  map {f g} α :=
    have : IsHomLift 𝒳.p (𝟙 S) (α.toNatTrans.app (Over.mk (𝟙 S))) := α.isHomLift rfl
    Fiber.homMk 𝒳.p S (α.toNatTrans.app (Over.mk (𝟙 S)))
  map_id f := by
    apply Fiber.hom_ext
    simp [BasedNatTrans.id]
  map_comp α β := by
    apply Fiber.hom_ext
    simp [BasedNatTrans.comp]

variable [𝒳.p.IsFiberedInGroupoids]

instance basedMap_isHomLift_left {F : overBased S ⥤ᵇ 𝒳} {X Y : Over S} (f : X ⟶ Y) :
    IsHomLift 𝒳.p f.left (F.map f) := by
  haveI : IsHomLift (overBased S).p f.left f := by
    apply IsHomLift.of_fac (overBased S).p f.left f rfl rfl
    simp
  exact BasedFunctor.preserves_isHomLift F f.left f

instance basedMap_comp_fiberHom_isHomLift {F G : overBased S ⥤ᵇ 𝒳}
    (α : (twoYonedaEval (𝒳 := 𝒳) S).obj F ⟶
      (twoYonedaEval (𝒳 := 𝒳) S).obj G) (X : Over S) :
    IsHomLift 𝒳.p X.hom
      (F.map (Over.homMk X.hom : X ⟶ Over.mk (𝟙 S)) ≫
        Fiber.fiberInclusion.map α) := by
  let t : X ⟶ Over.mk (𝟙 S) := Over.homMk X.hom
  change IsHomLift 𝒳.p X.hom (F.map t ≫ Fiber.fiberInclusion.map α)
  letI h₁ : IsHomLift 𝒳.p X.hom (F.map t) :=
    basedMap_isHomLift_left (𝒳 := 𝒳) (F := F) S t
  letI h₂ := α.2
  have h₃ := IsHomLift.comp 𝒳.p X.hom (𝟙 S)
    (F.map t)
    (Fiber.fiberInclusion.map α)
  simpa using h₃

/-- The morphism between chosen pullbacks induced by a morphism in the over category. -/
noncomputable def twoYonedaPullbackMap (a : 𝒳.p.Fiber S) {X Y : Over S} (f : X ⟶ Y) :
    IsPreFibered.pullbackObj a.2 X.hom ⟶ IsPreFibered.pullbackObj a.2 Y.hom :=
  IsStronglyCartesian.map 𝒳.p Y.hom (IsPreFibered.pullbackMap a.2 Y.hom)
    (Over.w f).symm (IsPreFibered.pullbackMap a.2 X.hom)

instance twoYonedaPullbackMap_isHomLift (a : 𝒳.p.Fiber S) {X Y : Over S} (f : X ⟶ Y) :
    IsHomLift 𝒳.p f.left (twoYonedaPullbackMap S a f) :=
  IsStronglyCartesian.map_isHomLift 𝒳.p Y.hom
    (IsPreFibered.pullbackMap a.2 Y.hom) (Over.w f).symm
    (IsPreFibered.pullbackMap a.2 X.hom)

@[reassoc (attr := simp)]
lemma twoYonedaPullbackMap_fac (a : 𝒳.p.Fiber S) {X Y : Over S} (f : X ⟶ Y) :
    twoYonedaPullbackMap S a f ≫ IsPreFibered.pullbackMap a.2 Y.hom =
      IsPreFibered.pullbackMap a.2 X.hom :=
  IsStronglyCartesian.fac 𝒳.p Y.hom (IsPreFibered.pullbackMap a.2 Y.hom)
    (Over.w f).symm (IsPreFibered.pullbackMap a.2 X.hom)

/-- Background construction used in the proof of Lemma 3.4.21 (the
quasi-inverse `Ψ` on objects): the morphism of prestacks represented by an object in the
fiber, obtained by taking chosen cartesian pullbacks along all arrows to `S`. -/
noncomputable def twoYonedaPullback (a : 𝒳.p.Fiber S) : overBased S ⥤ᵇ 𝒳 where
  obj X := IsPreFibered.pullbackObj a.2 X.hom
  map f := twoYonedaPullbackMap S a f
  map_id X := by
    have h₁ := twoYonedaPullbackMap_isHomLift S a (𝟙 X)
    have h₂ : IsHomLift 𝒳.p (𝟙 X.left)
        (𝟙 (IsPreFibered.pullbackObj a.2 X.hom)) :=
      IsHomLift.id (IsPreFibered.pullbackObj_proj a.2 X.hom)
    apply IsStronglyCartesian.ext (p := 𝒳.p) (f := X.hom)
      (IsPreFibered.pullbackMap a.2 X.hom) (𝟙 X.left)
    simp
  map_comp := fun {X Y Z} f g ↦ by
    have h₁ := twoYonedaPullbackMap_isHomLift S a (f ≫ g)
    have h₂ := twoYonedaPullbackMap_isHomLift S a f
    have h₃ := twoYonedaPullbackMap_isHomLift S a g
    have h₄ : IsHomLift 𝒳.p (f.left ≫ g.left)
        (twoYonedaPullbackMap S a f ≫ twoYonedaPullbackMap S a g) :=
      IsHomLift.comp 𝒳.p f.left g.left _ _
    apply IsStronglyCartesian.ext (p := 𝒳.p) (f := Z.hom)
      (IsPreFibered.pullbackMap a.2 Z.hom) (f.left ≫ g.left)
    simp
  w := by
    refine Functor.ext_of_iso
      (NatIso.ofComponents
        (fun X ↦ eqToIso (IsPreFibered.pullbackObj_proj a.2 X.hom)) ?_)
      (fun X ↦ IsPreFibered.pullbackObj_proj a.2 X.hom)
    intro X Y f
    have h := IsHomLift.fac' 𝒳.p f.left (twoYonedaPullbackMap S a f)
    simp only [Functor.comp_map, h]
    simp

/-- **Lemma 3.4.21** (`lem:2-yoneda`): the 2-Yoneda lemma — for a prestack `𝒳` over `𝒮`
and an object `S : 𝒮`, evaluation at the identity is an equivalence of categories
`MOR(𝒮/S, 𝒳) ≌ 𝒳(S)` between the category of morphisms of prestacks `𝒮/S → 𝒳` and the
fiber category of `𝒳` over `S`. -/
theorem isEquivalence_twoYonedaEval :
    (twoYonedaEval (𝒳 := 𝒳) S).IsEquivalence := by
  classical
  let E := twoYonedaEval (𝒳 := 𝒳) S
  have hfull : E.Full := by
    constructor
    intro F G α
    let terminalMap (X : Over S) : X ⟶ Over.mk (𝟙 S) := Over.homMk X.hom
    let app (X : Over S) : F.obj X ⟶ G.obj X :=
      letI : IsHomLift 𝒳.p X.hom (G.map (terminalMap X)) :=
        basedMap_isHomLift_left S (terminalMap X)
      IsStronglyCartesian.map 𝒳.p X.hom (G.map (terminalMap X))
        (Category.id_comp X.hom).symm
        (F.map (terminalMap X) ≫ Fiber.fiberInclusion.map α)
    have app_lift (X : Over S) : IsHomLift 𝒳.p (𝟙 X.left) (app X) :=
      letI : IsHomLift 𝒳.p X.hom (G.map (terminalMap X)) :=
        basedMap_isHomLift_left S (terminalMap X)
      IsStronglyCartesian.map_isHomLift 𝒳.p X.hom (G.map (terminalMap X))
        (Category.id_comp X.hom).symm
        (F.map (terminalMap X) ≫ Fiber.fiberInclusion.map α)
    have app_fac (X : Over S) :
        app X ≫ G.map (terminalMap X) =
          F.map (terminalMap X) ≫ Fiber.fiberInclusion.map α :=
      letI : IsHomLift 𝒳.p X.hom (G.map (terminalMap X)) :=
        basedMap_isHomLift_left S (terminalMap X)
      IsStronglyCartesian.fac 𝒳.p X.hom (G.map (terminalMap X))
        (Category.id_comp X.hom).symm
        (F.map (terminalMap X) ≫ Fiber.fiberInclusion.map α)
    let β : F ⟶ G :=
      { toNatTrans :=
          { app := app
            naturality := fun {X Y} f ↦ by
              have h₁ := app_lift X
              have h₂ := app_lift Y
              letI : IsHomLift 𝒳.p Y.hom (G.map (terminalMap Y)) :=
                basedMap_isHomLift_left S (terminalMap Y)
              apply IsStronglyCartesian.ext (p := 𝒳.p) (f := Y.hom)
                (G.map (terminalMap Y)) f.left
              have ht : f ≫ terminalMap Y = terminalMap X := by
                ext
                simp [terminalMap]
              calc
                (F.map f ≫ app Y) ≫ G.map (terminalMap Y) =
                    F.map f ≫ (F.map (terminalMap Y) ≫
                      Fiber.fiberInclusion.map α) := by rw [Category.assoc, app_fac Y]
                _ = F.map (f ≫ terminalMap Y) ≫ Fiber.fiberInclusion.map α := by
                  rw [← Category.assoc, F.toFunctor.map_comp]
                _ = F.map (terminalMap X) ≫ Fiber.fiberInclusion.map α := by rw [ht]
                _ = app X ≫ G.map (terminalMap X) := (app_fac X).symm
                _ = app X ≫ G.map (f ≫ terminalMap Y) := by rw [ht]
                _ = (app X ≫ G.map f) ≫ G.map (terminalMap Y) := by
                  rw [G.toFunctor.map_comp, Category.assoc] }
        isHomLift' := app_lift }
    refine ⟨β, ?_⟩
    apply Fiber.hom_ext
    letI : IsHomLift 𝒳.p (𝟙 S) (G.map (terminalMap (Over.mk (𝟙 S)))) :=
      basedMap_isHomLift_left S (terminalMap (Over.mk (𝟙 S)))
    apply IsStronglyCartesian.ext (p := 𝒳.p) (f := 𝟙 S)
      (G.map (terminalMap (Over.mk (𝟙 S)))) (𝟙 S)
    have ht : terminalMap (Over.mk (𝟙 S)) = 𝟙 (Over.mk (𝟙 S)) := by
      ext
      simp [terminalMap]
    rw [show Fiber.fiberInclusion.map (E.map β) = app (Over.mk (𝟙 S)) from rfl,
      app_fac, ht]
    simp
  have hfaithful : E.Faithful := by
    constructor
    intro F G α β h
    apply BasedNatTrans.ext
    ext X
    let terminalMap : X ⟶ Over.mk (𝟙 S) := Over.homMk X.hom
    letI hα : IsHomLift 𝒳.p (𝟙 X.left) (α.app X) := α.isHomLift rfl
    letI hβ : IsHomLift 𝒳.p (𝟙 X.left) (β.app X) := β.isHomLift rfl
    letI : IsHomLift 𝒳.p X.hom (G.map terminalMap) :=
      basedMap_isHomLift_left S terminalMap
    apply IsStronglyCartesian.ext (p := 𝒳.p) (f := X.hom)
      (G.map terminalMap) (𝟙 X.left)
    rw [← α.toNatTrans.naturality terminalMap, ← β.toNatTrans.naturality terminalMap]
    change F.map terminalMap ≫ Fiber.fiberInclusion.map (E.map α) =
      F.map terminalMap ≫ Fiber.fiberInclusion.map (E.map β)
    rw [h]
  have hess : E.EssSurj := by
    constructor
    intro a
    refine ⟨twoYonedaPullback S a, ?_⟩
    let π := IsPreFibered.pullbackMap a.2 (𝟙 S)
    have hπ : IsHomLift 𝒳.p (𝟙 S) π := inferInstance
    haveI : IsIso π :=
      IsFiberedInGroupoids.isIso_of_isHomLift_isIso (p := 𝒳.p) (𝟙 S) π
    let e : E.obj (twoYonedaPullback S a) ≅ a :=
      asIso (⟨π, hπ⟩ : E.obj (twoYonedaPullback S a) ⟶ a)
    exact ⟨e⟩
  exact { faithful := hfaithful, full := hfull, essSurj := hess }

end CategoryTheory.BasedCategory

end Lem2Yoneda
