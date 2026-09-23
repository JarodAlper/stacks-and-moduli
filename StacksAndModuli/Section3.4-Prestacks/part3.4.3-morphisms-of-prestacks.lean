module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.1-definition-of-a-prestack»
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory

/-!
# Morphisms of prestacks

This module formalizes `def:morphisms-of-prestacks` and the exercises following it of §3.4
(Prestacks) of *Stacks and Moduli*, section
label `sec:prestacks` (subsection label `subsec:morphisms-of-prestacks`).

A morphism of prestacks is a functor strictly compatible with the projections — Mathlib's
`BasedFunctor` (`𝒳 ⥤ᵇ 𝒴`) — and a 2-morphism is a natural transformation all of whose
components lie over identities — Mathlib's `BasedNatTrans`. The category `MOR(𝒳, 𝒴)` is the
hom-category of the (strict) bicategory `BasedCategory 𝒮`.

Main declarations:
- recalls of `CategoryTheory.BasedFunctor` and `CategoryTheory.BasedNatTrans`;
- `CategoryTheory.BasedNatTrans.isIso_of_isFiberedInGroupoids` and the `Groupoid` instance
  on hom-categories: every 2-morphism into a prestack is a 2-isomorphism;
- `CategoryTheory.BasedFunctor.IsMonomorphism`, `.IsEpimorphism`, and `.IsIsomorphism`;
- `CategoryTheory.BasedFunctor.isMonomorphism_iff_onFiber` and
  `.isIsomorphism_iff_monomorphism_and_epimorphism`, the two parts of Exercise 3.4.19.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

-- The fibered-category equivalence below unfolds a large anonymous functor structure.
set_option maxHeartbeats 1000000


section DefMorphismsOfPrestacks

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

/- **Definition 3.4.17** (`def:morphisms-of-prestacks`) (part (1)): a *morphism of
prestacks* `𝒳 → 𝒴` over `𝒮` is a functor commuting strictly with the projections to `𝒮`;
in Mathlib this is a `BasedFunctor 𝒳 𝒴`, written `𝒳 ⥤ᵇ 𝒴`. -/
example (𝒳 : BasedCategory.{v₂, u₂} 𝒮) (𝒴 : BasedCategory.{v₃, u₃} 𝒮) := 𝒳 ⥤ᵇ 𝒴

/- The commutation is strict: an equality of functors. -/
example {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮} (F : 𝒳 ⥤ᵇ 𝒴) :
    F.toFunctor ⋙ 𝒴.p = 𝒳.p :=
  F.w

/- **Definition 3.4.17** (`def:morphisms-of-prestacks`) (part (2)): a *2-morphism*
`α : f → g` between morphisms of prestacks is a natural transformation whose components
lie over identities; in Mathlib, a `BasedNatTrans f g`. (When the target is a prestack,
every such `α` is automatically an isomorphism — see below — which is why the book calls
them 2-isomorphisms.) -/
example {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮} (F G : 𝒳 ⥤ᵇ 𝒴) :=
  BasedNatTrans F G

/- **Definition 3.4.17** (`def:morphisms-of-prestacks`) (part (3)): the category
`MOR(𝒳, 𝒴)` of morphisms of prestacks and 2-morphisms — the hom-category of the strict
bicategory of based categories. -/
example (𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒮) : Category (𝒳 ⟶ 𝒴) :=
  inferInstance

namespace CategoryTheory.BasedNatTrans

variable {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒮}

/-- Result of the unlabeled exercise in Subsection 3.4.4
following Definition 3.4.17): let `𝒴` be a prestack over `𝒮`; every 2-morphism between
morphisms of prestacks `𝒳 ⟶ 𝒴` is an isomorphism. -/
instance isIso_of_isFiberedInGroupoids [𝒴.p.IsFiberedInGroupoids] {F G : 𝒳 ⟶ 𝒴}
    (α : F ⟶ G) : IsIso α := by
  have h : ∀ a : 𝒳.obj, IsIso (α.toNatTrans.app a) := fun a ↦
    Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id (p := 𝒴.p)
      (S := 𝒳.p.obj a) (α.toNatTrans.app a)
  have : IsIso (X := F.toFunctor) (Y := G.toFunctor) α.toNatTrans :=
    NatIso.isIso_of_isIso_app α.toNatTrans
  exact BasedNatIso.isIso_of_toNatTrans_isIso α

/-- Result of the unlabeled exercise in Subsection 3.4.4
following Definition 3.4.17): the category `MOR(𝒳, 𝒴)` of morphisms of prestacks into a
prestack is a groupoid. -/
noncomputable instance [𝒴.p.IsFiberedInGroupoids] : Groupoid (𝒳 ⟶ 𝒴) :=
  Groupoid.ofIsIso fun _ ↦ inferInstance

end CategoryTheory.BasedNatTrans

namespace CategoryTheory.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} 𝒮} {𝒴 : BasedCategory.{v₃, u₃} 𝒮}

/-- Background definition used in Exercise 3.4.19 (the
implicit definition of the induced functor `f_S`): the functor `𝒳(S) ⥤ 𝒴(S)` induced by a
morphism of prestacks on the fiber categories over an object `S` of the base. -/
def onFiber (F : 𝒳 ⥤ᵇ 𝒴) (S : 𝒮) : 𝒳.p.Fiber S ⥤ 𝒴.p.Fiber S where
  obj a := Fiber.mk (show 𝒴.p.obj (F.obj (Fiber.fiberInclusion.obj a)) = S from
    (Functor.congr_obj F.w _).trans
      (Functor.congr_obj Fiber.fiberInclusion_comp_eq_const a))
  map {a b} φ := Fiber.homMk 𝒴.p S (F.map (Fiber.fiberInclusion.map φ))
  map_id a := by
    apply Fiber.hom_ext
    simp
  map_comp φ ψ := by
    apply Fiber.hom_ext
    simp

@[simp]
lemma fiberInclusion_onFiber_obj (F : 𝒳 ⥤ᵇ 𝒴) (S : 𝒮) (a : 𝒳.p.Fiber S) :
    Fiber.fiberInclusion.obj ((F.onFiber S).obj a) =
      F.obj (Fiber.fiberInclusion.obj a) :=
  rfl

@[simp]
lemma fiberInclusion_onFiber_map (F : 𝒳 ⥤ᵇ 𝒴) (S : 𝒮) {a b : 𝒳.p.Fiber S} (φ : a ⟶ b) :
    Fiber.fiberInclusion.map ((F.onFiber S).map φ) =
      F.map (Fiber.fiberInclusion.map φ) :=
  rfl

/- Background formulation for part (5) of Definition 3.4.17: a morphism of prestacks is a *monomorphism*
if it is fully faithful and an *epimorphism* if it is essentially surjective; these are
the conditions `F.toFunctor.Full ∧ F.toFunctor.Faithful` and `F.toFunctor.EssSurj` on the
underlying functor. -/
example (F : 𝒳 ⥤ᵇ 𝒴) : Prop := F.toFunctor.Full ∧ F.toFunctor.Faithful

example (F : 𝒳 ⥤ᵇ 𝒴) : Prop := F.toFunctor.EssSurj

/-- A full morphism of based categories induces a full functor on every fiber category. -/
lemma onFiber_full (F : 𝒳 ⥤ᵇ 𝒴) [F.toFunctor.Full] (S : 𝒮) : (F.onFiber S).Full := by
  constructor
  intro a b φ
  let ψ : Fiber.fiberInclusion.obj a ⟶ Fiber.fiberInclusion.obj b :=
    F.toFunctor.preimage (Fiber.fiberInclusion.map φ)
  have hψS : IsHomLift 𝒳.p (𝟙 S) ψ := by
    haveI : IsHomLift 𝒴.p (𝟙 S) (F.map ψ) := by
      rw [F.toFunctor.map_preimage]
      exact φ.2
    exact F.isHomLift_map (𝟙 S) ψ
  refine ⟨⟨ψ, hψS⟩, ?_⟩
  apply Fiber.hom_ext
  exact F.toFunctor.map_preimage (Fiber.fiberInclusion.map φ)

/-- A faithful morphism of based categories induces a faithful functor on every fiber category. -/
lemma onFiber_faithful (F : 𝒳 ⥤ᵇ 𝒴) [F.toFunctor.Faithful] (S : 𝒮) :
    (F.onFiber S).Faithful := by
  constructor
  intro a b φ ψ h
  apply Fiber.hom_ext
  apply F.toFunctor.map_injective
  exact congrArg Fiber.fiberInclusion.map h

variable {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒮}

/-- An essentially surjective morphism of prestacks induces an essentially surjective
functor on every fiber category. -/
lemma onFiber_essSurj [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]
    (F : 𝒳 ⥤ᵇ 𝒴) [F.toFunctor.EssSurj] (S : 𝒮) : (F.onFiber S).EssSurj := by
  classical
  constructor
  intro b
  let a₀ : 𝒳.obj := F.toFunctor.objPreimage (Fiber.fiberInclusion.obj b)
  let e₀ : F.obj a₀ ≅ Fiber.fiberInclusion.obj b :=
    F.toFunctor.objObjPreimageIso (Fiber.fiberInclusion.obj b)
  let eBase : 𝒳.p.obj a₀ ≅ S :=
    (eqToIso (F.w_obj a₀)).symm ≪≫ 𝒴.p.mapIso e₀ ≪≫ eqToIso b.2
  obtain ⟨a, χ, hχ⟩ :=
    IsFiberedInGroupoids.exists_isHomLift (p := 𝒳.p) (a := a₀) eBase.inv
  letI := hχ
  haveI : IsIso χ :=
    IsFiberedInGroupoids.isIso_of_isHomLift_isIso (p := 𝒳.p) eBase.inv χ
  let e : F.obj a ≅ Fiber.fiberInclusion.obj b := asIso (F.map χ) ≪≫ e₀
  have ha : 𝒳.p.obj a = S := IsHomLift.domain_eq 𝒳.p eBase.inv χ
  have he : IsHomLift 𝒴.p (𝟙 S) e.hom := by
    haveI he₀ : IsHomLift 𝒴.p eBase.hom e₀.hom := by
      apply IsHomLift.of_fac 𝒴.p eBase.hom e₀.hom (F.w_obj a₀) b.2
      simp [eBase]
    have hecomp : IsHomLift 𝒴.p (eBase.inv ≫ eBase.hom) (F.map χ ≫ e₀.hom) :=
      inferInstance
    simpa [e] using hecomp
  let a' : 𝒳.p.Fiber S := Fiber.mk ha
  let ehom : (F.onFiber S).obj a' ⟶ b := ⟨e.hom, he⟩
  exact ⟨a', ⟨asIso ehom⟩⟩


/-- Background definition used for part (5) of Definition 3.4.17 (the isomorphism
clause): a morphism of
prestacks `F : 𝒳 ⟶ 𝒴` is an *isomorphism of prestacks* (an equivalence in the bicategory
of based categories) if there is a morphism `G : 𝒴 ⟶ 𝒳` together with 2-isomorphisms
`F ≫ G ≅ 𝟙 𝒳` and `G ≫ F ≅ 𝟙 𝒴`. -/
class IsEquivalence (F : 𝒳 ⟶ 𝒴) : Prop where
  exists_inverse : ∃ G : 𝒴 ⟶ 𝒳,
    Nonempty ((F : 𝒳 ⟶ 𝒴) ≫ G ≅ 𝟙 𝒳) ∧ Nonempty (G ≫ F ≅ 𝟙 𝒴)

/-- API lemma used in Exercise 3.4.19 (part (a)): a morphism of prestacks is a
monomorphism (fully faithful) if and only if the
induced functors `f_S : 𝒳(S) ⥤ 𝒴(S)` on all fiber categories are fully faithful. -/
theorem full_and_faithful_iff_onFiber [𝒳.p.IsFiberedInGroupoids]
    [𝒴.p.IsFiberedInGroupoids] (F : 𝒳 ⥤ᵇ 𝒴) :
    (F.toFunctor.Full ∧ F.toFunctor.Faithful) ↔
      ∀ S : 𝒮, (F.onFiber S).Full ∧ (F.onFiber S).Faithful := by
  constructor
  · rintro ⟨hfull, hfaithful⟩ S
    letI := hfull
    letI := hfaithful
    exact ⟨onFiber_full F S, onFiber_faithful F S⟩
  · intro h
    classical
    constructor
    · constructor
      intro a b φ
      let R : 𝒮 := 𝒳.p.obj a
      let g : R ⟶ 𝒳.p.obj b :=
        eqToHom (F.w_obj a).symm ≫ 𝒴.p.map φ ≫ eqToHom (F.w_obj b)
      obtain ⟨a', χ, hχ⟩ :=
        IsFiberedInGroupoids.exists_isHomLift (p := 𝒳.p) (a := b) g
      letI := hχ
      haveI hφ : IsHomLift 𝒴.p g φ := by
        apply IsHomLift.of_fac 𝒴.p g φ (F.w_obj a) (F.w_obj b)
        simp [g]
      haveI hFχ : IsStronglyCartesian 𝒴.p g (F.map χ) := inferInstance
      let δ : F.obj a ⟶ F.obj a' :=
        IsStronglyCartesian.map 𝒴.p g (F.map χ) (Category.id_comp g).symm φ
      haveI hδ : IsHomLift 𝒴.p (𝟙 R) δ :=
        IsStronglyCartesian.map_isHomLift 𝒴.p g (F.map χ)
          (Category.id_comp g).symm φ
      let aa : 𝒳.p.Fiber R := Fiber.mk rfl
      let aa' : 𝒳.p.Fiber R := Fiber.mk (IsHomLift.domain_eq 𝒳.p g χ)
      let δ' : (F.onFiber R).obj aa ⟶ (F.onFiber R).obj aa' := ⟨δ, hδ⟩
      letI : (F.onFiber R).Full := (h R).1
      let ε' : aa ⟶ aa' := (F.onFiber R).preimage δ'
      have hε : F.map (Fiber.fiberInclusion.map ε') = δ := by
        have hε' := (F.onFiber R).map_preimage δ'
        exact congrArg Fiber.fiberInclusion.map hε'
      refine ⟨Fiber.fiberInclusion.map ε' ≫ χ, ?_⟩
      calc
        F.map (Fiber.fiberInclusion.map ε' ≫ χ) = δ ≫ F.map χ := by
          rw [F.toFunctor.map_comp, hε]
        _ = φ := by simp [δ]
    · constructor
      intro a b α β hαβ
      let R : 𝒮 := 𝒳.p.obj a
      let g : R ⟶ 𝒳.p.obj b := 𝒳.p.map α
      haveI hβF : IsHomLift 𝒴.p g (F.map β) := by
        rw [← hαβ]
        infer_instance
      haveI hβ : IsHomLift 𝒳.p g β := F.isHomLift_map g β
      let δ : a ⟶ a :=
        IsStronglyCartesian.map 𝒳.p g α (Category.id_comp g).symm β
      haveI hδ : IsHomLift 𝒳.p (𝟙 R) δ :=
        IsStronglyCartesian.map_isHomLift 𝒳.p g α
          (Category.id_comp g).symm β
      have hFδ : F.map δ = 𝟙 (F.obj a) := by
        apply IsStronglyCartesian.ext (p := 𝒴.p) (f := g) (F.map α) (𝟙 R)
        rw [← F.toFunctor.map_comp, IsStronglyCartesian.fac, ← hαβ]
        simp
      let aa : 𝒳.p.Fiber R := Fiber.mk rfl
      let δ' : aa ⟶ aa := ⟨δ, hδ⟩
      letI : (F.onFiber R).Faithful := (h R).2
      have hδ' : (F.onFiber R).map δ' = (F.onFiber R).map (𝟙 aa) := by
        apply Fiber.hom_ext
        dsimp [δ', aa]
        rw [show Fiber.fiberInclusion.map (⟨δ, hδ⟩ : Fiber.mk rfl ⟶ Fiber.mk rfl) =
          δ from rfl]
        rw [show Fiber.fiberInclusion.map (𝟙 (Fiber.mk rfl : 𝒳.p.Fiber R)) =
          𝟙 a from rfl, F.toFunctor.map_id]
        exact hFδ
      have hδid : δ' = 𝟙 aa := (h R).2.map_injective hδ'
      have hδ_underlying : δ = 𝟙 a := congrArg Fiber.fiberInclusion.map hδid
      calc
        α = 𝟙 a ≫ α := (Category.id_comp α).symm
        _ = δ ≫ α := by rw [hδ_underlying]
        _ = β := IsStronglyCartesian.fac 𝒳.p g α (Category.id_comp g).symm β

/-- API lemma used in Exercise 3.4.19 (part (b)): a morphism of prestacks is an
isomorphism if and only if it is fully faithful
and essentially surjective. -/
theorem isEquivalence_iff_full_and_faithful_and_essSurj [𝒳.p.IsFiberedInGroupoids]
    [𝒴.p.IsFiberedInGroupoids] (F : 𝒳 ⟶ 𝒴) :
    IsEquivalence F ↔
      F.toFunctor.Full ∧ F.toFunctor.Faithful ∧ F.toFunctor.EssSurj := by
  constructor
  · rintro ⟨G, ⟨α⟩, ⟨β⟩⟩
    letI : F.toFunctor.IsEquivalence :=
      Functor.IsEquivalence.mk' G.toFunctor
        ((BasedNatTrans.forgetful 𝒳 𝒳).mapIso α).symm
        ((BasedNatTrans.forgetful 𝒴 𝒴).mapIso β)
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  · rintro ⟨hfull, hfaithful, hess⟩
    classical
    letI : F.toFunctor.Full := hfull
    letI : F.toFunctor.Faithful := hfaithful
    letI : F.toFunctor.EssSurj := hess
    let fiberEssSurj (S : 𝒮) : (F.onFiber S).EssSurj := onFiber_essSurj F S
    let yFiber (y : 𝒴.obj) : 𝒴.p.Fiber (𝒴.p.obj y) := Fiber.mk rfl
    let aFiber (y : 𝒴.obj) : 𝒳.p.Fiber (𝒴.p.obj y) :=
      letI := fiberEssSurj (𝒴.p.obj y)
      (F.onFiber (𝒴.p.obj y)).objPreimage (yFiber y)
    let τFiber (y : 𝒴.obj) :
        (F.onFiber (𝒴.p.obj y)).obj (aFiber y) ≅ yFiber y :=
      letI := fiberEssSurj (𝒴.p.obj y)
      (F.onFiber (𝒴.p.obj y)).objObjPreimageIso (yFiber y)
    let τ (y : 𝒴.obj) : F.obj (Fiber.fiberInclusion.obj (aFiber y)) ≅ y :=
      Fiber.fiberInclusion.mapIso (τFiber y)
    have τ_hom_lift (y : 𝒴.obj) :
        IsHomLift 𝒴.p (𝟙 (𝒴.p.obj y)) (τ y).hom :=
      (τFiber y).hom.2
    have τ_inv_lift (y : 𝒴.obj) :
        IsHomLift 𝒴.p (𝟙 (𝒴.p.obj y)) (τ y).inv :=
      (τFiber y).inv.2
    let G : 𝒴 ⥤ᵇ 𝒳 :=
      { obj := fun y ↦ Fiber.fiberInclusion.obj (aFiber y)
        map := fun {y z} k ↦ F.toFunctor.preimage ((τ y).hom ≫ k ≫ (τ z).inv)
        map_id := fun y ↦ by
          apply F.toFunctor.map_injective
          simp only [F.toFunctor.map_preimage, Functor.map_id, Category.id_comp]
          exact (τ y).hom_inv_id
        map_comp := fun k l ↦ by
          apply F.toFunctor.map_injective
          simp only [F.toFunctor.map_comp, F.toFunctor.map_preimage, Category.assoc,
            Iso.inv_hom_id_assoc]
        w := by
          refine Functor.ext_of_iso
            (NatIso.ofComponents (fun y ↦ eqToIso (aFiber y).2) ?_)
            (fun y ↦ (aFiber y).2)
          intro y z k
          haveI hy := τ_hom_lift y
          haveI hz := τ_inv_lift z
          haveI hk : IsHomLift 𝒴.p (𝒴.p.map k)
              ((τ y).hom ≫ k ≫ (τ z).inv) := by
            infer_instance
          haveI hpre : IsHomLift 𝒳.p (𝒴.p.map k)
              (F.toFunctor.preimage ((τ y).hom ≫ k ≫ (τ z).inv)) := by
            apply (F.isHomLift_iff (𝒴.p.map k) (F.toFunctor.preimage
              ((τ y).hom ≫ k ≫ (τ z).inv))).mp
            rw [F.toFunctor.map_preimage]
            exact hk
          have hfac := IsHomLift.fac' 𝒳.p (𝒴.p.map k)
            (F.toFunctor.preimage ((τ y).hom ≫ k ≫ (τ z).inv))
          simp only [Functor.comp_map, hfac]
          simp }
    -- Record the defining property of `G.map` once, rather than unfolding the anonymous
    -- structure inside each naturality proof (which is prohibitively expensive).
    have hGmap : ∀ {y z : 𝒴.obj} (k : y ⟶ z),
        F.map (G.map k) = (τ y).hom ≫ k ≫ (τ z).inv :=
      fun k ↦ F.toFunctor.map_preimage _
    let βNat : (G.comp F).toFunctor ≅ (BasedFunctor.id 𝒴).toFunctor :=
      NatIso.ofComponents τ (fun {y z} k ↦ by
        show F.map (G.map k) ≫ (τ z).hom = (τ y).hom ≫ k
        rw [hGmap]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    let β : G ≫ F ≅ 𝟙 𝒴 :=
      BasedNatIso.mkNatIso βNat τ_hom_lift
    let σ (x : 𝒳.obj) : G.obj (F.obj x) ≅ x :=
      F.toFunctor.preimageIso (τ (F.obj x))
    let σNat : (F.comp G).toFunctor ≅ (BasedFunctor.id 𝒳).toFunctor :=
      NatIso.ofComponents σ (fun {x x'} k ↦ by
        apply F.toFunctor.map_injective
        show F.map (G.map (F.map k) ≫ (σ x').hom) = F.map ((σ x).hom ≫ k)
        rw [F.toFunctor.map_comp, F.toFunctor.map_comp, hGmap]
        simp only [σ, Functor.preimageIso_hom, F.toFunctor.map_preimage, Category.assoc,
          Iso.inv_hom_id, Category.comp_id])
    have σ_hom_lift (x : 𝒳.obj) :
        IsHomLift 𝒳.p (𝟙 (𝒳.p.obj x)) (σ x).hom := by
      haveI hτ : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj x)) (τ (F.obj x)).hom :=
        F.w_obj x ▸ τ_hom_lift (F.obj x)
      haveI hσmap : IsHomLift 𝒴.p (𝟙 (𝒳.p.obj x)) (F.map (σ x).hom) := by
        rw [show F.map (σ x).hom = (τ (F.obj x)).hom by simp [σ]]
        infer_instance
      exact F.isHomLift_map (𝟙 (𝒳.p.obj x)) (σ x).hom
    let α : F ≫ G ≅ 𝟙 𝒳 :=
      BasedNatIso.mkNatIso σNat σ_hom_lift
    exact ⟨G, ⟨α⟩, ⟨β⟩⟩

end CategoryTheory.BasedFunctor

end DefMorphismsOfPrestacks


section DefMorphismsOfPrestacksMonomorphism

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.BasedFunctor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒮}

/-- **Definition 3.4.17** (`def:morphisms-of-prestacks`) (part (5), monomorphisms): a
morphism of prestacks is a monomorphism when its underlying functor is fully faithful. -/
abbrev IsMonomorphism (F : BasedFunctor 𝒳 𝒴) : Prop :=
  F.toFunctor.Full ∧ F.toFunctor.Faithful

/-- **Definition 3.4.17** (`def:morphisms-of-prestacks`) (part (5), epimorphisms): a
morphism of prestacks is an epimorphism when its underlying functor is essentially
surjective. -/
abbrev IsEpimorphism (F : BasedFunctor 𝒳 𝒴) : Prop :=
  F.toFunctor.EssSurj

/-- **Definition 3.4.17** (`def:morphisms-of-prestacks`) (part (5), isomorphisms): an
isomorphism of prestacks is a morphism admitting a two-sided inverse up to 2-isomorphism. -/
abbrev IsIsomorphism (F : BasedFunctor 𝒳 𝒴) : Prop :=
  F.IsEquivalence

end CategoryTheory.BasedFunctor

end DefMorphismsOfPrestacksMonomorphism


section ExerMorphismPrestacksFullyFaithfulIsomorphism

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.BasedFunctor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  {𝒳 𝒴 : BasedCategory.{v₂, u₂} 𝒮}

/-- **Exercise 3.4.19** (`exer:morphism-prestacks-fully-faithful-isomorphism`)
(part (a)): a morphism of prestacks is a monomorphism if and only if its restriction to
every fiber category is fully faithful. -/
theorem isMonomorphism_iff_onFiber [𝒳.p.IsFiberedInGroupoids]
    [𝒴.p.IsFiberedInGroupoids] (F : BasedFunctor 𝒳 𝒴) :
    F.IsMonomorphism ↔
      ∀ S : 𝒮, (F.onFiber S).Full ∧ (F.onFiber S).Faithful :=
  F.full_and_faithful_iff_onFiber

/-- **Exercise 3.4.19** (`exer:morphism-prestacks-fully-faithful-isomorphism`)
(part (b)): a morphism of prestacks is an isomorphism if and only if it is fully faithful
and essentially surjective. -/
theorem isIsomorphism_iff_monomorphism_and_epimorphism [𝒳.p.IsFiberedInGroupoids]
    [𝒴.p.IsFiberedInGroupoids] (F : BasedFunctor 𝒳 𝒴) :
    F.IsIsomorphism ↔ F.IsMonomorphism ∧ F.IsEpimorphism := by
  simpa only [IsIsomorphism, IsMonomorphism, IsEpimorphism, and_assoc] using
    F.isEquivalence_iff_full_and_faithful_and_essSurj

end CategoryTheory.BasedFunctor

end ExerMorphismPrestacksFullyFaithfulIsomorphism
