module

public import StacksAndModuli.API.FiberProductEquivalence

/-!
# Universe-polymorphic equivalences of based categories

An equivalence on the underlying categories of a morphism between categories fibered in
groupoids admits a quasi-inverse over the base. This file supplies the universe-polymorphic
form of that result.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.BasedFunctor

variable {C : Type u₁} [Category.{v₁} C]
  {X : BasedCategory.{v₂, u₂} C}
  {Y : BasedCategory.{v₃, u₃} C}

/-- A universe-heterogeneous based functor between categories fibered in groupoids whose
underlying functor is an equivalence admits a based quasi-inverse. -/
theorem exists_inverse_of_toFunctor (F : BasedFunctor X Y)
    [X.p.IsFiberedInGroupoids] [Y.p.IsFiberedInGroupoids]
    [F.toFunctor.IsEquivalence] :
    ∃ G : BasedFunctor Y X, Nonempty (F.comp G ≅ BasedFunctor.id X) ∧
      Nonempty (G.comp F ≅ BasedFunctor.id Y) := by
  classical
  let fiberEssSurj (S : C) : (F.onFiber S).EssSurj :=
    BasedCategory.onFiber_essSurj_of_essSurj F S
  let yFiber (y : Y.obj) : Y.p.Fiber (Y.p.obj y) := Fiber.mk rfl
  let aFiber (y : Y.obj) : X.p.Fiber (Y.p.obj y) :=
    letI := fiberEssSurj (Y.p.obj y)
    (F.onFiber (Y.p.obj y)).objPreimage (yFiber y)
  let τFiber (y : Y.obj) :
      (F.onFiber (Y.p.obj y)).obj (aFiber y) ≅ yFiber y :=
    letI := fiberEssSurj (Y.p.obj y)
    (F.onFiber (Y.p.obj y)).objObjPreimageIso (yFiber y)
  let τ (y : Y.obj) : F.obj (Fiber.fiberInclusion.obj (aFiber y)) ≅ y :=
    Fiber.fiberInclusion.mapIso (τFiber y)
  have τ_hom_lift (y : Y.obj) :
      IsHomLift Y.p (𝟙 (Y.p.obj y)) (τ y).hom :=
    (τFiber y).hom.2
  have τ_inv_lift (y : Y.obj) :
      IsHomLift Y.p (𝟙 (Y.p.obj y)) (τ y).inv :=
    (τFiber y).inv.2
  let G : BasedFunctor Y X :=
    { obj := fun y ↦ Fiber.fiberInclusion.obj (aFiber y)
      map := fun {y z} k ↦ F.toFunctor.preimage ((τ y).hom ≫ k ≫ (τ z).inv)
      map_id := fun y ↦ by
        apply F.toFunctor.map_injective
        simp only [F.toFunctor.map_preimage, Functor.map_id, Category.id_comp]
        exact (τ y).hom_inv_id
      map_comp := fun k l ↦ by
        apply F.toFunctor.map_injective
        simp only [F.toFunctor.map_comp, F.toFunctor.map_preimage,
          Category.assoc, Iso.inv_hom_id_assoc]
      w := by
        refine Functor.ext_of_iso
          (NatIso.ofComponents (fun y ↦ eqToIso (aFiber y).2) ?_)
          (fun y ↦ (aFiber y).2)
        intro y z k
        let _ := τ_hom_lift y
        let _ := τ_inv_lift z
        let hk : IsHomLift Y.p (Y.p.map k)
            ((τ y).hom ≫ k ≫ (τ z).inv) := by
          infer_instance
        let _ := hk
        let _ : IsHomLift X.p (Y.p.map k)
            (F.toFunctor.preimage ((τ y).hom ≫ k ≫ (τ z).inv)) := by
          apply (F.isHomLift_iff (Y.p.map k)
            (F.toFunctor.preimage ((τ y).hom ≫ k ≫ (τ z).inv))).mp
          rw [F.toFunctor.map_preimage]
          exact hk
        have hfac := IsHomLift.fac' X.p (Y.p.map k)
          (F.toFunctor.preimage ((τ y).hom ≫ k ≫ (τ z).inv))
        simp only [Functor.comp_map, hfac]
        simp }
  have hGmap : ∀ {y z : Y.obj} (k : y ⟶ z),
      F.map (G.map k) = (τ y).hom ≫ k ≫ (τ z).inv :=
    fun k ↦ F.toFunctor.map_preimage _
  let βNat : (G.comp F).toFunctor ≅ (BasedFunctor.id Y).toFunctor :=
    NatIso.ofComponents τ (fun {y z} k ↦ by
      change F.map (G.map k) ≫ (τ z).hom = (τ y).hom ≫ k
      rw [hGmap]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  let β : G.comp F ≅ BasedFunctor.id Y :=
    BasedNatIso.mkNatIso βNat τ_hom_lift
  let σ (x : X.obj) : G.obj (F.obj x) ≅ x :=
    F.toFunctor.preimageIso (τ (F.obj x))
  let σNat : (F.comp G).toFunctor ≅ (BasedFunctor.id X).toFunctor :=
    NatIso.ofComponents σ (fun {x x'} k ↦ by
      apply F.toFunctor.map_injective
      change F.map (G.map (F.map k) ≫ (σ x').hom) =
        F.map ((σ x).hom ≫ k)
      rw [F.toFunctor.map_comp, F.toFunctor.map_comp, hGmap]
      simp only [σ, Functor.preimageIso_hom, F.toFunctor.map_preimage,
        Category.assoc, Iso.inv_hom_id, Category.comp_id])
  have σ_hom_lift (x : X.obj) :
      IsHomLift X.p (𝟙 (X.p.obj x)) (σ x).hom := by
    let hτ : IsHomLift Y.p (𝟙 (X.p.obj x)) (τ (F.obj x)).hom :=
      F.w_obj x ▸ τ_hom_lift (F.obj x)
    let _ := hτ
    let _ : IsHomLift Y.p (𝟙 (X.p.obj x))
        (F.map (σ x).hom) := by
      rw [show F.map (σ x).hom = (τ (F.obj x)).hom by simp [σ]]
      infer_instance
    exact F.isHomLift_map (𝟙 (X.p.obj x)) (σ x).hom
  let α : F.comp G ≅ BasedFunctor.id X :=
    BasedNatIso.mkNatIso σNat σ_hom_lift
  exact ⟨G, ⟨α⟩, ⟨β⟩⟩

end CategoryTheory.BasedFunctor
