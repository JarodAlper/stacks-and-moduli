module

public import StacksAndModuli.API.OpenImmersionModuleBaseChange
public import StacksAndModuli.API.RestrictPullbackPentagon
public import StacksAndModuli.API.PseudofunctorToCatPullbackComp

/-!
# Pasting open-immersion base-change squares

This file proves the pasting law for the explicit Beck--Chevalley comparison
`Scheme.Modules.restrictPushforwardIsoOfOpenSquare`.  It also packages the corresponding
functoriality statement after transposing across the restriction--pushforward adjunction.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

set_option maxHeartbeats 3000000 in
-- The explicit comparison is defined sectionwise, so its pasting law is most
-- efficiently checked after evaluating a module morphism on an open subset.
/-- Beck--Chevalley comparisons for module sheaves paste across two open squares. -/
@[reassoc]
lemma restrictPushforwardIsoOfOpenSquare_paste_hom
    {Z W Y P Y' Q : Scheme.{u}}
    (i : W ⟶ Z) (j : Y ⟶ Z) (g : P ⟶ Y) (k : P ⟶ W)
    (l : Y' ⟶ Y) (h : Q ⟶ Y') (m : Q ⟶ P)
    [IsOpenImmersion j] [IsOpenImmersion k]
    [IsOpenImmersion l] [IsOpenImmersion m]
    (hsq₁ : g ≫ j = k ≫ i) (hsq₂ : h ≫ l = m ≫ g)
    (hopen₁ : ∀ U : Y.Opens, k ''ᵁ (g ⁻¹ᵁ U) = i ⁻¹ᵁ (j ''ᵁ U))
    (hopen₂ : ∀ U : Y'.Opens, m ''ᵁ (h ⁻¹ᵁ U) = g ⁻¹ᵁ (l ''ᵁ U))
    (hopen₃ : ∀ U : Y'.Opens,
      (m ≫ k) ''ᵁ (h ⁻¹ᵁ U) = i ⁻¹ᵁ ((l ≫ j) ''ᵁ U))
    (M : W.Modules) :
    (restrictFunctorComp l j).hom.app ((pushforward i).obj M) ≫
        (restrictFunctor l).map
          (restrictPushforwardIsoOfOpenSquare i g k j hsq₁ hopen₁ M).hom ≫
        (restrictPushforwardIsoOfOpenSquare g h m l hsq₂ hopen₂
          ((restrictFunctor k).obj M)).hom ≫
        (pushforward h).map ((restrictFunctorComp m k).inv.app M) =
      (restrictPushforwardIsoOfOpenSquare i h (m ≫ k) (l ≫ j)
        (by
          calc
            (h ≫ l) ≫ j = (m ≫ g) ≫ j :=
              congrArg (fun z ↦ z ≫ j) hsq₂
            _ = m ≫ (g ≫ j) := Category.assoc _ _ _
            _ = m ≫ (k ≫ i) := congrArg (fun z ↦ m ≫ z) hsq₁
            _ = (m ≫ k) ≫ i := (Category.assoc _ _ _).symm)
        hopen₃ M).hom := by
  apply Modules.hom_ext
  intro V
  simp only [Hom.comp_app]
  ext x
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
    Function.comp_apply]
  let x₀ : Γ((restrictFunctor j ⋙ restrictFunctor l).obj
      ((pushforward i).obj M), V) :=
    (Hom.app ((restrictFunctorComp l j).hom.app
      ((pushforward i).obj M)) V).hom x
  let x₁ : Γ((restrictFunctor l).obj
      ((pushforward g).obj ((restrictFunctor k).obj M)), V) :=
    (Hom.app ((restrictFunctor l).map
      (restrictPushforwardIsoOfOpenSquare i g k j hsq₁ hopen₁ M).hom) V).hom x₀
  let x₁' : Γ((restrictFunctor l).obj
      ((pushforward g).obj ((restrictFunctor k).obj M)), V) :=
    (M.presheaf.map (eqToHom (hopen₁ (l ''ᵁ V))).op).hom x₀
  have hx₁ : x₁ = x₁' :=
    restrictFunctor_map_restrictPushforwardIsoOfOpenSquare_hom_app_apply
      i g k j l hsq₁ hopen₁ M V x₀
  let e₂ := restrictPushforwardIsoOfOpenSquare
    g h m l hsq₂ hopen₂ ((restrictFunctor k).obj M)
  let e₃ := (pushforward h).map ((restrictFunctorComp m k).inv.app M)
  let x₂ : Γ((pushforward h).obj
      ((restrictFunctor k ⋙ restrictFunctor m).obj M), V) :=
    (Hom.app e₂.hom V).hom x₁'
  let x₂' : Γ((pushforward h).obj
      ((restrictFunctor k ⋙ restrictFunctor m).obj M), V) :=
    (((restrictFunctor k).obj M).presheaf.map
      (eqToHom (hopen₂ V)).op).hom x₁'
  have hx₂ : x₂ = x₂' :=
    restrictPushforwardIsoOfOpenSquare_hom_app_apply
      g h m l hsq₂ hopen₂ ((restrictFunctor k).obj M) V x₁'
  let x₃' : Γ((pushforward h).obj
      ((restrictFunctor (m ≫ k)).obj M), V) :=
    (M.presheaf.map (eqToHom (by simp)).op).hom x₂'
  have hx₃ : (Hom.app e₃ V).hom x₂' = x₃' := by
    dsimp [e₃, x₃']
    exact pushforward_map_restrictFunctorComp_inv_app_apply
      k m h M V x₂'
  let ep := restrictPushforwardIsoOfOpenSquare
    i h (m ≫ k) (l ≫ j) (by
      calc
        (h ≫ l) ≫ j = (m ≫ g) ≫ j :=
          congrArg (fun z ↦ z ≫ j) hsq₂
        _ = m ≫ (g ≫ j) := Category.assoc _ _ _
        _ = m ≫ (k ≫ i) := congrArg (fun z ↦ m ≫ z) hsq₁
        _ = (m ≫ k) ≫ i := (Category.assoc _ _ _).symm)
      hopen₃ M
  let xp : Γ((pushforward h).obj
      ((restrictFunctor (m ≫ k)).obj M), V) :=
    (Hom.app ep.hom V).hom x
  let xp' : Γ((pushforward h).obj
      ((restrictFunctor (m ≫ k)).obj M), V) :=
    (M.presheaf.map (eqToHom (hopen₃ V)).op).hom x
  have hxp : xp = xp' := by
    dsimp [xp, xp', ep]
    exact restrictPushforwardIsoOfOpenSquare_hom_app_apply
      i h (m ≫ k) (l ≫ j) _ hopen₃ M V x
  change (Hom.app e₃ V).hom ((Hom.app e₂.hom V).hom x₁) =
    (Hom.app ep.hom V).hom x
  calc
    (Hom.app e₃ V).hom ((Hom.app e₂.hom V).hom x₁) =
        (Hom.app e₃ V).hom ((Hom.app e₂.hom V).hom x₁') :=
      congrArg (fun z ↦ (Hom.app e₃ V).hom ((Hom.app e₂.hom V).hom z)) hx₁
    _ = (Hom.app e₃ V).hom x₂' :=
      congrArg (fun z ↦ (Hom.app e₃ V).hom z) hx₂
    _ = x₃' := hx₃
    _ = xp' := by
      dsimp [x₃', xp', x₂', x₁', x₀]
      dsimp [presheaf, PresheafOfModules.presheaf, restrictFunctor,
        pushforward, SheafOfModules.pushforward,
        PresheafOfModules.pushforward, PresheafOfModules.pushforward₀,
        PresheafOfModules.pushforward₀Obj,
        PresheafOfModules.restrictScalars,
        PresheafOfModules.restrictScalarsObj]
      change M.presheaf.map _
          (M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ x))) =
        M.presheaf.map _ x
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply,
        ← Functor.map_comp_apply]
      congr 2
    _ = (Hom.app ep.hom V).hom x := hxp.symm

end

end AlgebraicGeometry.Scheme.Modules
