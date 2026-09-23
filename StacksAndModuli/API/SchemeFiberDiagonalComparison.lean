module

public import StacksAndModuli.API.FiberProductIdentity
public import StacksAndModuli.API.PresentationBaseChange
public import StacksAndModuli.API.RepresentableWithCharts
public import StacksAndModuli.«Section4.3-Properties».«part4.3.3-separation-properties»

/-!
# Diagonals of morphisms between representable prestacks

The relative diagonal of the morphism of representable prestacks classified by a
scheme morphism `f : U ⟶ T` agrees, through the canonical representation of the
scheme pullback, with the representable-prestack morphism classified by the ordinary
diagonal `U ⟶ U ×_T U`.  Consequently, properness of the former in every scheme
base change is equivalent to separatedness of `f`.

This is the scheme-model endpoint needed when comparing the relative diagonal of a
representable morphism of prestacks with the ordinary diagonals of its scheme-valued
fibers.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits AlgebraicGeometry
open CategoryTheory.BasedCategory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

namespace AlgebraicGeometry.BasedFunctor

/-- For a morphism between representable prestacks, relative representability with a
base-change-stable property is equivalent to that property for the classified scheme
morphism. -/
theorem relativelyRepresentableWith_iff_overHom {U T : Scheme.{u}}
    (H : overBased U ⥤ᵇ overBased T) {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.IsStableUnderBaseChange] :
    H.RelativelyRepresentableWith P ↔ P H.overHom := by
  constructor
  · intro h
    let E := fiberProductFstIdInv H
    have hE : E.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductFstIdInv H
    have hP := h.2 T (CategoryTheory.BasedFunctor.id (overBased T)) U E hE
    rw [show E.comp (fiberProductSnd H
        (CategoryTheory.BasedFunctor.id (overBased T))) = H by
      simp only [E, fiberProductFstIdInv_comp_snd]] at hP
    exact hP
  · exact relativelyRepresentableWith_of_overHom H

/-- The ordinary scheme diagonal followed by the canonical representation of the
scheme pullback is 2-isomorphic to the relative diagonal of the corresponding map of
representable prestacks. -/
noncomputable def overBasedMapDiagonalIso {U T : Scheme.{u}} (f : U ⟶ T) :
    (overBased.map (pullback.diagonal f)).comp
        (overBasedPullbackLift f f) ≅
      (overBased.map f).diag :=
  BasedNatIso.mkNatIso
    (NatIso.ofComponents
      (fun w ↦ by
        let e₁ :
            (((overBased.map (pullback.diagonal f)).comp
              (overBasedPullbackLift f f)).obj w).fst ≅
              ((overBased.map f).diag.obj w).fst :=
          Over.isoMk (Iso.refl _) (by
            change w.hom = (w.hom ≫ pullback.diagonal f) ≫ pullback.fst f f
            rw [Category.assoc, pullback.diagonal_fst, Category.comp_id])
        let e₂ :
            (((overBased.map (pullback.diagonal f)).comp
              (overBasedPullbackLift f f)).obj w).snd ≅
              ((overBased.map f).diag.obj w).snd :=
          Over.isoMk (Iso.refl _) (by
            change w.hom = (w.hom ≫ pullback.diagonal f) ≫ pullback.snd f f
            rw [Category.assoc, pullback.diagonal_snd, Category.comp_id])
        apply FiberProductObj.isoMk e₁ e₂
        · let R : Scheme.{u} := w.left
          have h₁left : IsHomLift (Functor.id Scheme) (𝟙 R) e₁.hom.left := by
            dsimp [e₁, R]
            exact IsHomLift.id rfl
          have h₂left : IsHomLift (Functor.id Scheme) (𝟙 R) e₂.hom.left := by
            dsimp [e₂, R]
            exact IsHomLift.id rfl
          exact isHomLift_map_of_common_lift (𝟙 R) e₁.hom e₂.hom
            (over_isHomLift_of_left (𝟙 R) e₁.hom h₁left)
            (over_isHomLift_of_left (𝟙 R) e₂.hom h₂left)
        · apply Over.OverMorphism.ext
          rfl)
      (fun {w w'} q ↦ by
        apply FiberProductHom.ext
        · apply Over.OverMorphism.ext
          rfl
        · apply Over.OverMorphism.ext
          rfl))
    (fun w ↦ by
      apply FiberProductHom.isHomLift_of_fst _ (F := overBased.map f)
        (G := overBased.map f) (f := 𝟙 ((overBased U).p.obj w))
      apply over_isHomLift_of_left (𝟙 w.left)
      exact IsHomLift.id rfl)

/-- Properness of the relative diagonal of a morphism between representable prestacks
is equivalent to separatedness of its classified scheme morphism. -/
theorem relativelyRepresentableWith_proper_diag_iff_isSeparated
    {U T : Scheme.{u}} (f : U ⟶ T) :
    (overBased.map f).diag.RelativelyRepresentableWith
        (@IsProper : MorphismProperty Scheme.{u}) ↔
      IsSeparated f := by
  let d := pullback.diagonal f
  let L := overBasedPullbackLift f f
  have hL : L.toFunctor.IsEquivalence :=
    isEquivalence_overBasedPullbackLift f f
  have hd :
      (overBased.map d).RelativelyRepresentableWith
          (@IsProper : MorphismProperty Scheme.{u}) ↔ IsProper d := by
    simpa only [CategoryTheory.BasedFunctor.overHom_map] using
      (relativelyRepresentableWith_iff_overHom (overBased.map d)
        (P := (@IsProper : MorphismProperty Scheme.{u})))
  have hproperSep : IsProper d ↔ IsSeparated f :=
    (Scheme.Hom.isClosedImmersion_diagonal_iff_isProper f).symm.trans
      (isSeparated_iff f).symm
  have hdiagMap :
      (overBased.map f).diag.RelativelyRepresentableWith
          (@IsProper : MorphismProperty Scheme.{u}) ↔
        (overBased.map d).RelativelyRepresentableWith
          (@IsProper : MorphismProperty Scheme.{u}) := by
    constructor
    · intro h
      have hc : ((overBased.map d).comp L).RelativelyRepresentableWith
          (@IsProper : MorphismProperty Scheme.{u}) :=
        h.of_iso (overBasedMapDiagonalIso f).symm
      exact hc.of_comp_target_isEquivalence hL
    · intro h
      let _ : L.toFunctor.IsEquivalence := hL
      exact (h.comp_target_isEquivalence L).of_iso (overBasedMapDiagonalIso f)
  exact hdiagMap.trans (hd.trans hproperSep)

end AlgebraicGeometry.BasedFunctor
