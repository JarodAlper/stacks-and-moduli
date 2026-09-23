module

public import StacksAndModuli.«Section4.3-Properties».«part4.3.4-topological-space»

/-!
# Closed maps on point spaces of represented prestacks

The point space of `overBased X` is homeomorphic to the underlying topological space of
the scheme `X`.  This file makes the resulting closed-map comparison functorial and then
transports it through an arbitrary equivalence from a representable prestack.

## Main results

* `BasedFunctor.isClosedMap_mapPoints_overBased_map_iff`
* `BasedFunctor.isClosedMap_mapPoints_iff_of_scheme_representation`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v u' u

namespace AlgebraicGeometry.BasedFunctor

/-- A morphism of schemes is a closed map exactly when the induced morphism between its
representable prestacks is closed on point spaces. -/
theorem isClosedMap_mapPoints_overBased_map_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsClosedMap (mapPoints (overBased.map f)) ↔ IsClosedMap f := by
  have hX : IsHomeomorph X.toPointSpace :=
    ⟨BasedCategory.quotientMapOfPresentation.continuous_toPointSpace X,
      X.isOpenMap_toPointSpace, X.bijective_toPointSpace⟩
  have hY : IsHomeomorph Y.toPointSpace :=
    ⟨BasedCategory.quotientMapOfPresentation.continuous_toPointSpace Y,
      Y.isOpenMap_toPointSpace, Y.bijective_toPointSpace⟩
  let eX := hX.homeomorph X.toPointSpace
  let eY := hY.homeomorph Y.toPointSpace
  have hmap : mapPoints (overBased.map f) = eY ∘ f.base ∘ eX.symm := by
    funext z
    change mapPoints (overBased.map f) z = eY (f.base (eX.symm z))
    calc
      mapPoints (overBased.map f) z =
          mapPoints (overBased.map f) (eX (eX.symm z)) :=
        congrArg _ (eX.apply_symm_apply z).symm
      _ = Y.toPointSpace (f.base (eX.symm z)) := by
        simpa only [eX, IsHomeomorph.homeomorph_apply] using
          BasedCategory.quotientMapOfPresentation.mapPoints_overBased_map_toPointSpace
            f (eX.symm z)
      _ = eY (f.base (eX.symm z)) := by
        simp only [eY, IsHomeomorph.homeomorph_apply]
  constructor
  · intro h
    have hmap' : f.base = eY.symm ∘ mapPoints (overBased.map f) ∘ eX := by
      funext x
      change f.base x = eY.symm (mapPoints (overBased.map f) (eX x))
      calc
        f.base x = eY.symm (eY (f.base x)) := (eY.symm_apply_apply _).symm
        _ = eY.symm (Y.toPointSpace (f.base x)) := by
          simp only [eY, IsHomeomorph.homeomorph_apply]
        _ = eY.symm (mapPoints (overBased.map f) (X.toPointSpace x)) := by
          rw [BasedCategory.quotientMapOfPresentation.mapPoints_overBased_map_toPointSpace]
        _ = eY.symm (mapPoints (overBased.map f) (eX x)) := by
          simp only [eX, IsHomeomorph.homeomorph_apply]
    rw [hmap']
    exact eY.symm.isClosedMap.comp (h.comp eX.isClosedMap)
  · intro h
    rw [hmap]
    exact eY.isClosedMap.comp (h.comp eX.symm.isClosedMap)

/-- If a prestack is represented by a scheme, a morphism from that prestack is closed on
point spaces exactly when the induced structural morphism of schemes is closed. -/
theorem isClosedMap_mapPoints_iff_of_scheme_representation
    {Zcat : BasedCategory.{v, u'} Scheme.{u}} [Zcat.p.IsFiberedInGroupoids]
    {U T : Scheme.{u}} (E : overBased U ⥤ᵇ Zcat)
    (hE : E.toFunctor.IsEquivalence) (q : Zcat ⥤ᵇ overBased T) :
    IsClosedMap (mapPoints q) ↔ IsClosedMap (E.comp q).overHom := by
  let _ : E.toFunctor.IsEquivalence := hE
  let f := (E.comp q).overHom
  obtain ⟨e⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map (E.comp q)
  have heq : mapPoints (E.comp q) = mapPoints (overBased.map f) :=
    BasedCategory.quotientMapOfPresentation.mapPoints_eq_of_iso e
  constructor
  · intro hq
    have hcomp : IsClosedMap (mapPoints (E.comp q)) := by
      rw [show mapPoints (E.comp q) = mapPoints q ∘ mapPoints E by
        funext z
        exact BasedCategory.quotientMapOfPresentation.mapPoints_comp E q z]
      exact hq.comp (isClosedMap_mapPoints_of_isEquivalence E hE)
    rw [heq] at hcomp
    exact (isClosedMap_mapPoints_overBased_map_iff f).mp hcomp
  · intro hf
    have hcomp : IsClosedMap (mapPoints (E.comp q)) := by
      rw [heq]
      exact (isClosedMap_mapPoints_overBased_map_iff f).mpr hf
    obtain ⟨I, ⟨α⟩, ⟨β⟩⟩ :=
      CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor E
    have hI : I.toFunctor.IsEquivalence :=
      Functor.IsEquivalence.mk' E.toFunctor
        ((BasedNatTrans.forgetful _ _).mapIso β).symm
        ((BasedNatTrans.forgetful _ _).mapIso α)
    have hIq : IsClosedMap (mapPoints (I.comp (E.comp q))) := by
      rw [show mapPoints (I.comp (E.comp q)) =
          mapPoints (E.comp q) ∘ mapPoints I by
        funext z
        exact BasedCategory.quotientMapOfPresentation.mapPoints_comp I (E.comp q) z]
      exact hcomp.comp (isClosedMap_mapPoints_of_isEquivalence I hI)
    have eiq : I.comp (E.comp q) ≅ q :=
      (eqToIso (CategoryTheory.BasedFunctor.comp_assoc I E q)).trans
        ((BasedCategory.isoWhiskerRight β q).trans
          (eqToIso (CategoryTheory.BasedFunctor.id_comp q)))
    rw [BasedCategory.quotientMapOfPresentation.mapPoints_eq_of_iso eiq] at hIq
    exact hIq

end AlgebraicGeometry.BasedFunctor
