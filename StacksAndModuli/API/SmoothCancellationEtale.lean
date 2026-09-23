module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Etale.Field

/-!
# Cancelling an etale base from a smooth composite

This file records the ring and scheme forms of the fact that if `X ⟶ Y ⟶ Z`
has smooth composite and `Y ⟶ Z` is etale, then `X ⟶ Y` is smooth.  The ring
proof combines cancellation for formal smoothness with finite-presentation
cancellation; the scheme proof globalizes it using affine locality.

## Main results

* `RingHom.Smooth.of_comp_of_etale`;
* `AlgebraicGeometry.Smooth.of_comp_of_etale`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace RingHom.Smooth

/-- If `R ⟶ S` is etale and `R ⟶ T` is smooth, then the compatible map
`S ⟶ T` is smooth. -/
theorem of_comp_of_etale
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T)
    (hcomp : (g.comp f).Smooth) (hf : f.Etale) : g.Smooth := by
  algebraize [f, g, g.comp f]
  let _ : Algebra.Etale R S := hf
  let _ : Algebra.Smooth R T := hcomp
  exact
    { formallySmooth :=
        (Algebra.FormallySmooth.iff_restrictScalars
          (R := R) (A := S) (B := T)).mp
            (inferInstance : Algebra.FormallySmooth R T)
      finitePresentation :=
        Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R S T }

end RingHom.Smooth

namespace AlgebraicGeometry.Smooth

/-- If `X ⟶ Y ⟶ Z` has smooth composite and `Y ⟶ Z` is etale, then
`X ⟶ Y` is smooth. -/
theorem of_comp_of_etale {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hcomp : Smooth (f ≫ g)) (hg : Etale g) : Smooth f := by
  let _ : IsZariskiLocalAtTarget
      (@_root_.AlgebraicGeometry.Smooth) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (@_root_.AlgebraicGeometry.Smooth) (Q := @RingHom.Smooth)
  let _ : IsZariskiLocalAtSource
      (@_root_.AlgebraicGeometry.Smooth) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
      (P := @_root_.AlgebraicGeometry.Smooth) (Q := @RingHom.Smooth)
  let _ : IsZariskiLocalAtTarget
      (@_root_.AlgebraicGeometry.Etale) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (@_root_.AlgebraicGeometry.Etale) (Q := @RingHom.Etale)
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := @_root_.AlgebraicGeometry.Smooth) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have hcomp' := IsZariskiLocalAtTarget.restrict hcomp U.1
    rw [morphismRestrict_comp] at hcomp'
    exact this (f := f ∣_ g ⁻¹ᵁ U.1) (g := g ∣_ U.1) hcomp'
      (IsZariskiLocalAtTarget.restrict hg U.1) inferInstance
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := @_root_.AlgebraicGeometry.Smooth) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have hcomp' :=
      HasRingHomProperty.comp_of_isOpenImmersion
        @_root_.AlgebraicGeometry.Smooth
        (f ⁻¹ᵁ U.1).ι (f ≫ g) hcomp
    rw [← morphismRestrict_ι_assoc] at hcomp'
    exact this (f := f ∣_ U.1) (g := U.1.ι ≫ g) hcomp'
      inferInstance inferInstance
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top
      (P := @_root_.AlgebraicGeometry.Smooth) _
      (iSup_affineOpens_eq_top X)]
    intro U
    have hcomp' := HasRingHomProperty.comp_of_isOpenImmersion
      @_root_.AlgebraicGeometry.Smooth U.1.ι (f ≫ g) hcomp
    rw [← Category.assoc] at hcomp'
    exact this (f := U.1.ι ≫ f) hcomp' inferInstance
  rw [HasRingHomProperty.iff_of_isAffine
    (P := @_root_.AlgebraicGeometry.Smooth)] at hcomp ⊢
  rw [HasRingHomProperty.iff_of_isAffine
    (P := @_root_.AlgebraicGeometry.Etale)] at hg
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at hcomp
  exact RingHom.Smooth.of_comp_of_etale g.appTop.hom f.appTop.hom hcomp hg

end AlgebraicGeometry.Smooth

end
