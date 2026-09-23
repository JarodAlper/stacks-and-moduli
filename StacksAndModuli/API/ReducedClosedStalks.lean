module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.JacobsonSpace

/-!
# Reduced schemes from closed stalks

On a Jacobson scheme, reducedness can be checked at the closed points.  The proof passes to
an affine cover and applies the ring-theoretic criterion checking reducedness after localization
at every maximal ideal.

## Main result

* `AlgebraicGeometry.Scheme.isReduced_of_isReduced_closed_stalk`: a Jacobson scheme is reduced
  if every stalk at a closed point is reduced.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A Jacobson scheme is reduced if its stalk at every closed point is reduced. -/
theorem isReduced_of_isReduced_closed_stalk (X : Scheme.{u}) [JacobsonSpace X]
    (h : ∀ x : X, IsClosed ({x} : Set X) →
      _root_.IsReduced (X.presheaf.stalk x)) : IsReduced X := by
  apply +allowSynthFailures @AlgebraicGeometry.IsReduced.of_openCover
    (X := X) (𝒰 := X.affineCover)
  intro i
  let Y := X.affineCover.X i
  let f : Y ⟶ X := X.affineCover.f i
  have : IsAffine Y := Scheme.isAffine_affineCover X i
  let _ : JacobsonSpace Y := JacobsonSpace.of_isOpenEmbedding f.isOpenEmbedding
  let hYred : _root_.IsReduced Γ(Y, ⊤) := by
    apply _root_.isReduced_ofLocalizationMaximal
    intro P hP
    let p : PrimeSpectrum Γ(Y, ⊤) := ⟨P, hP.isPrime⟩
    let y : (⊤ : Y.Opens) := (isAffineOpen_top Y).isoSpec.inv p
    have hpy : (isAffineOpen_top Y).primeIdealOf y = p := by
      change (isAffineOpen_top Y).isoSpec.hom ((isAffineOpen_top Y).isoSpec.inv p) = p
      have hcat := (isAffineOpen_top Y).isoSpec.inv_hom_id
      exact congrArg (fun g : Spec (CommRingCat.of Γ(Y, ⊤)) ⟶
        Spec (CommRingCat.of Γ(Y, ⊤)) ↦ g p) hcat
    have hy : IsClosed ({y} : Set (⊤ : Y.Opens)) := by
      have hpclosed : IsClosed ({p} : Set (Spec (CommRingCat.of Γ(Y, ⊤)))) :=
        p.isClosed_singleton_iff_isMaximal.mpr hP
      have hpre := hpclosed.preimage (isAffineOpen_top Y).isoSpec.hom.continuous
      rw [show ({y} : Set (⊤ : Y.Opens)) =
          (isAffineOpen_top Y).isoSpec.hom ⁻¹' ({p} : Set _) by
        ext z
        change (z = y) ↔ ((isAffineOpen_top Y).isoSpec.hom z = p)
        constructor
        · rintro rfl
          exact hpy
        · intro hz
          apply (isAffineOpen_top Y).isoSpec.hom.homeomorph.injective
          exact hz.trans hpy.symm]
      exact hpre
    have hyY : IsClosed ({(y : Y)} : Set Y) := by
      have hymem : y ∈ closedPoints (⊤ : Y.Opens) := hy
      have heq := (⊤ : Y.Opens).isOpenEmbedding'.preimage_closedPoints
      have hymem' : y ∈
          ((Subtype.val : (⊤ : Y.Opens) → Y) ⁻¹' closedPoints Y) := by
        rw [heq]
        exact hymem
      exact hymem'
    have hfy : IsClosed ({f y} : Set X) := by
      have hymem : (y : Y) ∈ closedPoints Y := hyY
      rw [← f.isOpenEmbedding.preimage_closedPoints] at hymem
      exact hymem
    let _ : _root_.IsReduced (X.presheaf.stalk (f y)) := h (f y) hfy
    let _ : _root_.IsReduced (Y.presheaf.stalk (y : Y)) :=
      _root_.isReduced_of_injective (asIso (f.stalkMap y)).inv.hom
        (asIso (f.stalkMap y)).symm.commRingCatIsoToRingEquiv.injective
    let _ : Algebra Γ(Y, ⊤) (Y.presheaf.stalk (y : Y)) :=
      TopCat.Presheaf.algebra_section_stalk Y.presheaf y
    have hloc : IsLocalization.AtPrime (Y.presheaf.stalk (y : Y)) P := by
      have := (isAffineOpen_top Y).isLocalization_stalk y
      rwa [hpy] at this
    let _ : IsLocalization.AtPrime (Y.presheaf.stalk (y : Y)) P := hloc
    let e : Localization.AtPrime P ≃ₐ[Γ(Y, ⊤)] Y.presheaf.stalk (y : Y) :=
      IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
        (Y.presheaf.stalk (y : Y))
    exact _root_.isReduced_of_injective e e.injective
  let _ : _root_.IsReduced Γ(Y, ⊤) := hYred
  exact isReduced_of_isAffine_isReduced Y

end AlgebraicGeometry.Scheme
