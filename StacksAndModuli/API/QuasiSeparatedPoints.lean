module

public import StacksAndModuli.API.FiberProductPresentationMap
public import StacksAndModuli.«Section4.8-Properness».«part4.8.1-definitions»

/-!
# Quasi-compact points of quasi-separated prestacks

A quasi-separated prestack has quasi-compact field-valued points.  The proof identifies
an affine base change of a field-valued point with a base change of the diagonal.  The
product of the two affine test schemes is replaced by its affine `Spec` model before
applying quasi-compactness of the diagonal.

## Main results

* `AlgebraicGeometry.IsAffine.prod`: a chosen binary product of affine schemes is affine.
* `AlgebraicGeometry.BasedFunctor.QuasiSeparated.hasQuasiCompactRepresentative`:
  every point of a prestack with quasi-compact diagonal has a quasi-compact
  field-valued representative.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits
open CategoryTheory.BasedCategory

universe vY uY u

namespace AlgebraicGeometry

/-- A chosen binary product of affine schemes is affine. -/
theorem IsAffine.prod (X Y : Scheme.{u}) [IsAffine X] [IsAffine Y] :
    IsAffine (X ⨯ Y) := by
  let _ : IsAffineHom (terminal.from X) := inferInstance
  let _ : IsAffine
      (pullback (terminal.from X) (terminal.from Y)) := inferInstance
  exact IsAffine.of_isIso (prodIsoPullback X Y).hom

namespace BasedFunctor.QuasiSeparated

variable {Y : BasedCategory.{vY, uY} Scheme.{u}}
  [Y.p.IsFiberedInGroupoids]

/-- Every point of a prestack whose diagonal is quasi-compact has a field-valued
representative which is quasi-compact after every affine base change. -/
theorem hasQuasiCompactRepresentative
    (hY : BasedFunctor.QuasiSeparated Y.toBase) :
    ∀ y : BasedCategory.pointSpace Y,
      BasedCategory.HasQuasiCompactRepresentative y := by
  intro y
  induction y using BasedCategory.pointSpace.ind with
  | _ p =>
      refine ⟨p, rfl, ?_⟩
      intro B g
      let T := Spec (CommRingCat.of p.carrier) ⨯ Spec B
      let _ : _root_.AlgebraicGeometry.IsAffine T :=
        _root_.AlgebraicGeometry.IsAffine.prod _ _
      let E₀ := overBasedProdComparison
        (Spec (CommRingCat.of p.carrier)) (Spec B)
      let I := overBased.map T.isoSpec.inv
      let H := E₀.comp (prodMap p.hom g)
      have hI : I.toFunctor.IsEquivalence := by
        change (Over.map T.isoSpec.inv).IsEquivalence
        infer_instance
      let H' := I.comp H
      have hsource : BasedCategory.IsQuasiCompact
          (fiberProduct (diag Y) H') := hY.1 Γ(T, ⊤) H'
      let E₁ := fiberProductRightMap (diag Y) H I
      have hE₁ : E₁.toFunctor.IsEquivalence :=
        isEquivalence_fiberProductRightMap (diag Y) H I
      have hmiddle : BasedCategory.IsQuasiCompact
          (fiberProduct (diag Y) H) :=
        BasedFunctor.isQuasiCompact_of_equivalence E₁ hE₁ hsource
      let E₂ := overBasedPairDiagonalFiberComparison p.hom g
      exact BasedFunctor.isQuasiCompact_of_equivalence E₂
        (isEquivalence_overBasedPairDiagonalFiberComparison p.hom g) hmiddle

end BasedFunctor.QuasiSeparated

end AlgebraicGeometry
