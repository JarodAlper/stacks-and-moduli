module

public import StacksAndModuli.API.PrincipalClosedFiberCokernel
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The principal and residue-field models of a DVR's closed fibre

If `ϖ` is a uniformizer of a discrete valuation ring `R`, then
`R/(ϖ)` is canonically the residue field of `R`.  Scheme-theoretically, the
corresponding map from `Spec (R/(ϖ))` agrees, through this canonical
identification, with Mathlib's map from the residue field of the closed point
of `Spec R`.

This file connects the principal closed-fibre model used by
`PrincipalClosedFiberCokernel` to the canonical residue-field model used in
Chapter 2.

Main declarations:

* `AlgebraicGeometry.principalClosedFiberRingEquivSchemeResidueField`;
* `AlgebraicGeometry.principalClosedFiberRingIsoSchemeResidueField`;
* `AlgebraicGeometry.principalClosedFiberRingHom_comp_schemeResidueFieldIso_hom`;
* `AlgebraicGeometry.SpecMap_schemeResidueFieldIso_hom_comp_principalClosedFiber`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]

/-- For a uniformizer `ϖ` of a DVR `R`, the quotient `R/(ϖ)` is canonically
the scheme-theoretic residue field at the closed point of `Spec R`.

The first factor replaces `(ϖ)` by the maximal ideal.  The second transports
residue fields through the canonical identification of the stalk at the
closed point with `R`. -/
noncomputable def principalClosedFiberRingEquivSchemeResidueField
    {ϖ : R} (hϖ : Irreducible ϖ) :
    principalClosedFiberRing (R := CommRingCat.of R) ϖ ≃+*
      (Spec (CommRingCat.of R)).residueField
        (IsLocalRing.closedPoint (CommRingCat.of R)) := by
  let _ : IsLocalRing
      ((Spec (CommRingCat.of R)).presheaf.stalk
        (IsLocalRing.closedPoint (CommRingCat.of R))) :=
    (Spec (CommRingCat.of R)).toLocallyRingedSpace.isLocalRing _
  exact (Ideal.quotEquivOfEq hϖ.maximalIdeal_eq.symm).trans
    (IsLocalRing.ResidueField.mapEquiv
      (stalkClosedPointIso
        (CommRingCat.of R)).commRingCatIsoToRingEquiv).symm

/-- The categorical commutative-ring isomorphism underlying
`principalClosedFiberRingEquivSchemeResidueField`. -/
noncomputable def principalClosedFiberRingIsoSchemeResidueField
    {ϖ : R} (hϖ : Irreducible ϖ) :
    principalClosedFiberRing (R := CommRingCat.of R) ϖ ≅
      (Spec (CommRingCat.of R)).residueField
        (IsLocalRing.closedPoint (CommRingCat.of R)) :=
  (principalClosedFiberRingEquivSchemeResidueField hϖ).toCommRingCatIso

/-- The quotient map `R → R/(ϖ)`, followed by the canonical residue-field
identification, is the canonical ring map from `R` to the scheme-theoretic
residue field at the closed point of `Spec R`. -/
@[reassoc]
lemma principalClosedFiberRingHom_comp_schemeResidueFieldIso_hom
    {ϖ : R} (hϖ : Irreducible ϖ) :
    principalClosedFiberRingHom (R := CommRingCat.of R) ϖ ≫
        (principalClosedFiberRingIsoSchemeResidueField hϖ).hom =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec (CommRingCat.of R)).presheaf.germ ⊤
          (IsLocalRing.closedPoint (CommRingCat.of R)) trivial ≫
        (Spec (CommRingCat.of R)).residue
          (IsLocalRing.closedPoint (CommRingCat.of R)) := by
  let _ : IsLocalRing
      ((Spec (CommRingCat.of R)).presheaf.stalk
        (IsLocalRing.closedPoint (CommRingCat.of R))) :=
    (Spec (CommRingCat.of R)).toLocallyRingedSpace.isLocalRing _
  let e :=
    (stalkClosedPointIso
      (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let _ : IsLocalHom (e.symm : R →+*
      (Spec (CommRingCat.of R)).presheaf.stalk
        (IsLocalRing.closedPoint (CommRingCat.of R))) :=
    inferInstance
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change IsLocalRing.ResidueField.map
      (e.symm : R →+*
        (Spec (CommRingCat.of R)).presheaf.stalk
          (IsLocalRing.closedPoint (CommRingCat.of R)))
        (IsLocalRing.residue R r) = _
  rw [IsLocalRing.ResidueField.map_residue]
  have he : (stalkClosedPointIso (CommRingCat.of R)).inv =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec (CommRingCat.of R)).presheaf.germ ⊤
          (IsLocalRing.closedPoint (CommRingCat.of R)) trivial := by
    rw [stalkClosedPointIso_inv]
    rfl
  change IsLocalRing.residue _
      ((stalkClosedPointIso (CommRingCat.of R)).inv.hom r) = _
  rw [he]
  rfl

/-- On spectra, the principal closed-fibre map agrees with the canonical map
from the scheme-theoretic residue field of the closed point. -/
@[reassoc]
lemma SpecMap_schemeResidueFieldIso_hom_comp_principalClosedFiber
    {ϖ : R} (hϖ : Irreducible ϖ) :
    Spec.map (principalClosedFiberRingIsoSchemeResidueField hϖ).hom ≫
        Spec.map
          (principalClosedFiberRingHom (R := CommRingCat.of R) ϖ) =
      (Spec (CommRingCat.of R)).fromSpecResidueField
        (IsLocalRing.closedPoint (CommRingCat.of R)) := by
  rw [← Spec.map_comp,
    principalClosedFiberRingHom_comp_schemeResidueFieldIso_hom hϖ]
  unfold Scheme.fromSpecResidueField
  rw [Spec.fromSpecStalk_eq (CommRingCat.of R)
    (IsLocalRing.closedPoint (CommRingCat.of R))]
  rw [← Spec.map_comp]
  simp only [Category.assoc]

end AlgebraicGeometry

end
