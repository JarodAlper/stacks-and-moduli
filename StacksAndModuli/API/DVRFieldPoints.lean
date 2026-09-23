module

public import StacksAndModuli.API.DVRGenericFiber
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Field-valued points of the spectrum of a DVR

For a discrete valuation ring `R`, every field-valued point of `Spec R` lies either over
the generic point or over the unique closed point.  In scheme-theoretic form, every map
`Spec K ⟶ Spec R` factors either through the generic open immersion
`Spec Frac(R) ⟶ Spec R` or through the residue-field point at the closed point.

This is the reduction used in the fixed-Hilbert-polynomial refinement of the valuative
criterion for Quot: the generic alternative is controlled by the given generic family,
so constancy of the Hilbert polynomial only has to be checked on the closed fibre.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace IsDiscreteValuationRing

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Every prime of a discrete valuation ring is either the generic point or its unique
closed point. -/
theorem prime_eq_bot_or_closedPoint (x : PrimeSpectrum R) :
    x.asIdeal = ⊥ ∨ x = IsLocalRing.closedPoint R := by
  by_cases hx : x.asIdeal = ⊥
  · exact Or.inl hx
  · right
    have hmax : x.asIdeal.IsMaximal := by
      haveI := x.2
      exact IsPrime.to_maximal_ideal hx
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hmax)

/-- Every field-valued point of the spectrum of a DVR factors either through its generic
open point or through its closed residue-field point. -/
theorem fieldPoint_factorization
    (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)) :
    (∃ t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of (FractionRing R)),
      t ≫ Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) = s) ∨
    (∃ t : Spec (CommRingCat.of K) ⟶
        Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)),
      t ≫ (Spec (CommRingCat.of R)).fromSpecResidueField
        (IsLocalRing.closedPoint R) = s) := by
  let j : Spec (CommRingCat.of (FractionRing R)) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  haveI : IsOpenImmersion j :=
    IsDiscreteValuationRing.isOpenImmersion_specMap_fractionRing (R := R) (FractionRing R)
  let x : Spec (CommRingCat.of R) := s (IsLocalRing.closedPoint K)
  rcases prime_eq_bot_or_closedPoint x with hx | hx
  · left
    have hsrange : Set.range s ⊆ Set.range j := by
      rintro y ⟨z, rfl⟩
      obtain rfl : z = IsLocalRing.closedPoint K := Subsingleton.elim _ _
      change x ∈ j.opensRange
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
      rw [IsDiscreteValuationRing.opensRange_specMap_fractionRing hϖ (FractionRing R)]
      rw [AlgebraicGeometry.basicOpen_eq_of_affine]
      change ϖ ∉ x.asIdeal
      rw [hx]
      exact fun h ↦ hϖ.ne_zero (Ideal.mem_bot.mp h)
    exact ⟨IsOpenImmersion.lift j s hsrange, IsOpenImmersion.lift_fac j s hsrange⟩
  · right
    have hy : s (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint R := by
      simpa [x] using hx
    let f := Scheme.descResidueField (Scheme.stalkClosedPointTo s)
    let t : Spec (CommRingCat.of K) ⟶
        Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) :=
      Spec.map f ≫
        Spec.map ((Spec (CommRingCat.of R)).residueFieldCongr hy.symm).hom
    refine ⟨t, ?_⟩
    calc
      t ≫ (Spec (CommRingCat.of R)).fromSpecResidueField
          (IsLocalRing.closedPoint R) =
          Spec.map f ≫ (Spec (CommRingCat.of R)).fromSpecResidueField
            (s (IsLocalRing.closedPoint K)) := by
              dsimp only [t]
              rw [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField]
      _ = s := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K _ s

end IsDiscreteValuationRing
