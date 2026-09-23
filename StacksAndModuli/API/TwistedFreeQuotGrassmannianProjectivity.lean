module

public import StacksAndModuli.API.FreeGrassmannianImmersion
public import StacksAndModuli.API.ProjectiveDVRQuotientClosedFiberSerre

/-!
# Projectivity from the twisted-free Quot Grassmannian immersion

This file composes the exact quasi-projective input isolated by
`TwistedFreeQuotHasFreeGrassmannianImmersion` with the sorry-free DVR restriction
theorems.  It deliberately constructs the representing object from the
free-Grassmannian immersion and applies the DVR projectivity criterion to that same
object, without using the independently recorded quasi-projectivity theorem in §2.4.

For arbitrary relative projective dimension, the only additional input is uniform
scheme-level Serre vanishing over DVRs.  In dimension zero that input is already proved,
so the free-Grassmannian immersion alone implies projectivity.

Main declarations:

* `AlgebraicGeometry.Scheme.
    exists_quotFunctorP_representableBy_isHProjective_of_grassmannianImmersion`;
* `AlgebraicGeometry.Scheme.
    exists_quotFunctorP_representableBy_isHProjective_of_grassmannianImmersion_of_serre`;
* `AlgebraicGeometry.Scheme.
    exists_quotFunctorP_representableBy_isHProjective_zero_of_grassmannianImmersion`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A free-Grassmannian immersion for the finite twisted-free fixed-polynomial Quot
functor produces a projective representative.  The required DVR restriction
bijectivity is supplied by the unconditional closed-fibre Hilbert-polynomial theorem. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_of_grassmannianImmersion
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (himm : TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP
        (projectiveSpaceOverTwistedFree n S l r) P).RepresentableBy Q) ∧
      IsHProjective Q.hom := by
  obtain ⟨Q, ⟨hrep⟩, N, ι, hι, hcomp⟩ :=
    exists_twistedFreeQuot_representableBy_immersion_projectiveSpace
      n S l r P himm
  have hrep' :
      (quotFunctorP
        (projectiveSpaceOverTwistedFree n S l r) P).RepresentableBy Q := by
    simpa only [projectiveSpaceOverTwistedFree] using hrep
  refine ⟨Q, ⟨hrep'⟩,
    isHProjective_of_representableBy_dvr_map_bijective
      hrep' N ι hι hcomp ?_⟩
  intro sq hdvr
  let _ : IsDiscreteValuationRing sq.R := hdvr
  exact quotFunctorP_map_bijective_isFractionRing_of_closedFiberHilbertPolynomial
    n S (projectiveSpaceOverTwistedFree n S l r) P
      (canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_twistedFree
        n S l r P) sq.R sq.K sq.i₂

/-- A free-Grassmannian immersion for the finite twisted-free fixed-polynomial Quot
functor, together with scheme-level Serre vanishing over every DVR, produces a
projective representative.  The representative and its projective-space immersion are
constructed directly from the Grassmannian input. -/
theorem
    exists_quotFunctorP_representableBy_isHProjective_of_grassmannianImmersion_of_serre
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (himm : TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P)
    (hserre : ∀ (R : Type u) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R],
        ProjectiveSpaceHasSerreVanishing n (Spec (.of R))) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP
        (projectiveSpaceOverTwistedFree n S l r) P).RepresentableBy Q) ∧
      IsHProjective Q.hom := by
  obtain ⟨Q, ⟨hrep⟩, N, ι, hι, hcomp⟩ :=
    exists_twistedFreeQuot_representableBy_immersion_projectiveSpace
      n S l r P himm
  have hrep' :
      (quotFunctorP
        (projectiveSpaceOverTwistedFree n S l r) P).RepresentableBy Q := by
    simpa only [projectiveSpaceOverTwistedFree] using hrep
  refine ⟨Q, ⟨hrep'⟩,
    isHProjective_of_representableBy_dvr_map_bijective
      hrep' N ι hι hcomp ?_⟩
  intro sq hdvr
  let _ : IsDiscreteValuationRing sq.R := hdvr
  exact quotFunctorP_map_bijective_isFractionRing_of_serre
    n S l r P hserre sq.R sq.K sq.i₂

/-- For relative `P⁰`, a free-Grassmannian immersion for the finite twisted-free
fixed-polynomial Quot functor already produces a projective representative.  The DVR
restriction input is unconditional in dimension zero. -/
theorem exists_quotFunctorP_representableBy_isHProjective_zero_of_grassmannianImmersion
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (himm : TwistedFreeQuotHasFreeGrassmannianImmersion 0 S l r P) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP
        (projectiveSpaceOverTwistedFree 0 S l r) P).RepresentableBy Q) ∧
      IsHProjective Q.hom := by
  obtain ⟨Q, ⟨hrep⟩, N, ι, hι, hcomp⟩ :=
    exists_twistedFreeQuot_representableBy_immersion_projectiveSpace
      0 S l r P himm
  have hrep' :
      (quotFunctorP
        (projectiveSpaceOverTwistedFree 0 S l r) P).RepresentableBy Q := by
    simpa only [projectiveSpaceOverTwistedFree] using hrep
  refine ⟨Q, ⟨hrep'⟩,
    isHProjective_of_representableBy_dvr_map_bijective
      hrep' N ι hι hcomp ?_⟩
  intro sq hdvr
  let _ : IsDiscreteValuationRing sq.R := hdvr
  exact quotFunctorP_map_bijective_isFractionRing_zero
    S l r P sq.R sq.K sq.i₂

end AlgebraicGeometry.Scheme

end
