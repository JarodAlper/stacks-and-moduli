module

public import StacksAndModuli.API.ProjectiveDVRQuotientPullbackSerre
public import StacksAndModuli.API.ProjectiveSpaceZeroLocalCohomology
public import StacksAndModuli.«Section2.4-Projectivity».«part2.4.1-valuative-criteria»

/-!
# Serre vanishing and the closed-fibre condition for projective Quot

This file composes the normalized DVR Quot-pullback calculation with the exact
closed-fibre predicate isolated in §2.4.  Scheme-level Serre vanishing on projective
space over DVRs is the only remaining geometric input: all quotient representatives,
kernel coherence, flatness, and field-extension comparisons are constructed internally.

`canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_of_serre` itself now lives in
`Section2.4-Projectivity/part2.4.1-valuative-criteria.lean`, next to the predicate it is about
and upstream of the theorem that consumes it.

Main declarations:

* `AlgebraicGeometry.Scheme.
    quotFunctorP_map_bijective_isFractionRing_of_serre`;
* `AlgebraicGeometry.Scheme.
    exists_quotFunctorP_representableBy_isHProjective_of_serre`;
* the corresponding dimension-zero declarations ending in `_zero`, where the
  Serre hypothesis is discharged over every DVR.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

open Modules.QuotientPullbackData

-- `canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_of_serre` — scheme-level
-- Serre vanishing on projective space over every DVR forces the canonical twisted-free
-- extension of each generic fixed-polynomial Quot point to retain that polynomial on its
-- closed fibre — now lives in
-- `Section2.4-Projectivity/part2.4.1-valuative-criteria.lean`, next to the predicate it is
-- about and upstream of the theorem that consumes it.


/-- Under scheme-level Serre vanishing over DVRs, restriction from a DVR to
any chosen fraction field is bijective on fixed-polynomial twisted-free Quot
points. -/
theorem quotFunctorP_map_bijective_isFractionRing_of_serre
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hserre : ∀ (R : Type u) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R],
        ProjectiveSpaceHasSerreVanishing n (Spec (.of R)))
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (σ : Spec (.of R) ⟶ S) :
    Function.Bijective
      ((quotFunctorP (projectiveSpaceOverTwistedFree n S l r) P).map
        (Quiver.Hom.op (Over.homMk
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl :
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) ⟶
            Over.mk σ))) :=
  quotFunctorP_map_bijective_isFractionRing_of_closedFiberHilbertPolynomial
    n S (projectiveSpaceOverTwistedFree n S l r) P
      (canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_of_serre
        n S l r P hserre) R K σ

/-- If scheme-level Serre vanishing holds on projective space over every DVR,
then fixed-polynomial Quot for a finite twisted-free source has a projective
representing scheme. -/
theorem exists_quotFunctorP_representableBy_isHProjective_of_serre
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (hserre : ∀ (R : Type u) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R],
        ProjectiveSpaceHasSerreVanishing n (Spec (.of R))) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP
        (projectiveSpaceOverTwistedFree n S l r) P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  exists_quotFunctorP_representableBy_isHProjective_of_closedFiberHilbertPolynomial
    n S l r P
      (canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_of_serre
        n S l r P hserre)

/-- On relative zero-dimensional projective space, every canonical twisted-free
DVR Quot extension retains its generic Hilbert polynomial on the closed fibre.

There is no remaining cohomological hypothesis: a DVR is local, and all positive
cohomology of every abelian sheaf on relative `P⁰` over a local ring vanishes. -/
theorem canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_zero
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ) :
    CanonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial 0 S
      (projectiveSpaceOverTwistedFree 0 S l r) P := by
  apply canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_of_serre
  intro R _ _ _
  exact projectiveSpaceHasSerreVanishing_zero_spec_of_isLocalRing R

/-- Restriction from a DVR to any chosen fraction field is bijective on
fixed-polynomial twisted-free Quot points over relative `P⁰`, without an
additional Serre-vanishing hypothesis. -/
theorem quotFunctorP_map_bijective_isFractionRing_zero
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (σ : Spec (.of R) ⟶ S) :
    Function.Bijective
      ((quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r) P).map
        (Quiver.Hom.op (Over.homMk
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl :
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) ⟶
            Over.mk σ))) :=
  quotFunctorP_map_bijective_isFractionRing_of_closedFiberHilbertPolynomial
    0 S (projectiveSpaceOverTwistedFree 0 S l r) P
      (canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_zero
        S l r P) R K σ

/-- Fixed-polynomial twisted-free Quot on relative `P⁰` satisfies the complete
valuative projectivity endgame.  The closed-fibre input is unconditional; this
corollary still uses the independently recorded quasi-projective representation
theorem. -/
theorem exists_quotFunctorP_representableBy_isHProjective_zero
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP
        (projectiveSpaceOverTwistedFree 0 S l r) P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  exists_quotFunctorP_representableBy_isHProjective_of_closedFiberHilbertPolynomial
    0 S l r P
      (canonicalDVRQuotientExtensionsHaveClosedFiberHilbertPolynomial_zero
        S l r P)

end AlgebraicGeometry.Scheme

end
