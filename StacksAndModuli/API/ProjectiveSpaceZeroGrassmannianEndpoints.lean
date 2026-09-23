module

public import StacksAndModuli.API.ProjectiveHilbertGrassmannian
public import StacksAndModuli.API.ProjectiveSpaceZeroGrassmannianImmersion
public import StacksAndModuli.API.QuotPresentationGrassmannianProjectivity

/-!
# Projective-zero Grassmannian endpoints

The unconditional projective-zero Quot--Grassmannian immersion is threaded here through
the general categorical endpoints for quasi-projectivity, projectivity, Hilbert schemes,
and descent along a presentation of the ambient sheaf.

For the finite twisted-free ambient sheaf, no input remains.  For a general finitely
presented quasicoherent ambient sheaf, the only remaining input is the universal closed
zero locus for the kernel of a chosen twisted-free presentation (or, more concretely,
compatible affine finite-free models producing that zero locus).

Main declarations:

* `AlgebraicGeometry.Scheme.
  exists_quotFunctorP_zero_representableBy_isHQuasiProjective`;
* `AlgebraicGeometry.Scheme.
  exists_quotFunctorP_zero_representableBy_isHProjective_via_grassmannian`;
* `AlgebraicGeometry.Scheme.
  exists_generalQuotFunctorP_zero_representableBy_isHProjective_of_zeroLoci`;
* `AlgebraicGeometry.Scheme.
  exists_hilbFunctorP_projective_zero_via_grassmannian`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Fixed-polynomial Quot of a finite twisted-free sheaf on relative projective
zero-space has an H-quasi-projective representative over an arbitrary base.  This is
the dimension-zero specialization of the Grassmannian argument for the
quasi-projectivity theorem. -/
theorem exists_quotFunctorP_zero_representableBy_isHQuasiProjective
    (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP
        (projectiveSpaceOverTwistedFree 0 S l r) P).RepresentableBy Q) ∧
      IsHQuasiProjective Q.hom := by
  obtain ⟨Q, ⟨hQ⟩, N, ι, hι, hcomp⟩ :=
    exists_twistedFreeQuot_representableBy_immersion_projectiveSpace
      0 S l r P
        (twistedFreeQuotHasFreeGrassmannianImmersion_zero S l r P)
  have hQ' : (quotFunctorP
      (projectiveSpaceOverTwistedFree 0 S l r) P).RepresentableBy Q := by
    simpa only [projectiveSpaceOverTwistedFree] using hQ
  exact ⟨Q, ⟨hQ'⟩, N, ι, hι, hcomp⟩

/-- Fixed-polynomial Quot of a finite twisted-free sheaf on relative projective
zero-space has a projective representative by the Grassmannian-immersion and DVR
endgame. -/
theorem exists_quotFunctorP_zero_representableBy_isHProjective_via_grassmannian
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (l : ℤ) (r : ℕ) (P : Polynomial ℚ) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP
        (projectiveSpaceOverTwistedFree 0 S l r) P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  exists_quotFunctorP_representableBy_isHProjective_zero_of_grassmannianImmersion
    S l r P (twistedFreeQuotHasFreeGrassmannianImmersion_zero S l r P)

/-- In relative dimension zero, universal closed kernel zero loci descend the
unconditional twisted-free projectivity theorem to a general finitely presented
quasicoherent ambient sheaf. -/
theorem
    exists_generalQuotFunctorP_zero_representableBy_isHProjective_of_zeroLoci
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (projectiveSpaceOver 0 S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (l : ℤ) (r : ℕ)
    (p : projectiveSpaceOverTwistedFree 0 S l r ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (H : ∀ (T : Over S)
      (z : (quotFunctorP
        (projectiveSpaceOverTwistedFree 0 S l r) P).obj (op T)),
      Nonempty (QuotientKernelZeroLocusData p P T z)) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  exists_quotFunctorP_representableBy_isHProjective_zero_of_zeroLoci_grassmannian
    S F l r p P H
      (twistedFreeQuotHasFreeGrassmannianImmersion_zero S l r P)

/-- Compatible affine finite-free models for the presentation kernel are a concrete
sufficient input for the general-ambient projective-zero endpoint. -/
theorem
    exists_generalQuotFunctorP_zero_representableBy_isHProjective_of_finiteFreeModels
    (S : Scheme.{u}) [IsLocallyNoetherian S]
    (F : (projectiveSpaceOver 0 S).Modules)
    [F.IsQuasicoherent] [F.IsFinitePresentation]
    (l : ℤ) (r : ℕ)
    (p : projectiveSpaceOverTwistedFree 0 S l r ⟶ F) [Epi p]
    (P : Polynomial ℚ)
    (H : ∀ (T : Over S)
      (z : (quotFunctorP
        (projectiveSpaceOverTwistedFree 0 S l r) P).obj (op T)),
      Nonempty (CompatibleAffineFiniteFreeKernelModels p P (T := T) (z := z))) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP F P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  exists_quotFunctorP_representableBy_isHProjective_zero_of_finiteFreeModels_grassmannian
    S F l r p P H
      (twistedFreeQuotHasFreeGrassmannianImmersion_zero S l r P)

/-- Fixed-polynomial quotients of the structure sheaf on relative projective
zero-space have a projective representative via the unconditional
Quot--Grassmannian immersion. -/
theorem exists_structureSheafQuotP_projective_zero_via_grassmannian
    (S : Scheme.{u}) [IsLocallyNoetherian S] (P : Polynomial ℚ) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP
        (SheafOfModules.unit (projectiveSpaceOver 0 S).ringCatSheaf) P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  exists_structureSheafQuotP_projective_zero_of_grassmannianImmersion
    S P (twistedFreeQuotHasFreeGrassmannianImmersion_zero S 0 1 P)

/-- The fixed-polynomial Hilbert functor of relative projective zero-space has a
projective representative via the unconditional Quot--Grassmannian immersion. -/
theorem exists_hilbFunctorP_projective_zero_via_grassmannian
    (S : Scheme.{u}) [IsLocallyNoetherian S] (P : Polynomial ℚ) :
    ∃ H : Over S,
      Nonempty ((hilbFunctorP 0 S P).RepresentableBy H) ∧
      IsHProjective H.hom :=
  exists_hilbFunctorP_projective_zero_of_grassmannianImmersion
    S P (twistedFreeQuotHasFreeGrassmannianImmersion_zero S 0 1 P)

end AlgebraicGeometry.Scheme

end
