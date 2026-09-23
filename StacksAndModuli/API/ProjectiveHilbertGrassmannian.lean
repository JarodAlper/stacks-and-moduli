module

public import StacksAndModuli.API.ProjectiveTwistedFreeUnitIso
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianProjectivity
public import StacksAndModuli.«Section2.1-Intro».«part2.1.4-hilbert-representability-via-quot»

/-!
# Hilbert projectivity from the Quot-to-Grassmannian immersion

The structure sheaf of relative projective space is isomorphic to the one-summand
twisted-free sheaf with twist zero.  Consequently, the projective representability
obtained from a free-Grassmannian immersion for that twisted-free Quot functor
transports first to structure-sheaf Quot and then to the fixed-polynomial Hilbert
functor.

This file records both the general Serre-conditional reduction and its dimension-zero
specialization, where the DVR cohomological input has already been proved.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A free-Grassmannian immersion for the one-summand zero-twist Quot functor,
together with Serre vanishing over DVRs, gives a projective representative for
fixed-polynomial quotients of the structure sheaf. -/
theorem
    exists_structureSheafQuotP_projective_of_grassmannianImmersion_of_serre
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S] (P : Polynomial ℚ)
    (himm : TwistedFreeQuotHasFreeGrassmannianImmersion n S 0 1 P)
    (hserre : ∀ (R : Type u) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R],
        ProjectiveSpaceHasSerreVanishing n (Spec (.of R))) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP
        (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf) P).RepresentableBy Q) ∧
      IsHProjective Q.hom := by
  obtain ⟨Q, ⟨hQ⟩, hQproj⟩ :=
    exists_quotFunctorP_representableBy_isHProjective_of_grassmannianImmersion_of_serre
      n S 0 1 P himm hserre
  refine ⟨Q, ⟨?_⟩, hQproj⟩
  exact hQ.ofIso (projectiveSpaceOverUnitQuotFunctorPIso n S P).symm

/-- On relative `P⁰`, a free-Grassmannian immersion for the one-summand
zero-twist Quot functor gives a projective representative for fixed-polynomial
quotients of the structure sheaf without an additional cohomological hypothesis. -/
theorem
    exists_structureSheafQuotP_projective_zero_of_grassmannianImmersion
    (S : Scheme.{u}) [IsLocallyNoetherian S] (P : Polynomial ℚ)
    (himm : TwistedFreeQuotHasFreeGrassmannianImmersion 0 S 0 1 P) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP
        (SheafOfModules.unit (projectiveSpaceOver 0 S).ringCatSheaf) P).RepresentableBy Q) ∧
      IsHProjective Q.hom := by
  obtain ⟨Q, ⟨hQ⟩, hQproj⟩ :=
    exists_quotFunctorP_representableBy_isHProjective_zero_of_grassmannianImmersion
      S 0 1 P himm
  refine ⟨Q, ⟨?_⟩, hQproj⟩
  exact hQ.ofIso (projectiveSpaceOverUnitQuotFunctorPIso 0 S P).symm

/-- A free-Grassmannian immersion for the one-summand zero-twist Quot functor,
together with Serre vanishing over DVRs, gives a projective representative for the
fixed-polynomial Hilbert functor. -/
theorem
    exists_hilbFunctorP_projective_of_grassmannianImmersion_of_serre
    (n : ℕ) (S : Scheme.{u}) [IsLocallyNoetherian S] (P : Polynomial ℚ)
    (himm : TwistedFreeQuotHasFreeGrassmannianImmersion n S 0 1 P)
    (hserre : ∀ (R : Type u) [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R],
        ProjectiveSpaceHasSerreVanishing n (Spec (.of R))) :
    ∃ H : Over S,
      Nonempty ((hilbFunctorP n S P).RepresentableBy H) ∧
      IsHProjective H.hom :=
  exists_hilbFunctorP_representableBy_of_quotFunctorP n S P
    (exists_structureSheafQuotP_projective_of_grassmannianImmersion_of_serre
      n S P himm hserre)

/-- On relative `P⁰`, a free-Grassmannian immersion for the one-summand
zero-twist Quot functor gives a projective representative for the fixed-polynomial
Hilbert functor without an additional cohomological hypothesis. -/
theorem exists_hilbFunctorP_projective_zero_of_grassmannianImmersion
    (S : Scheme.{u}) [IsLocallyNoetherian S] (P : Polynomial ℚ)
    (himm : TwistedFreeQuotHasFreeGrassmannianImmersion 0 S 0 1 P) :
    ∃ H : Over S,
      Nonempty ((hilbFunctorP 0 S P).RepresentableBy H) ∧
      IsHProjective H.hom :=
  exists_hilbFunctorP_representableBy_of_quotFunctorP 0 S P
    (exists_structureSheafQuotP_projective_zero_of_grassmannianImmersion
      S P himm)

end AlgebraicGeometry.Scheme

end
