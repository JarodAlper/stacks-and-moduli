module

public import StacksAndModuli.API.ProjectiveSpaceZeroQuotGrassmannianIsoCore
public import StacksAndModuli.API.ProjectiveSpaceZeroProjectivity

/-!
# Structure-sheaf Quot and Hilbert endpoints on projective zero-space

The core Quot--Grassmannian isomorphism identifies the one-summand zero-twisted Quot
functor with a free relative Grassmannian.  This file transports that comparison to the
structure-sheaf Quot functor and the Hilbert functor.

Main declarations:
- `Scheme.exists_structureSheafQuotP_zero_representableBy_isHProjective`;
- `Scheme.exists_hilbFunctorP_zero_representableBy_isHProjective`.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Special-case API theorem for Theorem 2.1.3 (relative dimension zero, structure sheaf):
`Quot^P(𝒪/ℙ⁰ₛ/S)` is representable by an H-projective scheme over `S`. -/
theorem exists_structureSheafQuotP_zero_representableBy_isHProjective
    (S : Scheme.{u}) (P : Polynomial ℚ) :
    ∃ G : Over S,
      Nonempty ((quotFunctorP
        (SheafOfModules.unit (projectiveSpaceOver 0 S).ringCatSheaf)
        P).RepresentableBy G) ∧
      IsHProjective G.hom :=
  exists_structureSheafQuotP_zero_representableBy_isHProjective_of_grassmannianIso
    S P (fun q ↦ Modules.zeroQuotPGrassmannianIso S 0 1 q)

/-- Special-case API theorem for Theorem 2.1.2 (relative dimension zero): for every scheme
`S` and polynomial `P ∈ ℚ[z]`, the Hilbert functor `Hilb^P(ℙ⁰ₛ/S)` is representable by an
H-projective scheme over `S`. No noetherian hypothesis is needed. -/
theorem exists_hilbFunctorP_zero_representableBy_isHProjective
    (S : Scheme.{u}) (P : Polynomial ℚ) :
    ∃ H : Over S,
      Nonempty ((hilbFunctorP 0 S P).RepresentableBy H) ∧
      IsHProjective H.hom :=
  exists_hilbFunctorP_zero_representableBy_isHProjective_of_grassmannianIso
    S P (fun q ↦ Modules.zeroQuotPGrassmannianIso S 0 1 q)

end AlgebraicGeometry.Scheme

end
