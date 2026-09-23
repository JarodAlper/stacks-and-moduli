module

public import StacksAndModuli.API.ProjectiveSpaceZeroEmptyQuot
public import StacksAndModuli.«Section2.1-Intro».«part2.1.4-hilbert-representability-via-quot»

/-!
# Empty Hilbert functors on projective zero-space

The empty-scheme representative for non-natural-constant Quot polynomials
specializes to quotients of the structure sheaf and transports through the
Hilbert--Quot natural isomorphism.  Thus both moduli problems have an
H-projective empty representative in this case.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- If `P` is not `C(q)` for a natural number `q`, fixed-polynomial quotients
of the structure sheaf on relative `P⁰` are represented by the empty scheme. -/
theorem exists_structureSheafQuotP_zero_projective_empty
    (S : Scheme.{u}) (P : Polynomial ℚ)
    (hP : ¬ ∃ q : ℕ, P = Polynomial.C (q : ℚ)) :
    ∃ Q : Over S,
      Nonempty ((quotFunctorP
        (SheafOfModules.unit (projectiveSpaceOver 0 S).ringCatSheaf) P).RepresentableBy Q) ∧
      IsHProjective Q.hom :=
  exists_quotFunctorP_zero_representableBy_isHProjective_empty
    (SheafOfModules.unit (projectiveSpaceOver 0 S).ringCatSheaf) P hP

/-- If `P` is not `C(q)` for a natural number `q`, the fixed-polynomial
Hilbert functor on relative `P⁰` is represented by the empty scheme. -/
theorem exists_hilbFunctorP_zero_projective_empty
    (S : Scheme.{u}) (P : Polynomial ℚ)
    (hP : ¬ ∃ q : ℕ, P = Polynomial.C (q : ℚ)) :
    ∃ H : Over S,
      Nonempty ((hilbFunctorP 0 S P).RepresentableBy H) ∧
      IsHProjective H.hom :=
  exists_hilbFunctorP_representableBy_of_quotFunctorP 0 S P
    (exists_structureSheafQuotP_zero_projective_empty S P hP)

end AlgebraicGeometry.Scheme

end
