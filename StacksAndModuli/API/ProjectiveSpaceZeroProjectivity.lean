module

public import StacksAndModuli.API.ProjectiveSpaceZeroQuotProjectivity
public import StacksAndModuli.API.ProjectiveSpaceZeroEmptyHilbert
public import StacksAndModuli.API.ProjectiveTwistedFreeUnitIso

/-!
# Structure-sheaf Quot and Hilbert projectivity on projective zero-space

This file transports the twisted-free projective-zero Quot projectivity theorem through
the identification of the one-summand zero twist with the structure sheaf and then through
the Hilbert--Quot comparison.

Main declarations:
- `AlgebraicGeometry.Scheme.
  exists_structureSheafQuotP_zero_representableBy_isHProjective_of_grassmannianIso`;
- `AlgebraicGeometry.Scheme.
  exists_hilbFunctorP_zero_representableBy_isHProjective_of_grassmannianIso`.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

/-- A constant-polynomial Grassmannian comparison for the one-summand
zero-twisted ambient sheaf gives an H-projective representative for the
structure-sheaf Quot functor. -/
theorem
    exists_structureSheafQuotP_zero_C_representableBy_isHProjective_of_iso
    (S : Scheme.{u}) (q : ℕ)
    (e : quotFunctorP (projectiveSpaceOverTwistedFree 0 S 0 1)
        (Polynomial.C (q : ℚ)) ≅
      Modules.grassmannianOverFunctor q
        (SheafOfModules.free (R := S.ringCatSheaf)
          (ULift.{u} (Fin 1)))) :
    ∃ G : Over S,
      Nonempty ((quotFunctorP
        (SheafOfModules.unit (projectiveSpaceOver 0 S).ringCatSheaf)
        (Polynomial.C (q : ℚ))).RepresentableBy G) ∧
      IsHProjective G.hom := by
  obtain ⟨G, ⟨hG⟩, hproj⟩ :=
    exists_quotFunctorP_zero_C_representableBy_isHProjective_of_iso
      S 0 1 q e
  exact ⟨G, ⟨hG.ofIso
    (projectiveSpaceOverUnitQuotFunctorPIso 0 S
      (Polynomial.C (q : ℚ))).symm⟩, hproj⟩

/-- Under all constant-polynomial Grassmannian comparisons, the
structure-sheaf Quot functor on projective zero-space has an H-projective
representative for every polynomial. -/
theorem
    exists_structureSheafQuotP_zero_representableBy_isHProjective_of_grassmannianIso
    (S : Scheme.{u}) (P : Polynomial ℚ)
    (e : ∀ q : ℕ,
      quotFunctorP (projectiveSpaceOverTwistedFree 0 S 0 1)
          (Polynomial.C (q : ℚ)) ≅
        Modules.grassmannianOverFunctor q
          (SheafOfModules.free (R := S.ringCatSheaf)
            (ULift.{u} (Fin 1)))) :
    ∃ G : Over S,
      Nonempty ((quotFunctorP
        (SheafOfModules.unit (projectiveSpaceOver 0 S).ringCatSheaf) P).RepresentableBy G) ∧
      IsHProjective G.hom := by
  by_cases hP : ∃ q : ℕ, P = Polynomial.C (q : ℚ)
  · obtain ⟨q, rfl⟩ := hP
    exact
      exists_structureSheafQuotP_zero_C_representableBy_isHProjective_of_iso
        S q (e q)
  · exact exists_structureSheafQuotP_zero_projective_empty S P hP

/-- Under all constant-polynomial Grassmannian comparisons, the Hilbert
functor on projective zero-space has an H-projective representative for every
polynomial. -/
theorem
    exists_hilbFunctorP_zero_representableBy_isHProjective_of_grassmannianIso
    (S : Scheme.{u}) (P : Polynomial ℚ)
    (e : ∀ q : ℕ,
      quotFunctorP (projectiveSpaceOverTwistedFree 0 S 0 1)
          (Polynomial.C (q : ℚ)) ≅
        Modules.grassmannianOverFunctor q
          (SheafOfModules.free (R := S.ringCatSheaf)
            (ULift.{u} (Fin 1)))) :
    ∃ H : Over S,
      Nonempty ((hilbFunctorP 0 S P).RepresentableBy H) ∧
      IsHProjective H.hom :=
  exists_hilbFunctorP_representableBy_of_quotFunctorP 0 S P
    (exists_structureSheafQuotP_zero_representableBy_isHProjective_of_grassmannianIso
      S P e)

end AlgebraicGeometry.Scheme

end
