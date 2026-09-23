module

public import StacksAndModuli.API.FreeQuotientRankBound
public import StacksAndModuli.API.FreeGrassmannianImmersion
public import StacksAndModuli.API.ProjectiveSpaceZeroEmptyQuot
public import StacksAndModuli.API.ProjectiveSpaceZeroGrassmannian

/-!
# Projectivity endgame for twisted-free Quot on projective zero-space

This file packages the final projective-geometric argument after identifying a
constant-polynomial Quot functor on relative projective zero-space with a free
relative Grassmannian.  In the range `q ≤ r`, the Plücker embedding makes the
usual Grassmannian representative H-projective.  In the complementary range,
the rank obstruction makes the functor empty on every nonempty test scheme, so
it is represented by the empty H-projective scheme.

Main declaration:
- `AlgebraicGeometry.Scheme.
  exists_quotFunctorP_zero_representableBy_isHProjective_of_grassmannianIso`.
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

/-- In the range `r < q`, a Grassmannian comparison makes constant-polynomial
Quot on projective zero-space empty on every nonempty test scheme. -/
lemma quotFunctorPEmptyOnNonempty_zero_C_of_grassmannianIso_of_lt
    (S : Scheme.{u}) (l : ℤ) (r q : ℕ)
    (e : quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r)
        (Polynomial.C (q : ℚ)) ≅
      Modules.grassmannianOverFunctor q
        (SheafOfModules.free (R := S.ringCatSheaf)
          (ULift.{u} (Fin r))))
    (hqr : r < q) :
    QuotFunctorPEmptyOnNonempty
      (projectiveSpaceOverTwistedFree 0 S l r)
      (Polynomial.C (q : ℚ)) := by
  intro T hT
  letI : IsEmpty ((Modules.grassmannianOverFunctor q
      (SheafOfModules.free (R := S.ringCatSheaf)
        (ULift.{u} (Fin r)))).obj (op T)) :=
    Modules.grassmannianOverFunctor_isEmpty_of_lt S q r hqr T hT
  constructor
  intro z
  exact isEmptyElim (e.hom.app (op T) z)

/-- In the nonempty-rank range, a Grassmannian comparison gives an
H-projective representative for constant-polynomial Quot on projective
zero-space. -/
theorem exists_quotFunctorP_zero_C_representableBy_isHProjective_of_iso_of_le
    (S : Scheme.{u}) (l : ℤ) (r q : ℕ)
    (e : quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r)
        (Polynomial.C (q : ℚ)) ≅
      Modules.grassmannianOverFunctor q
        (SheafOfModules.free (R := S.ringCatSheaf)
          (ULift.{u} (Fin r))))
    (hqr : q ≤ r) :
    ∃ G : Over S,
      Nonempty ((quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r)
        (Polynomial.C (q : ℚ))).RepresentableBy G) ∧
      IsHProjective G.hom :=
  ⟨grassmannianOverRepresentation S q r,
    ⟨(freeGrassmannianRepresentableBy S q r).ofIso e.symm⟩,
    grassmannianOverRepresentation_isHProjective_of_le S q r hqr⟩

/-- A Grassmannian comparison gives an H-projective representative for
constant-polynomial Quot on projective zero-space in every rank. -/
theorem exists_quotFunctorP_zero_C_representableBy_isHProjective_of_iso
    (S : Scheme.{u}) (l : ℤ) (r q : ℕ)
    (e : quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r)
        (Polynomial.C (q : ℚ)) ≅
      Modules.grassmannianOverFunctor q
        (SheafOfModules.free (R := S.ringCatSheaf)
          (ULift.{u} (Fin r)))) :
    ∃ G : Over S,
      Nonempty ((quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r)
        (Polynomial.C (q : ℚ))).RepresentableBy G) ∧
      IsHProjective G.hom := by
  by_cases hqr : q ≤ r
  · exact
      exists_quotFunctorP_zero_C_representableBy_isHProjective_of_iso_of_le
        S l r q e hqr
  · exact
      exists_quotFunctorP_representableBy_isHProjective_empty_of_isEmptyOnNonempty
        (projectiveSpaceOverTwistedFree 0 S l r)
        (Polynomial.C (q : ℚ))
        (quotFunctorPEmptyOnNonempty_zero_C_of_grassmannianIso_of_lt
          S l r q e (Nat.lt_of_not_ge hqr))

/-- If every constant-polynomial comparison with the corresponding free
Grassmannian is available, fixed-polynomial Quot on projective zero-space has
an H-projective representative for every polynomial. -/
theorem exists_quotFunctorP_zero_representableBy_isHProjective_of_grassmannianIso
    (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (e : ∀ q : ℕ,
      quotFunctorP (projectiveSpaceOverTwistedFree 0 S l r)
          (Polynomial.C (q : ℚ)) ≅
        Modules.grassmannianOverFunctor q
          (SheafOfModules.free (R := S.ringCatSheaf)
            (ULift.{u} (Fin r)))) :
    ∃ G : Over S,
      Nonempty ((quotFunctorP
        (projectiveSpaceOverTwistedFree 0 S l r) P).RepresentableBy G) ∧
      IsHProjective G.hom := by
  by_cases hP : ∃ q : ℕ, P = Polynomial.C (q : ℚ)
  · obtain ⟨q, rfl⟩ := hP
    exact exists_quotFunctorP_zero_C_representableBy_isHProjective_of_iso
      S l r q (e q)
  · exact exists_quotFunctorP_zero_representableBy_isHProjective_empty
      (projectiveSpaceOverTwistedFree 0 S l r) P hP

end AlgebraicGeometry.Scheme

end
