module

public import StacksAndModuli.API.PolynomialLinearHilbertNatValue
public import StacksAndModuli.API.ProjectiveLineGeneratedRelationPersistence

/-!
# Hilbert-polynomial persistence for generated binary quotients

Binary relation persistence computes all later dimensions of a quotient generated in one
degree as an arithmetic progression.  A Hilbert polynomial of degree at most one has the
same progression once its two adjacent normalized values agree with those seed dimensions.
This file combines those two independent statements.

The result is still algebraic: it identifies the homogeneous pieces of the generated graded
quotient with the prescribed Hilbert values.  Comparing those pieces with the pushforwards
of the reconstructed sheaf remains the geometric saturation step.

Main declarations:

* `GradedModule.finrank_generatedQuotient_obj_eq_hilbertNatValue_of_binary_seed`;
* `finrank_affineReconstructedGeneratedGradedQuotient_obj_eq_hilbertNatValue_of_binary_seed`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable (K : Type u) [Field K]

/-- Binary persistence for a generated graded quotient, rewritten as agreement with every
later normalized value of a degree-at-most-one Hilbert polynomial. -/
theorem finrank_generatedQuotient_obj_eq_hilbertNatValue_of_binary_seed
    (P : Polynomial ℚ) (hP : P.natDegree ≤ 1)
    (l : ℤ) (r d e : ℕ) (he : (e : ℤ) = (d : ℤ) - l)
    (A : ModuleCat.{u} K)
    (f : A ⟶ ((((structureModule K 1).twist (-l)).pow r).obj (d : ℤ)))
    (a s : ℕ)
    (hself : Module.finrank K
      ((generatedQuotient
        (((structureModule K 1).twist (-l)).pow r) (d : ℤ) A f).obj (d : ℤ)) =
        P.hilbertNatValue d)
    (hnext : Module.finrank K
      ((generatedQuotient
        (((structureModule K 1).twist (-l)).pow r) (d : ℤ) A f).obj
          ((d : ℤ) + 1)) = P.hilbertNatValue (d + 1))
    (hPd : (P.hilbertNatValue d : ℚ) = P.eval (d : ℚ))
    (hPsucc : (P.hilbertNatValue (d + 1) : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (hquotientGrowth : P.hilbertNatValue (d + 1) =
      P.hilbertNatValue d + a)
    (hambientSplit : r = a + s)
    (hcase : s = 0 ∨ P.hilbertNatValue (d + 1) < (a + 1) * (e + 2)) :
    ∀ k : ℕ,
      Module.finrank K
        ((generatedQuotient
          (((structureModule K 1).twist (-l)).pow r) (d : ℤ) A f).obj
            ((d : ℤ) + (k : ℤ))) = P.hilbertNatValue (d + k) := by
  have hgraded := finrank_generatedQuotient_obj_eq_of_binary_seed
    K l r (d : ℤ) e he A f
      (P.hilbertNatValue d) (P.hilbertNatValue (d + 1)) a s
      hself hnext hquotientGrowth hambientSplit hcase
  have hpolynomial := P.hilbertNatValue_nat_add_eq_of_adjacent
    hP d a hPd hPsucc hquotientGrowth
  intro k
  exact (hgraded k).trans (hpolynomial k).symm

end AlgebraicGeometry.ProjectiveSpace.GradedModule

namespace AlgebraicGeometry

open ProjectiveSpace ProjectiveSpace.GradedModule

variable (K : Type u) [Field K]

/-- Affine reconstructed-quotient specialization of generated binary Hilbert persistence.
It computes every later algebraic homogeneous rank from the two expected seed ranks. -/
theorem
    finrank_affineReconstructedGeneratedGradedQuotient_obj_eq_hilbertNatValue_of_binary_seed
    (P : Polynomial ℚ) (hP : P.natDegree ≤ 1)
    (l : ℤ) (r d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    {E : (Spec (.of K)).Modules}
    (u : SheafOfModules.free (R := (Spec (.of K)).ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((1 + e).choose 1)) ⟶ E)
    (a s : ℕ)
    (hself : Module.finrank K
      ((affineReconstructedGeneratedGradedQuotient
        1 (.of K) l r d e he u).obj (d : ℤ)) = P.hilbertNatValue d)
    (hnext : Module.finrank K
      ((affineReconstructedGeneratedGradedQuotient
        1 (.of K) l r d e he u).obj ((d : ℤ) + 1)) =
          P.hilbertNatValue (d + 1))
    (hPd : (P.hilbertNatValue d : ℚ) = P.eval (d : ℚ))
    (hPsucc : (P.hilbertNatValue (d + 1) : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (hquotientGrowth : P.hilbertNatValue (d + 1) =
      P.hilbertNatValue d + a)
    (hambientSplit : r = a + s)
    (hcase : s = 0 ∨ P.hilbertNatValue (d + 1) < (a + 1) * (e + 2)) :
    ∀ k : ℕ,
      Module.finrank K
        ((affineReconstructedGeneratedGradedQuotient
          1 (.of K) l r d e he u).obj ((d : ℤ) + (k : ℤ))) =
            P.hilbertNatValue (d + k) := by
  have hgraded :=
    finrank_affineReconstructedGeneratedGradedQuotient_obj_eq_of_binary_seed
      K l r d e he u
        (P.hilbertNatValue d) (P.hilbertNatValue (d + 1)) a s
        hself hnext hquotientGrowth hambientSplit hcase
  have hpolynomial := P.hilbertNatValue_nat_add_eq_of_adjacent
    hP d a hPd hPsucc hquotientGrowth
  intro k
  exact (hgraded k).trans (hpolynomial k).symm

end AlgebraicGeometry

end

end
