module

public import StacksAndModuli.API.PolynomialModelBaseChange

/-!
# Coefficient rings of base-changed polynomial presentations

Applying a coefficient-ring map to a finite polynomial matrix cannot introduce new
coefficients.  Consequently, the canonical coefficient ring of the explicit base change of a
polynomial presentation is contained in the image of the original coefficient ring.  This is
the finite-coefficient input needed when a local approximation over a localization is compared
with the canonical coefficient stages over the original ring.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

namespace Module.FinitePresentation

variable {A B : Type u} {sigma : Type v} [CommRing A] [CommRing B]

/-- The coefficient ring of a coefficientwise image of a finite polynomial matrix lies in
the image of the original coefficient ring. -/
theorem polynomialMatrixCoeffSubalgebra_map_le
    {m n : ℕ} (G : Matrix (Fin n) (Fin m) (MvPolynomial sigma A))
    (f : A →+* B) :
    polynomialMatrixCoeffSubalgebra (R := ℤ)
        (G.map (MvPolynomial.map f)) ≤
      Subalgebra.map f.toIntAlgHom
        (polynomialMatrixCoeffSubalgebra (R := ℤ) G) := by
  classical
  apply Algebra.adjoin_le
  intro b hb
  simp only [Set.mem_iUnion] at hb
  obtain ⟨i, j, hb⟩ := hb
  have hbimage : b ∈ Finset.image f (G i j).coeffs :=
    MvPolynomial.coeffs_map f (G i j) hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hbimage
  apply Subalgebra.mem_map.mpr
  refine ⟨a, ?_, rfl⟩
  exact Algebra.subset_adjoin
    (Set.mem_iUnion_of_mem i (Set.mem_iUnion_of_mem j ha))

namespace PolynomialModel

variable {A B M : Type u} {sigma : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module (MvPolynomial sigma A) M]

/-- The canonical coefficient ring of the explicit scalar extension of a polynomial
presentation lies in the image of the presentation's original coefficient ring. -/
theorem coefficientRing_baseChange_le_map (D : PolynomialModel A sigma M) :
    letI : Algebra (MvPolynomial sigma A) (MvPolynomial sigma B) :=
      MvPolynomial.algebraMvPolynomial
    (D.baseChange (B := B)).coefficientRing (R := ℤ) ≤
      Subalgebra.map (algebraMap A B).toIntAlgHom
        (D.coefficientRing (R := ℤ)) := by
  letI : Algebra (MvPolynomial sigma A) (MvPolynomial sigma B) :=
    MvPolynomial.algebraMvPolynomial
  change polynomialMatrixCoeffSubalgebra (R := ℤ)
      (LinearMap.toMatrix' D.baseChangeRelation) ≤
    Subalgebra.map (algebraMap A B).toIntAlgHom
      (polynomialMatrixCoeffSubalgebra (R := ℤ)
        (LinearMap.toMatrix' D.relation))
  rw [D.toMatrix_baseChangeRelation]
  exact polynomialMatrixCoeffSubalgebra_map_le
    (LinearMap.toMatrix' D.relation) (algebraMap A B)

end PolynomialModel

end Module.FinitePresentation

end

end
