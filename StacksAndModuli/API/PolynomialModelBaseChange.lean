module

public import StacksProject.Algebra.ColimitsAndMapsOfFinitePresentationII.«lemma-flat-finite-presentation-limit-flat»

/-!
# Base change of finite polynomial-module presentations

A finite free presentation over `A[x_i]` has a canonical scalar extension along a
coefficient map `A → B`.  The generators and relations are unchanged, while the two free
modules and the presented cokernel are transported through the standard tensor-product
identifications.  Keeping this presentation explicit is useful in noetherian approximation:
the relation matrix after localization is visibly the image of the original matrix.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe uA uB uSigma uM

open TensorProduct

namespace Module.FinitePresentation.PolynomialModel

variable {A : Type uA} {B : Type uB} {sigma : Type uSigma} {M : Type uM}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module (MvPolynomial sigma A) M]

/-- The quotient map in the scalar extension of a finite polynomial presentation. -/
noncomputable def baseChangeQuotient (D : PolynomialModel A sigma M) :
    letI : Algebra (MvPolynomial sigma A) (MvPolynomial sigma B) :=
      MvPolynomial.algebraMvPolynomial
    (Fin D.generators → MvPolynomial sigma B) →ₗ[MvPolynomial sigma B]
      (MvPolynomial sigma B ⊗[MvPolynomial sigma A] M) := by
  letI : Algebra (MvPolynomial sigma A) (MvPolynomial sigma B) :=
    MvPolynomial.algebraMvPolynomial
  let e := TensorProduct.piScalarRight
    (MvPolynomial sigma A) (MvPolynomial sigma B) (MvPolynomial sigma B)
      (Fin D.generators)
  exact D.quotient.baseChange (MvPolynomial sigma B) ∘ₗ e.symm.toLinearMap

/-- The relation map in the scalar extension of a finite polynomial presentation. -/
noncomputable def baseChangeRelation (D : PolynomialModel A sigma M) :
    (Fin D.relations → MvPolynomial sigma B) →ₗ[MvPolynomial sigma B]
      (Fin D.generators → MvPolynomial sigma B) := by
  letI : Algebra (MvPolynomial sigma A) (MvPolynomial sigma B) :=
    MvPolynomial.algebraMvPolynomial
  let eN := TensorProduct.piScalarRight
    (MvPolynomial sigma A) (MvPolynomial sigma B) (MvPolynomial sigma B)
      (Fin D.generators)
  let eM := TensorProduct.piScalarRight
    (MvPolynomial sigma A) (MvPolynomial sigma B) (MvPolynomial sigma B)
      (Fin D.relations)
  exact eN.toLinearMap ∘ₗ D.relation.baseChange (MvPolynomial sigma B) ∘ₗ
    eM.symm.toLinearMap

/-- The base-changed relation is the linear map of the coefficientwise image of the
original relation matrix. -/
theorem baseChangeRelation_eq_toLin_map (D : PolynomialModel A sigma M) :
    D.baseChangeRelation = Matrix.toLin'
      ((LinearMap.toMatrix' D.relation).map
        (MvPolynomial.map (algebraMap A B))) := by
  let S := MvPolynomial sigma A
  let T := MvPolynomial sigma B
  letI : Algebra S T := MvPolynomial.algebraMvPolynomial
  let G := LinearMap.toMatrix' D.relation
  let eN := TensorProduct.piScalarRight S T T (Fin D.generators)
  let eM := TensorProduct.piScalarRight S T T (Fin D.relations)
  change (eN.toLinearMap.comp (D.relation.baseChange T)).comp
      eM.symm.toLinearMap = Matrix.toLin' (G.map (algebraMap S T))
  calc
    (eN.toLinearMap.comp (D.relation.baseChange T)).comp
          eM.symm.toLinearMap =
        ((Matrix.toLin' (G.map (algebraMap S T))).comp eM.toLinearMap).comp
          eM.symm.toLinearMap := by
      apply congrArg (fun q : (T ⊗[S] (Fin D.relations → S)) →ₗ[T]
        (Fin D.generators → T) ↦ q.comp eM.symm.toLinearMap)
      simpa only [G, Matrix.toLin'_toMatrix'] using
        Matrix.piScalarRight_toLin_map (A := T) G
    _ = Matrix.toLin' (G.map (algebraMap S T)) := by
      rw [LinearMap.comp_assoc, eM.comp_symm, LinearMap.comp_id]

/-- The matrix of the base-changed relation is obtained by applying the induced polynomial
coefficient map entrywise. -/
theorem toMatrix_baseChangeRelation (D : PolynomialModel A sigma M) :
    LinearMap.toMatrix' D.baseChangeRelation =
      (LinearMap.toMatrix' D.relation).map
        (MvPolynomial.map (algebraMap A B)) := by
  rw [D.baseChangeRelation_eq_toLin_map,
    LinearMap.toMatrix'_toLin']

/-- Scalar extension of a finite polynomial presentation along a coefficient-ring map. -/
noncomputable def baseChange (D : PolynomialModel A sigma M) :
    letI : Algebra (MvPolynomial sigma A) (MvPolynomial sigma B) :=
      MvPolynomial.algebraMvPolynomial
    PolynomialModel B sigma
      (MvPolynomial sigma B ⊗[MvPolynomial sigma A] M) := by
  letI : Algebra (MvPolynomial sigma A) (MvPolynomial sigma B) :=
    MvPolynomial.algebraMvPolynomial
  refine
    { generators := D.generators
      relations := D.relations
      quotient := D.baseChangeQuotient
      relation := D.baseChangeRelation
      quotient_surjective := ?_
      exact := ?_ }
  · let eN := TensorProduct.piScalarRight
      (MvPolynomial sigma A) (MvPolynomial sigma B) (MvPolynomial sigma B)
        (Fin D.generators)
    exact (LinearMap.lTensor_surjective
      (MvPolynomial sigma B) D.quotient_surjective).comp eN.symm.surjective
  · let S := MvPolynomial sigma A
    let T := MvPolynomial sigma B
    let eN := TensorProduct.piScalarRight S T T (Fin D.generators)
    let eM := TensorProduct.piScalarRight S T T (Fin D.relations)
    have hbc : Function.Exact
        (D.relation.baseChange T) (D.quotient.baseChange T) := by
      simpa only [LinearMap.baseChange_eq_ltensor] using
        lTensor_exact T D.exact D.quotient_surjective
    have hconj : Function.Exact
        (eN.toLinearMap.comp (D.relation.baseChange T))
        ((D.quotient.baseChange T).comp eN.symm.toLinearMap) :=
      (LinearEquiv.conj_exact_iff_exact
        (D.relation.baseChange T) (D.quotient.baseChange T) eN).mpr hbc
    have hpre : Function.Exact
        ((eN.toLinearMap.comp (D.relation.baseChange T)).comp
          eM.symm.toLinearMap)
        ((D.quotient.baseChange T).comp eN.symm.toLinearMap) :=
      (LinearEquiv.precomp_exact_iff_exact
        (f := eN.toLinearMap.comp (D.relation.baseChange T))
        (g := (D.quotient.baseChange T).comp eN.symm.toLinearMap)
        (e := eM.symm)).mpr hconj
    exact hpre

end Module.FinitePresentation.PolynomialModel

end

end
