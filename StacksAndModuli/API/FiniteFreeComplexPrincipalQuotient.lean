module

public import Mathlib.RingTheory.Regular.IsSMulRegular
public import StacksAndModuli.API.FiniteFreeComplexTail
public import StacksAndModuli.API.PolynomialModelBaseChange

/-!
# Finite free complexes modulo a regular element

The quotient of a finite free module by multiplication by `x` is canonically the same
finite free module over `R / (x)`.  This file makes that comparison natural for matrix
maps and applies Mathlib's four-term exactness lemma to finite free complexes.

Reducing an exact complex modulo a regular element preserves exactness after deleting
the bottom term.  The deletion is essential: exactness at the first positive degree can
fail after reduction unless `x` is also regular on the bottom cokernel.

Main declarations:

* `Matrix.quotSMulTopPiEquiv`;
* `Matrix.quotSMulTopPiEquiv_naturality`;
* `Matrix.FiniteFreeComplex.IsExactInPositiveDegreesUpTo.map_principalQuotient_tail`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace Matrix

variable {R : Type u} [CommRing R]

/-- Quotienting a finite free `R`-module by `x` gives the corresponding finite free
module over `R / (x)`, regarded here as an `R`-module. -/
noncomputable def quotSMulTopPiEquiv (x : R) (n : ℕ) :
    QuotSMulTop x (Fin n → R) ≃ₗ[R]
      (Fin n → R ⧸ Ideal.span {x}) :=
  QuotSMulTop.equivQuotTensor x (Fin n → R) ≪≫ₗ
    (TensorProduct.piScalarRight R (R ⧸ Ideal.span {x})
      (R ⧸ Ideal.span {x}) (Fin n)).restrictScalars R

/-- The finite-free quotient equivalences intertwine a matrix map modulo `x` with the
coefficientwise image of that matrix in `R / (x)`. -/
theorem quotSMulTopPiEquiv_naturality
    (x : R) {m n : ℕ} (B : Matrix (Fin m) (Fin n) R) :
    ((Matrix.toLin' (B.map (Ideal.Quotient.mk (Ideal.span {x})))).restrictScalars R).comp
        (quotSMulTopPiEquiv x n).toLinearMap =
      (quotSMulTopPiEquiv x m).toLinearMap.comp
        (QuotSMulTop.map x (Matrix.toLin' B)) := by
  let Q := R ⧸ Ideal.span {x}
  let eM := TensorProduct.piScalarRight R Q Q (Fin m)
  let eN := TensorProduct.piScalarRight R Q Q (Fin n)
  apply LinearMap.ext
  intro z
  change Matrix.toLin' (B.map (algebraMap R Q))
      (eN (QuotSMulTop.equivQuotTensor x (Fin n → R) z)) =
    eM (QuotSMulTop.equivQuotTensor x (Fin m → R)
      (QuotSMulTop.map x (Matrix.toLin' B) z))
  calc
    Matrix.toLin' (B.map (algebraMap R Q))
        (eN (QuotSMulTop.equivQuotTensor x (Fin n → R) z)) =
      eM (((Matrix.toLin' B).baseChange Q)
        (QuotSMulTop.equivQuotTensor x (Fin n → R) z)) :=
      (LinearMap.congr_fun
        (Matrix.piScalarRight_toLin_map (A := Q) B)
        (QuotSMulTop.equivQuotTensor x (Fin n → R) z)).symm
    _ = eM ((Matrix.toLin' B).lTensor Q
        (QuotSMulTop.equivQuotTensor x (Fin n → R) z)) := by
      rw [LinearMap.baseChange_eq_ltensor]
    _ = eM (QuotSMulTop.equivQuotTensor x (Fin m → R)
        (QuotSMulTop.map x (Matrix.toLin' B) z)) := by
      exact congrArg eM (LinearMap.congr_fun
        (QuotSMulTop.equivQuotTensor_naturality x (Matrix.toLin' B)) z).symm

namespace FiniteFreeComplex

/-- Away from the bottom degree, exactness of a finite free complex survives reduction
modulo a regular element. -/
theorem IsExactInPositiveDegreesUpTo.isExact_map_principalQuotient_at_succ
    {C : FiniteFreeComplex R} {N i : ℕ}
    (hC : C.IsExactInPositiveDegreesUpTo N) (hi : i + 1 < N)
    (x : R) (hx : IsRegular x) :
    Function.Exact
      (Matrix.toLin' ((C.map (Ideal.Quotient.mk (Ideal.span {x}))).differential
        ((i + 1) + 1)))
      (Matrix.toLin' ((C.map (Ideal.Quotient.mk (Ideal.span {x}))).differential
        (i + 1))) := by
  let q := Ideal.Quotient.mk (Ideal.span {x})
  have hquot : Function.Exact
      (QuotSMulTop.map x (Matrix.toLin' (C.differential (i + 2))))
      (QuotSMulTop.map x (Matrix.toLin' (C.differential (i + 1)))) :=
    QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
      (hC (i + 1) hi) (hC i (by omega))
      (IsSMulRegular.pi fun _ : Fin (C.termRank i) ↦ hx.isSMulRegular)
  have hmap : Function.Exact
      ((Matrix.toLin' ((C.differential (i + 2)).map q)).restrictScalars R)
      ((Matrix.toLin' ((C.differential (i + 1)).map q)).restrictScalars R) :=
    (Function.Exact.iff_of_ladder_linearEquiv
      (Matrix.quotSMulTopPiEquiv_naturality x (C.differential (i + 2)))
      (Matrix.quotSMulTopPiEquiv_naturality x (C.differential (i + 1)))).mpr hquot
  change Function.Exact
    (Matrix.toLin' ((C.differential ((i + 1) + 1)).map q))
    (Matrix.toLin' ((C.differential (i + 1)).map q))
  exact hmap

/-- Reducing an exact finite free complex modulo a regular element preserves exactness
of its tail. -/
theorem IsExactInPositiveDegreesUpTo.map_principalQuotient_tail
    {C : FiniteFreeComplex R} {N : ℕ}
    (hC : C.IsExactInPositiveDegreesUpTo (N + 1))
    (x : R) (hx : IsRegular x) :
    (C.map (Ideal.Quotient.mk (Ideal.span {x}))).tail.IsExactInPositiveDegreesUpTo N := by
  intro i hi
  change Function.Exact
    (Matrix.toLin' ((C.map (Ideal.Quotient.mk (Ideal.span {x}))).differential
      ((i + 1) + 1)))
    (Matrix.toLin' ((C.map (Ideal.Quotient.mk (Ideal.span {x}))).differential
      (i + 1)))
  exact hC.isExact_map_principalQuotient_at_succ (i := i) (by omega) x hx

end FiniteFreeComplex

end Matrix

end

end
