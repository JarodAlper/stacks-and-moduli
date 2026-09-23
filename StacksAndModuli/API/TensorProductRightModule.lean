module

public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# A tensor-product module structure through the right factor

Mathlib's standard `TensorProduct.leftModule` lets an algebra act through the left tensor
factor. This file supplies the symmetric explicit construction through the right factor.
It is deliberately not registered globally, since registering both actions would create
overlapping module instances when both factors carry the algebra action.

Main declarations:

* `TensorProduct.rightModule`;
* `TensorProduct.rightModule_smul_tmul`.
-/

@[expose] public section

universe u

namespace TensorProduct

variable {R A M N : Type u} [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N]

/-- The `A`-module structure on `M ⊗[R] N` obtained from the `A`-action on the right
factor. Install it explicitly with `letI := TensorProduct.rightModule`. -/
@[instance_reducible]
noncomputable def rightModule : Module A (M ⊗[R] N) where
  smul a x := (Algebra.lsmul R R N a).lTensor M x
  one_smul x := by
    change (Algebra.lsmul R R N (1 : A)).lTensor M x = x
    induction x with
    | zero => exact map_zero _
    | add x y hx hy => rw [map_add, hx, hy]
    | tmul x y =>
        rw [LinearMap.lTensor_tmul, Algebra.lsmul_apply, one_smul]
  mul_smul a b x := by
    change (Algebra.lsmul R R N (a * b)).lTensor M x =
      (Algebra.lsmul R R N a).lTensor M ((Algebra.lsmul R R N b).lTensor M x)
    induction x with
    | zero => rw [map_zero, map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul x y =>
        rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
        change x ⊗ₜ[R] ((a * b) • y) = x ⊗ₜ[R] (a • b • y)
        rw [mul_smul]
  smul_zero a := map_zero _
  smul_add a x y := map_add _ _ _
  zero_smul x := by
    change (Algebra.lsmul R R N (0 : A)).lTensor M x = 0
    induction x with
    | zero => exact map_zero _
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
    | tmul x y =>
        rw [LinearMap.lTensor_tmul, Algebra.lsmul_apply, zero_smul, tmul_zero]
  add_smul a b x := by
    change (Algebra.lsmul R R N (a + b)).lTensor M x =
      (Algebra.lsmul R R N a).lTensor M x + (Algebra.lsmul R R N b).lTensor M x
    induction x with
    | zero => rw [map_zero, map_zero, map_zero, add_zero]
    | add x y hx hy =>
        calc
          (Algebra.lsmul R R N (a + b)).lTensor M (x + y) =
              (Algebra.lsmul R R N (a + b)).lTensor M x +
                (Algebra.lsmul R R N (a + b)).lTensor M y := map_add _ _ _
          _ = ((Algebra.lsmul R R N a).lTensor M x +
                (Algebra.lsmul R R N b).lTensor M x) +
              ((Algebra.lsmul R R N a).lTensor M y +
                (Algebra.lsmul R R N b).lTensor M y) := congrArg₂ (· + ·) hx hy
          _ = ((Algebra.lsmul R R N a).lTensor M x +
                (Algebra.lsmul R R N a).lTensor M y) +
              ((Algebra.lsmul R R N b).lTensor M x +
                (Algebra.lsmul R R N b).lTensor M y) := add_add_add_comm _ _ _ _
          _ = (Algebra.lsmul R R N a).lTensor M (x + y) +
              (Algebra.lsmul R R N b).lTensor M (x + y) := by
                rw [map_add, map_add]
    | tmul x y =>
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
      rw [Algebra.lsmul_apply, Algebra.lsmul_apply, Algebra.lsmul_apply, add_smul, tmul_add]

/-- Scalar multiplication through `rightModule` acts on the right tensor factor. -/
@[simp]
lemma rightModule_smul_tmul (a : A) (x : M) (y : N) :
    let _ : Module A (M ⊗[R] N) := rightModule
    a • (x ⊗ₜ[R] y) = x ⊗ₜ[R] (a • y) := by
  rfl

end TensorProduct
