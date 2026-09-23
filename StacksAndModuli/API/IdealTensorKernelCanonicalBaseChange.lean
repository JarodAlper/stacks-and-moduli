module

public import StacksAndModuli.API.IdealTensorKernelConnectingFormula
public import StacksAndModuli.API.IdealTensorKernelMap

/-!
# Canonical base change of ideal-tensor kernels

For a ring map carrying an ideal `I` into an ideal `J`, the canonical one-tensor map on a
module induces a map between the corresponding ideal-multiplication kernels.  This file
identifies that canonical map with the presentation-theoretic 00MO comparison.  The
identification supplies the zero-compatibility needed in the finite-obstruction proof of
Stacks Project tag 00R6.
-/

@[expose] public section

open TensorProduct Function LinearMap

universe u v

namespace TensorProduct

/-- The canonical semilinear map from a module to its scalar extension. -/
def oneTensorSemilinear
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] :
    M →ₛₗ[algebraMap R S] S ⊗[R] M where
  toFun m := 1 ⊗ₜ[R] m
  map_add' x y := TensorProduct.tmul_add (1 : S) x y
  map_smul' r m := by
    change (1 : S) ⊗ₜ[R] (r • m) =
      algebraMap R S r • ((1 : S) ⊗ₜ[R] m)
    calc
      (1 : S) ⊗ₜ[R] (r • m) = (r • (1 : S)) ⊗ₜ[R] m :=
        TensorProduct.tmul_smul r (1 : S) m
      _ = (algebraMap R S r * (1 : S)) ⊗ₜ[R] m := by
        exact congrArg (fun s : S ↦ s ⊗ₜ[R] m)
          (_root_.Algebra.smul_def (R := R) (A := S) r (1 : S))
      _ = (algebraMap R S r • (1 : S)) ⊗ₜ[R] m := by
        rw [smul_eq_mul]
      _ = algebraMap R S r • ((1 : S) ⊗ₜ[R] m) :=
        (TensorProduct.smul_tmul' (algebraMap R S r) (1 : S) m).symm

@[simp]
theorem oneTensorSemilinear_apply
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] (m : M) :
    oneTensorSemilinear (R := R) (S := S) m = 1 ⊗ₜ[R] m := rfl

end TensorProduct

namespace Ideal

variable {R R' : Type u} {M : Type v} [CommRing R] [CommRing R'] [Algebra R R']
variable [AddCommGroup M] [Module R M]

/-- Canonical coefficient base change with the ideal in the left tensor factor. -/
def leftTensorBaseChangeMap (I : Ideal R) (J : Ideal R')
    (hIJ : I ≤ J.comap (algebraMap R R')) :
    I ⊗[R] M →+ J ⊗[R'] (R' ⊗[R] M) :=
  (TensorProduct.comm R' (R' ⊗[R] M) J).toLinearMap.toAddMonoidHom.comp <|
    (tensorMap (algebraMap R R') (algebraMap R R')
      (by ext r; simp)
      (TensorProduct.oneTensorSemilinear (R := R) (S := R') (M := M))
      I J (fun x ↦ show algebraMap R R' x.1 ∈ J from hIJ x.2)).toAddMonoidHom.comp <|
        (TensorProduct.comm R I M).toLinearMap.toAddMonoidHom

@[simp]
theorem leftTensorBaseChangeMap_tmul (I : Ideal R) (J : Ideal R')
    (hIJ : I ≤ J.comap (algebraMap R R')) (i : I) (m : M) :
    leftTensorBaseChangeMap I J hIJ (i ⊗ₜ[R] m) =
      (⟨algebraMap R R' i.1, hIJ i.2⟩ : J) ⊗ₜ[R']
        ((1 : R') ⊗ₜ[R] m) := by
  change (TensorProduct.comm R' (R' ⊗[R] M) J)
      (tensorMap (algebraMap R R') (algebraMap R R')
        (by ext r; simp)
        (TensorProduct.oneTensorSemilinear (R := R) (S := R') (M := M))
        I J (fun x ↦ show algebraMap R R' x.1 ∈ J from hIJ x.2)
        (m ⊗ₜ[R] i)) = _
  rw [tensorMap_tmul, TensorProduct.comm_tmul]
  rfl

/-- Base change of left-oriented tensors is natural in the module. -/
theorem lTensor_leftTensorBaseChangeMap
    {N : Type v} [AddCommGroup N] [Module R N]
    (q : M →ₗ[R] N) (I : Ideal R) (J : Ideal R')
    (hIJ : I ≤ J.comap (algebraMap R R')) (x : I ⊗[R] M) :
    (q.baseChange R').lTensor J (leftTensorBaseChangeMap I J hIJ x) =
      leftTensorBaseChangeMap I J hIJ (q.lTensor I x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (.+.) hx hy
  | tmul i m =>
      simp [leftTensorBaseChangeMap_tmul, LinearMap.baseChange_tmul]

/-- Ideal multiplication commutes with canonical coefficient base change. -/
theorem leftTensorMul_leftTensorBaseChangeMap
    (I : Ideal R) (J : Ideal R')
    (hIJ : I ≤ J.comap (algebraMap R R')) (x : I ⊗[R] M) :
    leftTensorMul (M := R' ⊗[R] M) J
        (leftTensorBaseChangeMap I J hIJ x) =
      TensorProduct.oneTensorSemilinear (R := R) (S := R')
        (leftTensorMul (M := M) I x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (.+.) hx hy
  | tmul i m =>
      simp [leftTensorBaseChangeMap_tmul, leftTensorMul_tmul]

/-- Ideal multiplication is natural in the module map. -/
theorem map_leftTensorMul
    {N : Type v} [AddCommGroup N] [Module R N]
    (q : M →ₗ[R] N) (I : Ideal R) (x : I ⊗[R] M) :
    q (leftTensorMul (M := M) I x) =
      leftTensorMul (M := N) I (q.lTensor I x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (.+.) hx hy
  | tmul i m => simp [leftTensorMul_tmul]

/-- The canonical base-change map on ideal-multiplication kernels. -/
def tensorMulKerBaseChangeMap (I : Ideal R) (J : Ideal R')
    (hIJ : I ≤ J.comap (algebraMap R R')) :
    LinearMap.ker (tensorMul (R := R) (S := R) (M := M) I) →+
      LinearMap.ker (tensorMul (R := R') (S := R')
        (M := R' ⊗[R] M) J) :=
  tensorMulKerMap (algebraMap R R') (algebraMap R R')
    (by ext r; simp)
    (TensorProduct.oneTensorSemilinear (R := R) (S := R') (M := M))
    I J (fun x ↦ show algebraMap R R' x.1 ∈ J from hIJ x.2)

/-- The underlying tensor of the canonical kernel base-change map is the tensor-product map
induced by the coefficient map and the one-tensor module map. -/
@[simp]
theorem tensorMulKerBaseChangeMap_val (I : Ideal R) (J : Ideal R')
    (hIJ : I ≤ J.comap (algebraMap R R'))
    (x : LinearMap.ker (tensorMul (R := R) (S := R) (M := M) I)) :
    (tensorMulKerBaseChangeMap I J hIJ x).1 =
      tensorMap (algebraMap R R') (algebraMap R R')
        (by ext r; simp)
        (TensorProduct.oneTensorSemilinear (R := R) (S := R') (M := M))
        I J (fun y ↦ show algebraMap R R' y.1 ∈ J from hIJ y.2) x.1 := rfl

/-- Switching the ideal to the left identifies the canonical kernel base-change map with
`leftTensorBaseChangeMap`. -/
theorem tensorMulKerEquivLeft_baseChangeMap_val
    (I : Ideal R) (J : Ideal R')
    (hIJ : I ≤ J.comap (algebraMap R R'))
    (x : LinearMap.ker (tensorMul (R := R) (S := R) (M := M) I)) :
    (tensorMulKerEquivLeft J (tensorMulKerBaseChangeMap I J hIJ x)).1 =
      leftTensorBaseChangeMap I J hIJ (tensorMulKerEquivLeft I x).1 := by
  simp [tensorMulKerEquivLeft, tensorMulKerBaseChangeMap,
    leftTensorBaseChangeMap]

/-- The canonical ideal-kernel base-change map has the same presentation value as the
00MO comparison: the pure tensor of the base-changed relation vector. -/
theorem tensorMulKerBaseChangeMap_presentation_val_of_lifts
    {F : Type v} [AddCommGroup F] [Module R F] [Module.Flat R F]
    (q : F →ₗ[R] M) (hq : Function.Surjective q)
    (I : Ideal R) (J : Ideal R')
    (hIJ : I ≤ J.comap (algebraMap R R'))
    (x : LinearMap.ker (tensorMul (R := R) (S := R) (M := M) I))
    (y : I ⊗[R] F)
    (hy : q.lTensor I y = (tensorMulKerEquivLeft I x).1)
    (z : LinearMap.ker q)
    (hz : z.1 = leftTensorMul (M := F) I y) :
    let q' := q.baseChange R'
    let hq' : Function.Surjective q' := LinearMap.lTensor_surjective R' hq
    (tensorMulKerPresentationBaseChangeLinearEquiv q' hq' J
      (tensorMulKerBaseChangeMap I J hIJ x)).1 =
        (1 : R' ⧸ J) ⊗ₜ[R']
          q.kerBaseChangeHom R' ((1 : R') ⊗ₜ[R] z) := by
  let q' := q.baseChange R'
  let hq' : Function.Surjective q' := LinearMap.lTensor_surjective R' hq
  let x' := tensorMulKerBaseChangeMap I J hIJ x
  let y' := leftTensorBaseChangeMap (M := F) I J hIJ y
  let z' := q.kerBaseChangeHom R' ((1 : R') ⊗ₜ[R] z)
  have hy' : q'.lTensor J y' = (tensorMulKerEquivLeft J x').1 := by
    calc
      q'.lTensor J y' =
          leftTensorBaseChangeMap I J hIJ (q.lTensor I y) :=
        lTensor_leftTensorBaseChangeMap q I J hIJ y
      _ = leftTensorBaseChangeMap I J hIJ (tensorMulKerEquivLeft I x).1 :=
        congrArg (leftTensorBaseChangeMap I J hIJ) hy
      _ = (tensorMulKerEquivLeft J x').1 := by
        exact (tensorMulKerEquivLeft_baseChangeMap_val I J hIJ x).symm
  have hz' : z'.1 = leftTensorMul (M := R' ⊗[R] F) J y' := by
    calc
      z'.1 = (1 : R') ⊗ₜ[R] z.1 := by
        simp [z', LinearMap.kerBaseChangeHom, LinearMap.baseChange_tmul]
      _ = (1 : R') ⊗ₜ[R] leftTensorMul (M := F) I y :=
        congrArg (fun f : F ↦ (1 : R') ⊗ₜ[R] f) hz
      _ = leftTensorMul (M := R' ⊗[R] F) J y' :=
        (leftTensorMul_leftTensorBaseChangeMap
          (M := F) I J hIJ y).symm
  exact tensorMulKerPresentationBaseChangeLinearEquiv_val_of_lifts
    q' hq' J x' y' hy' z' hz'

/-- The presentation-theoretic 00MO comparison is the canonical base-change map on actual
ideal-multiplication kernels. -/
theorem tensorMulKerLocalComparison_eq_baseChangeMap
    {F : Type v} [AddCommGroup F] [Module R F] [Module.Flat R F]
    (q : F →ₗ[R] M) (hq : Function.Surjective q)
    (I : Ideal R) (J : Ideal R')
    (hIJ : I ≤ J.comap (algebraMap R R')) :
    tensorMulKerLocalComparison q hq I J hIJ =
      tensorMulKerBaseChangeMap I J hIJ := by
  apply AddMonoidHom.ext
  intro x
  let xL := tensorMulKerEquivLeft I x
  obtain ⟨y, hy⟩ := LinearMap.lTensor_surjective I hq xL.1
  let z : LinearMap.ker q := ⟨leftTensorMul (M := F) I y, by
    change q (leftTensorMul (M := F) I y) = 0
    rw [map_leftTensorMul q I y, hy]
    exact xL.2⟩
  have hz : z.1 = leftTensorMul (M := F) I y := rfl
  let q' := q.baseChange R'
  let hq' : Function.Surjective q' := LinearMap.lTensor_surjective R' hq
  let e' := tensorMulKerPresentationBaseChangeLinearEquiv q' hq' J
  apply e'.injective
  apply Subtype.ext
  have hlocal := tensorMulKerLocalComparison_presentation_val_of_lifts
    q hq I J hIJ x y hy z hz
  have hcanonical := tensorMulKerBaseChangeMap_presentation_val_of_lifts
    q hq I J hIJ x y hy z hz
  exact hlocal.trans hcanonical.symm

/-- Under the closed-fibre flatness hypothesis of 00MO, the canonical ideal-kernel
base-change map spans the target kernel. -/
theorem span_range_tensorMulKerBaseChangeMap
    {F : Type v} [AddCommGroup F] [Module R F] [Module.Flat R F]
    (q : F →ₗ[R] M) (hq : Function.Surjective q)
    (I : Ideal R) (J : Ideal R')
    (hIJ : I ≤ J.comap (algebraMap R R'))
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)] :
    Submodule.span R' (Set.range
      (tensorMulKerBaseChangeMap (M := M) I J hIJ)) = ⊤ := by
  rw [← tensorMulKerLocalComparison_eq_baseChangeMap q hq I J hIJ]
  exact span_range_tensorMulKerLocalComparison q hq I J hIJ

end Ideal
