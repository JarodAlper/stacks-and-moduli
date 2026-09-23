module

public import StacksAndModuli.API.KernelFlatnessCriterion
public import StacksAndModuli.API.NoetherianLocalFlatnessCriterion
public import StacksAndModuli.API.TensorProductMixedFinite
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of ideal-tensor kernels over a Noetherian algebra

Let `R → S`, let `M` be an `S`-module, and let `I` be an ideal of `R`.  The multiplication
map `M ⊗[R] I → M` is `S`-linear.  If both rings are Noetherian and `M` is finite over
`S`, its kernel is finite over `S`.

For `I = maximalIdeal R`, this is the finite obstruction module used in the proof of Stacks
Project tag 00R6.  The file also identifies injectivity of this multiplication map with the
`rTensor` formulation consumed by the local flatness criterion.
-/

@[expose] public section

open TensorProduct

universe uR uS uM

namespace Ideal

variable {R : Type uR} {S : Type uS} {M : Type uM}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- The `S`-linear ideal multiplication map `M ⊗[R] I → M`. -/
def tensorMul (I : Ideal R) : M ⊗[R] I →ₗ[S] M where
  toFun z := (TensorProduct.lid R M)
    ((I.subtype.rTensor M) ((TensorProduct.comm R M I) z))
  map_add' x y := by simp
  map_smul' s z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul m i =>
      simp only [TensorProduct.smul_tmul', TensorProduct.comm_tmul,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
      rw [smul_comm]
      rfl

@[simp]
theorem tensorMul_tmul (I : Ideal R) (m : M) (i : I) :
    tensorMul (R := R) (S := S) (M := M) I (m ⊗ₜ[R] i) = (i : R) • m := by
  simp [tensorMul]

/-- Injectivity of ideal multiplication is equivalent to injectivity of the `rTensor`
map used by `Module.Flat.iff_rTensor_injective'`. -/
theorem tensorMul_injective_iff_rTensor_injective (I : Ideal R) :
    Function.Injective (tensorMul (R := R) (S := S) (M := M) I) ↔
      Function.Injective (I.subtype.rTensor M) := by
  constructor
  · intro h x y hxy
    let x' := (TensorProduct.comm R M I).symm x
    let y' := (TensorProduct.comm R M I).symm y
    have hxy' : tensorMul (R := R) (S := S) (M := M) I x' =
        tensorMul (R := R) (S := S) (M := M) I y' := by
      change (TensorProduct.lid R M)
          ((I.subtype.rTensor M) ((TensorProduct.comm R M I) x')) =
        (TensorProduct.lid R M)
          ((I.subtype.rTensor M) ((TensorProduct.comm R M I) y'))
      rw [show (TensorProduct.comm R M I) x' = x by simp [x'],
        show (TensorProduct.comm R M I) y' = y by simp [y'], hxy]
    have := h hxy'
    exact (TensorProduct.comm R M I).symm.injective this
  · intro h x y hxy
    apply (TensorProduct.comm R M I).injective
    apply h
    apply (TensorProduct.lid R M).injective
    exact hxy

/-- Over Noetherian `R` and `S`, the kernel of ideal multiplication on an `S`-finite
module is finite over `S`. -/
theorem finite_ker_tensorMul [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Finite S M] (I : Ideal R) :
    Module.Finite S
      (LinearMap.ker (tensorMul (R := R) (S := S) (M := M) I)) := by
  let _ : Module.Finite R I :=
    Module.Finite.of_fg (IsNoetherian.noetherian (R := R) I)
  let _ : Module.Finite S (M ⊗[R] I) :=
    Module.Finite.tensorProduct_of_scalarTower (R := R) (S := S) (M := M) (N := I)
  exact Module.Finite.of_fg
    (IsNoetherian.noetherian (R := S)
      (LinearMap.ker (tensorMul (R := R) (S := S) (M := M) I)))

end Ideal

namespace Module.Flat

variable {R S M : Type uR} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsLocalRing R]
variable [IsNoetherianRing S] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [AddCommGroup M] [Module R M] [Module S M]
variable [IsScalarTower R S M] [Module.Finite S M]

/-- Ideal-multiplication form of the variant local flatness criterion. -/
theorem of_tensorMul_injective_of_quotient_flat
    (I : Ideal R) (hIproper : I ≠ ⊤)
    (hI : Function.Injective (Ideal.tensorMul (S := S) (M := M) I))
    [Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] :
    Module.Flat R M := by
  apply Module.Flat.of_maximalIdeal_rTensor_injective_of_finite S
  apply LinearMap.maximalIdeal_rTensor_injective_of_ideal_of_flat_quotient
    I hIproper
  exact (Ideal.tensorMul_injective_iff_rTensor_injective (S := S) I).mp hI

end Module.Flat
