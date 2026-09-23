module

public import StacksAndModuli.API.NoetherianTorKernelFinite
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Flat base change of ideal multiplication

Let `R → S → T`, let `M` be an `S`-module, and let `I ⊆ R`.  Ideal multiplication on
`T ⊗[S] M` is the scalar extension to `T` of ideal multiplication on `M`, after the
canonical reassociation of tensor products.  Consequently, injectivity of ideal
multiplication is preserved by a flat extension `S → T`.

This is the localization step used after the finite obstruction has been killed in the
Noetherian approximation argument of Stacks Project tag 00R6.
-/

@[expose] public section

open TensorProduct Function LinearMap

universe u v

namespace Ideal

variable {R S T : Type u} {M : Type v}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Ideal multiplication after scalar extension agrees with the base-changed multiplication
map through the canonical tensor reassociation. -/
theorem tensorMul_baseChange_comp_assoc (I : Ideal R) :
    tensorMul (R := R) (S := T) (M := T ⊗[S] M) I =
      (tensorMul (R := R) (S := S) (M := M) I).baseChange T ∘ₗ
        (AlgebraTensorModule.assoc R S T T M I).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro z i
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [add_tmul, map_add, hx, hy]
  | tmul t m =>
      change (i : R) • (t ⊗ₜ[S] m) =
        (tensorMul (R := R) (S := S) (M := M) I).baseChange T
          (AlgebraTensorModule.assoc R S T T M I ((t ⊗ₜ[S] m) ⊗ₜ[R] i))
      rw [AlgebraTensorModule.assoc_tmul, baseChange_tmul, tensorMul_tmul]
      calc
        ((i : R) • t) ⊗ₜ[S] m =
            (algebraMap R S (i : R) • t) ⊗ₜ[S] m := by
          rw [IsScalarTower.algebraMap_smul S]
        _ = t ⊗ₜ[S] (algebraMap R S (i : R) • m) :=
          TensorProduct.smul_tmul _ _ _
        _ = t ⊗ₜ[S] ((i : R) • m) := by
          rw [IsScalarTower.algebraMap_smul S]

/-- Injectivity of ideal multiplication is preserved by flat scalar extension of the
auxiliary algebra. -/
theorem tensorMul_injective_baseChange [Module.Flat S T] (I : Ideal R)
    (h : Function.Injective (tensorMul (R := R) (S := S) (M := M) I)) :
    Function.Injective (tensorMul (R := R) (S := T) (M := T ⊗[S] M) I) := by
  rw [tensorMul_baseChange_comp_assoc]
  exact (Module.Flat.lTensor_preserves_injective_linearMap
      (tensorMul (R := R) (S := S) (M := M) I) h).comp
    (AlgebraTensorModule.assoc R S T T M I).injective

end Ideal
