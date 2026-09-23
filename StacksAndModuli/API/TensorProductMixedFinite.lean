module

public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finiteness of a mixed-base tensor product

If `R → S`, an `S`-finite module tensored over `R` with an `R`-finite module is
again `S`-finite.  The `S`-action is supplied by the left tensor factor.

This elementary result is useful in the Artin--Rees proof of the Noetherian local
flatness criterion: if `M` is finite over `S` and `I` is an ideal of the Noetherian
base ring `R`, then `M ⊗[R] I` is finite over `S`.
-/

@[expose] public section

open TensorProduct

universe uR uS uM uN

namespace Module.Finite

variable {R : Type uR} {S : Type uS} {M : Type uM} {N : Type uN}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module R N]

/-- An `S`-finite module tensored over `R` on the right with an `R`-finite module
is finite over `S`.

The tensor product carries its `S`-action through the left factor `M`. -/
theorem tensorProduct_of_scalarTower [Module.Finite S M] [Module.Finite R N] :
    Module.Finite S (M ⊗[R] N) := by
  classical
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R N
  let b : Fin n → (Fin n → R) := fun k a => if a = k then 1 else 0
  let f : (Fin n → M) →ₗ[S] M ⊗[R] N :=
    { toFun := fun x => ∑ i, x i ⊗ₜ[R] q (b i)
      map_add' := fun x y => by simp [add_tmul, Finset.sum_add_distrib]
      map_smul' := fun s x => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun _ _ => TensorProduct.smul_tmul' _ _ _ |>.symm }
  have hf : Function.Surjective f := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp [f]⟩
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', by simp⟩
    | tmul m y =>
      obtain ⟨v, rfl⟩ := hq y
      refine ⟨fun i => algebraMap R S (v i) • m, ?_⟩
      change (∑ i, (algebraMap R S (v i) • m) ⊗ₜ[R] q (b i)) = m ⊗ₜ[R] q v
      simp_rw [IsScalarTower.algebraMap_smul S, TensorProduct.smul_tmul, ← q.map_smul]
      rw [← TensorProduct.tmul_sum, ← map_sum q]
      congr 1
      apply congrArg q
      funext a
      simp [b]
  exact Module.Finite.of_surjective f hf

end Module.Finite
