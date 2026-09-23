module

public import StacksAndModuli.«Section3.1-Descent».«part3.1.1-modules»
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The full Amitsur complex

This module formalizes Exercise 3.1.3 (`exer:descent-long-exact-sequence`) of §3.1
of *Stacks and Moduli*. For a faithfully flat ring map `R → S`, it extends the
degree-zero equalizer of Proposition 3.1.1 to the exact Amitsur complex
`0 → M → S ⊗[R] M → S ⊗[R] S ⊗[R] M → ⋯`.

The book's displayed summation has an indexing typo: in degree `n` there are `n + 1`
insertion positions, indexed `0, …, n`, rather than `0, …, n + 1`. The recursive
differential below is precisely that corrected alternating insertion sum.
-/

@[expose] public section

-- Recursive `ModuleCat` carriers need the historical transparent-defeq behaviour.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExerDescentLongExactSequence

open TensorProduct LinearMap

universe u

namespace Module.FaithfullyFlat.Amitsur

variable (R : Type u) (S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- Background definition for Exercise 3.1.3 (terms): the degree-`n`
term of the Amitsur complex, written with tensor factors associated to the left of `M`.
Thus `Term R S M n` is `S ⊗[R] ⋯ ⊗[R] S ⊗[R] M`, with `n` copies of `S`. -/
@[reducible] noncomputable def Term (R : Type u) (S : Type u)
    [CommRing R] [CommRing S] [Algebra R S]
    (M : Type u) [AddCommGroup M] [Module R M] : ℕ → ModuleCat R
  | 0 => ModuleCat.of R M
  | n + 1 => ModuleCat.of R (S ⊗[R] (Term R S M n : Type u))

/-- Background definition for Exercise 3.1.3 (differential): the
alternating insertion-of-`1` differential. Recursively, `d 0 m = 1 ⊗ m` and
`d (n + 1) x = 1 ⊗ x - (1 ⊗ d n)(x)`, which expands to the alternating sum over the
`n + 1` possible insertion positions in degree `n`. -/
noncomputable def d : (n : ℕ) → (Term R S M n →ₗ[R] Term R S M (n + 1))
  | 0 => by
      change M →ₗ[R] S ⊗[R] M
      exact TensorProduct.mk R S M 1
  | n + 1 => by
      change (S ⊗[R] Term R S M n) →ₗ[R] S ⊗[R] (S ⊗[R] Term R S M n)
      let q := LinearMap.lTensor S (d n)
      change (S ⊗[R] Term R S M n) →ₗ[R]
        S ⊗[R] (S ⊗[R] Term R S M n) at q
      exact TensorProduct.mk R S (S ⊗[R] Term R S M n) 1 - q

@[simp]
lemma d_zero : d R S M 0 = TensorProduct.mk R S M 1 := rfl

lemma contractLeft_naturality {N : Type u} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    (Algebra.TensorProduct.contractLeft R S N).comp
        (LinearMap.lTensor S (LinearMap.lTensor S f)) =
      (LinearMap.lTensor S f).comp (Algebra.TensorProduct.contractLeft R S M) := by
  ext s s' m
  simp [Algebra.TensorProduct.contractLeft]

lemma contractLeft_comp_lTensor_mk_general :
    (Algebra.TensorProduct.contractLeft R S M).comp
        (LinearMap.lTensor S (TensorProduct.mk R S M 1)) = LinearMap.id := by
  ext s m
  simp [Algebra.TensorProduct.contractLeft]

lemma lTensor_d_succ_apply (n : ℕ)
    (x : S ⊗[R] Term R S M (n + 1)) :
    LinearMap.lTensor S (d R S M (n + 1)) x =
      LinearMap.lTensor S (TensorProduct.mk R S (Term R S M (n + 1)) 1) x -
        LinearMap.lTensor S (LinearMap.lTensor S (d R S M n)) x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, sub_zero]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]; abel
  | tmul s y =>
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
      change s ⊗ₜ[R] ((1 : S) ⊗ₜ[R] y - LinearMap.lTensor S (d R S M n) y) = _
      rw [TensorProduct.tmul_sub]
      rfl

lemma d_succ_apply (n : ℕ) (x : Term R S M (n + 1)) :
    d R S M (n + 1) x =
      TensorProduct.mk R S (Term R S M (n + 1)) 1 x -
        LinearMap.lTensor S (d R S M n) x := by
  rfl

lemma d_comp_d (n : ℕ) :
    (d R S M (n + 1)).comp (d R S M n) = 0 := by
  induction n with
  | zero =>
      ext m
      simp only [LinearMap.comp_apply, LinearMap.zero_apply]
      simp [d, Term]
  | succ n ih =>
      simp [d] at ih ⊢
      ext s x
      simp only [TensorProduct.AlgebraTensorModule.curry_apply,
        TensorProduct.curry_apply, LinearMap.restrictScalars_apply,
        LinearMap.comp_apply, LinearMap.sub_apply, TensorProduct.mk_apply,
        LinearMap.lTensor_tmul, TensorProduct.tmul_sub, LinearMap.zero_apply]
      simp only [map_sub, LinearMap.lTensor_tmul, TensorProduct.mk_apply]
      have hx := LinearMap.congr_fun ih x
      simp only [LinearMap.comp_apply, LinearMap.sub_apply,
        TensorProduct.mk_apply, LinearMap.zero_apply] at hx
      abel_nf
      have hgoal : s ⊗ₜ[R] ((1 : S) ⊗ₜ[R] (d R S M n) x) -
          s ⊗ₜ[R] (LinearMap.lTensor S (d R S M n)) ((d R S M n) x) = 0 := by
        rw [← TensorProduct.tmul_sub, hx, TensorProduct.tmul_zero]
      simpa only [sub_eq_add_neg, neg_one_smul] using hgoal

lemma lTensor_d_comp_d (n : ℕ) :
    (LinearMap.lTensor S (d R S M (n + 1))).comp
      (LinearMap.lTensor S (d R S M n)) = 0 := by
  rw [← LinearMap.lTensor_comp, d_comp_d, LinearMap.lTensor_zero]

lemma lTensor_d_exact (n : ℕ) :
    Function.Exact (LinearMap.lTensor S (d R S M n))
      (LinearMap.lTensor S (d R S M (n + 1))) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · exact lTensor_d_comp_d R S M n
  · intro x hx
    refine ⟨Algebra.TensorProduct.contractLeft R S (Term R S M n) x, ?_⟩
    have h := hx
    rw [lTensor_d_succ_apply] at h
    have hEq :
        LinearMap.lTensor S (TensorProduct.mk R S (Term R S M (n + 1)) 1) x =
          LinearMap.lTensor S (LinearMap.lTensor S (d R S M n)) x := sub_eq_zero.mp h
    have h' := congrArg (Algebra.TensorProduct.contractLeft R S (Term R S M (n + 1))) hEq
    simpa only [← LinearMap.comp_apply,
      contractLeft_comp_lTensor_mk_general,
      contractLeft_naturality, LinearMap.id_apply] using h'.symm

variable [Module.FaithfullyFlat R S]

/-- Helper lemma used in the proof of Exercise 3.1.3 (exactness at degree
`n + 1`): consecutive alternating insertion differentials have image equal to kernel. -/
theorem exact (n : ℕ) :
    Function.Exact (d R S M n) (d R S M (n + 1)) := by
  apply Module.FaithfullyFlat.lTensor_reflects_exact R S
  exact lTensor_d_exact R S M n

/-- API lemma derived from Exercise 3.1.3 (exactness at degree zero):
the first differential `M → S ⊗[R] M`, `m ↦ 1 ⊗ m`, is injective. -/
theorem injective_d_zero : Function.Injective (d R S M 0) := by
  exact Module.FaithfullyFlat.tensorProduct_mk_injective M

/-- **Exercise 3.1.3** (`exer:descent-long-exact-sequence`): for a faithfully flat
`R`-algebra `S`, the full Amitsur sequence
`0 → M → S ⊗[R] M → S ⊗[R] S ⊗[R] M → ⋯` is exact. -/
theorem longExactSequence :
    Function.Injective (d R S M 0) ∧
      ∀ n, Function.Exact (d R S M n) (d R S M (n + 1)) := by
  exact ⟨injective_d_zero R S M, exact R S M⟩

end Module.FaithfullyFlat.Amitsur

end ExerDescentLongExactSequence
