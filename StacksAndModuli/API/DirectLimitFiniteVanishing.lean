module

public import Mathlib.Algebra.Colimit.Module
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite-stage vanishing in a directed colimit

If finitely many elements of one stage die in a directed colimit, they all die after one
common transition.  Consequently, a map from a finite module that becomes zero in the
colimit is already zero at a finite stage.

This is the finite-generator colimit step in the flatness-spreading argument of Stacks
Project tag 00R6.  It is independent of the local flatness criterion used after that step.
-/

@[expose] public section

universe u v w

namespace Module.DirectLimit

variable {R : Type u} [Ring R] {ι : Type v} [DecidableEq ι]
  [Preorder ι] [IsDirectedOrder ι]
  {G : ι → Type w} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  {f : ∀ i j, i ≤ j → G i →ₗ[R] G j}
  [DirectedSystem G fun i j h => f i j h]

/-- Finitely many elements which vanish in a directed colimit vanish simultaneously after
one transition. -/
theorem exists_later_forall_fin_eq_zero {i : ι} {n : ℕ} (x : Fin n → G i)
    (hx : ∀ k, of R ι G f i (x k) = 0) :
    ∃ j, ∃ hij : i ≤ j, ∀ k, f i j hij (x k) = 0 := by
  classical
  have haux : ∀ s : Finset (Fin n),
      ∃ j, ∃ hij : i ≤ j, ∀ k ∈ s, f i j hij (x k) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨i, le_rfl, by simp⟩
    | @insert k s hks ih =>
      obtain ⟨j, hij, hj⟩ := ih
      obtain ⟨j', hij', hj'⟩ := of.zero_exact (hx k)
      obtain ⟨t, hjt, hj't⟩ := exists_ge_ge j j'
      refine ⟨t, hij.trans hjt, ?_⟩
      intro a ha
      rw [Finset.mem_insert] at ha
      rcases ha with rfl | ha
      · rw [← DirectedSystem.map_map (f := fun i j h => f i j h) hij' hj't]
        simp [hj']
      · rw [← DirectedSystem.map_map (f := fun i j h => f i j h) hij hjt]
        simp [hj a ha]
  obtain ⟨j, hij, hj⟩ := haux Finset.univ
  exact ⟨j, hij, fun k => hj k (Finset.mem_univ k)⟩

/-- A linear map from a finite module which becomes zero in a directed colimit is already
zero after one transition. -/
theorem exists_later_comp_eq_zero_of_finite {N : Type w} [AddCommGroup N]
    [Module R N] [Module.Finite R N] {i : ι} (g : N →ₗ[R] G i)
    (hg : (of R ι G f i).comp g = 0) :
    ∃ j, ∃ hij : i ≤ j, (f i j hij).comp g = 0 := by
  classical
  obtain ⟨n, q, hq⟩ := Module.Finite.exists_fin' R N
  let b : Fin n → (Fin n → R) := fun k a => if a = k then 1 else 0
  have hb : ∀ k, of R ι G f i (g (q (b k))) = 0 := by
    intro k
    have := LinearMap.congr_fun hg (q (b k))
    simpa using this
  obtain ⟨j, hij, hj⟩ :=
    exists_later_forall_fin_eq_zero (f := f) (fun k => g (q (b k))) hb
  refine ⟨j, hij, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := hq x
  change f i j hij (g (q y)) = 0
  have hy : y = ∑ k, y k • b k := by
    funext a
    simp [b]
  rw [hy, map_sum]
  simp [hj]

/-- A linear map from a finite module is killed at one common stage if each of its values is
killed at some (value-dependent) later stage. -/
theorem exists_later_comp_eq_zero_of_finite_of_eventually
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Finite R N]
    {i : ι} (g : N →ₗ[R] G i)
    (hg : ∀ x, ∃ j, ∃ hij : i ≤ j, f i j hij (g x) = 0) :
    ∃ j, ∃ hij : i ≤ j, (f i j hij).comp g = 0 := by
  apply exists_later_comp_eq_zero_of_finite g
  apply LinearMap.ext
  intro x
  obtain ⟨j, hij, hx⟩ := hg x
  change of R ι G f i (g x) = 0
  rw [← of_f (hij := hij), hx, map_zero]

/-- A finite submodule of one stage which maps to zero in a directed colimit is killed by
one transition map.  This is the form used for a finitely generated `Tor₁` kernel. -/
theorem exists_later_subtype_comp_eq_zero_of_finite {i : ι} (K : Submodule R (G i))
    [Module.Finite R K]
    (hK : (of R ι G f i).comp K.subtype = 0) :
    ∃ j, ∃ hij : i ≤ j, (f i j hij).comp K.subtype = 0 :=
  exists_later_comp_eq_zero_of_finite K.subtype hK

end Module.DirectLimit

end
