module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Minimal growth for polynomial-vector subspaces

This file isolates the elementary growth-one case of the linear-algebra input behind
Gotzmann persistence on the projective line.  For an injective endomorphism `f`, write
`V.forwardSpan f` for `V + f(V)`.  If this first span has dimension one more than `V`,
then the next span has dimension at most one more.  Equality follows as soon as the
first span is not `f`-invariant.

For polynomial vectors, coordinatewise multiplication by `X` has no nonzero invariant
subspace whose elements have uniformly bounded degree.  Consequently minimal growth by
one persists for one further step.  The result is valid over every field and for every
coefficient index type; in particular, it introduces neither an infinitude hypothesis on
the field nor a rank-one hypothesis on the polynomial vectors.

This is the first non-tautological numerical boundary case beyond the zero and full-ambient
Gotzmann seed bounds.  Growth by more than one requires a genuine Macaulay compression
inequality and is not addressed here.

Main declarations:

* `Submodule.forwardSpan`;
* `Submodule.finrank_forwardSpan_le_add_one_of_eq_add_one`;
* `Polynomial.xMulVector`;
* `Polynomial.vectorDegreeLT`;
* `Polynomial.finrank_forwardSpan_xMulVector_eq_add_one`.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

namespace Submodule

variable {K M M₂ : Type*} [DivisionRing K]
  [AddCommGroup M] [Module K M] [AddCommGroup M₂] [Module K M₂]

/-- The span of a submodule and its image under a linear endomorphism. -/
abbrev forwardSpan (V : Submodule K M) (f : M →ₗ[K] M) : Submodule K M :=
  V ⊔ V.map f

/-- An injective endomorphism preserves the dimension of a finite-dimensional
submodule. -/
lemma finrank_map_eq_of_injective (V : Submodule K M) [FiniteDimensional K V]
    (f : M →ₗ[K] M₂) (hf : Function.Injective f) :
    Module.finrank K (V.map f) = Module.finrank K V :=
  (Submodule.equivMapOfInjective f hf V).finrank_eq.symm

/-- If adjoining the image of a finite-dimensional subspace under an injective
endomorphism increases dimension by one, doing so once more increases dimension by at
most one. -/
theorem finrank_forwardSpan_le_add_one_of_eq_add_one
    (V : Submodule K M) [FiniteDimensional K V]
    (f : M →ₗ[K] M) (hf : Function.Injective f)
    (hgrowth : Module.finrank K (V.forwardSpan f) = Module.finrank K V + 1) :
    Module.finrank K ((V.forwardSpan f).forwardSpan f) ≤
      Module.finrank K (V.forwardSpan f) + 1 := by
  let W := V.forwardSpan f
  letI : FiniteDimensional K (V.map f) := Module.Finite.map V f
  letI : FiniteDimensional K W := by
    dsimp only [W, forwardSpan]
    exact Submodule.finiteDimensional_sup V (V.map f)
  letI : FiniteDimensional K (W.map f) := Module.Finite.map W f
  have hVmap : Module.finrank K (V.map f) = Module.finrank K V :=
    finrank_map_eq_of_injective V f hf
  have hWmap : Module.finrank K (W.map f) = Module.finrank K W :=
    finrank_map_eq_of_injective W f hf
  have hVmap_le : V.map f ≤ W ⊓ W.map f := by
    refine le_inf ?_ ?_
    · exact le_sup_right
    · exact Submodule.map_mono le_sup_left
  have hfinrank_le :
      Module.finrank K (V.map f) ≤
        Module.finrank K (W ⊓ W.map f : Submodule K M) :=
    LinearMap.finrank_le_finrank_of_injective
      (f := Submodule.inclusion hVmap_le)
      (Submodule.inclusion_injective hVmap_le)
  have hdimension := Submodule.finrank_sup_add_finrank_inf_eq W (W.map f)
  have hgrowthW : Module.finrank K W = Module.finrank K V + 1 := by
    simpa only [W] using hgrowth
  have hsum :
      Module.finrank K (W.forwardSpan f) + Module.finrank K (V.map f) ≤
        Module.finrank K W + Module.finrank K (W.map f) := by
    calc
      Module.finrank K (W.forwardSpan f) + Module.finrank K (V.map f) ≤
          Module.finrank K (W.forwardSpan f) +
            Module.finrank K (W ⊓ W.map f : Submodule K M) :=
        Nat.add_le_add_left hfinrank_le _
      _ = Module.finrank K W + Module.finrank K (W.map f) := by
        simpa only [forwardSpan] using hdimension
  rw [hVmap, hWmap] at hsum
  change Module.finrank K (W.forwardSpan f) ≤ Module.finrank K W + 1
  apply Nat.le_of_add_le_add_left
  calc
    Module.finrank K V + Module.finrank K (W.forwardSpan f) =
        Module.finrank K (W.forwardSpan f) + Module.finrank K V := Nat.add_comm _ _
    _ ≤ Module.finrank K W + Module.finrank K W := hsum
    _ = Module.finrank K V + (Module.finrank K W + 1) := by omega

/-- Minimal one-step growth persists when the first forward span is not invariant under
the endomorphism. -/
theorem finrank_forwardSpan_eq_add_one_of_eq_add_one_of_not_map_le
    (V : Submodule K M) [FiniteDimensional K V]
    (f : M →ₗ[K] M) (hf : Function.Injective f)
    (hgrowth : Module.finrank K (V.forwardSpan f) = Module.finrank K V + 1)
    (hnotInvariant : ¬ (V.forwardSpan f).map f ≤ V.forwardSpan f) :
    Module.finrank K ((V.forwardSpan f).forwardSpan f) =
      Module.finrank K (V.forwardSpan f) + 1 := by
  let W := V.forwardSpan f
  letI : FiniteDimensional K (V.map f) := Module.Finite.map V f
  letI : FiniteDimensional K W := by
    dsimp only [W, forwardSpan]
    exact Submodule.finiteDimensional_sup V (V.map f)
  letI : FiniteDimensional K (W.map f) := Module.Finite.map W f
  letI : FiniteDimensional K (W.forwardSpan f) := by
    dsimp only [forwardSpan]
    exact Submodule.finiteDimensional_sup W (W.map f)
  have hle : W ≤ W.forwardSpan f := le_sup_left
  have hne : W ≠ W.forwardSpan f := by
    intro h
    apply hnotInvariant
    change W.map f ≤ W
    have himage : W.map f ≤ W.forwardSpan f := le_sup_right
    rw [← h] at himage
    exact himage
  have hlower : Module.finrank K W < Module.finrank K (W.forwardSpan f) :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle hne)
  have hupper := finrank_forwardSpan_le_add_one_of_eq_add_one V f hf hgrowth
  dsimp only [W] at hlower ⊢
  omega

end Submodule

namespace Polynomial

variable (K : Type*) [Field K] (I : Type*)

/-- Coordinatewise multiplication by `X` on polynomial vectors. -/
def xMulVector : (I → K[X]) →ₗ[K] (I → K[X]) :=
  LinearMap.pi fun i ↦
    (LinearMap.mulLeft K X).comp (LinearMap.proj i)

@[simp]
lemma xMulVector_apply (p : I → K[X]) (i : I) :
    xMulVector K I p i = X * p i :=
  rfl

/-- Polynomial vectors all of whose coordinates have degree strictly less than `n`. -/
def vectorDegreeLT (n : ℕ) : Submodule K (I → K[X]) :=
  Submodule.pi Set.univ fun _ ↦ degreeLT K n

@[simp]
lemma mem_vectorDegreeLT {n : ℕ} {p : I → K[X]} :
    p ∈ vectorDegreeLT K I n ↔ ∀ i, p i ∈ degreeLT K n := by
  simp [vectorDegreeLT]

/-- Coordinatewise multiplication by `X` is injective on polynomial vectors. -/
lemma xMulVector_injective : Function.Injective (xMulVector K I) := by
  intro p q hpq
  funext i
  apply mul_left_cancel₀ Polynomial.X_ne_zero
  simpa only [xMulVector_apply] using congrFun hpq i

/-- A nonzero bounded-degree polynomial-vector subspace is not invariant under
coordinatewise multiplication by `X`. -/
lemma xMulVector_map_not_le_of_ne_bot_of_le_vectorDegreeLT
    (V : Submodule K (I → K[X])) (n : ℕ) (hV : V ≠ ⊥)
    (hdegree : V ≤ vectorDegreeLT K I n) :
    ¬ V.map (xMulVector K I) ≤ V := by
  intro hstable
  obtain ⟨p, hpV, hp₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  have hcoordinate : ∃ i, p i ≠ 0 := by
    by_contra! h
    apply hp₀
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hcoordinate
  have hpowers : ∀ m : ℕ, (fun j ↦ X ^ m * p j) ∈ V := by
    intro m
    induction m with
    | zero => simpa using hpV
    | succ m hm =>
        have hmem : xMulVector K I (fun j ↦ X ^ m * p j) ∈ V :=
          hstable (Submodule.mem_map_of_mem hm)
        rw [show (fun j ↦ X ^ (m + 1) * p j) =
            xMulVector K I (fun j ↦ X ^ m * p j) by
          funext j
          simp only [xMulVector_apply, pow_succ', mul_assoc]]
        exact hmem
  have hbounded : X ^ n * p i ∈ degreeLT K n :=
    ((mem_vectorDegreeLT K I).mp (hdegree (hpowers n))) i
  have hproduct : X ^ n * p i ≠ 0 :=
    mul_ne_zero (pow_ne_zero n Polynomial.X_ne_zero) hi
  have hnatDegree : (X ^ n * p i).natDegree < n :=
    (natDegree_lt_iff_degree_lt hproduct).mpr (mem_degreeLT.mp hbounded)
  rw [natDegree_X_pow_mul n hi] at hnatDegree
  omega

/-- For bounded-degree polynomial vectors, growth of the first `X`-span by exactly one
forces the next `X`-span to grow by exactly one as well.  This is the growth-one edge of
the binary module-Gotzmann argument. -/
theorem finrank_forwardSpan_xMulVector_eq_add_one
    (V : Submodule K (I → K[X])) [FiniteDimensional K V] (n : ℕ)
    (hgrowth : Module.finrank K (V.forwardSpan (xMulVector K I)) =
      Module.finrank K V + 1)
    (hdegree : V.forwardSpan (xMulVector K I) ≤ vectorDegreeLT K I n) :
    Module.finrank K
        ((V.forwardSpan (xMulVector K I)).forwardSpan (xMulVector K I)) =
      Module.finrank K (V.forwardSpan (xMulVector K I)) + 1 := by
  apply Submodule.finrank_forwardSpan_eq_add_one_of_eq_add_one_of_not_map_le
    V (xMulVector K I) (xMulVector_injective K I) hgrowth
  apply xMulVector_map_not_le_of_ne_bot_of_le_vectorDegreeLT K I
    (V.forwardSpan (xMulVector K I)) n
  · intro hzero
    rw [hzero, finrank_bot] at hgrowth
    omega
  · exact hdegree

end Polynomial

end
