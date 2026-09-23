module

public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

/-!
# The contracting homotopy of a full simplex

Supporting API with no Stacks Project counterpart, developed for the computation of the
cohomology of the twisting sheaves on `ℙⁿ_k` in
`StacksAndModuli/API/ProjectiveGradedStructureCohomology.lean`.

The Čech complex of the standard affine cover of `ℙⁿ` is indexed by the nonempty subsets
of `{0, …, n}`, with the alternating simplicial differential.  After decomposing along
Laurent monomials, each summand becomes the simplicial cochain complex of a *full*
simplex on a vertex set, which is contractible: coning off any vertex `v` is a homotopy
from the identity to zero.

This file develops that homotopy for cochains indexed by `Finset α`, `α` a linear order,
with the Koszul sign written intrinsically as `(-1)` to the number of elements below the
one removed.  That is exactly the sign with which a face enters the alternating sum once
the subset is listed in increasing order, and it is far easier to manipulate than a
position in a list.

Main declarations:
- `Finset.koszulSign`;
- `Finset.simplicialD`, `Finset.simplicialH`;
- `Finset.simplicialD_simplicialH_add`, the homotopy identity `dh + hd = id`.
-/

@[expose] public section

namespace Finset

variable {α : Type*} [LinearOrder α]
variable {V : Type*} [AddCommGroup V]

/-- The Koszul sign of `x` inside the finite set `s`: `(-1)` to the number of elements of
`s` strictly below `x`.  For `x ∈ s` this is the sign with which the face omitting `x`
enters the simplicial differential. -/
def koszulSign (x : α) (s : Finset α) : ℤ := (-1) ^ #{y ∈ s | y < x}

lemma neg_one_pow_add_succ (m : ℕ) : (-1 : ℤ) ^ m + (-1) ^ (m + 1) = 0 := by
  rw [pow_succ, mul_neg_one, add_neg_cancel]

lemma koszulSign_mul_self (x : α) (s : Finset α) :
    koszulSign x s * koszulSign x s = 1 := by
  rw [koszulSign, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

lemma koszulSign_smul_koszulSign_smul (x : α) (s : Finset α) (w : V) :
    koszulSign x s • koszulSign x s • w = w := by
  rw [smul_smul, koszulSign_mul_self, one_smul]

/-- The simplicial differential on cochains indexed by finite subsets. -/
def simplicialD (f : Finset α → V) (s : Finset α) : V :=
  ∑ x ∈ s, koszulSign x s • f (s.erase x)

/-- Coning off the vertex `v`: the contracting homotopy of the full simplex. -/
def simplicialH (v : α) (f : Finset α → V) (s : Finset α) : V :=
  if v ∈ s then 0 else koszulSign v (insert v s) • f (insert v s)

lemma simplicialH_of_mem {v : α} {s : Finset α} (h : v ∈ s) (f : Finset α → V) :
    simplicialH v f s = 0 := by
  simp only [simplicialH, h, ↓reduceIte]

lemma simplicialH_of_notMem {v : α} {s : Finset α} (h : v ∉ s) (f : Finset α → V) :
    simplicialH v f s = koszulSign v (insert v s) • f (insert v s) := by
  simp only [simplicialH, h, ↓reduceIte]

/-! ## Counting elements below a vertex -/

lemma card_filter_lt_insert_of_lt {v x : α} (h : v < x) {s : Finset α} (hv : v ∉ s) :
    #{y ∈ insert v s | y < x} = #{y ∈ s | y < x} + 1 := by
  classical
  rw [filter_insert]
  simp only [h, ↓reduceIte]
  exact card_insert_of_notMem (fun hc => hv (mem_of_mem_filter _ hc))

lemma card_filter_lt_insert_of_not_lt {v x : α} (h : ¬ v < x) (s : Finset α) :
    #{y ∈ insert v s | y < x} = #{y ∈ s | y < x} := by
  classical
  rw [filter_insert]
  simp only [h, ↓reduceIte]

lemma card_filter_lt_erase_of_lt {v x : α} (h : x < v) {s : Finset α} (hx : x ∈ s) :
    #{y ∈ s | y < v} = #{y ∈ s.erase x | y < v} + 1 := by
  classical
  rw [filter_erase, card_erase_of_mem (mem_filter.mpr ⟨hx, h⟩)]
  have : 0 < #{y ∈ s | y < v} := card_pos.mpr ⟨x, mem_filter.mpr ⟨hx, h⟩⟩
  omega

lemma card_filter_lt_erase_of_not_lt {v x : α} (h : ¬ x < v) (s : Finset α) :
    #{y ∈ s.erase x | y < v} = #{y ∈ s | y < v} := by
  classical
  rw [filter_erase,
    Finset.erase_eq_of_notMem (a := x) (s := {y ∈ s | y < v})
      (by simp only [mem_filter]; exact fun hc => h hc.2)]

/-- The two ways a face `t.erase x` of the cone `t = insert v s` is reached — directly,
or through the cone — carry opposite signs. -/
lemma koszulSign_cone_cancel {v x : α} {s : Finset α} (hv : v ∉ s) (hx : x ∈ s) :
    koszulSign x s * koszulSign v ((insert v s).erase x) +
      koszulSign v (insert v s) * koszulSign x (insert v s) = 0 := by
  classical
  have hne : v ≠ x := fun h => hv (h ▸ hx)
  have hvt : (insert v s).erase x = insert v (s.erase x) := erase_insert_of_ne hne
  have hvfil : #{y ∈ insert v s | y < v} = #{y ∈ s | y < v} :=
    card_filter_lt_insert_of_not_lt (lt_irrefl v) s
  have hvex : #{y ∈ insert v (s.erase x) | y < v} = #{y ∈ s.erase x | y < v} :=
    card_filter_lt_insert_of_not_lt (lt_irrefl v) _
  rcases lt_or_gt_of_ne hne with hvx | hxv
  · -- `v < x`: the cone face gains a slot below `x`
    have h1 : #{y ∈ insert v s | y < x} = #{y ∈ s | y < x} + 1 :=
      card_filter_lt_insert_of_lt hvx hv
    have h2 : #{y ∈ s.erase x | y < v} = #{y ∈ s | y < v} :=
      card_filter_lt_erase_of_not_lt (not_lt_of_gt hvx) s
    rw [koszulSign, koszulSign, koszulSign, koszulSign, hvt, hvfil, hvex, h1, h2,
      ← pow_add, ← pow_add,
      show #{y ∈ s | y < v} + (#{y ∈ s | y < x} + 1)
        = (#{y ∈ s | y < x} + #{y ∈ s | y < v}) + 1 from by omega]
    exact neg_one_pow_add_succ _
  · -- `x < v`: the cone loses a slot below `v`
    have h1 : #{y ∈ insert v s | y < x} = #{y ∈ s | y < x} :=
      card_filter_lt_insert_of_not_lt (not_lt_of_gt hxv) s
    have h2 : #{y ∈ s | y < v} = #{y ∈ s.erase x | y < v} + 1 :=
      card_filter_lt_erase_of_lt hxv hx
    rw [koszulSign, koszulSign, koszulSign, koszulSign, hvt, hvfil, hvex, h1, h2,
      ← pow_add, ← pow_add,
      show #{y ∈ s.erase x | y < v} + 1 + #{y ∈ s | y < x}
        = (#{y ∈ s | y < x} + #{y ∈ s.erase x | y < v}) + 1 from by omega]
    exact neg_one_pow_add_succ _

/-- The two ways of removing an unordered pair `{x, y}` from `t` carry opposite signs; this is
what makes the simplicial differential square to zero. -/
lemma koszulSign_pair_cancel {x y : α} {t : Finset α} (hx : x ∈ t) (hy : y ∈ t) (hxy : x ≠ y) :
    koszulSign y t * koszulSign x (t.erase y) +
      koszulSign x t * koszulSign y (t.erase x) = 0 := by
  classical
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have h1 : #{z ∈ t.erase y | z < x} = #{z ∈ t | z < x} :=
      card_filter_lt_erase_of_not_lt (not_lt_of_gt hlt) t
    have h2 : #{z ∈ t | z < y} = #{z ∈ t.erase x | z < y} + 1 :=
      card_filter_lt_erase_of_lt hlt hx
    rw [koszulSign, koszulSign, koszulSign, koszulSign, h1, h2, ← pow_add, ← pow_add,
      show #{z ∈ t.erase x | z < y} + 1 + #{z ∈ t | z < x}
        = (#{z ∈ t | z < x} + #{z ∈ t.erase x | z < y}) + 1 from by omega,
      show #{z ∈ t | z < x} + #{z ∈ t.erase x | z < y}
        = (#{z ∈ t | z < x} + #{z ∈ t.erase x | z < y}) from rfl]
    rw [add_comm]
    exact neg_one_pow_add_succ _
  · have h1 : #{z ∈ t.erase x | z < y} = #{z ∈ t | z < y} :=
      card_filter_lt_erase_of_not_lt (not_lt_of_gt hgt) t
    have h2 : #{z ∈ t | z < x} = #{z ∈ t.erase y | z < x} + 1 :=
      card_filter_lt_erase_of_lt hgt hy
    rw [koszulSign, koszulSign, koszulSign, koszulSign, h1, h2, ← pow_add, ← pow_add,
      show #{z ∈ t | z < y} + #{z ∈ t.erase y | z < x}
        = (#{z ∈ t.erase y | z < x} + #{z ∈ t | z < y}) from by omega,
      show #{z ∈ t.erase y | z < x} + 1 + #{z ∈ t | z < y}
        = (#{z ∈ t.erase y | z < x} + #{z ∈ t | z < y}) + 1 from by omega]
    exact neg_one_pow_add_succ _

/-! ## The homotopy identity -/

/-- **The full simplex is contractible.**  Coning off any vertex `v` is a contracting
homotopy for the simplicial cochain complex: `d ∘ h + h ∘ d = id`. -/
theorem simplicialD_simplicialH_add (v : α) (f : Finset α → V) (s : Finset α) :
    simplicialD (simplicialH v f) s + simplicialH v (simplicialD f) s = f s := by
  classical
  by_cases hv : v ∈ s
  · -- `v` is already a vertex of `s`: only the face omitting `v` survives
    rw [simplicialH_of_mem hv, add_zero, simplicialD,
      Finset.sum_eq_single v (fun x hx hxv => by
        rw [simplicialH_of_mem (mem_erase.mpr ⟨Ne.symm hxv, hv⟩), smul_zero])
        (fun hc => absurd hv hc),
      simplicialH_of_notMem (notMem_erase v s), insert_erase hv,
      koszulSign_smul_koszulSign_smul]
  · -- `v` is a new vertex: the direct and coned contributions cancel in pairs
    have hts : (insert v s).erase v = s := erase_insert hv
    have key : ∀ x ∈ s, koszulSign x s • simplicialH v f (s.erase x)
        + koszulSign v (insert v s) •
          (koszulSign x (insert v s) • f ((insert v s).erase x)) = 0 := by
      intro x hx
      have hne : v ≠ x := fun h => hv (h ▸ hx)
      have hvt : (insert v s).erase x = insert v (s.erase x) := erase_insert_of_ne hne
      rw [simplicialH_of_notMem (fun hc => hv (mem_of_mem_erase hc)), ← hvt,
        smul_smul, smul_smul, ← add_smul, koszulSign_cone_cancel hv hx, zero_smul]
    have hD : simplicialD f (insert v s)
        = koszulSign v (insert v s) • f ((insert v s).erase v)
          + ∑ x ∈ s, koszulSign x (insert v s) • f ((insert v s).erase x) := by
      rw [simplicialD, Finset.sum_insert hv]
    rw [simplicialH_of_notMem hv, hD, smul_add, Finset.smul_sum, simplicialD,
      show (∑ x ∈ s, koszulSign x s • simplicialH v f (s.erase x))
          + (koszulSign v (insert v s) •
              (koszulSign v (insert v s) • f ((insert v s).erase v))
            + ∑ x ∈ s, koszulSign v (insert v s) •
                (koszulSign x (insert v s) • f ((insert v s).erase x)))
        = (∑ x ∈ s, (koszulSign x s • simplicialH v f (s.erase x)
            + koszulSign v (insert v s) •
              (koszulSign x (insert v s) • f ((insert v s).erase x))))
          + koszulSign v (insert v s) •
              (koszulSign v (insert v s) • f ((insert v s).erase v))
        from by
          rw [Finset.sum_add_distrib,
            add_comm (koszulSign v (insert v s) •
              (koszulSign v (insert v s) • f ((insert v s).erase v)))
              (∑ x ∈ s, koszulSign v (insert v s) •
                (koszulSign x (insert v s) • f ((insert v s).erase x))),
            ← add_assoc],
      Finset.sum_congr rfl key, Finset.sum_const_zero, zero_add,
      koszulSign_smul_koszulSign_smul, hts]

end Finset

end
