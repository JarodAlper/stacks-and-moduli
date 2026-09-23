module

public import StacksAndModuli.API.SimplicialSignHomotopy
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# The contracting homotopy of a full simplex, with varying coefficients

Supporting API with no Stacks Project counterpart.

`StacksAndModuli/API/SimplicialSignHomotopy.lean` contracts the simplicial cochain complex of a full
simplex when the coefficients are a *fixed* module `V`. The Čech complex of an affine cover is
not of that shape: the cochain group attached to a subset `S` of the index set is the
localization `M[1/f_S]`, which grows with `S`.

This file generalizes the homotopy to a **coefficient system** — a family `V : Finset α → Type`
with compatible restriction maps `V s →ₗ V t` for `s ⊆ t` — together with a distinguished
vertex `v` in whose direction the system is *constant*: retractions `V (insert v s) →ₗ V s`
inverse to the restrictions and natural in `s`. That is exactly the situation on the chart
`D(f_v)` of an affine cover, where `f_v` is invertible and so `M[1/f_{S ∪ {v}}] = M[1/f_S]`.

Under those hypotheses coning off `v` is still a contracting homotopy, so the complex is
exact. This is the sign-bookkeeping heart of the vanishing of Čech cohomology of a
quasi-coherent sheaf on an affine scheme, which is in turn the first missing step on the way
to Serre vanishing at the scheme level — see `PLAN-hilbert-quot.md`.

Main declarations:
- `Finset.CoeffSystem`, `Finset.CoeffSystem.Retraction`;
- `Finset.CoeffSystem.coeffD`, `Finset.CoeffSystem.Retraction.coeffH`;
- `Finset.CoeffSystem.Retraction.coeffD_coeffH_add`, the homotopy identity `dh + hd = id`.
-/

@[expose] public section

universe u v

namespace Finset

variable {α : Type u} [LinearOrder α] {R : Type v} [Ring R]

/-- A **coefficient system** on the finite subsets of `α`: a family of modules with compatible
restriction maps along inclusions. -/
structure CoeffSystem (R : Type v) [Ring R] (V : Finset α → Type v)
    [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)] where
  /-- Restriction along an inclusion of subsets. -/
  map : ∀ {s t : Finset α}, s ⊆ t → (V s →ₗ[R] V t)
  /-- Restriction along the identity is the identity. -/
  map_self : ∀ {s : Finset α} (h : s ⊆ s) (x : V s), map h x = x
  /-- Restrictions compose. -/
  map_map : ∀ {s t u : Finset α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) (x : V s),
    map h₂ (map h₁ x) = map (h₁.trans h₂) x

namespace CoeffSystem

variable {V : Finset α → Type v} [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]

/-- The simplicial differential of a coefficient system: the alternating sum over the faces,
each restricted back up to the ambient subset. -/
def coeffD (C : CoeffSystem R V) (f : ∀ s, V s) (s : Finset α) : V s :=
  ∑ x ∈ s, koszulSign x s • C.map (erase_subset x s) (f (s.erase x))

/-- The simplicial differential as an `R`-linear map on the product of all the coefficient
groups. Since the differential raises the cardinality of the index by one, this single
endomorphism encodes the whole complex. -/
def coeffDₗ (C : CoeffSystem R V) : (∀ s, V s) →ₗ[R] (∀ s, V s) where
  toFun := C.coeffD
  map_add' g h := by
    funext s
    simp only [coeffD, Pi.add_apply, map_add, smul_add]
    exact Finset.sum_add_distrib
  map_smul' r g := by
    funext s
    simp only [coeffD, Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun x _ => smul_comm _ r _

@[simp] lemma coeffDₗ_apply (C : CoeffSystem R V) (g : ∀ s, V s) (s : Finset α) :
    C.coeffDₗ g s = C.coeffD g s := rfl

/-- A **retraction in the direction of `v`**: the coefficient system is constant along the
distinguished vertex `v`, by maps inverse to the restrictions and natural in the subset. -/
structure Retraction (C : CoeffSystem R V) (v : α) where
  /-- The retraction `V (insert v s) →ₗ V s`. -/
  inv : ∀ s : Finset α, (V (insert v s) →ₗ[R] V s)
  /-- The retraction undoes the restriction. -/
  inv_map : ∀ (s : Finset α) (x : V s), inv s (C.map (subset_insert v s) x) = x
  /-- The restriction undoes the retraction. -/
  map_inv : ∀ (s : Finset α) (x : V (insert v s)),
    C.map (subset_insert v s) (inv s x) = x
  /-- The retraction is natural in the subset. -/
  inv_naturality : ∀ {s t : Finset α} (h : s ⊆ t) (x : V (insert v s)),
    inv t (C.map (insert_subset_insert v h) x) = C.map h (inv s x)

variable {C : CoeffSystem R V} {v : α}

/-- Coning off the vertex `v`, with coefficients pulled back by the retraction. -/
def Retraction.coeffH (P : C.Retraction v) (f : ∀ s, V s) (s : Finset α) : V s :=
  if h : v ∈ s then 0 else koszulSign v (insert v s) • P.inv s (f (insert v s))

lemma Retraction.coeffH_of_mem (P : C.Retraction v) {s : Finset α} (h : v ∈ s)
    (f : ∀ s, V s) : P.coeffH f s = 0 := by
  simp only [Retraction.coeffH, h, dif_pos]

lemma Retraction.coeffH_of_notMem (P : C.Retraction v) {s : Finset α} (h : v ∉ s)
    (f : ∀ s, V s) :
    P.coeffH f s = koszulSign v (insert v s) • P.inv s (f (insert v s)) := by
  simp only [Retraction.coeffH, h, dif_neg, not_false_eq_true]

/-- Transport along an equality of subsets, expressed inside the coefficient system. -/
lemma map_congr_left (C : CoeffSystem R V) {s s' t : Finset α} (h : s = s')
    (hs : s ⊆ t) (hs' : s' ⊆ t) (x : V s) :
    C.map hs x = C.map hs' (C.map h.le x) := by
  subst h
  rw [C.map_self]

/-- Transport along an equality of the *target* subset. -/
lemma map_congr_right (C : CoeffSystem R V) {s t t' : Finset α} (h : t = t')
    (hs : s ⊆ t) (hs' : s ⊆ t') (x : V s) :
    C.map hs' x = C.map h.le (C.map hs x) := by
  subst h
  rw [C.map_map]

/-- Restriction along an equality is the canonical transport. -/
lemma map_eq_cast (C : CoeffSystem R V) {s s' : Finset α} (h : s = s') (x : V s) :
    C.map h.le x = h ▸ x := by
  subst h
  rw [C.map_self]

lemma cast_dep_apply {s s' : Finset α} (h : s = s') (f : ∀ u, V u) : h ▸ (f s) = f s' := by
  subst h
  rfl

/-- **The simplicial differential squares to zero**, with varying coefficients. -/
theorem coeffD_coeffD (C : CoeffSystem R V) (f : ∀ s, V s) (t : Finset α) :
    C.coeffD (C.coeffD f) t = 0 := by
  classical
  have hterm : ∀ y ∈ t, koszulSign y t • C.map (erase_subset y t) (C.coeffD f (t.erase y))
      = ∑ x ∈ t.erase y, (koszulSign y t * koszulSign x (t.erase y)) •
          C.map ((erase_subset x (t.erase y)).trans (erase_subset y t))
            (f ((t.erase y).erase x)) := by
    intro y _
    rw [CoeffSystem.coeffD, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_zsmul, smul_smul, C.map_map]
  rw [CoeffSystem.coeffD, Finset.sum_congr rfl hterm]
  -- turn the double sum into a sum over ordered pairs and cancel by swapping
  set G : α × α → V t := fun p =>
    if p.1 ≠ p.2 then
      (koszulSign p.1 t * koszulSign p.2 (t.erase p.1)) •
        C.map ((erase_subset p.2 (t.erase p.1)).trans (erase_subset p.1 t))
          (f ((t.erase p.1).erase p.2))
    else 0 with hG
  have hrw : ∑ y ∈ t, ∑ x ∈ t.erase y, (koszulSign y t * koszulSign x (t.erase y)) •
        C.map ((erase_subset x (t.erase y)).trans (erase_subset y t))
          (f ((t.erase y).erase x))
      = ∑ p ∈ t ×ˢ t, G p := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun y _ => ?_
    have h1 : ∀ x ∈ t.erase y, (koszulSign y t * koszulSign x (t.erase y)) •
        C.map ((erase_subset x (t.erase y)).trans (erase_subset y t))
          (f ((t.erase y).erase x)) = G (y, x) := by
      intro x hx
      rw [hG]
      simp only [ne_eq]
      rw [if_pos (Ne.symm (ne_of_mem_erase hx))]
    rw [Finset.sum_congr rfl h1]
    refine Finset.sum_subset (erase_subset y t) fun x _ hnx => ?_
    have hxy : x = y := by
      by_contra hc
      exact hnx (mem_erase.mpr ⟨hc, by simpa using ‹x ∈ t›⟩)
    rw [hG]
    simp [hxy]
  rw [hrw]
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨y, x⟩ hp
    by_cases hxy : y = x
    · simp [hG, hxy]
    · have hmem := Finset.mem_product.mp hp
      have hey : (t.erase y).erase x = (t.erase x).erase y := Finset.erase_right_comm (s := t)
      rw [hG]
      simp only [ne_eq, hxy, not_false_eq_true, if_pos, Ne.symm hxy]
      rw [C.map_congr_left hey ((erase_subset x (t.erase y)).trans (erase_subset y t))
          ((erase_subset y (t.erase x)).trans (erase_subset x t)),
        C.map_eq_cast hey, cast_dep_apply hey f, ← add_smul,
        koszulSign_pair_cancel hmem.2 hmem.1 (Ne.symm hxy), zero_smul]
  · rintro ⟨y, x⟩ _ hne hc
    apply hne
    have : y = x := (congrArg Prod.fst hc).symm
    simp [hG, this]
  · rintro ⟨y, x⟩ hp
    have hmem := Finset.mem_product.mp hp
    exact Finset.mem_product.mpr ⟨hmem.2, hmem.1⟩
  · rintro ⟨y, x⟩ _
    rfl

/-- **The full simplex is contractible, with varying coefficients.** -/
theorem Retraction.coeffD_coeffH_add (P : C.Retraction v) (f : ∀ s, V s) (s : Finset α) :
    C.coeffD (P.coeffH f) s + P.coeffH (C.coeffD f) s = f s := by
  classical
  by_cases hv : v ∈ s
  · obtain ⟨t, ht, rfl⟩ : ∃ t : Finset α, v ∉ t ∧ s = insert v t :=
      ⟨s.erase v, notMem_erase v s, (insert_erase hv).symm⟩
    rw [P.coeffH_of_mem (mem_insert_self v t), add_zero, CoeffSystem.coeffD,
      Finset.sum_eq_single v
        (fun x hx hxv => by
          rw [P.coeffH_of_mem (mem_erase.mpr ⟨Ne.symm hxv, mem_insert_self v t⟩), map_zero,
            smul_zero])
        (fun hc => absurd (mem_insert_self v t) hc)]
    have hEr : (insert v t).erase v = t := erase_insert ht
    rw [P.coeffH_of_notMem (notMem_erase v (insert v t))]
    set u : Finset α := (insert v t).erase v with hu
    have hins : insert v u = insert v t := insert_erase (mem_insert_self v t)
    rw [show koszulSign v (insert v u) = koszulSign v (insert v t) from by rw [hins],
      map_zsmul, smul_smul, koszulSign_mul_self, one_smul,
      C.map_congr_right hins (subset_insert v u) (erase_subset v (insert v t)),
      P.map_inv u (f (insert v u)), C.map_eq_cast hins, cast_dep_apply hins f]
  · -- the new vertex: the direct and coned contributions cancel in pairs
    have hsum : C.coeffD f (insert v s)
        = koszulSign v (insert v s) •
            C.map (erase_subset v (insert v s)) (f ((insert v s).erase v))
          + ∑ x ∈ s, koszulSign x (insert v s) •
              C.map (erase_subset x (insert v s)) (f ((insert v s).erase x)) := by
      rw [CoeffSystem.coeffD, Finset.sum_insert hv]
    -- the `v`-term of the differential is `f s` again
    have hEv : (insert v s).erase v = s := erase_insert hv
    have hA : P.inv s (C.map (erase_subset v (insert v s)) (f ((insert v s).erase v)))
        = f s := by
      rw [C.map_congr_left hEv (erase_subset v (insert v s)) (subset_insert v s),
        P.inv_map s, C.map_eq_cast hEv, cast_dep_apply hEv f]
    -- each `x ∈ s` cancels against the corresponding coned term
    have hcancel : ∀ x ∈ s,
        koszulSign x s • C.map (erase_subset x s) (P.coeffH f (s.erase x))
          + koszulSign v (insert v s) • P.inv s (koszulSign x (insert v s) •
              C.map (erase_subset x (insert v s)) (f ((insert v s).erase x))) = 0 := by
      intro x hx
      have hxv : x ≠ v := fun hc => hv (hc ▸ hx)
      have hxe : (insert v s).erase x = insert v (s.erase x) :=
        erase_insert_of_ne (Ne.symm hxv)
      have hnot : v ∉ s.erase x := fun hc => hv (mem_of_mem_erase hc)
      set w : V s := C.map (erase_subset x s)
        (P.inv (s.erase x) (f (insert v (s.erase x)))) with hw
      have h1 : koszulSign x s • C.map (erase_subset x s) (P.coeffH f (s.erase x))
          = (koszulSign x s * koszulSign v (insert v (s.erase x))) • w := by
        rw [P.coeffH_of_notMem hnot, map_zsmul, smul_smul, hw]
      have h2 : koszulSign v (insert v s) • P.inv s (koszulSign x (insert v s) •
            C.map (erase_subset x (insert v s)) (f ((insert v s).erase x)))
          = (koszulSign v (insert v s) * koszulSign x (insert v s)) • w := by
        rw [map_zsmul, smul_smul, hw,
          C.map_congr_left hxe (erase_subset x (insert v s))
            (insert_subset_insert v (erase_subset x s)),
          P.inv_naturality (erase_subset x s), C.map_eq_cast hxe, cast_dep_apply hxe f]
      rw [h1, h2, ← add_smul,
        show koszulSign v (insert v (s.erase x)) = koszulSign v ((insert v s).erase x) from
          by rw [hxe],
        koszulSign_cone_cancel hv hx, zero_smul]
    rw [P.coeffH_of_notMem hv, hsum, map_add, map_zsmul, hA, smul_add, smul_smul,
      koszulSign_mul_self, one_smul,
      map_sum, Finset.smul_sum, CoeffSystem.coeffD,
      show (∑ x ∈ s, koszulSign x s • C.map (erase_subset x s) (P.coeffH f (s.erase x)))
          + (f s + ∑ x ∈ s, koszulSign v (insert v s) • P.inv s
              (koszulSign x (insert v s) •
                C.map (erase_subset x (insert v s)) (f ((insert v s).erase x))))
        = (∑ x ∈ s, (koszulSign x s • C.map (erase_subset x s) (P.coeffH f (s.erase x))
            + koszulSign v (insert v s) • P.inv s (koszulSign x (insert v s) •
              C.map (erase_subset x (insert v s)) (f ((insert v s).erase x))))) + f s from
        by rw [Finset.sum_add_distrib]; abel,
      Finset.sum_congr rfl hcancel, Finset.sum_const_zero, zero_add]

lemma Retraction.coeffH_zero (P : C.Retraction v) (s : Finset α) :
    P.coeffH (fun u => (0 : V u)) s = 0 := by
  by_cases h : v ∈ s
  · rw [P.coeffH_of_mem h]
  · rw [P.coeffH_of_notMem h, map_zero, smul_zero]

/-- **Exactness of the contractible simplicial complex**: every cocycle is a coboundary. -/
theorem Retraction.coeffD_coeffH_of_coeffD_eq_zero (P : C.Retraction v) (f : ∀ s, V s)
    (hf : ∀ s, C.coeffD f s = 0) (s : Finset α) : C.coeffD (P.coeffH f) s = f s := by
  have h := P.coeffD_coeffH_add f s
  have hz : C.coeffD f = fun u => (0 : V u) := funext hf
  rwa [show P.coeffH (C.coeffD f) s = 0 from by rw [hz]; exact P.coeffH_zero s,
    add_zero] at h

/-- **A contractible coefficient system has exact simplicial complex.** -/
theorem Retraction.exact_coeffDₗ (P : C.Retraction v) :
    Function.Exact C.coeffDₗ C.coeffDₗ := by
  rw [LinearMap.exact_iff]
  refine le_antisymm (fun g hg => ?_) (fun g hg => ?_)
  · exact ⟨P.coeffH g, funext fun s =>
      P.coeffD_coeffH_of_coeffD_eq_zero g (fun t => congrFun hg t) s⟩
  · obtain ⟨h, rfl⟩ := hg
    exact funext fun s => C.coeffD_coeffD h s

end CoeffSystem

end Finset

end
