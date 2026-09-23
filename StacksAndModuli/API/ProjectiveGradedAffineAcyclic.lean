module

public import StacksAndModuli.API.ProjectiveGradedTorsion

/-!
# Acyclicity under a partition of unity

Supporting API with no Stacks Project counterpart.

The algebraic form of "a quasi-coherent sheaf is acyclic on an affine": if the variables
act on a graded module `Q` with a *partition of unity* — degree `-1` maps `aᵥ` commuting
with the variables and satisfying `∑ᵥ aᵥ ∘ xᵥ = id` — then the augmented Čech complex of
`Q` is exact.  This is the missing input to the `dropVarIso` field of `CechSerreData`:
after inverting `x_j` on a module killed by a linear form `L` with `IsUnit (c j)`, the
remaining variables acquire exactly such a partition of unity.

The proof is the classical one.  At the `t`-th stage of the localization tower the Čech
complex is a Koszul complex on `x₀^t, …, x_m^t`, and `∑ᵥ bᵥ ∘ xᵥ^t = id` contracts it;
`locIncl_exists` and `locIncl_eq_zero` move cocycles and relations between stages.  The
operators `bᵥ` come from a purely polynomial fact: a form of degree `N ≥ (m+1)t` is a
combination `∑ᵥ Xᵥ^t gᵥ` with `gᵥ` homogeneous.

Main declarations:
- `MvPolynomial.exists_isHomogeneous_split`;
-/

@[expose] public section

noncomputable section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable {k : Type u} [Field k] {n : ℕ}

/-! ## Splitting a form of large degree along the `t`-th powers of the variables -/

/-- A variable whose exponent in `b` is at least `t`, when one exists. -/
def splitIdx (t : ℕ) (b : Fin (n + 1) →₀ ℕ) : Fin (n + 1) :=
  if h : ∃ v, t ≤ b v then h.choose else 0

lemma splitIdx_spec {t : ℕ} {b : Fin (n + 1) →₀ ℕ} (h : ∃ v, t ≤ b v) :
    t ≤ b (splitIdx t b) := by
  rw [splitIdx, dif_pos h]
  exact h.choose_spec

/-- **A form of degree at least `(n+1)·t` is a combination of the `t`-th powers of the
variables, with homogeneous coefficients.** -/
theorem exists_isHomogeneous_split (p : MvPolynomial (Fin (n + 1)) k) {D t : ℕ}
    (ht : 1 ≤ t) (hp : p.IsHomogeneous D) (hD : (n + 1) * t ≤ D) :
    ∃ g : Fin (n + 1) → MvPolynomial (Fin (n + 1)) k,
      (∀ v, (g v).IsHomogeneous (D - t)) ∧
        p = ∑ v : Fin (n + 1), (X v : MvPolynomial (Fin (n + 1)) k) ^ t * g v := by
  classical
  have hdeg : ∀ b ∈ p.support, b.degree = D := fun b hb =>
    (degree_eq_weight_one b).trans (hp (MvPolynomial.mem_support_iff.mp hb))
  have hex : ∀ b ∈ p.support, ∃ v, t ≤ b v := by
    intro b hb
    exact exists_le_of_le_degree ht (by rw [hdeg b hb]; omega)
  refine ⟨fun v => ∑ b ∈ {b ∈ p.support | splitIdx t b = v},
    monomial (b - t • Finsupp.single v 1) (coeff b p), fun v => ?_, ?_⟩
  · refine IsHomogeneous.sum _ _ _ fun b hb => ?_
    rw [Finset.mem_filter] at hb
    have hv : t ≤ b v := hb.2 ▸ splitIdx_spec (hex b hb.1)
    refine isHomogeneous_monomial _ ?_
    have hvv : ((b - t • Finsupp.single v 1 : Fin (n + 1) →₀ ℕ)) v = b v - t := by
      simp [Finsupp.tsub_apply, Finsupp.single_apply]
    have hother : ∀ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase v,
        ((b - t • Finsupp.single v 1 : Fin (n + 1) →₀ ℕ)) i = b i := by
      intro i hi
      have hiv : i ≠ v := Finset.ne_of_mem_erase hi
      simp [Finsupp.tsub_apply, Finsupp.single_apply, hiv]
    have e1 : (b - t • Finsupp.single v 1 : Fin (n + 1) →₀ ℕ).degree
        = ((b - t • Finsupp.single v 1 : Fin (n + 1) →₀ ℕ) v)
          + ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase v,
            ((b - t • Finsupp.single v 1 : Fin (n + 1) →₀ ℕ) i) := by
      rw [degree_eq_sum_univ]
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ v)).symm
    have e2 : b.degree = b v + ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase v, b i := by
      rw [degree_eq_sum_univ]
      exact (Finset.add_sum_erase _ _ (Finset.mem_univ v)).symm
    have hsum : ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase v,
        ((b - t • Finsupp.single v 1 : Fin (n + 1) →₀ ℕ) i)
        = ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase v, b i :=
      Finset.sum_congr rfl hother
    have hkey : (b - t • Finsupp.single v 1 : Fin (n + 1) →₀ ℕ).degree + t = b.degree := by
      rw [e1, e2, hvv, hsum]
      omega
    have hbD : b.degree = D := hdeg b hb.1
    omega
  · conv_lhs => rw [MvPolynomial.as_sum p]
    rw [← Finset.sum_fiberwise p.support (fun b => splitIdx t b)
      (fun b => (monomial b (coeff b p) : MvPolynomial (Fin (n + 1)) k))]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [Finset.mem_filter] at hb
    have hv : t ≤ b v := hb.2 ▸ splitIdx_spec (hex b hb.1)
    have hle : (t • Finsupp.single v 1 : Fin (n + 1) →₀ ℕ) ≤ b := by
      refine Finsupp.le_def.mpr fun i => ?_
      by_cases hiv : i = v
      · subst hiv
        simpa using hv
      · simp [Finsupp.single_apply, hiv]
    have hXp : (X v : MvPolynomial (Fin (n + 1)) k) ^ t
        = monomial (t • Finsupp.single v 1) (1 : k) := by
      rw [X_pow_eq_monomial]
      congr 1
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hXp, monomial_mul, one_mul, add_tsub_cancel_of_le hle]

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
