module

public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Algebra.Polynomial.Sequence
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import StacksAndModuli.«Section2.3-Regularity».«part2.3.1a-properties-of-regularity»
public import StacksAndModuli.API.ProjectiveGradedFamilies
public import StacksAndModuli.API.ProjectiveHyperplaneIso

/-!
# Regularity bounds: numerical polynomials

This module corresponds to the second subsection ("Regularity bounds") of §2.3
(Castelnuovo–Mumford regularity) of Chapter 2 of *Stacks and Moduli*,
label `sec:regularity`.

The main results of this subsection are Mumford's Boundedness of Regularity,
**Theorem 2.3.8** (`thm:boundedness-of-regularity`, Stacks 08AG), and Regularity in
Families, **Proposition 2.3.18** (`prop:regularity-in-families`, which rests on Cohomology
and Base Change, §A.6). Both are formalized and proved in the graded-module model of
quasi-coherent sheaves on `ℙⁿ` relative to the packaged cohomology theories of
`StacksAndModuli/API/ProjectiveGradedCohomology.lean` and
`StacksAndModuli/API/ProjectiveGradedFamilies.lean`; see this folder's COMMENTARY.md.

Also formalized here is the arithmetic of **numerical polynomials** from the
unlabeled remark following the theorem, anchored at **Equation 2.3.13**
(`eqn:lambdarn`): every polynomial `P ∈ ℚ[z]` that
takes integer values at all large integers can be written uniquely as an integral
combination `P(z) = ∑ aᵢ C(z, i)` of the binomial coefficient polynomials. This module
introduces the binomial polynomials and the numerality predicate and proves the integral
binomial-basis theorem by finite differences and induction on degree.

Main book results:
- `AlgebraicGeometry.ProjectiveSpace.exists_boundsRegularity_of_field`: **Theorem 2.3.8**
  (`thm:boundedness-of-regularity`), Mumford's Boundedness of Regularity over every field.
- `AlgebraicGeometry.ProjectiveSpace.finite_projective_Hgr_zero_of_fibres`,
  `…subsingleton_Hgr_of_fibres`, `…isGloballyGenerated_of_fibres_regular`:
  **Proposition 2.3.18** (`prop:regularity-in-families`), Regularity in Families.
- `Polynomial.gotzmannPoly_eval`: the displayed identity in **Remark 2.3.15**
  (`rmk:optimal-bounds`).

Supporting numerical-polynomial API:
- `Polynomial.binomialPoly`: the binomial coefficient polynomial `C(z, i) ∈ ℚ[z]`.
- `Polynomial.IsNumerical`: integrality of the values `P(n)` for all large natural `n`.
- `Polynomial.isNumerical_binomialPoly`, `Polynomial.linearIndependent_binomialPoly`,
  `Polynomial.IsNumerical.exists_sum_binomialPoly`: the binomial polynomials are
  numerical, linearly independent, and integrally span the numerical polynomials.
- `Polynomial.isNumerical_iff_exists_sum_binomialPoly`: numerical polynomials are
  exactly the finite integral combinations of binomial coefficient polynomials.
- `Polynomial.IsNumerical.binomialCoeffs`: the canonical integral coefficients of a
  numerical polynomial in the binomial basis.

Equation 2.3.13 itself asserts the existence of the universal bound polynomial
`Λ_{r,n}`; that construction is not yet formalized.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ThmBoundednessOfRegularity

open CategoryTheory AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.ProjectiveSpace.GradedModule

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Background definition for Theorem 2.3.8 (the property being asserted): the
integer `m₀` *bounds the regularity* of subsheaves of `𝒪^{⊕r}` on `ℙⁿ` with Hilbert polynomial
`P` if every such subsheaf, over every field, is `m₀`-regular.

The base field is required to be infinite; the reduction of the general case to this one is
flat base change, `Cohomology.BaseChange`, and is carried out in
`exists_boundsRegularity_all_fields`. -/
def BoundsRegularity (r n : ℕ) (P : Polynomial ℚ) (m₀ : ℤ) : Prop :=
  ∀ (K : Type u) [Field K] [Infinite K] (C : Cohomology K) (F : GradedModule K n)
    (f : F ⟶ (structureModule K n).pow r), (∀ d, Function.Injective (f.app d).hom) →
    C.HasHilbertPolynomial F P → C.IsMRegular F m₀

namespace Cohomology

variable {k : Type u} [Field k] (C : Cohomology k)

/-- (local glue for **Theorem 2.3.8**) an alternating sum whose terms vanish from index `2`
on collapses to its first two terms. -/
lemma sum_range_eq_of_ge_two (g : ℕ → ℤ) (hg : ∀ i, 2 ≤ i → g i = 0) :
    ∀ N : ℕ, 2 ≤ N → ∑ i ∈ Finset.range N, g i = g 0 + g 1 := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
      intro _
      rcases Nat.lt_or_ge N 2 with hN | hN
      · interval_cases N
        · simp at *
        · simp [Finset.sum_range_succ]
      · rw [Finset.sum_range_succ, ih hN, hg N hN, add_zero]

/-- (local glue for **Theorem 2.3.8**) if `F|_H` is `m₁`-regular then `Hⁱ(H, F|_H(D)) = 0` for
all `i ≥ 1` and `D ≥ m₁ - i`. -/
lemma subsingleton_Hgr_quotL_of_le [Infinite k] {n : ℕ} {M : GradedModule k (n + 1)}
    (c : Fin (n + 2) → k) (j : Fin (n + 2)) (hj : IsUnit (c j))
    (hcoh : C.IsCoherent (M.restrictL c j)) {m₁ : ℤ}
    (hres : C.IsMRegular (M.restrictL c j) m₁) (i : ℕ) (hi : 1 ≤ i) (D : ℤ)
    (hD : m₁ - i ≤ D) : Subsingleton ((C.Hgr (M.quotL c) i).obj D) := by
  have hreg' : C.IsMRegular (M.restrictL c j) (D + i) :=
    C.isMRegular_of_le n (M.restrictL c j) hcoh m₁ (D + i) hres (by omega)
  have hv := hreg' i hi
  rw [show D + (i : ℤ) - (i : ℤ) = D from by ring] at hv
  rw [← C.subsingleton_Hgr_restrictL_iff M c j hj hcoh]
  exact hv

/-- (local glue for **Theorem 2.3.8**) the cohomology of `F` in degrees `≥ 2` is forced by the
regularity of `F|_H` together with Serre vanishing: `Hⁱ⁺¹(ℙⁿ⁺¹, F(D)) = 0` for `i ≥ 1` and
`D ≥ m₁ - i - 1`. -/
lemma subsingleton_Hgr_succ_of_le [Infinite k] {n : ℕ} {M : GradedModule k (n + 1)}
    (hM : C.IsCoherent M) (c : Fin (n + 2) → k) (j : Fin (n + 2)) (hj : IsUnit (c j))
    (hL : ∀ d, Function.Injective ((M.mulLHom c).app d).hom) {m₁ : ℤ}
    (hres : C.IsMRegular (M.restrictL c j) m₁) (i : ℕ) (hi : 1 ≤ i) (D : ℤ)
    (hD : m₁ - i - 1 ≤ D) : Subsingleton ((C.Hgr M (i + 1)).obj D) := by
  have hcoh : C.IsCoherent (M.restrictL c j) := C.isCoherent_restrictL hM c j hj
  obtain ⟨d₀, hd₀⟩ := C.serre_vanishing hM (i + 1) (by omega)
  have hSE : ShortExact (M.mulLHom c) (toCoker (M.mulLHom c)) := shortExact_toCoker _ hL
  obtain ⟨e₀, he₁, he₂⟩ : ∃ e₀ : ℤ, d₀ ≤ e₀ ∧ D ≤ e₀ :=
    ⟨max d₀ D, le_max_left _ _, le_max_right _ _⟩
  have key : ∀ t : ℕ, m₁ - (i : ℤ) - 1 ≤ e₀ - t →
      Subsingleton ((C.Hgr M (i + 1)).obj (e₀ - t)) := by
    intro t
    induction t with
    | zero => intro _; exact hd₀ (e₀ - ((0 : ℕ) : ℤ)) (by push_cast; omega)
    | succ t ih =>
        intro ht
        push_cast at ht
        have h1 : Subsingleton ((C.Hgr (coker (M.mulLHom c)) i).obj (e₀ - (t : ℤ))) :=
          C.subsingleton_Hgr_quotL_of_le c j hj hcoh hres i hi (e₀ - (t : ℤ)) (by omega)
        have h2 : Subsingleton ((C.Hgr M (i + 1)).obj (e₀ - (t : ℤ))) := ih (by omega)
        have h3 : Subsingleton ((C.Hgr (M.twist (-1)) (i + 1)).obj (e₀ - (t : ℤ))) :=
          C.subsingleton_H_X₁ hSE i (e₀ - (t : ℤ)) h1 h2
        rw [C.subsingleton_Hgr_twist_iff] at h3
        have heq : e₀ - (t : ℤ) + -1 = e₀ - ((t + 1 : ℕ) : ℤ) := by push_cast; ring
        rwa [heq] at h3
  have hDe : D = e₀ - (((e₀ - D).toNat : ℕ) : ℤ) := by omega
  rw [hDe]
  exact key _ (by rw [← hDe]; exact hD)

end Cohomology

/-- API lemma for Theorem 2.3.8 (Boundedness of Regularity, Mumford):
for every pair of nonnegative integers `r` and `n` and every polynomial `P ∈ ℚ[z]` there is an
integer `m₀` such that, over every infinite field `k`, every subsheaf `F ⊆ 𝒪^{⊕r}` of `ℙⁿ_k`
with Hilbert polynomial `P` is `m₀`-regular.

The proof is Mumford's: induct on `n`; choose a hyperplane `H` avoiding the associated points
of `𝒪^{⊕r}/F`, so that the sequence `0 → F → 𝒪^{⊕r} → 𝒪^{⊕r}/F → 0` restricts to `H` and the
Hilbert polynomial of `F|_H` is the first difference `P(d) - P(d-1)`; apply the inductive
hypothesis to `F|_H ⊆ 𝒪_H^{⊕r}` to obtain `m₁`; deduce the regularity conditions in
cohomological degrees `≥ 2` for every `m ≥ m₁`; and bound `h¹(ℙⁿ, F(m₁))` by
`r·C(n+m₁, n) - P(m₁)`, using that `h¹` drops strictly until it vanishes.

See this folder's COMMENTARY.md for the off-by-one in the book's intermediate constant `m₂`
(the final bound `m₀` is unaffected). -/
theorem exists_boundsRegularity (r : ℕ) : ∀ (n : ℕ) (P : Polynomial ℚ),
    ∃ m₀ : ℤ, BoundsRegularity.{u} r n P m₀ := by
  intro n
  induction n with
  | zero =>
      intro P
      refine ⟨0, ?_⟩
      intro K _ _ C F f _ _ i hi
      exact C.subsingleton_of_lt F i (0 - i) (by omega)
  | succ n ih =>
      intro P
      obtain ⟨m₁', hm₁'⟩ := ih (P - P.comp (Polynomial.X - 1))
      obtain ⟨m₁, hm₁a, hm₁b⟩ : ∃ m₁ : ℤ, m₁' ≤ m₁ ∧ 0 ≤ m₁ :=
        ⟨max m₁' 0, le_max_left _ _, le_max_right _ _⟩
      obtain ⟨B, hB0, hB1⟩ : ∃ B : ℤ, 0 ≤ B ∧
          ⌈(r : ℚ) * ((((n : ℤ) + 1 + m₁).toNat.choose (n + 1) : ℕ) : ℚ)
            - P.eval (m₁ : ℚ)⌉ ≤ B :=
        ⟨max 0 ⌈(r : ℚ) * ((((n : ℤ) + 1 + m₁).toNat.choose (n + 1) : ℕ) : ℚ)
          - P.eval (m₁ : ℚ)⌉, le_max_left _ _, le_max_right _ _⟩
      refine ⟨m₁ + 1 + B, ?_⟩
      intro K _ _ C F₀ f₀ hf₀ hP₀
      have hOrcoh : C.IsCoherent ((structureModule K (n + 1)).pow r) :=
        C.isCoherent_pow C.isCoherent_structureModule r
      -- Mumford's argument, for a subsheaf whose quotient has no irrelevant torsion.  The
      -- hyperplane field is available only then; see this folder's COMMENTARY.
      have key : ∀ (F : GradedModule K (n + 1)) (f : F ⟶ (structureModule K (n + 1)).pow r)
          (Q : GradedModule K (n + 1)) (v : (structureModule K (n + 1)).pow r ⟶ Q),
          (∀ d, Function.Injective (f.app d).hom) → ShortExact f v →
          C.IsCoherent Q → C.NoIrrelevantTorsion Q →
          C.HasHilbertPolynomial F P → C.IsMRegular F (m₁ + 1 + B) := by
        intro F f Q v hf hSEf hQcoh hQtf hP
        -- coherence of the players
        have hFcoh : C.IsCoherent F := C.isCoherent_of_injective f hf hOrcoh
        -- a hyperplane avoiding the associated points of `𝒪^{⊕r}/F` and of `𝒪^{⊕r}`
        obtain ⟨c, j, hj, hLQ, hLOr⟩ :=
          C.exists_nonZeroDivisor_linearForm inferInstance Q
            ((structureModule K (n + 1)).pow r) hQcoh hOrcoh hQtf
            (C.noIrrelevantTorsion_pow_structureModule r)
        have hLF : ∀ d, Function.Injective ((F.mulLHom c).app d).hom :=
          injective_mulLHom_of_injective c f hf hLOr
        have hSEres : ShortExact (quotLMap f c) (quotLMap v c) :=
          shortExact_quotLMap hSEf c hLQ
        obtain ⟨eiso⟩ := nonempty_restrictL_pow_structureIso c j hj r
        have hf'inj : ∀ d, Function.Injective ((restrictLMap f c j ≫ eiso.hom).app d).hom := by
          intro d x y hxy
          exact hSEres.injective d ((isoApp eiso d).toLinearEquiv.injective hxy)
        -- the Hilbert polynomial of the restriction is the first difference of `P`
        have hPres : C.HasHilbertPolynomial (F.restrictL c j) (P - P.comp (Polynomial.X - 1)) := by
          intro d
          have h1 := hP d
          have h2 := hP (d + -1)
          have hcast : ((d + -1 : ℤ) : ℚ) = (d : ℚ) - 1 := by push_cast; ring
          rw [hcast] at h2
          rw [C.chi_restrictL F c j hj (C.isCoherent_restrictL hFcoh c j hj) d,
            C.chi_quotL hFcoh c hLF d, Polynomial.eval_sub,
            Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
            ← h1, ← h2]
          push_cast
          ring
        have hrescoh : C.IsCoherent (F.restrictL c j) := C.isCoherent_restrictL hFcoh c j hj
        have hres : C.IsMRegular (F.restrictL c j) m₁ :=
          C.isMRegular_of_le n _ hrescoh m₁' m₁
            (hm₁' K C (F.restrictL c j) (restrictLMap f c j ≫ eiso.hom) hf'inj hPres) hm₁a
        -- cohomology in degrees `≥ 2`
        have hhigh : ∀ i : ℕ, 1 ≤ i → ∀ D : ℤ, m₁ - i - 1 ≤ D →
            Subsingleton ((C.Hgr F (i + 1)).obj D) :=
          fun i hi D hD => C.subsingleton_Hgr_succ_of_le hFcoh c j hj hLF hres i hi D hD
        -- the `h¹` count
        have hSEmul : ShortExact (F.mulLHom c) (toCoker (F.mulLHom c)) := shortExact_toCoker _ hLF
        have hq1 : ∀ m : ℤ, m₁ - 1 ≤ m →
            Subsingleton ((C.Hgr (coker (F.mulLHom c)) 1).obj m) := fun m hm =>
          C.subsingleton_Hgr_quotL_of_le c j hj hrescoh hres 1 le_rfl m (by push_cast; omega)
        have halpha : ∀ m : ℤ, m₁ - 1 ≤ m →
            Function.Surjective ((C.map (F.mulLHom c) 1).app m).hom := fun m hm =>
          C.surjective_map_fst_of_subsingleton hSEmul 1 m (hq1 m hm)
        have hrank : ∀ m : ℤ, m₁ - 1 ≤ m →
            C.h F 1 (m + -1) = C.h F 1 m
              + Module.finrank K (LinearMap.range (C.δ hSEmul 0 m).hom) := by
          intro m hm
          have hfd : FiniteDimensional K ((C.Hgr (F.twist (-1)) 1).obj m) :=
            C.finiteDimensional (C.isCoherent_twist hFcoh (-1)) 1 m
          have hrn := LinearMap.finrank_range_add_finrank_ker ((C.map (F.mulLHom c) 1).app m).hom
          rw [LinearMap.range_eq_top.mpr (halpha m hm), finrank_top,
            ← C.range_δ hSEmul 0 m] at hrn
          have htw : Module.finrank K ((C.Hgr (F.twist (-1)) 1).obj m) = C.h F 1 (m + -1) :=
            (C.twistIso F (-1) 1 m).toLinearEquiv.finrank_eq
          have hhm : Module.finrank K ((C.Hgr F 1).obj m) = C.h F 1 m := rfl
          rw [← htw, ← hhm]
          exact hrn.symm
        have hnu_iff : ∀ m : ℤ, m₁ - 1 ≤ m →
            (C.h F 1 (m + -1) = C.h F 1 m ↔
              Function.Surjective ((C.map (toCoker (F.mulLHom c)) 0).app m).hom) := by
          intro m hm
          have hfd : FiniteDimensional K ((C.Hgr (F.twist (-1)) 1).obj m) :=
            C.finiteDimensional (C.isCoherent_twist hFcoh (-1)) 1 m
          rw [← C.range_δ_eq_bot_iff hSEmul 0 m, hrank m hm]
          constructor
          · intro heq
            exact Submodule.finrank_eq_zero.mp (by omega)
          · intro hbot
            rw [hbot]
            simp
        have hanti : ∀ D D' : ℤ, m₁ - 1 ≤ D → D ≤ D' → C.h F 1 D' ≤ C.h F 1 D := by
          intro D D' hD hDD'
          induction D', hDD' using Int.leInduction with
          | base => exact le_refl _
          | succ E hE ihE =>
              have hr := hrank (E + 1) (by omega)
              rw [show E + 1 + -1 = E from by ring] at hr
              omega
        have hzero_of_eq : ∀ m : ℤ, m₁ ≤ m →
            C.h F 1 (m + -1) = C.h F 1 m → C.h F 1 (m + -1) = 0 := by
          intro m hm heq
          have hall : ∀ p : ℤ, m ≤ p →
              Function.Surjective ((C.map (toCoker (F.mulLHom c)) 0).app p).hom :=
            C.surjective_map_toCoker_of_le hFcoh c j hj hres hm ((hnu_iff m (by omega)).mp heq)
          have hconst : ∀ p : ℤ, m ≤ p → C.h F 1 p = C.h F 1 (m + -1) := by
            intro p hp
            induction p, hp using Int.leInduction with
            | base => exact heq.symm
            | succ E hE ihE =>
                have hr := (hnu_iff (E + 1) (by omega)).mpr (hall (E + 1) (by omega))
                rw [show E + 1 + -1 = E from by ring] at hr
                omega
          obtain ⟨d₀, hd₀⟩ := C.serre_vanishing hFcoh 1 le_rfl
          have h1 := hconst (max m d₀) (le_max_left _ _)
          have h2 : C.h F 1 (max m d₀) = 0 :=
            C.h_eq_zero_of_subsingleton (hd₀ (max m d₀) (le_max_right _ _))
          omega
        have hstep : ∀ t : ℕ,
            C.h F 1 (m₁ + (t : ℤ)) = 0 ∨ C.h F 1 (m₁ + (t : ℤ)) + t ≤ C.h F 1 m₁ := by
          intro t
          induction t with
          | zero => right; simp
          | succ t iht =>
              have hnorm : m₁ + ((t + 1 : ℕ) : ℤ) = m₁ + (t : ℤ) + 1 := by push_cast; ring
              rw [hnorm]
              have hmono : C.h F 1 (m₁ + (t : ℤ) + 1) ≤ C.h F 1 (m₁ + (t : ℤ)) :=
                hanti (m₁ + (t : ℤ)) (m₁ + (t : ℤ) + 1) (by omega) (by omega)
              rcases iht with h0 | hle
              · left; omega
              · by_cases hEq : C.h F 1 (m₁ + (t : ℤ) + 1) = C.h F 1 (m₁ + (t : ℤ))
                · left
                  have hshift : m₁ + (t : ℤ) + 1 + -1 = m₁ + (t : ℤ) := by ring
                  have hz := hzero_of_eq (m₁ + (t : ℤ) + 1) (by omega) (by rw [hshift]; omega)
                  rw [hshift] at hz
                  omega
                · right
                  omega
        have hazero : C.h F 1 (m₁ + (C.h F 1 m₁ : ℤ)) = 0 := by
          rcases hstep (C.h F 1 m₁) with h | h
          · exact h
          · omega
        -- the numerical bound on `h¹(F(m₁))`
        have hvan : ∀ i : ℕ, 2 ≤ i → C.h F i m₁ = 0 := by
          intro i hi
          obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          exact C.h_eq_zero_of_subsingleton (hhigh i' (by omega) m₁ (by omega))
        have hchi : C.chi F m₁ = (C.h F 0 m₁ : ℤ) - (C.h F 1 m₁ : ℤ) := by
          have hsum := Cohomology.sum_range_eq_of_ge_two (fun i => (-1 : ℤ) ^ i * (C.h F i m₁ : ℤ))
            (fun i hi => by rw [hvan i hi]; simp) (n + 2) (by omega)
          have hc : C.chi F m₁ = ∑ i ∈ Finset.range (n + 2), (-1 : ℤ) ^ i * (C.h F i m₁ : ℤ) := rfl
          rw [hc, hsum]
          norm_num
          omega
        have hh0 : (C.h F 0 m₁ : ℤ)
            ≤ (r : ℤ) * ((((n : ℤ) + 1 + m₁).toNat.choose (n + 1) : ℕ) : ℤ) := by
          have hfdOr : FiniteDimensional K ((C.Hgr ((structureModule K (n + 1)).pow r) 0).obj m₁) :=
            C.finiteDimensional hOrcoh 0 m₁
          have hle : C.h F 0 m₁
              ≤ Module.finrank K ((C.Hgr ((structureModule K (n + 1)).pow r) 0).obj m₁) :=
            LinearMap.finrank_le_finrank_of_injective (C.injective_map_zero hSEf m₁)
          have hfdS : FiniteDimensional K ((C.Hgr (structureModule K (n + 1)) 0).obj m₁) :=
            C.finiteDimensional C.isCoherent_structureModule 0 m₁
          have heq : Module.finrank K ((C.Hgr ((structureModule K (n + 1)).pow r) 0).obj m₁)
              = r * (((n : ℤ) + 1 + m₁).toNat.choose (n + 1)) := by
            rw [(C.HgrPowIso (structureModule K (n + 1)) r 0 m₁).toLinearEquiv.finrank_eq]
            have : Module.finrank K (((C.Hgr (structureModule K (n + 1)) 0).pow r).obj m₁)
                = ∑ _i : Fin r, Module.finrank K ((C.Hgr (structureModule K (n + 1)) 0).obj m₁) :=
              Module.finrank_pi_fintype K
            rw [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
              C.finrank_HgrZero_structureModule m₁ hm₁b]
            norm_num
          omega
        have habound : (C.h F 1 m₁ : ℤ) ≤ B := by
          have hPm := hP m₁
          have hkey : ((C.h F 1 m₁ : ℤ) : ℚ)
              ≤ (r : ℚ) * ((((n : ℤ) + 1 + m₁).toNat.choose (n + 1) : ℕ) : ℚ)
                - P.eval (m₁ : ℚ) := by
            rw [← hPm, hchi]
            push_cast
            have : ((C.h F 0 m₁ : ℤ) : ℚ)
                ≤ ((r : ℤ) * ((((n : ℤ) + 1 + m₁).toNat.choose (n + 1) : ℕ) : ℤ) : ℚ) := by
              exact_mod_cast hh0
            push_cast at this
            linarith
          have hceil := Int.ceil_le_ceil hkey
          rw [Int.ceil_intCast] at hceil
          omega
        -- conclusion
        intro i hi
        rcases i with _ | i
        · omega
        rcases i with _ | i
        · have hle : C.h F 1 (m₁ + 1 + B - ((1 : ℕ) : ℤ)) ≤ C.h F 1 (m₁ + (C.h F 1 m₁ : ℤ)) := by
            refine hanti _ _ (by omega) ?_
            push_cast
            omega
          have hz : C.h F 1 (m₁ + 1 + B - ((1 : ℕ) : ℤ)) = 0 := by omega
          exact C.subsingleton_of_h_eq_zero hFcoh 1 _ hz
        · exact hhigh (i + 1) (by omega) (m₁ + 1 + B - ((i + 1 + 1 : ℕ) : ℤ)) (by push_cast; omega)
      -- apply it to `F₀`: replace `𝒪^{⊕r}/F₀` by its torsion-free model `N`, which enlarges
      -- `F₀` to `ker g` by a finite-length quotient, so cohomology and `P` are unchanged
      have hF₀coh : C.IsCoherent F₀ := C.isCoherent_of_injective f₀ hf₀ hOrcoh
      have hQ₀coh : C.IsCoherent (coker f₀) := C.isCoherent_coker f₀ hF₀coh hOrcoh
      have hSE₀ : ShortExact f₀ (toCoker f₀) := shortExact_toCoker f₀ hf₀
      obtain ⟨N, φ, hNcoh, hNtf, hφsurj, ⟨e₀, he₀⟩, hφbij⟩ :=
        C.exists_noIrrelevantTorsion_quotient hQ₀coh
      have hgsurj : ∀ d, Function.Surjective (((toCoker f₀ ≫ φ)).app d).hom := by
        intro d z
        obtain ⟨y, hy⟩ := hφsurj d z
        obtain ⟨x, hx⟩ := surjective_toCoker_app f₀ d y
        refine ⟨x, ?_⟩
        show (φ.app d).hom (((toCoker f₀).app d).hom x) = z
        rw [hx, hy]
      have hzero : ∀ (d : ℤ) (x : F₀.obj d),
          (((toCoker f₀ ≫ φ)).app d).hom ((f₀.app d).hom x) = 0 := by
        intro d x
        have h1 : ((toCoker f₀).app d).hom ((f₀.app d).hom x) = 0 := by
          have hex := hSE₀.exact d
          exact LinearMap.mem_ker.mp (hex ▸ LinearMap.mem_range_self _ x)
        show (φ.app d).hom (((toCoker f₀).app d).hom ((f₀.app d).hom x)) = 0
        rw [h1, map_zero]
      have huinj : ∀ d, Function.Injective
          (((kerLift (toCoker f₀ ≫ φ) f₀ hzero).app d).hom) :=
        injective_kerLift _ f₀ hzero hf₀
      have hSEu : ShortExact (kerLift (toCoker f₀ ≫ φ) f₀ hzero)
          (toCoker (kerLift (toCoker f₀ ≫ φ) f₀ hzero)) := shortExact_toCoker _ huinj
      -- the enlargement is an equality in all large degrees
      have hTzero : ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
          Subsingleton ((coker (kerLift (toCoker f₀ ≫ φ) f₀ hzero)).obj d) := by
        refine ⟨e₀, fun d hd => ?_⟩
        have hsurj : Function.Surjective
            (((kerLift (toCoker f₀ ≫ φ) f₀ hzero).app d).hom) := by
          rintro ⟨y, hy⟩
          rw [LinearMap.mem_ker] at hy
          have hy0 : ((toCoker f₀).app d).hom y = 0 :=
            he₀ d hd (by rw [map_zero]; exact hy)
          have hy1 : y ∈ LinearMap.range ((f₀.app d).hom) := by
            rw [hSE₀.exact d, LinearMap.mem_ker]
            exact hy0
          obtain ⟨x, hx⟩ := hy1
          exact ⟨x, Subtype.ext hx⟩
        refine ⟨fun a b => ?_⟩
        obtain ⟨a', rfl⟩ := Submodule.Quotient.mk_surjective _ a
        obtain ⟨b', rfl⟩ := Submodule.Quotient.mk_surjective _ b
        obtain ⟨a'', rfl⟩ := hsurj a'
        obtain ⟨b'', rfl⟩ := hsurj b'
        exact (Submodule.Quotient.eq _).mpr (by
          rw [← map_sub]
          exact LinearMap.mem_range_self _ _)
      have hubij : ∀ (i : ℕ) (d : ℤ),
          Function.Bijective ((C.map (kerLift (toCoker f₀ ≫ φ) f₀ hzero) i).app d).hom :=
        fun i d => C.bijective_map_of_shortExact_of_subsingleton hSEu
          (C.subsingleton_Hgr_of_eventually_zero hTzero) i d
      refine (C.isMRegular_congr _ hubij (m₁ + 1 + B)).mpr ?_
      exact key _ (kerι (toCoker f₀ ≫ φ)) N (toCoker f₀ ≫ φ)
        (fun _ => Subtype.val_injective) (shortExact_kerι _ hgsurj) hNcoh hNtf
        ((C.hasHilbertPolynomial_congr _ hubij P).mp hP₀)

/-- **Theorem 2.3.8** (`thm:boundedness-of-regularity`) (Boundedness of Regularity, Mumford):
for every pair of nonnegative integers `r` and `n` and every polynomial `P ∈ ℚ[z]` there is an
integer `m₀` such that, **over every field** `k`, every subsheaf `F ⊆ 𝒪^{⊕r}` of `ℙⁿ_k` with
Hilbert polynomial `P` is `m₀`-regular.

The reduction to the infinite-field case `exists_boundsRegularity` is the book's first step:
`m`-regularity, coherence and all cohomological dimensions are unchanged by flat base change
along a field extension, and every field embeds into an infinite one. -/
theorem exists_boundsRegularity_of_field (r n : ℕ) (P : Polynomial ℚ) :
    ∃ m₀ : ℤ, ∀ (K : Type u) [Field K] (C : Cohomology K), C.HasInfiniteBaseChange →
      ∀ (F : GradedModule K n)
      (f : F ⟶ (structureModule K n).pow r), (∀ d, Function.Injective (f.app d).hom) →
      C.HasHilbertPolynomial F P → C.IsMRegular F m₀ := by
  obtain ⟨m₀, hm₀⟩ := exists_boundsRegularity.{u} r n P
  refine ⟨m₀, ?_⟩
  intro K _ C hC F f hf hP
  obtain ⟨K', instK', C', hinf, hbc⟩ := hC
  obtain ⟨bc⟩ := hbc
  obtain ⟨f', hf'⟩ := bc.mono f hf
  have hP' : C'.HasHilbertPolynomial (bc.obj F) P := by
    intro d
    have hchi : C'.chi (bc.obj F) d = C.chi F d :=
      Finset.sum_congr rfl fun i _ => congrArg _ (congrArg _ (bc.finrank_eq F i d))
    rw [hchi]
    exact hP d
  intro i hi
  rw [← bc.subsingleton_iff F i (m₀ - i)]
  exact hm₀ K' C' (bc.obj F) f' hf' hP' i hi

end AlgebraicGeometry.ProjectiveSpace

end ThmBoundednessOfRegularity

section EqnLambdarn

open Polynomial

/-- Background definition for Equation 2.3.13 (the implicit definition of the binomial
coefficient polynomials, from the unlabeled remark after
Theorem 2.3.8): the binomial coefficient polynomial
`C(z, i) = z(z-1)⋯(z-i+1)/i! ∈ ℚ[z]`. Its value at a natural number `n` is the
binomial coefficient `n.choose i`. -/
noncomputable def Polynomial.binomialPoly (i : ℕ) : Polynomial ℚ :=
  (i.factorial : ℚ)⁻¹ • descPochhammer ℚ i

/-- The value of the binomial coefficient polynomial `C(z, i)` at a natural number `n` is
the binomial coefficient `C(n, i)`. -/
lemma Polynomial.binomialPoly_eval_natCast (i n : ℕ) :
    (binomialPoly i).eval (n : ℚ) = n.choose i := by
  rw [binomialPoly, eval_smul, smul_eq_mul, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- Background definition for Equation 2.3.13 (the implicit definition of a numerical
polynomial, from the unlabeled remark after Theorem 2.3.8): a
polynomial `P ∈ ℚ[z]` is **numerical** if `P(n)` is an integer for all large
natural numbers `n` (equivalently, by the basis theorem, for all integers). The book
asks integrality at all integers `d ≫ 0`; see this folder's COMMENTARY.md. -/
def Polynomial.IsNumerical (P : Polynomial ℚ) : Prop :=
  ∀ᶠ n : ℕ in Filter.atTop, ∃ m : ℤ, P.eval (n : ℚ) = m

/-- The zero polynomial is numerical. -/
lemma Polynomial.isNumerical_zero : (0 : Polynomial ℚ).IsNumerical := by
  refine Filter.Eventually.of_forall fun _ ↦ ⟨0, ?_⟩
  simp

/-- The sum of two numerical polynomials is numerical. -/
lemma Polynomial.IsNumerical.add {P Q : Polynomial ℚ}
    (hP : P.IsNumerical) (hQ : Q.IsNumerical) : (P + Q).IsNumerical := by
  filter_upwards [hP, hQ] with n hnP hnQ
  obtain ⟨a, ha⟩ := hnP
  obtain ⟨b, hb⟩ := hnQ
  refine ⟨a + b, ?_⟩
  rw [eval_add, ha, hb]
  push_cast
  rfl

/-- The negative of a numerical polynomial is numerical. -/
lemma Polynomial.IsNumerical.neg {P : Polynomial ℚ} (hP : P.IsNumerical) : (-P).IsNumerical := by
  filter_upwards [hP] with n hn
  obtain ⟨a, ha⟩ := hn
  refine ⟨-a, ?_⟩
  rw [eval_neg, ha]
  norm_cast

/-- An integral scalar multiple of a numerical polynomial is numerical. -/
lemma Polynomial.IsNumerical.smul_int {P : Polynomial ℚ} (hP : P.IsNumerical) (a : ℤ) :
    ((a : ℚ) • P).IsNumerical := by
  filter_upwards [hP] with n hn
  obtain ⟨b, hb⟩ := hn
  refine ⟨a * b, ?_⟩
  rw [eval_smul, smul_eq_mul, hb]
  push_cast
  rfl

/-- A finite sum of numerical polynomials is numerical. -/
lemma Polynomial.isNumerical_finset_sum {ι : Type*} {s : Finset ι}
    {P : ι → Polynomial ℚ} (hP : ∀ i ∈ s, (P i).IsNumerical) :
    (∑ i ∈ s, P i).IsNumerical := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Polynomial.isNumerical_zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hP i (Finset.mem_insert_self i s)).add
        (ih fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))

/-- The binomial coefficient polynomials are numerical. -/
lemma Polynomial.isNumerical_binomialPoly (i : ℕ) : (binomialPoly i).IsNumerical := by
  refine Filter.Eventually.of_forall fun n ↦ ⟨n.choose i, ?_⟩
  rw [binomialPoly_eval_natCast]
  norm_cast

/-- The binomial coefficient polynomial `C(z, i)` has degree `i`; the family of binomial
polynomials is a polynomial sequence in the sense of `Polynomial.Sequence`. -/
noncomputable def Polynomial.binomialPolySequence : Polynomial.Sequence ℚ where
  elems' := binomialPoly
  degree_eq' i := by
    rw [binomialPoly, Polynomial.smul_eq_C_mul,
      Polynomial.degree_C_mul (inv_ne_zero (by positivity)),
      Polynomial.degree_eq_natDegree (monic_descPochhammer ℚ i).ne_zero,
      descPochhammer_natDegree]

/-- The binomial coefficient polynomials `C(z, i)`, `i = 0, 1, 2, …`, are linearly
independent over `ℚ` (they have pairwise distinct degrees). In particular the
representation of a numerical polynomial as an integral combination of binomial
polynomials is unique. -/
lemma Polynomial.linearIndependent_binomialPoly :
    LinearIndependent ℚ fun i : ℕ ↦ binomialPoly i :=
  binomialPolySequence.linearIndependent

/-- API lemma for Equation 2.3.13 (uniqueness of the numerical-polynomial
expansion, from the unlabeled remark after Theorem 2.3.8): an
integral linear combination of the binomial coefficient polynomials has unique
coefficients. More precisely, if two combinations supported in degrees at most `d` are
equal, then their coefficients agree in every degree at most `d`. -/
lemma Polynomial.sum_binomialPoly_injective {d : ℕ} {a b : ℕ → ℤ}
    (h : ∑ i ∈ Finset.range (d + 1), (a i : ℚ) • binomialPoly i =
      ∑ i ∈ Finset.range (d + 1), (b i : ℚ) • binomialPoly i) :
    ∀ i ≤ d, a i = b i := by
  have hzero : ∑ i ∈ Finset.range (d + 1),
      ((a i : ℚ) - (b i : ℚ)) • binomialPoly i = 0 := by
    simp_rw [sub_smul]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  intro i hi
  have hi' : i ∈ Finset.range (d + 1) := Finset.mem_range.mpr (by omega)
  have hc := (linearIndependent_iff'.mp linearIndependent_binomialPoly)
    (Finset.range (d + 1)) (fun j ↦ (a j : ℚ) - (b j : ℚ)) hzero i hi'
  exact_mod_cast sub_eq_zero.mp hc

/-- The zeroth binomial coefficient polynomial is the constant `1`. -/
lemma Polynomial.binomialPoly_zero : binomialPoly 0 = 1 := by
  rw [binomialPoly, descPochhammer_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
    one_smul]

/-- **Pascal's rule** for binomial polynomials: the difference operator sends `C(z, i+1)`
to `C(z, i)`, that is `C(z+1, i+1) - C(z, i+1) = C(z, i)`. -/
lemma Polynomial.binomialPoly_comp_X_add_one_sub_self (i : ℕ) :
    (binomialPoly (i + 1)).comp (X + 1) - binomialPoly (i + 1) = binomialPoly i := by
  haveI : Infinite ℚ := Infinite.of_injective ((↑) : ℕ → ℚ) Nat.cast_injective
  apply Polynomial.funext
  intro x
  have hsucc : (descPochhammer ℚ (i + 1)).eval (x + 1) =
      (x + 1) * (descPochhammer ℚ i).eval x := by
    rw [descPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_sub, eval_X, eval_one,
      add_sub_cancel_right]
  have hsucc' : (descPochhammer ℚ (i + 1)).eval x =
      (descPochhammer ℚ i).eval x * (x - i) := by
    rw [descPochhammer_succ_right, eval_mul, eval_sub, eval_X, eval_natCast]
  have h0 : (i.factorial : ℚ) ≠ 0 := by positivity
  have h1 : ((i : ℚ) + 1) ≠ 0 := by positivity
  simp only [binomialPoly]
  rw [eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_smul, eval_smul, eval_smul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, hsucc, hsucc', Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Numerical polynomials of degree at most `d` are integral combinations of the binomial
polynomials `C(z, 0), …, C(z, d)`; the induction on `d` behind
`Polynomial.IsNumerical.exists_sum_binomialPoly`. -/
theorem Polynomial.IsNumerical.exists_sum_binomialPoly_of_natDegree_le {d : ℕ} :
    ∀ {P : Polynomial ℚ}, P.natDegree ≤ d → P.IsNumerical →
      ∃ a : ℕ → ℤ, P = ∑ i ∈ Finset.range (d + 1), (a i : ℚ) • binomialPoly i := by
  induction d with
  | zero =>
    intro P hd hP
    obtain ⟨n, m, hm⟩ := hP.exists
    have hPC : P = C (P.coeff 0) := eq_C_of_natDegree_le_zero hd
    have hc : P.coeff 0 = (m : ℚ) := by
      rw [hPC, eval_C] at hm
      exact hm
    refine ⟨fun _ ↦ m, ?_⟩
    rw [hPC, hc, Finset.sum_range_one, binomialPoly_zero, Polynomial.smul_eq_C_mul,
      mul_one]
  | succ d ih =>
    intro P hd hP
    by_cases hPd' : P.natDegree ≤ d
    · obtain ⟨a, ha⟩ := ih hPd' hP
      refine ⟨fun i ↦ if i = d + 1 then 0 else a i, ?_⟩
      rw [Finset.sum_range_succ,
        show ((fun i ↦ if i = d + 1 then (0 : ℤ) else a i) (d + 1)) = 0 from if_pos rfl,
        Int.cast_zero, zero_smul, add_zero, ha]
      exact Finset.sum_congr rfl fun i hi ↦ by
        rw [show ((fun j ↦ if j = d + 1 then (0 : ℤ) else a j) i) = a i from
          if_neg (Finset.mem_range.mp hi).ne]
    · have hPd : P.natDegree = d + 1 := le_antisymm hd (by omega)
      have hPne : P ≠ 0 := fun h ↦ by simp [h] at hPd
      have hcompdeg : (P.comp (X + 1)).natDegree = P.natDegree := by
        rw [show (X + 1 : Polynomial ℚ) = X + C 1 by rw [C_1], natDegree_comp,
          natDegree_X_add_C, mul_one]
      have hcompne : P.comp (X + 1) ≠ 0 := fun h ↦ by
        rw [h, natDegree_zero] at hcompdeg
        omega
      have hdeg : (P.comp (X + 1) - P).degree < P.degree := by
        have h := degree_sub_lt
          (p := P.comp (X + 1)) (q := P)
          (by rw [degree_eq_natDegree hcompne, degree_eq_natDegree hPne, hcompdeg])
          hcompne
          (by rw [show (X + 1 : Polynomial ℚ) = X + C 1 by rw [C_1],
            leadingCoeff_comp (by rw [natDegree_X_add_C]; omega),
            (monic_X_add_C (1 : ℚ)).leadingCoeff, one_pow, mul_one])
        rwa [degree_eq_natDegree hcompne, hcompdeg, ← degree_eq_natDegree hPne] at h
      have hQd : (P.comp (X + 1) - P).natDegree ≤ d := by
        rcases eq_or_ne (P.comp (X + 1) - P) 0 with h | h
        · simp [h]
        · have h2 := natDegree_lt_natDegree h hdeg
          omega
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hP
      have hQnum : (P.comp (X + 1) - P).IsNumerical := by
        refine Filter.eventually_atTop.mpr ⟨N, fun n hn ↦ ?_⟩
        obtain ⟨m1, hm1⟩ := hN (n + 1) (by omega)
        obtain ⟨m2, hm2⟩ := hN n hn
        refine ⟨m1 - m2, ?_⟩
        have hcast : ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) := by push_cast; ring
        rw [eval_sub, eval_comp, eval_add, eval_X, eval_one, hcast, hm1, hm2]
        push_cast
        ring
      obtain ⟨b, hb⟩ := ih hQd hQnum
      have hΔT : (∑ i ∈ Finset.range (d + 1),
          (b i : ℚ) • binomialPoly (i + 1)).comp (X + 1) -
          (∑ i ∈ Finset.range (d + 1), (b i : ℚ) • binomialPoly (i + 1)) =
          P.comp (X + 1) - P := by
        rw [hb, Polynomial.sum_comp, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ ↦ by
          rw [Polynomial.smul_comp, ← smul_sub, binomialPoly_comp_X_add_one_sub_self]
      set P₀ := P - ∑ i ∈ Finset.range (d + 1), (b i : ℚ) • binomialPoly (i + 1)
        with hP₀
      have hΔP₀ : P₀.comp (X + 1) - P₀ = 0 := by
        rw [hP₀, sub_comp]
        rw [show P.comp (X + 1) -
            (∑ i ∈ Finset.range (d + 1), (b i : ℚ) • binomialPoly (i + 1)).comp (X + 1) -
            (P - ∑ i ∈ Finset.range (d + 1), (b i : ℚ) • binomialPoly (i + 1)) =
            (P.comp (X + 1) - P) -
            ((∑ i ∈ Finset.range (d + 1),
              (b i : ℚ) • binomialPoly (i + 1)).comp (X + 1) -
              ∑ i ∈ Finset.range (d + 1), (b i : ℚ) • binomialPoly (i + 1)) from by ring,
          hΔT, sub_self]
      have hval : ∀ n : ℕ, P₀.eval ((n : ℚ)) = P₀.eval 0 := by
        intro n
        induction n with
        | zero => norm_num
        | succ k ihk =>
          have h0 : P₀.eval ((k : ℚ) + 1) - P₀.eval (k : ℚ) = 0 := by
            have hev := congrArg (Polynomial.eval ((k : ℚ))) hΔP₀
            simpa [eval_sub, eval_comp] using hev
          have hcast : ((k + 1 : ℕ) : ℚ) = (k : ℚ) + 1 := by push_cast; ring
          rw [hcast, sub_eq_zero.mp h0, ihk]
      have hP₀C : P₀ = C (P₀.eval 0) := by
        have hroot : P₀ - C (P₀.eval 0) = 0 := by
          apply eq_zero_of_infinite_isRoot
          apply Set.infinite_of_injective_forall_mem
            (f := fun n : ℕ ↦ (n : ℚ)) Nat.cast_injective
          intro n
          change (P₀ - C (P₀.eval 0)).eval ((n : ℚ)) = 0
          rw [eval_sub, eval_C, hval n, sub_self]
        exact sub_eq_zero.mp hroot
      have hP₀int : ∃ c : ℤ, P₀.eval 0 = c := by
        obtain ⟨m, hm⟩ := hN N le_rfl
        refine ⟨m - ∑ i ∈ Finset.range (d + 1), b i * (N.choose (i + 1) : ℤ), ?_⟩
        rw [← hval N, hP₀, eval_sub, hm, eval_finsetSum]
        push_cast
        congr 1
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [eval_smul, smul_eq_mul, binomialPoly_eval_natCast]
      obtain ⟨c, hc⟩ := hP₀int
      refine ⟨fun i ↦ if i = 0 then c else b (i - 1), ?_⟩
      have hsplit : P = P₀ + ∑ i ∈ Finset.range (d + 1),
          (b i : ℚ) • binomialPoly (i + 1) := by
        rw [hP₀]
        ring
      rw [Finset.sum_range_succ',
        show ((fun i ↦ if i = 0 then c else b (i - 1)) 0) = c from if_pos rfl,
        binomialPoly_zero, Polynomial.smul_eq_C_mul, mul_one, hsplit, hP₀C, hc, add_comm]
      congr 1

/-- API lemma for Equation 2.3.13 (existence of the numerical-polynomial
expansion, from the unlabeled remark after Theorem 2.3.8; cf.
Hartshorne Prop. I.7.3): **numerical polynomials are integral combinations of binomial
polynomials.** Every numerical polynomial `P ∈ ℚ[z]` of degree `d` can be written as
`P(z) = ∑_{i ≤ d} aᵢ C(z, i)` with integer coefficients `aᵢ` (uniquely, by
`Polynomial.linearIndependent_binomialPoly`). The proof is by induction on the degree
using the difference operator `Δ P(z) = P(z+1) - P(z)`. -/
theorem Polynomial.IsNumerical.exists_sum_binomialPoly {P : Polynomial ℚ}
    (hP : P.IsNumerical) :
    ∃ a : ℕ → ℤ,
      P = ∑ i ∈ Finset.range (P.natDegree + 1), (a i : ℚ) • binomialPoly i :=
  hP.exists_sum_binomialPoly_of_natDegree_le le_rfl

/-- Every finite integral linear combination of binomial coefficient polynomials is
numerical. -/
lemma Polynomial.isNumerical_of_eq_sum_binomialPoly {P : Polynomial ℚ} {d : ℕ}
    {a : ℕ → ℤ}
    (hP : P = ∑ i ∈ Finset.range (d + 1), (a i : ℚ) • binomialPoly i) :
    P.IsNumerical := by
  rw [hP]
  apply Polynomial.isNumerical_finset_sum
  intro i _
  exact (Polynomial.isNumerical_binomialPoly i).smul_int (a i)

/-- API lemma for Equation 2.3.13 (the characterization of numerical
polynomials, from the unlabeled remark after Theorem 2.3.8): a
rational polynomial is numerical if and only if it is a finite integral linear
combination of the binomial coefficient polynomials. The forward representation can be
taken in degrees at most the degree of the polynomial. -/
theorem Polynomial.isNumerical_iff_exists_sum_binomialPoly {P : Polynomial ℚ} :
    P.IsNumerical ↔ ∃ d : ℕ, ∃ a : ℕ → ℤ,
      P = ∑ i ∈ Finset.range (d + 1), (a i : ℚ) • binomialPoly i := by
  constructor
  · intro hP
    obtain ⟨a, ha⟩ := hP.exists_sum_binomialPoly
    exact ⟨P.natDegree, a, ha⟩
  · rintro ⟨d, a, ha⟩
    exact Polynomial.isNumerical_of_eq_sum_binomialPoly ha

/-- Background definition for Equation 2.3.13 (the implicit definition of the integral
coefficients `aᵢ`, from the unlabeled remark after Theorem 2.3.8):
the canonical integral coefficients of a numerical polynomial in the binomial
coefficient basis. Coefficients above the degree of the polynomial are immaterial and
are fixed by the chosen representative. -/
noncomputable def Polynomial.IsNumerical.binomialCoeffs {P : Polynomial ℚ}
    (hP : P.IsNumerical) : ℕ → ℤ :=
  hP.exists_sum_binomialPoly.choose

/-- A numerical polynomial is the integral linear combination of binomial coefficient
polynomials given by its canonical coefficients. -/
lemma Polynomial.IsNumerical.sum_binomialCoeffs {P : Polynomial ℚ}
    (hP : P.IsNumerical) :
    P = ∑ i ∈ Finset.range (P.natDegree + 1),
      (hP.binomialCoeffs i : ℚ) • binomialPoly i :=
  hP.exists_sum_binomialPoly.choose_spec

/-- Any integral binomial-basis expansion of a numerical polynomial has the canonical
coefficients in every degree at most the degree of the polynomial. -/
lemma Polynomial.IsNumerical.eq_binomialCoeffs {P : Polynomial ℚ}
    (hP : P.IsNumerical) {a : ℕ → ℤ}
    (ha : P = ∑ i ∈ Finset.range (P.natDegree + 1),
      (a i : ℚ) • binomialPoly i) :
    ∀ i ≤ P.natDegree, a i = hP.binomialCoeffs i := by
  apply sum_binomialPoly_injective
  exact ha.symm.trans hP.sum_binomialCoeffs

end EqnLambdarn

section RmkOptimalBounds

open Polynomial

/-- Background definition for Remark 2.3.15 (the implicit definition of Gotzmann's normal
form): the polynomial `∑ᵢ C(z + λᵢ - i, λᵢ - 1)` attached to a sequence `λ₁ ≥ ⋯ ≥ λ_r ≥ 1`,
with the book's index `i` running from `1` to `r`.

The same polynomial appears again as Equation (2.5.7) in
Hartshorne's non-emptiness criterion for `Hilb^P(ℙⁿ)`; §2.5's `Polynomial.hilbertPartitionPoly`
is by definition this one.

Gotzmann's theorem — that every Hilbert polynomial of a projective scheme `X ⊆ ℙᴺ` is of this
form for a unique decreasing sequence, and that the ideal sheaf `𝓘_X` is then `r`-regular — is
a deep result of a different nature from Mumford's bound, quoted by the book without proof;
only the normal form itself is formalized here. See this folder's COMMENTARY.md. -/
noncomputable def Polynomial.gotzmannPoly (l : List ℕ) : Polynomial ℚ :=
  (l.zipIdx.map fun p ↦
    (binomialPoly (p.1 - 1)).comp (X + C ((p.1 : ℚ) - (p.2 + 1)))).sum

/-- Shifting the variable by an integer preserves numericality. -/
lemma Polynomial.IsNumerical.comp_X_add_intCast {P : Polynomial ℚ} (hP : P.IsNumerical) (m : ℤ) :
    (P.comp (X + C ((m : ℤ) : ℚ))).IsNumerical := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hP
  refine Filter.eventually_atTop.mpr ⟨N + m.natAbs, fun n hn => ?_⟩
  have hnm : 0 ≤ (n : ℤ) + m := by omega
  obtain ⟨z, hz⟩ := hN ((n : ℤ) + m).toNat (by omega)
  refine ⟨z, ?_⟩
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, ← hz]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hnm).symm

lemma Polynomial.IsNumerical.comp_X_add_C_intCast {P : Polynomial ℚ} (hP : P.IsNumerical)
    {q : ℚ} {m : ℤ} (hq : q = (m : ℚ)) : (P.comp (X + C q)).IsNumerical := by
  subst hq
  exact hP.comp_X_add_intCast m

lemma Polynomial.isNumerical_list_sum :
    ∀ L : List (Polynomial ℚ), (∀ P ∈ L, P.IsNumerical) → L.sum.IsNumerical
  | [], _ => by simpa using isNumerical_zero
  | P :: L, h => by
      rw [List.sum_cons]
      exact (h P (by simp)).add (isNumerical_list_sum L fun Q hQ => h Q (by simp [hQ]))

/-- Gotzmann's normal form is a numerical polynomial. -/
lemma Polynomial.isNumerical_gotzmannPoly (l : List ℕ) : (gotzmannPoly l).IsNumerical := by
  refine isNumerical_list_sum _ ?_
  intro P hP
  simp only [List.mem_map] at hP
  obtain ⟨p, -, rfl⟩ := hP
  exact (isNumerical_binomialPoly (p.1 - 1)).comp_X_add_C_intCast
    (m := (p.1 : ℤ) - (p.2 + 1)) (by push_cast; ring)

/-- **Remark 2.3.15** (`rmk:optimal-bounds`) (the displayed identity): the value of Gotzmann's
normal form at a natural number `d` is the sum of binomial coefficients
`∑ᵢ C(d + λᵢ - i, λᵢ - 1)` of the book's display, provided each `d + λᵢ ≥ i`. -/
lemma Polynomial.gotzmannPoly_eval (l : List ℕ) (d : ℕ)
    (h : ∀ p ∈ l.zipIdx, p.2 + 1 ≤ d + p.1) :
    (gotzmannPoly l).eval (d : ℚ)
      = (l.zipIdx.map fun p => ((d + p.1 - (p.2 + 1)).choose (p.1 - 1) : ℚ)).sum := by
  rw [gotzmannPoly, ← Polynomial.coe_evalRingHom, map_list_sum, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
  have hcast : (d : ℚ) + ((p.1 : ℚ) - (p.2 + 1)) = ((d + p.1 - (p.2 + 1) : ℕ) : ℚ) := by
    have := h p hp
    push_cast [Nat.cast_sub this]
    ring
  simp only [Function.comp_apply, Polynomial.coe_evalRingHom, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [hcast, Polynomial.binomialPoly_eval_natCast]

-- Gotzmann's regularity bound itself (the ideal sheaf of `X` is `r`-regular) and the
-- uniqueness of the sequence `λ₁ ≥ ⋯ ≥ λ_r ≥ 1` are quoted by the book from
-- [gotzmann], [bruns-herzog, §4.3], [green-restrictions]; they are outside the chapter and
-- are left as prose, as are the two further remarks of the subsection (the Gruson–Lazarsfeld–
-- Peskine bound `(d-N+2)` for integral non-degenerate curves and the Eisenbud–Goto
-- conjecture).  See this folder's COMMENTARY.md.
-- STATUS: remark-complete

end RmkOptimalBounds

section PropRegularityInFamilies

open CategoryTheory AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.ProjectiveSpace.GradedModule

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {R : Type u} [CommRing R] (Crel : RelativeCohomology R) {n : ℕ}
variable (M : GradedModule R n)

/-- API lemma for Proposition 2.3.18 (the fibrewise input): if every
fibre `Q_s` of the family is `m`-regular, then for `d ≥ m` every fibre has vanishing higher
cohomology at the twist `d`.

This is the one step of the book's proof that is not a citation: it is
Proposition 2.3.5(3) applied on each fibre. -/
theorem subsingleton_Hgr_fibre_of_le (hM : Crel.IsCoherent M) {m : ℤ}
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ],
      (Crel.fibre κ).IsMRegular (M.baseChange κ) m)
    {d : ℤ} (hd : m ≤ d) (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ) (hi : 1 ≤ i) :
    Subsingleton (((Crel.fibre κ).Hgr (M.baseChange κ) i).obj d) :=
  (Crel.fibre κ).subsingleton_Hgr_of_le_of_field (Crel.isCoherent_fibre M hM κ)
    (Crel.fibre_hasInfiniteBaseChange κ) (hfib κ) hd i hi

/-- **Proposition 2.3.18** (`prop:regularity-in-families`, part (1)) (Regularity in Families): let `S`
be a noetherian scheme, `π : ℙⁿ_S → S` relative projective space and `Q` a coherent sheaf on
`ℙⁿ_S` flat over `S` all of whose fibres `Q_s` are `m`-regular. Then for `d ≥ m` the
pushforward `π_* Q(d)` is a vector bundle whose formation commutes with base change.

Formalized over an affine base `S = Spec R`; see this folder's COMMENTARY.md. -/
theorem finite_projective_Hgr_zero_of_fibres (hM : Crel.IsCoherent M) (hflat : Crel.IsFlat M)
    {m : ℤ} (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ],
      (Crel.fibre κ).IsMRegular (M.baseChange κ) m)
    {d : ℤ} (hd : m ≤ d) :
    Module.Finite R ((Crel.Hgr M 0).obj d) ∧ Module.Projective R ((Crel.Hgr M 0).obj d) ∧
      Crel.CommutesWithBaseChange M d := by
  obtain ⟨-, hfin, hproj, hbc⟩ :=
    Crel.cbc M d hM hflat (subsingleton_Hgr_fibre_of_le Crel M hM hfib hd)
  exact ⟨hfin, hproj, hbc⟩

/-- API lemma for Proposition 2.3.18 (part (1)) (constancy consequence):
over a local base, a coherent flat family whose fibres are uniformly regular has the same
dimension of global sections on every field fibre in each twist `d ≥ m`.

This is the rank-theoretic step used to compare the generic and closed Hilbert polynomials
of a flat family over a discrete valuation ring. -/
theorem finrank_Hgr_fibre_zero_eq_fibre_zero_of_fibres_regular [IsLocalRing R]
    (hM : Crel.IsCoherent M) (hflat : Crel.IsFlat M)
    {m : ℤ} (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ],
      (Crel.fibre κ).IsMRegular (M.baseChange κ) m)
    {d : ℤ} (hd : m ≤ d)
    (κ κ' : Type u) [Field κ] [Algebra R κ] [Field κ'] [Algebra R κ'] :
    Module.finrank κ (((Crel.fibre κ).Hgr (M.baseChange κ) 0).obj d) =
      Module.finrank κ' (((Crel.fibre κ').Hgr (M.baseChange κ') 0).obj d) := by
  obtain ⟨hfin, hproj, hbc⟩ :=
    finite_projective_Hgr_zero_of_fibres Crel M hM hflat hfib hd
  exact Crel.finrank_fibre_zero_eq_fibre_zero_of_finite_projective_of_isLocalRing
    M d hfin hproj hbc κ κ'

/-- **Proposition 2.3.18** (`prop:regularity-in-families`, part (2)): under the same hypotheses,
`Rⁱπ_* Q(d) = 0` for `i > 0` and `d ≥ m`. -/
theorem subsingleton_Hgr_of_fibres (hM : Crel.IsCoherent M) (hflat : Crel.IsFlat M)
    {m : ℤ} (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ],
      (Crel.fibre κ).IsMRegular (M.baseChange κ) m)
    {d : ℤ} (hd : m ≤ d) (i : ℕ) (hi : 1 ≤ i) : Subsingleton ((Crel.Hgr M i).obj d) :=
  (Crel.cbc M d hM hflat (subsingleton_Hgr_fibre_of_le Crel M hM hfib hd)).1 i hi

/-- **Proposition 2.3.18** (`prop:regularity-in-families`, part (3)): under the same hypotheses,
`π^* π_* Q(d) → Q(d)` is surjective for `d ≥ m`.

The book's argument is that the cokernel `C` satisfies `C ⊗ κ(s) = 0` for every `s ∈ S`, by
part (1) and Proposition 2.3.5(3) on the fibre; here that is the fibrewise global generation
fed to the Nakayama step of the interface. -/
theorem isGloballyGenerated_of_fibres_regular (hM : Crel.IsCoherent M) (hflat : Crel.IsFlat M)
    {m : ℤ} (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ],
      (Crel.fibre κ).IsMRegular (M.baseChange κ) m)
    {d : ℤ} (hd : m ≤ d) : Crel.IsGloballyGenerated M d := by
  refine Crel.isGloballyGenerated_of_fibres M d hM hflat (fun κ _ _ e hde i hi => ?_)
    (fun κ _ _ e hde => ?_)
  · exact (Crel.fibre κ).subsingleton_Hgr_of_le_of_field (Crel.isCoherent_fibre M hM κ)
      (Crel.fibre_hasInfiniteBaseChange κ) (hfib κ) (le_trans hd hde) i hi
  · exact (Crel.fibre κ).mulSpan_eq_top_of_field (Crel.isCoherent_fibre M hM κ)
      (Crel.fibre_hasInfiniteBaseChange κ) (hfib κ) hd hde

/-- API lemma for Proposition 2.3.18 (the form in which §2.4 uses it):
let `0 → K → F → Q → 0` be a short exact sequence of families of coherent sheaves on `ℙⁿ_S`
with `K` and `Q` flat over `S`, and suppose every fibre of `K` and of `F` is `m`-regular. Then
for `d ≥ m` the pushforward `π_* Q(d)` is a vector bundle whose formation commutes with base
change, and `π_* F(d) → π_* Q(d)` is surjective.

This is Step 1 of the proof of Proposition 2.4.1 in §2.4, in the graded-module model:
the fibres of `Q` are `m`-regular by **Exercise 2.3.4** , so
parts (1) and (2) apply to `Q`, and `R¹π_* K(d) = 0` by part (2) applied to `K`, which makes
`π_* F(d) → π_* Q(d)` surjective. See `StacksAndModuli/Section2.4-Projectivity/COMMENTARY.md`. -/
theorem surjective_map_and_finite_projective_of_fibres_regular {K F Q : GradedModule R n}
    {f : K ⟶ F} {g : F ⟶ Q} (hfg : ShortExact f g) (hK : Crel.IsCoherent K)
    (hQ : Crel.IsCoherent Q) (hKflat : Crel.IsFlat K) (hQflat : Crel.IsFlat Q) {m : ℤ}
    (hKreg : ∀ (κ : Type u) [Field κ] [Algebra R κ],
      (Crel.fibre κ).IsMRegular (K.baseChange κ) m)
    (hFreg : ∀ (κ : Type u) [Field κ] [Algebra R κ],
      (Crel.fibre κ).IsMRegular (F.baseChange κ) m)
    {d : ℤ} (hd : m ≤ d) :
    (Module.Finite R ((Crel.Hgr Q 0).obj d) ∧ Module.Projective R ((Crel.Hgr Q 0).obj d) ∧
        Crel.CommutesWithBaseChange Q d) ∧
      Function.Surjective ((Crel.map g 0).app d).hom := by
  have hQreg : ∀ (κ : Type u) [Field κ] [Algebra R κ],
      (Crel.fibre κ).IsMRegular (Q.baseChange κ) m := by
    intro κ _ _
    refine (Crel.fibre κ).isMRegular_of_shortExact (Crel.shortExact_fibre hfg hQflat κ) ?_
      (hFreg κ)
    exact (Crel.fibre κ).isMRegular_of_le_of_field (Crel.isCoherent_fibre K hK κ)
      (Crel.fibre_hasInfiniteBaseChange κ) (hKreg κ) (by omega)
  refine ⟨finite_projective_Hgr_zero_of_fibres Crel Q hQ hQflat hQreg hd, ?_⟩
  exact Crel.surjective_map_of_subsingleton hfg 0 d
    (subsingleton_Hgr_of_fibres Crel K hK hKflat hKreg hd 1 le_rfl)

end AlgebraicGeometry.ProjectiveSpace

end PropRegularityInFamilies
