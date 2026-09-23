module

public import StacksAndModuli.«Section2.3-Regularity».«part2.3.2-regularity-bounds»

/-!
# Snapper's theorem in the graded-module model

Every coherent sheaf on `ℙⁿ` over a field has a Hilbert polynomial: the Euler
characteristic `d ↦ χ(M~(d))` agrees with a polynomial in **every** degree.

The proof is the classical induction on `n`.  Replace `M` by its quotient by the
irrelevant torsion (`Cohomology.exists_noIrrelevantTorsion_quotient`), which changes no
cohomology; over an infinite field choose a linear form regular on the quotient
(`Cohomology.exists_nonZeroDivisor_linearForm`); then

`χ(M~(d)) - χ(M~(d-1)) = χ((M/LM)~(d))`,

and `M/LM` lives on the hyperplane `ℙⁿ⁻¹`, where the inductive hypothesis applies.  The
base case `ℙ⁰` is the constancy of `h⁰`: multiplication by the variable is injective on a
torsion-free module (left exactness of `H⁰`) and surjective (`Cohomology.mulSpan_zero`).
A discrete antiderivative (`Polynomial.exists_sub_comp_X_sub_one_eq`, from Pascal's rule
for `Polynomial.binomialPoly`) turns the first-difference identity into the polynomial
itself.  A finite base field is handled by `Cohomology.HasInfiniteBaseChange`, since the
packaged base change preserves the Euler characteristic.

Main declarations:

* `Polynomial.exists_sub_comp_X_sub_one_eq` — the difference operator
  `Q ↦ Q - Q ∘ (X - 1)` on `ℚ[X]` is surjective;
* `AlgebraicGeometry.ProjectiveSpace.Cohomology.exists_hasHilbertPolynomial_of_infinite`;
* `AlgebraicGeometry.ProjectiveSpace.Cohomology.exists_hasHilbertPolynomial` —
  **Snapper's theorem**: a coherent graded module over any field has a Hilbert polynomial.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open Polynomial

namespace Polynomial

/-- Pascal's rule, recentred: `C(z, i+1) - C(z-1, i+1) = C(z-1, i)`. -/
lemma binomialPoly_sub_comp_X_sub_one (i : ℕ) :
    binomialPoly (i + 1) - (binomialPoly (i + 1)).comp (X - 1)
      = (binomialPoly i).comp (X - 1) := by
  have h := congrArg (fun P : Polynomial ℚ => P.comp (X - 1))
    (binomialPoly_comp_X_add_one_sub_self i)
  simp only [sub_comp, comp_assoc, add_comp, X_comp, one_comp] at h
  rw [show (X - 1 + 1 : Polynomial ℚ) = X by ring, comp_X] at h
  exact h

/-- **The difference operator is surjective on `ℚ[X]`**: every polynomial `P` is the first
difference `Q - Q ∘ (X - 1)` of some polynomial `Q`. -/
theorem exists_sub_comp_X_sub_one_eq (P : Polynomial ℚ) :
    ∃ Q : Polynomial ℚ, Q - Q.comp (X - 1) = P := by
  generalize hd : P.natDegree = d
  induction d using Nat.strong_induction_on generalizing P with
  | _ d ih =>
    rcases eq_or_ne P 0 with rfl | hP0
    · exact ⟨0, by simp⟩
    -- subtract the leading term of a suitable multiple of a binomial polynomial
    set a : ℚ := P.leadingCoeff with ha
    have ha0 : a ≠ 0 := leadingCoeff_ne_zero.mpr hP0
    set B : Polynomial ℚ := (a * (d.factorial : ℚ)) • binomialPoly (d + 1) with hB
    have hBdiff : B - B.comp (X - 1)
        = (a * (d.factorial : ℚ)) • (binomialPoly d).comp (X - 1) := by
      rw [hB, smul_comp, ← smul_sub, binomialPoly_sub_comp_X_sub_one]
    -- the difference has degree `d` and leading coefficient `a`
    have hbdeg : (binomialPoly d).degree = (d : ℕ) := binomialPolySequence.degree_eq d
    have hbne : binomialPoly d ≠ 0 := fun h => by
      rw [h, degree_zero] at hbdeg
      exact absurd hbdeg (by simp)
    have hcompdeg : ((binomialPoly d).comp (X - 1)).natDegree = d := by
      rw [show (X - 1 : Polynomial ℚ) = X + C (-1) by simp [sub_eq_add_neg], natDegree_comp,
        natDegree_X_add_C, mul_one, natDegree_eq_of_degree_eq_some hbdeg]
    have hcomplead : ((binomialPoly d).comp (X - 1)).leadingCoeff
        = (binomialPoly d).leadingCoeff := by
      rw [show (X - 1 : Polynomial ℚ) = X + C (-1) by simp [sub_eq_add_neg]]
      rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero)]
      rw [show (X + C (-1) : Polynomial ℚ).leadingCoeff = 1 from
        by rw [leadingCoeff_X_add_C]]
      rw [one_pow, mul_one]
    have hblead : (binomialPoly d).leadingCoeff = ((d.factorial : ℚ))⁻¹ := by
      rw [binomialPoly, smul_eq_C_mul, leadingCoeff_mul, leadingCoeff_C,
        (monic_descPochhammer ℚ d).leadingCoeff, mul_one]
    have hfac0 : (d.factorial : ℚ) ≠ 0 := by positivity
    have hdifflead : (B - B.comp (X - 1)).leadingCoeff = a := by
      rw [hBdiff, smul_eq_C_mul, leadingCoeff_mul, leadingCoeff_C, hcomplead, hblead]
      field_simp
    have hdiffdeg : (B - B.comp (X - 1)).natDegree = d := by
      rw [hBdiff, smul_eq_C_mul]
      rw [natDegree_C_mul (by exact mul_ne_zero ha0 hfac0), hcompdeg]
    have hdiffne : B - B.comp (X - 1) ≠ 0 := fun h => by
      rw [h, leadingCoeff_zero] at hdifflead
      exact ha0 hdifflead.symm
    -- the remainder has strictly smaller degree
    rcases eq_or_ne (P - (B - B.comp (X - 1))) 0 with hrem0 | hrem0
    · exact ⟨B, (sub_eq_zero.mp hrem0).symm⟩
    · have hremdeg : (P - (B - B.comp (X - 1))).degree < P.degree := by
        refine degree_sub_lt_left ?_ hP0 ?_
        · rw [degree_eq_natDegree hP0, degree_eq_natDegree hdiffne, hdiffdeg, hd]
        · rw [hdifflead]
      have hremnat : (P - (B - B.comp (X - 1))).natDegree < d := by
        rw [← hd]
        exact natDegree_lt_natDegree hrem0 hremdeg
      obtain ⟨Q₂, hQ₂⟩ := ih _ hremnat _ rfl
      refine ⟨B + Q₂, ?_⟩
      rw [add_comp, sub_add_eq_sub_sub]
      rw [show B + Q₂ - B.comp (X - 1) - Q₂.comp (X - 1)
        = (B - B.comp (X - 1)) + (Q₂ - Q₂.comp (X - 1)) by ring, hQ₂]
      ring

end Polynomial

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

open AlgebraicGeometry.ProjectiveSpace GradedModule

variable {k : Type u} [Field k]

/-- On `ℙ⁰` every cohomological dimension is independent of the twist: multiplication by
the variable is invertible on cohomology. -/
lemma h_zero_eq (C : Cohomology k) (M : GradedModule k 0) (q : ℕ) (d e : ℤ) :
    C.h M q d = C.h M q e := by
  have hstep : ∀ f : ℤ, C.h M q f = C.h M q (f + 1) := fun f =>
    (LinearEquiv.ofBijective _ (C.zero_mulX_bijective M 0 q f)).finrank_eq
  have hzero : ∀ f : ℤ, C.h M q f = C.h M q 0 := by
    intro f
    induction f using Int.induction_on with
    | zero => rfl
    | succ i ihp => rw [← hstep (i : ℤ), ihp]
    | pred i ihn =>
        rw [hstep (-(i : ℤ) - 1), show (-(i : ℤ) - 1) + 1 = -(i : ℤ) by ring, ihn]
  rw [hzero d, hzero e]

/-- On `ℙ⁰` the Euler characteristic is independent of the twist. -/
lemma chi_zero_eq (C : Cohomology k) (M : GradedModule k 0) (d e : ℤ) :
    C.chi M d = C.chi M e :=
  Finset.sum_congr rfl fun i _ => by rw [h_zero_eq C M i d e]

/-- **Snapper's theorem over an infinite field**: every coherent graded module has a
Hilbert polynomial — the Euler characteristic `d ↦ χ(M~(d))` agrees with a polynomial in
every degree `d ∈ ℤ`. -/
theorem exists_hasHilbertPolynomial_of_infinite :
    ∀ (n : ℕ) (K : Type u) [Field K], Infinite K → ∀ (C : Cohomology K)
      (M : GradedModule K n), C.IsCoherent M →
    ∃ P : Polynomial ℚ, C.HasHilbertPolynomial M P := by
  intro n
  induction n with
  | zero =>
      intro K _ _ C M _
      refine ⟨Polynomial.C ((C.chi M 0 : ℚ)), fun d => ?_⟩
      rw [Polynomial.eval_C]
      exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) (chi_zero_eq C M d 0)
  | succ n ih =>
      intro K instK hK C M hM
      obtain ⟨N, φ, hNcoh, hNtf, _, _, hbij⟩ := C.exists_noIrrelevantTorsion_quotient hM
      suffices h : ∃ P, C.HasHilbertPolynomial N P by
        obtain ⟨P, hP⟩ := h
        exact ⟨P, (C.hasHilbertPolynomial_congr φ hbij P).mpr hP⟩
      obtain ⟨c, j, hj, hLN, -⟩ :=
        C.exists_nonZeroDivisor_linearForm hK N N hNcoh hNcoh hNtf hNtf
      have hrescoh : C.IsCoherent (N.restrictL c j) := C.isCoherent_restrictL hNcoh c j hj
      obtain ⟨P₀, hP₀⟩ := ih K hK C (N.restrictL c j) hrescoh
      have hdiff : ∀ d : ℤ, (C.chi N d : ℚ) - (C.chi N (d + -1) : ℚ) = P₀.eval (d : ℚ) := by
        intro d
        have h1 := C.chi_quotL hNcoh c hLN d
        have h2 := C.chi_restrictL N c j hj hrescoh d
        have h3 := hP₀ d
        rw [h2.trans h1] at h3
        push_cast at h3 ⊢
        linarith
      obtain ⟨Q, hQ⟩ := Polynomial.exists_sub_comp_X_sub_one_eq P₀
      have hQdiff : ∀ x : ℚ, Q.eval x - Q.eval (x - 1) = P₀.eval x := by
        intro x
        have := congrArg (Polynomial.eval x) hQ
        rwa [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_one] at this
      set g : ℤ → ℚ := fun d => (C.chi N d : ℚ) - Q.eval (d : ℚ) with hg
      have hgstep : ∀ d : ℤ, g d = g (d - 1) := by
        intro d
        have h1 := hdiff d
        have h2 := hQdiff (d : ℚ)
        rw [hg]
        simp only []
        rw [show (d - 1 : ℤ) = d + -1 by ring]
        rw [show ((d + -1 : ℤ) : ℚ) = (d : ℚ) - 1 by push_cast; ring]
        linarith
      have hgconst : ∀ d : ℤ, g d = g 0 := by
        intro d
        induction d using Int.induction_on with
        | zero => rfl
        | succ i ihp =>
            rw [hgstep ((i : ℤ) + 1), show ((i : ℤ) + 1 : ℤ) - 1 = (i : ℤ) by ring, ihp]
        | pred i ihn =>
            rw [← ihn, ← hgstep (-(i : ℤ))]
      refine ⟨Q + Polynomial.C (g 0), fun d => ?_⟩
      rw [Polynomial.eval_add, Polynomial.eval_C, ← hgconst d, hg]
      simp only []
      ring

/-- **Snapper's theorem**: over any field, every coherent graded module on `ℙⁿ` has a
Hilbert polynomial — its Euler characteristic agrees with a polynomial in every degree.
A finite base field is handled by passing to an infinite extension, which changes no
cohomological dimension. -/
theorem exists_hasHilbertPolynomial {n : ℕ} (C : Cohomology k)
    (hC : C.HasInfiniteBaseChange) (M : GradedModule k n) (hM : C.IsCoherent M) :
    ∃ P : Polynomial ℚ, C.HasHilbertPolynomial M P := by
  obtain ⟨K', instK', C', hinf, hbc⟩ := hC
  obtain ⟨bc⟩ := hbc
  obtain ⟨P, hP⟩ := exists_hasHilbertPolynomial_of_infinite n K' hinf C' (bc.obj M)
    (bc.isCoherent M hM)
  exact ⟨P, (bc.hasHilbertPolynomial_iff M P).mp hP⟩

end AlgebraicGeometry.ProjectiveSpace.Cohomology

end
