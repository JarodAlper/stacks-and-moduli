module

public import Mathlib.LinearAlgebra.Lagrange
public import StacksAndModuli.API.ProjectiveGradedSnapper
public import StacksAndModuli.API.ProjectiveReconstructedGotzmannPersistence

/-!
# Hilbert-function persistence from Castelnuovo--Mumford regularity

This file isolates the part of the Hilbert--Quot construction that follows from
the regularity theory of Section 2.3 and does not use Macaulay's growth theorem.

For a coherent graded model that is `m`-regular, every higher cohomology group
vanishes in degrees at least `m`.  Hence its Hilbert function is exactly its
Euler-characteristic polynomial in every such degree.  A polynomial of degree
at most `n` is then determined by its values in any `n+1` consecutive degrees.

The structure `Scheme.Modules.FieldRegularityModel` is the precise comparison
datum needed to transfer this statement to the scheme-theoretic Hilbert
function.  Snapper's theorem constructs the fibre's a priori unknown polynomial
from that datum.  The two adjacent values used in a one-step Grassmannian
construction determine it only in projective dimension at most one.  In higher
dimension, the missing implication from two values to all later values is
exactly the Macaulay--Gotzmann input, not a consequence of bounded regularity
alone.

Main declarations:

* `Polynomial.eq_of_natDegree_le_of_eval_nat_add_eq`;
* `Polynomial.exists_ne_of_natDegree_le_of_two_eval_eq`;
* `ProjectiveSpace.Cohomology.exists_hasHilbertPolynomial_natDegree_le`;
* `ProjectiveSpace.Cohomology.chi_eq_h_zero_of_isMRegular`;
* `Scheme.Modules.FieldRegularityModel.hilbertFunctionOver_eq`;
* `Scheme.Modules.FieldRegularityModel.polynomial_eq_of_window`;
* `Scheme.Modules.FieldRegularityModel.hilbertFunctionOver_eq_of_window`;
* `Scheme.Modules.ProjectiveOneStepFieldGrowthEpi.`
  `of_regular_models_of_dimension_le_one`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Polynomial

/-- The discrete antiderivative in Snapper's theorem may be chosen with the
expected degree bound: integrating a polynomial of degree at most `d` raises
the degree by at most one. -/
theorem exists_sub_comp_X_sub_one_eq_natDegree_le (P : Polynomial ℚ) :
    ∃ Q : Polynomial ℚ,
      Q - Q.comp (X - 1) = P ∧ Q.natDegree ≤ P.natDegree + 1 := by
  generalize hd : P.natDegree = d
  induction d using Nat.strong_induction_on generalizing P with
  | _ d ih =>
    rcases eq_or_ne P 0 with rfl | hP0
    · exact ⟨0, by simp⟩
    set a : ℚ := P.leadingCoeff with ha
    have ha0 : a ≠ 0 := leadingCoeff_ne_zero.mpr hP0
    set B : Polynomial ℚ :=
      (a * (d.factorial : ℚ)) • binomialPoly (d + 1) with hB
    have hBdiff : B - B.comp (X - 1) =
        (a * (d.factorial : ℚ)) • (binomialPoly d).comp (X - 1) := by
      rw [hB, smul_comp, ← smul_sub, binomialPoly_sub_comp_X_sub_one]
    have hbdeg : (binomialPoly d).degree = (d : ℕ) :=
      binomialPolySequence.degree_eq d
    have hbne : binomialPoly d ≠ 0 := fun h => by
      rw [h, degree_zero] at hbdeg
      exact absurd hbdeg (by simp)
    have hcompdeg : ((binomialPoly d).comp (X - 1)).natDegree = d := by
      rw [show (X - 1 : Polynomial ℚ) = X + C (-1) by
        simp [sub_eq_add_neg], natDegree_comp, natDegree_X_add_C, mul_one,
        natDegree_eq_of_degree_eq_some hbdeg]
    have hcomplead : ((binomialPoly d).comp (X - 1)).leadingCoeff =
        (binomialPoly d).leadingCoeff := by
      rw [show (X - 1 : Polynomial ℚ) = X + C (-1) by
        simp [sub_eq_add_neg]]
      rw [leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero)]
      rw [show (X + C (-1) : Polynomial ℚ).leadingCoeff = 1 from by
        rw [leadingCoeff_X_add_C]]
      rw [one_pow, mul_one]
    have hblead : (binomialPoly d).leadingCoeff =
        ((d.factorial : ℚ))⁻¹ := by
      rw [binomialPoly, smul_eq_C_mul, leadingCoeff_mul, leadingCoeff_C,
        (monic_descPochhammer ℚ d).leadingCoeff, mul_one]
    have hfac0 : (d.factorial : ℚ) ≠ 0 := by positivity
    have hdifflead : (B - B.comp (X - 1)).leadingCoeff = a := by
      rw [hBdiff, smul_eq_C_mul, leadingCoeff_mul, leadingCoeff_C,
        hcomplead, hblead]
      field_simp
    have hdiffdeg : (B - B.comp (X - 1)).natDegree = d := by
      rw [hBdiff, smul_eq_C_mul]
      rw [natDegree_C_mul (mul_ne_zero ha0 hfac0), hcompdeg]
    have hdiffne : B - B.comp (X - 1) ≠ 0 := fun h => by
      rw [h, leadingCoeff_zero] at hdifflead
      exact ha0 hdifflead.symm
    have hBdeg : B.natDegree ≤ d + 1 := by
      rw [hB]
      exact (natDegree_smul_le _ _).trans
        (le_of_eq (natDegree_eq_of_degree_eq_some
          (binomialPolySequence.degree_eq (d + 1))))
    rcases eq_or_ne (P - (B - B.comp (X - 1))) 0 with hrem0 | hrem0
    · refine ⟨B, (sub_eq_zero.mp hrem0).symm, ?_⟩
      exact hBdeg
    · have hremdeg : (P - (B - B.comp (X - 1))).degree < P.degree := by
        refine degree_sub_lt_left ?_ hP0 ?_
        · rw [degree_eq_natDegree hP0, degree_eq_natDegree hdiffne,
            hdiffdeg, hd]
        · rw [hdifflead]
      have hremnat : (P - (B - B.comp (X - 1))).natDegree < d := by
        rw [← hd]
        exact natDegree_lt_natDegree hrem0 hremdeg
      obtain ⟨Q₂, hQ₂, hQ₂deg⟩ := ih _ hremnat _ rfl
      refine ⟨B + Q₂, ?_, ?_⟩
      · rw [add_comp, sub_add_eq_sub_sub]
        rw [show B + Q₂ - B.comp (X - 1) - Q₂.comp (X - 1) =
          (B - B.comp (X - 1)) + (Q₂ - Q₂.comp (X - 1)) by ring,
          hQ₂]
        ring
      · apply natDegree_add_le_of_degree_le hBdeg
        exact hQ₂deg.trans (by omega)

/-- Two rational polynomials of degree at most `n` that agree in the `n+1`
consecutive natural-number arguments `d, ..., d+n` are equal. -/
theorem eq_of_natDegree_le_of_eval_nat_add_eq
    {P Q : Polynomial ℚ} {n d : ℕ}
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n)
    (h : ∀ i : ℕ, i ≤ n →
      P.eval ((d + i : ℕ) : ℚ) = Q.eval ((d + i : ℕ) : ℚ)) :
    P = Q := by
  classical
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
      (s := Finset.range (n + 1))
      (v := fun i : ℕ ↦ ((d + i : ℕ) : ℚ))
  · intro i hi j hj hij
    change ((d + i : ℕ) : ℚ) = ((d + j : ℕ) : ℚ) at hij
    have hnat : d + i = d + j := by exact_mod_cast hij
    omega
  · by_cases hP0 : P = 0
    · simp [hP0]
    · rw [Polynomial.degree_eq_natDegree hP0, Finset.card_range]
      exact_mod_cast Nat.lt_succ_of_le hP
  · by_cases hQ0 : Q = 0
    · simp [hQ0]
    · rw [Polynomial.degree_eq_natDegree hQ0, Finset.card_range]
      exact_mod_cast Nat.lt_succ_of_le hQ
  · intro i hi
    exact h i (by simpa using (Finset.mem_range.mp hi))

/-- In degree at least two, two consecutive values do not determine a
polynomial, even after imposing the geometric degree bound. -/
theorem exists_ne_of_natDegree_le_of_two_eval_eq
    {P : Polynomial ℚ} {n d : ℕ} (hP : P.natDegree ≤ n) (hn : 2 ≤ n) :
    ∃ Q : Polynomial ℚ,
      Q ≠ P ∧ Q.natDegree ≤ n ∧
        Q.eval (d : ℚ) = P.eval (d : ℚ) ∧
        Q.eval ((d + 1 : ℕ) : ℚ) = P.eval ((d + 1 : ℕ) : ℚ) := by
  let R : Polynomial ℚ :=
    (X - C (d : ℚ)) * (X - C ((d + 1 : ℕ) : ℚ))
  have hR : R ≠ 0 := by
    dsimp [R]
    exact mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)
  refine ⟨P + R, ?_, ?_, ?_, ?_⟩
  · intro hEq
    apply hR
    have := congrArg (fun Z : Polynomial ℚ ↦ Z - P) hEq
    simpa using this
  · apply natDegree_add_le_of_degree_le hP
    dsimp [R]
    rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
      natDegree_X_sub_C, natDegree_X_sub_C]
    omega
  · simp [R]
  · simp [R]

end Polynomial

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

open GradedModule

variable {k : Type u} [Field k] {C : Cohomology k}

/-- Snapper's theorem with the geometric degree bound: a coherent sheaf on
`ℙⁿ` has an Euler-characteristic polynomial of degree at most `n`. -/
theorem exists_hasHilbertPolynomial_natDegree_le_of_infinite :
    ∀ (n : ℕ) (K : Type u) [Field K], Infinite K → ∀ (C : Cohomology K)
      (M : GradedModule K n), C.IsCoherent M →
    ∃ P : Polynomial ℚ, C.HasHilbertPolynomial M P ∧ P.natDegree ≤ n := by
  intro n
  induction n with
  | zero =>
      intro K _ _ C M _
      refine ⟨Polynomial.C ((C.chi M 0 : ℚ)), fun d ↦ ?_, by simp⟩
      rw [Polynomial.eval_C]
      exact_mod_cast congrArg (fun z : ℤ ↦ (z : ℚ)) (chi_zero_eq C M d 0)
  | succ n ih =>
      intro K instK hK C M hM
      obtain ⟨N, φ, hNcoh, hNtf, _, _, hbij⟩ :=
        C.exists_noIrrelevantTorsion_quotient hM
      suffices h : ∃ P, C.HasHilbertPolynomial N P ∧ P.natDegree ≤ n + 1 by
        obtain ⟨P, hP, hPdeg⟩ := h
        exact ⟨P, (C.hasHilbertPolynomial_congr φ hbij P).mpr hP, hPdeg⟩
      obtain ⟨c, j, hj, hLN, -⟩ :=
        C.exists_nonZeroDivisor_linearForm hK N N hNcoh hNcoh hNtf hNtf
      have hrescoh : C.IsCoherent (N.restrictL c j) :=
        C.isCoherent_restrictL hNcoh c j hj
      obtain ⟨P₀, hP₀, hP₀deg⟩ := ih K hK C (N.restrictL c j) hrescoh
      have hdiff : ∀ d : ℤ,
          (C.chi N d : ℚ) - (C.chi N (d + -1) : ℚ) = P₀.eval (d : ℚ) := by
        intro d
        have h1 := C.chi_quotL hNcoh c hLN d
        have h2 := C.chi_restrictL N c j hj hrescoh d
        have h3 := hP₀ d
        rw [h2.trans h1] at h3
        push_cast at h3 ⊢
        linarith
      obtain ⟨Q, hQ, hQdeg⟩ :=
        Polynomial.exists_sub_comp_X_sub_one_eq_natDegree_le P₀
      have hQdiff : ∀ x : ℚ, Q.eval x - Q.eval (x - 1) = P₀.eval x := by
        intro x
        have := congrArg (Polynomial.eval x) hQ
        rwa [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_one] at this
      set g : ℤ → ℚ := fun d ↦ (C.chi N d : ℚ) - Q.eval (d : ℚ) with hg
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
            rw [hgstep ((i : ℤ) + 1),
              show ((i : ℤ) + 1 : ℤ) - 1 = (i : ℤ) by ring, ihp]
        | pred i ihn => rw [← ihn, ← hgstep (-(i : ℤ))]
      refine ⟨Q + Polynomial.C (g 0), fun d ↦ ?_, ?_⟩
      · rw [Polynomial.eval_add, Polynomial.eval_C, ← hgconst d, hg]
        simp only []
        ring
      · apply Polynomial.natDegree_add_le_of_degree_le
        · exact hQdeg.trans (by omega)
        · simp

/-- Snapper's theorem with its dimension bound over an arbitrary field. -/
theorem exists_hasHilbertPolynomial_natDegree_le
    {n : ℕ} (C : Cohomology k) (hC : C.HasInfiniteBaseChange)
    (M : GradedModule k n) (hM : C.IsCoherent M) :
    ∃ P : Polynomial ℚ, C.HasHilbertPolynomial M P ∧ P.natDegree ≤ n := by
  obtain ⟨K', instK', C', hinf, hbc⟩ := hC
  obtain ⟨bc⟩ := hbc
  obtain ⟨P, hP, hPdeg⟩ :=
    exists_hasHilbertPolynomial_natDegree_le_of_infinite n K' hinf C'
      (bc.obj M) (bc.isCoherent M hM)
  exact ⟨P, (bc.hasHilbertPolynomial_iff M P).mp hP, hPdeg⟩

/-- Above a Castelnuovo--Mumford regularity bound, the Euler characteristic is
the dimension of `H⁰`: all positive cohomology groups vanish. -/
theorem chi_eq_h_zero_of_isMRegular
    {n : ℕ} {M : GradedModule k n} (hM : C.IsCoherent M)
    (hC : C.HasInfiniteBaseChange) {m e : ℤ}
    (hreg : C.IsMRegular M m) (hme : m ≤ e) :
    C.chi M e = (C.h M 0 e : ℤ) := by
  rw [chi]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro i hi hi0
    rw [C.h_eq_zero_of_subsingleton
      (C.subsingleton_Hgr_of_le_of_field hM hC hreg hme i (by omega))]
    ring
  · intro h0
    exact absurd (Finset.mem_range.mpr (by omega)) h0

/-- Above a regularity bound, the zeroth-cohomology dimension equals the value
of any polynomial representing the Euler characteristic. -/
theorem h_zero_eq_eval_of_isMRegular
    {n : ℕ} {M : GradedModule k n} (hM : C.IsCoherent M)
    (hC : C.HasInfiniteBaseChange) {P : Polynomial ℚ} {m e : ℤ}
    (hreg : C.IsMRegular M m) (hme : m ≤ e)
    (hP : C.HasHilbertPolynomial M P) :
    (C.h M 0 e : ℚ) = P.eval (e : ℚ) := by
  rw [← hP e]
  exact_mod_cast (C.chi_eq_h_zero_of_isMRegular hM hC hreg hme).symm

end AlgebraicGeometry.ProjectiveSpace.Cohomology

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A field-valued projective sheaf together with the regular graded model
needed to compute its Hilbert function from a fixed degree onward.

The associated Euler-characteristic polynomial is constructed below from the
bounded form of Snapper's theorem; it is not part of the comparison data. -/
structure FieldRegularityModel
    (n : ℕ) (k : Type u) [Field k]
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of k))).Modules) (d : ℕ) where
  /-- Cohomology theory for the graded model. -/
  C : ProjectiveSpace.Cohomology k
  /-- A graded module presenting the projective sheaf. -/
  M : ProjectiveSpace.GradedModule k n
  /-- Coherence of the graded model. -/
  coherent : C.IsCoherent M
  /-- The field-independent form of the regularity theorems. -/
  infiniteBaseChange : C.HasInfiniteBaseChange
  /-- Regularity from the comparison degree onward. -/
  regular : C.IsMRegular M (d : ℤ)
  /-- In the regular range, graded `H⁰` computes actual global sections. -/
  globalSectionsIso : ∀ t : ℕ, d ≤ t →
    letI := globalSectionsModule
      (Scheme.projectiveSpaceOverπ n (Spec (.of k)))
      (Scheme.projectiveSpaceOverTwistModule Q (t : ℤ))
    ((C.Hgr M 0).obj (t : ℤ)) ≃ₗ[k]
      projectiveSpaceTwistedGlobalSections Q (t : ℤ)

/-- The same regularity model interface for a bundled commutative ring known
to be a field.  The chosen field structure is the canonical one supplied by
`IsField.toField`, so its ring operations agree with the bundled object. -/
abbrev FieldRegularityModelOfIsField
    (n : ℕ) (K : CommRingCat.{u}) (hK : IsField K)
    (Q : (Scheme.projectiveSpaceOver n (Spec K)).Modules) (d : ℕ) : Type (u + 1) := by
  letI : Field K := hK.toField
  exact FieldRegularityModel n K Q d

namespace FieldRegularityModel

variable {n d : ℕ} {k : Type u} [Field k]
  {Q : (Scheme.projectiveSpaceOver n (Spec (.of k))).Modules}

/-- The a priori Hilbert polynomial supplied by bounded Snapper for a regular
graded comparison model. -/
noncomputable def polynomial (D : FieldRegularityModel n k Q d) : Polynomial ℚ :=
  Classical.choose
    (D.C.exists_hasHilbertPolynomial_natDegree_le D.infiniteBaseChange D.M D.coherent)

/-- The polynomial chosen for a regular comparison model represents its Euler
characteristic in every integer degree. -/
theorem hasHilbertPolynomial (D : FieldRegularityModel n k Q d) :
    D.C.HasHilbertPolynomial D.M D.polynomial :=
  (Classical.choose_spec
    (D.C.exists_hasHilbertPolynomial_natDegree_le D.infiniteBaseChange
      D.M D.coherent)).1

/-- The polynomial chosen for a model on `ℙⁿ` has degree at most `n`. -/
theorem polynomial_natDegree_le (D : FieldRegularityModel n k Q d) :
    D.polynomial.natDegree ≤ n :=
  (Classical.choose_spec
    (D.C.exists_hasHilbertPolynomial_natDegree_le D.infiniteBaseChange
      D.M D.coherent)).2

/-- A regular graded comparison computes the scheme-theoretic Hilbert function
by its a priori polynomial in every degree at least `d`. -/
theorem hilbertFunctionOver_eq
    (D : FieldRegularityModel n k Q d) (t : ℕ) (hdt : d ≤ t) :
    (Scheme.hilbertFunctionOver Q (t : ℤ) : ℚ) =
      D.polynomial.eval (t : ℚ) := by
  letI := globalSectionsModule
    (Scheme.projectiveSpaceOverπ n (Spec (.of k)))
    (Scheme.projectiveSpaceOverTwistModule Q (t : ℤ))
  have hfin := (D.globalSectionsIso t hdt).finrank_eq
  change (Module.finrank k
    (projectiveSpaceTwistedGlobalSections Q (t : ℤ)) : ℚ) = _
  rw [← hfin]
  exact D.C.h_zero_eq_eval_of_isMRegular D.coherent D.infiniteBaseChange
    D.regular (by exact_mod_cast hdt) D.hasHilbertPolynomial

/-- Values in `n+1` consecutive regular degrees identify the prescribed
polynomial with the fibre's a priori Hilbert polynomial. -/
theorem polynomial_eq_of_window
    (D : FieldRegularityModel n k Q d) (P : Polynomial ℚ)
    (hPdeg : P.natDegree ≤ n)
    (hvalues : ∀ i : ℕ, i ≤ n →
      (Scheme.hilbertFunctionOver Q ((d + i : ℕ) : ℤ) : ℚ) =
        P.eval ((d + i : ℕ) : ℚ)) :
    D.polynomial = P := by
  apply Polynomial.eq_of_natDegree_le_of_eval_nat_add_eq
    D.polynomial_natDegree_le hPdeg
  intro i hi
  rw [← hvalues i hi]
  exact (D.hilbertFunctionOver_eq (d + i) (Nat.le_add_right d i)).symm

/-- A regular model and equality with `P` in `n+1` consecutive degrees imply
exact Hilbert-function persistence in every later degree. -/
theorem hilbertFunctionOver_eq_of_window
    (D : FieldRegularityModel n k Q d) (P : Polynomial ℚ)
    (hPdeg : P.natDegree ≤ n)
    (hvalues : ∀ i : ℕ, i ≤ n →
      (Scheme.hilbertFunctionOver Q ((d + i : ℕ) : ℤ) : ℚ) =
        P.eval ((d + i : ℕ) : ℚ))
    (t : ℕ) (hdt : d ≤ t) :
    (Scheme.hilbertFunctionOver Q (t : ℤ) : ℚ) = P.eval (t : ℚ) := by
  rw [D.hilbertFunctionOver_eq t hdt, D.polynomial_eq_of_window P hPdeg hvalues]

end FieldRegularityModel

namespace FieldRegularityModelOfIsField

variable {n d : ℕ} {K : CommRingCat.{u}} {hK : IsField K}
  {Q : (Scheme.projectiveSpaceOver n (Spec K)).Modules}

/-- Equality in `n+1` consecutive degrees gives exact persistence for a
bundled-field regularity model. -/
theorem hilbertFunctionOver_eq_of_window
    (D : FieldRegularityModelOfIsField n K hK Q d)
    (P : Polynomial ℚ) (hPdeg : P.natDegree ≤ n)
    (hvalues : ∀ i : ℕ, i ≤ n →
      (Scheme.hilbertFunctionOver Q ((d + i : ℕ) : ℤ) : ℚ) =
        P.eval ((d + i : ℕ) : ℚ))
    (t : ℕ) (hdt : d ≤ t) :
    (Scheme.hilbertFunctionOver Q (t : ℤ) : ℚ) = P.eval (t : ℚ) := by
  letI : Field K := hK.toField
  exact FieldRegularityModel.hilbertFunctionOver_eq_of_window
    D P hPdeg hvalues t hdt

end FieldRegularityModelOfIsField

variable {T : Scheme.{u}} {n : ℕ}
  {Q : (Scheme.projectiveSpaceOver n T).Modules} [Q.IsQuasicoherent]
  {P : Polynomial ℚ} {d : ℕ}

omit [Q.IsQuasicoherent] in
/-- In projective dimension at most one, the two adjacent rank conditions do
determine the full Hilbert polynomial once they are connected to the fibre by
base change and the one-step hypotheses produce a regular graded model.

For `n ≥ 2`, the same argument needs `n+1` values; replacing those extra values
by the two-value hypothesis is precisely the Macaulay--Gotzmann theorem. -/
theorem ProjectiveOneStepFieldGrowthEpi.of_regular_models_of_dimension_le_one
    (hn : n ≤ 1) (hPdeg : P.natDegree ≤ n)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (hdegree : ∀ (K : CommRingCat.{u}) (_hK : IsField K)
      (s : Spec K ⟶ T),
      (pullback s).obj (projectiveTwistedPushforward n Q d) ≅
        projectiveTwistedPushforward n
          ((pullback (Scheme.projectiveSpaceOverMap n s)).obj Q) d)
    (hdegreeSucc : ∀ (K : CommRingCat.{u}) (_hK : IsField K)
      (s : Spec K ⟶ T),
      (pullback s).obj (projectiveTwistedPushforward n Q (d + 1)) ≅
        projectiveTwistedPushforward n
          ((pullback (Scheme.projectiveSpaceOverMap n s)).obj Q) (d + 1))
    (hmodel : ∀ (K : CommRingCat.{u}) (hK : IsField K)
      (s : Spec K ⟶ T),
      IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
          ((pullback s).obj (projectiveTwistedPushforward n Q d)) →
      IsProjectiveOfRank ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
          ((pullback s).obj (projectiveTwistedPushforward n Q (d + 1))) →
      Epi ((pullback s).map (projectiveTwistedPushforwardMul n Q d)) →
      FieldRegularityModelOfIsField n K hK
        ((pullback (Scheme.projectiveSpaceOverMap n s)).obj Q) d) :
    ProjectiveOneStepFieldGrowthEpi n Q P d := by
  intro K hK s h₀ h₁ hmul t hdt
  let Qs := (pullback (Scheme.projectiveSpaceOverMap n s)).obj Q
  let D : FieldRegularityModelOfIsField n K hK Qs d :=
    hmodel K hK s h₀ h₁ hmul
  apply D.hilbertFunctionOver_eq_of_window P hPdeg
  · intro i hi
    rcases (show i = 0 ∨ i = 1 by omega) with rfl | rfl
    · have hactual : IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
          (projectiveTwistedPushforward n Qs d) :=
        h₀.of_iso (hdegree K hK s)
      have hvalue :=
        hilbertFunctionOver_eq_of_projectiveTwistedPushforward_isProjectiveOfRank
          n K hK Qs (d : ℤ) ((P.eval (d : ℚ)).num.natAbs) hactual
      rw [Nat.add_zero]
      exact (congrArg (fun q : ℕ ↦ (q : ℚ)) hvalue).trans hPd
    · have hactual : IsProjectiveOfRank
          ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
          (projectiveTwistedPushforward n Qs (d + 1)) :=
        h₁.of_iso (hdegreeSucc K hK s)
      have hvalue :=
        hilbertFunctionOver_eq_of_projectiveTwistedPushforward_isProjectiveOfRank
          n K hK Qs ((d + 1 : ℕ) : ℤ)
            ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs) hactual
      exact (congrArg (fun q : ℕ ↦ (q : ℚ)) hvalue).trans hPsucc
  · exact hdt

end AlgebraicGeometry.Scheme.Modules

end

end
