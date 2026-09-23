module

public import StacksAndModuli.API.ProjectiveGradedTotalKernel
public import StacksAndModuli.API.ProjectiveGradedFlat
public import StacksProject.MoreOnAlgebra.FlatnessAndFinitenessConditions.«lemma-flat-graded-finite-type-finite-presentation-module»

/-!
# Finiteness and flatness of total graded modules

This file compares StacksAndModuli's diagrammatic finiteness and flatness conditions for a graded
module with the corresponding conditions on its total module over the polynomial ring.

The total module of a degreewise flat graded module is flat over the coefficient ring.  In the
other direction, finite generation over the polynomial ring forces every diagrammatic degree
piece to be finite over the coefficient ring.  The latter uses the internal grading of
`GradedModule.Total` and the degreewise finiteness theorem developed for Stacks Project tag
053C.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {n : ℕ}

namespace Total

/-- The total module of a degreewise flat graded module is flat over the coefficient ring. -/
theorem flat_of_isFlat {M : GradedModule R n} (hM : IsFlat M) :
    Module.Flat R (Total M) := by
  letI : ∀ d : ℤ, Module.Flat R (M.obj d) := hM
  exact Module.Flat.dfinsupp_iff.mpr hM

/-- A fixed degree of a polynomial-finite total module is finite over the coefficient ring. -/
theorem finite_obj_of_finite_total (M : GradedModule R n)
    (hM : Module.Finite (MvPolynomial (Fin (n + 1)) R) (Total M)) (d : ℤ) :
    Module.Finite R (M.obj d) := by
  letI : Module.Finite (MvPolynomial (Fin (n + 1)) R) (Total M) := hM
  have hsol : ∀ (e d : ℤ), Set.Finite {a : ℕ | a +ᵥ e = d} := by
    intro e d
    refine Set.Finite.subset (Set.finite_singleton (d - e).toNat) ?_
    intro a ha
    simp only [Set.mem_ofPred_eq, nat_vadd_int] at ha
    have hade : (a : ℤ) = d - e := by omega
    rw [Set.mem_singleton_iff]
    have := congrArg Int.toNat hade
    simpa using this
  letI : Module.Finite R (degreePiece M d) :=
    Module.Finite.finite_decomposition_component
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (degreePiece M) (fun _ => inferInstance) hsol d
  exact Module.Finite.equiv (pieceLinearEquiv M d).symm

/-- A polynomial multiple of a pure element has no component below the element's degree. -/
lemma tcomp_smul_tof_eq_zero_of_lt (M : GradedModule R n)
    (p : MvPolynomial (Fin (n + 1)) R) {e d : ℤ} (hde : d < e) (x : M.obj e) :
    tcomp M d (p • tof M e x) = 0 := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum p]
  rw [Finset.sum_smul, map_sum]
  apply Finset.sum_eq_zero
  intro b hb
  rw [monomial_smul_tof M b (coeff b p)
    (rfl : e + (b.degree : ℤ) = e + (b.degree : ℤ)) x, map_smul,
    tcomp_tof_ne M (by omega), smul_zero]

/-- A positive-degree monomial ending in degree `d + 1` factors through multiplication by one
variable from degree `d`. -/
lemma mulMono_mem_mulSpan_succ (M : GradedModule R n)
    (b : Fin (n + 1) →₀ ℕ) {e d : ℤ} (hed : e ≤ d)
    (hdeg : e + (b.degree : ℤ) = d + 1) (x : M.obj e) :
    (M.mulMono b e (d + 1) hdeg).hom x ∈ M.mulSpan d (d + 1) := by
  classical
  have hbpos : 1 ≤ b.degree := by omega
  obtain ⟨i, hi⟩ := exists_pos_of_degree_pos hbpos
  let b' : Fin (n + 1) →₀ ℕ := b - Finsupp.single i 1
  have hle : (Finsupp.single i 1 : Fin (n + 1) →₀ ℕ) ≤ b :=
    Finsupp.single_le_iff.mpr hi
  have hsum : b' + Finsupp.single i 1 = b := by
    exact tsub_add_cancel_of_le hle
  have hb'deg : b'.degree + 1 = b.degree := by
    have h := congrArg Finsupp.degree hsum
    simpa only [map_add, Finsupp.degree_single] using h
  have hfirst : e + (b'.degree : ℤ) = d := by
    omega
  have hsplit := M.mulMono_add' b b' (Finsupp.single i 1) hsum.symm
    e d (d + 1) hfirst (by simp) hdeg
  have happ :
      (M.mulMono b e (d + 1) hdeg).hom x =
        (M.mulX' i d (d + 1) rfl).hom ((M.mulMono b' e d hfirst).hom x) := by
    have := congrArg (fun g : M.obj e ⟶ M.obj (d + 1) => g.hom x) hsplit
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply,
      mulMono_single] using this
  rw [happ]
  exact range_mulX'_le_mulSpan M i d (d + 1) rfl (LinearMap.mem_range_self _ _)

/-- Once a pure generator lies in degree at most `d`, the degree-`d+1` component of every
polynomial multiple belongs to the multiplication span from degree `d`. -/
lemma tcomp_smul_tof_mem_mulSpan_succ (M : GradedModule R n)
    (p : MvPolynomial (Fin (n + 1)) R) {e d : ℤ} (hed : e ≤ d) (x : M.obj e) :
    tcomp M (d + 1) (p • tof M e x) ∈ M.mulSpan d (d + 1) := by
  classical
  conv_rhs => rw [MvPolynomial.as_sum p]
  rw [Finset.sum_smul, map_sum]
  apply Submodule.sum_mem
  intro b hb
  by_cases hdeg : e + (b.degree : ℤ) = d + 1
  · rw [monomial_smul_tof M b (coeff b p) hdeg x, map_smul, tcomp_tof]
    exact Submodule.smul_mem _ _ (mulMono_mem_mulSpan_succ M b hed hdeg x)
  · rw [monomial_smul_tof M b (coeff b p)
      (rfl : e + (b.degree : ℤ) = e + (b.degree : ℤ)) x,
      map_smul, tcomp_tof_ne M hdeg, smul_zero]
    exact Submodule.zero_mem _

/-- Finite generation of the total polynomial module implies finite generation in the
diagrammatic graded-module sense. -/
theorem isFG_of_finite_total (M : GradedModule R n)
    (hM : Module.Finite (MvPolynomial (Fin (n + 1)) R) (Total M)) : IsFG M := by
  classical
  letI : Module.Finite (MvPolynomial (Fin (n + 1)) R) (Total M) := hM
  obtain ⟨t, htHom, htSpan⟩ :=
    Module.Finite.exists_finset_isHomogeneousElem_span_eq_top
      (S := MvPolynomial (Fin (n + 1)) R) (degreePiece M)
  let s : Set (Total M) := t
  have hsSpan : Submodule.span (MvPolynomial (Fin (n + 1)) R) s = ⊤ := by
    simpa only [s] using htSpan
  let deg : s → ℤ := fun x =>
    (htHom x.1 (by simpa only [s, Finset.mem_coe] using x.2)).choose
  have hdeg_mem (x : s) : x.1 ∈ degreePiece M (deg x) :=
    (htHom x.1 (by simpa only [s, Finset.mem_coe] using x.2)).choose_spec
  have htof (x : s) : ∃ y : M.obj (deg x), tof M (deg x) y = x.1 := by
    simpa only [degreePiece, LinearMap.mem_range] using hdeg_mem x
  let B : ℤ := ∑ x : s, |deg x|
  have habs_le (x : s) : |deg x| ≤ B := by
    dsimp only [B]
    exact Finset.single_le_sum (fun y _ => abs_nonneg (deg y)) (Finset.mem_univ x)
  have hdeg_le (x : s) : deg x ≤ B := (le_abs_self (deg x)).trans (habs_le x)
  have hneg_le_deg (x : s) : -B ≤ deg x :=
    (neg_le_neg (habs_le x)).trans (neg_abs_le (deg x))
  have hrep : ∀ (d : ℤ) (z : M.obj d),
      ∃ l : s →₀ MvPolynomial (Fin (n + 1)) R,
        l.sum (fun x p => p • x.1) = tof M d z := by
    intro d z
    have hzmem : tof M d z ∈
        Submodule.span (MvPolynomial (Fin (n + 1)) R) s := by
      rw [hsSpan]
      trivial
    obtain ⟨l, hl⟩ :=
      (Finsupp.mem_span_iff_linearCombination
        (MvPolynomial (Fin (n + 1)) R) s (tof M d z)).mp hzmem
    exact ⟨l, by simpa only [Finsupp.linearCombination_apply] using hl⟩
  refine ⟨fun d => finite_obj_of_finite_total M hM d, ⟨-B, fun d hd => ?_⟩,
    ⟨B, fun d hd => ?_⟩⟩
  · constructor
    intro x y
    have hzero : ∀ z : M.obj d, z = 0 := by
      intro z
      obtain ⟨l, hl⟩ := hrep d z
      have hzsum : l.sum (fun q p => tcomp M d (p • q.1)) = z := by
        have h := congrArg (tcomp M d) hl
        simpa only [map_finsuppSum, tcomp_tof] using h
      have hsumzero : l.sum (fun q p => tcomp M d (p • q.1)) = 0 := by
        rw [Finsupp.sum]
        apply Finset.sum_eq_zero
        intro q hq
        obtain ⟨zq, hzq⟩ := htof q
        rw [← hzq]
        exact tcomp_smul_tof_eq_zero_of_lt M (l q)
          (lt_of_lt_of_le hd (hneg_le_deg q)) zq
      exact hzsum.symm.trans hsumzero
    exact (hzero x).trans (hzero y).symm
  · apply eq_top_iff.mpr
    intro z hz
    obtain ⟨l, hl⟩ := hrep (d + 1) z
    have hzsum : l.sum (fun q p => tcomp M (d + 1) (p • q.1)) = z := by
      have h := congrArg (tcomp M (d + 1)) hl
      simpa only [map_finsuppSum, tcomp_tof] using h
    rw [← hzsum, Finsupp.sum]
    apply Submodule.sum_mem
    intro q hq
    obtain ⟨zq, hzq⟩ := htof q
    rw [← hzq]
    exact tcomp_smul_tof_mem_mulSpan_succ M (l q) ((hdeg_le q).trans hd) zq

end Total

/-- Degreewise flatness makes the total graded module flat over the coefficient ring. -/
theorem IsFlat.flat_total {M : GradedModule R n} (hM : IsFlat M) :
    Module.Flat R (Total M) := Total.flat_of_isFlat hM

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end
