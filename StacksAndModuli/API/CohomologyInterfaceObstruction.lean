module

public import StacksAndModuli.API.ProjectiveGradedCohomology

/-!
# Why the cohomology interface needs a torsion hypothesis

Supporting API with no Stacks Project counterpart.

`AlgebraicGeometry.ProjectiveSpace.Cohomology k` packages the cohomology of quasi-coherent
sheaves on `ℙⁿ_k` that §2.3 runs on.  As first written, two of its fields contradicted each
other and the structure was **empty**, so every statement of §2.3 taking a `Cohomology k` as
a parameter was vacuous.  The two fields were

* `isCoherent_coker` — a cokernel of a map of coherent sheaves is coherent, and
* `exists_nonZeroDivisor_linearForm` — over an infinite field a coherent sheaf admits a
  linear form that is a nonzerodivisor **in every degree**.

This file keeps the witness.  Starting from `S = k[x₀, x₁]` on `ℙ¹` and quotienting twice —
first by `x₀`, then by `x₁` — the closure fields force the graded module `S/(x₀, x₁)` to be
coherent.  It is `k` in degree `0` and `0` in degree `1`, so multiplication by *any* linear
form from degree `0` to degree `1` kills a nonzero element.  Note that each step quotients by
a variable that **is** a nonzerodivisor on its source, so nothing degenerate is involved.

The interface has since been repaired: `exists_nonZeroDivisor_linearForm` now requires
`NoIrrelevantTorsion`, the vanishing of `H⁰_m`.  The theorem below records what the witness
now says — that `S/(x₀, x₁)` must fail that hypothesis in *every* cohomology theory — so the
hypothesis cannot be weakened away again.  Mathematically the point is that
`exists_nonZeroDivisor_linearForm` is a statement about **sheaves** (a general hyperplane
avoids the associated points), which pins a graded module only up to irrelevant torsion:
a finite-length module is invisible to `Hgr`, since all its localizations vanish, but is very
visible to `mulLHom`.  See `StacksAndModuli/Section2.3-Regularity/COMMENTARY.md`.

Main declarations:
- `MvPolynomial.eq_linear_of_isHomogeneous_one`;
- `GradedModule.finiteLengthQuot`, the coherent module of finite length;
- `AlgebraicGeometry.ProjectiveSpace.Cohomology.not_noIrrelevantTorsion_finiteLengthQuot`.
-/
@[expose] public section

noncomputable section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace MvPolynomial

variable {k : Type u} [CommRing k]

/-- A homogeneous polynomial of degree `1` in two variables is a linear form. -/
lemma eq_linear_of_isHomogeneous_one (p : MvPolynomial (Fin 2) k) (hp : p.IsHomogeneous 1) :
    p = C (coeff (Finsupp.single 0 1) p) * X 0 + C (coeff (Finsupp.single 1 1) p) * X 1 := by
  have hne : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) ≠ Finsupp.single 1 1 := by
    intro h
    have h0 := congrArg (fun f => f 0) h
    simp at h0
  refine MvPolynomial.ext _ _ fun b => ?_
  rw [coeff_add, ← pow_one (X (0 : Fin 2)), ← pow_one (X (1 : Fin 2)),
    C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, coeff_monomial, coeff_monomial]
  by_cases h0 : (Finsupp.single (0 : Fin 2) 1 : Fin 2 →₀ ℕ) = b
  · subst h0
    have h2 : ¬ ((Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) = Finsupp.single 0 1) :=
      fun h => hne h.symm
    simp only [↓reduceIte, h2, add_zero]
  · by_cases h1 : (Finsupp.single (1 : Fin 2) 1 : Fin 2 →₀ ℕ) = b
    · subst h1
      simp only [h0, ↓reduceIte, zero_add]
    · simp only [h0, h1, ↓reduceIte, add_zero]
      by_contra hc
      have hd := hp hc
      have hsum : ∑ i, b i = 1 := by
        rw [← hd, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => by simp)]
        exact Finset.sum_congr rfl (fun i _ => by simp)
      rw [Fin.sum_univ_two] at hsum
      rcases Nat.lt_or_ge (b 0) 1 with h | h
      · refine h1 (Finsupp.ext ?_)
        intro i
        fin_cases i <;> simp <;> omega
      · refine h0 (Finsupp.ext ?_)
        intro i
        fin_cases i <;> simp <;> omega

end MvPolynomial

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable {k : Type u} [Field k]

/-! ## Generalities on quotients -/

lemma range_eq_bot_of_subsingleton {M N : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup N] [Module k N] [Subsingleton M] (f : M →ₗ[k] N) :
    LinearMap.range f = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr ?_
  rintro x ⟨y, rfl⟩
  rw [Subsingleton.elim y 0, map_zero]

lemma nontrivial_quotient_of_bot {M : Type*} [AddCommGroup M] [Module k M]
    {p : Submodule k M} (hp : p = ⊥) [Nontrivial M] : Nontrivial (M ⧸ p) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  refine ⟨Submodule.Quotient.mk x, 0, fun h => hx ?_⟩
  rw [Submodule.Quotient.mk_eq_zero, hp, Submodule.mem_bot] at h
  exact h

lemma subsingleton_quotient_of_top {M : Type*} [AddCommGroup M] [Module k M]
    {p : Submodule k M} (hp : p = ⊤) : Subsingleton (M ⧸ p) := by
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective p x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective p y
  exact (Submodule.Quotient.eq p).mpr (by rw [hp]; trivial)

lemma subsingleton_quotient_of_subsingleton {M : Type*} [AddCommGroup M] [Module k M]
    (p : Submodule k M) [Subsingleton M] : Subsingleton (M ⧸ p) := by
  constructor
  intro x y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective p x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective p y
  rw [Subsingleton.elim a b]

/-! ## The graded pieces of `k[x₀, x₁]` in low degrees -/

lemma subsingleton_polySubmodule_neg {n : ℕ} {e : ℤ} (he : e < 0) :
    Subsingleton (polySubmodule k n e) := by
  constructor
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  rw [polySubmodule_of_neg k n he, Submodule.mem_bot] at hx hy
  exact Subtype.ext (hx.trans hy.symm)

lemma one_mem_polySubmodule_zero {n : ℕ} :
    (1 : MvPolynomial (Fin (n + 1)) k) ∈ polySubmodule k n 0 := by
  rw [polySubmodule_of_nonneg k n le_rfl, MvPolynomial.mem_homogeneousSubmodule,
    show ((0 : ℤ).toNat) = 0 from rfl]
  exact MvPolynomial.isHomogeneous_one (Fin (n + 1)) k

lemma C_mem_polySubmodule_zero {n : ℕ} (a : k) :
    (C a : MvPolynomial (Fin (n + 1)) k) ∈ polySubmodule k n 0 := by
  rw [polySubmodule_of_nonneg k n le_rfl, MvPolynomial.mem_homogeneousSubmodule,
    show ((0 : ℤ).toNat) = 0 from rfl]
  exact MvPolynomial.isHomogeneous_C (Fin (n + 1)) a

instance nontrivial_structureModule_zero : Nontrivial ((structureModule k 1).obj 0) := by
  refine ⟨⟨⟨1, one_mem_polySubmodule_zero⟩, 0, fun h => ?_⟩⟩
  exact one_ne_zero (congrArg Subtype.val h)

lemma range_mulLHom_eq_bot {n : ℕ} (M : GradedModule k n) (c : Fin (n + 1) → k) (d e : ℤ)
    (hde : d + -1 = e) (h : Subsingleton (M.obj e)) :
    LinearMap.range ((M.mulLHom c).app d).hom = ⊥ := by
  subst hde
  have h2 : Subsingleton ((M.twist (-1)).obj d) := h
  exact range_eq_bot_of_subsingleton _

/-! ## `S/(x₀, x₁)` on `ℙ¹`: coherent, nonzero, of finite length -/

variable (k) in
/-- The coefficient vector of the variable `xᵢ`. -/
def unitVector {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) → k := Pi.single i 1

lemma linearForm_unitVector_zero :
    MvPolynomial.linearForm (unitVector k (0 : Fin 2)) = X 0 := by
  rw [MvPolynomial.linearForm_def, Fin.sum_univ_two]
  simp [unitVector]

lemma linearForm_unitVector_one :
    MvPolynomial.linearForm (unitVector k (1 : Fin 2)) = X 1 := by
  rw [MvPolynomial.linearForm_def, Fin.sum_univ_two]
  simp [unitVector]

variable (k) in
/-- `S/(x₀)` on `ℙ¹`. -/
abbrev hyperplaneQuot : GradedModule k 1 :=
  (structureModule k 1).quotL (unitVector k 0)

variable (k) in
/-- `S/(x₀, x₁)` on `ℙ¹`: forced to be coherent by the closure fields of `Cohomology`,
nonzero in degree `0`, and zero in degree `1`. -/
abbrev finiteLengthQuot : GradedModule k 1 :=
  (hyperplaneQuot k).quotL (unitVector k 1)

/-- Multiplication by `x₁` is surjective from degree `0` to degree `1` on `S/(x₀)`. -/
lemma surjective_hyperplaneQuot_mulL :
    Function.Surjective
      (((hyperplaneQuot k).mulL (unitVector k 1) 0 1 (by norm_num)).hom) := by
  intro z
  obtain ⟨p, rfl⟩ :=
    surjective_toCoker_app ((structureModule k 1).mulLHom (unitVector k 0)) 1 z
  obtain ⟨pv, hpv⟩ := p
  have hp1 : pv.IsHomogeneous 1 := by
    rw [polySubmodule_of_nonneg k 1 (by norm_num),
      MvPolynomial.mem_homogeneousSubmodule] at hpv
    exact hpv
  set a := coeff (Finsupp.single 0 1) pv with ha
  set b := coeff (Finsupp.single 1 1) pv with hb
  have hpeq : pv = C a * X 0 + C b * X 1 :=
    MvPolynomial.eq_linear_of_isHomogeneous_one _ hp1
  refine ⟨((toCoker ((structureModule k 1).mulLHom (unitVector k 0))).app 0).hom
    ⟨C b, C_mem_polySubmodule_zero b⟩, ?_⟩
  have hcomm := congrArg
    (fun g : (structureModule k 1).obj 0 ⟶ (hyperplaneQuot k).obj 1 =>
      g.hom ⟨C b, C_mem_polySubmodule_zero b⟩)
    (comm_mulL (toCoker ((structureModule k 1).mulLHom (unitVector k 0)))
      (unitVector k 1) 0 1 (by norm_num))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  refine hcomm.trans ?_
  simp only [toCoker_app, ModuleCat.hom_ofHom]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [mulLHom_app, range_mulL_eq (structureModule k 1) (unitVector k 0) (1 + -1) 0 1
    (by norm_num) (by norm_num)]
  refine ⟨⟨- C a, Submodule.neg_mem _ (C_mem_polySubmodule_zero a)⟩, Subtype.ext ?_⟩
  rw [structureModule_mulL_val, linearForm_unitVector_zero, Submodule.coe_sub,
    structureModule_mulL_val, linearForm_unitVector_one]
  have hfin : (X 0 : MvPolynomial (Fin (1 + 1)) k) * (- C a) = X 1 * C b - pv := by
    rw [hpeq]; ring
  exact hfin

lemma subsingleton_hyperplaneQuot_neg : Subsingleton ((hyperplaneQuot k).obj (-1)) := by
  haveI h : Subsingleton ((structureModule k 1).obj (-1)) :=
    subsingleton_polySubmodule_neg (by norm_num)
  exact subsingleton_quotient_of_subsingleton _

/-- `S/(x₀, x₁)` is nonzero in degree `0`. -/
lemma nontrivial_finiteLengthQuot (d : ℤ) (hd : d = 0) :
    Nontrivial ((finiteLengthQuot k).obj d) := by
  subst hd
  have hb1 : LinearMap.range
      (((structureModule k 1).mulLHom (unitVector k 0)).app 0).hom = ⊥ :=
    range_mulLHom_eq_bot _ _ 0 (-1) (by norm_num)
      (subsingleton_polySubmodule_neg (by norm_num))
  haveI : Nontrivial ((hyperplaneQuot k).obj 0) := nontrivial_quotient_of_bot hb1
  have hb2 : LinearMap.range
      (((hyperplaneQuot k).mulLHom (unitVector k 1)).app 0).hom = ⊥ :=
    range_mulLHom_eq_bot _ _ 0 (-1) (by norm_num) subsingleton_hyperplaneQuot_neg
  exact nontrivial_quotient_of_bot hb2

/-- `S/(x₀, x₁)` vanishes in degree `1`. -/
lemma subsingleton_finiteLengthQuot (d : ℤ) (hd : d = 1) :
    Subsingleton ((finiteLengthQuot k).obj d) := by
  subst hd
  have htop : LinearMap.range
      (((hyperplaneQuot k).mulLHom (unitVector k 1)).app 1).hom = ⊤ := by
    rw [mulLHom_app, range_mulL_eq (hyperplaneQuot k) (unitVector k 1) (1 + -1) 0 1
      (by norm_num) (by norm_num)]
    exact LinearMap.range_eq_top.mpr surjective_hyperplaneQuot_mulL
  exact subsingleton_quotient_of_top htop

end AlgebraicGeometry.ProjectiveSpace.GradedModule

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

open GradedModule

variable {k : Type u} [Field k]

/-- **The `NoIrrelevantTorsion` hypothesis of `exists_nonZeroDivisor_linearForm` cannot be
dropped.**

`isCoherent_structureModule`, `isCoherent_twist` and `isCoherent_coker` force the graded
module `S/(x₀, x₁)` on `ℙ¹` to be coherent; it is `k` in degree `0` and `0` in degree `1`, so
no linear form multiplies injectively from degree `0` to degree `1`.  Hence in every
cohomology theory this module must fail `NoIrrelevantTorsion` — and without that hypothesis
the interface is empty, which is how it stood before 2026-08-29. -/
theorem not_noIrrelevantTorsion_finiteLengthQuot [Infinite k] (C : Cohomology k) :
    ¬ C.NoIrrelevantTorsion (finiteLengthQuot k) := by
  intro htf
  have hA : C.IsCoherent (structureModule k 1) := C.isCoherent_structureModule
  have hB : C.IsCoherent (hyperplaneQuot k) :=
    C.isCoherent_coker ((structureModule k 1).mulLHom (unitVector k 0))
      (C.isCoherent_twist hA (-1)) hA
  have hQ : C.IsCoherent (finiteLengthQuot k) :=
    C.isCoherent_coker ((hyperplaneQuot k).mulLHom (unitVector k 1))
      (C.isCoherent_twist hB (-1)) hB
  obtain ⟨c, j, hj, hL, -⟩ :=
    C.exists_nonZeroDivisor_linearForm inferInstance
      (finiteLengthQuot k) (finiteLengthQuot k) hQ hQ htf htf
  haveI : Subsingleton ((finiteLengthQuot k).obj 1) := subsingleton_finiteLengthQuot 1 rfl
  haveI hnt : Nontrivial ((finiteLengthQuot k).obj ((1 : ℤ) + -1)) :=
    nontrivial_finiteLengthQuot _ (by norm_num)
  obtain ⟨x, y, hxy⟩ := hnt
  exact hxy (hL 1 (Subsingleton.elim _ _))

end AlgebraicGeometry.ProjectiveSpace.Cohomology

end
