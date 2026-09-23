module

public import StacksAndModuli.API.ProjectiveTwistHomogeneousSection

/-!
# Global sections of the twisting sheaves on `ℙⁿ_R`

`Γ(ℙⁿ_R, 𝒪(d)) = R[x₀, …, xₙ]_d` for `d ≥ 0` is proved in
`API/ProjectiveTwistGlobalSections.lean` (`homogeneousToGlobalSections_bijective`), for a
degree presented as a natural number.  This file supplies the two facts a `ℤ`-graded
statement needs:

* the same bijectivity with the degree presented as an integer together with an equation
  (`bijective_homogeneousSection'`), so that no section is ever transported across a degree
  equality;
* the vanishing `Γ(ℙⁿ_R, 𝒪(d)) = 0` for `d < 0` (`globalSection_twist_eq_zero_of_neg`),
  which **requires `0 < n`** — on `ℙ⁰` every twist of the structure sheaf is trivial, so the
  statement is false there (see `Section2.4-Projectivity/INSIGHTS.md`).

The vanishing proof is the classical one, made pointwise.  For `d < 0` write `m = -d > 0`.
Multiplying a global section `s` of `𝒪(d)` by `xᵢ^m` gives a global section of `𝒪`, hence a
constant `cᵢ`; multiplying `cᵢ` by `xⱼ^m` and comparing with the same computation in the other
order gives `cᵢ·xⱼ^m = cⱼ·xᵢ^m` in `R[x]ₘ`, which forces `cᵢ = 0` once `i ≠ j` and `m > 0` —
this is where a second variable, i.e. `0 < n`, is used.  So `xᵢ^m · s = 0` for every `i`; at
any point of `ℙⁿ` some `xᵢ` is invertible in the local ring, so `s` vanishes there, and a
section that vanishes at every point is zero.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.bijective_homogeneousSection'`;
* `AlgebraicGeometry.ProjectiveSpace.eq_zero_of_C_mul_X_pow_eq`, the polynomial input;
* `AlgebraicGeometry.ProjectiveSpace.globalSection_twist_eq_zero_of_neg`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry MvPolynomial
open ProjectiveSpectrum.Twist

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) (R : Type u) [CommRing R]

/-- Bijectivity of the form-to-section map in any degree presented as a natural number. -/
theorem bijective_homogeneousSection' (m : ℕ) (e : ℤ) (he : e = (m : ℤ)) :
    Function.Bijective (fun p : homogeneousSubmodule (Fin (n + 1)) R m ↦
      homogeneousSection' (homogeneousSubmodule (Fin (n + 1)) R) p e he ⊤) := by
  subst he
  exact homogeneousToGlobalSections_bijective n R m

/-- `Xᵢ^m`, homogeneous of degree `m`. -/
def stdVarPow (i : Fin (n + 1)) (m : ℕ) : homogeneousSubmodule (Fin (n + 1)) R m :=
  ⟨X i ^ m, by
    have := SetLike.pow_mem_graded (A := homogeneousSubmodule (Fin (n + 1)) R) m
      (X_mem_homogeneousSubmodule_one n R i)
    simpa using this⟩

@[simp] theorem stdVarPow_coe (i : Fin (n + 1)) (m : ℕ) :
    ((stdVarPow n R i m : MvPolynomial (Fin (n + 1)) R)) = X i ^ m := rfl

/-- A constant multiple of `Xⱼ^m` equals a constant multiple of `Xᵢ^m` only if both constants
vanish, for `i ≠ j` and `m > 0`. -/
theorem eq_zero_of_C_mul_X_pow_eq {i j : Fin (n + 1)} (hij : i ≠ j) {m : ℕ} (hm : 0 < m)
    {a b : R} (h : C a * X j ^ m = C b * X i ^ m) : a = 0 := by
  have hne : ¬ (Finsupp.single i m = Finsupp.single j m) := by
    intro hcontra
    rcases (Finsupp.single_eq_single_iff _ _ _ _).mp hcontra with ⟨hji, _⟩ | ⟨hm0, _⟩
    · exact hij hji
    · omega
  have hco := congrArg (MvPolynomial.coeff (Finsupp.single j m)) h
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C_mul,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial] at hco
  simp only [MvPolynomial.coeff_monomial, hne, ↓reduceIte, mul_zero, mul_one] at hco
  exact hco

theorem coe_degreeZero_eq_C (c : homogeneousSubmodule (Fin (n + 1)) R 0) :
    (c : MvPolynomial (Fin (n + 1)) R)
      = C (MvPolynomial.coeff 0 (c : MvPolynomial (Fin (n + 1)) R)) := by
  have h0 : (c : MvPolynomial (Fin (n + 1)) R).totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (σ := Fin (n + 1))).mpr
      ((mem_homogeneousSubmodule _ _).mp c.2)
  exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0

theorem degreeZero_eq_zero_of_mul_X_pow_eq {i j : Fin (n + 1)} (hij : i ≠ j) {m : ℕ}
    (hm : 0 < m) (c c' : homogeneousSubmodule (Fin (n + 1)) R 0)
    (h : (c : MvPolynomial (Fin (n + 1)) R) * X j ^ m
      = (c' : MvPolynomial (Fin (n + 1)) R) * X i ^ m) : c = 0 := by
  obtain ⟨a, ha⟩ : ∃ a, (c : MvPolynomial (Fin (n + 1)) R) = C a :=
    ⟨_, coe_degreeZero_eq_C n R c⟩
  obtain ⟨b, hb⟩ : ∃ b, (c' : MvPolynomial (Fin (n + 1)) R) = C b :=
    ⟨_, coe_degreeZero_eq_C n R c'⟩
  rw [ha, hb] at h
  have ha0 : a = 0 := eq_zero_of_C_mul_X_pow_eq n R hij hm h
  refine Subtype.ext ?_
  rw [ha, ha0, map_zero]
  rfl

/-- Multiplication by `f / 1` is invertible in the localization at a prime avoiding `f`. -/
theorem isUnit_localization_mk_one {A : Type*} [CommRing A] (P : Ideal A) [P.IsPrime]
    {f : A} (hf : f ∉ P) :
    IsUnit (Localization.mk f 1 : Localization P.primeCompl) := by
  have hmem : f ∈ P.primeCompl := hf
  have : (Localization.mk f 1 : Localization P.primeCompl)
      = algebraMap A (Localization P.primeCompl) f := by
    rw [Localization.mk_eq_mk', IsLocalization.mk'_one]
  rw [this]
  exact IsLocalization.map_units _ ⟨f, hmem⟩

/-- **`H⁰(ℙⁿ_R, 𝒪(d)) = 0` for `d < 0`**, when `n ≥ 1`.  (On `ℙ⁰` this is false: every twist
of the structure sheaf is trivial there.) -/
theorem globalSection_twist_eq_zero_of_neg (hn : 0 < n) {d : ℤ} (hd : d < 0)
    (s : Γ(twist (homogeneousSubmodule (Fin (n + 1)) R) d, ⊤)) : s = 0 := by
  classical
  obtain ⟨m, hmpos, hdm⟩ : ∃ m : ℕ, 0 < m ∧ d + (m : ℤ) = 0 :=
    ⟨(-d).toNat, by omega, by omega⟩
  have ht : ∀ i : Fin (n + 1), ∃ c : homogeneousSubmodule (Fin (n + 1)) R 0,
      homogeneousSection' (homogeneousSubmodule (Fin (n + 1)) R) c (0 : ℤ) (by simp) ⊤
        = mulSectionHom (homogeneousSubmodule (Fin (n + 1)) R) (stdVarPow n R i m) d 0
            (by omega) (op ⊤) s :=
    fun i ↦ (bijective_homogeneousSection' n R 0 (0 : ℤ) (by simp)).2 _
  choose c hc using ht
  have hczero : ∀ i : Fin (n + 1), c i = 0 := by
    intro i
    obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), i ≠ j := by
      -- this is the only place `0 < n` is used: a second variable must exist
      haveI : Nontrivial (Fin (n + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
      obtain ⟨j, hj⟩ := exists_ne i
      exact ⟨j, hj.symm⟩
    have hcomm := mulSectionHom_comm (homogeneousSubmodule (Fin (n + 1)) R)
      (stdVarPow n R i m) (stdVarPow n R j m) d 0 (m : ℤ) (by omega) (by omega) (op ⊤) s
    rw [← hc i, ← hc j] at hcomm
    rw [mulSectionHom_homogeneousSection' (homogeneousSubmodule (Fin (n + 1)) R)
        (c i) (stdVarPow n R j m) 0 (m : ℤ) (by simp) (by omega) (by push_cast; omega) (op ⊤),
      mulSectionHom_homogeneousSection' (homogeneousSubmodule (Fin (n + 1)) R)
        (c j) (stdVarPow n R i m) 0 (m : ℤ) (by simp) (by omega) (by push_cast; omega)
        (op ⊤)] at hcomm
    have hpoly := congrArg Subtype.val
      ((bijective_homogeneousSection' n R (0 + m) (m : ℤ) (by push_cast; omega)).1 hcomm)
    exact degreeZero_eq_zero_of_mul_X_pow_eq n R hj hmpos (c i) (c j) hpoly
  have hkill : ∀ i : Fin (n + 1),
      mulSectionHom (homogeneousSubmodule (Fin (n + 1)) R) (stdVarPow n R i m) d 0
        (by omega) (op ⊤) s = 0 := by
    intro i
    rw [← hc i, hczero i]
    exact homogeneousSection'_zero _ _ _ _
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), x.1 ∈ projectiveStandardOpen n R i := by
    have hx : x.1 ∈ (⨆ i : Fin (n + 1), projectiveStandardOpen n R i) := by
      rw [iSup_projectiveStandardOpen_eq_top]
      trivial
    simpa using hx
  have hval := congrArg (fun t : Γ(twist (homogeneousSubmodule (Fin (n + 1)) R) 0, ⊤) ↦
    (t.1 x).1) (hkill i)
  have hne : (X i : MvPolynomial (Fin (n + 1)) R) ∉
      x.1.asHomogeneousIdeal.toIdeal := hi
  have hunit := isUnit_localization_mk_one x.1.asHomogeneousIdeal.toIdeal (f := X i ^ m)
    (by
      intro hcon
      exact hne (x.1.isPrime.mem_of_pow_mem m hcon))
  have hzero0 : (((0 : Γ(twist (homogeneousSubmodule (Fin (n + 1)) R) 0, ⊤)).1 x).1
      : Localization (x.1).asHomogeneousIdeal.toIdeal.primeCompl) = 0 := rfl
  have hAmk : ((s.1 x).1 : Localization (x.1).asHomogeneousIdeal.toIdeal.primeCompl)
      * Localization.mk ((X i : MvPolynomial (Fin (n + 1)) R) ^ m) 1 = 0 := hval.trans hzero0
  refine hunit.mul_left_cancel ?_
  refine (mul_comm _ _).trans (hAmk.trans
    ((mul_zero (Localization.mk ((X i : MvPolynomial (Fin (n + 1)) R) ^ m) 1)).symm.trans ?_))
  exact congrArg (fun z ↦ Localization.mk ((X i : MvPolynomial (Fin (n + 1)) R) ^ m) 1 * z)
    hzero0.symm

end AlgebraicGeometry.ProjectiveSpace

end

end
