module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic

/-!
# Divisibility by powers of the variables

Supporting API with no Stacks Project counterpart, developed for the computation of
`H⁰(ℙⁿ, 𝒪(d))` in `StacksAndModuli/API/ProjectiveGradedCech.lean`.

The classical statement `⋂ᵢ S[1/xᵢ] = S` for `S = k[x₀, …, xₙ]` rests on two facts about
the variables: they are prime, and distinct variables are coprime.  From
`xⱼ^m · f = xᵢ^m · g` with `i ≠ j` one concludes `xᵢ^m ∣ f`, and if `f` is homogeneous
then so is the quotient.  This file isolates both steps.

Main declarations:
- `MvPolynomial.X_pow_dvd_of_mul_eq_mul`;
- `MvPolynomial.IsHomogeneous.of_X_pow_mul`;
- `MvPolynomial.eq_zero_of_X_pow_mul_of_isHomogeneous`.
-/

@[expose] public section

universe u v

namespace MvPolynomial

variable {σ : Type v} {R : Type u} [CommRing R]

/-- Multiplying by a power of a variable shifts coefficients. -/
lemma coeff_X_pow_mul (i : σ) (m : ℕ) (s : σ →₀ ℕ) (p : MvPolynomial σ R) :
    coeff (Finsupp.single i m + s) ((X i) ^ m * p) = coeff s p := by
  rw [X_pow_eq_monomial, coeff_monomial_mul, one_mul]

/-- Multiplication by a power of a variable is injective, over any commutative ring: it
shifts coefficients. -/
lemma eq_of_X_pow_mul_eq {i : σ} {m : ℕ} {p q : MvPolynomial σ R}
    (h : (X i) ^ m * p = (X i) ^ m * q) : p = q := by
  refine MvPolynomial.ext _ _ fun s => ?_
  have h1 := congrArg (coeff (Finsupp.single i m + s)) h
  rwa [coeff_X_pow_mul, coeff_X_pow_mul] at h1

/-- A power of a variable divides a product by a coprime variable power only through the
other factor: if `xⱼ^m f = xᵢ^m g` with `i ≠ j`, then `xᵢ^m ∣ f`.

Stated over an arbitrary commutative ring: the argument is combinatorial on monomial
supports, not a primality argument, so no domain hypothesis is needed. -/
lemma X_pow_dvd_of_mul_eq_mul {i j : σ} (hij : i ≠ j)
    (m : ℕ) {f g : MvPolynomial σ R}
    (h : (X j) ^ m * f = (X i) ^ m * g) :
    ((X i : MvPolynomial σ R)) ^ m ∣ f := by
  classical
  rw [X_pow_eq_monomial, monomial_one_dvd_iff_modMonomial_eq_zero]
  refine MvPolynomial.ext _ _ fun s => ?_
  rw [coeff_zero]
  by_cases hle : Finsupp.single i m ≤ s
  · rw [coeff_modMonomial_of_le _ hle]
  · rw [coeff_modMonomial_of_not_le _ hle]
    have h1 : coeff (Finsupp.single j m + s) ((X j) ^ m * f) = coeff s f :=
      coeff_X_pow_mul j m s f
    rw [h, X_pow_eq_monomial, coeff_monomial_mul'] at h1
    have hnle : ¬ (Finsupp.single i m ≤ Finsupp.single j m + s) := by
      intro hc
      refine hle fun a => ?_
      by_cases ha : a = i
      · have hci := hc a
        rw [ha] at hci ⊢
        simpa [Finsupp.single_apply, Ne.symm hij] using hci
      · simp [ha]
    rw [ite_eq_right hnle] at h1
    exact h1.symm

/-- The quotient of a homogeneous polynomial by a power of a variable is homogeneous. -/
lemma IsHomogeneous.of_X_pow_mul {i : σ} {m D : ℕ}
    {g h : MvPolynomial σ R} (hg : g.IsHomogeneous (D + m))
    (hgh : g = (X i) ^ m * h) : h.IsHomogeneous D := by
  intro s hs
  have hcoeff : coeff (Finsupp.single i m + s) g = coeff s h := by
    rw [hgh, coeff_X_pow_mul]
  have hne : coeff (Finsupp.single i m + s) g ≠ 0 := by
    rw [hcoeff]; exact hs
  have hdeg := hg hne
  rw [map_add] at hdeg
  have hsingle : (Finsupp.weight (1 : σ → ℕ)) (Finsupp.single i m) = m := by
    rw [Finsupp.weight_single]
    simp
  rw [hsingle] at hdeg
  omega

/-- **A homogeneous polynomial of degree less than `m` divisible by `Xᵢ^m` is zero.**  Every
monomial of `Xᵢ^m * h` has `Xᵢ`-exponent at least `m`, hence total degree at least `m`; if
the product is homogeneous of degree `N < m` it can have no monomials at all.

This is what makes `H⁰(ℙⁿ, 𝒪(d))` vanish for `d < 0`: a `0`-cocycle of the Čech complex is
represented at a common tower stage `m` by forms divisible by `Xᵢ^m` and homogeneous of
degree `d + m < m`. -/
lemma eq_zero_of_X_pow_mul_of_isHomogeneous {i : σ} {m N : ℕ}
    {g h : MvPolynomial σ R} (hg : g.IsHomogeneous N) (hgh : g = (X i) ^ m * h)
    (hN : N < m) : g = 0 := by
  have hh : h = 0 := by
    refine MvPolynomial.ext _ _ fun s => ?_
    rw [coeff_zero]
    by_contra hs
    have hcoeff : coeff (Finsupp.single i m + s) g = coeff s h := by
      rw [hgh, coeff_X_pow_mul]
    have hne : coeff (Finsupp.single i m + s) g ≠ 0 := by
      rw [hcoeff]; exact hs
    have hdeg := hg hne
    rw [map_add] at hdeg
    have hsingle : (Finsupp.weight (1 : σ → ℕ)) (Finsupp.single i m) = m := by
      rw [Finsupp.weight_single]
      simp
    rw [hsingle] at hdeg
    omega
  rw [hgh, hh, mul_zero]

/-- With only one variable, a homogeneous polynomial is a scalar times a power of that
variable. -/
lemma eq_C_mul_X_pow_of_isHomogeneous_subsingleton [Subsingleton σ] (i : σ)
    {g : MvPolynomial σ R} {D : ℕ} (hg : g.IsHomogeneous D) :
    g = C (coeff (Finsupp.single i D) g) * (X i) ^ D := by
  classical
  have hsupp : ∀ s : σ →₀ ℕ, s = Finsupp.single i (s i) := by
    intro s
    refine Finsupp.ext fun a => ?_
    have hai : a = i := Subsingleton.elim a i
    subst hai
    simp
  refine MvPolynomial.ext _ _ fun s => ?_
  rw [C_mul_X_pow_eq_monomial, coeff_monomial]
  by_cases hs : Finsupp.single i D = s
  · rw [ite_eq_left hs, hs]
  · rw [ite_eq_right hs]
    by_contra hc
    have hdeg := hg hc
    rw [hsupp s, Finsupp.weight_single] at hdeg
    simp only [smul_eq_mul, Pi.one_apply, mul_one] at hdeg
    refine hs ?_
    conv_rhs => rw [hsupp s]
    rw [hdeg]

/-- With only one variable, a homogeneous polynomial of degree `D` is divisible by every
power `xᵢ^e` with `e ≤ D`. -/
lemma X_pow_dvd_of_isHomogeneous_subsingleton [Subsingleton σ] (i : σ)
    {g : MvPolynomial σ R} {D e : ℕ} (hg : g.IsHomogeneous D) (he : e ≤ D) :
    ((X i : MvPolynomial σ R)) ^ e ∣ g := by
  rw [eq_C_mul_X_pow_of_isHomogeneous_subsingleton i hg]
  exact Dvd.dvd.mul_left (pow_dvd_pow _ he) _

end MvPolynomial

end
