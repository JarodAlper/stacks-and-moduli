module

public import StacksAndModuli.API.IntegralExtensionKrullDimension
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization

/-!
# Dimension-indexed Noether normalization

Mathlib's Noether normalization theorem produces a finite injective map from a polynomial
ring in some finite number of variables.  Krull-dimension invariance under that integral
injection identifies the number of variables with any prescribed finite value of the target
dimension.

Main declaration:

* `NoetherNormalization.exists_finite_inj_algHom_of_fg_of_ringKrullDim_eq`.
-/

@[expose] public section

noncomputable section

universe u v

namespace NoetherNormalization

/-- A finite-type algebra of finite Krull dimension `n` admits a finite injective
normalization by affine `n`-space. -/
theorem exists_finite_inj_algHom_of_fg_of_ringKrullDim_eq
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A] (n : ℕ)
    (hdim : ringKrullDim A = (n : WithBot ℕ∞)) :
    ∃ g : MvPolynomial (Fin n) k →ₐ[k] A,
      Function.Injective g ∧ g.Finite := by
  obtain ⟨s, g, hginj, hgfinite⟩ :=
    _root_.exists_finite_inj_algHom_of_fg k A
  let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  let _ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A :=
    ⟨RingHom.Finite.to_isIntegral hgfinite⟩
  have hdimIntegral :
      ringKrullDim A = ringKrullDim (MvPolynomial (Fin s) k) :=
    Algebra.IsIntegral.ringKrullDim_eq_of_injective hginj
  have hpoly :
      ringKrullDim (MvPolynomial (Fin s) k) = (s : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add]
    simp
  have hsnCast : (s : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
    rw [← hpoly, ← hdimIntegral]
    exact hdim
  have hsn : s = n := by
    exact_mod_cast hsnCast
  subst n
  exact ⟨g, hginj, hgfinite⟩

end NoetherNormalization

end

end
