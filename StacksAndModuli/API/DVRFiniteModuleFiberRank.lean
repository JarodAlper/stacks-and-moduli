module

public import StacksAndModuli.API.FiniteProjectiveFiberRank
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Ranks of finite modules over discrete valuation rings

Supporting API for the closed-fibre step in the projectivity argument for the Quot
functor.  Over a discrete valuation ring, injectivity of multiplication by one
uniformizer implies torsion-freeness.  A finite module with this property is therefore
free and projective, so all of its field base changes have the same dimension.
-/

@[expose] public section

set_option linter.style.haveILetI false

universe u

open TensorProduct

namespace Module

/-- A module over a discrete valuation ring is torsion-free if multiplication by one
uniformizer is injective. -/
theorem isTorsionFree_of_uniformizer_smul_injective
    (R M : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] (ϖ : R) (hϖ : Irreducible ϖ)
    (hinj : Function.Injective (fun x : M ↦ ϖ • x)) :
    Module.IsTorsionFree R M := by
  rw [Module.isTorsionFree_iff_smul_eq_zero]
  intro r x hr
  by_cases hr0 : r = 0
  · exact Or.inl hr0
  · right
    obtain ⟨n, a, ha⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
    have hpow : ∀ n : ℕ, Function.Injective (fun x : M ↦ ϖ ^ n • x) := by
      intro n
      induction n with
      | zero =>
          intro x y hxy
          simpa using hxy
      | succ n ih =>
          intro x y hxy
          apply hinj
          apply ih
          simpa [pow_succ, mul_smul] using hxy
    have hzero : ϖ ^ n • x = 0 := by
      rw [ha, mul_smul, a.isUnit.smul_eq_zero] at hr
      exact hr
    exact hpow n (by simpa using hzero)

/-- A finite module over a discrete valuation ring on which a uniformizer acts
injectively is free. -/
theorem free_of_finite_of_uniformizer_smul_injective
    (R M : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hinj : Function.Injective (fun x : M ↦ ϖ • x)) :
    Module.Free R M := by
  letI : Module.IsTorsionFree R M :=
    isTorsionFree_of_uniformizer_smul_injective R M ϖ hϖ hinj
  exact Module.free_of_finite_type_torsion_free'

/-- A finite module over a discrete valuation ring on which a uniformizer acts
injectively is projective. -/
theorem projective_of_finite_of_uniformizer_smul_injective
    (R M : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hinj : Function.Injective (fun x : M ↦ ϖ • x)) :
    Module.Projective R M := by
  letI : Module.Free R M :=
    free_of_finite_of_uniformizer_smul_injective R M ϖ hϖ hinj
  infer_instance

/-- The dimensions of any two field base changes of a finite module over a DVR agree
if multiplication by a uniformizer is injective. -/
theorem finrank_baseChange_eq_of_finite_of_uniformizer_smul_injective
    (R M K L : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Field K] [Algebra R K] [Field L] [Algebra R L]
    (ϖ : R) (hϖ : Irreducible ϖ)
    (hinj : Function.Injective (fun x : M ↦ ϖ • x)) :
    Module.finrank K (K ⊗[R] M) = Module.finrank L (L ⊗[R] M) := by
  letI : Module.Projective R M :=
    projective_of_finite_of_uniformizer_smul_injective R M ϖ hϖ hinj
  rw [Module.finrank_tensorProduct_eq_of_finite_projective_of_isLocalRing,
    Module.finrank_tensorProduct_eq_of_finite_projective_of_isLocalRing]

end Module
