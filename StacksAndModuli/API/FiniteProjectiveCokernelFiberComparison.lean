module

public import StacksAndModuli.API.FiniteProjectiveCokernelFiberCriterion
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Finite projective two-step recurrences from fibre comparison

This file combines two algebraic mechanisms used in relative graded persistence on
projective one-space.  A comparison of right-exact two-step recurrences advances an
isomorphism from two consecutive terms to the next.  If the comparison target has an
injective first Koszul map over every maximal-local residue field, the same comparison
also supplies the fibrewise injectivity criterion making the next source term projective.

The main declarations are
`LinearMap.finite_projective_and_fibreComparison_of_twoStep` and its direct-residue form
`LinearMap.finite_projective_and_fibreComparison_of_twoStep_baseChange`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace LinearMap

open TensorProduct

variable {R : Type u} [CommRing R]
variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type u}
variable [AddCommGroup X₀] [Module R X₀]
variable [AddCommGroup X₁] [Module R X₁]
variable [AddCommGroup X₂] [Module R X₂]
variable [AddCommGroup Y₀] [Module R Y₀]
variable [AddCommGroup Y₁] [Module R Y₁]
variable [AddCommGroup Y₂] [Module R Y₂]

/-- In a comparison of right-exact sequences, bijectivity of the first two vertical maps
implies bijectivity of the third. -/
theorem bijective_right_of_exact_comparison
    (f : X₀ →ₗ[R] X₁) (g : X₁ →ₗ[R] X₂)
    (f' : Y₀ →ₗ[R] Y₁) (g' : Y₁ →ₗ[R] Y₂)
    (β₀ : X₀ →ₗ[R] Y₀) (β₁ : X₁ →ₗ[R] Y₁) (β₂ : X₂ →ₗ[R] Y₂)
    (hex : Function.Exact f g) (hg : Function.Surjective g)
    (hex' : Function.Exact f' g') (hg' : Function.Surjective g')
    (hcommF : β₁.comp f = f'.comp β₀)
    (hcommG : β₂.comp g = g'.comp β₁)
    (hβ₀ : Function.Bijective β₀) (hβ₁ : Function.Bijective β₁) :
    Function.Bijective β₂ := by
  constructor
  · intro x y hxy
    obtain ⟨z, rfl⟩ := hg x
    obtain ⟨w, hw⟩ := hg y
    have hker : g' (β₁ (z - w)) = 0 := by
      have hG := congrArg (fun h ↦ h (z - w)) hcommG
      simp only [comp_apply, map_sub] at hG
      calc
        g' (β₁ (z - w)) = g' (β₁ z) - g' (β₁ w) := by rw [map_sub, map_sub]
        _ = β₂ (g z) - β₂ (g w) := hG.symm
        _ = β₂ (g z) - β₂ y := congrArg (fun v ↦ β₂ (g z) - β₂ v) hw
        _ = 0 := sub_eq_zero.mpr hxy
    obtain ⟨a', ha'⟩ := (hex' (β₁ (z - w))).mp hker
    obtain ⟨a, rfl⟩ := hβ₀.2 a'
    have hF := congrArg (fun h ↦ h a) hcommF
    simp only [comp_apply] at hF
    have hzw : f a = z - w := hβ₁.1 (hF.trans ha')
    have hgf : g (f a) = 0 := (hex (f a)).mpr ⟨a, rfl⟩
    rw [hzw, map_sub, sub_eq_zero] at hgf
    exact hgf.trans hw
  · intro y
    obtain ⟨z', rfl⟩ := hg' y
    obtain ⟨z, hz⟩ := hβ₁.2 z'
    refine ⟨g z, ?_⟩
    have hG := congrArg (fun h ↦ h z) hcommG
    simp only [comp_apply] at hG
    exact hG.trans (congrArg g' hz)

/-- The residue field at a maximal localization, used by the two-step finite-projectivity
induction below. -/
abbrev maximalLocalResidue (I : Ideal R) [I.IsMaximal] :=
  IsLocalRing.ResidueField (Localization.AtPrime I)

/-- Cancelling localization before passage to a maximal residue field identifies the
maximal-local fibre of a module with its direct scalar extension from the original ring. -/
noncomputable def maximalResidueCancelLocalizationEquiv
    (I : Ideal R) [I.IsMaximal]
    (M : Type u) [AddCommGroup M] [Module R M] :
    (I.ResidueField ⊗[Localization.AtPrime I]
        LocalizedModule I.primeCompl M) ≃ₗ[I.ResidueField]
      I.ResidueField ⊗[R] M :=
  (TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl I.ResidueField I.ResidueField)
      (LocalizedModule.equivTensorProduct I.primeCompl M)).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange
      R (Localization.AtPrime I) I.ResidueField I.ResidueField M)

/-- The preceding cancellation equivalence is natural in the module. -/
theorem maximalResidueCancelLocalizationEquiv_naturality
    (I : Ideal R) [I.IsMaximal]
    {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    (maximalResidueCancelLocalizationEquiv I N).toLinearMap.comp
        ((LocalizedModule.map I.primeCompl f).baseChange I.ResidueField) =
      (f.baseChange I.ResidueField).comp
        (maximalResidueCancelLocalizationEquiv I M).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k z =>
      induction z using LocalizedModule.induction_on with
      | h m s =>
          simp [maximalResidueCancelLocalizationEquiv]
  | add x y hx hy =>
      simpa only [comp_apply, map_add] using congrArg₂ (fun a b ↦ a + b) hx hy

/-- Injectivity after direct scalar extension to a maximal residue field implies the
localized-residue injectivity used by the local projective-cokernel criterion. -/
theorem injective_lTensor_localized_of_injective_baseChange
    (I : Ideal R) [I.IsMaximal]
    {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (hf : Function.Injective (f.baseChange I.ResidueField)) :
    Function.Injective
      ((LocalizedModule.map I.primeCompl f).lTensor I.ResidueField) := by
  intro x y hxy
  apply (maximalResidueCancelLocalizationEquiv I M).injective
  apply hf
  have hnat := maximalResidueCancelLocalizationEquiv_naturality I f
  have hx := congrArg (fun h ↦ h x) hnat
  have hy := congrArg (fun h ↦ h y) hnat
  simp only [comp_apply, LinearMap.baseChange_eq_ltensor] at hx hy
  exact hx.symm.trans
    ((congrArg (maximalResidueCancelLocalizationEquiv I N) hxy).trans hy)

/-- Direct-residue form of the finite-projective cokernel criterion. -/
theorem projective_of_exact_of_surjective_of_forall_maximal_baseChange_injective
    {M N P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hex : Function.Exact f g) (hg : Function.Surjective g)
    (hf : ∀ (I : Ideal R) [I.IsMaximal],
      Function.Injective (f.baseChange I.ResidueField)) :
    Module.Projective R P := by
  apply projective_of_exact_of_surjective_of_forall_maximal_lTensor_injective
    f g hex hg
  intro I hI
  exact injective_lTensor_localized_of_injective_baseChange I f (hf I)

/-- A two-step exact recurrence propagates both finite projectivity and a residue-field
comparison.  The comparison with a second recurrence is assumed in each degree, but
bijectivity is required only in the first two degrees; right exactness advances it together
with projectivity. -/
theorem finite_projective_and_fibreComparison_of_twoStep
    (X : ℕ → Type u) [∀ t, AddCommGroup (X t)] [∀ t, Module R (X t)]
    (f : ∀ t, X t →ₗ[R] (Fin 2 → X (t + 1)))
    (g : ∀ t, (Fin 2 → X (t + 1)) →ₗ[R] X (t + 2))
    (hex : ∀ t, Function.Exact (f t) (g t))
    (hg : ∀ t, Function.Surjective (g t))
    (Y : ∀ (I : Ideal R) [I.IsMaximal], ℕ → Type u)
    [∀ (I : Ideal R) [I.IsMaximal] (t : ℕ), AddCommGroup (Y I t)]
    [∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      Module (maximalLocalResidue I) (Y I t)]
    (fY : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      Y I t →ₗ[maximalLocalResidue I] (Fin 2 → Y I (t + 1)))
    (gY : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      (Fin 2 → Y I (t + 1)) →ₗ[maximalLocalResidue I] Y I (t + 2))
    (hexY : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      Function.Exact (fY I t) (gY I t))
    (hgY : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ), Function.Surjective (gY I t))
    (hinjY : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ), Function.Injective (fY I t))
    (β : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      ((maximalLocalResidue I) ⊗[Localization.AtPrime I]
          LocalizedModule I.primeCompl (X t)) →ₗ[maximalLocalResidue I]
        Y I t)
    (βpow : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      ((maximalLocalResidue I) ⊗[Localization.AtPrime I]
          LocalizedModule I.primeCompl (Fin 2 → X t)) →ₗ[maximalLocalResidue I]
        (Fin 2 → Y I t))
    (hβpow : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ), Function.Bijective (β I t) →
      Function.Bijective (βpow I t))
    (hcommF : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      (βpow I (t + 1)).comp
          ((LocalizedModule.map I.primeCompl (f t)).baseChange
            (maximalLocalResidue I)) =
        (fY I t).comp (β I t))
    (hcommG : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      (β I (t + 2)).comp
          ((LocalizedModule.map I.primeCompl (g t)).baseChange
            (maximalLocalResidue I)) =
        (gY I t).comp (βpow I (t + 1)))
    (hfin0 : Module.Finite R (X 0)) (hproj0 : Module.Projective R (X 0))
    (hfin1 : Module.Finite R (X 1)) (hproj1 : Module.Projective R (X 1))
    (hβ0 : ∀ (I : Ideal R) [I.IsMaximal], Function.Bijective (β I 0))
    (hβ1 : ∀ (I : Ideal R) [I.IsMaximal], Function.Bijective (β I 1)) :
    ∀ t, (Module.Finite R (X t) ∧ Module.Projective R (X t)) ∧
      ∀ (I : Ideal R) [I.IsMaximal], Function.Bijective (β I t) := by
  intro t
  induction t using Nat.twoStepInduction with
  | zero => exact ⟨⟨hfin0, hproj0⟩, hβ0⟩
  | one => exact ⟨⟨hfin1, hproj1⟩, hβ1⟩
  | more t ht ht1 =>
      rcases ht with ⟨⟨hft, hpt⟩, hbt⟩
      rcases ht1 with ⟨⟨hft1, hpt1⟩, hbt1⟩
      letI : Module.Finite R (X t) := hft
      letI : Module.Projective R (X t) := hpt
      letI : Module.Finite R (X (t + 1)) := hft1
      letI : Module.Projective R (X (t + 1)) := hpt1
      letI : Module.Projective R (Fin 2 → X (t + 1)) :=
        Module.Projective.of_equiv'
          (LinearEquiv.finTwoArrow R (X (t + 1))).symm
      have hfin2 : Module.Finite R (X (t + 2)) :=
        Module.Finite.of_surjective (g t) (hg t)
      have hfibreInj : ∀ (I : Ideal R) (hI : I.IsMaximal),
          Function.Injective
            ((LocalizedModule.map I.primeCompl (f t)).lTensor
              (maximalLocalResidue I)) := by
        intro I hI x y hxy
        apply (hbt I).1
        apply (hinjY I t)
        have hc := congrArg
          (fun h ↦ h x) (hcommF I t)
        have hc' := congrArg
          (fun h ↦ h y) (hcommF I t)
        simp only [comp_apply] at hc hc'
        exact Eq.trans hc.symm (Eq.trans (congrArg (βpow I (t + 1)) hxy) hc')
      have hproj2 : Module.Projective R (X (t + 2)) :=
        projective_of_exact_of_surjective_of_forall_maximal_lTensor_injective
          (f t) (g t) (hex t) (hg t) hfibreInj
      refine ⟨⟨hfin2, hproj2⟩, ?_⟩
      intro I hI
      have hgLoc : Function.Surjective
          (LocalizedModule.map I.primeCompl (g t)) :=
        LocalizedModule.map_surjective I.primeCompl (g t) (hg t)
      have hexLoc : Function.Exact
          (LocalizedModule.map I.primeCompl (f t))
          (LocalizedModule.map I.primeCompl (g t)) :=
        LocalizedModule.map_exact I.primeCompl (f t) (g t) (hex t)
      have hgRes : Function.Surjective
          ((LocalizedModule.map I.primeCompl (g t)).baseChange
            (maximalLocalResidue I)) :=
        LinearMap.baseChange_surjective (maximalLocalResidue I) hgLoc
      have hexRes : Function.Exact
          ((LocalizedModule.map I.primeCompl (f t)).baseChange
            (maximalLocalResidue I))
          ((LocalizedModule.map I.primeCompl (g t)).baseChange
            (maximalLocalResidue I)) := by
        simpa only [LinearMap.baseChange_eq_ltensor] using
          lTensor_exact (maximalLocalResidue I) hexLoc hgLoc
      exact bijective_right_of_exact_comparison
        ((LocalizedModule.map I.primeCompl (f t)).baseChange
          (maximalLocalResidue I))
        ((LocalizedModule.map I.primeCompl (g t)).baseChange
          (maximalLocalResidue I))
        (fY I t) (gY I t)
        (β I t) (βpow I (t + 1)) (β I (t + 2))
        hexRes hgRes (hexY I t) (hgY I t)
        (hcommF I t) (hcommG I t)
        (hbt I) (hβpow I (t + 1) (hbt1 I))

/-- Direct-residue form of
`LinearMap.finite_projective_and_fibreComparison_of_twoStep`.  This version is convenient
when the comparison is a canonical base-change map with source `κ(I) ⊗[R] X`; the
localization required by the projective-cokernel criterion is cancelled internally. -/
theorem finite_projective_and_fibreComparison_of_twoStep_baseChange
    (X : ℕ → Type u) [∀ t, AddCommGroup (X t)] [∀ t, Module R (X t)]
    (f : ∀ t, X t →ₗ[R] (Fin 2 → X (t + 1)))
    (g : ∀ t, (Fin 2 → X (t + 1)) →ₗ[R] X (t + 2))
    (hex : ∀ t, Function.Exact (f t) (g t))
    (hg : ∀ t, Function.Surjective (g t))
    (Y : ∀ (I : Ideal R) [I.IsMaximal], ℕ → Type u)
    [∀ (I : Ideal R) [I.IsMaximal] (t : ℕ), AddCommGroup (Y I t)]
    [∀ (I : Ideal R) [I.IsMaximal] (t : ℕ), Module I.ResidueField (Y I t)]
    (fY : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      Y I t →ₗ[I.ResidueField] (Fin 2 → Y I (t + 1)))
    (gY : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      (Fin 2 → Y I (t + 1)) →ₗ[I.ResidueField] Y I (t + 2))
    (hexY : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      Function.Exact (fY I t) (gY I t))
    (hgY : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ), Function.Surjective (gY I t))
    (hinjY : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ), Function.Injective (fY I t))
    (β : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      (I.ResidueField ⊗[R] X t) →ₗ[I.ResidueField] Y I t)
    (βpow : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      (I.ResidueField ⊗[R] (Fin 2 → X t)) →ₗ[I.ResidueField]
        (Fin 2 → Y I t))
    (hβpow : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ), Function.Bijective (β I t) →
      Function.Bijective (βpow I t))
    (hcommF : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      (βpow I (t + 1)).comp ((f t).baseChange I.ResidueField) =
        (fY I t).comp (β I t))
    (hcommG : ∀ (I : Ideal R) [I.IsMaximal] (t : ℕ),
      (β I (t + 2)).comp ((g t).baseChange I.ResidueField) =
        (gY I t).comp (βpow I (t + 1)))
    (hfin0 : Module.Finite R (X 0)) (hproj0 : Module.Projective R (X 0))
    (hfin1 : Module.Finite R (X 1)) (hproj1 : Module.Projective R (X 1))
    (hβ0 : ∀ (I : Ideal R) [I.IsMaximal], Function.Bijective (β I 0))
    (hβ1 : ∀ (I : Ideal R) [I.IsMaximal], Function.Bijective (β I 1)) :
    ∀ t, (Module.Finite R (X t) ∧ Module.Projective R (X t)) ∧
      ∀ (I : Ideal R) [I.IsMaximal], Function.Bijective (β I t) := by
  intro t
  induction t using Nat.twoStepInduction with
  | zero => exact ⟨⟨hfin0, hproj0⟩, hβ0⟩
  | one => exact ⟨⟨hfin1, hproj1⟩, hβ1⟩
  | more t ht ht1 =>
      rcases ht with ⟨⟨hft, hpt⟩, hbt⟩
      rcases ht1 with ⟨⟨hft1, hpt1⟩, hbt1⟩
      letI : Module.Finite R (X t) := hft
      letI : Module.Projective R (X t) := hpt
      letI : Module.Finite R (X (t + 1)) := hft1
      letI : Module.Projective R (X (t + 1)) := hpt1
      letI : Module.Projective R (Fin 2 → X (t + 1)) :=
        Module.Projective.of_equiv'
          (LinearEquiv.finTwoArrow R (X (t + 1))).symm
      have hfin2 : Module.Finite R (X (t + 2)) :=
        Module.Finite.of_surjective (g t) (hg t)
      have hfibreInj : ∀ (I : Ideal R) [I.IsMaximal],
          Function.Injective ((f t).baseChange I.ResidueField) := by
        intro I hI x y hxy
        apply (hbt I).1
        apply (hinjY I t)
        have hc := congrArg (fun h ↦ h x) (hcommF I t)
        have hc' := congrArg (fun h ↦ h y) (hcommF I t)
        simp only [comp_apply] at hc hc'
        exact Eq.trans hc.symm (Eq.trans (congrArg (βpow I (t + 1)) hxy) hc')
      have hproj2 : Module.Projective R (X (t + 2)) :=
        projective_of_exact_of_surjective_of_forall_maximal_baseChange_injective
          (f t) (g t) (hex t) (hg t) hfibreInj
      refine ⟨⟨hfin2, hproj2⟩, ?_⟩
      intro I hI
      have hgRes : Function.Surjective ((g t).baseChange I.ResidueField) :=
        LinearMap.baseChange_surjective I.ResidueField (hg t)
      have hexRes : Function.Exact
          ((f t).baseChange I.ResidueField)
          ((g t).baseChange I.ResidueField) := by
        simpa only [LinearMap.baseChange_eq_ltensor] using
          lTensor_exact I.ResidueField (hex t) (hg t)
      exact bijective_right_of_exact_comparison
        ((f t).baseChange I.ResidueField)
        ((g t).baseChange I.ResidueField)
        (fY I t) (gY I t)
        (β I t) (βpow I (t + 1)) (β I (t + 2))
        hexRes hgRes (hexY I t) (hgY I t)
        (hcommF I t) (hcommG I t)
        (hbt I) (hβpow I (t + 1) (hbt1 I))

end LinearMap

end
