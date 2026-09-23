module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Projective cokernels from fibrewise injectivity

Let `f : M → N` be a map between finite projective modules.  If the localization of `f`
at every maximal ideal remains injective after tensoring with the residue field, then the
cokernel of `f` is projective.

This is the algebraic induction step needed by relative graded persistence arguments.  Over
each localized coefficient ring, Mathlib's local-ring splitting criterion turns residue-field
injectivity into a split injection.  Equivalently, the localized cokernel is free.  Projectivity
then descends from all maximal localizations because the global cokernel is finitely presented.

Main declaration:

* `LinearMap.projective_of_exact_of_surjective_of_forall_maximal_lTensor_injective`;
* `LinearMap.finite_projective_of_twoStep_exact_of_forall_maximal_lTensor_injective`;
* `LinearMap.projective_quotient_range_of_forall_maximal_lTensor_injective`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace LinearMap

variable {R M N P : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- In an exact sequence `M → N → P → 0`, with `M` and `N` finite projective,
residue-field injectivity of the first map at every maximal localization makes `P`
projective. -/
theorem projective_of_exact_of_surjective_of_forall_maximal_lTensor_injective
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hex : Function.Exact f g) (hg : Function.Surjective g)
    (hf : ∀ (I : Ideal R) (_ : I.IsMaximal),
      Function.Injective
        ((LocalizedModule.map I.primeCompl f).lTensor
          (IsLocalRing.ResidueField (Localization.AtPrime I)))) :
    Module.Projective R P := by
  letI : Module.FinitePresentation R N :=
    Module.finitePresentation_of_projective R N
  letI : Module.FinitePresentation R P :=
    Module.finitePresentation_of_surjective g hg (by
      rw [hex.linearMap_ker_eq]
      exact Submodule.fg_range f)
  apply Module.projective_of_localization_maximal
  intro I hI
  let S := I.primeCompl
  let Rₚ := Localization.AtPrime I
  let Mₚ := LocalizedModule S M
  let Nₚ := LocalizedModule S N
  let Pₚ := LocalizedModule S P
  let fₚ : Mₚ →ₗ[Rₚ] Nₚ := LocalizedModule.map S f
  let gₚ : Nₚ →ₗ[Rₚ] Pₚ := LocalizedModule.map S g
  have hgₚ : Function.Surjective gₚ := LocalizedModule.map_surjective S g hg
  have hexₚ : Function.Exact fₚ gₚ := LocalizedModule.map_exact S f g hex
  letI : Module.Free Rₚ Nₚ := by
    exact Module.free_of_flat_of_isLocalRing
  have hfree : Module.Free Rₚ Pₚ :=
    Module.free_of_lTensor_residueField_injective fₚ gₚ hgₚ hexₚ (hf I hI)
  letI : Module.Free Rₚ Pₚ := hfree
  exact Module.Projective.of_free

/-- Flatness form of
`LinearMap.projective_of_exact_of_surjective_of_forall_maximal_lTensor_injective`. -/
theorem flat_of_exact_of_surjective_of_forall_maximal_lTensor_injective
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hex : Function.Exact f g) (hg : Function.Surjective g)
    (hf : ∀ (I : Ideal R) (_ : I.IsMaximal),
      Function.Injective
        ((LocalizedModule.map I.primeCompl f).lTensor
          (IsLocalRing.ResidueField (Localization.AtPrime I)))) :
    Module.Flat R P := by
  letI : Module.Projective R P :=
    projective_of_exact_of_surjective_of_forall_maximal_lTensor_injective
      f g hex hg hf
  exact Module.Flat.of_projective

/-- A two-step recurrence
`0 → X t → (X (t + 1))² → X (t + 2) → 0`
whose first map remains injective over every maximal-local residue field propagates
finiteness and projectivity from `X 0` and `X 1` to every `X t`.

This is the module-theoretic persistence step for the standard two-variable Koszul
recurrence on projective one-space. -/
theorem finite_projective_of_twoStep_exact_of_forall_maximal_lTensor_injective
    (X : ℕ → Type u) [∀ t, AddCommGroup (X t)] [∀ t, Module R (X t)]
    (f : ∀ t, X t →ₗ[R] (Fin 2 → X (t + 1)))
    (g : ∀ t, (Fin 2 → X (t + 1)) →ₗ[R] X (t + 2))
    (hex : ∀ t, Function.Exact (f t) (g t))
    (hg : ∀ t, Function.Surjective (g t))
    (hf : ∀ t (I : Ideal R) (_ : I.IsMaximal),
      Function.Injective
        ((LocalizedModule.map I.primeCompl (f t)).lTensor
          (IsLocalRing.ResidueField (Localization.AtPrime I))))
    (hfin0 : Module.Finite R (X 0)) (hproj0 : Module.Projective R (X 0))
    (hfin1 : Module.Finite R (X 1)) (hproj1 : Module.Projective R (X 1)) :
    ∀ t, Module.Finite R (X t) ∧ Module.Projective R (X t) := by
  intro t
  induction t using Nat.twoStepInduction with
  | zero => exact ⟨hfin0, hproj0⟩
  | one => exact ⟨hfin1, hproj1⟩
  | more t ht ht1 =>
      rcases ht with ⟨hft, hpt⟩
      rcases ht1 with ⟨hft1, hpt1⟩
      letI : Module.Finite R (X t) := hft
      letI : Module.Projective R (X t) := hpt
      letI : Module.Finite R (X (t + 1)) := hft1
      letI : Module.Projective R (X (t + 1)) := hpt1
      letI : Module.Projective R (Fin 2 → X (t + 1)) :=
        Module.Projective.of_equiv'
          (LinearEquiv.finTwoArrow R (X (t + 1))).symm
      have hfin2 : Module.Finite R (X (t + 2)) :=
        Module.Finite.of_surjective (g t) (hg t)
      have hproj2 : Module.Projective R (X (t + 2)) :=
        projective_of_exact_of_surjective_of_forall_maximal_lTensor_injective
          (f t) (g t) (hex t) (hg t) (hf t)
      exact ⟨hfin2, hproj2⟩

/-- A map between finite projective modules whose maximal-local residue maps are injective
has projective cokernel. -/
theorem projective_quotient_range_of_forall_maximal_lTensor_injective
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N)
    (hf : ∀ (I : Ideal R) (_ : I.IsMaximal),
      Function.Injective
        ((LocalizedModule.map I.primeCompl f).lTensor
          (IsLocalRing.ResidueField (Localization.AtPrime I)))) :
    Module.Projective R (N ⧸ LinearMap.range f) := by
  let q : N →ₗ[R] (N ⧸ LinearMap.range f) := (LinearMap.range f).mkQ
  exact projective_of_exact_of_surjective_of_forall_maximal_lTensor_injective
    f q f.exact_map_mkQ_range (Submodule.mkQ_surjective (LinearMap.range f)) hf

end LinearMap

end
