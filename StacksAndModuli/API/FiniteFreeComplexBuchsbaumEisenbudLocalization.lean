module

public import Mathlib.RingTheory.Regular.Flat
public import StacksAndModuli.API.FiniteFreeComplexDeterminantalGrade

/-!
# Localizing Buchsbaum--Eisenbud grade conditions

This file packages the determinantal grade condition for a finite free complex over one
ring and proves that it is preserved by localization at a prime.  If an expected-minor
ideal is not contained in the prime, its extension is the unit ideal.  Otherwise every
member of a regular-sequence witness lies in the prime; weak regularity survives the flat
localization, and membership in the localized maximal ideal restores regularity.

This is the localization step in the dimension induction for the local
Buchsbaum--Eisenbud acyclicity criterion.

Main declarations:

* `Matrix.FiniteFreeComplex.HasBuchsbaumEisenbudGrade`;
* `Matrix.FiniteFreeComplex.HasBuchsbaumEisenbudGrade.map_atPrime`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Matrix.FiniteFreeComplex

variable {R : Type u} [CommRing R]

/-- The expected-minor ideals of a finite free complex are either the unit ideal or
contain regular sequences of the homologically prescribed lengths. -/
def HasBuchsbaumEisenbudGrade
    (C : FiniteFreeComplex R) {N : ℕ} (r : C.ExpectedRanks N) : Prop :=
  ∀ i : ℕ, i < N →
    let I := minorIdeal (C.differential i) (r.rank i)
    I = ⊤ ∨
      ∃ f : Fin (i + 1) → R, (∀ j, f j ∈ I) ∧
        RingTheory.Sequence.IsRegular R (List.ofFn f)

/-- The Buchsbaum--Eisenbud grade condition is preserved by localization at a prime. -/
theorem HasBuchsbaumEisenbudGrade.map_atPrime
    {C : FiniteFreeComplex R} {N : ℕ} (r : C.ExpectedRanks N)
    (h : C.HasBuchsbaumEisenbudGrade r) (p : Ideal R) [p.IsPrime] :
    (C.map (algebraMap R (Localization.AtPrime p))).HasBuchsbaumEisenbudGrade
      (r.map (algebraMap R (Localization.AtPrime p))) := by
  intro i hi
  let I := minorIdeal (C.differential i) (r.rank i)
  have hminor : minorIdeal
      ((C.differential i).map (algebraMap R (Localization.AtPrime p)))
        (r.rank i) = I.map (algebraMap R (Localization.AtPrime p)) := by
    exact Matrix.minorIdeal_map (C.differential i) (r.rank i)
      (algebraMap R (Localization.AtPrime p))
  rw [map_differential, ExpectedRanks.map_rank, hminor]
  by_cases hIp : I ≤ p
  · right
    rcases h i hi with htop | ⟨f, hfI, hreg⟩
    · exfalso
      change I = ⊤ at htop
      apply (inferInstance : p.IsPrime).ne_top
      apply top_unique
      rw [← htop]
      exact hIp
    · refine ⟨fun j ↦ algebraMap R (Localization.AtPrime p) (f j), ?_, ?_⟩
      · intro j
        exact Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime p)) (hfI j)
      · have hmem : ∀ x ∈ List.ofFn f, x ∈ p := by
          intro x hx
          rw [List.mem_ofFn'] at hx
          obtain ⟨j, rfl⟩ := hx
          exact hIp (hfI j)
        have hreg' :=
          hreg.toIsWeaklyRegular.isRegular_of_isLocalization_of_mem
            (Localization.AtPrime p) p hmem
        simpa only [List.map_ofFn, Function.comp_def] using hreg'
  · left
    exact (Ideal.map_atPrime_eq_top_iff_not_le I p).mpr hIp

end Matrix.FiniteFreeComplex

end
