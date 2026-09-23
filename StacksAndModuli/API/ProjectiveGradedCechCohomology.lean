module

public import StacksAndModuli.API.ProjectiveGradedCech
public import StacksAndModuli.API.ProjectiveGradedH0
public import StacksAndModuli.API.ProjectiveGradedStructureCohomology
public import StacksAndModuli.API.ProjectiveGradedCoherent
public import StacksAndModuli.API.ProjectiveGradedCohomology

/-!
# The Čech model of projective cohomology, and what remains of Serre's theorems

Supporting API with no Stacks Project counterpart.

`API/ProjectiveGradedCohomology.lean` packages the cohomology of quasi-coherent sheaves
on `ℙⁿ_k` as a structure `Cohomology k`, and records the construction of a term of it as
the obligation `Cohomology.nonempty`.  `API/ProjectiveGradedCech.lean` builds the graded
Čech complex of the standard affine cover and proves the *formal* half of that structure:
functoriality, the long exact sequence, Grothendieck vanishing, the twist comparison,
compatibility with linear forms and with finite direct sums, and the invertibility of
multiplication on `ℙ⁰`.

This file assembles those into a partial constructor.  `CechSerreData k` collects exactly
the fields the Čech construction does **not** supply — the coherence predicate with its
closure properties, Serre finiteness and vanishing, prime avoidance over an infinite
field, and the hyperplane comparison — and `Cohomology.ofCech` produces a `Cohomology k`
from them.  The cohomology of the twisting sheaves themselves is now *proved*, in
`StacksAndModuli/API/ProjectiveGradedH0.lean` (degree `0`) and
`StacksAndModuli/API/ProjectiveGradedStructureCohomology.lean` (higher degrees).  Consequently

`Cohomology.nonempty` is reduced to `Nonempty (CechSerreData k)`,

i.e. to Serre's theorems for `ℙⁿ_k` (Hartshorne III.5.1–5.2) and the hyperplane
comparison, with all the homological bookkeeping discharged.  See
`StacksAndModuli/Section2.3-Regularity/COMMENTARY.md`.

Main declarations:
- `AlgebraicGeometry.ProjectiveSpace.CechSerreData`;
- `AlgebraicGeometry.ProjectiveSpace.Cohomology.ofCech`;
- `AlgebraicGeometry.ProjectiveSpace.Cohomology.nonempty_of_cechSerreData`.
-/

@[expose] public section

noncomputable section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open CategoryTheory GradedModule

variable (k : Type u) [Field k]

/-- The part of the cohomology interface that the graded Čech complex does not supply:
the coherence predicate together with its closure properties, Serre finiteness and
vanishing, existence of a hyperplane avoiding the associated points over an infinite
field, and the hyperplane (drop-variable) comparison.

Every field is stated for the Čech cohomology `GradedModule.cechHgr`, so a term of this
structure is exactly what is missing for `Cohomology.nonempty`. -/
structure CechSerreData where
  /-- Cohomology of a coherent sheaf is finite dimensional (Serre finiteness). -/
  finiteDimensional : ∀ {n : ℕ} {M : GradedModule k n}, IsFG M → ∀ (i : ℕ) (d : ℤ),
    FiniteDimensional k ((M.cechHgr i).obj d)
  /-- Serre vanishing: the higher cohomology of a coherent sheaf vanishes after a large
  twist. -/
  serre_vanishing : ∀ {n : ℕ} {M : GradedModule k n}, IsFG M → ∀ i : ℕ, 1 ≤ i →
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → Subsingleton ((M.cechHgr i).obj d)
  /-- Every coherent sheaf has a torsion-free model with the same cohomology. -/
  exists_noIrrelevantTorsion_quotient : ∀ {n : ℕ} {M : GradedModule k n}, IsFG M →
    ∃ (N : GradedModule k n) (φ : M ⟶ N), IsFG N ∧ NoIrrelevantTorsion N ∧
      (∀ d, Function.Surjective (φ.app d).hom) ∧
      (∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → Function.Injective (φ.app d).hom) ∧
      (∀ (i : ℕ) (d : ℤ), Function.Bijective ((cechHgrMap φ i).app d).hom)
  /-- Over an infinite field, a coherent sheaf with no irrelevant torsion admits a hyperplane
  avoiding its associated points. -/
  exists_nonZeroDivisor_linearForm : ∀ {n : ℕ}, Infinite k →
    ∀ M M' : GradedModule k (n + 1), IsFG M → IsFG M' →
      NoIrrelevantTorsion M → NoIrrelevantTorsion M' →
      ∃ (c : Fin (n + 2) → k) (j : Fin (n + 2)), IsUnit (c j) ∧
        (∀ d, Function.Injective ((M.mulLHom c).app d).hom) ∧
        (∀ d, Function.Injective ((M'.mulLHom c).app d).hom)
  /-- The hyperplane comparison: cohomology is insensitive to the closed immersion of the
  hyperplane cut out by a linear form killing the sheaf. -/
  dropVarIso : ∀ {n : ℕ} (N : GradedModule k (n + 1)) (c : Fin (n + 2) → k)
    (j : Fin (n + 2)), IsUnit (c j) →
    (∀ d e (h : d + 1 = e), N.mulL c d e h = 0) → IsFG (N.dropVar j) → ∀ i : ℕ,
    (N.dropVar j).cechHgr i ≅ (N.cechHgr i).dropVar j

namespace Cohomology

variable {k}

/-- The Čech model of the cohomology of quasi-coherent sheaves on `ℙⁿ_k`: everything
formal is supplied by `API/ProjectiveGradedCech.lean`, and the substantive Serre-theoretic
input is the argument. -/
noncomputable def ofCech (D : CechSerreData k) : Cohomology k where
  Hgr M i := M.cechHgr i
  map φ i := cechHgrMap φ i
  map_id M i := cechHgrMap_id M i
  map_comp f g i := cechHgrMap_comp f g i
  δ h i d := cechδ h i d
  injective_map_zero h d := cech_injective_map_zero h.injective d
  exact_map_map h i d := cech_exact_map_map h i d
  exact_map_δ h i d := cech_exact_map_δ h i d
  exact_δ_map h i d := cech_exact_δ_map h i d
  subsingleton_of_lt M i d h := subsingleton_cechHgr M i h d
  twistIso M a i d := cechHgrTwistIso M a i d
  dropVarIso N c j hj hkill hcoh i := D.dropVarIso N c j hj hkill hcoh i
  IsCoherent := IsFG
  isCoherent_structureModule := isFG_structureModule
  isCoherent_twist := fun hM a => hM.twist a
  isCoherent_pow := fun hM r => hM.pow r
  isCoherent_coker := fun f _ hN => IsFG.coker f hN
  isCoherent_of_injective := fun f hf hN => IsFG.of_injective f hf hN
  isCoherent_dropVar := fun hN c j hj hkill => hN.dropVar c j hj hkill
  finiteDimensional := D.finiteDimensional
  serre_vanishing := D.serre_vanishing
  exists_nonZeroDivisor_linearForm := D.exists_nonZeroDivisor_linearForm
  NoIrrelevantTorsion := fun {_} M => GradedModule.NoIrrelevantTorsion M
  noIrrelevantTorsion_pow_structureModule := fun r =>
    GradedModule.noIrrelevantTorsion_pow_structureModule r
  exists_noIrrelevantTorsion_quotient := D.exists_noIrrelevantTorsion_quotient
  subsingleton_Hgr_of_eventually_zero := fun {_} {M} hM i d =>
    subsingleton_cechHgr_of_eventually_zero M hM i d
  hgrZeroStructureIso := fun {n} d hd => by
    haveI : Mono ((structureModule k n).cechAug d) :=
      (ModuleCat.mono_iff_injective _).mpr
        (injective_cechAug _ (injective_structureModule_mulX n) d)
    haveI : Epi ((structureModule k n).cechAug d) :=
      (ModuleCat.epi_iff_surjective _).mpr
        (surjective_cechAug_of_cocycles _ d
          (fun cc hcc => cocycle_structureModule d hd cc hcc))
    haveI : IsIso ((structureModule k n).cechAug d) := isIso_of_mono_of_epi _
    exact (asIso ((structureModule k n).cechAug d)).symm
  subsingleton_Hgr_structureModule := fun {_} i d hi h =>
    subsingleton_cechHgr_structureModule i d hi h
  map_mulLHom M c i d := cechHgr_map_mulLHom M c i d
  mulSpan_zero M d e h := zero_cechHgr_mulSpan M d e h
  zero_mulX_bijective M i q d := by
    have := zero_cechHgr_mulX_isIso M i q d
    exact (ConcreteCategory.isIso_iff_bijective ((M.cechHgr q).mulX i d)).mp inferInstance
  HgrPowIso M r i d := cechHgrPowIso M r i d
  IsGloballyGenerated M d := ∃ e₀ : ℤ, ∀ e : ℤ, e₀ ≤ e → (M.cechHgr 0).mulSpan d e = ⊤
  isGloballyGenerated_iff _ _ := Iff.rfl

/-- **The construction obligation `Cohomology.nonempty` reduces to Serre's theorems.**
Given the coherence predicate with its closure properties, Serre finiteness and vanishing,
prime avoidance over an infinite field, and the hyperplane comparison, the graded Čech
complex of the standard affine cover supplies a
cohomology theory. -/
theorem nonempty_of_cechSerreData (D : CechSerreData k) : Nonempty (Cohomology k) :=
  ⟨ofCech D⟩

end Cohomology

end AlgebraicGeometry.ProjectiveSpace

end
