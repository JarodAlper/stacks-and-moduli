module

public import StacksAndModuli.API.ProjectiveGradedDropVarLoc
public import StacksAndModuli.API.ProjectiveGradedTotal
public import StacksAndModuli.API.ProjectiveGradedCechCohomology

/-!
# The cohomology of quasi-coherent sheaves on `ℙⁿ_k` exists

Supporting API with no Stacks Project counterpart.

This file discharges the obligation `Cohomology.nonempty`: the graded Čech complex of the
standard affine cover supplies every field of `Cohomology k`.  The five substantive inputs,
packaged as `CechSerreData`, are proved in

- `API/ProjectiveGradedSerre.lean` — Serre finiteness and Serre vanishing;
- `API/ProjectiveGradedTorsion.lean` — the torsion-free model;
- `API/ProjectiveGradedTotal.lean` — prime avoidance over an infinite field;
- `API/ProjectiveGradedDropVarLoc.lean` — the hyperplane comparison.

Main declarations:
- `Cohomology.cechSerreData`;
- `Cohomology.nonempty`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

open CategoryTheory GradedModule

/-- **Serre's theorems for the graded Čech complex**, assembled. -/
noncomputable def cechSerreData (k : Type u) [Field k] : CechSerreData k where
  finiteDimensional := fun {_} {M} hM i d => finiteDimensional_cechHgr_of_isFG M hM i d
  serre_vanishing := fun {_} {M} hM i hi => exists_subsingleton_cechHgr_of_isFG M hM i hi
  exists_noIrrelevantTorsion_quotient := fun {_} {M} hM =>
    exists_noIrrelevantTorsion_quotient_of_isFG M hM
  exists_nonZeroDivisor_linearForm := fun {_} hk M M' hM hM' hT hT' =>
    exists_nonZeroDivisor_linearForm_of_infinite hk M M' hM hM' hT hT'
  dropVarIso := fun {_} N _ j _ _ hcoh i =>
    dropVarHgrIso N j (IsFG.of_dropVar j hcoh) hcoh i

/-- **The** cohomology of quasi-coherent sheaves on `ℙⁿ_k`: the graded Čech complex of the
standard affine cover.  Statements that need a *specific* theory — anything using base change
along a field extension, where an abstract theory over `k` cannot be compared with one over
`k'` — should use this one. -/
noncomputable def cech (k : Type u) [Field k] : Cohomology k :=
  ofCech (cechSerreData k)

@[simp] lemma cech_Hgr {k : Type u} [Field k] {n : ℕ} (M : GradedModule k n) (i : ℕ) :
    (cech k).Hgr M i = M.cechHgr i := rfl

@[simp] lemma cech_isCoherent {k : Type u} [Field k] {n : ℕ} (M : GradedModule k n) :
    (cech k).IsCoherent M = GradedModule.IsFG M := rfl

/-- **The cohomology of quasi-coherent sheaves on `ℙⁿ_k` in the graded-module model.** -/
theorem nonempty (k : Type u) [Field k] : Nonempty (Cohomology k) :=
  ⟨cech k⟩

end AlgebraicGeometry.ProjectiveSpace.Cohomology

end
