module

public import StacksAndModuli.API.QuasicoherentSectionsQcqs
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Localization of quasicoherent global sections on projective space

For a quasicoherent sheaf on relative projective space over an affine base, restriction
to the basic open cut out by a base element localizes global sections away from that
element.  Compactness and quasi-separatedness of relative projective space are derived
from the corresponding properties of its structural morphism.

For a discrete valuation ring and a uniformizer, this basic open is the generic fibre.
Thus this result supplies the generic-fibre half of eventual global-sections base change
without using Serre vanishing or Cohomology and Base Change.

Main declaration:

* `Scheme.Modules.isLocalizedModule_projectiveSpace_resBaseBasicOpen`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction of a quasicoherent sheaf on relative projective space to the basic open
of a base element is localization of global sections away from that element. -/
theorem isLocalizedModule_projectiveSpace_resBaseBasicOpen
    (n : ℕ) (R : CommRingCat.{u})
    (N : (Scheme.projectiveSpaceOver n (Spec R)).Modules) [N.IsQuasicoherent]
    (r : R) :
    let X := Scheme.projectiveSpaceOver n (Spec R)
    let p := Scheme.projectiveSpaceOverπ n (Spec R)
    letI : Algebra R Γ(X, ⊤) := globalSectionsAlgebra p
    let t : Γ(X, ⊤) := algebraMap R Γ(X, ⊤) r
    letI : Algebra Γ(X, ⊤) Γ(X, X.basicOpen t) :=
      ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom).toAlgebra
    letI : Module Γ(X, ⊤) Γ(N, X.basicOpen t) :=
      Module.compHom _ ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom)
    letI : Module R Γ(N, ⊤) := globalSectionsModule p N
    letI : Module R Γ(N, X.basicOpen t) :=
      Module.compHom _ (baseRingHom p).hom
    letI : IsScalarTower R Γ(X, ⊤) Γ(N, ⊤) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    letI : IsScalarTower R Γ(X, ⊤) Γ(N, X.basicOpen t) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsLocalizedModule (Submonoid.powers r)
      ((resBasicOpenLinearMap N t).restrictScalars R) := by
  letI : CompactSpace (Scheme.projectiveSpaceOver n (Spec R)) :=
    (AlgebraicGeometry.quasiCompact_iff_compactSpace
      (Scheme.projectiveSpaceOverπ n (Spec R))).mp inferInstance
  letI : QuasiSeparatedSpace (Scheme.projectiveSpaceOver n (Spec R)) :=
    (AlgebraicGeometry.quasiSeparated_iff_quasiSeparatedSpace
      (Scheme.projectiveSpaceOverπ n (Spec R))).mp inferInstance
  exact isLocalizedModule_resBasicOpenLinearMap_of_qcqs_overBase
    (Scheme.projectiveSpaceOverπ n (Spec R)) N CompactSpace.isCompact_univ
      isQuasiSeparated_univ r

end AlgebraicGeometry.Scheme.Modules

end
