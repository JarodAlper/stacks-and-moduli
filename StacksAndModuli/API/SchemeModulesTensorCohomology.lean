module

public import StacksAndModuli.API.SchemeModulesTensorExact
public import StacksAndModuli.API.SheafCohomologyLES

/-!
# Cohomology of tensor products with a locally trivial module sheaf

Let `q : M ⟶ Q` be an epimorphism of module sheaves and let `L` be a module sheaf
which is trivial on an open cover.  Exactness of tensoring by `L` identifies the tensor
of the canonical kernel sequence of `q` as a short exact sequence

`0 → (kernel q) ⊗ L → M ⊗ L → Q ⊗ L → 0`.

This file combines that exactness result with the cohomology long exact sequence.  It
packages the two consequences needed for Quot presentations:

* finite generation of `H⁰(M ⊗ L)` and vanishing of `H¹((kernel q) ⊗ L)` imply
  finite generation of `H⁰(Q ⊗ L)`;
* vanishing of `H¹(M ⊗ L)` and `H²((kernel q) ⊗ L)` imply vanishing of
  `H¹(Q ⊗ L)`.

Main declarations:
- `AlgebraicGeometry.Scheme.Modules.
    shortExact_kernel_map_tensorRightFunctor_of_iSup_iso_unit`;
- `AlgebraicGeometry.Scheme.Modules.
    finite_globalSections_tensorRight_of_epi_of_iSup_iso_unit`;
- `AlgebraicGeometry.Scheme.Modules.
    subsingleton_H_one_tensorRight_of_epi_of_iSup_iso_unit`;
- `AlgebraicGeometry.Scheme.Modules.
    finite_globalSections_and_subsingleton_H_one_tensorRight_of_epi_of_iSup_iso_unit`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Tensoring the canonical kernel sequence of an epimorphism by a module sheaf which is
trivial on an open cover gives a short exact sequence. -/
theorem shortExact_kernel_map_tensorRightFunctor_of_iSup_iso_unit
    {M Q L : X.Modules} (q : M ⟶ Q) [Epi q]
    {J : Type u} (U : J → X.Opens) (hU : IsOpenCover U)
    (e : ∀ j, (restrictFunctor (U j).ι).obj L ≅
      SheafOfModules.unit (U j).toScheme.ringCatSheaf) :
    ((ShortComplex.mk (kernel.ι q) q (kernel.condition q)).map
      (tensorRightFunctor L)).ShortExact := by
  exact CategoryTheory.ShortComplex.ShortExact.map_tensorRightFunctor_of_iSup_iso_unit
    ({ exact := ShortComplex.exact_kernel q } :
      (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact)
    L U hU e

/-- Let `q : M ⟶ Q` be an epimorphism and let `L` be trivial on an open cover.  If
`H⁰(M ⊗ L)` is finite over the base ring and `H¹((kernel q) ⊗ L)` vanishes, then
`H⁰(Q ⊗ L)` is finite over the base ring. -/
theorem finite_globalSections_tensorRight_of_epi_of_iSup_iso_unit
    {R : CommRingCat.{u}} (p : X ⟶ Spec R) {M Q L : X.Modules}
    (q : M ⟶ Q) [Epi q]
    {J : Type u} (U : J → X.Opens) (hU : IsOpenCover U)
    (e : ∀ j, (restrictFunctor (U j).ι).obj L ≅
      SheafOfModules.unit (U j).toScheme.ringCatSheaf)
    (hfinite :
      letI := globalSectionsModule p (M ⊗ₘ L)
      Module.Finite R Γ(M ⊗ₘ L, ⊤))
    (hker₁ : Subsingleton
      (((SheafOfModules.toSheaf _).obj ((kernel q) ⊗ₘ L)).H 1)) :
    letI := globalSectionsModule p (Q ⊗ₘ L)
    Module.Finite R Γ(Q ⊗ₘ L, ⊤) := by
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  let ST := S.map (tensorRightFunctor L)
  have hST : ST.ShortExact :=
    shortExact_kernel_map_tensorRightFunctor_of_iSup_iso_unit q U hU e
  exact finite_globalSections_of_shortExact_of_subsingleton_H_one p hST hfinite hker₁

/-- Let `q : M ⟶ Q` be an epimorphism and let `L` be trivial on an open cover.  If
`H¹(M ⊗ L)` and `H²((kernel q) ⊗ L)` vanish, then `H¹(Q ⊗ L)` vanishes. -/
theorem subsingleton_H_one_tensorRight_of_epi_of_iSup_iso_unit
    {M Q L : X.Modules} (q : M ⟶ Q) [Epi q]
    {J : Type u} (U : J → X.Opens) (hU : IsOpenCover U)
    (e : ∀ j, (restrictFunctor (U j).ι).obj L ≅
      SheafOfModules.unit (U j).toScheme.ringCatSheaf)
    (hM₁ : Subsingleton
      (((SheafOfModules.toSheaf _).obj (M ⊗ₘ L)).H 1))
    (hker₂ : Subsingleton
      (((SheafOfModules.toSheaf _).obj ((kernel q) ⊗ₘ L)).H 2)) :
    Subsingleton (((SheafOfModules.toSheaf _).obj (Q ⊗ₘ L)).H 1) := by
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  let ST := S.map (tensorRightFunctor L)
  have hST : ST.ShortExact :=
    shortExact_kernel_map_tensorRightFunctor_of_iSup_iso_unit q U hU e
  exact subsingleton_H_of_shortExact_right hST rfl hM₁ hker₂

/-- The two Quot-presentation consequences of tensor exactness and the cohomology long
exact sequence, packaged together.  The hypotheses are exactly finite generation of
`H⁰(M ⊗ L)` and vanishing of `H¹(M ⊗ L)`, `H¹((kernel q) ⊗ L)`, and
`H²((kernel q) ⊗ L)`. -/
theorem finite_globalSections_and_subsingleton_H_one_tensorRight_of_epi_of_iSup_iso_unit
    {R : CommRingCat.{u}} (p : X ⟶ Spec R) {M Q L : X.Modules}
    (q : M ⟶ Q) [Epi q]
    {J : Type u} (U : J → X.Opens) (hU : IsOpenCover U)
    (e : ∀ j, (restrictFunctor (U j).ι).obj L ≅
      SheafOfModules.unit (U j).toScheme.ringCatSheaf)
    (hfinite :
      letI := globalSectionsModule p (M ⊗ₘ L)
      Module.Finite R Γ(M ⊗ₘ L, ⊤))
    (hM₁ : Subsingleton
      (((SheafOfModules.toSheaf _).obj (M ⊗ₘ L)).H 1))
    (hker₁ : Subsingleton
      (((SheafOfModules.toSheaf _).obj ((kernel q) ⊗ₘ L)).H 1))
    (hker₂ : Subsingleton
      (((SheafOfModules.toSheaf _).obj ((kernel q) ⊗ₘ L)).H 2)) :
    (letI := globalSectionsModule p (Q ⊗ₘ L)
     Module.Finite R Γ(Q ⊗ₘ L, ⊤)) ∧
      Subsingleton (((SheafOfModules.toSheaf _).obj (Q ⊗ₘ L)).H 1) := by
  exact ⟨finite_globalSections_tensorRight_of_epi_of_iSup_iso_unit
      p q U hU e hfinite hker₁,
    subsingleton_H_one_tensorRight_of_epi_of_iSup_iso_unit
      q U hU e hM₁ hker₂⟩

end AlgebraicGeometry.Scheme.Modules

end
