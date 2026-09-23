module

public import StacksAndModuli.API.SchemeModulesTensor
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Exact.Basic

/-!
# Sections of a kernel of a morphism of sheaves of modules

Evaluation of a sheaf of modules at an open preserves kernels, so the sections of
`ker(π : M ⟶ N)` over an open are exactly the sections of `M` killed by `π`.  This file
records that as an exactness statement, which is the shape needed by left-exactness
arguments for `Γ_*`.  Injectivity of the inclusion on sections is
`Scheme.Modules.app_injective_of_mono` (`API/OpenCoverQuotient.lean`).

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.exists_kernel_ι_app_eq_iff`;
* `AlgebraicGeometry.Scheme.Modules.exact_kernel_ι_app`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules} (π : M ⟶ N) (V : X.Opens)

/-- A section of `M` over `V` lies in the image of `ker π` exactly when `π` kills it. -/
theorem exists_kernel_ι_app_eq_iff (s : Γ(M, V)) :
    (∃ y : Γ(kernel π, V), ((kernel.ι π).app V).hom y = s) ↔ (π.app V).hom s = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h0 : ((kernel.ι π ≫ π).app V).hom y = 0 := by
      rw [kernel.condition]
      rfl
    exact h0
  · intro hs
    let E := SheafOfModules.evaluation (R := X.ringCatSheaf) (op V)
    let sk : LinearMap.ker (E.map π).hom := ⟨s, hs⟩
    let y0 : ToType (kernel (E.map π)) := (ModuleCat.kernelIsoKer (E.map π)).inv.hom sk
    let y : Γ(kernel π, V) := ((PreservesKernel.iso E π).inv.hom y0 : ToType (E.obj (kernel π)))
    refine ⟨y, ?_⟩
    have h1 : ((PreservesKernel.iso E π).inv ≫ E.map (kernel.ι π)).hom y0 =
        (kernel.ι (E.map π)).hom y0 :=
      CategoryTheory.congr_fun (PreservesKernel.iso_inv_ι E π) y0
    have h2 : ((ModuleCat.kernelIsoKer (E.map π)).inv ≫ kernel.ι (E.map π)).hom sk =
        (ModuleCat.ofHom (LinearMap.ker (E.map π).hom).subtype).hom sk :=
      CategoryTheory.congr_fun (ModuleCat.kernelIsoKer_inv_kernel_ι (E.map π)) sk
    exact h1.trans h2

/-- **Sections are left exact at a kernel.**

Injectivity of `(kernel.ι π).app V` is `Scheme.Modules.app_injective_of_mono`
(`API/OpenCoverQuotient.lean`), since `kernel.ι π` is a monomorphism. -/
theorem exact_kernel_ι_app :
    Function.Exact ((kernel.ι π).app V).hom ((π.app V).hom) := fun s ↦
  (exists_kernel_ι_app_eq_iff π V s).symm.trans
    ⟨fun ⟨y, hy⟩ ↦ ⟨y, hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, hy⟩⟩

end AlgebraicGeometry.Scheme.Modules

end

end
