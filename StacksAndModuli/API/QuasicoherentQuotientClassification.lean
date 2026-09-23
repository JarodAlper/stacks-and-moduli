module

public import StacksAndModuli.API.EpiKernelClassification
public import StacksAndModuli.API.IdealSheafFromQuasicoherent
public import StacksAndModuli.API.OpenCoverQuotient
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Quasicoherent quotients classified by their ideal sheaves

A quasicoherent quotient of the structure sheaf is determined, compatibly with its
quotient map, by its affine-local kernel ideal.  This file connects the concrete
`IdealSheafData` construction with the categorical classification of epimorphisms by
their kernel subobjects.

This is supporting API with no direct Stacks Project counterpart.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {M Q : X.Modules}

private lemma Modules.exists_kernel_ι_app_eq_iff_of_quotient
    (π : M ⟶ Q) (V : X.Opens) (s : Γ(M, V)) :
    (∃ y : Γ(kernel π, V), ((kernel.ι π).app V).hom y = s) ↔
      (π.app V).hom s = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    have h0 : ((kernel.ι π ≫ π).app V).hom y = 0 := by
      rw [kernel.condition]
      rfl
    exact h0
  · intro hs
    let E := SheafOfModules.evaluation (R := X.ringCatSheaf) (Opposite.op V)
    letI : CategoryTheory.Functor.PreservesZeroMorphisms E := by
      constructor
      intro A B
      rfl
    let sk : LinearMap.ker (E.map π).hom := ⟨s, hs⟩
    let y0 : ToType (kernel (E.map π)) :=
      (ModuleCat.kernelIsoKer (E.map π)).inv.hom sk
    let y : Γ(kernel π, V) :=
      ((PreservesKernel.iso E π).inv.hom y0 : ToType (E.obj (kernel π)))
    refine ⟨y, ?_⟩
    have h1 : ((PreservesKernel.iso E π).inv ≫ E.map (kernel.ι π)).hom y0 =
        (kernel.ι (E.map π)).hom y0 :=
      CategoryTheory.congr_fun (PreservesKernel.iso_inv_ι E π) y0
    have h2 : ((ModuleCat.kernelIsoKer (E.map π)).inv ≫ kernel.ι (E.map π)).hom sk =
        (ModuleCat.ofHom (LinearMap.ker (E.map π).hom).subtype).hom sk :=
      CategoryTheory.congr_fun (ModuleCat.kernelIsoKer_inv_kernel_ι (E.map π)) sk
    exact h1.trans h2

namespace Modules.Hom

/-- Two epimorphic quasicoherent quotients of the structure sheaf with the same
affine-local kernel ideal are isomorphic under the structure sheaf. -/
theorem exists_iso_of_kernelIdealSheafData_eq
    (M Q : X.Modules) [M.IsQuasicoherent] [Q.IsQuasicoherent]
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (ψ : SheafOfModules.unit X.ringCatSheaf ⟶ Q) [Epi φ] [Epi ψ]
    (h : kernelIdealSheafData M φ = kernelIdealSheafData Q ψ) :
    ∃ e : M ≅ Q, φ ≫ e.hom = ψ := by
  have haff (V : X.affineOpens) :
      (PresheafOfModules.Submodule.range (kernel.ι φ).val).obj (op V.1) =
        (PresheafOfModules.Submodule.range (kernel.ι ψ).val).obj (op V.1) := by
    ext s
    rw [PresheafOfModules.Submodule.mem_range_iff,
      PresheafOfModules.Submodule.mem_range_iff]
    change (∃ y : Γ(kernel φ, V.1),
      (Modules.Hom.app (kernel.ι φ) V.1).hom y = s) ↔
      (∃ y : Γ(kernel ψ, V.1),
        (Modules.Hom.app (kernel.ι ψ) V.1).hom y = s)
    rw [Modules.exists_kernel_ι_app_eq_iff_of_quotient φ V.1 s,
      Modules.exists_kernel_ι_app_eq_iff_of_quotient ψ V.1 s]
    have hmem :=
      SetLike.ext_iff.mp (congrArg (fun I : X.IdealSheafData ↦ I.ideal V) h) s
    change s ∈ kernelIdeal φ V ↔ s ∈ kernelIdeal ψ V at hmem
    rw [mem_kernelIdeal_iff, mem_kernelIdeal_iff] at hmem
    exact hmem
  have hrange : PresheafOfModules.Submodule.range (kernel.ι φ).val =
      PresheafOfModules.Submodule.range (kernel.ι ψ).val :=
    Modules.presheafSubmodule_eq_of_isLocal_of_affine
      (Modules.presheafSubmoduleIsLocal_range _)
      (Modules.presheafSubmoduleIsLocal_range _) haff
  haveI : Mono (kernel.ι φ).val := Modules.val_mono_of_mono _
  haveI : Mono (kernel.ι ψ).val := Modules.val_mono_of_mono _
  apply CategoryTheory.Abelian.exists_iso_comp_eq_of_kernelSubobject_eq φ ψ
  exact Subobject.mk_eq_mk_of_comm _ _
    ((SheafOfModules.unit X.ringCatSheaf).isoOfRangeEq
      (kernel.ι φ) (kernel.ι ψ) hrange)
    (SheafOfModules.isoOfRangeEq_hom_comp
      (SheafOfModules.unit X.ringCatSheaf) (kernel.ι φ) (kernel.ι ψ) hrange)

end Modules.Hom

end AlgebraicGeometry.Scheme

end
