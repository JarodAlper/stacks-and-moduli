module

public import StacksAndModuli.API.AffineQuasicoherentEpi
public import StacksAndModuli.API.AffineOpenSectionsExact
public import StacksAndModuli.API.HilbertQuotientBridge
public import StacksAndModuli.API.SchemeModulesKernelFinitePresentation
public import StacksAndModuli.API.SchemeModulesKernelSections

/-!
# Finite affine sections of kernels of finite presentations

Over an arbitrary affine spectrum, an epimorphism between finitely presented quasicoherent
modules has a kernel whose global-section module is finite.  No coherence or noetherian
hypothesis is needed: the target's finite presentation makes the kernel of the surjective map
on affine sections finitely generated.

This is the finite-type half of the syzygy step in a relative twisted-free resolution.  Turning
the resulting finite module into a finitely presented module from flatness over a separate base
ring is the additional relative finiteness theorem needed for iteration.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Sections of a categorical kernel identify linearly with the kernel of the map on sections.
The explicit linear maps bridge the module-valued sheaf morphism and the underlying additive
presheaf notation used by `Γ`. -/
noncomputable def sectionsKernelLinearEquiv {X : Scheme.{u}} (U : X.Opens)
    {M N : X.Modules} (q : M ⟶ N) :
    Γ(kernel q, U) ≃ₗ[Γ(X, U)] LinearMap.ker
      ({ toFun := (q.app U).hom
         map_add' := (q.app U).hom.map_add
         map_smul' := fun r x => (q.val.app (Opposite.op U)).hom.map_smul r x } :
        Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U)) := by
  let qlin : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) :=
    { toFun := (q.app U).hom
      map_add' := (q.app U).hom.map_add
      map_smul' := fun r x => (q.val.app (Opposite.op U)).hom.map_smul r x }
  let f : Γ(kernel q, U) →ₗ[Γ(X, U)] LinearMap.ker qlin :=
    LinearMap.codRestrict (LinearMap.ker qlin)
      { toFun := ((kernel.ι q).app U).hom
        map_add' := ((kernel.ι q).app U).hom.map_add
        map_smul' := fun r x =>
          ((kernel.ι q).val.app (Opposite.op U)).hom.map_smul r x }
      fun x => by
        change (q.app U).hom (((kernel.ι q).app U).hom x) = 0
        exact congrArg (fun h : kernel q ⟶ N => (h.app U).hom x) (kernel.condition q)
  exact LinearEquiv.ofBijective f ⟨by
    intro x y h
    exact app_injective_of_mono (kernel.ι q) U (congrArg Subtype.val h), by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := (exact_kernel_ι_app q U x).mp hx
    exact ⟨y, Subtype.ext hy⟩⟩

/-- On every affine open, the sections of the kernel of an epimorphism between finitely
presented quasicoherent modules form a finite module over the coordinate ring of the open. -/
theorem finite_sections_kernel_of_epi {X : Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [M.IsFinitePresentation]
    [N.IsQuasicoherent] [N.IsFinitePresentation] (q : M ⟶ N) [Epi q]
    (U : X.affineOpens) : Module.Finite Γ(X, U.1) Γ(kernel q, U.1) := by
  have hMfp : Module.FinitePresentation Γ(X, U.1) Γ(M, U.1) :=
    (Scheme.Modules.isFinitePresentation_iff_sections_affineOpens M).mp inferInstance U
  have hNfp : Module.FinitePresentation Γ(X, U.1) Γ(N, U.1) :=
    (Scheme.Modules.isFinitePresentation_iff_sections_affineOpens N).mp inferInstance U
  letI : Module.FinitePresentation Γ(X, U.1) Γ(M, U.1) := hMfp
  letI : Module.FinitePresentation Γ(X, U.1) Γ(N, U.1) := hNfp
  letI : (kernel q).IsQuasicoherent := kernel_isQuasicoherent q
  have hS : (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact :=
    ({ exact := ShortComplex.exact_kernel q } :
      (ShortComplex.mk (kernel.ι q) q (kernel.condition q)).ShortExact)
  have hq : Function.Surjective ((q.app U.1).hom) :=
    surjective_app_of_shortExact_of_isAffineOpen U.2 hS
  let qlin : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(N, U.1) :=
    { toFun := (q.app U.1).hom
      map_add' := (q.app U.1).hom.map_add
      map_smul' := fun r x => (q.val.app (Opposite.op U.1)).hom.map_smul r x }
  have hker : (LinearMap.ker qlin).FG :=
    Module.FinitePresentation.fg_ker qlin hq
  letI : Module.Finite Γ(X, U.1) (LinearMap.ker qlin) := Module.Finite.of_fg hker
  exact Module.Finite.equiv (sectionsKernelLinearEquiv U.1 q).symm

/-- On an affine scheme, the global sections of the kernel of an epimorphism between finitely
presented quasicoherent modules form a finite module over the ring of global functions. -/
theorem finite_sections_kernel_of_epi_of_isAffine {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [M.IsFinitePresentation]
    [N.IsQuasicoherent] [N.IsFinitePresentation] (q : M ⟶ N) [Epi q] :
    Module.Finite Γ(X, ⊤) Γ(kernel q, ⊤) :=
  finite_sections_kernel_of_epi q ⟨⊤, isAffineOpen_top X⟩

/-- On an affine spectrum, the global sections of the kernel of an epimorphism between finitely
presented quasicoherent modules form a finite module over the affine coordinate ring. -/
theorem finite_specEvaluation_kernel_of_epi {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [M.IsFinitePresentation]
    [N.IsQuasicoherent] [N.IsFinitePresentation] (q : M ⟶ N) [Epi q] :
    Module.Finite R ((specEvaluation R ⊤).obj (kernel q)) := by
  have hMfp : Module.FinitePresentation R ((specEvaluation R ⊤).obj M) :=
    moduleSpecΓFunctor_finitePresentation_of_isFinitePresentation M
  have hNfp : Module.FinitePresentation R ((specEvaluation R ⊤).obj N) :=
    moduleSpecΓFunctor_finitePresentation_of_isFinitePresentation N
  letI : Module.FinitePresentation R ((specEvaluation R ⊤).obj M) := hMfp
  letI : Module.FinitePresentation R ((specEvaluation R ⊤).obj N) := hNfp
  let g := (specEvaluation R ⊤).map q
  have hg : Function.Surjective g.hom :=
    (epi_iff_appTop_surjective q).mp inferInstance
  have hker : (LinearMap.ker g.hom).FG :=
    Module.FinitePresentation.fg_ker g.hom hg
  letI : Module.Finite R (LinearMap.ker g.hom) := Module.Finite.of_fg hker
  exact Module.Finite.equiv (specEvaluationKernelLinearEquiv R ⊤ q).symm

end AlgebraicGeometry.Scheme.Modules

end

end
