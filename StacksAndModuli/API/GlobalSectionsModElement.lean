module

public import StacksAndModuli.API.GlobalSectionsOverBase
public import StacksAndModuli.API.ModuleSheafGlobalSectionMul
public import StacksAndModuli.API.SheafCohomologyLES
public import StacksAndModuli.API.DVRFiniteModuleFiberRank
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Global sections modulo a base element

A short exact sequence

`0 → M --r→ M → C → 0`

on a scheme over `Spec R` gives the expected comparison
`(R/(r)) ⊗ H⁰(M) ≅ H⁰(C)` as soon as `H¹(M)` vanishes.  This is the elementary
long-exact-sequence step in closed-fibre Cohomology and Base Change over a discrete
valuation ring.

Main declaration:

* `Scheme.Modules.quotientTensorGlobalSectionsLinearEquiv_of_shortExact_mul`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry
open scoped Pointwise

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- If multiplication by `r` followed by `q` is a short exact sequence of module
sheaves and `H¹(M) = 0`, then global sections of the quotient are the reduction modulo
`r` of global sections of `M`. -/
noncomputable def quotientTensorGlobalSectionsLinearEquiv_of_shortExact_mul
    {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R) (r : R)
    {M C : X.Modules} (mul : M ⟶ M) (q : M ⟶ C) (hzero : mul ≫ q = 0)
    (hS : (ShortComplex.mk mul q hzero).ShortExact)
    (hmul : ∀ x : Γ(M, ⊤),
      letI := globalSectionsModule p M
      mul.val.app (op ⊤) x = r • x)
    (hH1 : Subsingleton (((SheafOfModules.toSheaf _).obj M).H 1)) :
    letI := globalSectionsModule p M
    letI := globalSectionsModule p C
    ((R ⧸ Ideal.span {r}) ⊗[R] Γ(M, ⊤)) ≃ₗ[R] Γ(C, ⊤) := by
  letI := globalSectionsModule p M
  letI := globalSectionsModule p C
  let S := ShortComplex.mk mul q hzero
  let f : Γ(M, ⊤) →ₗ[R] Γ(M, ⊤) := globalSectionsLinearMap p mul
  let g : Γ(M, ⊤) →ₗ[R] Γ(C, ⊤) := globalSectionsLinearMap p q
  have hf : f = LinearMap.lsmul R Γ(M, ⊤) r := by
    ext x
    exact hmul x
  have hex : Function.Exact f g := by
    intro x
    change (q.val.app (op ⊤)).hom x = 0 ↔
      ∃ y, (mul.val.app (op ⊤)).hom y = x
    exact exact_appTop_of_shortExact hS x
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨y, hy⟩ :=
      surjective_appTop_of_shortExact_of_subsingleton_H_one hS hH1 x
    refine ⟨y, ?_⟩
    change (q.val.app (op ⊤)).hom y = x
    exact hy
  have hrange : LinearMap.range f = r • (⊤ : Submodule R Γ(M, ⊤)) := by
    rw [hf]
    ext x
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
  exact (QuotSMulTop.equivQuotTensor r Γ(M, ⊤)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hrange.symm ≪≫ₗ
      hex.linearEquivOfSurjective hg

/-- The canonical cokernel of multiplication by a base element has the expected
global sections after reduction modulo that element, provided `H¹(M)` vanishes. -/
noncomputable def quotientTensorGlobalSectionsCokernelLinearEquiv
    {R : CommRingCat.{u}} {X : Scheme.{u}} (p : X ⟶ Spec R) (r : R)
    (M : X.Modules)
    [Mono (M.mulByGlobalSection ((baseRingHom p).hom r))]
    (hH1 : Subsingleton (((SheafOfModules.toSheaf _).obj M).H 1)) :
    letI := globalSectionsModule p M
    letI := globalSectionsModule p (cokernel
      (M.mulByGlobalSection ((baseRingHom p).hom r)))
    ((R ⧸ Ideal.span {r}) ⊗[R] Γ(M, ⊤)) ≃ₗ[R]
      Γ(cokernel (M.mulByGlobalSection ((baseRingHom p).hom r)), ⊤) := by
  let mul := M.mulByGlobalSection ((baseRingHom p).hom r)
  apply quotientTensorGlobalSectionsLinearEquiv_of_shortExact_mul p r mul
    (cokernel.π mul) (cokernel.condition mul)
    { exact := ShortComplex.exact_cokernel mul } _ hH1
  intro x
  rw [mulByGlobalSection_app_top_apply]
  rfl

/-- If multiplication by a uniformizer is a monomorphism of module sheaves, then finite
global sections are projective over the discrete valuation ring. -/
theorem projective_globalSections_of_finite_of_mulByGlobalSection_mono
    {R : CommRingCat.{u}} [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (p : X ⟶ Spec R) (ϖ : R) (hϖ : Irreducible ϖ)
    (M : X.Modules)
    [Mono (M.mulByGlobalSection ((baseRingHom p).hom ϖ))]
    (hfinite : letI := globalSectionsModule p M
      Module.Finite R Γ(M, ⊤)) :
    letI := globalSectionsModule p M
    Module.Projective R Γ(M, ⊤) := by
  letI := globalSectionsModule p M
  letI : Module.Finite R Γ(M, ⊤) := hfinite
  apply Module.projective_of_finite_of_uniformizer_smul_injective R Γ(M, ⊤) ϖ hϖ
  let f := M.mulByGlobalSection ((baseRingHom p).hom ϖ)
  haveI : Mono f.val :=
    Functor.map_mono (SheafOfModules.forget X.ringCatSheaf) f
  have hinj : Function.Injective (f.val.app (op ⊤)).hom :=
    PresheafOfModules.injective_of_mono f.val (op ⊤)
  intro x y hxy
  apply hinj
  rw [mulByGlobalSection_app_top_apply, mulByGlobalSection_app_top_apply]
  exact hxy

end AlgebraicGeometry.Scheme.Modules

end
