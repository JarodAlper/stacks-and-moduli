module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Support
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Surjectivity after localization versus after residue-field base change

Supporting API with no Stacks Project counterpart.

For a linear map `g : M →ₗ[R] N` with `N` finite, surjectivity of the localization of
`g` at a prime `p` is equivalent to surjectivity of the base change of `g` to the
residue field at `p`.  This is the residue-field Nakayama criterion used to compare
the coordinate charts of the Grassmannian with their Plücker images
(`Module.Grassmannian.coordinateToQuotient_localized_surjective_iff_plucker`).

Both statements are read off from the vanishing of the cokernel of `g` after the
respective base changes, using `Module.support`.

Main declarations:
- `LinearMap.baseChange_surjective_iff_subsingleton_tensor_coker`;
- `LinearMap.surjective_localizedMap_iff_surjective_baseChange_residueField`.
-/

@[expose] public section

universe u

open TensorProduct

/-- Surjectivity of a base-changed linear map is the vanishing of the base-changed
cokernel. -/
theorem LinearMap.baseChange_surjective_iff_subsingleton_tensor_coker
    {R : Type*} [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) :
    Function.Surjective (g.baseChange A) ↔
      Subsingleton (A ⊗[R] (N ⧸ LinearMap.range g)) := by
  have hcoe : ⇑(g.baseChange A) = ⇑(g.lTensor A) := g.baseChange_eq_ltensor
  have hex : Function.Exact (g.lTensor A) ((LinearMap.range g).mkQ.lTensor A) :=
    lTensor_exact A (LinearMap.exact_map_mkQ_range g) (Submodule.mkQ_surjective _)
  have hsurj : Function.Surjective ((LinearMap.range g).mkQ.lTensor A) :=
    LinearMap.lTensor_surjective A (Submodule.mkQ_surjective _)
  rw [show Function.Surjective ⇑(g.baseChange A) ↔ Function.Surjective ⇑(g.lTensor A) from
    iff_of_eq (congrArg _ hcoe)]
  constructor
  · intro h
    refine subsingleton_iff_forall_eq 0 |>.mpr fun y ↦ ?_
    obtain ⟨x, rfl⟩ := hsurj y
    obtain ⟨m, hm⟩ := h x
    rw [← hm, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    simp [LinearMap.range_mkQ_comp]
  · intro h y
    have h0 : ((LinearMap.range g).mkQ.lTensor A) y = 0 := Subsingleton.elim _ _
    exact (hex y).mp h0

/-- A linear map into a finite module is surjective after localization at a prime
exactly when it is surjective after base change to the residue field at that prime. -/
theorem LinearMap.surjective_localizedMap_iff_surjective_baseChange_residueField
    {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (g : M →ₗ[R] N) (p : PrimeSpectrum R) :
    Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl g) ↔
      Function.Surjective (g.baseChange p.asIdeal.ResidueField) := by
  rw [LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker,
      LinearMap.baseChange_surjective_iff_subsingleton_tensor_coker,
      ← not_nontrivial_iff_subsingleton, ← not_nontrivial_iff_subsingleton,
      show Nontrivial (LocalizedModule p.asIdeal.primeCompl (N ⧸ LinearMap.range g)) ↔
        p ∈ Module.support R (N ⧸ LinearMap.range g) from (Module.mem_support_iff).symm,
      show (p ∈ Module.support R (N ⧸ LinearMap.range g)) ↔
        Nontrivial (p.asIdeal.ResidueField ⊗[R] (N ⧸ LinearMap.range g)) from
      Module.mem_support_iff_nontrivial_residueField_tensorProduct p]
