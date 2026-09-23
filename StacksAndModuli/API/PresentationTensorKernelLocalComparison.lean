module

public import StacksAndModuli.API.PresentationTensorKernelChangeOfRings

/-!
# The two-step presentation-kernel comparison

Suppose a presentation over `R` is first reduced to an `R`-algebra `A` and then compared over
a common algebra `C` with the base-changed presentation over another `R`-algebra `R'`.  This
file composes the presentation-kernel forms of Stacks Project tags 00MM and 00MN:

`C ⊗[A] presentationTensorKernel q A → presentationTensorKernel (q.baseChange R') C`.

When `A ⊗[R] M` is flat over `A`, this comparison is surjective.  In the local flatness
argument of tag 00MO, `A` and `C` are the appropriate residue rings.  Relating this
presentation-level map to multiplication kernels is handled by
`Ideal.idealKernelPresentationTorEquiv`.
-/

@[expose] public section

open TensorProduct Function

universe u v w

namespace LinearMap

/-- The two-step map obtained by base-changing a presentation kernel and then changing the
presentation ring. -/
noncomputable def presentationTensorKernelLocalComparison
    {R : Type u} {F M : Type v} [CommRing R]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (A R' C : Type u)
    [CommRing A] [CommRing R'] [CommRing C]
    [Algebra R A] [Algebra R R'] [Algebra R C]
    [Algebra A C] [Algebra R' C]
    [IsScalarTower R A C] [IsScalarTower R R' C] :
    C ⊗[A] presentationTensorKernel q A →ₗ[C]
      presentationTensorKernel (q.baseChange R') C :=
  (presentationTensorKernelToBaseChangedMap q R' C).comp
    (presentationTensorKernelBaseChangeMap q A C)

/-- If the reduced presented module is flat, the two-step presentation-kernel comparison is
surjective.  This is the presentation form of the comparison used in tag 00MO. -/
theorem presentationTensorKernelLocalComparison_surjective
    {R A R' C : Type u} {F M : Type v}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing C]
    [Algebra R A] [Algebra R R'] [Algebra R C]
    [Algebra A C] [Algebra R' C]
    [IsScalarTower R A C] [IsScalarTower R R' C]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (hq : Function.Surjective q)
    [Module.Flat A (A ⊗[R] M)] :
    Function.Surjective (presentationTensorKernelLocalComparison q A R' C) :=
  (presentationTensorKernelToBaseChangedMap_surjective q hq).comp
    (presentationTensorKernelBaseChangeMap_surjective q hq)

/-- Apply the two-step comparison to the pure tensors associated to an arbitrary additive
set of generators for the initial presentation kernel. -/
noncomputable def presentationTensorKernelLocalComparisonOnGenerators
    {R : Type u} {F M : Type v} {K : Type w} [CommRing R]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    [AddCommGroup K]
    (q : F →ₗ[R] M) (A R' C : Type u)
    [CommRing A] [CommRing R'] [CommRing C]
    [Algebra R A] [Algebra R R'] [Algebra R C]
    [Algebra A C] [Algebra R' C]
    [IsScalarTower R A C] [IsScalarTower R R' C]
    (e : K ≃+ presentationTensorKernel q A) :
    K →+ presentationTensorKernel (q.baseChange R') C :=
  (presentationTensorKernelLocalComparison q A R' C).toAddMonoidHom.comp
    ((TensorProduct.mk A C (presentationTensorKernel q A) 1).toAddMonoidHom.comp
      e.toAddMonoidHom)

/-- If the comparison is surjective, its values on pure tensors coming from any additive
model of the initial presentation kernel span the target.  This is the precise spanning
consequence of the 00MM--00MN comparison used in the finite-obstruction proof of tag 00R6. -/
theorem span_range_presentationTensorKernelLocalComparisonOnGenerators
    {R A R' C : Type u} {F M : Type v} {K : Type w}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing C]
    [Algebra R A] [Algebra R R'] [Algebra R C]
    [Algebra A C] [Algebra R' C]
    [IsScalarTower R A C] [IsScalarTower R R' C]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    [AddCommGroup K]
    (q : F →ₗ[R] M) (hq : Function.Surjective q)
    [Module.Flat A (A ⊗[R] M)]
    (e : K ≃+ presentationTensorKernel q A) :
    Submodule.span C (Set.range
      (presentationTensorKernelLocalComparisonOnGenerators q A R' C e)) = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨z, rfl⟩ :=
    (presentationTensorKernelLocalComparison_surjective
      (A := A) (R' := R') (C := C) q hq) y
  induction z using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero]
      exact Submodule.zero_mem _
  | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ (hx trivial) (hy trivial)
  | tmul c p =>
      have hgen : presentationTensorKernelLocalComparison q A R' C (1 ⊗ₜ[A] p) ∈
          Submodule.span C (Set.range
            (presentationTensorKernelLocalComparisonOnGenerators q A R' C e)) := by
        apply Submodule.subset_span
        refine ⟨e.symm p, ?_⟩
        simp [presentationTensorKernelLocalComparisonOnGenerators]
      have htmul : c ⊗ₜ[A] p = c • (1 ⊗ₜ[A] p) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [htmul, map_smul]
      exact Submodule.smul_mem _ c hgen

end LinearMap
