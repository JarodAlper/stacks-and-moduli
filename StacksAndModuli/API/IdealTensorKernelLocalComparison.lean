module

public import StacksAndModuli.API.PresentationTensorKernelLocalComparison
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The local comparison on ideal-tensor kernels

This file transports the presentation-kernel form of the 00MM--00MN comparison back to the
actual kernels of ideal multiplication.  Given `R → R'`, ideals `I ⊆ R` and `J ⊆ R'` with
`I` mapping into `J`, and a flat presentation module `F → M`, it constructs an additive map

`ker (M ⊗ I → M) → ker ((R' ⊗ M) ⊗ J → R' ⊗ M)`.

If `(R/I) ⊗ M` is flat over `R/I`, the image of this map spans the target over `R'`.  This is
the ideal-multiplication-kernel form of the local comparison in Stacks Project tag 00MO and
the `hspan` input required in the finite-obstruction argument of tag 00R6.

The comparison is constructed through the snake-lemma presentation equivalences; it is not
asserted here to be definitionally equal to `Ideal.tensorMulKerMap`.
-/

@[expose] public section

open TensorProduct Function LinearMap

universe u v

namespace Ideal

/-- Forgetting the auxiliary algebra action does not change the underlying kernel of ideal
multiplication. -/
noncomputable def tensorMulKerForgetAlgebraEquiv
    {R S : Type u} {M : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (I : Ideal R) :
    LinearMap.ker (tensorMul (R := R) (S := S) (M := M) I) ≃+
      LinearMap.ker (tensorMul (R := R) (S := R) (M := M) I) where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The actual ideal-multiplication kernel is additively equivalent to its presentation
model. -/
noncomputable def tensorMulKerPresentationEquiv
    {R S : Type u} {F M : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup F] [Module R F] [Module.Flat R F]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (q : F →ₗ[R] M) (hq : Function.Surjective q) (I : Ideal R) :
    LinearMap.ker (tensorMul (R := R) (S := S) (M := M) I) ≃+
      presentationTorOne q I :=
  (tensorMulKerForgetAlgebraEquiv I).trans
    ((tensorMulKerEquivLeft I).toAddEquiv.trans
      (idealKernelPresentationTorEquiv q hq I).toAddEquiv)

/-- The `lTensor` and `baseChange` presentations define linearly equivalent kernels after
restriction of scalars. -/
noncomputable def presentationTorOneBaseChangeLinearEquiv
    {R : Type u} {F M : Type v} [CommRing R]
    [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (I : Ideal R) :
    presentationTorOne q I ≃ₗ[R]
      LinearMap.presentationTensorKernel q (R ⧸ I) where
  toFun x := ⟨x.1, by
    change ((LinearMap.ker q).subtype.baseChange (R ⧸ I)) x.1 = 0
    rw [LinearMap.baseChange_eq_ltensor]
    exact x.2⟩
  invFun x := ⟨x.1, by
    change ((LinearMap.ker q).subtype.lTensor (R ⧸ I)) x.1 = 0
    rw [← LinearMap.baseChange_eq_ltensor]
    exact x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The ideal-multiplication kernel and the scalar-extension presentation kernel are linearly
equivalent. -/
noncomputable def tensorMulKerPresentationBaseChangeLinearEquiv
    {R : Type u} {F M : Type v} [CommRing R]
    [AddCommGroup F] [Module R F] [Module.Flat R F]
    [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (hq : Function.Surjective q) (I : Ideal R) :
    LinearMap.ker (tensorMul (R := R) (S := R) (M := M) I) ≃ₗ[R]
      LinearMap.presentationTensorKernel q (R ⧸ I) :=
  ((tensorMulKerEquivLeft I).trans
    (idealKernelPresentationTorEquiv q hq I)).trans
      (presentationTorOneBaseChangeLinearEquiv q I)

/-- The 00MO comparison map on actual ideal-multiplication kernels, constructed through a
flat presentation. -/
noncomputable def tensorMulKerLocalComparison
    {R R' : Type u} {F M : Type v} [CommRing R] [CommRing R']
    [Algebra R R']
    [AddCommGroup F] [Module R F] [Module.Flat R F]
    [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (hq : Function.Surjective q)
    (I : Ideal R) (J : Ideal R')
    (hIJ : I ≤ J.comap (algebraMap R R')) :
    LinearMap.ker (tensorMul (R := R) (S := R) (M := M) I) →+
      LinearMap.ker (tensorMul (R := R') (S := R')
        (M := R' ⊗[R] M) J) := by
  let _ : Algebra (R ⧸ I) (R' ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap hIJ
  letI : IsScalarTower R R' (R' ⧸ J) := inferInstance
  letI : IsScalarTower R (R ⧸ I) (R' ⧸ J) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change Ideal.Quotient.mk J (algebraMap R R' x) =
        Ideal.quotientMap J (algebraMap R R') hIJ (Ideal.Quotient.mk I x)
      rw [Ideal.quotientMap_mk])
  let q' := q.baseChange R'
  let hq' : Function.Surjective q' := LinearMap.lTensor_surjective R' hq
  let e := tensorMulKerPresentationBaseChangeLinearEquiv q hq I
  let e' := tensorMulKerPresentationBaseChangeLinearEquiv q' hq' J
  let one : LinearMap.presentationTensorKernel q (R ⧸ I) →+
      (R' ⧸ J) ⊗[R ⧸ I] LinearMap.presentationTensorKernel q (R ⧸ I) :=
    (TensorProduct.mk (R ⧸ I) (R' ⧸ J)
      (LinearMap.presentationTensorKernel q (R ⧸ I)) 1).toAddMonoidHom
  exact e'.symm.toAddEquiv.toAddMonoidHom.comp
    ((LinearMap.presentationTensorKernelLocalComparison
      (R := R) (F := F) (M := M) q (R ⧸ I) R' (R' ⧸ J)).toAddMonoidHom.comp
      (one.comp e.toAddEquiv.toAddMonoidHom))

/-- Under the flatness hypothesis of 00MO, the comparison from the initial ideal-tensor
kernel spans the target kernel after change of rings. -/
theorem span_range_tensorMulKerLocalComparison
    {R R' : Type u} {F M : Type v} [CommRing R] [CommRing R']
    [Algebra R R']
    [AddCommGroup F] [Module R F] [Module.Flat R F]
    [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (hq : Function.Surjective q)
    (I : Ideal R) (J : Ideal R')
    (hIJ : I ≤ J.comap (algebraMap R R'))
    [Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] M)] :
    Submodule.span R' (Set.range
      (tensorMulKerLocalComparison q hq I J hIJ)) = ⊤ := by
  let _ : Algebra (R ⧸ I) (R' ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap hIJ
  let _ : IsScalarTower R R' (R' ⧸ J) := inferInstance
  let _ : IsScalarTower R (R ⧸ I) (R' ⧸ J) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change Ideal.Quotient.mk J (algebraMap R R' x) =
        Ideal.quotientMap J (algebraMap R R') hIJ (Ideal.Quotient.mk I x)
      rw [Ideal.quotientMap_mk])
  let q' := q.baseChange R'
  let hq' : Function.Surjective q' := LinearMap.lTensor_surjective R' hq
  let e := tensorMulKerPresentationBaseChangeLinearEquiv q hq I
  let e' := tensorMulKerPresentationBaseChangeLinearEquiv q' hq' J
  let g := LinearMap.presentationTensorKernelLocalComparisonOnGenerators
    q (R ⧸ I) R' (R' ⧸ J) e.toAddEquiv
  have hC : Submodule.span (R' ⧸ J) (Set.range g) = ⊤ :=
    LinearMap.span_range_presentationTensorKernelLocalComparisonOnGenerators
      q hq e.toAddEquiv
  have hR : Submodule.span R' (Set.range g) = ⊤ := by
    apply top_unique
    intro y _
    have hy : y ∈ Submodule.span (R' ⧸ J) (Set.range g) := by
      rw [hC]
      exact Submodule.mem_top
    refine Submodule.span_induction
      (p := fun z _ ↦ z ∈ Submodule.span R' (Set.range g)) ?_ ?_ ?_ ?_ hy
    · exact fun z hz ↦ Submodule.subset_span hz
    · exact Submodule.zero_mem _
    · exact fun _ _ _ _ hx hy ↦ Submodule.add_mem _ hx hy
    · intro c x _ hx
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
      change algebraMap R' (R' ⧸ J) r • x ∈ Submodule.span R' (Set.range g)
      rw [IsScalarTower.algebraMap_smul (R' ⧸ J)]
      exact Submodule.smul_mem _ r hx
  change Submodule.span R' (Set.range
    (e'.symm.toAddEquiv.toAddMonoidHom.comp g)) = ⊤
  apply top_unique
  intro y _
  have hy : e' y ∈ Submodule.span R' (Set.range g) := by
    rw [hR]
    exact Submodule.mem_top
  have hy' : e'.symm (e' y) ∈ Submodule.span R' (Set.range
      (e'.symm.toAddEquiv.toAddMonoidHom.comp g)) := by
    refine Submodule.span_induction
      (p := fun z _ ↦ e'.symm z ∈ Submodule.span R' (Set.range
        (e'.symm.toAddEquiv.toAddMonoidHom.comp g))) ?_ ?_ ?_ ?_ hy
    · rintro z ⟨x, rfl⟩
      exact Submodule.subset_span ⟨x, rfl⟩
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      simpa only [map_add] using Submodule.add_mem _ hx hy
    · intro r x _ hx
      simpa only [map_smul] using Submodule.smul_mem _ r hx
  simpa using hy'

end Ideal
