module

public import StacksAndModuli.API.IdealTensorKernelLocalComparison

/-!
# Element formula for the ideal-tensor connecting map

The presentation model for an ideal-multiplication kernel is built from the module snake
lemma.  This file records its elementwise formula: after lifting a tensor relation through
a chosen free presentation, the connecting map is the residue class of the resulting
relation vector.  The formula is the naturality input needed to compare the presentation
construction with canonical tensor base change in the local approximation argument.
-/

@[expose] public section

open TensorProduct Function LinearMap

universe u v

namespace Ideal

variable {R : Type u} {F M : Type v} [CommRing R]
variable [AddCommGroup F] [Module R F]
variable [AddCommGroup M] [Module R M]

/-- Element formula for the snake-lemma connecting map used in the presentation of an
ideal-tensor kernel. -/
theorem idealKernelConnecting_eq_oneTensor_of_lifts
    (q : F →ₗ[R] M) (hq : Function.Surjective q) (I : Ideal R)
    (x : LinearMap.ker (leftTensorMul (M := M) I))
    (y : I ⊗[R] F)
    (hy : q.lTensor I y = x.1)
    (z : LinearMap.ker q)
    (hz : z.1 = leftTensorMul (M := F) I y) :
    idealKernelConnecting q hq I x = 1 ⊗ₜ[R] z := by
  let K := LinearMap.ker q
  let f₁ : I ⊗[R] K →ₗ[R] I ⊗[R] F := K.subtype.lTensor I
  let f₂ : I ⊗[R] F →ₗ[R] I ⊗[R] M := q.lTensor I
  let g₁ : K →ₗ[R] F := K.subtype
  let g₂ : F →ₗ[R] M := q
  let i₁ : I ⊗[R] K →ₗ[R] K := leftTensorMul I
  let i₂ : I ⊗[R] F →ₗ[R] F := leftTensorMul I
  let i₃ : I ⊗[R] M →ₗ[R] M := leftTensorMul I
  let π₁ : K →ₗ[R] (R ⧸ I) ⊗[R] K := oneTensorQuotient I
  have hf : Function.Exact f₁ f₂ :=
    lTensor_exact I (LinearMap.exact_subtype_ker_map q) hq
  have hg : Function.Exact g₁ g₂ := LinearMap.exact_subtype_ker_map q
  have h₁ : g₁.comp i₁ = i₂.comp f₁ := by
    ext a b
    simp [f₁, g₁, i₁, i₂, leftTensorMul]
  have h₂ : g₂.comp i₂ = i₃.comp f₂ := by
    ext a b
    simp [f₂, g₂, i₂, i₃, leftTensorMul]
  have hformula := SnakeLemma.δ'_eq i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂
    (LinearMap.ker i₃).subtype (LinearMap.exact_subtype_ker_map i₃)
    π₁ (exact_leftTensorMul_oneTensorQuotient I)
    (LinearMap.lTensor_surjective I hq) K.subtype_injective
    x y hy z (by simpa [g₁, i₂] using hz)
  simpa [idealKernelConnecting, K, f₁, f₂, g₁, g₂, i₁, i₂, i₃, π₁,
    oneTensorQuotient] using hformula

end Ideal

namespace LinearMap

/-- On a pure tensor coming from a presentation kernel, the kernel base-change map is the
canonical pure tensor in the total scalar extension. -/
@[simp]
theorem presentationTensorKernelBaseChangeMap_one_tmul_val
    {R A B : Type u} {F M : Type v}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (x : presentationTensorKernel q A)
    (z : LinearMap.ker q) (hx : x.1 = (1 : A) ⊗ₜ[R] z) :
    ((presentationTensorKernelBaseChangeMap q A B)
        ((1 : B) ⊗ₜ[A] x)).1 =
      (1 : B) ⊗ₜ[R] z := by
  simp [presentationTensorKernelBaseChangeMap, hx]

/-- On a pure tensor, changing the presentation ring sends the relation vector by the
canonical kernel base-change map. -/
@[simp]
theorem presentationTensorKernelToBaseChangedMap_one_tmul_val
    {R R' C : Type u} {F M : Type v}
    [CommRing R] [CommRing R'] [CommRing C]
    [Algebra R R'] [Algebra R C] [Algebra R' C] [IsScalarTower R R' C]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (z : LinearMap.ker q)
    (hz : ((LinearMap.ker q).subtype.baseChange C)
      ((1 : C) ⊗ₜ[R] z) = 0) :
    ((presentationTensorKernelToBaseChangedMap q R' C)
        ⟨(1 : C) ⊗ₜ[R] z, hz⟩).1 =
      (1 : C) ⊗ₜ[R'] q.kerBaseChangeHom R' ((1 : R') ⊗ₜ[R] z) := by
  simp [presentationTensorKernelToBaseChangedMap]

/-- The two-step local presentation comparison has the expected value on a pure tensor
represented by a single relation vector. -/
@[simp]
theorem presentationTensorKernelLocalComparison_one_tmul_val
    {R A R' C : Type u} {F M : Type v}
    [CommRing R] [CommRing A] [CommRing R'] [CommRing C]
    [Algebra R A] [Algebra R R'] [Algebra R C]
    [Algebra A C] [Algebra R' C]
    [IsScalarTower R A C] [IsScalarTower R R' C]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (x : presentationTensorKernel q A)
    (z : LinearMap.ker q) (hx : x.1 = (1 : A) ⊗ₜ[R] z) :
    (presentationTensorKernelLocalComparison q A R' C
        ((1 : C) ⊗ₜ[A] x)).1 =
      (1 : C) ⊗ₜ[R'] q.kerBaseChangeHom R' ((1 : R') ⊗ₜ[R] z) := by
  let y : presentationTensorKernel q C :=
    presentationTensorKernelBaseChangeMap q A C ((1 : C) ⊗ₜ[A] x)
  have hyval : y.1 = (1 : C) ⊗ₜ[R] z :=
    presentationTensorKernelBaseChangeMap_one_tmul_val q x z hx
  have hzC : ((LinearMap.ker q).subtype.baseChange C)
      ((1 : C) ⊗ₜ[R] z) = 0 := by
    rw [← hyval]
    exact y.2
  have hy : y = ⟨(1 : C) ⊗ₜ[R] z, hzC⟩ := Subtype.ext hyval
  change (presentationTensorKernelToBaseChangedMap q R' C y).1 = _
  rw [hy]
  exact presentationTensorKernelToBaseChangedMap_one_tmul_val q z hzC

end LinearMap

namespace Ideal

variable {R : Type u} {F M : Type v} [CommRing R]
variable [AddCommGroup F] [Module R F] [Module.Flat R F]
variable [AddCommGroup M] [Module R M]

/-- Element formula for the equivalence from an ideal-multiplication kernel to its
base-change presentation kernel. -/
theorem tensorMulKerPresentationBaseChangeLinearEquiv_val_of_lifts
    (q : F →ₗ[R] M) (hq : Function.Surjective q) (I : Ideal R)
    (x : LinearMap.ker (tensorMul (R := R) (S := R) (M := M) I))
    (y : I ⊗[R] F)
    (hy : q.lTensor I y = (tensorMulKerEquivLeft I x).1)
    (z : LinearMap.ker q)
    (hz : z.1 = leftTensorMul (M := F) I y) :
    (tensorMulKerPresentationBaseChangeLinearEquiv q hq I x).1 =
      (1 : R ⧸ I) ⊗ₜ[R] z := by
  have hconnect := idealKernelConnecting_eq_oneTensor_of_lifts
    q hq I (tensorMulKerEquivLeft I x) y hy z hz
  exact hconnect

/-- Under the target presentation equivalence, the 00MO local comparison is the pure
tensor of the base-changed relation vector. -/
theorem tensorMulKerLocalComparison_presentation_val_of_lifts
    {R' : Type u} [CommRing R'] [Algebra R R']
    (q : F →ₗ[R] M) (hq : Function.Surjective q)
    (I : Ideal R) (J : Ideal R')
    (hIJ : I ≤ J.comap (algebraMap R R'))
    (x : LinearMap.ker (tensorMul (R := R) (S := R) (M := M) I))
    (y : I ⊗[R] F)
    (hy : q.lTensor I y = (tensorMulKerEquivLeft I x).1)
    (z : LinearMap.ker q)
    (hz : z.1 = leftTensorMul (M := F) I y) :
    let q' := q.baseChange R'
    let hq' : Function.Surjective q' := LinearMap.lTensor_surjective R' hq
    (tensorMulKerPresentationBaseChangeLinearEquiv q' hq' J
      (tensorMulKerLocalComparison q hq I J hIJ x)).1 =
        (1 : R' ⧸ J) ⊗ₜ[R']
          q.kerBaseChangeHom R' ((1 : R') ⊗ₜ[R] z) := by
  let _ : Algebra (R ⧸ I) (R' ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap hIJ
  letI : IsScalarTower R R' (R' ⧸ J) := inferInstance
  letI : IsScalarTower R (R ⧸ I) (R' ⧸ J) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext a
      change Ideal.Quotient.mk J (algebraMap R R' a) =
        Ideal.quotientMap J (algebraMap R R') hIJ (Ideal.Quotient.mk I a)
      rw [Ideal.quotientMap_mk])
  let q' := q.baseChange R'
  let hq' : Function.Surjective q' := LinearMap.lTensor_surjective R' hq
  let e := tensorMulKerPresentationBaseChangeLinearEquiv q hq I
  let e' := tensorMulKerPresentationBaseChangeLinearEquiv q' hq' J
  have heval : (e x).1 = (1 : R ⧸ I) ⊗ₜ[R] z :=
    tensorMulKerPresentationBaseChangeLinearEquiv_val_of_lifts
      q hq I x y hy z hz
  change (e' (e'.symm
    (LinearMap.presentationTensorKernelLocalComparison q (R ⧸ I) R' (R' ⧸ J)
      ((1 : R' ⧸ J) ⊗ₜ[R ⧸ I] e x)))).1 = _
  rw [e'.apply_symm_apply]
  exact LinearMap.presentationTensorKernelLocalComparison_one_tmul_val
    q (e x) z heval

end Ideal
