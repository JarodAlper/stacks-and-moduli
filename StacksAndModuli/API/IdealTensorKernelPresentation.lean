module

public import StacksAndModuli.API.NoetherianTorKernelFinite
public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Presentation model for ideal-tensor kernels

Given a surjection `F → M` from a flat module, the kernel of ideal multiplication
`I ⊗ M → M` is naturally linearly equivalent to the presentation kernel
`ker ((R/I) ⊗ ker(F → M) → (R/I) ⊗ F)`.  The construction is the connecting map
in the snake lemma applied to the multiplication/quotient diagram.

This elementary model is the bridge used to formalize the `Tor₁` comparison lemmas in the
local flat-approximation argument of Stacks Project tags 00MM, 00MN, and 00R6.  It avoids a
dependency on a general derived-functor definition of `Tor`.
-/

@[expose] public section

open TensorProduct Function LinearMap

universe u v

namespace Ideal

variable {R : Type u} {M : Type v} [CommRing R]
variable [AddCommGroup M] [Module R M]

/-- Ideal multiplication with the ideal in the left tensor factor. -/
def leftTensorMul (I : Ideal R) : I ⊗[R] M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap.comp (I.subtype.rTensor M)

@[simp]
theorem leftTensorMul_tmul (I : Ideal R) (i : I) (m : M) :
    leftTensorMul (M := M) I (i ⊗ₜ[R] m) = (i : R) • m := by
  simp [leftTensorMul]

/-- The canonical map from a module to its scalar extension to `R/I`. -/
def oneTensorQuotient (I : Ideal R) : M →ₗ[R] (R ⧸ I) ⊗[R] M :=
  TensorProduct.mk R (R ⧸ I) M 1

@[simp]
theorem oneTensorQuotient_apply (I : Ideal R) (m : M) :
    oneTensorQuotient (M := M) I m = 1 ⊗ₜ[R] m := rfl

/-- Quotient scalar extension, written on `R ⊗ M`, agrees with `oneTensorQuotient`
after the left unitor. -/
theorem quotient_rTensor_eq_oneTensor_lid (I : Ideal R) (z : R ⊗[R] M) :
    ((Ideal.Quotient.mkₐ R I).toLinearMap.rTensor M) z =
      oneTensorQuotient (M := M) I ((TensorProduct.lid R M) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r m =>
    rw [LinearMap.rTensor_tmul, TensorProduct.lid_tmul]
    simp only [oneTensorQuotient_apply]
    rw [← TensorProduct.smul_tmul]
    congr 1
    simp [Algebra.smul_def]

/-- Because `R → R/I` is surjective, every tensor over `R/I` is a one-tensor. -/
theorem oneTensorQuotient_surjective (I : Ideal R) :
    Function.Surjective (oneTensorQuotient (M := M) I) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, TensorProduct.tmul_add 1 a b⟩
  | tmul a m =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨r • m, ?_⟩
    simp only [oneTensorQuotient_apply]
    rw [← TensorProduct.smul_tmul]
    congr 1
    simp [Algebra.smul_def]

/-- Ideal multiplication followed by passage to `R/I` is an exact pair. -/
theorem exact_leftTensorMul_oneTensorQuotient (I : Ideal R) :
    Function.Exact (leftTensorMul (M := M) I) (oneTensorQuotient (M := M) I) := by
  let q : R →ₗ[R] R ⧸ I := (Ideal.Quotient.mkₐ R I).toLinearMap
  have hq : Function.Exact I.subtype q := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
    ext x
    simp [q, LinearMap.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hqsurj : Function.Surjective q := Ideal.Quotient.mkₐ_surjective R I
  have htex := rTensor_exact M hq hqsurj
  intro x
  constructor
  · intro hx
    let y : R ⊗[R] M := (TensorProduct.lid R M).symm x
    have hy : (q.rTensor M) y = 0 := by
      change q.rTensor M ((TensorProduct.lid R M).symm x) = 0
      simpa [oneTensorQuotient, q] using hx
    obtain ⟨z, hz⟩ := (htex y).mp hy
    refine ⟨z, ?_⟩
    simp [leftTensorMul, y, hz]
  · rintro ⟨z, rfl⟩
    have hz := htex.apply_apply_eq_zero z
    rw [quotient_rTensor_eq_oneTensor_lid] at hz
    exact hz

/-- The kernel model for `Tor₁(R/I, M)` associated to a surjection onto `M`. -/
abbrev presentationTorOne {F : Type v} [AddCommGroup F] [Module R F]
    (q : F →ₗ[R] M) (I : Ideal R) :=
  LinearMap.ker ((LinearMap.ker q).subtype.lTensor (R ⧸ I))

/-- The snake-lemma connecting map from the ideal-tensor kernel to the presentation
model for `Tor₁`. -/
noncomputable def idealKernelConnecting
    {F : Type v} [AddCommGroup F] [Module R F]
    (q : F →ₗ[R] M) (hq : Function.Surjective q) (I : Ideal R) :
    LinearMap.ker (leftTensorMul (M := M) I) →ₗ[R]
      (R ⧸ I) ⊗[R] LinearMap.ker q := by
  let K := LinearMap.ker q
  let f₁ : I ⊗[R] K →ₗ[R] I ⊗[R] F := K.subtype.lTensor I
  let f₂ : I ⊗[R] F →ₗ[R] I ⊗[R] M := q.lTensor I
  let g₁ : K →ₗ[R] F := K.subtype
  let g₂ : F →ₗ[R] M := q
  let i₁ : I ⊗[R] K →ₗ[R] K := leftTensorMul I
  let i₂ : I ⊗[R] F →ₗ[R] F := leftTensorMul I
  let i₃ : I ⊗[R] M →ₗ[R] M := leftTensorMul I
  let π₁ : K →ₗ[R] (R ⧸ I) ⊗[R] K := oneTensorQuotient I
  have hf : Function.Exact f₁ f₂ := by
    exact lTensor_exact I (LinearMap.exact_subtype_ker_map q) hq
  have hg : Function.Exact g₁ g₂ := LinearMap.exact_subtype_ker_map q
  have h₁ : g₁.comp i₁ = i₂.comp f₁ := by
    ext x y
    simp [f₁, g₁, i₁, i₂, leftTensorMul]
  have h₂ : g₂.comp i₂ = i₃.comp f₂ := by
    ext x y
    simp [f₂, g₂, i₂, i₃, leftTensorMul]
  exact SnakeLemma.δ' (K₃ := LinearMap.ker i₃)
    (C₁ := (R ⧸ I) ⊗[R] K) i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂
    (LinearMap.ker i₃).subtype (LinearMap.exact_subtype_ker_map i₃)
    π₁ (exact_leftTensorMul_oneTensorQuotient I)
    (LinearMap.lTensor_surjective I hq) K.subtype_injective

/-- Exactness of the connecting map at the presentation kernel. -/
theorem exact_idealKernelConnecting
    {F : Type v} [AddCommGroup F] [Module R F]
    (q : F →ₗ[R] M) (hq : Function.Surjective q) (I : Ideal R) :
    Function.Exact (idealKernelConnecting q hq I)
      ((LinearMap.ker q).subtype.lTensor (R ⧸ I)) := by
  let K := LinearMap.ker q
  let f₁ : I ⊗[R] K →ₗ[R] I ⊗[R] F := K.subtype.lTensor I
  let f₂ : I ⊗[R] F →ₗ[R] I ⊗[R] M := q.lTensor I
  let g₁ : K →ₗ[R] F := K.subtype
  let g₂ : F →ₗ[R] M := q
  let i₁ : I ⊗[R] K →ₗ[R] K := leftTensorMul I
  let i₂ : I ⊗[R] F →ₗ[R] F := leftTensorMul I
  let i₃ : I ⊗[R] M →ₗ[R] M := leftTensorMul I
  let π₁ : K →ₗ[R] (R ⧸ I) ⊗[R] K := oneTensorQuotient I
  let π₂ : F →ₗ[R] (R ⧸ I) ⊗[R] F := oneTensorQuotient I
  let G : (R ⧸ I) ⊗[R] K →ₗ[R] (R ⧸ I) ⊗[R] F :=
    K.subtype.lTensor (R ⧸ I)
  have hf : Function.Exact f₁ f₂ :=
    lTensor_exact I (LinearMap.exact_subtype_ker_map q) hq
  have hg : Function.Exact g₁ g₂ := LinearMap.exact_subtype_ker_map q
  have h₁ : g₁.comp i₁ = i₂.comp f₁ := by
    ext a b
    simp [f₁, g₁, i₁, i₂, leftTensorMul]
  have h₂ : g₂.comp i₂ = i₃.comp f₂ := by
    ext a b
    simp [f₂, g₂, i₂, i₃, leftTensorMul]
  have hπ : G.comp π₁ = π₂.comp g₁ := by
    ext z
    simp [G, π₁, π₂, g₁, oneTensorQuotient]
  have hex := SnakeLemma.exact_δ'_left (K₃ := LinearMap.ker i₃)
    (C₁ := (R ⧸ I) ⊗[R] K) (C₂ := (R ⧸ I) ⊗[R] F)
    i₁ i₂ i₃ f₁ f₂ hf
    g₁ g₂ hg h₁ h₂ (LinearMap.ker i₃).subtype
    (LinearMap.exact_subtype_ker_map i₃) π₁
    (exact_leftTensorMul_oneTensorQuotient I) π₂
    (exact_leftTensorMul_oneTensorQuotient I)
    (LinearMap.lTensor_surjective I hq) K.subtype_injective G hπ
    (oneTensorQuotient_surjective I)
  simpa [idealKernelConnecting, K, f₁, f₂, g₁, g₂, i₁, i₂, i₃, π₁]
    using hex

theorem idealKernelConnecting_mem_presentationTorOne
    {F : Type v} [AddCommGroup F] [Module R F]
    (q : F →ₗ[R] M) (hq : Function.Surjective q) (I : Ideal R)
    (x : LinearMap.ker (leftTensorMul (M := M) I)) :
    idealKernelConnecting q hq I x ∈ presentationTorOne q I :=
  (exact_idealKernelConnecting q hq I).apply_apply_eq_zero x

/-- The connecting map with codomain restricted to the presentation kernel. -/
noncomputable def idealKernelPresentationTorMap
    {F : Type v} [AddCommGroup F] [Module R F]
    (q : F →ₗ[R] M) (hq : Function.Surjective q) (I : Ideal R) :
    LinearMap.ker (leftTensorMul (M := M) I) →ₗ[R] presentationTorOne q I :=
  (idealKernelConnecting q hq I).codRestrict _
    (idealKernelConnecting_mem_presentationTorOne q hq I)

theorem idealKernelPresentationTorMap_surjective
    {F : Type v} [AddCommGroup F] [Module R F]
    (q : F →ₗ[R] M) (hq : Function.Surjective q) (I : Ideal R) :
    Function.Surjective (idealKernelPresentationTorMap q hq I) := by
  intro y
  obtain ⟨x, hx⟩ := (exact_idealKernelConnecting q hq I y.1).mp y.2
  refine ⟨x, Subtype.ext ?_⟩
  exact hx

/-- If the presentation module is flat, the connecting map is injective. -/
theorem idealKernelConnecting_injective
    {F : Type v} [AddCommGroup F] [Module R F] [Module.Flat R F]
    (q : F →ₗ[R] M) (hq : Function.Surjective q) (I : Ideal R) :
    Function.Injective (idealKernelConnecting q hq I) := by
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
  let Fker : LinearMap.ker i₂ →ₗ[R] LinearMap.ker i₃ :=
    { toFun := fun y => ⟨f₂ y.1, by
        change i₃ (f₂ y.1) = 0
        rw [← LinearMap.comp_apply, ← h₂, LinearMap.comp_apply, y.2, map_zero]⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro r x; ext; simp }
  have hFker : f₂.comp (LinearMap.ker i₂).subtype =
      (LinearMap.ker i₃).subtype.comp Fker := by
    ext y
    rfl
  have hex := SnakeLemma.exact_δ'_right
    (K₂ := LinearMap.ker i₂) (K₃ := LinearMap.ker i₃)
    (C₁ := (R ⧸ I) ⊗[R] K) i₁ i₂ i₃ f₁ f₂ hf
    g₁ g₂ hg h₁ h₂ (LinearMap.ker i₂).subtype
    (LinearMap.exact_subtype_ker_map i₂) (LinearMap.ker i₃).subtype
    (LinearMap.exact_subtype_ker_map i₃) π₁
    (exact_leftTensorMul_oneTensorQuotient I)
    (LinearMap.lTensor_surjective I hq) K.subtype_injective Fker hFker
    (LinearMap.ker i₃).subtype_injective
  have hi₂ : Function.Injective i₂ := by
    intro x y hxy
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := F)
      I.subtype I.subtype_injective
    apply (TensorProduct.lid R F).injective
    exact hxy
  intro x y hxy
  rw [← sub_eq_zero]
  have hzero : idealKernelConnecting q hq I (x - y) = 0 := by
    calc
      idealKernelConnecting q hq I (x - y) =
          idealKernelConnecting q hq I x - idealKernelConnecting q hq I y :=
        (idealKernelConnecting q hq I).map_sub x y
      _ = 0 := sub_eq_zero.mpr hxy
  have hzero' :
      (SnakeLemma.δ' i₁ i₂ i₃ f₁ f₂ hf g₁ g₂ hg h₁ h₂
        (LinearMap.ker i₃).subtype (LinearMap.exact_subtype_ker_map i₃)
        π₁ (exact_leftTensorMul_oneTensorQuotient I)
        (LinearMap.lTensor_surjective I hq) K.subtype_injective) (x - y) = 0 := by
    simpa [idealKernelConnecting, K, f₁, f₂, g₁, g₂, i₁, i₂, i₃, π₁]
      using hzero
  obtain ⟨z, hz⟩ := (hex (x - y)).mp hzero'
  have hz0 : z = 0 := by
    apply Subtype.ext
    apply hi₂
    exact z.2.trans i₂.map_zero.symm
  rw [← hz, hz0, map_zero]

theorem idealKernelPresentationTorMap_injective
    {F : Type v} [AddCommGroup F] [Module R F] [Module.Flat R F]
    (q : F →ₗ[R] M) (hq : Function.Surjective q) (I : Ideal R) :
    Function.Injective (idealKernelPresentationTorMap q hq I) := by
  intro x y hxy
  apply idealKernelConnecting_injective q hq I
  exact congrArg Subtype.val hxy

/-- The ideal-tensor kernel is the presentation model for `Tor₁(R/I, M)`. -/
noncomputable def idealKernelPresentationTorEquiv
    {F : Type v} [AddCommGroup F] [Module R F] [Module.Flat R F]
    (q : F →ₗ[R] M) (hq : Function.Surjective q) (I : Ideal R) :
    LinearMap.ker (leftTensorMul (M := M) I) ≃ₗ[R] presentationTorOne q I :=
  LinearEquiv.ofBijective (idealKernelPresentationTorMap q hq I)
    ⟨idealKernelPresentationTorMap_injective q hq I,
      idealKernelPresentationTorMap_surjective q hq I⟩

/-- Switching the factors identifies the two orientations of the ideal-tensor kernel. -/
noncomputable def tensorMulKerEquivLeft (I : Ideal R) :
    LinearMap.ker (tensorMul (R := R) (S := R) (M := M) I) ≃ₗ[R]
      LinearMap.ker (leftTensorMul (M := M) I) := by
  let e := TensorProduct.comm R M I
  have he : (leftTensorMul (M := M) I).comp e.toLinearMap =
      tensorMul (R := R) (S := R) (M := M) I := by
    ext m i
    simp [leftTensorMul, e, TensorProduct.comm_tmul]
  let f : LinearMap.ker (tensorMul (R := R) (S := R) (M := M) I) →ₗ[R]
      LinearMap.ker (leftTensorMul (M := M) I) :=
    { toFun := fun x => ⟨e x.1, by
        change leftTensorMul (M := M) I (e x.1) = 0
        have hx := LinearMap.congr_fun he x.1
        change leftTensorMul (M := M) I (e x.1) =
          tensorMul (R := R) (S := R) (M := M) I x.1 at hx
        exact hx.trans x.2⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro r x; ext; simp }
  let g : LinearMap.ker (leftTensorMul (M := M) I) →ₗ[R]
      LinearMap.ker (tensorMul (R := R) (S := R) (M := M) I) :=
    { toFun := fun x => ⟨e.symm x.1, by
        change tensorMul (R := R) (S := R) (M := M) I (e.symm x.1) = 0
        have hx := LinearMap.congr_fun he (e.symm x.1)
        change leftTensorMul (M := M) I (e (e.symm x.1)) =
          tensorMul (R := R) (S := R) (M := M) I (e.symm x.1) at hx
        rw [e.apply_symm_apply] at hx
        exact hx.symm.trans x.2⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro r x; ext; simp }
  exact LinearEquiv.ofLinearMap f g (by ext x; simp [f, g, e])
    (by ext x; simp [f, g, e])

end Ideal
