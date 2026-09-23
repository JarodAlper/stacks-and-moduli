module

public import StacksAndModuli.API.IdealTensorKernelPresentation
public import StacksAndModuli.API.KernelBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Base change of kernels in a finite presentation

Let `F → M` be a surjection, put `K = ker (F → M)`, and let `R → A → B` be a tower of
commutative rings.  If `A ⊗[R] M` is flat over `A`, then right exactness and flatness give a
surjection

`B ⊗[A] ker (A ⊗[R] K → A ⊗[R] F) → ker (B ⊗[R] K → B ⊗[R] F)`.

This is the presentation-kernel form of the base-change surjection used in the proof of Stacks
Project tag 00MM.  Together with `Ideal.idealKernelPresentationTorEquiv`, it provides an
elementary replacement for the corresponding `Tor₁` comparison without introducing derived
functors.
-/

@[expose] public section

open TensorProduct Function

universe u v w x

namespace LinearMap

/-- The canonical map from the base change of a kernel to the kernel of the base-changed map is
surjective when the original map is surjective.  This is right exactness of tensor product. -/
theorem kerBaseChangeHom_surjective_of_surjective
    {R S : Type u} {F M : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (hq : Function.Surjective q) :
    Function.Surjective (q.kerBaseChangeHom S) := by
  intro y
  have hex : Function.Exact
      ((LinearMap.ker q).subtype.baseChange S) (q.baseChange S) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      lTensor_exact S (LinearMap.exact_subtype_ker_map q) hq
  obtain ⟨x, hx⟩ := (hex y.1).mp y.2
  exact ⟨x, Subtype.ext hx⟩

private theorem ker_subtype_baseChange_injective_of_flat
    {A B : Type u} {N P : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    [Module.Flat A P] (q : N →ₗ[A] P) (hq : Function.Surjective q) :
    Function.Injective ((LinearMap.ker q).subtype.baseChange B) := by
  change Function.Injective ((LinearMap.ker q).subtype.lTensor B)
  let e := q.kerLTensorEquivOfSurjective hq B
  intro x y hxy
  apply e.symm.injective
  apply Subtype.ext
  exact hxy

/-- Cancellation of two successive scalar extensions is natural in the module map. -/
theorem cancelBaseChange_naturality
    {R : Type u} {A : Type v} {B : Type w} {N P : Type x}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    (f : N →ₗ[R] P) :
    (AlgebraTensorModule.cancelBaseChange R A B B P).toLinearMap.comp
        ((f.baseChange A).baseChange B) =
      (f.baseChange B).comp
        (AlgebraTensorModule.cancelBaseChange R A B B N).toLinearMap := by
  change (AlgebraTensorModule.cancelBaseChange R A B B P).toLinearMap.comp
      ((AlgebraTensorModule.lTensor B B)
        ((AlgebraTensorModule.lTensor A A) f)) =
    ((AlgebraTensorModule.lTensor B B) f).comp
      (AlgebraTensorModule.cancelBaseChange R A B B N).toLinearMap
  exact (AlgebraTensorModule.lTensor_comp_cancelBaseChange R A B (M := B) f).symm

private theorem baseChange_subtype_comp_codRestrict
    {A B : Type u} {X Y : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (f : X →ₗ[A] Y) (P : Submodule A Y) (h : ∀ x, f x ∈ P) :
    P.subtype.baseChange B ∘ₗ (f.codRestrict P h).baseChange B = f.baseChange B := by
  rw [← LinearMap.baseChange_comp]
  rfl

private theorem exact_baseChange_ker_codRestrict
    {A B : Type u} {X Y : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (f : X →ₗ[A] Y) (P : Submodule A Y) (h : ∀ x, f x ∈ P)
    (hsurj : Function.Surjective (f.codRestrict P h)) :
    Function.Exact ((LinearMap.ker f).subtype.baseChange B)
      ((f.codRestrict P h).baseChange B) := by
  let v := f.codRestrict P h
  have hker : LinearMap.ker v = LinearMap.ker f := by
    ext x
    change v x = 0 ↔ f x = 0
    constructor
    · exact fun hx => congrArg Subtype.val hx
    · intro hx
      apply Subtype.ext
      exact hx
  have hex : Function.Exact (LinearMap.ker f).subtype v := by
    rw [LinearMap.exact_iff, hker, Submodule.range_subtype]
  simpa only [LinearMap.baseChange_eq_ltensor] using
    lTensor_exact B hex hsurj

/-- The presentation kernel after the scalar extension `R → A`. -/
abbrev presentationTensorKernel
    {R : Type u} {F M : Type v} [CommRing R]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (A : Type u) [CommRing A] [Algebra R A] :=
  LinearMap.ker ((LinearMap.ker q).subtype.baseChange A)

/-- The canonical transition from the scalar extension of the presentation kernel over `A` to
the presentation kernel over `B`. -/
noncomputable def presentationTensorKernelBaseChangeMap
    {R : Type u} {F M : Type v} [CommRing R]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (A B : Type u)
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [Algebra A B] [IsScalarTower R A B] :
    B ⊗[A] presentationTensorKernel q A →ₗ[B] presentationTensorKernel q B := by
  let K := LinearMap.ker q
  let eK := AlgebraTensorModule.cancelBaseChange R A B B K
  let raw : B ⊗[A] presentationTensorKernel q A →ₗ[B] B ⊗[R] K :=
    eK.toLinearMap.comp
      ((LinearMap.ker (K.subtype.baseChange A)).subtype.baseChange B)
  refine raw.codRestrict _ fun z => ?_
  change (K.subtype.baseChange B) (raw z) = 0
  have hcomm : (K.subtype.baseChange B).comp eK.toLinearMap =
      (AlgebraTensorModule.cancelBaseChange R A B B F).toLinearMap.comp
        ((K.subtype.baseChange A).baseChange B) := by
    exact (cancelBaseChange_naturality K.subtype).symm
  change (K.subtype.baseChange B)
    (eK (((LinearMap.ker (K.subtype.baseChange A)).subtype.baseChange B) z)) = 0
  have hz := LinearMap.congr_fun hcomm
    (((LinearMap.ker (K.subtype.baseChange A)).subtype.baseChange B) z)
  change (K.subtype.baseChange B)
      (eK (((LinearMap.ker (K.subtype.baseChange A)).subtype.baseChange B) z)) =
    (AlgebraTensorModule.cancelBaseChange R A B B F)
      (((K.subtype.baseChange A).baseChange B)
        (((LinearMap.ker (K.subtype.baseChange A)).subtype.baseChange B) z)) at hz
  rw [hz]
  have hinner : ((K.subtype.baseChange A).baseChange B)
      (((LinearMap.ker (K.subtype.baseChange A)).subtype.baseChange B) z) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    have hcomp : (K.subtype.baseChange A).comp
        (LinearMap.ker (K.subtype.baseChange A)).subtype = 0 := by
      ext t
      exact t.2
    rw [hcomp, LinearMap.baseChange_zero, LinearMap.zero_apply]
  exact hinner ▸ map_zero (AlgebraTensorModule.cancelBaseChange R A B B F)

/-- If the intermediate scalar extension of the presented module is flat, the canonical
transition between presentation kernels is surjective. -/
theorem presentationTensorKernelBaseChangeMap_surjective
    {R A B : Type u} {F M : Type v}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (hq : Function.Surjective q)
    [Module.Flat A (A ⊗[R] M)] :
    Function.Surjective (presentationTensorKernelBaseChangeMap q A B) := by
  let K := LinearMap.ker q
  let uA : A ⊗[R] K →ₗ[A] A ⊗[R] F := K.subtype.baseChange A
  let qA : A ⊗[R] F →ₗ[A] A ⊗[R] M := q.baseChange A
  have hexA : Function.Exact uA qA := by
    simpa only [uA, qA, K, LinearMap.baseChange_eq_ltensor] using
      lTensor_exact A (LinearMap.exact_subtype_ker_map q) hq
  have hqA : Function.Surjective qA := LinearMap.lTensor_surjective A hq
  let L := LinearMap.ker qA
  let vA : A ⊗[R] K →ₗ[A] L :=
    uA.codRestrict L fun x => hexA.apply_apply_eq_zero x
  have hvA : Function.Surjective vA := by
    intro y
    obtain ⟨x, hx⟩ := (hexA y.1).mp y.2
    exact ⟨x, Subtype.ext hx⟩
  have hLinj : Function.Injective (L.subtype.baseChange B) := by
    exact ker_subtype_baseChange_injective_of_flat qA hqA
  intro y
  let eK := AlgebraTensorModule.cancelBaseChange R A B B K
  let eF := AlgebraTensorModule.cancelBaseChange R A B B F
  let x : B ⊗[A] (A ⊗[R] K) := eK.symm y.1
  have hx : (vA.baseChange B) x = 0 := by
    apply hLinj
    have hcommL : (L.subtype.baseChange B).comp (vA.baseChange B) =
        (uA.baseChange B) :=
      baseChange_subtype_comp_codRestrict uA L fun z => hexA.apply_apply_eq_zero z
    have hcommLx := LinearMap.congr_fun hcommL x
    simp only [LinearMap.comp_apply] at hcommLx
    have hcomm : eF.toLinearMap.comp (uA.baseChange B) =
        (K.subtype.baseChange B).comp eK.toLinearMap := by
      exact cancelBaseChange_naturality K.subtype
    have hcommx := LinearMap.congr_fun hcomm x
    simp only [LinearMap.comp_apply] at hcommx
    calc
      (L.subtype.baseChange B) ((vA.baseChange B) x) = (uA.baseChange B) x := hcommLx
      _ = 0 := eF.injective <| hcommx.trans <| by
        calc
          (K.subtype.baseChange B) (eK x) =
              (K.subtype.baseChange B) y.1 :=
            congrArg (K.subtype.baseChange B) (eK.apply_symm_apply y.1)
          _ = 0 := y.2
          _ = eF 0 := (map_zero eF).symm
      _ = (L.subtype.baseChange B) 0 := (map_zero _).symm
  have hexvB : Function.Exact ((LinearMap.ker uA).subtype.baseChange B)
      (vA.baseChange B) :=
    exact_baseChange_ker_codRestrict uA L
      (fun z => hexA.apply_apply_eq_zero z) hvA
  obtain ⟨z, hz⟩ := (hexvB x).mp hx
  refine ⟨z, Subtype.ext ?_⟩
  change eK ((LinearMap.ker uA).subtype.baseChange B z) = y.1
  rw [hz, eK.apply_symm_apply]

end LinearMap
