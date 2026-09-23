module

public import StacksAndModuli.API.PresentationTensorKernelBaseChange

/-!
# Change of rings for presentation tensor kernels

For a surjection `F → M` over `R` and a tower `R → A → C`, this file constructs the canonical
map

`ker (C ⊗[R] ker(F → M) → C ⊗[R] F) →
  ker (C ⊗[A] ker(A ⊗ F → A ⊗ M) → C ⊗[A] (A ⊗ F))`

and proves that it is surjective.  This is the presentation-kernel form of the change-of-rings
surjection in Stacks Project tag 00MN.  It uses only right exactness of tensor product and the
canonical cancellation equivalences for a tower of scalar extensions.
-/

@[expose] public section

open TensorProduct Function

universe u v

namespace LinearMap

/-- The canonical map from a presentation tensor kernel over `R` to the presentation tensor
kernel obtained after changing the presentation ring to `A`. -/
noncomputable def presentationTensorKernelToBaseChangedMap
    {R : Type u} {F M : Type v} [CommRing R]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (A C : Type u)
    [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    [Algebra A C] [IsScalarTower R A C] :
    presentationTensorKernel q C →ₗ[C]
      presentationTensorKernel (q.baseChange A) C := by
  let K := LinearMap.ker q
  let L := LinearMap.ker (q.baseChange A)
  let eK := AlgebraTensorModule.cancelBaseChange R A C C K
  let raw : C ⊗[R] K →ₗ[C] C ⊗[A] L :=
    (q.kerBaseChangeHom A).baseChange C ∘ₗ eK.symm.toLinearMap
  refine (raw.comp (presentationTensorKernel q C).subtype).codRestrict _ fun z => ?_
  change (L.subtype.baseChange C) (raw z.1) = 0
  have hsub : L.subtype.comp (q.kerBaseChangeHom A) = K.subtype.baseChange A := rfl
  have hcomp : (L.subtype.baseChange C).comp
      ((q.kerBaseChangeHom A).baseChange C) =
      ((K.subtype.baseChange A).baseChange C) := by
    rw [← LinearMap.baseChange_comp, hsub]
  have hraw : (L.subtype.baseChange C).comp raw =
      ((K.subtype.baseChange A).baseChange C).comp eK.symm.toLinearMap := by
    change (L.subtype.baseChange C).comp
        (((q.kerBaseChangeHom A).baseChange C).comp eK.symm.toLinearMap) = _
    rw [← LinearMap.comp_assoc, hcomp]
  have hz := LinearMap.congr_fun hraw z.1
  simp only [LinearMap.comp_apply] at hz
  rw [hz]
  let eF := AlgebraTensorModule.cancelBaseChange R A C C F
  apply eF.injective
  have hcomm := cancelBaseChange_naturality (A := A) (B := C) K.subtype
  have hcommz := LinearMap.congr_fun hcomm (eK.symm z.1)
  simp only [LinearMap.comp_apply] at hcommz
  calc
    eF (((K.subtype.baseChange A).baseChange C) (eK.symm z.1)) =
        (K.subtype.baseChange C) (eK (eK.symm z.1)) := hcommz
    _ = (K.subtype.baseChange C) z.1 := by rw [eK.apply_symm_apply]
    _ = 0 := z.2
    _ = eF 0 := (map_zero eF).symm

/-- The change-of-presentation-ring map on presentation tensor kernels is surjective. -/
theorem presentationTensorKernelToBaseChangedMap_surjective
    {R A C : Type u} {F M : Type v}
    [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Algebra A C] [IsScalarTower R A C]
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    (q : F →ₗ[R] M) (hq : Function.Surjective q) :
    Function.Surjective (presentationTensorKernelToBaseChangedMap q A C) := by
  let K := LinearMap.ker q
  let L := LinearMap.ker (q.baseChange A)
  let eK := AlgebraTensorModule.cancelBaseChange R A C C K
  let eF := AlgebraTensorModule.cancelBaseChange R A C C F
  let raw : C ⊗[R] K →ₗ[C] C ⊗[A] L :=
    (q.kerBaseChangeHom A).baseChange C ∘ₗ eK.symm.toLinearMap
  have hkerSurj : Function.Surjective (q.kerBaseChangeHom A) :=
    kerBaseChangeHom_surjective_of_surjective q hq
  have hraw : Function.Surjective raw :=
    (LinearMap.lTensor_surjective C hkerSurj).comp eK.symm.surjective
  intro y
  obtain ⟨z, hz⟩ := hraw y.1
  have hzker : (K.subtype.baseChange C) z = 0 := by
    have hsub : L.subtype.comp (q.kerBaseChangeHom A) = K.subtype.baseChange A := rfl
    have hcomp : (L.subtype.baseChange C).comp
        ((q.kerBaseChangeHom A).baseChange C) =
        ((K.subtype.baseChange A).baseChange C) := by
      rw [← LinearMap.baseChange_comp, hsub]
    have hcompz := LinearMap.congr_fun hcomp (eK.symm z)
    simp only [LinearMap.comp_apply] at hcompz
    have hcomm := cancelBaseChange_naturality (A := A) (B := C) K.subtype
    have hcommz := LinearMap.congr_fun hcomm (eK.symm z)
    simp only [LinearMap.comp_apply] at hcommz
    calc
      (K.subtype.baseChange C) z =
          (K.subtype.baseChange C) (eK (eK.symm z)) :=
        congrArg (K.subtype.baseChange C) (eK.apply_symm_apply z).symm
      _ = eF (((K.subtype.baseChange A).baseChange C) (eK.symm z)) := hcommz.symm
      _ = eF ((L.subtype.baseChange C)
          (((q.kerBaseChangeHom A).baseChange C) (eK.symm z))) :=
        congrArg eF hcompz.symm
      _ = eF ((L.subtype.baseChange C) (raw z)) := rfl
      _ = eF ((L.subtype.baseChange C) y.1) := congrArg
        (fun t => eF ((L.subtype.baseChange C) t)) hz
      _ = eF 0 := congrArg eF y.2
      _ = 0 := map_zero eF
  let x : presentationTensorKernel q C := ⟨z, hzker⟩
  refine ⟨x, Subtype.ext ?_⟩
  exact hz

end LinearMap
