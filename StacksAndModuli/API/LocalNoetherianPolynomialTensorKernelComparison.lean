module

public import StacksAndModuli.API.IdealTensorKernelCanonicalBaseChange
public import StacksAndModuli.API.LocalNoetherianPolynomialTensorSystem

/-!
# Comparing the local polynomial tensor system with canonical kernel base change

The finite obstruction killed in the local coefficient system is expressed using a fixed
initial polynomial module.  The local flatness comparison theorem instead uses canonical
coefficient base change of the actual ideal-multiplication kernel.  This file identifies
those two maps and turns simultaneous finite-stage vanishing into injectivity of ideal
multiplication at that stage.

This is the comparison step in the flatness-spreading argument of Stacks Project tag 00R6.
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u v w

namespace Module.FinitePresentation.PolynomialModel

open LocalNoetherianApproximation

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {σ : Type v}
variable {M : Type w} [AddCommGroup M] [Module (MvPolynomial σ R) M]

/-- The initial maximal ideal maps into every later maximal ideal. -/
theorem localMaximalIdeal_le_comap (D : PolynomialModel R σ M)
    (j : Later R D.localIndex) :
    maximalIdeal D.localCoefficient ≤
      (maximalIdeal (coefficient R j.1)).comap
        (algebraMap D.localCoefficient (coefficient R j.1)) := by
  intro x hx
  change transition R D.localIndex j.1 j.2 x ∈
    maximalIdeal (coefficient R j.1)
  exact map_nonunit (transition R D.localIndex j.1 j.2) x hx

/-- With the ideal on the left, canonical coefficient base change of the initial module is
the corresponding object of the fixed obstruction system. -/
noncomputable def localCoefficientLeftTensorObstructionEquiv
    (D : PolynomialModel R σ M) (j : Later R D.localIndex) :
    maximalIdeal (coefficient R j.1) ⊗[coefficient R j.1]
        ((coefficient R j.1) ⊗[D.localCoefficient] D.localModelModule) ≃+
      D.localSystemTensorObstruction j := by
  letI : Module D.localCoefficient (maximalIdeal (coefficient R j.1)) :=
    maximalIdealModule R j
  exact (LinearEquiv.lTensor (maximalIdeal (coefficient R j.1))
      (D.localSystemCoefficientBaseChangeEquiv j).symm).toAddEquiv.trans <|
    (D.localSystemIdealTensorEquiv j).toAddEquiv.trans <|
      (TensorProduct.comm D.localCoefficient
          (maximalIdeal (coefficient R j.1)) D.localModelModule).toAddEquiv.trans <|
        (LinearEquiv.lTensor D.localModelModule
            ((localSystemMaximalIdealAddEquiv D j).linearEquiv
              D.localCoefficient).symm).toAddEquiv

@[simp]
theorem localCoefficientLeftTensorObstructionEquiv_tmul_one_tmul
    (D : PolynomialModel R σ M) (j : Later R D.localIndex)
    (x : D.localModelModule) (a : maximalIdeal (coefficient R j.1)) :
    D.localCoefficientLeftTensorObstructionEquiv j
        (a ⊗ₜ ((1 : coefficient R j.1) ⊗ₜ x)) =
      x ⊗ₜ (localSystemMaximalIdealAddEquiv D j).symm a := by
  simp [localCoefficientLeftTensorObstructionEquiv]

/-- Canonical left-oriented tensor base change is exactly the transition from the initial
object of the fixed tensor system. -/
theorem localCoefficientLeftTensorObstructionEquiv_baseChangeMap
    (D : PolynomialModel R σ M) (j : Later R D.localIndex)
    (z : maximalIdeal D.localCoefficient ⊗[D.localCoefficient]
      D.localModelModule) :
    D.localCoefficientLeftTensorObstructionEquiv j
        (Ideal.leftTensorBaseChangeMap
          (maximalIdeal D.localCoefficient)
          (maximalIdeal (coefficient R j.1))
          (D.localMaximalIdeal_le_comap j) z) =
      D.localSystemTensorObstructionTransition
        (initialLater R D.localIndex) j j.2
          (D.localInitialTensorToSystem
            (TensorProduct.comm D.localCoefficient
              (maximalIdeal D.localCoefficient) D.localModelModule z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add, hx, hy]
  | tmul a x =>
      simp [Ideal.leftTensorBaseChangeMap_tmul,
        localSystemTensorObstructionTransition,
        localSystemTensorObstructionTransitionBase]
      congr 1

/-- On an element of the initial ideal-multiplication kernel, the canonical left-oriented
base-change tensor agrees with the transition in the fixed obstruction system. -/
theorem localCoefficientLeftTensorObstructionEquiv_tensorMulKerSource
    (D : PolynomialModel R σ M) (j : Later R D.localIndex)
    (x : D.localInitialTensorKernel) :
    D.localCoefficientLeftTensorObstructionEquiv j
        (Ideal.leftTensorBaseChangeMap
          (maximalIdeal D.localCoefficient)
          (maximalIdeal (coefficient R j.1))
          (D.localMaximalIdeal_le_comap j)
          (Ideal.tensorMulKerEquivLeft
            (M := D.localModelModule)
            (maximalIdeal D.localCoefficient) x).1) =
      D.localSystemTensorObstructionTransition
        (initialLater R D.localIndex) j j.2
          (D.localInitialTensorKernelMap x) := by
  rw [localCoefficientLeftTensorObstructionEquiv_baseChangeMap]
  change D.localSystemTensorObstructionTransition
      (initialLater R D.localIndex) j j.2
        (D.localInitialTensorToSystem
          (TensorProduct.comm D.localCoefficient
            (maximalIdeal D.localCoefficient) D.localModelModule
            (Ideal.tensorMulKerEquivLeft
              (M := D.localModelModule)
              (maximalIdeal D.localCoefficient) x).1)) =
    D.localSystemTensorObstructionTransition
      (initialLater R D.localIndex) j j.2
        (D.localInitialTensorToSystem x.1)
  congr 2
  change (TensorProduct.comm D.localCoefficient
      (maximalIdeal D.localCoefficient) D.localModelModule)
      ((TensorProduct.comm D.localCoefficient D.localModelModule
        (maximalIdeal D.localCoefficient)) x.1) = x.1
  simp

/-- If the fixed-system transition kills the initial obstruction, the canonical map on
ideal-multiplication kernels is zero. -/
theorem tensorMulKerBaseChangeMap_eq_zero_of_transition_comp_eq_zero
    (D : PolynomialModel R σ M) (j : Later R D.localIndex)
    (hzero :
      (D.localSystemTensorObstructionTransition
        (initialLater R D.localIndex) j j.2).comp
          D.localInitialTensorKernelMap = 0) :
    Ideal.tensorMulKerBaseChangeMap
        (M := D.localModelModule)
        (maximalIdeal D.localCoefficient)
        (maximalIdeal (coefficient R j.1))
        (D.localMaximalIdeal_le_comap j) = 0 := by
  apply AddMonoidHom.ext
  intro x
  let f := Ideal.tensorMulKerBaseChangeMap
    (M := D.localModelModule)
    (maximalIdeal D.localCoefficient)
    (maximalIdeal (coefficient R j.1))
    (D.localMaximalIdeal_le_comap j)
  let y := f x
  let z := f (0 : D.localInitialTensorKernel)
  have htransition : D.localSystemTensorObstructionTransition
      (initialLater R D.localIndex) j j.2
        (D.localInitialTensorKernelMap x) = 0 := by
    calc
      D.localSystemTensorObstructionTransition
          (initialLater R D.localIndex) j j.2
            (D.localInitialTensorKernelMap x) =
        (0 : D.localInitialTensorKernel →ₗ[
          MvPolynomial σ D.localCoefficient]
            D.localSystemTensorObstruction j) x :=
          LinearMap.congr_fun hzero x
      _ = 0 := rfl
  have hleft : Ideal.leftTensorBaseChangeMap
      (M := D.localModelModule)
      (maximalIdeal D.localCoefficient)
      (maximalIdeal (coefficient R j.1))
      (D.localMaximalIdeal_le_comap j)
      (Ideal.tensorMulKerEquivLeft
        (M := D.localModelModule)
        (maximalIdeal D.localCoefficient) x).1 = 0 := by
    apply (D.localCoefficientLeftTensorObstructionEquiv j).injective
    calc
      D.localCoefficientLeftTensorObstructionEquiv j
          (Ideal.leftTensorBaseChangeMap
            (M := D.localModelModule)
            (maximalIdeal D.localCoefficient)
            (maximalIdeal (coefficient R j.1))
            (D.localMaximalIdeal_le_comap j)
            (Ideal.tensorMulKerEquivLeft
              (M := D.localModelModule)
              (maximalIdeal D.localCoefficient) x).1) =
        D.localSystemTensorObstructionTransition
          (initialLater R D.localIndex) j j.2
            (D.localInitialTensorKernelMap x) :=
          D.localCoefficientLeftTensorObstructionEquiv_tensorMulKerSource j x
      _ = 0 := htransition
      _ = D.localCoefficientLeftTensorObstructionEquiv j 0 := (map_zero _).symm
  have hcanonical := Ideal.tensorMulKerEquivLeft_baseChangeMap_val
    (M := D.localModelModule)
    (maximalIdeal D.localCoefficient)
    (maximalIdeal (coefficient R j.1))
    (D.localMaximalIdeal_le_comap j) x
  change (TensorProduct.comm (coefficient R j.1)
      ((coefficient R j.1) ⊗[D.localCoefficient] D.localModelModule)
      (maximalIdeal (coefficient R j.1))) y.1 = _ at hcanonical
  have hyComm : (TensorProduct.comm (coefficient R j.1)
      ((coefficient R j.1) ⊗[D.localCoefficient] D.localModelModule)
      (maximalIdeal (coefficient R j.1))) y.1 = Zero.zero :=
    hcanonical.trans hleft
  have hz : z = 0 := by
    change f 0 = 0
    exact map_zero f
  have hyzComm : (TensorProduct.comm (coefficient R j.1)
      ((coefficient R j.1) ⊗[D.localCoefficient] D.localModelModule)
      (maximalIdeal (coefficient R j.1))) y.1 =
      (TensorProduct.comm (coefficient R j.1)
        ((coefficient R j.1) ⊗[D.localCoefficient] D.localModelModule)
        (maximalIdeal (coefficient R j.1))) z.1 := by
    rw [hz]
    exact hyComm
  have hyzVal : y.1 = z.1 :=
    (TensorProduct.comm (coefficient R j.1)
      ((coefficient R j.1) ⊗[D.localCoefficient] D.localModelModule)
      (maximalIdeal (coefficient R j.1))).injective
        hyzComm
  have hyz : y = z := Subtype.ext hyzVal
  exact hyz.trans hz

set_option maxHeartbeats 800000 in
/-- If the finite initial obstruction is killed at a later coefficient stage, ideal
multiplication on the coefficient base change is injective.  The closed-fibre flatness
hypothesis is the 00MO input. -/
theorem tensorMul_injective_of_transition_comp_eq_zero
    (D : PolynomialModel R σ M) (j : Later R D.localIndex)
    [Module.Flat
      (D.localCoefficient ⧸ maximalIdeal D.localCoefficient)
      ((D.localCoefficient ⧸ maximalIdeal D.localCoefficient) ⊗[
        D.localCoefficient] D.localModelModule)]
    (hzero :
      (D.localSystemTensorObstructionTransition
        (initialLater R D.localIndex) j j.2).comp
          D.localInitialTensorKernelMap = 0) :
    Function.Injective
      (Ideal.tensorMul
        (R := coefficient R j.1) (S := polynomial R σ j)
        (M := D.localSystemStage j)
        (maximalIdeal (coefficient R j.1))) := by
  letI : Module.FinitePresentation
      (MvPolynomial σ D.localCoefficient) D.localModelModule :=
    D.localModelModule_finitePresentation
  obtain ⟨n, _m, q, _g, hq, _hgq⟩ :=
    Module.FinitePresentation.exists_fin'
      (MvPolynomial σ D.localCoefficient) D.localModelModule
  have hspan := Ideal.span_range_tensorMulKerBaseChangeMap
    (M := D.localModelModule) (q.restrictScalars D.localCoefficient) hq
    (maximalIdeal D.localCoefficient)
    (maximalIdeal (coefficient R j.1))
    (D.localMaximalIdeal_le_comap j)
  have hmapzero :=
    D.tensorMulKerBaseChangeMap_eq_zero_of_transition_comp_eq_zero j hzero
  let coefficientModule : Module D.localCoefficient (coefficient R j.1) :=
    (LocalNoetherianApproximation.coefficientAlgebra (R := R) j).toModule
  let modelModule : Module D.localCoefficient D.localModelModule := inferInstance
  let tensorGroup : AddCommGroup
      ((coefficient R j.1) ⊗[D.localCoefficient] D.localModelModule) :=
    @TensorProduct.addCommGroup D.localCoefficient _
      (coefficient R j.1) D.localModelModule _ _ coefficientModule modelModule
  letI : AddCommGroup
      ((coefficient R j.1) ⊗[D.localCoefficient] D.localModelModule) :=
    { neg := tensorGroup.neg
      sub := tensorGroup.sub
      zsmul := tensorGroup.zsmul
      neg_add_cancel := tensorGroup.neg_add_cancel
      sub_eq_add_neg := tensorGroup.sub_eq_add_neg
      zsmul_zero' := tensorGroup.zsmul_zero'
      zsmul_succ' := tensorGroup.zsmul_succ'
      zsmul_neg' := tensorGroup.zsmul_neg' }
  rw [injective_iff_map_eq_zero]
  intro z hz
  let e := D.localSystemCoefficientBaseChangeEquiv j
  have hnatural (w : D.localSystemStage j ⊗[coefficient R j.1]
      maximalIdeal (coefficient R j.1)) :
      Ideal.tensorMul
          (R := coefficient R j.1) (S := coefficient R j.1)
          (maximalIdeal (coefficient R j.1))
          ((e.rTensor (maximalIdeal (coefficient R j.1))) w) =
        e (Ideal.tensorMul
          (R := coefficient R j.1) (S := polynomial R σ j)
          (M := D.localSystemStage j)
          (maximalIdeal (coefficient R j.1)) w) := by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add, hx, hy]
    | tmul x a => simp [Ideal.tensorMul_tmul]
  let y := (e.rTensor (maximalIdeal (coefficient R j.1))) z
  have hy : Ideal.tensorMul
      (R := coefficient R j.1) (S := coefficient R j.1)
      (maximalIdeal (coefficient R j.1)) y = 0 := by
    rw [show y = (e.rTensor (maximalIdeal (coefficient R j.1))) z by rfl]
    rw [hnatural, hz, map_zero]
  let x : LinearMap.ker
      (Ideal.tensorMul
        (R := coefficient R j.1) (S := coefficient R j.1)
        (M := (coefficient R j.1) ⊗[D.localCoefficient]
          D.localModelModule)
        (maximalIdeal (coefficient R j.1))) := ⟨y, hy⟩
  have hx : x ∈
      Submodule.span (coefficient R j.1)
        (Set.range (Ideal.tensorMulKerBaseChangeMap
          (M := D.localModelModule)
          (maximalIdeal D.localCoefficient)
          (maximalIdeal (coefficient R j.1))
          (D.localMaximalIdeal_le_comap j))) := by
    exact (ge_of_eq hspan) Submodule.mem_top
  have hzeroSpan : Submodule.span (coefficient R j.1)
      (Set.range (Ideal.tensorMulKerBaseChangeMap
        (M := D.localModelModule)
        (maximalIdeal D.localCoefficient)
        (maximalIdeal (coefficient R j.1))
        (D.localMaximalIdeal_le_comap j))) = ⊥ := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      have hw : Ideal.tensorMulKerBaseChangeMap
          (M := D.localModelModule)
          (maximalIdeal D.localCoefficient)
          (maximalIdeal (coefficient R j.1))
          (D.localMaximalIdeal_le_comap j) w = 0 := by
        exact DFunLike.congr_fun hmapzero w
      rw [hw]
      exact Submodule.zero_mem _
    · exact bot_le
  have hxzero : x = 0 :=
    (Submodule.mem_bot (coefficient R j.1)).mp ((le_of_eq hzeroSpan) hx)
  apply (e.rTensor (maximalIdeal (coefficient R j.1))).injective
  exact congrArg Subtype.val hxzero

end Module.FinitePresentation.PolynomialModel

end
