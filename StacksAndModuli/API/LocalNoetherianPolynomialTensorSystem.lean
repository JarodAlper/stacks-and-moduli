module

public import StacksAndModuli.API.LocalNoetherianMaximalIdealSystem
public import StacksAndModuli.API.LocalNoetherianPolynomialModelSystem
public import StacksAndModuli.API.NoetherianTorKernelFinite
public import StacksAndModuli.API.DirectLimitFiniteVanishing
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Ideal-tensor systems attached to local polynomial models

For a finite polynomial presentation over a local ring, every later model is both a
polynomial base change and a coefficient base change of the fixed initial model.  This file
records that second description and uses it to identify the left-oriented maximal-ideal
tensor at every stage with one directed system over the initial polynomial ring.

This is the ambient tensor system in the finite-obstruction proof of Stacks Project tag
00R6.  Kernel vanishing and eventual flatness are not asserted here.
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u v w

namespace Module.FinitePresentation.PolynomialModel

open LocalNoetherianApproximation

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {σ : Type v}
variable {M : Type w} [AddCommGroup M] [Module (MvPolynomial σ R) M]

/-- A later polynomial model is coefficient base change of the initial local model. -/
noncomputable def localSystemCoefficientBaseChangeEquiv
    (D : PolynomialModel R σ M) (j : Later R D.localIndex) :
    D.localSystemStage j ≃ₗ[coefficient R j.1]
      coefficient R j.1 ⊗[D.localCoefficient] D.localModelModule := by
  letI : IsScalarTower D.localCoefficient
      (MvPolynomial σ D.localCoefficient) (polynomial R σ j) :=
    LocalNoetherianApproximation.coefficientPolynomialTower R σ j
  exact Algebra.IsPushout.cancelBaseChange
    D.localCoefficient (coefficient R j.1)
      (MvPolynomial σ D.localCoefficient) (polynomial R σ j)
      D.localModelModule

@[simp]
theorem localSystemCoefficientBaseChangeEquiv_one_tmul
    (D : PolynomialModel R σ M) (j : Later R D.localIndex)
    (x : D.localModelModule) :
    D.localSystemCoefficientBaseChangeEquiv j
        ((1 : polynomial R σ j) ⊗ₜ x) =
      (1 : coefficient R j.1) ⊗ₜ x := by
  letI : IsScalarTower D.localCoefficient
      (MvPolynomial σ D.localCoefficient) (polynomial R σ j) :=
    LocalNoetherianApproximation.coefficientPolynomialTower R σ j
  exact Algebra.IsPushout.cancelBaseChange_tmul
    D.localCoefficient (coefficient R j.1)
      (MvPolynomial σ D.localCoefficient) (polynomial R σ j)
      D.localModelModule x

/-- The inverse coefficient base-change equivalence sends a canonical one-tensor back to
the corresponding one-tensor over the later polynomial ring. -/
@[simp]
theorem localSystemCoefficientBaseChangeEquiv_symm_one_tmul
    (D : PolynomialModel R σ M) (j : Later R D.localIndex)
    (x : D.localModelModule) :
    (D.localSystemCoefficientBaseChangeEquiv j).symm
        ((1 : coefficient R j.1) ⊗ₜ x) =
      (1 : polynomial R σ j) ⊗ₜ x := by
  apply (D.localSystemCoefficientBaseChangeEquiv j).injective
  rw [LinearEquiv.apply_symm_apply]
  exact (D.localSystemCoefficientBaseChangeEquiv_one_tmul j x).symm

/-- The left-oriented ideal tensor at a later polynomial stage, expressed over the fixed
initial coefficient ring. -/
abbrev localSystemIdealTensor (D : PolynomialModel R σ M)
    (j : Later R D.localIndex) :=
  (maximalIdeal (coefficient R j.1)) ⊗[D.localCoefficient] D.localModelModule

/-- The actual left-oriented ideal tensor of a later model is the fixed-model tensor
system obtained by coefficient base change. -/
noncomputable def localSystemIdealTensorEquiv
    (D : PolynomialModel R σ M) (j : Later R D.localIndex) :
    (maximalIdeal (coefficient R j.1)) ⊗[coefficient R j.1]
        D.localSystemStage j ≃ₗ[coefficient R j.1]
      D.localSystemIdealTensor j :=
  LinearEquiv.lTensor (maximalIdeal (coefficient R j.1))
      (D.localSystemCoefficientBaseChangeEquiv j) ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange
      D.localCoefficient (coefficient R j.1) (coefficient R j.1)
      (maximalIdeal (coefficient R j.1)) D.localModelModule

@[simp]
theorem localSystemIdealTensorEquiv_tmul_one_tmul
    (D : PolynomialModel R σ M) (j : Later R D.localIndex)
    (x : maximalIdeal (coefficient R j.1)) (y : D.localModelModule) :
    D.localSystemIdealTensorEquiv j
        (x ⊗ₜ ((1 : polynomial R σ j) ⊗ₜ y)) = x ⊗ₜ y := by
  simp [localSystemIdealTensorEquiv]

/-- A later maximal ideal with its action by the fixed initial coefficient ring remembered
as part of a distinct wrapper type.  The wrapper prevents the self-stage from accidentally
acquiring the ordinary submodule action instead of the transition action. -/
@[ext]
structure LocalSystemMaximalIdeal (D : PolynomialModel R σ M)
    (j : Later R D.localIndex) where
  val : maximalIdeal (coefficient R j.1)

/-- Forget the wrapper on a maximal ideal in the local coefficient system. -/
noncomputable def localSystemMaximalIdealEquiv (D : PolynomialModel R σ M)
    (j : Later R D.localIndex) :
    LocalSystemMaximalIdeal D j ≃ maximalIdeal (coefficient R j.1) where
  toFun := LocalSystemMaximalIdeal.val
  invFun := LocalSystemMaximalIdeal.mk
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance localSystemMaximalIdealAddCommGroup
    (D : PolynomialModel R σ M) (j : Later R D.localIndex) :
    AddCommGroup (LocalSystemMaximalIdeal D j) :=
  (localSystemMaximalIdealEquiv D j).addCommGroup

/-- The additive equivalence forgetting the maximal-ideal system wrapper. -/
noncomputable def localSystemMaximalIdealAddEquiv
    (D : PolynomialModel R σ M) (j : Later R D.localIndex) :
    LocalSystemMaximalIdeal D j ≃+ maximalIdeal (coefficient R j.1) where
  __ := localSystemMaximalIdealEquiv D j
  map_add' _ _ := rfl

/-- The action of the initial coefficient ring on a wrapped later maximal ideal is induced
by the coefficient transition. -/
noncomputable instance localSystemMaximalIdealModule
    (D : PolynomialModel R σ M) (j : Later R D.localIndex) :
    Module D.localCoefficient (LocalSystemMaximalIdeal D j) := by
  letI : Module D.localCoefficient (maximalIdeal (coefficient R j.1)) :=
    maximalIdealModule R j
  exact (localSystemMaximalIdealAddEquiv D j).module D.localCoefficient

/-- Transition between wrapped maximal ideals in the local coefficient system. -/
noncomputable def localSystemMaximalIdealTransition
    (D : PolynomialModel R σ M)
    (j k : Later R D.localIndex) (h : j ≤ k) :
    LocalSystemMaximalIdeal D j →ₗ[D.localCoefficient]
      LocalSystemMaximalIdeal D k := by
  letI : Module D.localCoefficient (maximalIdeal (coefficient R j.1)) :=
    maximalIdealModule R j
  letI : Module D.localCoefficient (maximalIdeal (coefficient R k.1)) :=
    maximalIdealModule R k
  exact ((localSystemMaximalIdealAddEquiv D k).linearEquiv
      D.localCoefficient).symm.toLinearMap.comp <|
    (maximalIdealTransition R j k h).comp <|
      (localSystemMaximalIdealAddEquiv D j).linearEquiv
        D.localCoefficient |>.toLinearMap

@[simp]
theorem localSystemMaximalIdealTransition_val
    (D : PolynomialModel R σ M)
    (j k : Later R D.localIndex) (h : j ≤ k)
    (x : LocalSystemMaximalIdeal D j) :
    (D.localSystemMaximalIdealTransition j k h x).val =
      maximalIdealTransition R j k h x.val := rfl

/-- The wrapped maximal ideals form a directed system over the initial coefficient ring. -/
noncomputable instance localSystemMaximalIdealDirectedSystem
    (D : PolynomialModel R σ M) :
    DirectedSystem
      (fun j : Later R D.localIndex ↦ LocalSystemMaximalIdeal D j)
      (fun j k h ↦ D.localSystemMaximalIdealTransition j k h) where
  map_self {j} x := by
    apply LocalSystemMaximalIdeal.ext
    apply Subtype.ext
    exact DirectedSystem.map_self' (transition R) x.val.1
  map_map {l k j} hjk hkl x := by
    apply LocalSystemMaximalIdeal.ext
    apply Subtype.ext
    exact DirectedSystem.map_map' (transition R) hjk hkl x.val.1

/-- Right-oriented ideal tensors of the fixed initial model.  This orientation carries the
initial polynomial-ring action on the first tensor factor. -/
abbrev localSystemTensorObstruction (D : PolynomialModel R σ M)
    (j : Later R D.localIndex) :=
  D.localModelModule ⊗[D.localCoefficient] LocalSystemMaximalIdeal D j

/-- The actual tensor source of ideal multiplication at a later stage is additively
equivalent to the fixed-model obstruction tensor. -/
noncomputable def localSystemTensorObstructionEquiv
    (D : PolynomialModel R σ M) (j : Later R D.localIndex) :
    D.localSystemStage j ⊗[coefficient R j.1]
        (maximalIdeal (coefficient R j.1)) ≃+
      D.localSystemTensorObstruction j := by
  letI : Module D.localCoefficient (maximalIdeal (coefficient R j.1)) :=
    maximalIdealModule R j
  exact (TensorProduct.comm (coefficient R j.1) (D.localSystemStage j)
      (maximalIdeal (coefficient R j.1))).toAddEquiv.trans <|
    (D.localSystemIdealTensorEquiv j).toAddEquiv.trans <|
      (TensorProduct.comm D.localCoefficient
        (maximalIdeal (coefficient R j.1)) D.localModelModule).toAddEquiv.trans <|
        (LinearEquiv.lTensor D.localModelModule
          ((localSystemMaximalIdealAddEquiv D j).linearEquiv
            D.localCoefficient).symm).toAddEquiv

@[simp]
theorem localSystemTensorObstructionEquiv_one_tmul_tmul
    (D : PolynomialModel R σ M) (j : Later R D.localIndex)
    (x : D.localModelModule) (a : maximalIdeal (coefficient R j.1)) :
    D.localSystemTensorObstructionEquiv j
        (((1 : polynomial R σ j) ⊗ₜ x) ⊗ₜ a) =
      x ⊗ₜ (localSystemMaximalIdealAddEquiv D j).symm a := by
  simp [localSystemTensorObstructionEquiv]

/-- The underlying initial-coefficient-linear transition of the obstruction tensors. -/
noncomputable def localSystemTensorObstructionTransitionBase
    (D : PolynomialModel R σ M)
    (j k : Later R D.localIndex) (h : j ≤ k) :
    D.localSystemTensorObstruction j →ₗ[D.localCoefficient]
      D.localSystemTensorObstruction k :=
  LinearMap.lTensor D.localModelModule
    (D.localSystemMaximalIdealTransition j k h)

/-- The coefficient-linear obstruction tensors form a directed system. -/
noncomputable instance localSystemTensorObstructionDirectedSystemBase
    (D : PolynomialModel R σ M) :
    DirectedSystem (fun j : Later R D.localIndex ↦ D.localSystemTensorObstruction j)
      (fun j k h ↦ D.localSystemTensorObstructionTransitionBase j k h) := by
  change DirectedSystem
    (fun j : Later R D.localIndex ↦
      D.localModelModule ⊗[D.localCoefficient]
        LocalSystemMaximalIdeal D j)
    (fun j k h ↦ LinearMap.lTensor D.localModelModule
      (D.localSystemMaximalIdealTransition j k h))
  infer_instance

/-- The obstruction-tensor transition is linear over the initial polynomial ring. -/
noncomputable def localSystemTensorObstructionTransition
    (D : PolynomialModel R σ M)
    (j k : Later R D.localIndex) (h : j ≤ k) :
    D.localSystemTensorObstruction j →ₗ[MvPolynomial σ D.localCoefficient]
      D.localSystemTensorObstruction k where
  toFun := D.localSystemTensorObstructionTransitionBase j k h
  map_add' := map_add _
  map_smul' p x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [smul_add, map_add, hx, hy]
    | tmul m a => rfl

/-- The right-oriented obstruction tensors form a polynomial-linear directed system. -/
noncomputable instance localSystemTensorObstructionDirectedSystem
    (D : PolynomialModel R σ M) :
    DirectedSystem (fun j : Later R D.localIndex ↦ D.localSystemTensorObstruction j)
      (fun j k h ↦ D.localSystemTensorObstructionTransition j k h) where
  map_self {j} x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add, hx, hy]
    | tmul m a =>
        change m ⊗ₜ D.localSystemMaximalIdealTransition j j le_rfl a = m ⊗ₜ a
        congr 1
        exact DirectedSystem.map_self'
          (D.localSystemMaximalIdealTransition) a
  map_map {l k j} hjk hkl x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add, hx, hy]
    | tmul m a =>
        change m ⊗ₜ D.localSystemMaximalIdealTransition k l hkl
            (D.localSystemMaximalIdealTransition j k hjk a) =
          m ⊗ₜ D.localSystemMaximalIdealTransition j l (hjk.trans hkl) a
        congr 1
        exact DirectedSystem.map_map'
          (D.localSystemMaximalIdealTransition) hjk hkl a

/-- Forgetting the wrapper is linear for the initial coefficient action. -/
noncomputable def localSystemMaximalIdealLinearEquiv
    (D : PolynomialModel R σ M) (j : Later R D.localIndex) :
    LocalSystemMaximalIdeal D j ≃ₗ[D.localCoefficient]
      maximalIdeal (coefficient R j.1) := by
  letI : Module D.localCoefficient (maximalIdeal (coefficient R j.1)) :=
    maximalIdealModule R j
  exact (localSystemMaximalIdealAddEquiv D j).linearEquiv
    D.localCoefficient

theorem localSystemMaximalIdealLinearEquiv_transition
    (D : PolynomialModel R σ M)
    (i j : Later R D.localIndex) (h : i ≤ j) :
    D.localSystemMaximalIdealLinearEquiv j ∘ₗ
        D.localSystemMaximalIdealTransition i j h =
      maximalIdealTransition R i j h ∘ₗ
        D.localSystemMaximalIdealLinearEquiv i := by
  ext x
  rfl

/-- The direct limit of the wrapped maximal ideals is the maximal ideal of the original
local ring. -/
noncomputable def localSystemMaximalIdealLimitEquiv
    (D : PolynomialModel R σ M) :
    Module.DirectLimit
      (fun j : Later R D.localIndex ↦ LocalSystemMaximalIdeal D j)
      (fun j k h ↦ D.localSystemMaximalIdealTransition j k h) ≃ₗ[
        D.localCoefficient] maximalIdeal R :=
  (Module.DirectLimit.congr
      (f := fun j k h ↦ D.localSystemMaximalIdealTransition j k h)
      (f' := fun j k h ↦ maximalIdealTransition R j k h)
      (fun j ↦ D.localSystemMaximalIdealLinearEquiv j)
      D.localSystemMaximalIdealLinearEquiv_transition) ≪≫ₗ
    maximalIdealLimitEquiv R D.localIndex

@[simp]
theorem localSystemMaximalIdealLimitEquiv_of
    (D : PolynomialModel R σ M) (j : Later R D.localIndex)
    (a : LocalSystemMaximalIdeal D j) :
    D.localSystemMaximalIdealLimitEquiv
        (Module.DirectLimit.of
          D.localCoefficient (Later R D.localIndex)
          (fun k : Later R D.localIndex ↦ LocalSystemMaximalIdeal D k)
          (fun k l h ↦ D.localSystemMaximalIdealTransition k l h) j a) =
      maximalIdealToLimit R j a.val := by
  rw [localSystemMaximalIdealLimitEquiv, LinearEquiv.trans_apply,
    Module.DirectLimit.congr_apply_of]
  change maximalIdealLimitMap R D.localIndex
      (Module.DirectLimit.of
        D.localCoefficient (Later R D.localIndex)
        (fun k : Later R D.localIndex ↦ maximalIdeal (coefficient R k.1))
        (fun k l h ↦ maximalIdealTransition R k l h) j a.val) = _
  rw [maximalIdealLimitMap, Module.DirectLimit.lift_of]

/-- The same obstruction system, viewed over the initial coefficient ring, has limit the
initial model tensored with the maximal ideal of the original local ring. -/
noncomputable def localSystemTensorObstructionLimitEquivBase
    (D : PolynomialModel R σ M) :
    Module.DirectLimit
        (fun j : Later R D.localIndex ↦ D.localSystemTensorObstruction j)
        (fun j k h ↦ D.localSystemTensorObstructionTransitionBase j k h) ≃ₗ[
          D.localCoefficient]
      D.localModelModule ⊗[D.localCoefficient] (maximalIdeal R) :=
  (TensorProduct.directLimitRight
      (fun j k h ↦ D.localSystemMaximalIdealTransition j k h)
      D.localModelModule).symm ≪≫ₗ
    LinearEquiv.lTensor D.localModelModule
      D.localSystemMaximalIdealLimitEquiv

@[simp]
theorem localSystemTensorObstructionLimitEquivBase_of_tmul
    (D : PolynomialModel R σ M) (j : Later R D.localIndex)
    (x : D.localModelModule) (a : LocalSystemMaximalIdeal D j) :
    D.localSystemTensorObstructionLimitEquivBase
        (Module.DirectLimit.of
          D.localCoefficient (Later R D.localIndex)
          (fun k : Later R D.localIndex ↦ D.localSystemTensorObstruction k)
          (fun k l h ↦ D.localSystemTensorObstructionTransitionBase k l h)
          j (x ⊗ₜ a)) =
      x ⊗ₜ maximalIdealToLimit R j a.val := by
  change
    ((TensorProduct.directLimitRight
        (fun j k h ↦ D.localSystemMaximalIdealTransition j k h)
        D.localModelModule).symm ≪≫ₗ
      LinearEquiv.lTensor D.localModelModule
        D.localSystemMaximalIdealLimitEquiv)
      (Module.DirectLimit.of
        D.localCoefficient (Later R D.localIndex)
        (fun k : Later R D.localIndex ↦
          D.localModelModule ⊗[D.localCoefficient]
            LocalSystemMaximalIdeal D k)
        (fun k l h ↦ LinearMap.lTensor D.localModelModule
          (D.localSystemMaximalIdealTransition k l h)) j (x ⊗ₜ a)) = _
  rw [LinearEquiv.trans_apply, TensorProduct.directLimitRight_symm_of_tmul,
    LinearEquiv.lTensor_tmul]
  rw [localSystemMaximalIdealLimitEquiv_of]

/-- The initial obstruction tensor maps to the limiting maximal-ideal tensor. -/
noncomputable def localInitialMaximalIdealToLimit
    (D : PolynomialModel R σ M) :
    maximalIdeal D.localCoefficient →ₗ[D.localCoefficient] maximalIdeal R where
  toFun x := ⟨LocalNoetherianApproximation.toLimit R D.localIndex x.1,
    map_nonunit (LocalNoetherianApproximation.toLimit R D.localIndex) x.1 x.2⟩
  map_add' x y := by ext; simp
  map_smul' a x := by ext; exact map_mul _ _ _

/-- The initial obstruction tensor maps to the limiting maximal-ideal tensor. -/
noncomputable def localSystemTensorObstructionInitialToLimit
    (D : PolynomialModel R σ M) :
    D.localModelModule ⊗[D.localCoefficient]
        (maximalIdeal D.localCoefficient) →ₗ[D.localCoefficient]
      D.localModelModule ⊗[D.localCoefficient] (maximalIdeal R) :=
  LinearMap.lTensor D.localModelModule
    D.localInitialMaximalIdealToLimit

/-- The natural initial tensor maps canonically to the first object of the coefficient
system.  The balancing check uses that the self-transition is the identity. -/
noncomputable def localInitialMaximalIdealToSystem
    (D : PolynomialModel R σ M) :
    maximalIdeal D.localCoefficient →ₗ[D.localCoefficient]
      LocalSystemMaximalIdeal D (initialLater R D.localIndex) where
  toFun a := ⟨⟨a.1, a.2⟩⟩
  map_add' a b := by
    apply LocalSystemMaximalIdeal.ext
    apply Subtype.ext
    rfl
  map_smul' b a := by
    apply LocalSystemMaximalIdeal.ext
    apply Subtype.ext
    simp only [localSystemMaximalIdealModule, Equiv.smul_def,
      localSystemMaximalIdealAddEquiv]
    change b * a.1 = transition R D.localIndex D.localIndex le_rfl b * a.1
    rw [DirectedSystem.map_self']

/-- The natural initial tensor maps canonically to the first object of the coefficient
system. -/
noncomputable def localInitialTensorToSystemBase
    (D : PolynomialModel R σ M) :
    D.localModelModule ⊗[D.localCoefficient]
        (maximalIdeal D.localCoefficient) →ₗ[D.localCoefficient]
      D.localSystemTensorObstruction (initialLater R D.localIndex) :=
  LinearMap.lTensor D.localModelModule D.localInitialMaximalIdealToSystem

/-- The initial-tensor map is linear over the initial polynomial ring. -/
noncomputable def localInitialTensorToSystem
    (D : PolynomialModel R σ M) :
    D.localModelModule ⊗[D.localCoefficient]
        (maximalIdeal D.localCoefficient) →ₗ[
          MvPolynomial σ D.localCoefficient]
      D.localSystemTensorObstruction (initialLater R D.localIndex) where
  toFun := D.localInitialTensorToSystemBase
  map_add' := map_add _
  map_smul' p z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [smul_add, map_add, hx, hy]
    | tmul x a => rfl

@[simp]
theorem localInitialTensorToSystem_tmul
    (D : PolynomialModel R σ M)
    (x : D.localModelModule) (a : maximalIdeal D.localCoefficient) :
    D.localInitialTensorToSystem (x ⊗ₜ a) =
      x ⊗ₜ D.localInitialMaximalIdealToSystem a := rfl

/-- Coefficient-ring scalar extension of the initial local model recovers the original
polynomial module. -/
noncomputable def localCoefficientBaseChangeEquiv
    (D : PolynomialModel R σ M) :
    letI : Algebra D.localCoefficient R := D.localCoefficientAlgebra
    letI : Module R M := Module.compHom M
      (algebraMap R (MvPolynomial σ R))
    R ⊗[D.localCoefficient] D.localModelModule ≃ₗ[R] M := by
  letI : Algebra D.localCoefficient R := D.localCoefficientAlgebra
  letI : Module R M := Module.compHom M
    (algebraMap R (MvPolynomial σ R))
  letI : IsScalarTower R (MvPolynomial σ R) M :=
    IsScalarTower.of_compHom R (MvPolynomial σ R) M
  letI : Algebra (MvPolynomial σ D.localCoefficient) (MvPolynomial σ R) :=
    MvPolynomial.algebraMvPolynomial
  letI : IsScalarTower D.localCoefficient
      (MvPolynomial σ D.localCoefficient) (MvPolynomial σ R) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change MvPolynomial.C
          (LocalNoetherianApproximation.toLimit R D.localIndex x) =
        MvPolynomial.map (LocalNoetherianApproximation.toLimit R D.localIndex)
          (MvPolynomial.C x)
      simp
  letI : IsScalarTower R (MvPolynomial σ R)
      ((MvPolynomial σ R) ⊗[MvPolynomial σ D.localCoefficient]
        D.localModelModule) :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      induction x with
      | zero => rw [TensorProduct.smul_zero, TensorProduct.smul_zero]
      | add x y hx hy =>
          rw [TensorProduct.smul_add, TensorProduct.smul_add, hx, hy]
      | tmul s m => simp [Algebra.smul_def, TensorProduct.smul_tmul']
  exact (Algebra.IsPushout.cancelBaseChange D.localCoefficient R
      (MvPolynomial σ D.localCoefficient) (MvPolynomial σ R)
      D.localModelModule).symm.trans
    (D.localBaseChangeEquiv.restrictScalars R)

@[simp]
theorem localCoefficientBaseChangeEquiv_one_tmul
    (D : PolynomialModel R σ M) (x : D.localModelModule) :
    letI : Algebra D.localCoefficient R := D.localCoefficientAlgebra
    letI : Module R M := Module.compHom M
      (algebraMap R (MvPolynomial σ R))
    D.localCoefficientBaseChangeEquiv ((1 : R) ⊗ₜ x) =
      D.localBaseChangeEquiv ((1 : MvPolynomial σ R) ⊗ₜ x) := by
  letI : Algebra D.localCoefficient R := D.localCoefficientAlgebra
  letI : Module R M := Module.compHom M
    (algebraMap R (MvPolynomial σ R))
  letI : IsScalarTower R (MvPolynomial σ R) M :=
    IsScalarTower.of_compHom R (MvPolynomial σ R) M
  letI : Algebra (MvPolynomial σ D.localCoefficient) (MvPolynomial σ R) :=
    MvPolynomial.algebraMvPolynomial
  letI : IsScalarTower D.localCoefficient
      (MvPolynomial σ D.localCoefficient) (MvPolynomial σ R) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change MvPolynomial.C
          (LocalNoetherianApproximation.toLimit R D.localIndex x) =
        MvPolynomial.map (LocalNoetherianApproximation.toLimit R D.localIndex)
          (MvPolynomial.C x)
      simp
  letI : IsScalarTower R (MvPolynomial σ R)
      ((MvPolynomial σ R) ⊗[MvPolynomial σ D.localCoefficient]
        D.localModelModule) :=
    IsScalarTower.of_algebraMap_smul fun a z ↦ by
      induction z with
      | zero => rw [TensorProduct.smul_zero, TensorProduct.smul_zero]
      | add z w hz hw =>
          rw [TensorProduct.smul_add, TensorProduct.smul_add, hz, hw]
      | tmul s m => simp [Algebra.smul_def, TensorProduct.smul_tmul']
  change ((Algebra.IsPushout.cancelBaseChange D.localCoefficient R
      (MvPolynomial σ D.localCoefficient) (MvPolynomial σ R)
      D.localModelModule).symm.trans
    (D.localBaseChangeEquiv.restrictScalars R)) ((1 : R) ⊗ₜ x) = _
  rw [LinearEquiv.trans_apply, Algebra.IsPushout.cancelBaseChange_symm_tmul]
  simp

/-- The limiting obstruction tensor is the actual maximal-ideal tensor of the original
module. -/
noncomputable def localSystemTensorObstructionTargetEquiv
    (D : PolynomialModel R σ M) :
    letI : Algebra D.localCoefficient R := D.localCoefficientAlgebra
    letI : Module R M := Module.compHom M
      (algebraMap R (MvPolynomial σ R))
    D.localModelModule ⊗[D.localCoefficient] (maximalIdeal R) ≃+
      M ⊗[R] (maximalIdeal R) := by
  letI : Algebra D.localCoefficient R := D.localCoefficientAlgebra
  letI : Module R M := Module.compHom M
    (algebraMap R (MvPolynomial σ R))
  exact (TensorProduct.comm D.localCoefficient D.localModelModule
      (maximalIdeal R)).toAddEquiv.trans <|
    (AlgebraTensorModule.cancelBaseChange D.localCoefficient R R
      (maximalIdeal R) D.localModelModule).symm.toAddEquiv.trans <|
      (LinearEquiv.lTensor (maximalIdeal R)
        D.localCoefficientBaseChangeEquiv).toAddEquiv.trans <|
        (TensorProduct.comm R (maximalIdeal R) M).toAddEquiv

@[simp]
theorem localSystemTensorObstructionTargetEquiv_tmul
    (D : PolynomialModel R σ M)
    (x : D.localModelModule) (a : maximalIdeal R) :
    letI : Algebra D.localCoefficient R := D.localCoefficientAlgebra
    letI : Module R M := Module.compHom M
      (algebraMap R (MvPolynomial σ R))
    D.localSystemTensorObstructionTargetEquiv (x ⊗ₜ a) =
      D.localCoefficientBaseChangeEquiv ((1 : R) ⊗ₜ x) ⊗ₜ a := by
  letI : Algebra D.localCoefficient R := D.localCoefficientAlgebra
  letI : Module R M := Module.compHom M
    (algebraMap R (MvPolynomial σ R))
  simp [localSystemTensorObstructionTargetEquiv]

/-- For an obstruction tensor at the initial local stage, multiplication after passage to
the original ring is coefficient base change of its initial multiplication. -/
theorem tensorMul_localSystemTensorObstructionTargetEquiv_initial
    (D : PolynomialModel R σ M)
    (z : D.localModelModule ⊗[D.localCoefficient]
      (maximalIdeal D.localCoefficient)) :
    letI : Algebra D.localCoefficient R := D.localCoefficientAlgebra
    letI : Module R M := Module.compHom M
      (algebraMap R (MvPolynomial σ R))
    Ideal.tensorMul (R := R) (S := R) (M := M) (maximalIdeal R)
        (D.localSystemTensorObstructionTargetEquiv
          (D.localSystemTensorObstructionInitialToLimit z)) =
      D.localCoefficientBaseChangeEquiv
        ((1 : R) ⊗ₜ
          Ideal.tensorMul (R := D.localCoefficient)
            (S := MvPolynomial σ D.localCoefficient)
            (M := D.localModelModule) (maximalIdeal D.localCoefficient) z) := by
  letI : Algebra D.localCoefficient R := D.localCoefficientAlgebra
  letI : Module R M := Module.compHom M
    (algebraMap R (MvPolynomial σ R))
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (.+.) hx hy
  | tmul x a =>
      rw [show D.localSystemTensorObstructionInitialToLimit (x ⊗ₜ a) =
          x ⊗ₜ D.localInitialMaximalIdealToLimit a by rfl]
      rw [localSystemTensorObstructionTargetEquiv_tmul,
        Ideal.tensorMul_tmul, Ideal.tensorMul_tmul]
      rw [← map_smul]
      congr 1
      rw [TensorProduct.tmul_smul]
      rfl

/-- The finite ideal-multiplication obstruction at the initial local Noetherian stage. -/
noncomputable abbrev localInitialTensorKernel (D : PolynomialModel R σ M) :=
  LinearMap.ker
    (Ideal.tensorMul (R := D.localCoefficient)
      (S := MvPolynomial σ D.localCoefficient)
      (M := D.localModelModule) (maximalIdeal D.localCoefficient))

/-- The initial ideal-multiplication obstruction is finite over the initial polynomial
ring. -/
theorem localInitialTensorKernel_finite [Finite σ]
    (D : PolynomialModel R σ M) :
    Module.Finite (MvPolynomial σ D.localCoefficient)
      D.localInitialTensorKernel := by
  letI : Module.FinitePresentation
      (MvPolynomial σ D.localCoefficient) D.localModelModule :=
    D.localModelModule_finitePresentation
  exact Ideal.finite_ker_tensorMul (maximalIdeal D.localCoefficient)

/-- The initial obstruction included in the first term of the fixed tensor system. -/
noncomputable def localInitialTensorKernelMap (D : PolynomialModel R σ M) :
    D.localInitialTensorKernel →ₗ[MvPolynomial σ D.localCoefficient]
      D.localSystemTensorObstruction (initialLater R D.localIndex) :=
  D.localInitialTensorToSystem.comp
    (Ideal.tensorMul (R := D.localCoefficient)
      (S := MvPolynomial σ D.localCoefficient)
      (M := D.localModelModule) (maximalIdeal D.localCoefficient)).ker.subtype

/-- On the initial stage, the coefficient-linear colimit equivalence is the explicit map
to the limiting maximal-ideal tensor. -/
theorem localSystemTensorObstructionLimitEquivBase_of_initial
    (D : PolynomialModel R σ M)
    (z : D.localModelModule ⊗[D.localCoefficient]
      (maximalIdeal D.localCoefficient)) :
    D.localSystemTensorObstructionLimitEquivBase
        (Module.DirectLimit.of
          D.localCoefficient (Later R D.localIndex)
          (fun k : Later R D.localIndex ↦ D.localSystemTensorObstruction k)
          (fun k l h ↦ D.localSystemTensorObstructionTransitionBase k l h)
          (initialLater R D.localIndex) (D.localInitialTensorToSystem z)) =
      D.localSystemTensorObstructionInitialToLimit z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add, hx, hy]
  | tmul x a =>
      rw [localInitialTensorToSystem_tmul,
        localSystemTensorObstructionLimitEquivBase_of_tmul]
      rfl

/-- If the original polynomial module is flat over the local base, every element of the
initial ideal-multiplication obstruction dies at some later Noetherian coefficient stage. -/
theorem localInitialTensorKernel_eventually_zero
    (D : PolynomialModel R σ M)
    (hflat :
      letI : Module R M := Module.compHom M
        (algebraMap R (MvPolynomial σ R))
      Module.Flat R M)
    (x : D.localInitialTensorKernel) :
    ∃ j : Later R D.localIndex,
      ∃ hij : initialLater R D.localIndex ≤ j,
        D.localSystemTensorObstructionTransitionBase
          (initialLater R D.localIndex) j hij
            (D.localInitialTensorKernelMap x) = 0 := by
  letI : Algebra D.localCoefficient R := D.localCoefficientAlgebra
  letI : Module R M := Module.compHom M
    (algebraMap R (MvPolynomial σ R))
  letI : Module.Flat R M := hflat
  have hmul : Function.Injective
      (Ideal.tensorMul (R := R) (S := R) (M := M) (maximalIdeal R)) := by
    rw [Ideal.tensorMul_injective_iff_rTensor_injective]
    exact Module.Flat.rTensor_preserves_injective_linearMap
      (M := M) (maximalIdeal R).subtype Subtype.val_injective
  have htarget : D.localSystemTensorObstructionTargetEquiv
      (D.localSystemTensorObstructionInitialToLimit x.1) = 0 := by
    apply hmul
    rw [tensorMul_localSystemTensorObstructionTargetEquiv_initial]
    rw [x.2, TensorProduct.tmul_zero, map_zero]
    simp
  have hlimitTarget : D.localSystemTensorObstructionInitialToLimit x.1 = 0 :=
    D.localSystemTensorObstructionTargetEquiv.injective
      (by simpa using htarget)
  have hlimit : Module.DirectLimit.of
      D.localCoefficient (Later R D.localIndex)
      (fun k : Later R D.localIndex ↦ D.localSystemTensorObstruction k)
      (fun k l h ↦ D.localSystemTensorObstructionTransitionBase k l h)
      (initialLater R D.localIndex) (D.localInitialTensorKernelMap x) = 0 := by
    apply D.localSystemTensorObstructionLimitEquivBase.injective
    change D.localSystemTensorObstructionLimitEquivBase
        (Module.DirectLimit.of
          D.localCoefficient (Later R D.localIndex)
          (fun k : Later R D.localIndex ↦ D.localSystemTensorObstruction k)
          (fun k l h ↦ D.localSystemTensorObstructionTransitionBase k l h)
          (initialLater R D.localIndex)
          (D.localInitialTensorToSystem x.1)) =
      D.localSystemTensorObstructionLimitEquivBase 0
    rw [localSystemTensorObstructionLimitEquivBase_of_initial, hlimitTarget, map_zero]
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hlimit
  exact ⟨j, hij, hj⟩

/-- If the original polynomial module is flat over the local base, the entire finite initial
ideal-multiplication obstruction dies at one later Noetherian coefficient stage. -/
theorem exists_later_localInitialTensorKernelMap_eq_zero [Finite σ]
    (D : PolynomialModel R σ M)
    (hflat :
      letI : Module R M := Module.compHom M
        (algebraMap R (MvPolynomial σ R))
      Module.Flat R M) :
    ∃ j : Later R D.localIndex,
      ∃ hij : initialLater R D.localIndex ≤ j,
        (D.localSystemTensorObstructionTransition
          (initialLater R D.localIndex) j hij).comp
            D.localInitialTensorKernelMap = 0 := by
  letI : Module.Finite (MvPolynomial σ D.localCoefficient)
      D.localInitialTensorKernel := D.localInitialTensorKernel_finite
  apply Module.DirectLimit.exists_later_comp_eq_zero_of_finite_of_eventually
    (R := MvPolynomial σ D.localCoefficient)
    (G := fun j : Later R D.localIndex ↦ D.localSystemTensorObstruction j)
    (f := fun j k h ↦ D.localSystemTensorObstructionTransition j k h)
    (N := D.localInitialTensorKernel)
    (i := initialLater R D.localIndex) (g := D.localInitialTensorKernelMap)
  intro x
  obtain ⟨j, hij, hx⟩ := D.localInitialTensorKernel_eventually_zero hflat x
  exact ⟨j, hij, hx⟩

end Module.FinitePresentation.PolynomialModel
