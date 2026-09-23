module

public import StacksAndModuli.API.LocalNoetherianCoefficientSystem
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Polynomial modules over the local Noetherian coefficient system

Fix a local ring `R` and one local Noetherian coefficient stage `i`.  The stages later than
`i` form a directed cofinal subsystem.  Their polynomial rings are algebras over the
polynomial ring at `i`, and their direct limit is the polynomial ring over `R`.  Consequently,
for every module `N` over the polynomial ring at `i`, the direct limit of its scalar
extensions to the later polynomial stages is canonically its scalar extension to `R`.

This is the simultaneous ring-and-module colimit layer needed in the local approximation
argument of Stacks Project tags 00QX and 00R6.
-/

@[expose] public section

open TensorProduct

universe u v w

namespace LocalNoetherianApproximation

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The cofinal subsystem of coefficient stages later than a fixed stage. -/
abbrev Later (i : Index R) := {j : Index R // i ≤ j}

instance (i : Index R) : Nonempty (Later R i) := ⟨⟨i, le_rfl⟩⟩

noncomputable instance (i : Index R) : DecidableEq (Later R i) := Classical.decEq _

instance (i : Index R) : IsDirectedOrder (Later R i) where
  directed a b := by
    obtain ⟨c, hac, hbc⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨c, a.2.trans hac⟩, hac, hbc⟩

/-- The polynomial ring at a later coefficient stage. -/
abbrev polynomial (σ : Type v) {i : Index R} (j : Later R i) : Type max u v :=
  MvPolynomial σ (coefficient R j.1)

/-- The polynomial ring at the fixed initial coefficient stage. -/
abbrev initialPolynomial (σ : Type v) (i : Index R) : Type max u v :=
  MvPolynomial σ (coefficient R i)

/-- Transition between polynomial rings in the later coefficient system. -/
noncomputable def polynomialTransition (σ : Type v) {i : Index R}
    (j k : Later R i) (h : j ≤ k) : polynomial R σ j →+* polynomial R σ k :=
  MvPolynomial.map (transition R j.1 k.1 h)

instance polynomialDirectedSystem (σ : Type v) (i : Index R) :
    DirectedSystem (fun j : Later R i ↦ polynomial R σ j)
      (fun (j k : Later R i) h ↦ polynomialTransition R σ j k h) where
  map_self {j} x := by
    have hcoeff : transition R j.1 j.1 le_rfl = RingHom.id _ := by
      apply RingHom.ext
      intro y
      exact DirectedSystem.map_self' (transition R) y
    rw [polynomialTransition, hcoeff]
    exact MvPolynomial.map_id x
  map_map {l k j} hjk hkl x := by
    have hcoeff : (transition R k.1 l.1 hkl).comp
        (transition R j.1 k.1 hjk) = transition R j.1 l.1 (hjk.trans hkl) := by
      apply RingHom.ext
      intro y
      exact DirectedSystem.map_map' (f := transition R) hjk hkl y
    rw [polynomialTransition, polynomialTransition, polynomialTransition,
      MvPolynomial.map_map, hcoeff]

/-- The initial object of the later-stage subsystem. -/
abbrev initialLater (i : Index R) : Later R i := ⟨i, le_rfl⟩

/-- Every later coefficient ring is an algebra over the fixed initial stage. -/
@[instance_reducible]
noncomputable instance coefficientAlgebra {i : Index R} (j : Later R i) :
    Algebra (coefficient R i) (coefficient R j.1) :=
  (transition R i j.1 j.2).toAlgebra

/-- Every later polynomial ring is canonically an algebra over the initial polynomial ring. -/
@[instance_reducible]
noncomputable instance polynomialAlgebra (σ : Type v) {i : Index R} (j : Later R i) :
    Algebra (initialPolynomial R σ i) (polynomial R σ j) :=
  MvPolynomial.algebraMvPolynomial

/-- The coefficient inclusion and polynomial base-change map form the expected scalar
tower. -/
noncomputable instance coefficientPolynomialTower (σ : Type v) {i : Index R}
    (j : Later R i) :
    IsScalarTower (coefficient R i) (initialPolynomial R σ i)
      (polynomial R σ j) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    change MvPolynomial.C (transition R i j.1 j.2 x) =
      MvPolynomial.map (transition R i j.1 j.2) (MvPolynomial.C x)
    simp

/-- Polynomial transition, regarded as a linear map over the initial polynomial ring. -/
noncomputable def polynomialTransitionLinear (σ : Type v) {i : Index R}
    (j k : Later R i) (h : j ≤ k) :
    polynomial R σ j →ₗ[initialPolynomial R σ i] polynomial R σ k where
  toFun := MvPolynomial.map (transition R j.1 k.1 h)
  map_add' x y := map_add (MvPolynomial.map (transition R j.1 k.1 h)) x y
  map_smul' c x := by
    have hcoeff : (transition R j.1 k.1 h).comp (transition R i j.1 j.2) =
        transition R i k.1 k.2 := by
      apply RingHom.ext
      intro y
      exact DirectedSystem.map_map' (transition R) j.2 h y
    change MvPolynomial.map (transition R j.1 k.1 h)
        (MvPolynomial.map (transition R i j.1 j.2) c * x) =
      MvPolynomial.map (transition R i k.1 k.2) c *
        MvPolynomial.map (transition R j.1 k.1 h) x
    rw [map_mul, MvPolynomial.map_map, hcoeff]

instance polynomialModuleDirectedSystem (σ : Type v) (i : Index R) :
    DirectedSystem (fun j : Later R i ↦ polynomial R σ j)
      (fun (j k : Later R i) h ↦ polynomialTransitionLinear R σ j k h) where
  map_self {j} x := DirectedSystem.map_self'
    (fun (a b : Later R i) hab ↦ polynomialTransition R σ a b hab) x
  map_map {l k j} hjk hkl x := DirectedSystem.map_map'
    (fun (a b : Later R i) hab ↦ polynomialTransition R σ a b hab) hjk hkl x

/-- The polynomial ring over the original local ring, as an algebra over the initial
polynomial stage. -/
@[instance_reducible]
noncomputable instance targetPolynomialAlgebra (σ : Type v) (i : Index R) :
    Algebra (initialPolynomial R σ i) (MvPolynomial σ R) :=
  (MvPolynomial.map (toLimit R i)).toAlgebra

/-- The map to the limit polynomial ring, regarded as linear over the initial stage. -/
noncomputable def polynomialToLimitLinear (σ : Type v) {i : Index R} (j : Later R i) :
    polynomial R σ j →ₗ[initialPolynomial R σ i] MvPolynomial σ R where
  toFun := MvPolynomial.map (toLimit R j.1)
  map_add' x y := map_add (MvPolynomial.map (toLimit R j.1)) x y
  map_smul' c x := by
    have hcoeff : (toLimit R j.1).comp (transition R i j.1 j.2) =
        toLimit R i := by
      apply RingHom.ext
      intro y
      exact toLimit_transition R i j.1 j.2 y
    change MvPolynomial.map (toLimit R j.1)
        (MvPolynomial.map (transition R i j.1 j.2) c * x) =
      MvPolynomial.map (toLimit R i) c * MvPolynomial.map (toLimit R j.1) x
    rw [map_mul, MvPolynomial.map_map, hcoeff]

theorem polynomialToLimit_transition (σ : Type v) {i : Index R}
    (j k : Later R i) (h : j ≤ k) (x : polynomial R σ j) :
    polynomialToLimitLinear R σ k (polynomialTransitionLinear R σ j k h x) =
      polynomialToLimitLinear R σ j x := by
  change MvPolynomial.map (toLimit R k.1)
      (MvPolynomial.map (transition R j.1 k.1 h) x) =
    MvPolynomial.map (toLimit R j.1) x
  have hcoeff : (toLimit R k.1).comp (transition R j.1 k.1 h) =
      toLimit R j.1 := by
    apply RingHom.ext
    intro y
    exact toLimit_transition R j.1 k.1 h y
  rw [MvPolynomial.map_map, hcoeff]

/-- The canonical linear map from the direct limit of the later polynomial rings to the
polynomial ring over `R`. -/
noncomputable def polynomialLimitMap (σ : Type v) (i : Index R) :
    Module.DirectLimit
      (fun j : Later R i ↦ polynomial R σ j)
      (fun j k h ↦ polynomialTransitionLinear R σ j k h) →ₗ[
        initialPolynomial R σ i] MvPolynomial σ R :=
  Module.DirectLimit.lift _ _ _ _
    (fun j ↦ polynomialToLimitLinear R σ j)
    (polynomialToLimit_transition R σ)

theorem polynomialLimitMap_injective (σ : Type v) (i : Index R) :
    Function.Injective (polynomialLimitMap R σ i) := by
  apply Module.DirectLimit.lift_injective
  intro j
  change Function.Injective (MvPolynomial.map (toLimit R j.1))
  exact MvPolynomial.map_injective (toLimit R j.1) (toLimit_injective R j.1)

theorem polynomialLimitMap_surjective (σ : Type v) (i : Index R) :
    Function.Surjective (polynomialLimitMap R σ i) := by
  intro p
  let A : Subalgebra ℤ R :=
    i.1 ⊔ Algebra.adjoin ℤ (p.coeffs : Set R)
  have hA : A.FG :=
    i.2.sup (Subalgebra.fg_adjoin_finset p.coeffs)
  let j₀ : Index R := ⟨A, hA⟩
  have hij : i ≤ j₀ := by
    change i.1 ≤ A
    exact le_sup_left
  let j : Later R i := ⟨j₀, hij⟩
  have hcoeff : (p.coeffs : Set R) ⊆ Set.range (toLimit R j.1) := by
    intro c hc
    have hcA : c ∈ A :=
      (show Algebra.adjoin ℤ (p.coeffs : Set R) ≤ A from le_sup_right)
        (Algebra.subset_adjoin hc)
    let y : j.1.1 := ⟨c, hcA⟩
    refine ⟨ofBase R j.1 y, ?_⟩
    exact toLimit_ofBase R j.1 y
  obtain ⟨q, hq⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hcoeff
  refine ⟨Module.DirectLimit.of
    (initialPolynomial R σ i) (Later R i)
    (fun k : Later R i ↦ polynomial R σ k)
    (fun a b h ↦ polynomialTransitionLinear R σ a b h) j q, ?_⟩
  rw [polynomialLimitMap, Module.DirectLimit.lift_of]
  exact hq

/-- The direct limit of the later polynomial rings is the polynomial ring over the original
local ring. -/
noncomputable def polynomialLimitEquiv (σ : Type v) (i : Index R) :
    Module.DirectLimit
      (fun j : Later R i ↦ polynomial R σ j)
      (fun j k h ↦ polynomialTransitionLinear R σ j k h) ≃ₗ[
        initialPolynomial R σ i] MvPolynomial σ R :=
  LinearEquiv.ofBijective (polynomialLimitMap R σ i)
    ⟨polynomialLimitMap_injective R σ i, polynomialLimitMap_surjective R σ i⟩

section ModuleSystem

variable (σ : Type v) (i : Index R)
variable (N : Type w) [AddCommMonoid N] [Module (initialPolynomial R σ i) N]

/-- Scalar extension of an initial polynomial module to a later coefficient stage. -/
abbrev polynomialBaseChange (j : Later R i) : Type max u v w :=
  polynomial R σ j ⊗[initialPolynomial R σ i] N

/-- Transition between the scalar extensions of an initial polynomial module. -/
noncomputable def polynomialBaseChangeTransition (j k : Later R i) (h : j ≤ k) :
    polynomialBaseChange R σ i N j →ₗ[initialPolynomial R σ i]
      polynomialBaseChange R σ i N k :=
  (polynomialTransitionLinear R σ j k h).rTensor N

/-- The scalar extensions of an initial polynomial module form a directed system. -/
noncomputable instance polynomialBaseChangeDirectedSystem :
    DirectedSystem (fun j : Later R i ↦ polynomialBaseChange R σ i N j)
      (fun j k h ↦ polynomialBaseChangeTransition R σ i N j k h) :=
  by
    change DirectedSystem
      (fun j : Later R i ↦ polynomial R σ j ⊗[initialPolynomial R σ i] N)
      (fun j k h ↦ (polynomialTransitionLinear R σ j k h).rTensor N)
    infer_instance

/-- Scalar extension of an initial polynomial module commutes with the cofinal limit of
the Noetherian coefficient stages. -/
noncomputable def polynomialBaseChangeLimitEquiv :
    Module.DirectLimit
      (fun j : Later R i ↦ polynomialBaseChange R σ i N j)
      (fun j k h ↦ polynomialBaseChangeTransition R σ i N j k h) ≃ₗ[
        initialPolynomial R σ i]
      MvPolynomial σ R ⊗[initialPolynomial R σ i] N :=
  (TensorProduct.directLimitLeft
      (fun j k h ↦ polynomialTransitionLinear R σ j k h) N).symm ≪≫ₗ
    (polynomialLimitEquiv R σ i).rTensor N

@[simp]
theorem polynomialBaseChangeLimitEquiv_of_tmul (j : Later R i)
    (p : polynomial R σ j) (x : N) :
    polynomialBaseChangeLimitEquiv R σ i N
        (Module.DirectLimit.of
          (initialPolynomial R σ i) (Later R i)
          (fun k : Later R i ↦ polynomialBaseChange R σ i N k)
          (fun a b h ↦ polynomialBaseChangeTransition R σ i N a b h) j (p ⊗ₜ x)) =
      MvPolynomial.map (toLimit R j.1) p ⊗ₜ x := by
  change
    ((TensorProduct.directLimitLeft
        (fun j k h ↦ polynomialTransitionLinear R σ j k h) N).symm ≪≫ₗ
      (polynomialLimitEquiv R σ i).rTensor N)
        (Module.DirectLimit.of
          (initialPolynomial R σ i) (Later R i)
          (fun k : Later R i ↦
            polynomial R σ k ⊗[initialPolynomial R σ i] N)
          (fun a b h ↦ (polynomialTransitionLinear R σ a b h).rTensor N)
          j (p ⊗ₜ x)) = _
  rw [LinearEquiv.trans_apply, TensorProduct.directLimitLeft_symm_of_tmul,
    LinearEquiv.rTensor_tmul]
  change polynomialLimitMap R σ i
      (Module.DirectLimit.of
        (initialPolynomial R σ i) (Later R i)
        (fun k : Later R i ↦ polynomial R σ k)
        (fun a b h ↦ polynomialTransitionLinear R σ a b h) j p) ⊗ₜ x = _
  rw [polynomialLimitMap, Module.DirectLimit.lift_of]
  rfl

end ModuleSystem

end LocalNoetherianApproximation
