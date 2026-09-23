module

public import StacksAndModuli.API.KernelBaseChange
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Flat.Tensor

/-!
# Kernel forms of local flatness steps

Two elementary kernel arguments isolate the formal linear-algebra content of the local
flatness criteria used in Stacks Project tags 00ML and 00MO.

* a surjective kernel base-change comparison which is the zero map forces the base-changed
  map to be injective;
* injectivity for `I ⊗ M → M` propagates to `J ⊗ M → M` once every element of the latter
  kernel lifts from `I ⊗ M`.

The remaining commutative-algebra input is not asserted here: 00ML obtains the kernel-lifting
hypothesis from flatness modulo `I`, and 00MK converts maximal-ideal tensor injectivity into
flatness for a finite module over a local Noetherian algebra.
-/

@[expose] public section

open TensorProduct

universe u v w

namespace LinearMap

variable {R : Type u} [CommRing R] {M : Type v} {N : Type w}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- If the canonical map from the scalar extension of a kernel onto the kernel after scalar
extension is both surjective and zero, then the scalar-extended map is injective.

This is the final kernel argument in the proof of the local base-change criterion for
flatness: surjectivity comes from the relevant `Tor₁` comparison, while zero is the
finite-stage vanishing condition. -/
theorem baseChange_injective_of_kerBaseChangeHom_surjective_of_eq_zero
    (f : M →ₗ[R] N) (S : Type*) [CommRing S] [Algebra R S]
    (hsurj : Function.Surjective (f.kerBaseChangeHom S))
    (hzero : f.kerBaseChangeHom S = 0) :
    Function.Injective (f.baseChange S) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have hy' := congrArg Subtype.val hy
  rw [hzero] at hy'
  simpa using hy'.symm

/-- Let `I ≤ J` be ideals.  If `I ⊗ M → M` is injective and every element of the kernel of
`J ⊗ M → M` comes from `I ⊗ M`, then `J ⊗ M → M` is injective.

In the variant local criterion, `J` is the maximal ideal and flatness of `M / IM` supplies
the kernel-lifting hypothesis by the equational criterion. -/
theorem injective_rTensor_of_ker_le_range_inclusion
    (I J : Ideal R) (hIJ : I ≤ J)
    (hI : Function.Injective (I.subtype.rTensor M))
    (hker : LinearMap.ker (J.subtype.rTensor M) ≤
      LinearMap.range ((Submodule.inclusion hIJ).rTensor M)) :
    Function.Injective (J.subtype.rTensor M) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hzker : z ∈ LinearMap.ker (J.subtype.rTensor M) :=
    LinearMap.mem_ker.mpr hz
  obtain ⟨w, hw⟩ := hker hzker
  have hcomm : J.subtype.comp (Submodule.inclusion hIJ) = I.subtype := rfl
  have hwzero : (I.subtype.rTensor M) w = 0 := by
    rw [← hcomm, LinearMap.rTensor_comp_apply, hw, hz]
  rw [(injective_iff_map_eq_zero _).mp hI w hwzero] at hw
  simpa using hw.symm

end LinearMap

namespace Ideal

variable {R : Type u} [CommRing R] {M : Type v}
variable [AddCommGroup M] [Module R M]

/-- The explicit equational kernel-lifting condition for ideals `I ≤ J`: every relation
with coefficients in `J` which vanishes in `M` lifts, as a tensor, from `I ⊗ M`.

The equational proof of the variant local criterion establishes this condition for the
inclusion of a proper ideal into the maximal ideal by using flatness of `M / IM`. -/
def TensorKernelLifting (I J : Ideal R) (hIJ : I ≤ J) : Prop :=
  ∀ {n : ℕ} (a : Fin n → J) (x : Fin n → M),
    (∑ i, (a i : R) • x i) = 0 →
      ∃ w : I ⊗[R] M,
        ((Submodule.inclusion hIJ).rTensor M) w = ∑ i, a i ⊗ₜ[R] x i

/-- A tensor with one coefficient in `J` and one vector in `IM` comes from `I ⊗ M`.
This is the elementary balancing step used to turn lifted equations modulo `I` into an
actual tensor-kernel lift. -/
theorem tmul_mem_range_rTensor_inclusion_of_mem_smul
    (I J : Ideal R) (hIJ : I ≤ J) (a : J) {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) :
    a ⊗ₜ[R] x ∈ LinearMap.range ((Submodule.inclusion hIJ).rTensor M) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m hm
    let ra : I := ⟨r * (a : R), I.mul_mem_right (a : R) hr⟩
    refine ⟨ra ⊗ₜ[R] m, ?_⟩
    rw [LinearMap.rTensor_tmul, TensorProduct.tmul_smul]
    change (Submodule.inclusion hIJ ra) ⊗ₜ[R] m = (r • a) ⊗ₜ[R] m
    congr 1
  · intro x y hx hy
    rw [TensorProduct.tmul_add]
    exact Submodule.add_mem _ hx hy

/-- The lifted-equation hypothesis appearing verbatim in the equational proof of the variant
local criterion.  A relation with coefficients in `J` is trivial modulo `I` after choosing
lifts of the factorization coefficients and vectors. -/
def ModuloRelationLifting (I J : Ideal R) : Prop :=
  ∀ {n : ℕ} (a : Fin n → J) (x : Fin n → M),
    (∑ i, (a i : R) • x i) = 0 →
      ∃ (k : ℕ) (c : Fin n → Fin k → R) (y : Fin k → M),
        (∀ i, x i - ∑ j, c i j • y j ∈ I • (⊤ : Submodule R M)) ∧
          ∀ j, ∑ i, (a i : R) * c i j ∈ I

/-- Lifted triviality of all relations modulo `I` implies the tensor-kernel lifting
condition.  This packages the tensor calculation in the equational proof of the variant
local criterion. -/
theorem tensorKernelLifting_of_moduloRelationLifting
    (I J : Ideal R) (hIJ : I ≤ J)
    (hLift : ModuloRelationLifting (M := M) I J) :
    TensorKernelLifting (M := M) I J hIJ := by
  intro n a x hzero
  obtain ⟨k, c, y, hx, hc⟩ := hLift a x hzero
  let b : Fin k → I := fun j => ⟨∑ i, (a i : R) * c i j, hc j⟩
  have hb (j : Fin k) :
      Submodule.inclusion hIJ (b j) = ∑ i, c i j • a i := by
    apply Subtype.ext
    simp [b, mul_comm]
  have heq :
      (∑ i, a i ⊗ₜ[R] x i) =
        (∑ i, a i ⊗ₜ[R] (x i - ∑ j, c i j • y j)) +
          ∑ j, (Submodule.inclusion hIJ (b j)) ⊗ₜ[R] y j := by
    calc
      (∑ i, a i ⊗ₜ[R] x i) =
          ∑ i, ((a i ⊗ₜ[R] (x i - ∑ j, c i j • y j)) +
            a i ⊗ₜ[R] (∑ j, c i j • y j)) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [← TensorProduct.tmul_add, sub_add_cancel]
      _ = (∑ i, a i ⊗ₜ[R] (x i - ∑ j, c i j • y j)) +
          ∑ i, a i ⊗ₜ[R] (∑ j, c i j • y j) := Finset.sum_add_distrib
      _ = (∑ i, a i ⊗ₜ[R] (x i - ∑ j, c i j • y j)) +
          ∑ i, ∑ j, (c i j • a i) ⊗ₜ[R] y j := by
            congr 1
            apply Finset.sum_congr rfl
            intro i hi
            simp_rw [TensorProduct.tmul_sum, TensorProduct.tmul_smul,
              TensorProduct.smul_tmul']
      _ = (∑ i, a i ⊗ₜ[R] (x i - ∑ j, c i j • y j)) +
          ∑ j, ∑ i, (c i j • a i) ⊗ₜ[R] y j := by rw [Finset.sum_comm]
      _ = (∑ i, a i ⊗ₜ[R] (x i - ∑ j, c i j • y j)) +
          ∑ j, (Submodule.inclusion hIJ (b j)) ⊗ₜ[R] y j := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [hb, TensorProduct.sum_tmul]
  rw [heq]
  change _ ∈ LinearMap.range ((Submodule.inclusion hIJ).rTensor M)
  apply Submodule.add_mem
  · exact Submodule.sum_mem _ fun i _ =>
      tmul_mem_range_rTensor_inclusion_of_mem_smul I J hIJ (a i) (hx i)
  · exact Submodule.sum_mem _ fun j _ => ⟨b j ⊗ₜ[R] y j, by simp⟩

/-- Flatness of `M / IM` supplies the lifted-equation hypothesis of the variant local
criterion.  This is the equational-criterion portion of Stacks Project tag 00ML; it does not
use Noetherianity or a local-ring hypothesis. -/
theorem moduloRelationLifting_of_flat_quotient
    (I J : Ideal R)
    [Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] :
    ModuloRelationLifting (M := M) I J := by
  classical
  intro n a x hzero
  let abar : Fin n → (R ⧸ I) := fun i => Ideal.Quotient.mk I (a i : R)
  let xbar : Fin n → (M ⧸ I • (⊤ : Submodule R M)) := fun i =>
    Submodule.Quotient.mk (x i)
  have hbar : ∑ i, abar i • xbar i = 0 := by
    change ∑ i, Submodule.Quotient.mk ((a i : R) • x i) = 0
    simpa only [map_sum, map_zero, Submodule.mkQ_apply] using
      congrArg (I • (⊤ : Submodule R M)).mkQ hzero
  obtain ⟨k, cbar, ybar, hxbar, hcbar⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hbar
  choose c hc using fun i j => Ideal.Quotient.mk_surjective (cbar i j)
  choose y hy using fun j => Submodule.Quotient.mk_surjective
    (I • (⊤ : Submodule R M)) (ybar j)
  refine ⟨k, c, y, ?_, ?_⟩
  · intro i
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
    change xbar i - Submodule.Quotient.mk (∑ j, c i j • y j) = 0
    change xbar i - (I • (⊤ : Submodule R M)).mkQ (∑ j, c i j • y j) = 0
    rw [map_sum]
    simp_rw [Submodule.mkQ_apply, ← Module.Quotient.mk_smul_mk, hc, hy]
    exact sub_eq_zero.mpr (hxbar i)
  · intro j
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sum]
    simp_rw [map_mul, hc]
    exact hcbar j

end Ideal

namespace LinearMap

variable {R : Type u} [CommRing R] {M : Type v}
variable [AddCommGroup M] [Module R M]

/-- The explicit equational kernel-lifting condition upgrades injectivity of
`I ⊗ M → M` to injectivity of `J ⊗ M → M`. -/
theorem injective_rTensor_of_tensorKernelLifting
    (I J : Ideal R) (hIJ : I ≤ J)
    (hI : Function.Injective (I.subtype.rTensor M))
    (hLift : Ideal.TensorKernelLifting (M := M) I J hIJ) :
    Function.Injective (J.subtype.rTensor M) := by
  apply injective_rTensor_of_ker_le_range_inclusion I J hIJ hI
  intro z hz
  obtain ⟨n, a, x, ha⟩ := TensorProduct.exists_sum_tmul_eq z
  have hzero : (∑ i, (a i : R) • x i) = 0 := by
    have hz' := LinearMap.mem_ker.mp hz
    rw [ha] at hz'
    have hz'' := congrArg (TensorProduct.lid R M) hz'
    simpa using hz''
  obtain ⟨w, hw⟩ := hLift a x hzero
  exact ⟨w, hw.trans ha.symm⟩

/-- If `I ≤ J`, flatness modulo `I` and injectivity of `I ⊗ M → M` imply injectivity of
`J ⊗ M → M`.  This is the complete equational step in the variant local criterion. -/
theorem injective_rTensor_of_ideal_of_flat_quotient
    (I J : Ideal R) (hIJ : I ≤ J)
    (hI : Function.Injective (I.subtype.rTensor M))
    [Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] :
    Function.Injective (J.subtype.rTensor M) :=
  injective_rTensor_of_tensorKernelLifting I J hIJ hI <|
    Ideal.tensorKernelLifting_of_moduloRelationLifting I J hIJ <|
      Ideal.moduloRelationLifting_of_flat_quotient I J

/-- Over a local ring, the preceding equational step applies to the maximal ideal for every
proper `I`.  The remaining implication from this injectivity to flatness is exactly the
Noetherian local criterion of Stacks Project tag 00MK. -/
theorem maximalIdeal_rTensor_injective_of_ideal_of_flat_quotient
    [IsLocalRing R] (I : Ideal R) (hIproper : I ≠ ⊤)
    (hI : Function.Injective (I.subtype.rTensor M))
    [Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] :
    Function.Injective ((IsLocalRing.maximalIdeal R).subtype.rTensor M) :=
  injective_rTensor_of_ideal_of_flat_quotient I (IsLocalRing.maximalIdeal R)
    (IsLocalRing.le_maximalIdeal hIproper) hI

end LinearMap

namespace Module

/-- The precise remaining local input after the equational part of the variant local
criterion: maximal-ideal tensor injectivity implies flatness.

Stacks Project tag 00MK proves this when `R → S` is a local homomorphism of local Noetherian
rings and `M` is finite over `S`, using Artin--Rees and faithful flatness of completion.  The
predicate deliberately records only the implication, so it can be consumed without asserting
that still-unformalized theorem. -/
def MaximalIdealTensorFlatnessCriterion
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] [Module.Finite S M] : Prop :=
  Function.Injective ((IsLocalRing.maximalIdeal R).subtype.rTensor M) →
    Module.Flat R M

namespace Flat

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
variable [AddCommGroup M] [Module S M] [Module R M]
variable [IsScalarTower R S M] [Module.Finite S M]

/-- Conditional kernel-map form of the variant local criterion: the equational argument is
fully discharged, and the sole remaining hypothesis is the maximal-ideal criterion isolated
above. -/
theorem of_ideal_rTensor_injective_of_quotient_flat
    (hcriterion : Module.MaximalIdealTensorFlatnessCriterion R S M)
    (I : Ideal R) (hIproper : I ≠ ⊤)
    (hI : Function.Injective (I.subtype.rTensor M))
    [Module.Flat (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] :
    Module.Flat R M :=
  hcriterion <|
    LinearMap.maximalIdeal_rTensor_injective_of_ideal_of_flat_quotient I hIproper hI

end Flat

end Module

end
