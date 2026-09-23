module

public import StacksAndModuli.API.LocalNoetherianPolynomialSystem
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Maximal ideals in the local Noetherian coefficient system

The transition maps in the local Noetherian coefficient system are local.  Consequently
their maximal ideals form a directed system over any fixed initial stage, and its direct
limit is the maximal ideal of the original local ring.  This is the varying-ideal component
of the tensor obstruction system in Stacks Project tag 00R6.
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u w

namespace LocalNoetherianApproximation

variable (R : Type u) [CommRing R] [IsLocalRing R]

private noncomputable instance targetIsLocalization :
    IsLocalization (maximalIdeal R).primeCompl R :=
  IsLocalization.of_le_isUnit fun _x hx ↦
    IsLocalRing.notMem_maximalIdeal.mp hx

noncomputable instance toLimit_isLocalHom (i : Index R) :
    IsLocalHom (toLimit R i) := by
  apply ((IsLocalRing.local_hom_TFAE (toLimit R i)).out 2 0).mp
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
    ((maximalIdeal R).comap i.1.val) (coefficient R i)]
  rw [Ideal.map_map]
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  change toLimit R i (algebraMap i.1 (coefficient R i) x) ∈ maximalIdeal R
  rw [toLimit_algebraMap]
  exact hx

/-- A later maximal ideal, regarded as a module over the fixed initial coefficient stage. -/
@[instance_reducible]
noncomputable instance maximalIdealModule {i : Index R} (j : Later R i) :
    Module (coefficient R i) (maximalIdeal (coefficient R j.1)) :=
  Module.compHom _ (transition R i j.1 j.2)

/-- Transition between maximal ideals in the later coefficient system. -/
noncomputable def maximalIdealTransition {i : Index R}
    (j k : Later R i) (h : j ≤ k) :
    maximalIdeal (coefficient R j.1) →ₗ[coefficient R i]
      maximalIdeal (coefficient R k.1) where
  toFun x := ⟨transition R j.1 k.1 h x.1,
    map_nonunit (transition R j.1 k.1 h) x.1 x.2⟩
  map_add' x y := by ext; simp
  map_smul' a x := by
    apply Subtype.ext
    change transition R j.1 k.1 h
        (transition R i j.1 j.2 a * x.1) =
      transition R i k.1 k.2 a * transition R j.1 k.1 h x.1
    rw [map_mul]
    congr 1
    exact DirectedSystem.map_map'
      (transition R) j.2 h a

instance maximalIdealDirectedSystem (i : Index R) :
    DirectedSystem
      (fun j : Later R i ↦ maximalIdeal (coefficient R j.1))
      (fun j k h ↦ maximalIdealTransition R j k h) where
  map_self {j} x := by
    apply Subtype.ext
    exact DirectedSystem.map_self' (transition R) x.1
  map_map {l k j} hjk hkl x := by
    apply Subtype.ext
    exact DirectedSystem.map_map' (transition R) hjk hkl x.1

/-- The maximal ideal of the original local ring, restricted to the initial coefficient
stage. -/
@[instance_reducible]
noncomputable instance targetMaximalIdealModule (i : Index R) :
    Module (coefficient R i) (maximalIdeal R) :=
  Module.compHom _ (toLimit R i)

/-- A later maximal ideal maps compatibly into the maximal ideal of the original ring. -/
noncomputable def maximalIdealToLimit {i : Index R} (j : Later R i) :
    maximalIdeal (coefficient R j.1) →ₗ[coefficient R i]
      maximalIdeal R where
  toFun x := ⟨toLimit R j.1 x.1,
    map_nonunit (toLimit R j.1) x.1 x.2⟩
  map_add' x y := by ext; simp
  map_smul' a x := by
    apply Subtype.ext
    change toLimit R j.1 (transition R i j.1 j.2 a * x.1) =
      toLimit R i a * toLimit R j.1 x.1
    rw [map_mul, toLimit_transition]

theorem maximalIdealToLimit_transition {i : Index R}
    (j k : Later R i) (h : j ≤ k)
    (x : maximalIdeal (coefficient R j.1)) :
    maximalIdealToLimit R k (maximalIdealTransition R j k h x) =
      maximalIdealToLimit R j x := by
  apply Subtype.ext
  exact toLimit_transition R j.1 k.1 h x.1

/-- The canonical map from the direct limit of later maximal ideals to the maximal ideal of
the original local ring. -/
noncomputable def maximalIdealLimitMap (i : Index R) :
    Module.DirectLimit
      (fun j : Later R i ↦ maximalIdeal (coefficient R j.1))
      (fun j k h ↦ maximalIdealTransition R j k h) →ₗ[coefficient R i]
        maximalIdeal R :=
  Module.DirectLimit.lift _ _ _ _
    (fun j ↦ maximalIdealToLimit R j)
    (maximalIdealToLimit_transition R)

theorem maximalIdealLimitMap_injective (i : Index R) :
    Function.Injective (maximalIdealLimitMap R i) := by
  apply Module.DirectLimit.lift_injective
  intro j x y hxy
  apply Subtype.ext
  apply toLimit_injective R j.1
  exact congrArg Subtype.val hxy

theorem maximalIdealLimitMap_surjective (i : Index R) :
    Function.Surjective (maximalIdealLimitMap R i) := by
  intro x
  let A : Subalgebra ℤ R :=
    i.1 ⊔ Algebra.adjoin ℤ ({x.1} : Set R)
  have hA : A.FG :=
    i.2.sup (by
      simpa only [Finset.coe_singleton] using
        Subalgebra.fg_adjoin_finset ({x.1} : Finset R))
  let j₀ : Index R := ⟨A, hA⟩
  have hij : i ≤ j₀ := by
    change i.1 ≤ A
    exact le_sup_left
  let j : Later R i := ⟨j₀, hij⟩
  have hxA : x.1 ∈ A :=
    (show Algebra.adjoin ℤ ({x.1} : Set R) ≤ A from le_sup_right)
      (Algebra.subset_adjoin (Set.mem_singleton x.1))
  let a : j.1.1 := ⟨x.1, hxA⟩
  let y₀ : coefficient R j.1 := ofBase R j.1 a
  have hy₀ : toLimit R j.1 y₀ = x.1 := toLimit_ofBase R j.1 a
  have hy : y₀ ∈ maximalIdeal (coefficient R j.1) := by
    rw [← IsLocalRing.maximalIdeal_comap (toLimit R j.1)]
    change toLimit R j.1 y₀ ∈ maximalIdeal R
    rw [hy₀]
    exact x.2
  let y : maximalIdeal (coefficient R j.1) := ⟨y₀, hy⟩
  refine ⟨Module.DirectLimit.of
    (coefficient R i) (Later R i)
    (fun k : Later R i ↦ maximalIdeal (coefficient R k.1))
    (fun a b h ↦ maximalIdealTransition R a b h) j y, ?_⟩
  rw [maximalIdealLimitMap, Module.DirectLimit.lift_of]
  exact Subtype.ext hy₀

/-- The direct limit of the later maximal ideals is the maximal ideal of the original local
ring. -/
noncomputable def maximalIdealLimitEquiv (i : Index R) :
    Module.DirectLimit
      (fun j : Later R i ↦ maximalIdeal (coefficient R j.1))
      (fun j k h ↦ maximalIdealTransition R j k h) ≃ₗ[coefficient R i]
        maximalIdeal R :=
  LinearEquiv.ofBijective (maximalIdealLimitMap R i)
    ⟨maximalIdealLimitMap_injective R i,
      maximalIdealLimitMap_surjective R i⟩

section ModuleSystem

variable (i : Index R)
variable (N : Type w) [AddCommMonoid N] [Module (coefficient R i) N]

/-- Tensoring a later maximal ideal with a fixed module over the initial coefficient
stage. -/
abbrev maximalIdealBaseChange (j : Later R i) : Type max u w :=
  (maximalIdeal (coefficient R j.1)) ⊗[coefficient R i] N

/-- Transition maps for maximal ideals tensored with a fixed module. -/
noncomputable def maximalIdealBaseChangeTransition (j k : Later R i) (h : j ≤ k) :
    maximalIdealBaseChange R i N j →ₗ[coefficient R i]
      maximalIdealBaseChange R i N k :=
  (maximalIdealTransition R j k h).rTensor N

/-- The tensor extensions of the later maximal ideals form a directed system. -/
noncomputable instance maximalIdealBaseChangeDirectedSystem :
    DirectedSystem (fun j : Later R i ↦ maximalIdealBaseChange R i N j)
      (fun j k h ↦ maximalIdealBaseChangeTransition R i N j k h) :=
  by
    change DirectedSystem
      (fun j : Later R i ↦ (maximalIdeal (coefficient R j.1)) ⊗[coefficient R i] N)
      (fun j k h ↦ (maximalIdealTransition R j k h).rTensor N)
    infer_instance

/-- Tensoring with a fixed module commutes with the cofinal limit of the later maximal
ideals. -/
noncomputable def maximalIdealBaseChangeLimitEquiv :
    Module.DirectLimit
      (fun j : Later R i ↦ maximalIdealBaseChange R i N j)
      (fun j k h ↦ maximalIdealBaseChangeTransition R i N j k h) ≃ₗ[
        coefficient R i]
      (maximalIdeal R) ⊗[coefficient R i] N :=
  (TensorProduct.directLimitLeft
      (fun j k h ↦ maximalIdealTransition R j k h) N).symm ≪≫ₗ
    (maximalIdealLimitEquiv R i).rTensor N

@[simp]
theorem maximalIdealBaseChangeLimitEquiv_of_tmul (j : Later R i)
    (x : maximalIdeal (coefficient R j.1)) (y : N) :
    maximalIdealBaseChangeLimitEquiv R i N
        (Module.DirectLimit.of
          (coefficient R i) (Later R i)
          (fun k : Later R i ↦ maximalIdealBaseChange R i N k)
          (fun a b h ↦ maximalIdealBaseChangeTransition R i N a b h)
          j (x ⊗ₜ y)) =
      maximalIdealToLimit R j x ⊗ₜ y := by
  change
    ((TensorProduct.directLimitLeft
        (fun j k h ↦ maximalIdealTransition R j k h) N).symm ≪≫ₗ
      (maximalIdealLimitEquiv R i).rTensor N)
        (Module.DirectLimit.of
          (coefficient R i) (Later R i)
          (fun k : Later R i ↦
            (maximalIdeal (coefficient R k.1)) ⊗[coefficient R i] N)
          (fun a b h ↦ (maximalIdealTransition R a b h).rTensor N)
          j (x ⊗ₜ y)) = _
  rw [LinearEquiv.trans_apply, TensorProduct.directLimitLeft_symm_of_tmul,
    LinearEquiv.rTensor_tmul]
  change maximalIdealLimitMap R i
      (Module.DirectLimit.of
        (coefficient R i) (Later R i)
        (fun k : Later R i ↦ maximalIdeal (coefficient R k.1))
        (fun a b h ↦ maximalIdealTransition R a b h) j x) ⊗ₜ y = _
  rw [maximalIdealLimitMap, Module.DirectLimit.lift_of]

end ModuleSystem

end LocalNoetherianApproximation
