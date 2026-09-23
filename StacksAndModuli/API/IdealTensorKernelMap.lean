module

public import StacksAndModuli.API.NoetherianTorKernelFinite

/-!
# Base change maps on ideal-tensor kernels

This file constructs the semilinear transition map on the kernel of ideal multiplication
associated to a commutative square of rings and a compatible semilinear map of modules.  It
is the canonical comparison map for the finite obstruction modules in the local flat
approximation argument of Stacks Project tag 00R6.
-/

@[expose] public section

open TensorProduct

universe u v w

namespace Ideal

variable {R R' S S' : Type u} {M : Type v} {M' : Type w}
variable [CommRing R] [CommRing R'] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R' S']
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommGroup M'] [Module R' M'] [Module S' M'] [IsScalarTower R' S' M']

/-- Restrict an `S`-semilinear map along a commutative square `R → S`, `R' → S'`. -/
def restrictScalarsSemilinear
    (r : R →+* R') (s : S →+* S')
    (hsq : s.comp (algebraMap R S) = (algebraMap R' S').comp r)
    (g : M →ₛₗ[s] M') : M →ₛₗ[r] M' where
  toFun := g
  map_add' := g.map_add
  map_smul' a x := by
    rw [← IsScalarTower.algebraMap_smul S a x, g.map_smulₛₗ]
    have hcoeff : s (algebraMap R S a) = algebraMap R' S' (r a) := by
      simpa only [RingHom.coe_comp, Function.comp_apply] using RingHom.congr_fun hsq a
    calc
      s (algebraMap R S a) • g x = algebraMap R' S' (r a) • g x :=
        congrArg (fun b : S' => b • g x) hcoeff
      _ = r a • g x := IsScalarTower.algebraMap_smul S' (r a) (g x)

/-- The semilinear map of ideals induced by a ring map carrying `I` into `J`. -/
def mapSemilinear (r : R →+* R') (I : Ideal R) (J : Ideal R')
    (hIJ : ∀ x : I, r x.1 ∈ J) : I →ₛₗ[r] J where
  toFun x := ⟨r x.1, hIJ x⟩
  map_add' x y := by ext; simp
  map_smul' a x := by ext; simp

/-- The semilinear map `M ⊗[R] I → M' ⊗[R'] J` induced by compatible maps. -/
def tensorMap
    (r : R →+* R') (s : S →+* S')
    (hsq : s.comp (algebraMap R S) = (algebraMap R' S').comp r)
    (g : M →ₛₗ[s] M') (I : Ideal R) (J : Ideal R')
    (hIJ : ∀ x : I, r x.1 ∈ J) :
    M ⊗[R] I →ₛₗ[r] M' ⊗[R'] J :=
  TensorProduct.map (restrictScalarsSemilinear r s hsq g)
    (mapSemilinear r I J hIJ)

@[simp]
theorem tensorMap_tmul
    (r : R →+* R') (s : S →+* S')
    (hsq : s.comp (algebraMap R S) = (algebraMap R' S').comp r)
    (g : M →ₛₗ[s] M') (I : Ideal R) (J : Ideal R')
    (hIJ : ∀ x : I, r x.1 ∈ J) (m : M) (x : I) :
    tensorMap r s hsq g I J hIJ (m ⊗ₜ[R] x) =
      g m ⊗ₜ[R'] (⟨r x.1, hIJ x⟩ : J) := by
  simp [tensorMap, restrictScalarsSemilinear, mapSemilinear]

/-- Ideal multiplication commutes with `tensorMap`. -/
theorem tensorMul_tensorMap
    (r : R →+* R') (s : S →+* S')
    (hsq : s.comp (algebraMap R S) = (algebraMap R' S').comp r)
    (g : M →ₛₗ[s] M') (I : Ideal R) (J : Ideal R')
    (hIJ : ∀ x : I, r x.1 ∈ J) (z : M ⊗[R] I) :
    tensorMul (R := R') (S := S') (M := M') J
        (tensorMap r s hsq g I J hIJ z) =
      g (tensorMul (R := R) (S := S) (M := M) I z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (.+.) hx hy
  | tmul m x =>
    simp only [tensorMap_tmul, tensorMul_tmul]
    exact (restrictScalarsSemilinear r s hsq g).map_smulₛₗ x.1 m |>.symm

/-- The induced additive transition map between kernels of ideal multiplication. -/
def tensorMulKerMap
    (r : R →+* R') (s : S →+* S')
    (hsq : s.comp (algebraMap R S) = (algebraMap R' S').comp r)
    (g : M →ₛₗ[s] M') (I : Ideal R) (J : Ideal R')
    (hIJ : ∀ x : I, r x.1 ∈ J) :
    LinearMap.ker (tensorMul (R := R) (S := S) (M := M) I) →+
      LinearMap.ker (tensorMul (R := R') (S := S') (M := M') J) where
  toFun x := ⟨tensorMap r s hsq g I J hIJ x.1, by
    change tensorMul (R := R') (S := S') (M := M') J
      (tensorMap r s hsq g I J hIJ x.1) = 0
    rw [tensorMul_tensorMap, x.2, map_zero]⟩
  map_zero' := by ext; simp [tensorMap]
  map_add' x y := by ext; simp [tensorMap]

@[simp]
theorem tensorMulKerMap_val
    (r : R →+* R') (s : S →+* S')
    (hsq : s.comp (algebraMap R S) = (algebraMap R' S').comp r)
    (g : M →ₛₗ[s] M') (I : Ideal R) (J : Ideal R')
    (hIJ : ∀ x : I, r x.1 ∈ J)
    (x : LinearMap.ker (tensorMul (R := R) (S := S) (M := M) I)) :
    (tensorMulKerMap r s hsq g I J hIJ x).1 =
      tensorMap r s hsq g I J hIJ x.1 := rfl

end Ideal
