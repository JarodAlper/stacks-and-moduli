module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Base change of cokernels of linear maps

Tensor product is right exact, so scalar extension commutes with the cokernel of a linear
map.  This file packages the resulting linear equivalence using the concrete module model
`F / range(g)` on both sides.  It also records the complementary exactness statement: if
two maps are exact and the cokernel of the second is flat, their scalar extensions remain
exact even when the scalar extension itself is not flat.

Main declarations:

* `LinearMap.baseChangeCokerEquiv`;
* `LinearMap.lTensor_exact_of_exact_of_flat_cokernel`;
* `LinearMap.lTensor_exact_of_exact_of_coker_flat`.
-/

@[expose] public section

noncomputable section

universe u v

open TensorProduct

namespace LinearMap

/-- Scalar extension commutes with taking the cokernel presented by a linear map. -/
noncomputable def baseChangeCokerEquiv
    {S T K F : Type u} [CommRing S] [CommRing T] [Algebra S T]
    [AddCommGroup K] [Module S K]
    [AddCommGroup F] [Module S F]
    (g : K →ₗ[S] F) :
    ((T ⊗[S] F) ⧸ LinearMap.range (g.baseChange T)) ≃ₗ[T]
      T ⊗[S] (F ⧸ LinearMap.range g) := by
  let q : F →ₗ[S] F ⧸ LinearMap.range g :=
    (LinearMap.range g).mkQ
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hex : Function.Exact (g.baseChange T) (q.baseChange T) := by
    simpa only [LinearMap.baseChange_eq_ltensor] using
      lTensor_exact T (LinearMap.exact_map_mkQ_range g) hq
  have hqT : Function.Surjective (q.baseChange T) :=
    LinearMap.baseChange_surjective T hq
  have hker : LinearMap.ker (q.baseChange T) =
      LinearMap.range (g.baseChange T) :=
    hex.linearMap_ker_eq
  let eKer : ((T ⊗[S] F) ⧸ LinearMap.range (g.baseChange T)) ≃ₗ[T]
      ((T ⊗[S] F) ⧸ LinearMap.ker (q.baseChange T)) :=
    Submodule.Quotient.equiv _ _ (LinearEquiv.refl T _)
      (by simpa using hker.symm)
  exact eKer.trans ((q.baseChange T).quotKerEquivOfSurjective hqT)

/-- If `f`, `g`, and a surjection `p` form two consecutive exact pairs and the target of
`p` is flat, tensoring `f` and `g` with an arbitrary module preserves exactness.

The proof factors `g` through `ker p`.  Right exactness preserves exactness up to that
surjective factor, while flatness of the cokernel target makes the tensor of the kernel
inclusion injective. -/
theorem lTensor_exact_of_exact_of_flat_cokernel
    {R A : Type u} {L K F M : Type v} [CommRing R]
    [AddCommGroup A] [Module R A]
    [AddCommGroup L] [Module R L]
    [AddCommGroup K] [Module R K]
    [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (f : L →ₗ[R] K) (g : K →ₗ[R] F)
    (hfg : Function.Exact f g)
    (p : F →ₗ[R] M) (hgp : Function.Exact g p)
    (hp : Function.Surjective p) :
    Function.Exact (f.lTensor A) (g.lTensor A) := by
  let I := LinearMap.ker p
  let gr : K →ₗ[R] I := g.codRestrict I fun x ↦ by
    rw [LinearMap.mem_ker]
    exact (hgp (g x)).mpr ⟨x, rfl⟩
  have hgr_apply (x : K) : (gr x : F) = g x := by
    rfl
  have hgr : Function.Surjective gr := by
    intro y
    obtain ⟨x, hx⟩ := (hgp y).mp y.property
    refine ⟨x, ?_⟩
    apply Subtype.ext
    simpa only [hgr_apply] using hx
  have hfg' : Function.Exact f gr := by
    intro x
    have hzero : gr x = 0 ↔ g x = 0 := by
      constructor
      · intro hx
        simpa only [hgr_apply, Submodule.coe_zero] using congrArg Subtype.val hx
      · intro hx
        apply Subtype.ext
        simpa only [hgr_apply, Submodule.coe_zero] using hx
    exact hzero.trans (hfg x)
  have hexact : Function.Exact (f.lTensor A) (gr.lTensor A) :=
    lTensor_exact A hfg' hgr
  have hinj : Function.Injective (I.subtype.lTensor A) :=
    LinearMap.lTensor_injective_of_exact_of_flat
      p hp I.subtype Subtype.val_injective p.exact_subtype_ker_map A
  have hcomp :=
    hexact.comp_injective (I.subtype.lTensor A) hinj (map_zero _)
  rw [show g = I.subtype.comp gr from rfl, lTensor_comp]
  intro x
  change (I.subtype.lTensor A) ((gr.lTensor A) x) = 0 ↔ _
  exact hcomp x

/-- If two linear maps are exact and the concrete cokernel of the second map is flat,
tensoring the pair with an arbitrary module preserves exactness. -/
theorem lTensor_exact_of_exact_of_coker_flat
    {R A L K F : Type u} [CommRing R]
    [AddCommGroup A] [Module R A]
    [AddCommGroup L] [Module R L]
    [AddCommGroup K] [Module R K]
    [AddCommGroup F] [Module R F]
    (f : L →ₗ[R] K) (g : K →ₗ[R] F)
    (h : Function.Exact f g)
    [Module.Flat R (F ⧸ LinearMap.range g)] :
    Function.Exact (f.lTensor A) (g.lTensor A) :=
  lTensor_exact_of_exact_of_flat_cokernel f g h
    (LinearMap.range g).mkQ (LinearMap.exact_map_mkQ_range g)
      (Submodule.mkQ_surjective _)

end LinearMap

end

end
