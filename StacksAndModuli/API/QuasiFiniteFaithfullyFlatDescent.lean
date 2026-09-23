module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Descent
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Descent of quasi-finiteness along a faithfully flat algebra

If `R → A → B` are ring maps with `A → B` faithfully flat and `R → B` quasi-finite, then
`R → A` is quasi-finite.

Mathlib's `Algebra.QuasiFinite R S` (Stacks
[00PL](https://stacks.math.columbia.edu/tag/00PL)) asks that the fibre
`κ(P) ⊗[R] S` be a finite-dimensional `κ(P)`-vector space for every prime `P` of `R`; it does
*not* include a finite-type hypothesis. So the descent cannot be run through the
finite-fibre criterion `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton` (which needs
`Algebra.FiniteType`) and is instead a statement about vector spaces: the comparison map
`κ(P) ⊗[R] A → κ(P) ⊗[R] B` is injective, because it is the map `M → M ⊗[A] B` for
`M = κ(P) ⊗[R] A` and `B` is faithfully flat over `A`
(`Module.FaithfullyFlat.tensorProduct_mk_injective`), and a subspace of a finite-dimensional
space is finite-dimensional.

The identification of the comparison map with `M → M ⊗[A] B` is where the work is: it is a
chain of four maps whose composite is checked on pure tensors,

    κ(P) ⊗[R] A ≃ A ⊗[R] κ(P) → B ⊗[A] (A ⊗[R] κ(P)) ≃ B ⊗[R] κ(P) ≃ κ(P) ⊗[R] B,

only the second of which is not an isomorphism. Injectivity is a statement about the
underlying *function*, so the intermediate maps need not be `κ(P)`-linear — only the map
being shown injective is, and it is `κ(P)`-linear by construction
(`TensorProduct.AlgebraTensorModule.map`).

Together with `StacksAndModuli/API/QuasiFiniteSourceLocal.lean` this gives étale-locality on the
source and the target of local quasi-finiteness, `def:properties-of-morphisms-of-stacks` in
§4.3 of *Stacks and Moduli*.

## Main results

* `Algebra.QuasiFinite.of_faithfullyFlat`: the algebra form.
* `RingHom.QuasiFinite.of_comp_of_faithfullyFlat`: the ring-homomorphism form.
* `RingHom.QuasiFinite.of_etale`: an étale ring map is quasi-finite.
-/

@[expose] public section

universe u

open TensorProduct

theorem Algebra.QuasiFinite.of_faithfullyFlat {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.QuasiFinite R B] :
    Algebra.QuasiFinite R A := by
  refine ⟨fun P _ => ?_⟩
  set K := P.ResidueField with hK
  have hfin : Module.Finite K (P.Fiber B) := Algebra.QuasiFinite.finite_fiber P
  -- the K-linear comparison map on fibers
  let ι : P.Fiber A →ₗ[K] P.Fiber B :=
    TensorProduct.AlgebraTensorModule.map (LinearMap.id (R := K) (M := K))
      (IsScalarTower.toAlgHom R A B).toLinearMap
  -- factor it through `B ⊗[A] (A ⊗[R] K)`
  have hfac : ∀ x : P.Fiber A, ι x =
      ((Algebra.TensorProduct.comm R B K) ∘
        (Algebra.TensorProduct.cancelBaseChange R A A B K) ∘
        (TensorProduct.mk A B (A ⊗[R] K) 1) ∘
        (Algebra.TensorProduct.comm R K A)) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [ι]
    | tmul k a => simp [ι, Algebra.algebraMap_eq_smul_one]
    | add x y hx hy => simp only [Function.comp_apply] at hx hy ⊢; simp [map_add, hx, hy]
  have hinj : Function.Injective ι := by
    rw [funext hfac]
    refine (Algebra.TensorProduct.comm R B K).injective.comp
      ((Algebra.TensorProduct.cancelBaseChange R A A B K).injective.comp
        ((Module.FaithfullyFlat.tensorProduct_mk_injective (A := A) (B := B)
          (A ⊗[R] K)).comp (Algebra.TensorProduct.comm R K A).injective))
  exact Module.Finite.of_injective ι hinj

/-- Ring-homomorphism form of `Algebra.QuasiFinite.of_faithfullyFlat`. -/
theorem RingHom.QuasiFinite.of_comp_of_faithfullyFlat {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] (φ : R →+* A) (ψ : A →+* B) (hcomp : (ψ.comp φ).QuasiFinite)
    (hff : ψ.FaithfullyFlat) : φ.QuasiFinite := by
  algebraize [φ, ψ, ψ.comp φ]
  exact Algebra.QuasiFinite.of_faithfullyFlat (B := B)

/-- An étale ring map is quasi-finite: it is essentially of finite type and formally
unramified. -/
theorem RingHom.QuasiFinite.of_etale {R S : Type u} [CommRing R] [CommRing S] {φ : R →+* S}
    (h : φ.Etale) : φ.QuasiFinite := by
  algebraize [φ]
  have h₁ : Algebra.FormallyUnramified R S := inferInstance
  have h₂ : Algebra.EssFiniteType R S := inferInstance
  exact inferInstanceAs (Algebra.QuasiFinite _ _)
