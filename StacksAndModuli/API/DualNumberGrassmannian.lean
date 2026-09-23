module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import StacksAndModuli.API.BaseChangePi

/-!
# The tangent space to the Grassmannian over the dual numbers

Supporting API with no Stacks Project counterpart.

Let `k` be a field, `K ⊆ k^n` a subspace with quotient `Q = k^n/K`, and
`k[ε] = DualNumber k` the dual numbers. A point of the Grassmannian `Gr(q, n)` over
`k[ε]` restricting to the point `K` over `k` is a submodule `N ⊆ k[ε]^n` whose quotient
is projective (equivalently, finite free over the local ring `k[ε]`) and whose scalar
part is `K`. This file establishes the classical bijection between such lifts and
`k`-linear maps `K → Q`, which is the module-theoretic heart of the tangent-space
exercise `exer:grassmannian-tangent-space` of *Stacks and Moduli*:
`T_[K] Gr(q, n) ≅ Hom_k(K, k^n/K)`.

The lift attached to `φ : K →ₗ[k] Q` is
`N_φ = {x | fst ∘ x ∈ K and φ (fst ∘ x) = [snd ∘ x]}`.

Main declarations:
- `Submodule.dualNumberLift φ`: the lift `N_φ` of `K` attached to `φ : K →ₗ[k] Q`;
- `Submodule.dualNumberLift_free`, `Submodule.span_fst_image_dualNumberLift`: the
  quotient by `N_φ` is finite free, of the expected rank
  (`Submodule.rankAtStalk_dualNumberLift`), and `N_φ` restricts to `K`;
- `Submodule.dualNumberLiftEquiv`: the bijection between lifts of `K` with projective
  quotient and `Hom_k(K, k^n/K)`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open TensorProduct TrivSqZeroExt

universe u

namespace Submodule

variable {k : Type u} [Field k] {n : ℕ} {K : Submodule k (Fin n → k)}

/-! ### Componentwise scalar and infinitesimal parts -/

/-- The componentwise scalar part of a vector of dual numbers. -/
def dualFstPi (x : Fin n → DualNumber k) : Fin n → k := fun i ↦ (x i).fst

/-- The componentwise infinitesimal part of a vector of dual numbers. -/
def dualSndPi (x : Fin n → DualNumber k) : Fin n → k := fun i ↦ (x i).snd

/-- The componentwise inclusion of scalars into dual numbers. -/
def dualInlPi (v : Fin n → k) : Fin n → DualNumber k := fun i ↦ .inl (v i)

omit [Field k] in
@[simp] lemma dualFstPi_apply (x : Fin n → DualNumber k) (i : Fin n) :
    dualFstPi x i = (x i).fst := rfl

omit [Field k] in
@[simp] lemma dualSndPi_apply (x : Fin n → DualNumber k) (i : Fin n) :
    dualSndPi x i = (x i).snd := rfl

@[simp] lemma dualInlPi_apply (v : Fin n → k) (i : Fin n) :
    dualInlPi v i = TrivSqZeroExt.inl (v i) := rfl

@[simp] lemma dualFstPi_add (x y : Fin n → DualNumber k) :
    dualFstPi (x + y) = dualFstPi x + dualFstPi y := by
  funext i
  simp [dualFstPi]

@[simp] lemma dualSndPi_add (x y : Fin n → DualNumber k) :
    dualSndPi (x + y) = dualSndPi x + dualSndPi y := by
  funext i
  simp [dualSndPi]

@[simp] lemma dualFstPi_neg (x : Fin n → DualNumber k) :
    dualFstPi (-x) = -dualFstPi x := by
  funext i
  simp [dualFstPi]

@[simp] lemma dualSndPi_neg (x : Fin n → DualNumber k) :
    dualSndPi (-x) = -dualSndPi x := by
  funext i
  simp [dualSndPi]

@[simp] lemma dualFstPi_sub (x y : Fin n → DualNumber k) :
    dualFstPi (x - y) = dualFstPi x - dualFstPi y := by
  funext i
  simp [dualFstPi]

@[simp] lemma dualSndPi_sub (x y : Fin n → DualNumber k) :
    dualSndPi (x - y) = dualSndPi x - dualSndPi y := by
  funext i
  simp [dualSndPi]

@[simp] lemma dualFstPi_zero : dualFstPi (0 : Fin n → DualNumber k) = 0 := by
  funext i
  simp [dualFstPi]

@[simp] lemma dualSndPi_zero : dualSndPi (0 : Fin n → DualNumber k) = 0 := by
  funext i
  simp [dualSndPi]

@[simp] lemma dualFstPi_smul (c : DualNumber k) (x : Fin n → DualNumber k) :
    dualFstPi (c • x) = c.fst • dualFstPi x := by
  funext i
  simp [dualFstPi, smul_eq_mul]

@[simp] lemma dualSndPi_smul (c : DualNumber k) (x : Fin n → DualNumber k) :
    dualSndPi (c • x) = c.fst • dualSndPi x + c.snd • dualFstPi x := by
  funext i
  simp only [dualSndPi, Pi.smul_apply, smul_eq_mul, DualNumber.snd_mul, Pi.add_apply,
    dualFstPi]

@[simp] lemma dualFstPi_inlPi (v : Fin n → k) : dualFstPi (dualInlPi v) = v := by
  funext i
  simp [dualFstPi, dualInlPi]

@[simp] lemma dualSndPi_inlPi (v : Fin n → k) : dualSndPi (dualInlPi v) = 0 := by
  funext i
  simp [dualSndPi, dualInlPi]

@[simp] lemma dualInlPi_add (v w : Fin n → k) :
    dualInlPi (v + w) = dualInlPi v + dualInlPi w := by
  funext i
  simp [dualInlPi]

@[simp] lemma dualInlPi_neg (v : Fin n → k) : dualInlPi (-v) = -dualInlPi v := by
  funext i
  simp [dualInlPi]

@[simp] lemma dualInlPi_zero : dualInlPi (0 : Fin n → k) = 0 := by
  funext i
  simp [dualInlPi]

/-- Multiplication by `ε` moves the scalar part to the infinitesimal part. -/
lemma eps_mul_eq_inr_fst (x : DualNumber k) :
    (DualNumber.eps : DualNumber k) * x = TrivSqZeroExt.inr x.fst := by
  ext
  · rw [TrivSqZeroExt.fst_mul, DualNumber.fst_eps, zero_mul, TrivSqZeroExt.fst_inr]
  · rw [DualNumber.snd_mul, DualNumber.fst_eps, DualNumber.snd_eps,
      TrivSqZeroExt.snd_inr, zero_mul, one_mul, zero_add]

@[simp] lemma dualFstPi_eps_smul (x : Fin n → DualNumber k) :
    dualFstPi ((DualNumber.eps : DualNumber k) • x) = 0 := by
  funext i
  simp only [dualFstPi, Pi.smul_apply, smul_eq_mul, eps_mul_eq_inr_fst,
    TrivSqZeroExt.fst_inr, Pi.zero_apply]

@[simp] lemma dualSndPi_eps_smul (x : Fin n → DualNumber k) :
    dualSndPi ((DualNumber.eps : DualNumber k) • x) = dualFstPi x := by
  funext i
  simp only [dualSndPi, Pi.smul_apply, smul_eq_mul, eps_mul_eq_inr_fst,
    TrivSqZeroExt.snd_inr, dualFstPi]

/-- Decomposition of a vector of dual numbers into scalar and infinitesimal parts. -/
lemma eq_inlPi_fstPi_add_eps_smul (x : Fin n → DualNumber k) :
    x = dualInlPi (dualFstPi x) +
      (DualNumber.eps : DualNumber k) • dualInlPi (dualSndPi x) := by
  funext i
  rw [Pi.add_apply, Pi.smul_apply, dualInlPi_apply, dualInlPi_apply, smul_eq_mul,
    eps_mul_eq_inr_fst, TrivSqZeroExt.fst_inl, dualFstPi_apply, dualSndPi_apply]
  exact (TrivSqZeroExt.inl_fst_add_inr_snd_eq (x i)).symm

/-! ### The lift attached to a homomorphism -/

/-- The lift of the Grassmannian point `K ⊆ k^n` to the dual numbers attached to a
homomorphism `φ : K →ₗ[k] k^n/K`: the submodule of `k[ε]^n` of vectors whose scalar
part lies in `K` and whose infinitesimal part reduces to the `φ`-image of the scalar
part. -/
def dualNumberLift (φ : K →ₗ[k] ((Fin n → k) ⧸ K)) :
    Submodule (DualNumber k) (Fin n → DualNumber k) where
  carrier := {x | ∃ v : K, dualFstPi x = v.1 ∧
    Submodule.Quotient.mk (dualSndPi x) = φ v}
  add_mem' := by
    rintro x y ⟨v, hv, hv'⟩ ⟨w, hw, hw'⟩
    refine ⟨v + w, ?_, ?_⟩
    · rw [dualFstPi_add, hv, hw]
      rfl
    · rw [dualSndPi_add, Submodule.Quotient.mk_add, hv', hw', map_add]
  zero_mem' :=
    ⟨0, by rw [dualFstPi_zero]; rfl, by
      rw [dualSndPi_zero, map_zero]
      exact (Submodule.Quotient.mk_eq_zero K).mpr K.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨v, hv, hv'⟩
    refine ⟨c.fst • v, ?_, ?_⟩
    · rw [dualFstPi_smul, hv]
      rfl
    · rw [dualSndPi_smul, hv, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul,
        hv', map_smul]
      have h0 : Submodule.Quotient.mk (p := K) (c.snd • v.1) = 0 :=
        (Submodule.Quotient.mk_eq_zero K).mpr (K.smul_mem c.snd v.2)
      rw [h0, add_zero]

lemma mem_dualNumberLift {φ : K →ₗ[k] ((Fin n → k) ⧸ K)}
    {x : Fin n → DualNumber k} :
    x ∈ dualNumberLift φ ↔ ∃ v : K, dualFstPi x = v.1 ∧
      Submodule.Quotient.mk (dualSndPi x) = φ v :=
  Iff.rfl

/-- The scalar part of any element of a lift lies in `K`. -/
lemma dualFstPi_mem_of_mem_dualNumberLift {φ : K →ₗ[k] ((Fin n → k) ⧸ K)}
    {x : Fin n → DualNumber k} (hx : x ∈ dualNumberLift φ) : dualFstPi x ∈ K := by
  obtain ⟨v, hv, -⟩ := hx
  rw [hv]
  exact v.2

/-- Every element of `K` is the scalar part of an element of the lift. -/
lemma exists_mem_dualNumberLift_fstPi_eq (φ : K →ₗ[k] ((Fin n → k) ⧸ K))
    (v : K) :
    ∃ x ∈ dualNumberLift φ, dualFstPi x = v.1 := by
  obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective K (φ v)
  have hfst : dualFstPi (dualInlPi v.1 +
      (DualNumber.eps : DualNumber k) • dualInlPi w) = v.1 := by
    rw [dualFstPi_add, dualFstPi_inlPi, dualFstPi_eps_smul, add_zero]
  refine ⟨dualInlPi v.1 + (DualNumber.eps : DualNumber k) • dualInlPi w,
    ⟨v, hfst, ?_⟩, hfst⟩
  rw [dualSndPi_add, dualSndPi_inlPi, dualSndPi_eps_smul, dualFstPi_inlPi, zero_add,
    hw]

/-- The `k`-span of the scalar parts of a lift recovers `K`. -/
lemma span_fst_image_dualNumberLift (φ : K →ₗ[k] ((Fin n → k) ⧸ K)) :
    Submodule.span k (dualFstPi '' (dualNumberLift φ : Set (Fin n → DualNumber k)))
      = K := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact dualFstPi_mem_of_mem_dualNumberLift hx
  · intro v hv
    obtain ⟨x, hx, hfst⟩ := exists_mem_dualNumberLift_fstPi_eq φ ⟨v, hv⟩
    exact Submodule.subset_span ⟨x, hx, hfst⟩

/-! ### The zero lift is a base change -/

/-- The zero lift is the `k[ε]`-span of (the scalar inclusion of) `K`. -/
lemma dualNumberLift_zero_eq_span :
    dualNumberLift (0 : K →ₗ[k] ((Fin n → k) ⧸ K)) =
      Submodule.span (DualNumber k)
        ((fun (v : Fin n → k) i ↦ algebraMap k (DualNumber k) (v i)) ''
          (K : Set (Fin n → k))) := by
  have hinl : ∀ v : Fin n → k,
      (fun i ↦ algebraMap k (DualNumber k) (v i)) = dualInlPi v := by
    intro v
    funext i
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    rfl
  apply le_antisymm
  · rintro x ⟨v, hv, hv'⟩
    rw [LinearMap.zero_apply] at hv'
    have hsnd : dualSndPi x ∈ K := (Submodule.Quotient.mk_eq_zero K).mp hv'
    have hfstK : dualFstPi x ∈ K := by rw [hv]; exact v.2
    rw [eq_inlPi_fstPi_add_eps_smul x]
    have hmem : ∀ (w : Fin n → k), w ∈ K → dualInlPi w ∈
        Submodule.span (DualNumber k)
          ((fun (v : Fin n → k) i ↦ algebraMap k (DualNumber k) (v i)) ''
            (K : Set (Fin n → k))) := by
      intro w hw
      exact Submodule.subset_span ⟨w, hw, hinl w⟩
    exact Submodule.add_mem _ (hmem _ hfstK) (Submodule.smul_mem _ _ (hmem _ hsnd))
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    change (fun i ↦ algebraMap k (DualNumber k) (v i)) ∈ dualNumberLift 0
    rw [hinl v]
    refine ⟨⟨v, hv⟩, by rw [dualFstPi_inlPi], ?_⟩
    rw [dualSndPi_inlPi, LinearMap.zero_apply]
    exact (Submodule.Quotient.mk_eq_zero K).mpr K.zero_mem

/-- The quotient by the zero lift is the base change of `k^n/K` to the dual numbers. -/
noncomputable def dualNumberLiftZeroQuotientEquiv :
    ((Fin n → DualNumber k) ⧸
        dualNumberLift (0 : K →ₗ[k] ((Fin n → k) ⧸ K))) ≃ₗ[DualNumber k]
      (DualNumber k) ⊗[k] ((Fin n → k) ⧸ K) := by
  have hker : LinearMap.ker (LinearMap.baseChangePi (DualNumber k) K.mkQ) =
      dualNumberLift (0 : K →ₗ[k] ((Fin n → k) ⧸ K)) := by
    rw [LinearMap.ker_baseChangePi_eq_span (DualNumber k)
      (Submodule.mkQ_surjective K), Submodule.ker_mkQ, dualNumberLift_zero_eq_span]
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    ((LinearMap.baseChangePi (DualNumber k) K.mkQ).quotKerEquivOfSurjective
      (LinearMap.baseChangePi_surjective (DualNumber k)
        (Submodule.mkQ_surjective K)))

/-! ### The shear automorphism -/

/-- `ε · inl c = c · ε` in the dual numbers. -/
lemma eps_mul_inl_fst (c : DualNumber k) :
    (DualNumber.eps : DualNumber k) * TrivSqZeroExt.inl c.fst =
      c * DualNumber.eps := by
  rw [eps_mul_eq_inr_fst, TrivSqZeroExt.fst_inl]
  ext
  · rw [TrivSqZeroExt.fst_inr, TrivSqZeroExt.fst_mul, DualNumber.fst_eps, mul_zero]
  · rw [TrivSqZeroExt.snd_inr, DualNumber.snd_mul, DualNumber.fst_eps,
      DualNumber.snd_eps, mul_one, mul_zero, add_zero]

/-- The infinitesimal shear of `k[ε]^n` along a `k`-linear endomorphism `g` of `k^n`:
`x ↦ x + ε · g(fst x)`. -/
def dualShearMap (g : (Fin n → k) →ₗ[k] (Fin n → k)) :
    (Fin n → DualNumber k) →ₗ[DualNumber k] (Fin n → DualNumber k) where
  toFun x := x + (DualNumber.eps : DualNumber k) • dualInlPi (g (dualFstPi x))
  map_add' x y := by
    rw [dualFstPi_add, map_add, dualInlPi_add, smul_add]
    abel
  map_smul' c x := by
    rw [RingHom.id_apply, dualFstPi_smul, map_smul, smul_add]
    congr 1
    have hsmul : dualInlPi (c.fst • g (dualFstPi x)) =
        (TrivSqZeroExt.inl c.fst : DualNumber k) • dualInlPi (g (dualFstPi x)) := by
      funext i
      rw [Pi.smul_apply, dualInlPi_apply, dualInlPi_apply, smul_eq_mul,
        TrivSqZeroExt.inl_mul_inl, Pi.smul_apply, smul_eq_mul]
    rw [hsmul, smul_smul, smul_smul, eps_mul_inl_fst]

@[simp] lemma dualShearMap_apply (g : (Fin n → k) →ₗ[k] (Fin n → k))
    (x : Fin n → DualNumber k) :
    dualShearMap g x = x + (DualNumber.eps : DualNumber k) •
      dualInlPi (g (dualFstPi x)) := rfl

/-- The infinitesimal shear as a `k[ε]`-linear automorphism. -/
def dualShear (g : (Fin n → k) →ₗ[k] (Fin n → k)) :
    (Fin n → DualNumber k) ≃ₗ[DualNumber k] (Fin n → DualNumber k) := by
  refine LinearEquiv.ofLinearMap (dualShearMap g) (dualShearMap (-g)) ?_ ?_
  · apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.id_apply, dualShearMap_apply,
      dualShearMap_apply, LinearMap.neg_apply, dualFstPi_add, dualFstPi_eps_smul,
      add_zero, dualInlPi_neg, smul_neg]
    abel
  · apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.id_apply, dualShearMap_apply,
      dualShearMap_apply, LinearMap.neg_apply, dualFstPi_add, dualFstPi_eps_smul,
      add_zero, dualInlPi_neg, smul_neg]
    abel

lemma dualShear_apply (g : (Fin n → k) →ₗ[k] (Fin n → k))
    (x : Fin n → DualNumber k) :
    dualShear g x = x + (DualNumber.eps : DualNumber k) •
      dualInlPi (g (dualFstPi x)) := rfl

/-- The shear along `g` carries the zero lift to the lift attached to `φ`, provided
`g` reduces to `φ` on `K`. -/
lemma map_dualShear_dualNumberLift_zero (φ : K →ₗ[k] ((Fin n → k) ⧸ K))
    (g : (Fin n → k) →ₗ[k] (Fin n → k))
    (hg : ∀ v : K, Submodule.Quotient.mk (g v.1) = φ v) :
    (dualNumberLift (0 : K →ₗ[k] ((Fin n → k) ⧸ K))).map
        (dualShear g).toLinearMap = dualNumberLift φ := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨v, hv, hv'⟩, rfl⟩
    rw [LinearMap.zero_apply] at hv'
    have hsnd : dualSndPi x ∈ K := (Submodule.Quotient.mk_eq_zero K).mp hv'
    have happ : (dualShear g).toLinearMap x = x + (DualNumber.eps : DualNumber k) •
        dualInlPi (g (dualFstPi x)) := rfl
    rw [happ]
    refine ⟨v, ?_, ?_⟩
    · rw [dualFstPi_add, dualFstPi_eps_smul, add_zero, hv]
    · rw [dualSndPi_add, dualSndPi_eps_smul, dualFstPi_inlPi,
        Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero K).mpr hsnd,
        zero_add, hv, hg v]
  · rintro y ⟨v, hv, hv'⟩
    refine ⟨y - (DualNumber.eps : DualNumber k) • dualInlPi (g (dualFstPi y)),
      ⟨v, ?_, ?_⟩, ?_⟩
    · rw [dualFstPi_sub, dualFstPi_eps_smul, sub_zero, hv]
    · rw [LinearMap.zero_apply, dualSndPi_sub, dualSndPi_eps_smul, dualFstPi_inlPi,
        Submodule.Quotient.mk_sub, hv', hv, hg v, sub_self]
    · have happ : (dualShear g).toLinearMap
          (y - (DualNumber.eps : DualNumber k) • dualInlPi (g (dualFstPi y))) =
          (y - (DualNumber.eps : DualNumber k) • dualInlPi (g (dualFstPi y))) +
            (DualNumber.eps : DualNumber k) • dualInlPi (g (dualFstPi
              (y - (DualNumber.eps : DualNumber k) •
                dualInlPi (g (dualFstPi y))))) := rfl
      rw [happ, dualFstPi_sub, dualFstPi_eps_smul, sub_zero]
      abel

/-- A reducing endomorphism exists for every `φ`: extend `φ` off `K` and lift along the
quotient map. -/
lemma exists_dualShear_reduction (φ : K →ₗ[k] ((Fin n → k) ⧸ K)) :
    ∃ g : (Fin n → k) →ₗ[k] (Fin n → k),
      ∀ v : K, Submodule.Quotient.mk (g v.1) = φ v := by
  obtain ⟨φ', hφ'⟩ := LinearMap.exists_extend φ
  obtain ⟨σ, hσ⟩ := K.mkQ.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective K))
  refine ⟨σ ∘ₗ φ', fun v ↦ ?_⟩
  have h1 : Submodule.Quotient.mk (p := K) ((σ ∘ₗ φ') v.1) =
      K.mkQ (σ (φ' v.1)) := rfl
  rw [h1, ← LinearMap.comp_apply, hσ, LinearMap.id_apply, ← hφ']
  rfl

/-- The quotient by any lift is isomorphic to the base change of `k^n/K`; in
particular it is finite free over the dual numbers. -/
noncomputable def dualNumberLiftQuotientEquiv (φ : K →ₗ[k] ((Fin n → k) ⧸ K)) :
    ((Fin n → DualNumber k) ⧸ dualNumberLift φ) ≃ₗ[DualNumber k]
      (DualNumber k) ⊗[k] ((Fin n → k) ⧸ K) :=
  ((Submodule.Quotient.equiv _ _
      (dualShear (exists_dualShear_reduction φ).choose)
      (map_dualShear_dualNumberLift_zero φ _
        (exists_dualShear_reduction φ).choose_spec)).symm.trans
    dualNumberLiftZeroQuotientEquiv)

/-- The quotient by a lift is free over the dual numbers. -/
lemma dualNumberLift_free (φ : K →ₗ[k] ((Fin n → k) ⧸ K)) :
    Module.Free (DualNumber k)
      ((Fin n → DualNumber k) ⧸ dualNumberLift φ) :=
  Module.Free.of_equiv (dualNumberLiftQuotientEquiv φ).symm

/-- The quotient by a lift has constant stalk rank `dim_k (k^n/K)`. -/
lemma rankAtStalk_dualNumberLift (φ : K →ₗ[k] ((Fin n → k) ⧸ K))
    (p : PrimeSpectrum (DualNumber k)) :
    Module.rankAtStalk ((Fin n → DualNumber k) ⧸ dualNumberLift φ) p =
      Module.finrank k ((Fin n → k) ⧸ K) := by
  have _i : Module.Free (DualNumber k)
      ((Fin n → DualNumber k) ⧸ dualNumberLift φ) := dualNumberLift_free φ
  rw [congrFun (Module.rankAtStalk_eq_finrank_of_free
    (R := DualNumber k) (M := (Fin n → DualNumber k) ⧸ dualNumberLift φ)) p]
  change Module.finrank (DualNumber k) _ = _
  rw [(dualNumberLiftQuotientEquiv φ).finrank_eq]
  exact Module.finrank_baseChange (R := DualNumber k) (S := k)
    (M' := (Fin n → k) ⧸ K)

/-! ### Injectivity -/

/-- Distinct homomorphisms give distinct lifts. -/
lemma dualNumberLift_injective :
    Function.Injective
      (dualNumberLift : (K →ₗ[k] ((Fin n → k) ⧸ K)) →
        Submodule (DualNumber k) (Fin n → DualNumber k)) := by
  intro φ ψ h
  apply LinearMap.ext
  intro v
  obtain ⟨x, hx, hfst⟩ := exists_mem_dualNumberLift_fstPi_eq φ v
  obtain ⟨vφ, hvφ, hφ⟩ := hx
  have hx' : x ∈ dualNumberLift ψ := by rw [← h]; exact ⟨vφ, hvφ, hφ⟩
  obtain ⟨vψ, hvψ, hψ⟩ := hx'
  have hvφv : vφ = v := Subtype.ext (by rw [← hvφ, hfst])
  have hvψv : vψ = v := Subtype.ext (by rw [← hvψ, hfst])
  rw [← hvφv, ← hφ, hvφv, ← hvψv, hψ, hvψv]

/-! ### Surjectivity -/

/-- In a free module over the dual numbers, an element annihilated by `ε` is a multiple
of `ε`. -/
lemma exists_eq_eps_smul_of_eps_smul_eq_zero {M : Type*} [AddCommGroup M]
    [Module (DualNumber k) M] [Module.Free (DualNumber k) M] (m : M)
    (h : (DualNumber.eps : DualNumber k) • m = 0) :
    ∃ m', m = (DualNumber.eps : DualNumber k) • m' := by
  classical
  let b := Module.Free.chooseBasis (DualNumber k) M
  have hrepr : ∀ i, (DualNumber.eps : DualNumber k) * b.repr m i = 0 := by
    intro i
    have h0 := congrArg (fun z ↦ b.repr z i) h
    simpa [map_smul, smul_eq_mul] using h0
  have hfst : ∀ i, (b.repr m i).fst = 0 := by
    intro i
    have h1 := congrArg TrivSqZeroExt.snd (hrepr i)
    rwa [eps_mul_eq_inr_fst, TrivSqZeroExt.snd_inr, TrivSqZeroExt.snd_zero] at h1
  refine ⟨b.repr.symm ((b.repr m).mapRange (fun x ↦ TrivSqZeroExt.inl x.snd)
    (by rw [TrivSqZeroExt.snd_zero, TrivSqZeroExt.inl_zero])), ?_⟩
  apply b.repr.injective
  rw [map_smul, LinearEquiv.apply_symm_apply]
  refine Finsupp.ext fun i ↦ ?_
  rw [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, eps_mul_eq_inr_fst,
    TrivSqZeroExt.fst_inl]
  conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq (b.repr m i)]
  rw [hfst i, TrivSqZeroExt.inl_zero, zero_add]

/-- The image of the scalar parts of a submodule of `k[ε]^n`, as a subspace of
`k^n`. -/
def dualFstImage (N : Submodule (DualNumber k) (Fin n → DualNumber k)) :
    Submodule k (Fin n → k) where
  carrier := dualFstPi '' (N : Set (Fin n → DualNumber k))
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, N.add_mem hx hy, by rw [dualFstPi_add]⟩
  zero_mem' := ⟨0, N.zero_mem, dualFstPi_zero⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    refine ⟨TrivSqZeroExt.inl c • x, N.smul_mem _ hx, ?_⟩
    rw [dualFstPi_smul, TrivSqZeroExt.fst_inl (M := k)]

@[simp] lemma mem_dualFstImage {N : Submodule (DualNumber k) (Fin n → DualNumber k)}
    {v : Fin n → k} :
    v ∈ dualFstImage N ↔ ∃ x ∈ N, dualFstPi x = v :=
  Iff.rfl

/-- If the span of the scalar parts of `N` is `K` then every element of `K` is a
scalar part. -/
lemma dualFstImage_eq_of_span_eq
    {N : Submodule (DualNumber k) (Fin n → DualNumber k)}
    (hN : Submodule.span k (dualFstPi '' (N : Set (Fin n → DualNumber k))) = K) :
    dualFstImage N = K := by
  rw [← hN]
  exact (Submodule.span_eq (dualFstImage N)).symm

/-- Well-definedness of the induced homomorphism: two elements of a lift with
projective quotient sharing a scalar part have infinitesimal parts congruent
modulo `K`. -/
lemma sndPi_congr_of_mem {N : Submodule (DualNumber k) (Fin n → DualNumber k)}
    (hproj : Module.Projective (DualNumber k) ((Fin n → DualNumber k) ⧸ N))
    (hspan : Submodule.span k (dualFstPi '' (N : Set (Fin n → DualNumber k))) = K)
    {x y : Fin n → DualNumber k} (hx : x ∈ N) (hy : y ∈ N)
    (hfst : dualFstPi x = dualFstPi y) :
    Submodule.Quotient.mk (p := K) (dualSndPi x) =
      Submodule.Quotient.mk (dualSndPi y) := by
  have _i1 : Module.Finite (DualNumber k) ((Fin n → DualNumber k) ⧸ N) :=
    Module.Finite.of_surjective N.mkQ (Submodule.mkQ_surjective N)
  have _i2 : Module.Flat (DualNumber k) ((Fin n → DualNumber k) ⧸ N) := by
    have := hproj
    exact Module.Flat.of_projective
  have _i3 : Module.Free (DualNumber k) ((Fin n → DualNumber k) ⧸ N) :=
    Module.free_of_flat_of_isLocalRing
  -- the difference has vanishing scalar part
  have hdN : x - y ∈ N := N.sub_mem hx hy
  have hdfst : dualFstPi (x - y) = 0 := by
    rw [dualFstPi_sub, hfst, sub_self]
  -- `x - y = ε • inl (snd (x - y))`, so `ε` kills the class of `inl (snd (x - y))`
  have hdd : x - y = (DualNumber.eps : DualNumber k) •
      dualInlPi (dualSndPi (x - y)) := by
    conv_lhs => rw [eq_inlPi_fstPi_add_eps_smul (x - y)]
    rw [hdfst, dualInlPi_zero, zero_add]
  have hkill : (DualNumber.eps : DualNumber k) •
      (Submodule.Quotient.mk (dualInlPi (dualSndPi (x - y))) :
        (Fin n → DualNumber k) ⧸ N) = 0 := by
    rw [← Submodule.Quotient.mk_smul, ← hdd, Submodule.Quotient.mk_eq_zero]
    exact hdN
  obtain ⟨m', hm'⟩ := exists_eq_eps_smul_of_eps_smul_eq_zero _ hkill
  obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective N m'
  rw [← hu, ← Submodule.Quotient.mk_smul] at hm'
  have hmem : dualInlPi (dualSndPi (x - y)) -
      (DualNumber.eps : DualNumber k) • u ∈ N := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hm', sub_self]
  have hsnd_mem : dualSndPi (x - y) ∈ K := by
    rw [← dualFstImage_eq_of_span_eq hspan]
    refine ⟨_, hmem, ?_⟩
    rw [dualFstPi_sub, dualFstPi_inlPi, dualFstPi_eps_smul, sub_zero]
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, ← dualSndPi_sub,
    Submodule.Quotient.mk_eq_zero]
  exact hsnd_mem

/-- A lift with projective quotient restricting to `K` arises from a unique
homomorphism. -/
lemma exists_dualNumberLift_eq
    {N : Submodule (DualNumber k) (Fin n → DualNumber k)}
    (hproj : Module.Projective (DualNumber k) ((Fin n → DualNumber k) ⧸ N))
    (hspan : Submodule.span k (dualFstPi '' (N : Set (Fin n → DualNumber k))) = K) :
    ∃ φ : K →ₗ[k] ((Fin n → k) ⧸ K), dualNumberLift φ = N := by
  classical
  have hK := dualFstImage_eq_of_span_eq hspan
  -- choose, for each `v ∈ K`, an element of `N` with scalar part `v`
  have hchoice : ∀ v : K, ∃ x, x ∈ N ∧ dualFstPi x = v.1 := by
    intro v
    have hv : v.1 ∈ dualFstImage N := by rw [hK]; exact v.2
    obtain ⟨x, hx, hfst⟩ := hv
    exact ⟨x, hx, hfst⟩
  choose sec hsecN hsecFst using hchoice
  -- the induced function
  let f : K → ((Fin n → k) ⧸ K) := fun v ↦ Submodule.Quotient.mk (dualSndPi (sec v))
  have hf_spec : ∀ (v : K) (x : Fin n → DualNumber k), x ∈ N → dualFstPi x = v.1 →
      f v = Submodule.Quotient.mk (dualSndPi x) := by
    intro v x hx hfst
    exact sndPi_congr_of_mem hproj hspan (hsecN v) hx ((hsecFst v).trans hfst.symm)
  have hf_add : ∀ v w : K, f (v + w) = f v + f w := by
    intro v w
    have hmem : sec v + sec w ∈ N := N.add_mem (hsecN v) (hsecN w)
    have hfst : dualFstPi (sec v + sec w) = (v + w).1 := by
      rw [dualFstPi_add, hsecFst v, hsecFst w]
      rfl
    rw [hf_spec (v + w) _ hmem hfst, dualSndPi_add, Submodule.Quotient.mk_add]
  have hf_smul : ∀ (c : k) (v : K), f (c • v) = c • f v := by
    intro c v
    have hmem : (TrivSqZeroExt.inl c : DualNumber k) • sec v ∈ N :=
      N.smul_mem _ (hsecN v)
    have hfst : dualFstPi ((TrivSqZeroExt.inl c : DualNumber k) • sec v) =
        (c • v).1 := by
      rw [dualFstPi_smul, TrivSqZeroExt.fst_inl (M := k), hsecFst v]
      rfl
    rw [hf_spec (c • v) _ hmem hfst, dualSndPi_smul, TrivSqZeroExt.fst_inl (M := k),
      TrivSqZeroExt.snd_inl (M := k), zero_smul, add_zero,
      Submodule.Quotient.mk_smul]
  let φ : K →ₗ[k] ((Fin n → k) ⧸ K) :=
    { toFun := f
      map_add' := hf_add
      map_smul' := hf_smul }
  refine ⟨φ, ?_⟩
  apply le_antisymm
  · rintro x ⟨v, hv, hx'⟩
    -- `x` and `sec v` share scalar parts; conclude `x ∈ N`
    have hx'' : Submodule.Quotient.mk (dualSndPi x) = f v := hx'
    have hsec : f v = Submodule.Quotient.mk (dualSndPi (sec v)) := rfl
    -- difference of infinitesimal parts lies in `K`
    have hdiff : dualSndPi x - dualSndPi (sec v) ∈ K := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, hx'', hsec,
        sub_self]
    -- write the difference as a scalar part of an element of `N`
    have hdiff' : dualSndPi x - dualSndPi (sec v) ∈ dualFstImage N := by
      rw [hK]; exact hdiff
    obtain ⟨z, hz, hzfst⟩ := hdiff'
    -- verify directly that `x - sec v - ε • z` vanishes
    have hzero : x - sec v - (DualNumber.eps : DualNumber k) • z = 0 := by
      have hfst0 : dualFstPi (x - sec v - (DualNumber.eps : DualNumber k) • z)
          = 0 := by
        rw [dualFstPi_sub, dualFstPi_sub, dualFstPi_eps_smul, sub_zero, hv,
          hsecFst v, sub_self]
      have hsnd0 : dualSndPi (x - sec v - (DualNumber.eps : DualNumber k) • z)
          = 0 := by
        rw [dualSndPi_sub, dualSndPi_sub, dualSndPi_eps_smul, hzfst]
        abel
      funext i
      have h1 := congrFun hfst0 i
      have h2 := congrFun hsnd0 i
      rw [dualFstPi_apply, Pi.zero_apply] at h1
      rw [dualSndPi_apply, Pi.zero_apply] at h2
      rw [Pi.zero_apply]
      ext
      · exact h1
      · exact h2
    have hxeq : x = sec v + (DualNumber.eps : DualNumber k) • z := by
      rw [sub_sub] at hzero
      exact sub_eq_zero.mp hzero
    rw [hxeq]
    exact N.add_mem (hsecN v) (N.smul_mem _ hz)
  · intro x hx
    exact ⟨⟨dualFstPi x, by rw [← hK]; exact ⟨x, hx, rfl⟩⟩, rfl,
      (hf_spec _ x hx rfl).symm⟩

/-- **The tangent space to the Grassmannian**: lifts of the point `K ⊆ k^n` of
`Gr(q, n)` to the dual numbers — submodules of `k[ε]^n` with projective quotient whose
scalar part spans `K` — are in bijection with `k`-linear maps `K → k^n/K`. -/
noncomputable def dualNumberLiftEquiv (K : Submodule k (Fin n → k)) :
    (K →ₗ[k] ((Fin n → k) ⧸ K)) ≃
      {N : Submodule (DualNumber k) (Fin n → DualNumber k) //
        Module.Projective (DualNumber k) ((Fin n → DualNumber k) ⧸ N) ∧
        Submodule.span k (dualFstPi '' (N : Set (Fin n → DualNumber k))) = K} := by
  refine Equiv.ofBijective
    (fun φ ↦ ⟨dualNumberLift φ, ?_, span_fst_image_dualNumberLift φ⟩) ⟨?_, ?_⟩
  · have := dualNumberLift_free φ
    exact Module.Projective.of_free
  · intro φ ψ h
    exact dualNumberLift_injective (congrArg Subtype.val h)
  · rintro ⟨N, hproj, hspan⟩
    obtain ⟨φ, hφ⟩ := exists_dualNumberLift_eq hproj hspan
    exact ⟨φ, Subtype.ext hφ⟩

end Submodule
