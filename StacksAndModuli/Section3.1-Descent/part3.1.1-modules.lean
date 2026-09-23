module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Faithfully flat descent for modules: the Amitsur equalizer

This module formalizes Proposition 3.1.1 (`prop:descent-modules`) of §3.1 (Descent theory,
`sec:descent-theory`) of *Stacks and Moduli*:
for a faithfully flat ring map $R \to S$ and an $R$-module $M$, the sequence
$$0 \to M \to S \otimes_R M \rightrightarrows S \otimes_R S \otimes_R M$$
(Equation 3.1.2, `eqn:descent-modules`) is exact, where the two parallel maps insert $1$
in the first and second tensor factor. (The book writes base change on the right,
$M \otimes_A B$; following Mathlib conventions we write it on the left, $S \otimes_R M$.)

Main results:
- `Module.FaithfullyFlat.range_tensorProductMk`: the exactness of the Amitsur sequence,
  in the form `range (m ↦ 1 ⊗ₜ m) = eqLocus (x ↦ 1 ⊗ₜ x) (s ⊗ m ↦ s ⊗ 1 ⊗ m)`;
- recalls of the injectivity statements from Mathlib
  (`Module.FaithfullyFlat.tensorProduct_mk_injective`).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section PropDescentModules

open TensorProduct LinearMap

universe u v w

namespace Algebra.TensorProduct

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable (N : Type w) [AddCommGroup N] [Module R N]

/-- For an `R`-algebra `S` and an `R`-module `N`, the contraction map
`S ⊗[R] (S ⊗[R] N) →ₗ[R] S ⊗[R] N` multiplying the two `S`-factors:
`s ⊗ (s' ⊗ n) ↦ (s * s') ⊗ n`. -/
noncomputable def contractLeft : S ⊗[R] (S ⊗[R] N) →ₗ[R] S ⊗[R] N :=
  (LinearMap.rTensor N (LinearMap.mul' R S)).comp
    ((_root_.TensorProduct.assoc R S S N).symm.toLinearMap)

@[simp]
lemma contractLeft_tmul (s s' : S) (n : N) :
    contractLeft R S N (s ⊗ₜ (s' ⊗ₜ n)) = (s * s') ⊗ₜ n := by
  simp [contractLeft]

variable {N} in
/-- Contracting after inserting `1` in the first factor is the identity. -/
lemma contractLeft_one_tmul (x : S ⊗[R] N) :
    contractLeft R S N ((1 : S) ⊗ₜ x) = x := by
  induction x with
  | zero => simp [tmul_zero]
  | tmul s n => simp
  | add x y hx hy => rw [tmul_add, map_add, hx, hy]

end Algebra.TensorProduct

namespace Module.FaithfullyFlat

open Algebra.TensorProduct

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type w) [AddCommGroup M] [Module R M]

/-- The Amitsur sequence is a complex: `1 ⊗ₜ m` has equal images under the two insertion
maps `S ⊗[R] M →ₗ[R] S ⊗[R] (S ⊗[R] M)`. -/
lemma range_tensorProductMk_le_eqLocus :
    LinearMap.range (TensorProduct.mk R S M 1) ≤
      LinearMap.eqLocus (TensorProduct.mk R S (S ⊗[R] M) 1)
        (LinearMap.lTensor S (TensorProduct.mk R S M 1)) := by
  rintro - ⟨m, rfl⟩
  simp [LinearMap.mem_eqLocus]

/-- Contracting after applying the first insertion map (in the once base-changed Amitsur
sequence) is the identity. -/
lemma contractLeft_comp_lTensor_mk :
    (contractLeft R S (S ⊗[R] M)).comp
        (LinearMap.lTensor S (TensorProduct.mk R S (S ⊗[R] M) 1)) =
      LinearMap.id := by
  ext s m
  simp

/-- Contracting after applying the base change of the second insertion map equals the base
change of the inclusion applied to the contraction. -/
lemma contractLeft_comp_lTensor_lTensor_mk :
    (contractLeft R S (S ⊗[R] M)).comp
        (LinearMap.lTensor S (LinearMap.lTensor S (TensorProduct.mk R S M 1))) =
      (LinearMap.lTensor S (TensorProduct.mk R S M 1)).comp (contractLeft R S M) := by
  ext s s' m
  simp

variable {R S M} in
/-- After base change along `R → S`, the Amitsur sequence becomes exact by an explicit
contraction: an element `y` of `S ⊗[R] (S ⊗[R] M)` on which the base changes of the two
insertion maps agree lies in the image of the base change of `m ↦ 1 ⊗ₜ m`. -/
lemma exists_lTensor_tensorProductMk_eq_of_lTensor_eq {y : S ⊗[R] (S ⊗[R] M)}
    (hy : LinearMap.lTensor S (TensorProduct.mk R S (S ⊗[R] M) 1) y =
      LinearMap.lTensor S (LinearMap.lTensor S (TensorProduct.mk R S M 1)) y) :
    LinearMap.lTensor S (TensorProduct.mk R S M 1) (contractLeft R S M y) = y := by
  have hA := LinearMap.congr_fun (contractLeft_comp_lTensor_mk R S M) y
  have hB := LinearMap.congr_fun (contractLeft_comp_lTensor_lTensor_mk R S M) y
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hA hB
  rw [← hB, ← hy]
  exact hA

variable [Module.FaithfullyFlat R S]

/-- **Proposition 3.1.1** (`prop:descent-modules`), also **Equation 3.1.2**
(`eqn:descent-modules`) (module form): faithfully flat descent for modules, the Amitsur equalizer. Let
$R \to S$ be a faithfully flat ring map and $M$ an $R$-module. Then the sequence
$0 \to M \to S \otimes_R M \rightrightarrows S \otimes_R S \otimes_R M$ is exact: the image
of $m \mapsto 1 \otimes m$ is the equalizer of the two maps inserting $1$ in the first and
second tensor factor. (The injectivity of $m \mapsto 1 \otimes m$ is Mathlib's
`Module.FaithfullyFlat.tensorProduct_mk_injective`.) -/
theorem range_tensorProductMk :
    LinearMap.range (TensorProduct.mk R S M 1) =
      LinearMap.eqLocus (TensorProduct.mk R S (S ⊗[R] M) 1)
        (LinearMap.lTensor S (TensorProduct.mk R S M 1)) := by
  refine le_antisymm (range_tensorProductMk_le_eqLocus R S M) ?_
  set d₁ := TensorProduct.mk R S (S ⊗[R] M) 1
  set d₂ := LinearMap.lTensor S (TensorProduct.mk R S M 1)
  -- the corestriction `M →ₗ[R] eqLocus d₁ d₂` of `m ↦ 1 ⊗ₜ m`
  set e : M →ₗ[R] LinearMap.eqLocus d₁ d₂ :=
    (TensorProduct.mk R S M 1).codRestrict _
      (fun m ↦ range_tensorProductMk_le_eqLocus R S M ⟨m, rfl⟩) with he
  -- it suffices to prove that `e` is surjective
  suffices h : Function.Surjective e by
    intro x hx
    obtain ⟨m, hm⟩ := h ⟨x, hx⟩
    exact ⟨m, congrArg Subtype.val hm⟩
  -- by faithful flatness, it suffices to prove surjectivity after base change to `S`;
  -- flatness identifies `S ⊗ eqLocus d₁ d₂` with the equalizer of the base-changed maps
  refine (Module.FaithfullyFlat.lTensor_surjective_iff_surjective R S
    (N := M) (N' := LinearMap.eqLocus d₁ d₂) e).mp ?_
  have hval : ∀ z : S ⊗[R] M,
      ((LinearMap.tensorEqLocusEquiv S S d₁ d₂) (LinearMap.lTensor S e z) :
        S ⊗[R] (S ⊗[R] M)) = LinearMap.lTensor S (TensorProduct.mk R S M 1) z := by
    intro z
    rw [LinearMap.tensorEqLocusEquiv_apply, LinearMap.tensorEqLocus_coe,
      ← LinearMap.lTensor_comp_apply, LinearMap.subtype_comp_codRestrict]
  intro w'
  have hyval : LinearMap.lTensor S d₁
        ((LinearMap.tensorEqLocusEquiv S S d₁ d₂) w' : S ⊗[R] (S ⊗[R] M)) =
      LinearMap.lTensor S d₂
        ((LinearMap.tensorEqLocusEquiv S S d₁ d₂) w' : S ⊗[R] (S ⊗[R] M)) :=
    ((LinearMap.tensorEqLocusEquiv S S d₁ d₂) w').prop
  -- the contraction provides an explicit preimage
  refine ⟨contractLeft R S M
    ((LinearMap.tensorEqLocusEquiv S S d₁ d₂) w' : S ⊗[R] (S ⊗[R] M)), ?_⟩
  apply (LinearMap.tensorEqLocusEquiv S S d₁ d₂).injective
  apply Subtype.ext
  rw [hval]
  exact exists_lTensor_tensorProductMk_eq_of_lTensor_eq hyval

variable {R S M} in
/-- API lemma used in the proof of Proposition 3.1.1 (membership criterion): an element
`x : S ⊗[R] M` is of the form `1 ⊗ₜ m` if and only if its images under the two insertion
maps `S ⊗[R] M → S ⊗[R] S ⊗[R] M` agree. -/
theorem exists_one_tmul_eq_iff (x : S ⊗[R] M) :
    (∃ m, (1 : S) ⊗ₜ[R] m = x) ↔
      (1 : S) ⊗ₜ[R] x = LinearMap.lTensor S (TensorProduct.mk R S M 1) x := by
  constructor
  · rintro ⟨m, rfl⟩
    have h := range_tensorProductMk_le_eqLocus R S M
      (⟨m, rfl⟩ : (1 : S) ⊗ₜ[R] m ∈ LinearMap.range (TensorProduct.mk R S M 1))
    rw [LinearMap.mem_eqLocus] at h
    exact h
  · intro h
    have : x ∈ LinearMap.eqLocus (TensorProduct.mk R S (S ⊗[R] M) 1)
        (LinearMap.lTensor S (TensorProduct.mk R S M 1)) := by
      rw [LinearMap.mem_eqLocus]
      simpa using h
    rw [← range_tensorProductMk R S M] at this
    obtain ⟨m, hm⟩ := this
    exact ⟨m, hm⟩

variable {R S} in
/-- API lemma used in the proof of Proposition 3.1.1 (ring form, elementwise): an element $s$
of a faithfully flat $R$-algebra $S$ lies in the image of $R$ if and only if
$1 \otimes s = s \otimes 1$ in $S \otimes_R S$. -/
theorem exists_algebraMap_eq_iff (s : S) :
    (∃ r, algebraMap R S r = s) ↔ (1 : S) ⊗ₜ[R] s = s ⊗ₜ[R] (1 : S) := by
  constructor
  · rintro ⟨r, rfl⟩
    rw [Algebra.algebraMap_eq_smul_one, tmul_smul, smul_tmul']
  · intro h
    have h' : (1 : S) ⊗ₜ[R] (s ⊗ₜ[R] (1 : R)) =
        LinearMap.lTensor S (TensorProduct.mk R S R 1) (s ⊗ₜ[R] (1 : R)) := by
      apply (TensorProduct.congr (LinearEquiv.refl R S) (TensorProduct.rid R S)).injective
      simpa using h
    obtain ⟨r, hr⟩ := (exists_one_tmul_eq_iff (s ⊗ₜ[R] (1 : R))).mpr h'
    refine ⟨r, ?_⟩
    have := congrArg (TensorProduct.rid R S) hr
    simpa [Algebra.algebraMap_eq_smul_one] using this

/-- API lemma used in the proof of Proposition 3.1.1 (specialized ring form): for a faithfully flat ring
map $R \to S$ the sequence $0 \to R \to S \rightrightarrows S \otimes_R S$ is exact, the
two maps being $s \mapsto 1 \otimes s$ and $s \mapsto s \otimes 1$. (Injectivity of
$R \to S$ is Mathlib's `FaithfulSMul.algebraMap_injective`, available since faithfully flat
algebras are faithful.) -/
theorem range_linearMap :
    LinearMap.range (Algebra.linearMap R S) =
      LinearMap.eqLocus (TensorProduct.mk R S S 1) ((TensorProduct.mk R S S).flip 1) := by
  ext s
  rw [LinearMap.mem_eqLocus]
  simp only [TensorProduct.mk_apply, LinearMap.flip_apply, LinearMap.mem_range,
    Algebra.linearMap_apply]
  exact exists_algebraMap_eq_iff s

/- **Proposition 3.1.1** (`prop:descent-modules`) (injectivity part): for a faithfully flat
$R$-algebra $S$ and an $R$-module $M$, the map $M \to S \otimes_R M$, $m \mapsto
1 \otimes m$, is injective. This is Mathlib's
`Module.FaithfullyFlat.tensorProduct_mk_injective`. (A plain comment, not a docstring: an
anonymous `example` cannot carry one.) -/
example : Function.Injective (TensorProduct.mk R S M 1) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective M

end Module.FaithfullyFlat

end PropDescentModules
