module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Nakayama

/-!
# Flatness of filtered colimits, finite products and kernels; Nakayama over all residue fields

Supporting API with no Stacks Project counterpart, filling four gaps in Mathlib's module API
that the relative cohomology of `ℙⁿ_R` needs.

* `Module.Flat.directLimit`: a filtered colimit of flat modules is flat.  This is what makes
  the Čech cochain groups of a family flat over the base — each `M[1/x_I]_d` is a sequential
  colimit of the flat pieces `M_{d+t·|I|}`.
* `Module.Flat.pi`: a finite product of flat modules is flat.  The Čech cochains are a finite
  product over the index set of the standard affine cover.
* `Module.Flat.of_shortExact`: for `0 → A → B → N → 0` with `B` and `N` flat, `A` is flat.
  This is the inductive step that walks the flatness of the Čech cochains down through the
  cocycle groups.

* `Module.subsingleton_of_forall_quotient_maximal`: a finite module that dies after `⊗ R/𝔪`
  for **every** maximal ideal `𝔪` is zero.  This is the Nakayama step that turns fibrewise
  vanishing of cohomology into vanishing over the base.

Main declarations:
- `Module.DirectLimit.map_injective`;
- `Module.Flat.directLimit`, `Module.Flat.pi`, `Module.Flat.of_shortExact`;
- `Module.subsingleton_of_forall_quotient_maximal`,
  `Module.surjective_of_forall_quotient_maximal`.
-/

@[expose] public section

universe u v w

open Module TensorProduct

namespace Module.DirectLimit

/-- The map induced on filtered colimits by a levelwise injective map of directed systems is
injective. -/
lemma map_injective {R : Type u} [Ring R] {ι : Type v} [DecidableEq ι]
    [Preorder ι] [IsDirectedOrder ι] {G : ι → Type*} [∀ i, AddCommGroup (G i)]
    [∀ i, Module R (G i)] {f : ∀ i j, i ≤ j → G i →ₗ[R] G j}
    {G' : ι → Type*} [∀ i, AddCommGroup (G' i)] [∀ i, Module R (G' i)]
    {f' : ∀ i j, i ≤ j → G' i →ₗ[R] G' j}
    [DirectedSystem G' fun i j h => f' i j h]
    (g : (i : ι) → G i →ₗ[R] G' i) (hg : ∀ i j h, g j ∘ₗ f i j h = f' i j h ∘ₗ g i)
    (hinj : ∀ i, Function.Injective (g i)) :
    Function.Injective (Module.DirectLimit.map g hg) := by
  cases isEmpty_or_nonempty ι
  · apply Function.injective_of_subsingleton
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨i, a, rfl⟩ := Module.DirectLimit.exists_of x
  rw [Module.DirectLimit.map_apply_of] at hx
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hx
  have h1 : g j (f i j hij a) = 0 := by
    have := LinearMap.congr_fun (hg i j hij) a
    simpa [hj] using this
  have h2 : f i j hij a = 0 := hinj j (by simpa using h1)
  rw [← Module.DirectLimit.of_f (hij := hij), h2, map_zero]

end Module.DirectLimit

namespace Module.Flat

variable {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι] [Preorder ι]
  [IsDirectedOrder ι] {G : ι → Type w} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  (f : ∀ i j, i ≤ j → G i →ₗ[R] G j)

/-- Tensoring a directed system on the right gives a directed system. -/
instance directedSystem_rTensor [DirectedSystem G fun i j h => f i j h] (N : Type*)
    [AddCommGroup N] [Module R N] :
    DirectedSystem (fun i => G i ⊗[R] N) (fun i j h => LinearMap.rTensor N (f i j h)) where
  map_self i x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [DirectedSystem.map_self (f := fun i j h => f i j h)]
    | add p q hp hq => simp [hp, hq]
  map_map {i j k} hij hjk x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [DirectedSystem.map_map (f := fun i j h => f i j h)]
    | add p q hp hq => simp [hp, hq]

/-- **A filtered colimit of flat modules is flat.**

The proof is Mathlib's submodule criterion `Module.Flat.iff_lTensor_injectiveₛ` combined with
`TensorProduct.directLimitLeft` (the tensor product commutes with filtered colimits) and
`Module.DirectLimit.map_injective` (a levelwise injective map of directed systems induces an
injective map of colimits). -/
lemma directLimit [Nonempty ι] [DirectedSystem G fun i j h => f i j h]
    [∀ i, Module.Flat R (G i)] : Module.Flat R (Module.DirectLimit G f) := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N
  have hcomm : ∀ i j (h : i ≤ j),
      (LinearMap.lTensor (G j) N.subtype) ∘ₗ (LinearMap.rTensor (N : Type u) (f i j h))
        = (LinearMap.rTensor P (f i j h)) ∘ₗ (LinearMap.lTensor (G i) N.subtype) := by
    intro i j h
    refine TensorProduct.ext' fun a b => ?_
    simp
  have hsq : ∀ x : (Module.DirectLimit G f) ⊗[R] N,
      TensorProduct.directLimitLeft f P
          (LinearMap.lTensor (Module.DirectLimit G f) N.subtype x)
        = Module.DirectLimit.map (fun i => LinearMap.lTensor (G i) N.subtype) hcomm
            (TensorProduct.directLimitLeft f (N : Type u) x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z b =>
        obtain ⟨i, a, rfl⟩ := Module.DirectLimit.exists_of z
        simp
    | add p q hp hq => simp [hp, hq]
  intro x y hxy
  refine (TensorProduct.directLimitLeft f (N : Type u)).injective ?_
  refine Module.DirectLimit.map_injective
    (fun i => LinearMap.lTensor (G i) N.subtype) hcomm
    (fun i => Module.Flat.lTensor_preserves_injective_linearMap (M := G i) N.subtype
      (Submodule.injective_subtype N)) ?_
  rw [← hsq, ← hsq, hxy]

/-- A finite product of flat modules is flat. -/
lemma pi {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι] (M : ι → Type w)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Flat R (M i)] :
    Module.Flat R (∀ i, M i) :=
  Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι M).symm

/-- **The kernel of a surjection of flat modules with flat kernel-quotient is flat**: if
`0 → A → B → N → 0` is exact with `B` and `N` flat, then `A` is flat.

The `Tor₁`-vanishing input is `LinearMap.lTensor_injective_of_exact_of_flat`. -/
lemma of_shortExact {R : Type u} [CommRing R] {A B N : Type v} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup N] [Module R N]
    (f : A →ₗ[R] B) (g : B →ₗ[R] N) (hf : Function.Injective f) (hex : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Flat R B] [Module.Flat R N] : Module.Flat R A := by
  rw [Module.Flat.iff_rTensor_injective']
  intro Q x y hxy
  have hsub : ∀ z : (Q : Type u) ⊗[R] A,
      LinearMap.rTensor B Q.subtype (LinearMap.lTensor (Q : Type u) f z)
        = LinearMap.lTensor R f (LinearMap.rTensor A Q.subtype z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp
    | add p q hp hq => simp [hp, hq]
  have hBinj : Function.Injective (LinearMap.rTensor B Q.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective
  have h1 : LinearMap.lTensor (Q : Type u) f x = LinearMap.lTensor (Q : Type u) f y := by
    refine hBinj ?_
    rw [hsub, hsub, hxy]
  exact LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hex _ h1

end Module.Flat

namespace Module

/-- **Nakayama, globally.** A finite module over a commutative ring that vanishes after
tensoring with every residue field `R ⧸ 𝔪` at a maximal ideal is itself zero.

One maximal ideal is not enough (`ℤ ⧸ 2` dies against `ℤ ⧸ 3`), and localization is not needed
either: pick a maximal ideal containing the annihilator, and Cayley–Hamilton
(`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`) produces `r ≡ 1` mod `𝔪`
annihilating the module, so `1 ∈ 𝔪`. -/
lemma subsingleton_of_forall_quotient_maximal {R : Type u} [CommRing R] {N : Type u}
    [AddCommGroup N] [Module R N] [Module.Finite R N]
    (h : ∀ m : Ideal R, m.IsMaximal → Subsingleton ((R ⧸ m) ⊗[R] N)) : Subsingleton N := by
  rw [← not_nontrivial_iff_subsingleton]
  intro hnt
  have hann : Module.annihilator R N ≠ ⊤ := by
    intro hc
    have h1 : (1 : R) ∈ Module.annihilator R N := hc ▸ Submodule.mem_top
    rw [Module.mem_annihilator] at h1
    exact (not_subsingleton_iff_nontrivial.mpr hnt) ⟨fun a b => by
      have ha := h1 a; have hb := h1 b; simp only [one_smul] at ha hb; rw [ha, hb]⟩
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hann
  have := h m hm
  have hsub : Subsingleton (N ⧸ (m • (⊤ : Submodule R N))) :=
    (TensorProduct.quotTensorEquivQuotSMul N m).symm.injective.subsingleton
  have htop : (⊤ : Submodule R N) = m • (⊤ : Submodule R N) := by
    refine le_antisymm (fun x _ => ?_) (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _)
    exact (Submodule.Quotient.mk_eq_zero (m • (⊤ : Submodule R N)) (x := x)).mp
      (Subsingleton.elim _ _)
  obtain ⟨r, hr1, hr2⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    m ⊤ Module.Finite.fg_top htop.le
  have hrann : r ∈ Module.annihilator R N :=
    Module.mem_annihilator.mpr fun n => hr2 n Submodule.mem_top
  have hone : (1 : R) ∈ m := by simpa using m.sub_mem (hle hrann) hr1
  exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hone isUnit_one)

/-- **Nakayama for surjectivity.** A map into a finite module is surjective as soon as it is
surjective after tensoring with every residue field `R ⧸ 𝔪`.

The cokernel is finite and its base change is the cokernel of the base change (right
exactness), so this is `Module.subsingleton_of_forall_quotient_maximal` applied to it. -/
lemma surjective_of_forall_quotient_maximal {R : Type u} [CommRing R] {U V : Type u}
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V] [Module.Finite R V]
    (φ : U →ₗ[R] V)
    (h : ∀ m : Ideal R, m.IsMaximal →
      Function.Surjective (LinearMap.baseChange (R ⧸ m) φ)) :
    Function.Surjective φ := by
  have hquot : ∀ (A : Type u) [CommRing A] [Algebra R A],
      Function.Surjective (LinearMap.baseChange A φ) →
      Subsingleton (A ⊗[R] (V ⧸ LinearMap.range φ)) := by
    intro A _ _ hs
    have hcomp : ∀ z : A ⊗[R] V,
        (LinearMap.baseChange A (LinearMap.range φ).mkQ) z = 0 := by
      intro z
      obtain ⟨w, rfl⟩ := hs z
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have h0 : (LinearMap.range φ).mkQ ∘ₗ φ = 0 :=
        LinearMap.ext fun x =>
          (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _)
      rw [h0]
      simp
    have hsurj : Function.Surjective (LinearMap.baseChange A (LinearMap.range φ).mkQ) :=
      LinearMap.baseChange_surjective A (Submodule.mkQ_surjective _)
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hsurj a
    obtain ⟨b', rfl⟩ := hsurj b
    rw [hcomp, hcomp]
  haveI : Module.Finite R (V ⧸ LinearMap.range φ) := Module.Finite.quotient R _
  have hs : Subsingleton (V ⧸ LinearMap.range φ) :=
    Module.subsingleton_of_forall_quotient_maximal (R := R)
      (N := V ⧸ LinearMap.range φ) (fun m hm => hquot (R ⧸ m) (h m hm))
  rw [← LinearMap.range_eq_top]
  exact Submodule.Quotient.subsingleton_iff.mp hs

end Module

end
