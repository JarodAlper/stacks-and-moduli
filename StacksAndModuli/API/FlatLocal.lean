module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Ideal.Span

/-!
# Flatness over a base ring is local on the spectrum

Supporting API with no Stacks Project counterpart of its own.

§2.1 needs to check flatness of the sections of a quasi-coherent sheaf over an *external*
coefficient ring `R₀` — i.e. flatness of an `A`-module regarded as an `R₀`-module along
`R₀ → A` — and to do so basic-open by basic-open. That requires two directions:

- flatness passes from global sections to each localization (`of_isLocalizedModule_of_flat_base`);
- flatness of all the localizations along a spanning family implies flatness of the whole
  (`of_isLocalizedModule_span_of_isScalarTower`).

Mathlib has the corresponding statements for flatness over the *same* ring
(`Mathlib/RingTheory/Flat/Localization.lean`: `Module.flat_of_isLocalized_span`,
`Module.Flat.of_isLocalizedModule`), but not for flatness over a base ring `R₀` mapping into
`A`, which is what the scalar-tower hypotheses here express.

**Proof route.** Both reduce to the same-ring statements. Since `R₀ → A` makes every
localization `M_r` an `R₀`-algebra compatibly, flatness over `R₀` is detected on the
localizations exactly as flatness over `A` is: tensoring with `M` commutes with localization, and
a family of localizations at a spanning set of `A` is jointly faithfully flat. Concretely,
compose Mathlib's `Module.flat_of_isLocalized_span` with the scalar-tower transfer.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v w z

open TensorProduct

namespace Module.Flat

/-- The kernel term in a short exact sequence of flat modules is flat, with the base ring
and the three module types allowed to live in independent universes. -/
theorem of_shortExact_general {R : Type u} {A : Type v} {B : Type w} {N : Type z}
    [CommRing R]
    [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B]
    [AddCommGroup N] [Module R N]
    (f : A →ₗ[R] B) (g : B →ₗ[R] N)
    (hf : Function.Injective f) (hex : Function.Exact f g)
    (hg : Function.Surjective g) [Module.Flat R B] [Module.Flat R N] :
    Module.Flat R A := by
  rw [Module.Flat.iff_rTensor_injective']
  intro Q x y hxy
  have hcomm (t : Q ⊗[R] A) :
      (LinearMap.rTensor B Q.subtype) (LinearMap.lTensor Q f t) =
        LinearMap.lTensor R f (LinearMap.rTensor A Q.subtype t) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul q a => rfl
    | add t₁ t₂ ht₁ ht₂ => simp only [map_add, ht₁, ht₂]
  have hBinj : Function.Injective (LinearMap.rTensor B Q.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap Q.subtype Subtype.val_injective
  have hfx : LinearMap.lTensor Q f x = LinearMap.lTensor Q f y := by
    apply hBinj
    rw [hcomm, hcomm, hxy]
  exact LinearMap.lTensor_injective_of_exact_of_flat g hg f hf hex Q hfx

/-- Flatness over a base ring passes to a localization of the module. -/
theorem of_isLocalizedModule_of_flat_base (R₀ : Type u) {A : Type v} {N Nₗ : Type w}
    [CommRing R₀] [CommRing A] [Algebra R₀ A]
    [AddCommGroup N] [Module A N] [Module R₀ N] [IsScalarTower R₀ A N]
    [AddCommGroup Nₗ] [Module A Nₗ] [Module R₀ Nₗ] [IsScalarTower R₀ A Nₗ]
    (S : Submonoid A) (res : N →ₗ[A] Nₗ) [IsLocalizedModule S res]
    [Module.Flat R₀ N] : Module.Flat R₀ Nₗ := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ f hf
  -- the fibre map over `Nₗ` is the localization of the fibre map over `N`
  have hNinj : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor A N f) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := N) f hf
  have hmap := IsLocalizedModule.map_injective S
    (TensorProduct.AlgebraTensorModule.rTensor R₀ P res)
    (TensorProduct.AlgebraTensorModule.rTensor R₀ Q res)
    (TensorProduct.AlgebraTensorModule.lTensor A N f) hNinj
  rw [IsLocalizedModule.map_lTensor] at hmap
  exact hmap

/-- Flatness over a base ring is detected on a spanning family of localizations. -/
theorem of_isLocalizedModule_span_of_isScalarTower {R₀ : Type u} {A : Type v} {N : Type w}
    [CommRing R₀] [CommRing A] [Algebra R₀ A]
    [AddCommGroup N] [Module A N] [Module R₀ N] [IsScalarTower R₀ A N]
    (s : Set A) (hs : Ideal.span s = ⊤)
    (Mₗ : s → Type z) [∀ r : s, AddCommGroup (Mₗ r)] [∀ r : s, Module A (Mₗ r)]
    [∀ r : s, Module R₀ (Mₗ r)] [∀ r : s, IsScalarTower R₀ A (Mₗ r)]
    (res : ∀ r : s, N →ₗ[A] Mₗ r) [∀ r : s, IsLocalizedModule.Away (r : A) (res r)]
    (hflat : ∀ r : s, Module.Flat R₀ (Mₗ r)) :
    Module.Flat R₀ N := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ f hf
  intro x y hxy
  -- the difference vanishes in each localized fibre
  have hz : (TensorProduct.AlgebraTensorModule.lTensor A N f) (x - y) = 0 := by
    have hx : (TensorProduct.AlgebraTensorModule.lTensor A N f) x =
        LinearMap.lTensor N f x := rfl
    have hy : (TensorProduct.AlgebraTensorModule.lTensor A N f) y =
        LinearMap.lTensor N f y := rfl
    rw [map_sub, hx, hy, hxy, sub_self]
  have hloc : ∀ r : s,
      (TensorProduct.AlgebraTensorModule.rTensor R₀ P (res r)) (x - y) = 0 := by
    intro r
    haveI := hflat r
    have hinj : Function.Injective
        (TensorProduct.AlgebraTensorModule.lTensor A (Mₗ r) f) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := Mₗ r) f hf
    apply hinj
    have hcomm := LinearMap.congr_fun
      (IsLocalizedModule.map_comp (Submonoid.powers (r : A))
        (TensorProduct.AlgebraTensorModule.rTensor R₀ P (res r))
        (TensorProduct.AlgebraTensorModule.rTensor R₀ Q (res r))
        (TensorProduct.AlgebraTensorModule.lTensor A N f)) (x - y)
    simp only [LinearMap.comp_apply] at hcomm
    rw [IsLocalizedModule.map_lTensor] at hcomm
    rw [hcomm, hz, map_zero, map_zero]
  -- an element vanishing in all localizations of a spanning family is zero
  have hsub : x - y ∈ (⊥ : Submodule A (TensorProduct R₀ N P)) := by
    refine Submodule.mem_of_isLocalized_span s hs _
      (fun r ↦ TensorProduct.AlgebraTensorModule.rTensor R₀ P (res r)) ?_
    intro r
    rw [hloc r]
    exact Submodule.zero_mem _
  have hzero : x - y = 0 := by simpa using hsub
  exact sub_eq_zero.mp hzero

end Module.Flat
