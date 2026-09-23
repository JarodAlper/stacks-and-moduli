module

public import Mathlib.RingTheory.Depth.Rees

/-!
# Module depth through Ext

For an ideal `I` and a module `M`, this file packages the assertion that
`Ext^i_R(R/I, M)` vanishes below a specified degree.  The quotient is replaced by
`Shrink (R ⧸ I)` so that it lies in the same universe as `M`, exactly as in Mathlib's
formulation of the Rees theorem.

The Rees theorem identifies this Ext-vanishing condition with the existence of an
`M`-regular sequence of the specified length in `I`.  The covariant long exact sequence
for Ext also gives the three standard depth-lemma transfers across a short exact sequence.

Main declarations:

* `ModuleCat.ExtDepthAtLeast`;
* `ModuleCat.extDepthAtLeast_iff_exists_isRegular`;
* `ModuleCat.ExtDepthAtLeast.shortExact_right`;
* `ModuleCat.ExtDepthAtLeast.shortExact_middle`;
* `ModuleCat.ExtDepthAtLeast.shortExact_left`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe v u

open CategoryTheory CategoryTheory.Abelian

namespace ModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- The test object `R/I`, shrunk into the universe of the ambient module category. -/
noncomputable abbrev extDepthTestObject (I : Ideal R) : ModuleCat.{v} R :=
  ModuleCat.of R (Shrink.{v} (R ⧸ I))

/-- A module has Ext-depth at least `n` along `I` when `Ext^i_R(R/I, M)` vanishes for
every `i < n`.

Vanishing is expressed by `Subsingleton`, the convention used by Mathlib's Ext API. -/
def ExtDepthAtLeast (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) : Prop :=
  ∀ i < n, Subsingleton (Ext (extDepthTestObject I) M i)

/-- The defining Ext-vanishing characterization of `ExtDepthAtLeast`. -/
theorem extDepthAtLeast_iff (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    ExtDepthAtLeast I M n ↔
      ∀ i < n, Subsingleton (Ext (extDepthTestObject I) M i) :=
  Iff.rfl

namespace ExtDepthAtLeast

/-- Every module has Ext-depth at least zero. -/
@[simp]
theorem zero (I : Ideal R) (M : ModuleCat.{v} R) : ExtDepthAtLeast I M 0 := by
  intro i hi
  omega

/-- Ext-depth is downward closed in the numerical bound. -/
theorem of_le {I : Ideal R} {M : ModuleCat.{v} R} {m n : ℕ}
    (h : ExtDepthAtLeast I M n) (hmn : m ≤ n) : ExtDepthAtLeast I M m := by
  intro i hi
  exact h i (hi.trans_le hmn)

end ExtDepthAtLeast

/-- Rees's theorem identifies Ext-depth along a proper-on-`M` ideal with the existence
of an `M`-regular sequence of the same length in that ideal. -/
theorem extDepthAtLeast_iff_exists_isRegular [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{v} R) [Module.Finite R M] (n : ℕ)
    (smul_lt : I • (⊤ : Submodule R M) < ⊤) :
    ExtDepthAtLeast I M n ↔
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧
        RingTheory.Sequence.IsRegular M rs := by
  change (∀ i < n, Subsingleton
    (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i)) ↔ _
  exact (ModuleCat.exists_isRegular_tfae I n M smul_lt).out 1 3

/-- Vanishing transfer at the right position of the covariant Ext long exact sequence. -/
theorem subsingleton_ext_of_shortExact_right
    {K : ModuleCat.{v} R} {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (h₂ : Subsingleton (Ext K S.X₂ n₀))
    (h₁ : Subsingleton (Ext K S.X₁ n₁)) :
    Subsingleton (Ext K S.X₃ n₀) := by
  have hex := Ext.covariant_sequence_exact₃' K hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hgx : (AddCommGrpCat.ofHom (hS.extClass.postcomp K h)).hom x = 0 :=
    Subsingleton.elim _ _
  obtain ⟨y, rfl⟩ := (hex x).mp hgx
  rw [Subsingleton.elim y 0]
  exact map_zero _

/-- Vanishing transfer at the middle position of the covariant Ext long exact sequence. -/
theorem subsingleton_ext_of_shortExact_middle
    {K : ModuleCat.{v} R} {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    {n : ℕ} (h₁ : Subsingleton (Ext K S.X₁ n))
    (h₃ : Subsingleton (Ext K S.X₃ n)) :
    Subsingleton (Ext K S.X₂ n) := by
  have hex := Ext.covariant_sequence_exact₂' K hS n
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hgx : (AddCommGrpCat.ofHom
      ((Ext.mk₀ S.g).postcomp K (add_zero n))).hom x = 0 :=
    Subsingleton.elim _ _
  obtain ⟨y, rfl⟩ := (hex x).mp hgx
  rw [Subsingleton.elim y 0]
  exact map_zero _

/-- Vanishing transfer at a positive degree of the left position of the covariant Ext
long exact sequence. -/
theorem subsingleton_ext_of_shortExact_left
    {K : ModuleCat.{v} R} {S : ShortComplex (ModuleCat.{v} R)} (hS : S.ShortExact)
    {n₀ n₁ : ℕ} (h : n₀ + 1 = n₁)
    (h₃ : Subsingleton (Ext K S.X₃ n₀))
    (h₂ : Subsingleton (Ext K S.X₂ n₁)) :
    Subsingleton (Ext K S.X₁ n₁) := by
  have hex := Ext.covariant_sequence_exact₁' K hS n₀ n₁ h
  rw [ShortComplex.ab_exact_iff_function_exact] at hex
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  have hgx : (AddCommGrpCat.ofHom
      ((Ext.mk₀ S.f).postcomp K (add_zero n₁))).hom x = 0 :=
    Subsingleton.elim _ _
  obtain ⟨y, rfl⟩ := (hex x).mp hgx
  rw [Subsingleton.elim y 0]
  exact map_zero _

namespace ExtDepthAtLeast

/-- In a short exact sequence, depth at least `n` for the middle term and depth at least
`n + 1` for the left term imply depth at least `n` for the right term. -/
theorem shortExact_right {I : Ideal R} {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) {n : ℕ}
    (h₂ : ExtDepthAtLeast I S.X₂ n)
    (h₁ : ExtDepthAtLeast I S.X₁ (n + 1)) :
    ExtDepthAtLeast I S.X₃ n := by
  intro i hi
  exact subsingleton_ext_of_shortExact_right hS rfl
    (h₂ i hi) (h₁ (i + 1) (by omega))

/-- In a short exact sequence, depth at least `n` for the left and right terms implies
depth at least `n` for the middle term. -/
theorem shortExact_middle {I : Ideal R} {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) {n : ℕ}
    (h₁ : ExtDepthAtLeast I S.X₁ n)
    (h₃ : ExtDepthAtLeast I S.X₃ n) :
    ExtDepthAtLeast I S.X₂ n := by
  intro i hi
  exact subsingleton_ext_of_shortExact_middle hS (h₁ i hi) (h₃ i hi)

/-- In a short exact sequence, depth at least `n + 1` for the middle term and depth at
least `n` for the right term imply depth at least `n + 1` for the left term. -/
theorem shortExact_left {I : Ideal R} {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) {n : ℕ}
    (h₂ : ExtDepthAtLeast I S.X₂ (n + 1))
    (h₃ : ExtDepthAtLeast I S.X₃ n) :
    ExtDepthAtLeast I S.X₁ (n + 1) := by
  intro i hi
  cases i with
  | zero =>
      let _ : Mono S.f := hS.mono_f
      let _ : Subsingleton (Ext (extDepthTestObject I) S.X₂ 0) := h₂ 0 (by omega)
      exact (Ext.postcomp_mk₀_injective_of_mono (extDepthTestObject I) S.f).subsingleton
  | succ i =>
      exact subsingleton_ext_of_shortExact_left hS rfl
        (h₃ i (by omega)) (h₂ (i + 1) (by omega))

end ExtDepthAtLeast

end ModuleCat

end
