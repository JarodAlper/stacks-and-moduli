module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Bezout

/-!
# Extending quotients across the generic fibre of a discrete valuation ring

Supporting API with no Stacks Project counterpart of its own, used by the formalization of
`prop:quot-proper` in §2.4.  This is the affine-local heart of the valuative criterion for the
Quot functor: over a discrete valuation ring `R` with uniformizer `ϖ`, quotients of a module
that are flat over `R` correspond bijectively to quotients of its generic fibre.

Setting: `B` is an `R`-algebra (the sections of the ambient scheme over an affine chart),
`B'` its localization away from `ϖ` (the sections of the generic fibre), `F` a `B`-module and
`j : F → F'` the corresponding localization of modules.  For a `B'`-submodule `N'` of `F'`
(the kernel of a quotient on the generic fibre), the **saturation** is `j⁻¹(N') ⊆ F`.  The
three main statements:

- `smul_mem_comapSubmodule` / `torsion_quotient_comapSubmodule_eq_bot` /
  `flat_quotient_comapSubmodule`: the quotient by the saturation is `R`-torsion-free, hence
  flat over the valuation ring `R` — the *existence* of the flat extension;
- `localized'_comapSubmodule`: the saturation restricts back to `N'` on the generic fibre —
  the extension *does* extend;
- `comapSubmodule_localized'_of_saturated`: a kernel saturated with respect to `ϖ`-powers
  (as the kernel of an `R`-flat quotient is) equals its own saturation — the *uniqueness* of
  the flat extension.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v w

namespace DVRQuotientExtension

variable {R : Type u} [CommRing R]
variable {B : Type v} [CommRing B] [Algebra R B]
variable {B' : Type v} [CommRing B'] [Algebra B B'] [Algebra R B']
  [IsScalarTower R B B']
variable {F : Type w} [AddCommGroup F] [Module B F]
variable {F' : Type w} [AddCommGroup F'] [Module B F'] [Module B' F']
  [IsScalarTower B B' F']
variable (ϖ : R)
variable (j : F →ₗ[B] F')
variable [IsLocalizedModule (Submonoid.powers (algebraMap R B ϖ)) j]

/-- The saturation of a submodule of the generic fibre: its preimage under the localization
map.  This is the kernel of the canonical flat extension of a quotient on the generic
fibre. -/
def comapSubmodule (N' : Submodule B' F') : Submodule B F :=
  (N'.restrictScalars B).comap j

@[simp]
lemma mem_comapSubmodule {N' : Submodule B' F'} {x : F} :
    x ∈ comapSubmodule j N' ↔ j x ∈ N' :=
  Iff.rfl

section Torsion

variable [IsDomain R] [IsDiscreteValuationRing R]
variable [IsLocalization.Away (algebraMap R B ϖ) B']

/-- Every nonzero element of `R` acts invertibly on the localized ring `B'`. -/
theorem isUnit_algebraMap_of_ne_zero
    [IsLocalization.Away (algebraMap R B ϖ) B'] (hϖ : Irreducible ϖ)
    {r : R} (hr : r ≠ 0) :
    IsUnit (algebraMap R B' r) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
  rw [map_mul, map_pow]
  refine IsUnit.mul (u.isUnit.map (algebraMap R B')) (IsUnit.pow n ?_)
  rw [IsScalarTower.algebraMap_apply R B B']
  exact IsLocalization.Away.algebraMap_isUnit (S := B') (algebraMap R B ϖ)

variable [Module R F] [IsScalarTower R B F]

/-- The quotient by a saturation is `R`-torsion-free: if `r • x` maps into `N'` for some
nonzero `r : R`, then so does `x`, because `r` acts invertibly on the generic fibre. -/
theorem smul_mem_comapSubmodule (hϖ : Irreducible ϖ) (N' : Submodule B' F')
    {r : R} (hr : r ≠ 0) {x : F} (hx : r • x ∈ comapSubmodule j N') :
    x ∈ comapSubmodule j N' := by
  rw [mem_comapSubmodule] at hx ⊢
  obtain ⟨v, hv⟩ := isUnit_algebraMap_of_ne_zero (B := B) (B' := B') ϖ hϖ hr
  have hj : j (r • x) = algebraMap R B' r • j x := by
    rw [show r • x = algebraMap R B r • x from (algebraMap_smul B r x).symm, map_smul,
      IsScalarTower.algebraMap_apply R B B']
    exact (algebraMap_smul B' (algebraMap R B r) (j x)).symm
  rw [hj, ← hv] at hx
  have hmem := N'.smul_mem ((v⁻¹ : B'ˣ) : B') hx
  rwa [smul_smul, Units.inv_mul, one_smul] at hmem

/-- The quotient by a saturation is `R`-torsion-free. -/
theorem torsion_quotient_comapSubmodule_eq_bot (hϖ : Irreducible ϖ)
    (N' : Submodule B' F') :
    Submodule.torsion R (F ⧸ comapSubmodule j N') = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro z ⟨⟨r, hr⟩, hrz⟩
  induction z using Submodule.Quotient.induction_on with
  | H x =>
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    have hrx : r • x ∈ comapSubmodule j N' := by
      rw [← Submodule.Quotient.mk_eq_zero]
      have : (Submodule.Quotient.mk (r • x) :
          F ⧸ comapSubmodule j N') = r • Submodule.Quotient.mk x := by
        rw [← Submodule.Quotient.mk_smul]
      rw [this]
      exact hrz
    rw [Submodule.Quotient.mk_eq_zero]
    exact smul_mem_comapSubmodule ϖ j hϖ N' hr0 hrx

/-- The quotient by a saturation is flat over the discrete valuation ring: torsion-free
modules over a valuation (in particular Bezout) domain are flat. -/
theorem flat_quotient_comapSubmodule (hϖ : Irreducible ϖ) (N' : Submodule B' F') :
    Module.Flat R (F ⧸ comapSubmodule j N') := by
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
  exact torsion_quotient_comapSubmodule_eq_bot ϖ j hϖ N'

end Torsion

section Extension

variable [IsLocalization.Away (algebraMap R B ϖ) B']

/-- The saturation restricts back to the original submodule on the generic fibre: the
localization of `j⁻¹(N')` is `N'`. -/
theorem localized'_comapSubmodule (N' : Submodule B' F') :
    Submodule.localized' B' (Submonoid.powers (algebraMap R B ϖ)) j
      (comapSubmodule j N') = N' := by
  apply le_antisymm
  · rintro x hx
    obtain ⟨m, hm, s, rfl⟩ := (Submodule.mem_localized' _ _ _ _ _).mp hx
    rw [mem_comapSubmodule] at hm
    obtain ⟨v, hv⟩ := IsLocalization.map_units B' s
    have hcancel : algebraMap B B' (s : B) • IsLocalizedModule.mk' j m s = j m := by
      rw [algebraMap_smul, ← Submonoid.smul_def, IsLocalizedModule.mk'_cancel']
    have hmem : algebraMap B B' (s : B) • IsLocalizedModule.mk' j m s ∈ N' := by
      rw [hcancel]; exact hm
    rw [← hv] at hmem
    have := N'.smul_mem ((v⁻¹ : B'ˣ) : B') hmem
    rwa [smul_smul, Units.inv_mul, one_smul] at this
  · intro n' hn'
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalizedModule.surj
      (Submonoid.powers (algebraMap R B ϖ)) j n'
    have hjx : j x ∈ N' := by
      rw [← hxs]
      have : (s : B) • n' = algebraMap B B' (s : B) • n' := (algebraMap_smul B' _ _).symm
      rw [Submonoid.smul_def, this]
      exact N'.smul_mem _ hn'
    refine (Submodule.mem_localized' _ _ _ _ _).mpr ⟨x, hjx, s, ?_⟩
    apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units j s)).1
    show (s : B) • IsLocalizedModule.mk' j x s = (s : B) • n'
    rw [← Submonoid.smul_def, IsLocalizedModule.mk'_cancel', ← Submonoid.smul_def, hxs]

end Extension

section Uniqueness

variable [IsLocalization.Away (algebraMap R B ϖ) B']

/-- A submodule saturated with respect to powers of `ϖ` — as the kernel of any `R`-flat
quotient is — equals the saturation of its own restriction to the generic fibre. -/
theorem comapSubmodule_localized'_of_saturated (N : Submodule B F)
    (hsat : ∀ (m : ℕ) (x : F), algebraMap R B ϖ ^ m • x ∈ N → x ∈ N) :
    comapSubmodule j
      (Submodule.localized' B' (Submonoid.powers (algebraMap R B ϖ)) j N) = N := by
  apply le_antisymm
  · intro x hx
    rw [mem_comapSubmodule] at hx
    obtain ⟨m, hm, s, hs⟩ := (Submodule.mem_localized' _ _ _ _ _).mp hx
    -- `s • j x = j m`, so some power of `ϖ` multiplies `x` into `N`
    have hsx : (s : B) • j x = j m := by
      have h1 := congrArg (fun z ↦ (s : B) • z) hs
      rw [← Submonoid.smul_def, IsLocalizedModule.mk'_cancel'] at h1
      exact h1.symm
    have hdiff : j ((s : B) • x - m) = j 0 := by
      rw [map_sub, map_smul, hsx, sub_self, map_zero]
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers (algebraMap R B ϖ)) (f := j) hdiff
    obtain ⟨k, hk⟩ := t.2
    obtain ⟨n, hn⟩ := s.2
    have hmem : ((t : B) * (s : B)) • x ∈ N := by
      have h2 : (t : B) • ((s : B) • x - m) = 0 := by
        rw [Submonoid.smul_def] at ht
        rwa [smul_zero] at ht
      rw [smul_sub, sub_eq_zero, smul_smul] at h2
      rw [h2]
      exact N.smul_mem _ hm
    have hts : (t : B) * (s : B) = algebraMap R B ϖ ^ (k + n) := by
      have hk' : algebraMap R B ϖ ^ k = (t : B) := hk
      have hn' : algebraMap R B ϖ ^ n = (s : B) := hn
      rw [pow_add, hk', hn']
    rw [hts] at hmem
    exact hsat (k + n) x hmem
  · intro x hx
    rw [mem_comapSubmodule]
    refine (Submodule.mem_localized' _ _ _ _ _).mpr ⟨x, hx, 1, ?_⟩
    rw [IsLocalizedModule.mk'_one]

/-- The kernel of an `R`-torsion-free quotient is saturated with respect to `ϖ`-powers. -/
theorem saturated_of_torsion_quotient_eq_bot [IsDomain R]
    [Module R F] [IsScalarTower R B F] (hϖ0 : ϖ ≠ 0) (N : Submodule B F)
    (htf : Submodule.torsion R (F ⧸ N) = ⊥)
    (m : ℕ) (x : F) (hx : algebraMap R B ϖ ^ m • x ∈ N) : x ∈ N := by
  have hres : (ϖ ^ m) • x ∈ N := by
    rw [← map_pow] at hx
    rwa [algebraMap_smul (A := B)] at hx
  have hzero : (ϖ ^ m) • (Submodule.Quotient.mk x : F ⧸ N) = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hres
  have htors : (Submodule.Quotient.mk x : F ⧸ N) ∈ Submodule.torsion R (F ⧸ N) :=
    ⟨⟨ϖ ^ m, mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m hϖ0)⟩, hzero⟩
  rw [htf] at htors
  rw [← Submodule.Quotient.mk_eq_zero]
  exact htors

end Uniqueness

end DVRQuotientExtension

end
