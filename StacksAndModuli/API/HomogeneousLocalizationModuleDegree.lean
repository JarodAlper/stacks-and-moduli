module

public import StacksAndModuli.API.HomogeneousLocalizationDegree
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Graded pieces of the localization of a graded module

Step **9a** of `PLAN-hilbert-quot.md`: Mathlib has `HomogeneousLocalization 𝒜 x` for a graded
*ring* only, so `M ↦ M~` on `Proj` (Stacks 01M6) needs the module analogue first.

For a graded module `ℳ` over a graded ring `𝒜` and a submonoid `x ⊆ A`, the degree-`d`
part of `LocalizedModule x M` is carved out as the set of fractions `m / b` with `m` homogeneous of
degree `j`, `b` homogeneous of degree `i`, `b ∈ x`, and `j - i = d`.  Addition, negation and
multiplication by degree-zero fractions are inherited from `LocalizedModule x M`, so the graded
piece is a `HomogeneousLocalization 𝒜 x`-submodule of `LocalizedModule x M`.

This mirrors `StacksAndModuli/API/HomogeneousLocalizationDegree.lean` exactly, with a module
numerator; that file is the case `ℳ = 𝒜`.

## Main definitions

* `HomogeneousLocalization.ModuleNumDenShift 𝒜 ℳ x d`: a numerator/denominator pair with a
  homogeneous module numerator and a homogeneous ring denominator whose degrees differ by `d`.
* `HomogeneousLocalization.moduleDegSet 𝒜 ℳ x d`: the degree-`d` part, as a set.
* `HomogeneousLocalization.moduleDegSubmodule 𝒜 ℳ x d`: the same as a
  `HomogeneousLocalization 𝒜 x`-submodule of `LocalizedModule x M`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace HomogeneousLocalization

variable {A σ M τ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [AddCommGroup M] [Module A M] [SetLike τ M] [AddSubgroupClass τ M]
variable (𝒜 : ℕ → σ) (ℳ : ℕ → τ) [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 ℳ]

/-- A numerator/denominator pair with homogeneous module numerator and homogeneous ring
denominator, whose degrees differ by the integer `d`, the denominator lying in `x`. -/
structure ModuleNumDenShift (x : Submonoid A) (d : ℤ) where
  /-- The degree of the denominator. -/
  degDen : ℕ
  /-- The degree of the numerator. -/
  degNum : ℕ
  /-- The numerator, a homogeneous element of the module. -/
  num : ℳ degNum
  /-- The denominator, homogeneous of degree `degDen`. -/
  den : 𝒜 degDen
  /-- The denominator lies in the submonoid being inverted. -/
  den_mem : (den : A) ∈ x
  /-- The numerator exceeds the denominator in degree by exactly `d`. -/
  deg_eq : (degNum : ℤ) = degDen + d

variable {𝒜 ℳ}
variable {x : Submonoid A} {d : ℤ}

/-- `LocalizedModule x M` is a module over the degree-zero part of the localized ring, by
restriction of scalars along `HomogeneousLocalization.val`. -/
noncomputable instance moduleHomogeneousLocalization :
    Module (HomogeneousLocalization 𝒜 x) (LocalizedModule x M) :=
  Module.compHom _ (algebraMap (HomogeneousLocalization 𝒜 x) (Localization x))

/-- The element of `LocalizedModule x M` named by such a pair. -/
def ModuleNumDenShift.embed (p : ModuleNumDenShift 𝒜 ℳ x d) : LocalizedModule x M :=
  LocalizedModule.mk p.num ⟨p.den, p.den_mem⟩

omit [AddSubgroupClass σ A] [AddSubgroupClass τ M] [GradedRing 𝒜]
  [SetLike.GradedSMul 𝒜 ℳ] in
@[simp]
theorem ModuleNumDenShift.embed_def (p : ModuleNumDenShift 𝒜 ℳ x d) :
    p.embed = LocalizedModule.mk (p.num : M) ⟨(p.den : A), p.den_mem⟩ := rfl

variable (𝒜 ℳ x d) in
/-- The degree-`d` part of `LocalizedModule x M`. -/
def moduleDegSet : Set (LocalizedModule x M) :=
  Set.range (ModuleNumDenShift.embed (𝒜 := 𝒜) (ℳ := ℳ) (x := x) (d := d))

omit [AddSubgroupClass σ A] [AddSubgroupClass τ M] [GradedRing 𝒜]
  [SetLike.GradedSMul 𝒜 ℳ] in
theorem ModuleNumDenShift.embed_mem (p : ModuleNumDenShift 𝒜 ℳ x d) :
    p.embed ∈ moduleDegSet 𝒜 ℳ x d := ⟨p, rfl⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 ℳ] in
/-- Every graded piece contains `0`, provided `x` owns homogeneous elements of arbitrarily
large degree. -/
theorem zero_mem_moduleDegSet [HasLargeDegrees 𝒜 x] :
    (0 : LocalizedModule x M) ∈ moduleDegSet 𝒜 ℳ x d := by
  obtain ⟨i, hi, b, hb, hbx⟩ :=
    HasLargeDegrees.exists_homogeneous_mem (𝒜 := 𝒜) (x := x) (-d).toNat
  have hid : (((i : ℤ) + d).toNat : ℤ) = (i : ℤ) + d := Int.toNat_of_nonneg (by omega)
  refine ⟨{ degDen := i
            degNum := ((i : ℤ) + d).toNat
            num := ⟨0, zero_mem _⟩
            den := ⟨b, hb⟩
            den_mem := hbx
            deg_eq := hid }, ?_⟩
  change LocalizedModule.mk (0 : M) _ = 0
  exact LocalizedModule.zero_mk _

/-- The sum of two pairs of the same shift. -/
def ModuleNumDenShift.add (p q : ModuleNumDenShift 𝒜 ℳ x d) :
    ModuleNumDenShift 𝒜 ℳ x d where
  degDen := p.degDen + q.degDen
  degNum := q.degDen + p.degNum
  num := ⟨(q.den : A) • (p.num : M) + (p.den : A) • (q.num : M), by
    refine add_mem (SetLike.GradedSMul.smul_mem q.den.2 p.num.2) ?_
    have hnat : p.degDen + q.degNum = q.degDen + p.degNum := by
      have := p.deg_eq; have := q.deg_eq; omega
    exact hnat ▸ SetLike.GradedSMul.smul_mem p.den.2 q.num.2⟩
  den := ⟨(p.den : A) * (q.den : A), SetLike.mul_mem_graded p.den.2 q.den.2⟩
  den_mem := mul_mem p.den_mem q.den_mem
  deg_eq := by have := p.deg_eq; have := q.deg_eq; push_cast; omega

@[simp]
theorem ModuleNumDenShift.embed_add (p q : ModuleNumDenShift 𝒜 ℳ x d) :
    (p.add q).embed = p.embed + q.embed := by
  show LocalizedModule.mk _ _ = LocalizedModule.mk _ _ + LocalizedModule.mk _ _
  rw [LocalizedModule.mk_add_mk]
  rfl

/-- Negation of a pair. -/
def ModuleNumDenShift.neg (p : ModuleNumDenShift 𝒜 ℳ x d) : ModuleNumDenShift 𝒜 ℳ x d :=
  { p with num := ⟨-(p.num : M), neg_mem p.num.2⟩ }

omit [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 ℳ] in
@[simp]
theorem ModuleNumDenShift.embed_neg (p : ModuleNumDenShift 𝒜 ℳ x d) :
    p.neg.embed = -p.embed := by
  show LocalizedModule.mk _ _ = -LocalizedModule.mk _ _
  rw [← LocalizedModule.mk_neg]
  rfl

/-- Scaling a pair by a degree-zero fraction. -/
def ModuleNumDenShift.smul (c : NumDenSameDeg 𝒜 x) (p : ModuleNumDenShift 𝒜 ℳ x d) :
    ModuleNumDenShift 𝒜 ℳ x d where
  degDen := c.deg + p.degDen
  degNum := c.deg + p.degNum
  num := ⟨(c.num : A) • (p.num : M), SetLike.GradedSMul.smul_mem c.num.2 p.num.2⟩
  den := ⟨(c.den : A) * (p.den : A), SetLike.mul_mem_graded c.den.2 p.den.2⟩
  den_mem := mul_mem c.den_mem p.den_mem
  deg_eq := by have := p.deg_eq; push_cast; omega

@[simp]
theorem ModuleNumDenShift.embed_smul (c : NumDenSameDeg 𝒜 x)
    (p : ModuleNumDenShift 𝒜 ℳ x d) :
    (ModuleNumDenShift.smul c p).embed
      = (HomogeneousLocalization.mk c : HomogeneousLocalization 𝒜 x) • p.embed := by
  have hsm : (HomogeneousLocalization.mk c : HomogeneousLocalization 𝒜 x) • p.embed
      = ((HomogeneousLocalization.mk c : HomogeneousLocalization 𝒜 x).val
          : Localization x) • p.embed := rfl
  rw [hsm, HomogeneousLocalization.val_mk, embed_def, embed_def, LocalizedModule.mk_smul_mk]
  rfl

variable (𝒜 ℳ x d) in
/-- **The degree-`d` part of `LocalizedModule x M`**, as a module over the degree-zero part
`HomogeneousLocalization 𝒜 x` of the localized ring. -/
def moduleDegSubmodule [HasLargeDegrees 𝒜 x] :
    Submodule (HomogeneousLocalization 𝒜 x) (LocalizedModule x M) where
  carrier := moduleDegSet 𝒜 ℳ x d
  add_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p.add q, p.embed_add q⟩
  zero_mem' := zero_mem_moduleDegSet
  smul_mem' := by
    rintro c _ ⟨p, rfl⟩
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective c
    exact ⟨ModuleNumDenShift.smul c p, ModuleNumDenShift.embed_smul c p⟩

@[simp]
theorem coe_moduleDegSubmodule [HasLargeDegrees 𝒜 x] :
    (moduleDegSubmodule 𝒜 ℳ x d : Set (LocalizedModule x M)) = moduleDegSet 𝒜 ℳ x d := rfl

@[simp]
theorem mem_moduleDegSubmodule [HasLargeDegrees 𝒜 x] (z : LocalizedModule x M) :
    z ∈ moduleDegSubmodule 𝒜 ℳ x d ↔ z ∈ moduleDegSet 𝒜 ℳ x d := Iff.rfl

end HomogeneousLocalization
