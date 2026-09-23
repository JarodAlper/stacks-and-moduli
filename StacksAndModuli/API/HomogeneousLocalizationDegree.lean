module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Graded pieces of a homogeneous localization

Mathlib's `HomogeneousLocalization 𝒜 x` is the *degree zero* part of the localization of a
graded ring `A` at a submonoid `x`. Twisting sheaves on `Proj 𝒜` need the other graded
pieces: the degree `d` part of that localization, for `d : ℤ`.

This file introduces those pieces. Rather than repeating the quotient construction of
`HomogeneousLocalization`, the degree `d` part is carved out of `Localization x` as the set
of fractions `a / b` with `a` homogeneous of degree `j`, `b` homogeneous of degree `i` and
`j - i = d`. Addition, negation and multiplication by degree zero fractions are then
inherited from `Localization x`, so the graded piece is a `HomogeneousLocalization 𝒜 x`
submodule of `Localization x`.

The one point requiring care is that the degree `d` part contains `0` only when `x` owns
homogeneous elements of degree at least `-d`: the fraction `0 / b` has numerator degree
`deg b + d`, which must be a natural number. The class `HasLargeDegrees` records that `x`
owns homogeneous elements of arbitrarily large degree, which is exactly what makes every
graded piece nonempty. It holds at every point of `ProjectiveSpectrum 𝒜`, because such a
point misses some homogeneous `f` of positive degree and therefore misses all of its
powers.

## Main definitions

* `HomogeneousLocalization.NumDenShift 𝒜 x d`: a numerator/denominator pair of homogeneous
  elements whose degrees differ by `d`, with the denominator in `x`.
* `HomogeneousLocalization.degSet 𝒜 x d`: the degree `d` part of `Localization x`, as a set.
* `HomogeneousLocalization.HasLargeDegrees 𝒜 x`: `x` owns homogeneous elements of
  arbitrarily large degree.
* `HomogeneousLocalization.degSubmodule 𝒜 x d`: the degree `d` part as a
  `HomogeneousLocalization 𝒜 x` submodule of `Localization x`.

## Main results

* `HomogeneousLocalization.hasLargeDegrees_primeCompl`: the instance at a point of
  `ProjectiveSpectrum 𝒜`.
* `HomogeneousLocalization.degSubmodule_zero`: the degree zero part is the image of
  `HomogeneousLocalization 𝒜 x` under `val`.
* `HomogeneousLocalization.mul_mem_degSet`: multiplying the degree `d` and degree `e` parts
  lands in the degree `d + e` part.
* `HomogeneousLocalization.degZeroEquiv`: the degree zero part is the homogeneous
  localization itself — the pointwise form of `𝒪(0) = 𝒪`.
* `HomogeneousLocalization.unitPow`, `unitPow_embed_mul`, `mulUnitPowEquiv`,
  `mulUnitPowLinearEquiv`: when `x` owns a degree-one element `f`, multiplication by `f^d`
  identifies the degree `e` part with the degree `e + d` part, linearly over the degree zero
  part. This is the local triviality of `𝒪(d)` on `D₊(f)`, read at a point.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace HomogeneousLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A numerator/denominator pair of homogeneous elements of `A` whose degrees differ by the
integer `d`, with the denominator lying in the submonoid `x`. Such a pair names an element
of the degree `d` part of `Localization x`. -/
structure NumDenShift (x : Submonoid A) (d : ℤ) where
  /-- The degree of the denominator. -/
  degDen : ℕ
  /-- The degree of the numerator. -/
  degNum : ℕ
  /-- The numerator, homogeneous of degree `degNum`. -/
  num : 𝒜 degNum
  /-- The denominator, homogeneous of degree `degDen`. -/
  den : 𝒜 degDen
  /-- The denominator lies in the submonoid being inverted. -/
  den_mem : (den : A) ∈ x
  /-- The numerator exceeds the denominator in degree by exactly `d`. -/
  deg_eq : (degNum : ℤ) = degDen + d

/-- The submonoid `x` owns homogeneous elements of arbitrarily large degree.

This is exactly the condition making every graded piece of `Localization x` nonempty, and
it holds at every point of `ProjectiveSpectrum 𝒜`
(`HomogeneousLocalization.hasLargeDegrees_primeCompl`). -/
class HasLargeDegrees (x : Submonoid A) : Prop where
  /-- Beyond every bound there is a degree in which `x` owns a homogeneous element. -/
  exists_homogeneous_mem (N : ℕ) : ∃ i, N ≤ i ∧ ∃ b : A, b ∈ 𝒜 i ∧ b ∈ x

variable {𝒜}
variable {x : Submonoid A} {d e : ℤ}

/-- The element of `Localization x` named by a shifted numerator/denominator pair. -/
def NumDenShift.embed (p : NumDenShift 𝒜 x d) : Localization x :=
  Localization.mk p.num ⟨p.den, p.den_mem⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
@[simp]
theorem NumDenShift.embed_def (p : NumDenShift 𝒜 x d) :
    p.embed = Localization.mk (p.num : A) ⟨(p.den : A), p.den_mem⟩ := rfl

variable (𝒜 x d) in
/-- The degree `d` part of the localization of the graded ring `A` at the submonoid `x`:
those elements of `Localization x` expressible as a fraction of homogeneous elements whose
degrees differ by `d`. -/
def degSet : Set (Localization x) :=
  Set.range (NumDenShift.embed (𝒜 := 𝒜) (x := x) (d := d))

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
theorem NumDenShift.embed_mem (p : NumDenShift 𝒜 x d) : p.embed ∈ degSet 𝒜 x d := ⟨p, rfl⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
theorem mem_degSet_iff (z : Localization x) :
    z ∈ degSet 𝒜 x d ↔ ∃ p : NumDenShift 𝒜 x d, p.embed = z := Iff.rfl

omit [GradedRing 𝒜] in
/-- Every graded piece contains `0`, provided `x` owns homogeneous elements of arbitrarily
large degree. -/
theorem zero_mem_degSet [HasLargeDegrees 𝒜 x] : (0 : Localization x) ∈ degSet 𝒜 x d := by
  obtain ⟨i, hi, b, hb, hbx⟩ :=
    HasLargeDegrees.exists_homogeneous_mem (𝒜 := 𝒜) (x := x) (-d).toNat
  have hid : (((i : ℤ) + d).toNat : ℤ) = (i : ℤ) + d := Int.toNat_of_nonneg (by omega)
  let p : NumDenShift 𝒜 x d :=
    { degDen := i
      degNum := ((i : ℤ) + d).toNat
      num := ⟨0, zero_mem _⟩
      den := ⟨b, hb⟩
      den_mem := hbx
      deg_eq := hid }
  refine ⟨p, ?_⟩
  change Localization.mk (0 : A) _ = 0
  exact Localization.mk_zero _

/-- The sum of two shifted numerator/denominator pairs of the same shift. -/
def NumDenShift.add (p q : NumDenShift 𝒜 x d) : NumDenShift 𝒜 x d where
  degDen := p.degDen + q.degDen
  degNum := p.degDen + q.degNum
  num := ⟨(p.den : A) * (q.num : A) + (q.den : A) * (p.num : A), by
    refine add_mem (SetLike.mul_mem_graded p.den.2 q.num.2) ?_
    have hnat : q.degDen + p.degNum = p.degDen + q.degNum := by
      have := p.deg_eq; have := q.deg_eq; omega
    exact hnat ▸ SetLike.mul_mem_graded q.den.2 p.num.2⟩
  den := ⟨(p.den : A) * (q.den : A), SetLike.mul_mem_graded p.den.2 q.den.2⟩
  den_mem := mul_mem p.den_mem q.den_mem
  deg_eq := by have := q.deg_eq; push_cast; omega

@[simp]
theorem NumDenShift.embed_add (p q : NumDenShift 𝒜 x d) :
    (p.add q).embed = p.embed + q.embed := by
  show Localization.mk _ _ = Localization.mk _ _ + Localization.mk _ _
  rw [Localization.add_mk]
  rfl

/-- Negation of a shifted numerator/denominator pair. -/
def NumDenShift.neg (p : NumDenShift 𝒜 x d) : NumDenShift 𝒜 x d :=
  { p with num := ⟨-(p.num : A), neg_mem p.num.2⟩ }

omit [GradedRing 𝒜] in
@[simp]
theorem NumDenShift.embed_neg (p : NumDenShift 𝒜 x d) : p.neg.embed = -p.embed := by
  show Localization.mk _ _ = -Localization.mk _ _
  rw [Localization.neg_mk]
  rfl

/-- Scaling a shifted numerator/denominator pair by a degree zero fraction. -/
def NumDenShift.smul (c : NumDenSameDeg 𝒜 x) (p : NumDenShift 𝒜 x d) : NumDenShift 𝒜 x d where
  degDen := c.deg + p.degDen
  degNum := c.deg + p.degNum
  num := ⟨(c.num : A) * (p.num : A), SetLike.mul_mem_graded c.num.2 p.num.2⟩
  den := ⟨(c.den : A) * (p.den : A), SetLike.mul_mem_graded c.den.2 p.den.2⟩
  den_mem := mul_mem c.den_mem p.den_mem
  deg_eq := by have := p.deg_eq; push_cast; omega

@[simp]
theorem NumDenShift.embed_smul (c : NumDenSameDeg 𝒜 x) (p : NumDenShift 𝒜 x d) :
    (NumDenShift.smul c p).embed = HomogeneousLocalization.mk c • p.embed := by
  show Localization.mk _ _ = (HomogeneousLocalization.mk c).val * Localization.mk _ _
  rw [HomogeneousLocalization.val_mk, Localization.mk_mul]
  rfl

/-- The product of a shifted pair of shift `d` with one of shift `e`, of shift `d + e`. -/
def NumDenShift.mul (p : NumDenShift 𝒜 x d) (q : NumDenShift 𝒜 x e) :
    NumDenShift 𝒜 x (d + e) where
  degDen := p.degDen + q.degDen
  degNum := p.degNum + q.degNum
  num := ⟨(p.num : A) * (q.num : A), SetLike.mul_mem_graded p.num.2 q.num.2⟩
  den := ⟨(p.den : A) * (q.den : A), SetLike.mul_mem_graded p.den.2 q.den.2⟩
  den_mem := mul_mem p.den_mem q.den_mem
  deg_eq := by have := p.deg_eq; have := q.deg_eq; push_cast; omega

@[simp]
theorem NumDenShift.embed_mul (p : NumDenShift 𝒜 x d) (q : NumDenShift 𝒜 x e) :
    (p.mul q).embed = p.embed * q.embed := by
  show Localization.mk _ _ = Localization.mk _ _ * Localization.mk _ _
  rw [Localization.mk_mul]
  rfl

variable (𝒜 x d) in
/-- The degree `d` part of `Localization x`, as a submodule over the degree zero part
`HomogeneousLocalization 𝒜 x`. -/
def degSubmodule [HasLargeDegrees 𝒜 x] :
    Submodule (HomogeneousLocalization 𝒜 x) (Localization x) where
  carrier := degSet 𝒜 x d
  add_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p.add q, p.embed_add q⟩
  zero_mem' := zero_mem_degSet
  smul_mem' := by
    rintro c _ ⟨p, rfl⟩
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective c
    exact ⟨NumDenShift.smul c p, NumDenShift.embed_smul c p⟩

@[simp]
theorem coe_degSubmodule [HasLargeDegrees 𝒜 x] :
    (degSubmodule 𝒜 x d : Set (Localization x)) = degSet 𝒜 x d := rfl

@[simp]
theorem mem_degSubmodule [HasLargeDegrees 𝒜 x] (z : Localization x) :
    z ∈ degSubmodule 𝒜 x d ↔ z ∈ degSet 𝒜 x d := Iff.rfl

omit [GradedRing 𝒜] in
theorem neg_mem_degSet (z : Localization x) (hz : z ∈ degSet 𝒜 x d) : -z ∈ degSet 𝒜 x d := by
  obtain ⟨p, rfl⟩ := hz
  exact ⟨p.neg, p.embed_neg⟩

/-- Multiplying a degree `d` element by a degree `e` element gives a degree `d + e`
element. -/
theorem mul_mem_degSet {z w : Localization x} (hz : z ∈ degSet 𝒜 x d)
    (hw : w ∈ degSet 𝒜 x e) : z * w ∈ degSet 𝒜 x (d + e) := by
  obtain ⟨p, rfl⟩ := hz
  obtain ⟨q, rfl⟩ := hw
  exact ⟨p.mul q, p.embed_mul q⟩

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The degree zero part is exactly the image of `HomogeneousLocalization 𝒜 x` in the
localization. -/
theorem degSet_zero : degSet 𝒜 x 0 = Set.range (HomogeneousLocalization.val (𝒜 := 𝒜)) := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    have hdeg : p.degNum = p.degDen := by have := p.deg_eq; omega
    refine ⟨HomogeneousLocalization.mk
      ⟨p.degDen, ⟨(p.num : A), hdeg ▸ p.num.2⟩, ⟨(p.den : A), p.den.2⟩, p.den_mem⟩, ?_⟩
    rw [HomogeneousLocalization.val_mk]
    rfl
  · rintro ⟨c, rfl⟩
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective c
    let p : NumDenShift 𝒜 x 0 :=
      { degDen := c.deg
        degNum := c.deg
        num := c.num
        den := c.den
        den_mem := c.den_mem
        deg_eq := by omega }
    refine ⟨p, ?_⟩
    rw [HomogeneousLocalization.val_mk]
    rfl

/-! ### The degree zero part

`degSet 𝒜 x 0` is the image of `HomogeneousLocalization 𝒜 x` under `val`
(`degSet_zero`), and `val` is injective, so the two are isomorphic as modules. On `Proj`
this is the statement `𝒪(0) = 𝒪` read at a point — the unit of the family of twisting
sheaves. -/
/-- `val` as a linear map into the degree zero part. -/
noncomputable def toDegZero [HasLargeDegrees 𝒜 x] :
    HomogeneousLocalization 𝒜 x →ₗ[HomogeneousLocalization 𝒜 x] degSubmodule 𝒜 x 0 where
  toFun c := ⟨c.val, by
    rw [mem_degSubmodule, degSet_zero]; exact ⟨c, rfl⟩⟩
  map_add' c c' := Subtype.ext (by simp [HomogeneousLocalization.val_add])
  map_smul' d c := Subtype.ext (by
    show (d * c).val = d.val * c.val
    simp [HomogeneousLocalization.val_mul])

/-- The degree zero part of the localization is the homogeneous localization itself. -/
noncomputable def degZeroEquiv [HasLargeDegrees 𝒜 x] :
    HomogeneousLocalization 𝒜 x ≃ₗ[HomogeneousLocalization 𝒜 x] degSubmodule 𝒜 x 0 :=
  LinearEquiv.ofBijective toDegZero
    ⟨fun c c' h ↦ HomogeneousLocalization.val_injective _ (congrArg Subtype.val h),
      fun z ↦ by
        have hz : (z : Localization x) ∈ Set.range (HomogeneousLocalization.val (𝒜 := 𝒜)) := by
          rw [← degSet_zero]; exact z.2
        obtain ⟨c, hc⟩ := hz
        exact ⟨c, Subtype.ext hc⟩⟩

/-! ### Degree-one units and the shift isomorphism

When the graded ring owns a degree-one element `f` inside `x` — which on `Proj` means a
degree-one `f` not vanishing at the point, i.e. the point lies in `D₊(f)` — the graded
pieces are all isomorphic to one another, shifted by multiplication by powers of `f`. This
is the algebraic heart of the invertibility of `𝒪(d)` on `ℙ^n`, and hence of the exactness
and additivity of twisting there. -/

/-- For `f` homogeneous of degree one lying in `x`, the fraction `f^d` — read as `1 / f^{-d}`
when `d < 0` — as a numerator/denominator pair of degree `d`.

The single formula `f^{d⁺} / f^{d⁻}` covers both signs, since `d⁺ - d⁻ = d`. -/
def unitPow {f : A} (hf : f ∈ 𝒜 1) (hfx : f ∈ x) (d : ℤ) : NumDenShift 𝒜 x d where
  degDen := (-d).toNat
  degNum := d.toNat
  num := ⟨f ^ d.toNat, by simpa [smul_eq_mul] using SetLike.pow_mem_graded d.toNat hf⟩
  den := ⟨f ^ (-d).toNat, by simpa [smul_eq_mul] using SetLike.pow_mem_graded (-d).toNat hf⟩
  den_mem := pow_mem hfx _
  deg_eq := by omega

/-- The degree-one units multiply as expected: `f^d · f^e = f^{d+e}`. -/
theorem unitPow_embed_mul {f : A} (hf : f ∈ 𝒜 1) (hfx : f ∈ x) (d e : ℤ) :
    (unitPow hf hfx d).embed * (unitPow hf hfx e).embed
      = (unitPow hf hfx (d + e)).embed := by
  show Localization.mk _ _ * Localization.mk _ _ = Localization.mk _ _
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  have hexp : (-(d + e)).toNat + (d.toNat + e.toNat)
      = (-d).toNat + (-e).toNat + (d + e).toNat := by omega
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, unitPow]
  rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
  congr 1

/-- `f^0 = 1`. -/
theorem unitPow_embed_zero {f : A} (hf : f ∈ 𝒜 1) (hfx : f ∈ x) :
    (unitPow hf hfx 0).embed = 1 := by
  show Localization.mk _ _ = 1
  simp [unitPow]

/-- Multiplying by the degree `d` unit `f^d` is a bijection from the degree `e` part onto
the degree `e + d` part: this is the local triviality of `𝒪(d)` on `D₊(f)`, read at a
point. -/
def mulUnitPowEquiv {f : A} (hf : f ∈ 𝒜 1) (hfx : f ∈ x) (d e : ℤ) :
    degSet 𝒜 x e ≃ degSet 𝒜 x (e + d) where
  toFun z := ⟨z.1 * (unitPow hf hfx d).embed,
    mul_mem_degSet z.2 (unitPow hf hfx d).embed_mem⟩
  invFun w := ⟨w.1 * (unitPow hf hfx (-d)).embed, by
    have := mul_mem_degSet w.2 (unitPow hf hfx (-d)).embed_mem
    simpa using this⟩
  left_inv z := by
    ext
    show z.1 * _ * _ = z.1
    rw [mul_assoc, unitPow_embed_mul, add_neg_cancel, unitPow_embed_zero, mul_one]
  right_inv w := by
    ext
    show w.1 * _ * _ = w.1
    rw [mul_assoc, unitPow_embed_mul, neg_add_cancel, unitPow_embed_zero, mul_one]

/-- The shift bijection is linear over the degree zero part, so the graded pieces of a
homogeneous localization owning a degree-one unit are isomorphic as modules. -/
def mulUnitPowLinearEquiv [HasLargeDegrees 𝒜 x] {f : A} (hf : f ∈ 𝒜 1) (hfx : f ∈ x)
    (d e : ℤ) :
    degSubmodule 𝒜 x e ≃ₗ[HomogeneousLocalization 𝒜 x] degSubmodule 𝒜 x (e + d) where
  toFun := (mulUnitPowEquiv hf hfx d e).toFun
  invFun := (mulUnitPowEquiv hf hfx d e).invFun
  left_inv := (mulUnitPowEquiv hf hfx d e).left_inv
  right_inv := (mulUnitPowEquiv hf hfx d e).right_inv
  map_add' _ _ := Subtype.ext (add_mul _ _ _)
  map_smul' _ _ := Subtype.ext (mul_assoc _ _ _)

section ProjectiveSpectrum

variable (𝒜)

/-- At a point of `ProjectiveSpectrum 𝒜` the homogeneous elements outside the corresponding
prime have arbitrarily large degrees: the point misses some homogeneous `f` of positive
degree, hence misses every power of `f`. -/
instance hasLargeDegrees_primeCompl (y : ProjectiveSpectrum 𝒜) :
    HasLargeDegrees 𝒜 (y.asHomogeneousIdeal.toIdeal.primeCompl) where
  exists_homogeneous_mem N := by
    by_contra hcon
    push Not at hcon
    apply y.not_irrelevant_le
    rw [HomogeneousIdeal.irrelevant_le]
    intro i hi b hb
    have hbi : b ∈ 𝒜 i := hb
    have hpow : b ^ (N + 1) ∈ 𝒜 ((N + 1) * i) := by
      simpa [smul_eq_mul] using SetLike.pow_mem_graded (N + 1) hbi
    have hge : N ≤ (N + 1) * i := by
      calc N ≤ N + 1 := Nat.le_succ N
        _ = (N + 1) * 1 := by ring
        _ ≤ (N + 1) * i := Nat.mul_le_mul_left _ hi
    have hmem := hcon ((N + 1) * i) hge (b ^ (N + 1)) hpow
    simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, not_not] at hmem
    exact y.isPrime.mem_of_pow_mem (N + 1) hmem

end ProjectiveSpectrum

end HomogeneousLocalization
