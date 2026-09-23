module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksAndModuli.API.HomogeneousLocalizationDegree
public import StacksAndModuli.API.SchemeModulesTensor

/-!
# Twisting sheaves on `Proj`

Stacks Project tag **01MN**, label `constructions-definition-twist`, in `constructions.tex`,
§`01MM` (Invertible sheaves on Proj).

> Let `S` be a graded ring. Let `X = Proj(S)`.
> 1. We define `𝒪_X(n) = S(n)~`. This is called the *`n`th twist of the structure sheaf of
>    `Proj(S)`*.
> 2. For any sheaf of `𝒪_X`-modules `ℱ` we set `ℱ(n) = ℱ ⊗_{𝒪_X} 𝒪_X(n)`.

Mathlib has `AlgebraicGeometry.Proj` and its structure sheaf but no twisting sheaves of any
kind, and no `M~` for a graded module `M`. This file supplies part (1) directly, without
first building `M~` in general.

The construction mirrors Mathlib's `ProjectiveSpectrum.Proj.structureSheaf` exactly. The
structure sheaf is the subsheaf of `∏_{x ∈ U} (S_{(x)})` cut out by the local predicate "is
locally a fraction of homogeneous elements of *equal* degree". Replacing "equal degree" by
"degrees differing by `d`" gives `𝒪(d)`: its value at a point is the degree `d` part of the
homogeneous localization there (`HomogeneousLocalization.degSubmodule`, from
`StacksAndModuli/API/HomogeneousLocalizationDegree.lean`), and its sections are those dependent
functions locally of the form `r / s` with `deg r - deg s = d`.

Taking `d = 0` recovers the structure sheaf, so this is a genuine generalization of the
Mathlib construction rather than a parallel one.

Note, per the Stacks Project's own warning (tag 01MS and the example in `01MR`), that
`𝒪(d)` is **not** invertible for a general graded ring; it is when `S` is generated in
degree one over `S₀`, which is the case of relative projective space. Nothing here assumes
invertibility.

## Main definitions

* `ProjectiveSpectrum.Twist.atDeg 𝒜 d x`: the value of `𝒪(d)` at a point, the degree `d`
  part of the homogeneous localization.
* `ProjectiveSpectrum.Twist.isLocallyFraction 𝒜 d`: the local predicate cutting out the
  sections.
* `ProjectiveSpectrum.Twist.sheafInType 𝒜 d`: `𝒪(d)` as a sheaf of types.
* `ProjectiveSpectrum.Twist.twist 𝒜 d`: `𝒪(d)` as a sheaf of `𝒪_{Proj 𝒜}`-modules, i.e. an
  object of `(Proj 𝒜).Modules`.
* `ProjectiveSpectrum.Twist.twistModule F d`: part (2) of the tag, the twist
  `ℱ(d) = ℱ ⊗_{𝒪_X} 𝒪_X(d)` of an arbitrary sheaf of modules.
* `ProjectiveSpectrum.Twist.mulUnitPowSection` with `…_injective` and `…_surjective`: the
  local triviality of `𝒪(d)` on `D₊(f)` for `f` of degree one.
* `ProjectiveSpectrum.Twist.sectionsZeroEquiv` (with `…_add`, `…_smul`),
  `isLocallyFraction_zero_iff`, and `zeroIso`: `𝒪(0) = 𝒪` on sections and as a
  sheaf of modules.
* `ProjectiveSpectrum.Twist.unitSection` and `unitSectionEquiv` (with
  `unitSectionEquiv_one`): `Γ(𝒪(d), U)` is free of rank one over `Γ(𝒪, U)` with basis
  `f^d`, for `U ≤ D₊(f)` and `f` of degree one; and `mulSections_unitSection`,
  `f^a · f^b = f^{a+b}`.
* `ProjectiveSpectrum.Twist.mulSectionsBilinear` and `mulSections_naturality`: the bilinear,
  restriction-compatible multiplication of sections; and
  `ProjectiveSpectrum.Twist.multiplyHom`, the canonical map `𝒪(a) ⊗ 𝒪(b) → 𝒪(a+b)` it
  yields (Stacks `constructions-equation-multiply`), not an isomorphism in general.
* `ProjectiveSpectrum.Twist.bijective_tensorLift_mulSections`: over an open inside `D₊(f)`
  with `f` of degree one, that map *is* bijective — both sides are free of rank one and it
  carries `f^a ⊗ f^b` to `f^{a+b}`. This is the computation behind the invertibility of
  `𝒪(d)` on `ℙ^n`.

## Main results

* `ProjectiveSpectrum.Twist.zero_mem'`, `add_mem'`, `neg_mem'`, `smul_mem'`: the local
  predicate is closed under the module operations, which is what makes `𝒪(d)` a sheaf of
  modules. Note `zero_mem'` is the one place where the graded ring is genuinely used: the
  zero section is written `0 / s` and needs a homogeneous `s` of degree at least `-d` not
  vanishing at the point, which exists exactly because points of `Proj` do not contain the
  irrelevant ideal.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open HomogeneousLocalization

namespace ProjectiveSpectrum.Twist

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℤ)

local notation3 "at " x =>
  HomogeneousLocalization.AtPrime 𝒜
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x))

/-- **Stacks 01MN** (`constructions-definition-twist`) (the value of `𝒪(d)` at a point):
the degree `d` part of the homogeneous localization of `𝒜` at `x`. For `d = 0` this is
Mathlib's `HomogeneousLocalization.AtPrime`, the value of the structure sheaf. -/
abbrev atDeg (x : ProjectiveSpectrum.top 𝒜) : Type _ :=
  degSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl d

variable {𝒜 d}

/-- **Stacks 01MN** (`constructions-definition-twist`) (the defining local condition): a
dependent function on an open set is a *fraction of degree `d`* when it is given by a single
homogeneous fraction `r / s` whose numerator and denominator degrees differ by `d`. This is
Mathlib's `ProjectiveSpectrum.StructureSheaf.IsFraction` with "same degree" relaxed to
"degrees differing by `d`". -/
def IsFraction {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, atDeg 𝒜 d x.1) : Prop :=
  ∃ (i j : ℕ) (_ : (j : ℤ) = i + d) (r : 𝒜 j) (s : 𝒜 i)
    (s_nin : ∀ x : U, (s : A) ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl),
    ∀ x : U, (f x : Localization _) = Localization.mk (r : A) ⟨(s : A), s_nin x⟩

variable (𝒜 d)

/-- Being a fraction of degree `d` is a prelocal predicate: it passes to open subsets. -/
def isFractionPrelocal : PrelocalPredicate (atDeg 𝒜 d) where
  pred f := IsFraction f
  res := by
    rintro V U i f ⟨a, b, hab, r, s, h, w⟩
    exact ⟨a, b, hab, r, s, (h <| i ·), (w <| i ·)⟩

/-- **Stacks 01MN** (`constructions-definition-twist`) (the sheaf condition): the sections of
`𝒪(d)` are the dependent functions that are *locally* a homogeneous fraction of degree `d`.
-/
def isLocallyFraction : LocalPredicate (atDeg 𝒜 d) :=
  (isFractionPrelocal 𝒜 d).sheafify

/-- At any point of `Proj 𝒜` there are homogeneous elements of arbitrarily large degree
outside the corresponding prime, since the point does not contain the irrelevant ideal. -/
theorem exists_homogeneous_nmem (x : ProjectiveSpectrum.top 𝒜) (N : ℕ) :
    ∃ (i : ℕ) (s : A), N ≤ i ∧ s ∈ 𝒜 i ∧ s ∉ x.asHomogeneousIdeal := by
  obtain ⟨i, hi, s, hs, hsx⟩ :=
    HasLargeDegrees.exists_homogeneous_mem (𝒜 := 𝒜)
      (x := x.asHomogeneousIdeal.toIdeal.primeCompl) N
  exact ⟨i, s, hi, hs, hsx⟩

/-- The zero function is a section of `𝒪(d)`.

Unlike for the structure sheaf, this is not immediate: writing `0` as the fraction `0 / s`
forces `deg s ≥ -d`, so a denominator of large enough degree must be found near each point.
`exists_homogeneous_nmem` supplies one, and the corresponding basic open set is the
neighbourhood on which the fraction is valid. -/
theorem zero_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜 d).pred (0 : ∀ x : U.unop, atDeg 𝒜 d x.1) := by
  intro x
  obtain ⟨i, s, hiN, hs, hsx⟩ := exists_homogeneous_nmem 𝒜 x.1 (-d).toNat
  have hnn : (0 : ℤ) ≤ (i : ℤ) + d := by omega
  refine ⟨U.unop ⊓ ProjectiveSpectrum.basicOpen 𝒜 s, ⟨x.2, hsx⟩,
    homOfLE inf_le_left, i, ((i : ℤ) + d).toNat, Int.toNat_of_nonneg hnn,
    ⟨0, zero_mem _⟩, ⟨s, hs⟩, fun y ↦ y.2.2, fun _ ↦ ?_⟩
  exact (Localization.mk_zero _).symm

/-- Sections of `𝒪(d)` are closed under addition: `r₁/s₁ + r₂/s₂ = (s₂r₁ + s₁r₂)/(s₁s₂)`
again has numerator and denominator degrees differing by `d`. -/
theorem add_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a b : ∀ x : U.unop, atDeg 𝒜 d x.1)
    (ha : (isLocallyFraction 𝒜 d).pred a) (hb : (isLocallyFraction 𝒜 d).pred b) :
    (isLocallyFraction 𝒜 d).pred (a + b) := by
  intro x
  obtain ⟨Va, ma, ia, dda, dna, hda, ⟨ra, hra⟩, ⟨sa, hsa⟩, sa_nin, wa⟩ := ha x
  obtain ⟨Vb, mb, ib, ddb, dnb, hdb, ⟨rb, hrb⟩, ⟨sb, hsb⟩, sb_nin, wb⟩ := hb x
  have hnat : dda + dnb = ddb + dna := by omega
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, dda + ddb, ddb + dna, by push_cast; omega,
    ⟨sb * ra + sa * rb, add_mem (SetLike.mul_mem_graded hsb hra)
      (hnat ▸ SetLike.mul_mem_graded hsa hrb)⟩,
    ⟨sa * sb, SetLike.mul_mem_graded hsa hsb⟩,
    fun y ↦ mul_mem (sa_nin ⟨y.1, y.2.1⟩) (sb_nin ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp [wa y hy.1, wb y hy.2, Localization.add_mk, add_comm (sa * rb)]

/-- Sections of `𝒪(d)` are closed under negation. -/
theorem neg_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : ∀ x : U.unop, atDeg 𝒜 d x.1) (ha : (isLocallyFraction 𝒜 d).pred a) :
    (isLocallyFraction 𝒜 d).pred (-a) := by
  intro x
  obtain ⟨Va, ma, ia, dda, dna, hda, ⟨ra, hra⟩, ⟨sa, hsa⟩, sa_nin, wa⟩ := ha x
  refine ⟨Va, ma, ia, dda, dna, hda, ⟨-ra, neg_mem hra⟩, ⟨sa, hsa⟩, sa_nin, fun y ↦ ?_⟩
  simp only [Pi.neg_apply, Submodule.coe_neg, wa y, Localization.neg_mk]

/-- Sections of `𝒪(d)` are closed under multiplication by sections of the structure sheaf:
multiplying `r/s` of degree `d` by `c/e` of degree `0` gives `cr/es`, again of degree `d`.
This is what makes `𝒪(d)` a sheaf of `𝒪`-modules. -/
theorem smul_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (g : ∀ x : U.unop, at x.1) (a : ∀ x : U.unop, atDeg 𝒜 d x.1)
    (hg : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred g)
    (ha : (isLocallyFraction 𝒜 d).pred a) :
    (isLocallyFraction 𝒜 d).pred (fun x ↦ g x • a x) := by
  intro x
  obtain ⟨Vg, mg, ig, k, ⟨c, hc⟩, ⟨e, he⟩, e_nin, wg⟩ := hg x
  obtain ⟨Va, ma, ia, dda, dna, hda, ⟨r, hr⟩, ⟨s, hs⟩, s_nin, wa⟩ := ha x
  refine ⟨Vg ⊓ Va, ⟨mg, ma⟩, Opens.infLELeft _ _ ≫ ig, k + dda, k + dna, by push_cast; omega,
    ⟨c * r, SetLike.mul_mem_graded hc hr⟩, ⟨e * s, SetLike.mul_mem_graded he hs⟩,
    fun y ↦ mul_mem (e_nin ⟨y.1, y.2.1⟩) (s_nin ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wg wa
  have hg' := wg y hy.1
  have ha' := wa y hy.2
  have hsm : ∀ (z : ProjectiveSpectrum.top 𝒜) (u : at z) (w : Localization
      (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal z)).primeCompl),
      u • w = u.val * w := fun _ _ _ ↦ rfl
  simp only [Submodule.coe_smul, hsm]
  simp [hg', ha', HomogeneousLocalization.val_mk, Localization.mk_mul]

/-- **Stacks 01MN** (`constructions-definition-twist`) (as a sheaf of types): `𝒪(d)` before
the module structure is installed, obtained from the local predicate by Mathlib's
`TopCat.subsheafToTypes`, which supplies the sheaf condition. -/
def sheafInType : TopCat.Sheaf (Type _) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜 d)

/-- The sections of `𝒪(d)` over an open set, as an additive subgroup of all dependent
functions into the graded pieces. -/
def sectionsAddSubgroup (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddSubgroup (∀ x : U.unop, atDeg 𝒜 d x.1) where
  carrier := {f | (isLocallyFraction 𝒜 d).pred f}
  zero_mem' := zero_mem' 𝒜 d U
  add_mem' ha hb := add_mem' 𝒜 d U _ _ ha hb
  neg_mem' ha := neg_mem' 𝒜 d U _ ha

instance addCommGroupSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddCommGroup ((sheafInType 𝒜 d).1.obj U) :=
  inferInstanceAs (AddCommGroup (sectionsAddSubgroup 𝒜 d U))

instance smulSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    SMul ((Proj 𝒜).presheaf.obj U) ((sheafInType 𝒜 d).1.obj U) where
  smul g a := ⟨fun x ↦ g.1 x • a.1 x, smul_mem' 𝒜 d U g.1 a.1 g.2 a.2⟩

@[simp]
theorem smul_apply (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (g : (Proj 𝒜).presheaf.obj U) (a : (sheafInType 𝒜 d).1.obj U) (x : U.unop) :
    (g • a).1 x = g.1 x • a.1 x := rfl

instance moduleSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((Proj 𝒜).presheaf.obj U) ((sheafInType 𝒜 d).1.obj U) where
  one_smul _ := Subtype.ext (funext fun _ ↦ one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (funext fun _ ↦ mul_smul _ _ _)
  smul_zero _ := Subtype.ext (funext fun _ ↦ smul_zero _)
  smul_add _ _ _ := Subtype.ext (funext fun _ ↦ smul_add _ _ _)
  add_smul _ _ _ := Subtype.ext (funext fun _ ↦ add_smul _ _ _)
  zero_smul _ := Subtype.ext (funext fun _ ↦ zero_smul _ _)

/-- `𝒪(d)` as a presheaf of abelian groups, dressing up the `Type`-valued sheaf. -/
def presheafInAddCommGrp : Presheaf AddCommGrpCat (ProjectiveSpectrum.top 𝒜) where
  obj U := AddCommGrpCat.of ((sheafInType 𝒜 d).1.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (sheafInType 𝒜 d).1.map i
      map_add' _ _ := rfl
      map_zero' := rfl }

/-- `𝒪(d)` as a presheaf of `𝒪_{Proj 𝒜}`-modules. -/
noncomputable def presheafOfModules : (Proj 𝒜).PresheafOfModules :=
  letI (X : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
      Module ((Proj 𝒜).ringCatSheaf.obj.obj X) ((presheafInAddCommGrp 𝒜 d).obj X) :=
    inferInstanceAs (Module ((Proj 𝒜).presheaf.obj X) ((sheafInType 𝒜 d).1.obj X))
  PresheafOfModules.ofPresheaf (presheafInAddCommGrp 𝒜 d) fun _ _ _ _ _ ↦ rfl

/-- **Stacks 01MN** (`constructions-definition-twist`) (part (1)): the `d`-th twist
`𝒪_{Proj 𝒜}(d) = 𝒜(d)~` of the structure sheaf of `Proj 𝒜`, as a sheaf of
`𝒪_{Proj 𝒜}`-modules.

The Stacks Project defines it as `S(n)~`, the sheaf associated to the shifted graded
module; here it is built directly as the subsheaf of `∏_x (𝒜_x)_d` of functions that are
locally a homogeneous fraction of degree `d`, which is the same sheaf. See this file's
module docstring, and the section COMMENTARY.md, for the choice. -/
@[stacks 01MN "(1)"]
noncomputable def twist : (Proj 𝒜).Modules where
  val := presheafOfModules 𝒜 d
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (sheafInType 𝒜 d).2

/-! ### Local triviality: `𝒪(d)` is free of rank one on `D₊(f)`

For `f` homogeneous of degree one, multiplication by `f^d` carries degree `e` sections to
degree `e + d` sections bijectively over any open inside `D₊(f)`. This is the local
triviality of `𝒪(d)`, and is the content of its invertibility on `ℙ^n` — where the graded
ring is generated in degree one, so the `D₊(f)` with `deg f = 1` cover. It is the input any
proof that twisting is exact, or that `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a+b)`, has to start from.

Note this says nothing at the generality of an arbitrary graded ring: without degree-one
elements there need be no such `f`, and indeed `𝒪(d)` is then not invertible (Stacks 01MS).
-/

variable (da db : ℤ)
/-- The pointwise product of a degree `a` section and a degree `b` section is a section of
degree `a + b`. -/
theorem mul_mem' {dc : ℤ} (hdc : dc = da + db) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : ∀ x : U.unop, atDeg 𝒜 da x.1) (b : ∀ x : U.unop, atDeg 𝒜 db x.1)
    (ha : (isLocallyFraction 𝒜 da).pred a) (hb : (isLocallyFraction 𝒜 db).pred b)
    (hm : ∀ x : U.unop, ((a x).1 * (b x).1) ∈
      degSet 𝒜 (x.1).asHomogeneousIdeal.toIdeal.primeCompl dc) :
    (isLocallyFraction 𝒜 dc).pred
      (fun x ↦ (⟨(a x).1 * (b x).1, hm x⟩ : atDeg 𝒜 dc x.1)) := by
  subst hdc
  intro x
  obtain ⟨Va, ma, ia, dda, dna, hda, ⟨ra, hra⟩, ⟨sa, hsa⟩, sa_nin, wa⟩ := ha x
  obtain ⟨Vb, mb, ib, ddb, dnb, hdb, ⟨rb, hrb⟩, ⟨sb, hsb⟩, sb_nin, wb⟩ := hb x
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, dda + ddb, dna + dnb,
    by push_cast; omega,
    ⟨ra * rb, SetLike.mul_mem_graded hra hrb⟩,
    ⟨sa * sb, SetLike.mul_mem_graded hsa hsb⟩,
    fun y ↦ mul_mem (sa_nin ⟨y.1, y.2.1⟩) (sb_nin ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp [wa y hy.1, wb y hy.2, Localization.mk_mul]

/-- On `D₊(f)` with `f` of degree one, `f^d` is a section of `𝒪(d)`. -/
theorem unitPow_pred {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (isLocallyFraction 𝒜 d).pred
      (fun x : U.unop ↦ (⟨(unitPow hf (hU x.2) d).embed,
        (unitPow hf (hU x.2) d).embed_mem⟩ : atDeg 𝒜 d x.1)) := by
  intro x
  refine ⟨U.unop, x.2, 𝟙 _, (-d).toNat, d.toNat, by omega,
    ⟨f ^ d.toNat, by simpa [smul_eq_mul] using SetLike.pow_mem_graded d.toNat hf⟩,
    ⟨f ^ (-d).toNat, by simpa [smul_eq_mul] using SetLike.pow_mem_graded (-d).toNat hf⟩,
    fun y ↦ Submonoid.pow_mem _ (hU y.2) _, fun _ ↦ rfl⟩

/-- Multiplication by `f^d` on sections over an open contained in `D₊(f)`. -/
def mulUnitPowSection {f : A} (hf : f ∈ 𝒜 1) (d e : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (g : (sheafInType 𝒜 e).1.obj U) : (sheafInType 𝒜 (e + d)).1.obj U :=
  ⟨fun x ↦ ⟨(g.1 x : Localization _) * (unitPow hf (hU x.2) d).embed,
      mul_mem_degSet (g.1 x).2 (unitPow hf (hU x.2) d).embed_mem⟩,
    mul_mem' 𝒜 e d rfl U g.1 _ g.2 (unitPow_pred 𝒜 hf d U hU) _⟩

theorem mulUnitPowSection_injective {f : A} (hf : f ∈ 𝒜 1) (d e : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Function.Injective (mulUnitPowSection 𝒜 hf d e U hU) := by
  intro g g' h
  refine Subtype.ext (funext fun x ↦ ?_)
  have hx := congrArg (fun s : (sheafInType 𝒜 (e + d)).1.obj U ↦ (s.1 x).1) h
  dsimp only [mulUnitPowSection] at hx
  refine Subtype.ext ?_
  have h2 : ((g.1 x).1 * (unitPow hf (hU x.2) d).embed) * (unitPow hf (hU x.2) (-d)).embed
      = ((g'.1 x).1 * (unitPow hf (hU x.2) d).embed) * (unitPow hf (hU x.2) (-d)).embed :=
    congrArg (fun z ↦ z * (unitPow hf (hU x.2) (-d)).embed) hx
  rw [mul_assoc, mul_assoc, unitPow_embed_mul, add_neg_cancel, unitPow_embed_zero,
    mul_one, mul_one] at h2
  exact h2

theorem mulUnitPowSection_surjective {f : A} (hf : f ∈ 𝒜 1) (d e : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Function.Surjective (mulUnitPowSection 𝒜 hf d e U hU) := by
  intro h
  have hde : e + d + -d = e := by ring
  have hmem : ∀ x : U.unop, ((h.1 x).1 * (unitPow hf (hU x.2) (-d)).embed) ∈
      degSet 𝒜 (x.1).asHomogeneousIdeal.toIdeal.primeCompl e := by
    intro x
    have := mul_mem_degSet (h.1 x).2 (unitPow hf (hU x.2) (-d)).embed_mem
    rwa [hde] at this
  have hpred : (isLocallyFraction 𝒜 e).pred (fun x : U.unop ↦
      (⟨(h.1 x).1 * (unitPow hf (hU x.2) (-d)).embed, hmem x⟩ : atDeg 𝒜 e x.1)) :=
    mul_mem' 𝒜 (e + d) (-d) hde.symm U h.1 _ h.2 (unitPow_pred 𝒜 hf (-d) U hU) hmem
  refine ⟨⟨_, hpred⟩, ?_⟩
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  show ((h.1 x).1 * (unitPow hf (hU x.2) (-d)).embed) * (unitPow hf (hU x.2) d).embed
      = (h.1 x).1
  rw [mul_assoc, unitPow_embed_mul, neg_add_cancel, unitPow_embed_zero, mul_one]

/-! ### `𝒪(0) = 𝒪`

The degree zero twist is the structure sheaf. Pointwise this is
`HomogeneousLocalization.degZeroEquiv`; here it is lifted to sections, which needs the two
"locally a fraction" predicates to agree — the degree zero condition `deg r - deg s = 0` is
Mathlib's "same degree" condition.

This is the unit of the family of twisting sheaves, and it is what turns the local
triviality above into a statement that `𝒪(d)` is *free of rank one* over `𝒪` on `D₊(f)`,
rather than merely that its sections are in bijection with those of `𝒪(e)`.
-/

/-- The degree zero predicate agrees with the structure sheaf's. -/
theorem isLocallyFraction_zero_iff {U : Opens (ProjectiveSpectrum.top 𝒜)}
    (g : ∀ x : U, HomogeneousLocalization.AtPrime 𝒜
      (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x.1))) :
    (isLocallyFraction 𝒜 0).pred
        (fun x ↦ (degZeroEquiv (g x) : atDeg 𝒜 0 x.1)) ↔
      (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred g := by
  constructor
  · rintro h x
    obtain ⟨V, m, i, dd, dn, hd, ⟨r, hr⟩, ⟨s, hs⟩, s_nin, w⟩ := h x
    have hdn : dn = dd := by omega
    subst hdn
    refine ⟨V, m, i, dn, ⟨r, hr⟩, ⟨s, hs⟩, fun y ↦ s_nin y, fun y ↦ ?_⟩
    apply HomogeneousLocalization.val_injective
    exact w y
  · rintro h x
    obtain ⟨V, m, i, j, ⟨r, hr⟩, ⟨s, hs⟩, s_nin, w⟩ := h x
    refine ⟨V, m, i, j, j, by omega, ⟨r, hr⟩, ⟨s, hs⟩, fun y ↦ s_nin y, fun y ↦ ?_⟩
    exact congrArg HomogeneousLocalization.val (w y)

/-- `𝒪(0) = 𝒪` on sections: the structure sheaf's sections are the degree zero sections. -/
noncomputable def sectionsZeroEquiv (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (Proj 𝒜).presheaf.obj U ≃ (sheafInType 𝒜 0).1.obj U where
  toFun g := ⟨fun x ↦ degZeroEquiv (g.1 x), (isLocallyFraction_zero_iff 𝒜 g.1).mpr g.2⟩
  invFun h := ⟨fun x ↦ degZeroEquiv.symm (h.1 x), by
    refine (isLocallyFraction_zero_iff 𝒜 (fun x ↦ degZeroEquiv.symm (h.1 x))).mp ?_
    have : (fun x ↦ (degZeroEquiv (degZeroEquiv.symm (h.1 x)) : atDeg 𝒜 0 x.1)) = h.1 := by
      funext x; simp
    rw [this]; exact h.2⟩
  left_inv g := by
    refine Subtype.ext (funext fun x ↦ ?_)
    simp
  right_inv h := by
    refine Subtype.ext (funext fun x ↦ ?_)
    simp

theorem sectionsZeroEquiv_add (U) (g g' : (Proj 𝒜).presheaf.obj U) :
    sectionsZeroEquiv 𝒜 U (g + g') = sectionsZeroEquiv 𝒜 U g + sectionsZeroEquiv 𝒜 U g' := by
  refine Subtype.ext (funext fun x ↦ ?_)
  exact (degZeroEquiv (𝒜 := 𝒜)
    (x := ((x.1 : ProjectiveSpectrum.top 𝒜)).asHomogeneousIdeal.toIdeal.primeCompl)).map_add
      (g.1 x) (g'.1 x)

theorem sectionsZeroEquiv_smul (U) (r g : (Proj 𝒜).presheaf.obj U) :
    sectionsZeroEquiv 𝒜 U (r * g) = r • sectionsZeroEquiv 𝒜 U g := by
  refine Subtype.ext (funext fun x ↦ ?_)
  exact (degZeroEquiv (𝒜 := 𝒜)
    (x := ((x.1 : ProjectiveSpectrum.top 𝒜)).asHomogeneousIdeal.toIdeal.primeCompl)).map_smul
      (r.1 x) (g.1 x)

/-! ### `𝒪(d)` is free of rank one on `D₊(f)`

Multiplication by `f^d` is not merely a bijection on sections but a `Γ(𝒪, U)`-linear one,
and composing it with `𝒪(0) = 𝒪` turns that into freeness: `trivializationEquiv` exhibits
`Γ(𝒪(d), U)` as a free rank one module over `Γ(𝒪, U)` with basis `f^d`, for every open `U`
inside `D₊(f)`.

Freeness rather than bijection is what a tensor-product computation needs, which is why the
`𝒪(0) = 𝒪` step above is on the critical path.

`unitSectionEquiv` is the form to use: it is literally `g ↦ g · f^d`, so it sends `1` to the
basis `f^d` (`unitSectionEquiv_one`) — and `mulSections_unitSection` says the bases multiply
correctly, `f^a · f^b = f^{a+b}`. Those two facts are what identify the multiplication map
with an isomorphism on `D₊(f)`.
-/

theorem mulUnitPowSection_add {f : A} (hf : f ∈ 𝒜 1) (d e : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (g g' : (sheafInType 𝒜 e).1.obj U) :
    mulUnitPowSection 𝒜 hf d e U hU (g + g')
      = mulUnitPowSection 𝒜 hf d e U hU g + mulUnitPowSection 𝒜 hf d e U hU g' := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  show ((g.1 x).1 + (g'.1 x).1) * _ = _
  exact add_mul _ _ _

theorem mulUnitPowSection_smul {f : A} (hf : f ∈ 𝒜 1) (d e : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (r : (Proj 𝒜).presheaf.obj U) (g : (sheafInType 𝒜 e).1.obj U) :
    mulUnitPowSection 𝒜 hf d e U hU (r • g) = r • mulUnitPowSection 𝒜 hf d e U hU g := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  show ((r.1 x).val * (g.1 x).1) * _ = (r.1 x).val * ((g.1 x).1 * _)
  exact mul_assoc _ _ _

/-- On `D₊(f)` with `f` of degree one, multiplication by `f^d` is a *linear* isomorphism
from degree `e` sections onto degree `e + d` sections: `𝒪(d)` is free of rank one there. -/
noncomputable def mulUnitPowSectionEquiv {f : A} (hf : f ∈ 𝒜 1) (d e : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (sheafInType 𝒜 e).1.obj U ≃ₗ[(Proj 𝒜).presheaf.obj U]
      (sheafInType 𝒜 (e + d)).1.obj U :=
  LinearEquiv.ofBijective
    { toFun := mulUnitPowSection 𝒜 hf d e U hU
      map_add' := mulUnitPowSection_add 𝒜 hf d e U hU
      map_smul' := mulUnitPowSection_smul 𝒜 hf d e U hU }
    ⟨mulUnitPowSection_injective 𝒜 hf d e U hU,
      mulUnitPowSection_surjective 𝒜 hf d e U hU⟩

/-- `𝒪(0) = 𝒪` on sections, as a linear equivalence. -/
noncomputable def sectionsZeroLinearEquiv (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (Proj 𝒜).presheaf.obj U ≃ₗ[(Proj 𝒜).presheaf.obj U] (sheafInType 𝒜 0).1.obj U where
  __ := sectionsZeroEquiv 𝒜 U
  map_add' := sectionsZeroEquiv_add 𝒜 U
  map_smul' := sectionsZeroEquiv_smul 𝒜 U

/-- **Stacks 01MN** (`constructions-definition-twist`) (part (1), degree zero): the
degree-zero twisting sheaf on `Proj 𝒜` is canonically isomorphic to the structure sheaf. -/
@[stacks 01MN "(1), degree zero"]
noncomputable def zeroIso :
    twist 𝒜 0 ≅ SheafOfModules.unit (Proj 𝒜).ringCatSheaf :=
  ((SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun U ↦ (sectionsZeroLinearEquiv 𝒜 U).toModuleIso)
      (by
        intro U V f
        rfl))).symm

/-- The degree-shift linear equivalence, with the output degree given by an equation so no
dependent rewrite is needed. -/
noncomputable def mulUnitPowSectionEquivOfEq {f : A} (hf : f ∈ 𝒜 1) (d e dc : ℤ)
    (hdc : dc = e + d) (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (sheafInType 𝒜 e).1.obj U ≃ₗ[(Proj 𝒜).presheaf.obj U]
      (sheafInType 𝒜 dc).1.obj U := by
  subst hdc; exact mulUnitPowSectionEquiv 𝒜 hf d e U hU

/-- The section `f^d` of `𝒪(d)` over an open inside `D₊(f)`. -/
def unitSection {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (sheafInType 𝒜 d).1.obj U :=
  ⟨fun x ↦ ⟨(unitPow hf (hU x.2) d).embed, (unitPow hf (hU x.2) d).embed_mem⟩,
    unitPow_pred 𝒜 hf d U hU⟩

/-- Scaling `f^d` by structure-sheaf sections: manifestly linear. -/
theorem smul_unitSection_injective {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Function.Injective (fun g : (Proj 𝒜).presheaf.obj U ↦ g • unitSection 𝒜 hf d U hU) := by
  intro g g' h
  refine Subtype.ext (funext fun x ↦ ?_)
  have hx : (g.1 x).val * (unitPow hf (hU x.2) d).embed
      = (g'.1 x).val * (unitPow hf (hU x.2) d).embed :=
    congrArg (fun s : (sheafInType 𝒜 d).1.obj U ↦ (s.1 x).1) h
  apply HomogeneousLocalization.val_injective _
  have h2 : ((g.1 x).val * (unitPow hf (hU x.2) d).embed) * (unitPow hf (hU x.2) (-d)).embed
      = ((g'.1 x).val * (unitPow hf (hU x.2) d).embed) * (unitPow hf (hU x.2) (-d)).embed :=
    congrArg (fun z ↦ z * (unitPow hf (hU x.2) (-d)).embed) hx
  rwa [mul_assoc, mul_assoc, unitPow_embed_mul, add_neg_cancel, unitPow_embed_zero,
    mul_one, mul_one] at h2

theorem smul_unitSection_surjective {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Function.Surjective (fun g : (Proj 𝒜).presheaf.obj U ↦ g • unitSection 𝒜 hf d U hU) := by
  intro h
  have hd : (0 : ℤ) = d + -d := by ring
  have hmem : ∀ x : U.unop, ((h.1 x).1 * (unitPow hf (hU x.2) (-d)).embed) ∈
      degSet 𝒜 (x.1).asHomogeneousIdeal.toIdeal.primeCompl 0 := by
    intro x
    have := mul_mem_degSet (h.1 x).2 (unitPow hf (hU x.2) (-d)).embed_mem
    rwa [← hd] at this
  have hpred0 : (isLocallyFraction 𝒜 0).pred (fun x : U.unop ↦
      (⟨(h.1 x).1 * (unitPow hf (hU x.2) (-d)).embed, hmem x⟩ : atDeg 𝒜 0 x.1)) :=
    mul_mem' 𝒜 d (-d) hd U h.1 _ h.2 (unitPow_pred 𝒜 hf (-d) U hU) hmem
  set g0 : ∀ x : U.unop, HomogeneousLocalization.AtPrime 𝒜
      (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x.1)) :=
    fun x ↦ degZeroEquiv.symm ⟨_, hmem x⟩ with hg0
  have hval : ∀ x : U.unop, (g0 x).val = (h.1 x).1 * (unitPow hf (hU x.2) (-d)).embed := by
    intro x
    exact congrArg Subtype.val (degZeroEquiv.apply_symm_apply ⟨_, hmem x⟩)
  have hpred : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred g0 := by
    refine (isLocallyFraction_zero_iff 𝒜 g0).mp ?_
    have heq : (fun x : U.unop ↦ (degZeroEquiv (g0 x) : atDeg 𝒜 0 x.1))
        = fun x ↦ (⟨(h.1 x).1 * (unitPow hf (hU x.2) (-d)).embed, hmem x⟩ : atDeg 𝒜 0 x.1) := by
      funext x; exact Subtype.ext (hval x)
    rw [heq]; exact hpred0
  refine ⟨⟨g0, hpred⟩, ?_⟩
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  show (g0 x).val * (unitPow hf (hU x.2) d).embed = (h.1 x).1
  rw [hval x, mul_assoc, unitPow_embed_mul, neg_add_cancel, unitPow_embed_zero, mul_one]

/-- On `D₊(f)` with `f` of degree one, `𝒪(d)` is free of rank one over `𝒪` with basis
`f^d`: the map `g ↦ g · f^d` is a linear isomorphism. -/
noncomputable def unitSectionEquiv {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    (Proj 𝒜).presheaf.obj U ≃ₗ[(Proj 𝒜).presheaf.obj U]
      (sheafInType 𝒜 d).1.obj U :=
  LinearEquiv.ofBijective
    { toFun := fun g ↦ g • unitSection 𝒜 hf d U hU
      map_add' := fun g g' ↦ add_smul g g' _
      map_smul' := fun r g ↦ mul_smul r g _ }
    ⟨smul_unitSection_injective 𝒜 hf d U hU, smul_unitSection_surjective 𝒜 hf d U hU⟩

@[simp]
theorem unitSectionEquiv_one {f : A} (hf : f ∈ 𝒜 1) (d : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    unitSectionEquiv 𝒜 hf d U hU 1 = unitSection 𝒜 hf d U hU := by
  show (1 : (Proj 𝒜).presheaf.obj U) • unitSection 𝒜 hf d U hU = _
  exact one_smul _ _

/-! ### The multiplication maps `𝒪(a) ⊗ 𝒪(b) → 𝒪(a+b)`

Stacks `constructions-equation-multiply`, in the same section as tag 01MN: since
`S(a) ⊗_S S(b) = S(a+b)` there are canonical maps `𝒪_X(a) ⊗ 𝒪_X(b) → 𝒪_X(a+b)`, which the
Stacks Project immediately warns are *not* isomorphisms in general (the example before tag
01MS). They are isomorphisms when the graded ring is generated in degree one, which is the
case of `ℙ^n`.

What is built here is the bilinear, restriction-compatible multiplication of sections that
those maps come from — `mulSectionsBilinear`, together with `mulSections_naturality`. It is then lifted objectwise through the presheaf tensor product
(`multiplyPresheafHom`) and across the universal property of sheafification
(`multiplyHom`). What is *not* done here is the proof that `multiplyHom` is an isomorphism
when `𝒜` is generated in degree one, which is where the local triviality above gets used.
-/
/-- Multiplication of a degree `a` section by a degree `b` section. -/
def mulSections (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (s : (sheafInType 𝒜 da).1.obj U) (t : (sheafInType 𝒜 db).1.obj U) :
    (sheafInType 𝒜 (da + db)).1.obj U :=
  ⟨fun x ↦ ⟨(s.1 x).1 * (t.1 x).1, mul_mem_degSet (s.1 x).2 (t.1 x).2⟩,
    mul_mem' 𝒜 da db rfl U s.1 t.1 s.2 t.2 _⟩

theorem mulSections_add_left (U) (s s' : (sheafInType 𝒜 da).1.obj U)
    (t : (sheafInType 𝒜 db).1.obj U) :
    mulSections 𝒜 da db U (s + s') t
      = mulSections 𝒜 da db U s t + mulSections 𝒜 da db U s' t := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  show ((s.1 x).1 + (s'.1 x).1) * (t.1 x).1 = _
  exact add_mul _ _ _

theorem mulSections_smul_left (U) (r : (Proj 𝒜).presheaf.obj U)
    (s : (sheafInType 𝒜 da).1.obj U) (t : (sheafInType 𝒜 db).1.obj U) :
    mulSections 𝒜 da db U (r • s) t = r • mulSections 𝒜 da db U s t := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  show ((r.1 x).val * (s.1 x).1) * (t.1 x).1 = (r.1 x).val * ((s.1 x).1 * (t.1 x).1)
  exact mul_assoc _ _ _

theorem mulSections_add_right (U) (s : (sheafInType 𝒜 da).1.obj U)
    (t t' : (sheafInType 𝒜 db).1.obj U) :
    mulSections 𝒜 da db U s (t + t')
      = mulSections 𝒜 da db U s t + mulSections 𝒜 da db U s t' := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  show (s.1 x).1 * ((t.1 x).1 + (t'.1 x).1) = _
  exact mul_add _ _ _

theorem mulSections_smul_right (U) (r : (Proj 𝒜).presheaf.obj U)
    (s : (sheafInType 𝒜 da).1.obj U) (t : (sheafInType 𝒜 db).1.obj U) :
    mulSections 𝒜 da db U s (r • t) = r • mulSections 𝒜 da db U s t := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  show (s.1 x).1 * ((r.1 x).val * (t.1 x).1) = (r.1 x).val * ((s.1 x).1 * (t.1 x).1)
  ring

/-- Restriction commutes with the multiplication of sections. -/
theorem mulSections_naturality {U V : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (i : U ⟶ V)
    (s : (sheafInType 𝒜 da).1.obj U) (t : (sheafInType 𝒜 db).1.obj U) :
    (sheafInType 𝒜 (da + db)).1.map i (mulSections 𝒜 da db U s t)
      = mulSections 𝒜 da db V ((sheafInType 𝒜 da).1.map i s)
          ((sheafInType 𝒜 db).1.map i t) := rfl

/-- The unit sections multiply as expected: `f^a · f^b = f^{a+b}`. -/
theorem mulSections_unitSection {f : A} (hf : f ∈ 𝒜 1) (a b : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    mulSections 𝒜 a b U (unitSection 𝒜 hf a U hU) (unitSection 𝒜 hf b U hU)
      = unitSection 𝒜 hf (a + b) U hU := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  exact unitPow_embed_mul hf (hU x.2) a b

/-- Multiplication of sections, bundled as a bilinear map. -/
noncomputable def mulSectionsBilinear (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (sheafInType 𝒜 da).1.obj U →ₗ[(Proj 𝒜).presheaf.obj U]
      (sheafInType 𝒜 db).1.obj U →ₗ[(Proj 𝒜).presheaf.obj U]
        (sheafInType 𝒜 (da + db)).1.obj U where
  toFun s :=
    { toFun := fun t ↦ mulSections 𝒜 da db U s t
      map_add' := mulSections_add_right 𝒜 da db U s
      map_smul' := fun r t ↦ mulSections_smul_right 𝒜 da db U r s t }
  map_add' s s' := by
    ext t
    exact mulSections_add_left 𝒜 da db U s s' t
  map_smul' r s := by
    ext t
    exact mulSections_smul_left 𝒜 da db U r s t

/-- **Stacks `constructions-equation-multiply`** (presheaf level): the multiplication
`𝒪(a) ⊗ 𝒪(b) → 𝒪(a+b)` as a morphism of presheaves of modules, obtained from
`mulSectionsBilinear` objectwise by `ModuleCat.MonoidalCategory.tensorLift`. Naturality is
`mulSections_naturality`. -/
noncomputable def multiplyPresheafHom :
    MonoidalCategoryStruct.tensorObj (C := (Proj 𝒜).PresheafOfModules)
      (twist 𝒜 da).val (twist 𝒜 db).val ⟶ (twist 𝒜 (da + db)).val where
  app U := ModuleCat.MonoidalCategory.tensorLift (mulSections 𝒜 da db U)
    (fun s s' t ↦ mulSections_add_left 𝒜 da db U s s' t)
    (fun r s t ↦ mulSections_smul_left 𝒜 da db U r s t)
    (fun s t t' ↦ mulSections_add_right 𝒜 da db U s t t')
    (fun r s t ↦ mulSections_smul_right 𝒜 da db U r s t)
  naturality {U V} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    exact mulSections_naturality 𝒜 da db f s t

/-- **Stacks `constructions-equation-multiply`**: the canonical map
`𝒪(a) ⊗_{𝒪} 𝒪(b) → 𝒪(a+b)` of sheaves of modules on `Proj 𝒜`, obtained from the presheaf
map by the universal property of sheafification.

The Stacks Project stresses that this is **not** an isomorphism in general (the example
before tag 01MS). It is one when `𝒜` is generated in degree one — in particular on `ℙ^n` —
and that is where `mulUnitPowSection_injective`/`_surjective` above get used. -/
noncomputable def multiplyHom :
    Scheme.Modules.tensor (twist 𝒜 da) (twist 𝒜 db) ⟶ twist 𝒜 (da + db) :=
  ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Proj 𝒜).ringCatSheaf.obj)).homEquiv _ _).symm (multiplyPresheafHom 𝒜 da db)

/-- On `D₊(f)`, the multiplication map on the tensor product is bijective: both sides are
free of rank one and it matches bases. -/
theorem bijective_tensorLift_mulSections {f : A} (hf : f ∈ 𝒜 1) (a b : ℤ)
    (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (hU : U.unop ≤ ProjectiveSpectrum.basicOpen 𝒜 f) :
    Function.Bijective (TensorProduct.lift (mulSectionsBilinear 𝒜 a b U)) := by
  set φ := (TensorProduct.lid ((Proj 𝒜).presheaf.obj U)
      ((Proj 𝒜).presheaf.obj U)).symm.trans
    (TensorProduct.congr (unitSectionEquiv 𝒜 hf a U hU) (unitSectionEquiv 𝒜 hf b U hU))
    with hφdef
  have key : (TensorProduct.lift (mulSectionsBilinear 𝒜 a b U)).comp φ.toLinearMap
      = (unitSectionEquiv 𝒜 hf (a + b) U hU).toLinearMap := by
    apply LinearMap.ext_ring
    show TensorProduct.lift (mulSectionsBilinear 𝒜 a b U)
        (TensorProduct.congr _ _ ((TensorProduct.lid _ _).symm 1)) = _
    rw [TensorProduct.lid_symm_apply, TensorProduct.congr_tmul]
    show mulSections 𝒜 a b U _ _ = _
    simp only [unitSectionEquiv_one]
    exact (mulSections_unitSection 𝒜 hf a b U hU).trans
      (unitSectionEquiv_one 𝒜 hf (a + b) U hU).symm
  have hcomp : Function.Bijective
      (⇑(TensorProduct.lift (mulSectionsBilinear 𝒜 a b U)) ∘ ⇑φ) := by
    have hfun : (⇑(TensorProduct.lift (mulSectionsBilinear 𝒜 a b U)) ∘ ⇑φ)
        = ⇑(unitSectionEquiv 𝒜 hf (a + b) U hU) := by
      funext y; exact DFunLike.congr_fun key y
    rw [hfun]
    exact (unitSectionEquiv 𝒜 hf (a + b) U hU).bijective
  have heq : ((⇑(TensorProduct.lift (mulSectionsBilinear 𝒜 a b U)) ∘ ⇑φ) ∘ ⇑φ.symm)
      = ⇑(TensorProduct.lift (mulSectionsBilinear 𝒜 a b U)) := by
    funext y; simp
  rw [← heq]
  exact hcomp.comp φ.symm.bijective

/-- **Stacks 01MN** (`constructions-definition-twist`) (part (2)): the `d`-th twist
`ℱ(d) = ℱ ⊗_{𝒪_X} 𝒪_X(d)` of an arbitrary sheaf of `𝒪_{Proj 𝒜}`-modules.

The tensor product of sheaves of modules on a scheme is not in Mathlib; it is supplied by
`StacksAndModuli/API/SchemeModulesTensor.lean` as the sheafification of the presheaf-level tensor
product. -/
@[stacks 01MN "(2)"]
noncomputable def twistModule (F : (Proj 𝒜).Modules) (d : ℤ) : (Proj 𝒜).Modules :=
  Scheme.Modules.tensor F (twist 𝒜 d)

/-- Twisting a sheaf of modules is functorial. -/
noncomputable def twistModuleMap {F F' : (Proj 𝒜).Modules} (φ : F ⟶ F') (d : ℤ) :
    twistModule 𝒜 F d ⟶ twistModule 𝒜 F' d :=
  Scheme.Modules.tensorMapLeft φ (twist 𝒜 d)

@[simp]
theorem twistModuleMap_id (F : (Proj 𝒜).Modules) (d : ℤ) :
    twistModuleMap 𝒜 (𝟙 F) d = 𝟙 (twistModule 𝒜 F d) :=
  Scheme.Modules.tensorMapLeft_id F (twist 𝒜 d)

@[simp]
theorem twistModuleMap_comp {F F' F'' : (Proj 𝒜).Modules} (φ : F ⟶ F') (φ' : F' ⟶ F'')
    (d : ℤ) :
    twistModuleMap 𝒜 (φ ≫ φ') d = twistModuleMap 𝒜 φ d ≫ twistModuleMap 𝒜 φ' d :=
  Scheme.Modules.tensorMapLeft_comp φ φ' (twist 𝒜 d)

end ProjectiveSpectrum.Twist
