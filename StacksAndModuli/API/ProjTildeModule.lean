module

public import StacksAndModuli.API.HomogeneousLocalizationModuleDegree
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The sheaf `M~` on `Proj` of a graded ring

Step **9b** of `PLAN-hilbert-quot.md`, the module analogue of Stacks tag **01MN** as
formalized in
`stacks-project-lean/StacksProject/Constructions/InvertibleSheavesOnProj/definition-twist.lean`.
For a graded module `ℳ` over a graded ring `𝒜`, the sheaf `M~` on `Proj 𝒜` is the subsheaf
of `∏_{x ∈ U} (M_{(x)})_d` cut out by the local predicate "is locally a fraction `m / s`
with `deg m - deg s = d`".

Taking `ℳ = 𝒜` recovers the twisting sheaves `𝒪(d)`, so this generalizes
`ProjectiveSpectrum.Twist` verbatim; the file is a transcription of it with a module
numerator, resting on `StacksAndModuli/API/HomogeneousLocalizationModuleDegree.lean`.

## Main definitions

* `ProjectiveSpectrum.TildeModule.atDeg 𝒜 ℳ d x`: the value of `M~(d)` at a point.
* `ProjectiveSpectrum.TildeModule.isLocallyFraction 𝒜 ℳ d`: the local predicate.
* `ProjectiveSpectrum.TildeModule.sheafInType 𝒜 ℳ d`: `M~(d)` as a sheaf of types.
* `ProjectiveSpectrum.TildeModule.tilde 𝒜 ℳ d`: `M~(d)` as an object of `(Proj 𝒜).Modules`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite TopCat
open HomogeneousLocalization

namespace ProjectiveSpectrum.TildeModule

universe u

noncomputable section

variable {A : Type u} {σ : Type*} {M : Type u} {τ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable [AddCommGroup M] [Module A M] [SetLike τ M] [AddSubgroupClass τ M]
variable (𝒜 : ℕ → σ) (ℳ : ℕ → τ) [GradedRing 𝒜] [SetLike.GradedSMul 𝒜 ℳ]
variable (d : ℤ)

local notation3 "at " x =>
  HomogeneousLocalization.AtPrime 𝒜
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x))

/-- The value of `M~(d)` at a point: the degree-`d` part of the homogeneous localization of
`ℳ` there.  For `ℳ = 𝒜` this is `ProjectiveSpectrum.Twist.atDeg`. -/
abbrev atDeg (x : ProjectiveSpectrum.top 𝒜) : Type _ :=
  moduleDegSubmodule 𝒜 ℳ x.asHomogeneousIdeal.toIdeal.primeCompl d

variable {𝒜 ℳ d}

/-- The defining local condition: a dependent function on an open set is a *fraction of
degree `d`* when it is given by a single fraction `m / s` with `m` a homogeneous element of
the module and `s` a homogeneous element of the ring, whose degrees differ by `d`. -/
def IsFraction {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : ∀ x : U, atDeg 𝒜 ℳ d x.1) :
    Prop :=
  ∃ (i j : ℕ) (_ : (j : ℤ) = i + d) (r : ℳ j) (s : 𝒜 i)
    (s_nin : ∀ x : U, (s : A) ∈ x.1.asHomogeneousIdeal.toIdeal.primeCompl),
    ∀ x : U, (f x : LocalizedModule _ M) = LocalizedModule.mk (r : M) ⟨(s : A), s_nin x⟩

variable (𝒜 ℳ d)

/-- Being a fraction of degree `d` is a prelocal predicate: it passes to open subsets. -/
def isFractionPrelocal : PrelocalPredicate (atDeg 𝒜 ℳ d) where
  pred f := IsFraction f
  res := by
    rintro V U i f ⟨a, b, hab, r, s, h, w⟩
    exact ⟨a, b, hab, r, s, (h <| i ·), (w <| i ·)⟩

/-- The sheaf condition: sections of `M~(d)` are the dependent functions that are *locally*
a fraction of degree `d`. -/
def isLocallyFraction : LocalPredicate (atDeg 𝒜 ℳ d) :=
  (isFractionPrelocal 𝒜 ℳ d).sheafify

/-- The zero function is a section of `M~(d)`: writing `0` as `0 / s` forces
`deg s ≥ -d`, and a homogeneous denominator of large enough degree exists near each point
because points of `Proj` do not contain the irrelevant ideal. -/
theorem zero_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜 ℳ d).pred (0 : ∀ x : U.unop, atDeg 𝒜 ℳ d x.1) := by
  intro x
  obtain ⟨i, hiN, s, hs, hsx⟩ :=
    HasLargeDegrees.exists_homogeneous_mem (𝒜 := 𝒜)
      (x := x.1.asHomogeneousIdeal.toIdeal.primeCompl) (-d).toNat
  have hnn : (0 : ℤ) ≤ (i : ℤ) + d := by omega
  refine ⟨U.unop ⊓ ProjectiveSpectrum.basicOpen 𝒜 s, ⟨x.2, hsx⟩,
    homOfLE inf_le_left, i, ((i : ℤ) + d).toNat, Int.toNat_of_nonneg hnn,
    ⟨0, zero_mem _⟩, ⟨s, hs⟩, fun y ↦ y.2.2, fun _ ↦ ?_⟩
  exact (LocalizedModule.zero_mk _).symm

/-- Sections of `M~(d)` are closed under addition. -/
theorem add_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a b : ∀ x : U.unop, atDeg 𝒜 ℳ d x.1)
    (ha : (isLocallyFraction 𝒜 ℳ d).pred a) (hb : (isLocallyFraction 𝒜 ℳ d).pred b) :
    (isLocallyFraction 𝒜 ℳ d).pred (a + b) := by
  intro x
  obtain ⟨Va, ma, ia, dda, dna, hda, ⟨ra, hra⟩, ⟨sa, hsa⟩, sa_nin, wa⟩ := ha x
  obtain ⟨Vb, mb, ib, ddb, dnb, hdb, ⟨rb, hrb⟩, ⟨sb, hsb⟩, sb_nin, wb⟩ := hb x
  have hnat : dda + dnb = ddb + dna := by omega
  refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, dda + ddb, ddb + dna,
    by push_cast; omega,
    ⟨sb • ra + sa • rb, add_mem (SetLike.GradedSMul.smul_mem hsb hra)
      (hnat ▸ SetLike.GradedSMul.smul_mem hsa hrb)⟩,
    ⟨sa * sb, SetLike.mul_mem_graded hsa hsb⟩,
    fun y ↦ mul_mem (sa_nin ⟨y.1, y.2.1⟩) (sb_nin ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp [wa y hy.1, wb y hy.2, LocalizedModule.mk_add_mk]

/-- Sections of `M~(d)` are closed under negation. -/
theorem neg_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (a : ∀ x : U.unop, atDeg 𝒜 ℳ d x.1) (ha : (isLocallyFraction 𝒜 ℳ d).pred a) :
    (isLocallyFraction 𝒜 ℳ d).pred (-a) := by
  intro x
  obtain ⟨Va, ma, ia, dda, dna, hda, ⟨ra, hra⟩, ⟨sa, hsa⟩, sa_nin, wa⟩ := ha x
  refine ⟨Va, ma, ia, dda, dna, hda, ⟨-ra, neg_mem hra⟩, ⟨sa, hsa⟩, sa_nin,
    fun y ↦ ?_⟩
  simp only [Pi.neg_apply, wa y, NegMemClass.coe_neg, LocalizedModule.mk_neg]

/-- Sections of `M~(d)` are closed under multiplication by sections of the structure
sheaf, which is what makes `M~(d)` a sheaf of `𝒪_{Proj 𝒜}`-modules. -/
theorem smul_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (g : ∀ x : U.unop, at x.1) (a : ∀ x : U.unop, atDeg 𝒜 ℳ d x.1)
    (hg : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜).pred g)
    (ha : (isLocallyFraction 𝒜 ℳ d).pred a) :
    (isLocallyFraction 𝒜 ℳ d).pred (fun x ↦ g x • a x) := by
  intro x
  obtain ⟨Vg, mg, ig, k, ⟨c, hc⟩, ⟨e, he⟩, e_nin, wg⟩ := hg x
  obtain ⟨Va, ma, ia, dda, dna, hda, ⟨r, hr⟩, ⟨s, hs⟩, s_nin, wa⟩ := ha x
  refine ⟨Vg ⊓ Va, ⟨mg, ma⟩, Opens.infLELeft _ _ ≫ ig, k + dda, k + dna,
    by push_cast; omega,
    ⟨c • r, SetLike.GradedSMul.smul_mem hc hr⟩, ⟨e * s, SetLike.mul_mem_graded he hs⟩,
    fun y ↦ mul_mem (e_nin ⟨y.1, y.2.1⟩) (s_nin ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wg wa
  have hg' := wg y hy.1
  have ha' := wa y hy.2
  have hsm : ∀ (z : ProjectiveSpectrum.top 𝒜) (u : at z)
      (w : LocalizedModule
        (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal z)).primeCompl M),
      u • w = u.val • w := fun _ _ _ ↦ rfl
  simp only [Submodule.coe_smul, hsm]
  simp [hg', ha', HomogeneousLocalization.val_mk, LocalizedModule.mk_smul_mk]

/-- `M~(d)` before the module structure is installed. -/
def sheafInType : TopCat.Sheaf (Type _) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜 ℳ d)

/-- The sections of `M~(d)` over an open set, as an additive subgroup. -/
def sectionsAddSubgroup (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddSubgroup (∀ x : U.unop, atDeg 𝒜 ℳ d x.1) where
  carrier := {f | (isLocallyFraction 𝒜 ℳ d).pred f}
  zero_mem' := zero_mem' 𝒜 ℳ d U
  add_mem' ha hb := add_mem' 𝒜 ℳ d U _ _ ha hb
  neg_mem' ha := neg_mem' 𝒜 ℳ d U _ ha

instance addCommGroupSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    AddCommGroup ((sheafInType 𝒜 ℳ d).1.obj U) :=
  inferInstanceAs (AddCommGroup (sectionsAddSubgroup 𝒜 ℳ d U))

instance smulSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    SMul ((Proj 𝒜).presheaf.obj U) ((sheafInType 𝒜 ℳ d).1.obj U) where
  smul g a := ⟨fun x ↦ g.1 x • a.1 x, smul_mem' 𝒜 ℳ d U g.1 a.1 g.2 a.2⟩

@[simp]
theorem smul_apply (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
    (g : (Proj 𝒜).presheaf.obj U) (a : (sheafInType 𝒜 ℳ d).1.obj U) (x : U.unop) :
    (g • a).1 x = g.1 x • a.1 x := rfl

instance moduleSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Module ((Proj 𝒜).presheaf.obj U) ((sheafInType 𝒜 ℳ d).1.obj U) where
  one_smul _ := Subtype.ext (funext fun _ ↦ one_smul _ _)
  mul_smul _ _ _ := Subtype.ext (funext fun _ ↦ mul_smul _ _ _)
  smul_zero _ := Subtype.ext (funext fun _ ↦ smul_zero _)
  smul_add _ _ _ := Subtype.ext (funext fun _ ↦ smul_add _ _ _)
  add_smul _ _ _ := Subtype.ext (funext fun _ ↦ add_smul _ _ _)
  zero_smul _ := Subtype.ext (funext fun _ ↦ zero_smul _ _)

/-- `M~(d)` as a presheaf of abelian groups. -/
def presheafInAddCommGrp : Presheaf AddCommGrpCat (ProjectiveSpectrum.top 𝒜) where
  obj U := AddCommGrpCat.of ((sheafInType 𝒜 ℳ d).1.obj U)
  map i := AddCommGrpCat.ofHom
    { toFun := (sheafInType 𝒜 ℳ d).1.map i
      map_add' _ _ := rfl
      map_zero' := rfl }

/-- `M~(d)` as a presheaf of `𝒪_{Proj 𝒜}`-modules. -/
def presheafOfModules : (Proj 𝒜).PresheafOfModules :=
  letI (X : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
      Module ((Proj 𝒜).ringCatSheaf.obj.obj X) ((presheafInAddCommGrp 𝒜 ℳ d).obj X) :=
    inferInstanceAs (Module ((Proj 𝒜).presheaf.obj X) ((sheafInType 𝒜 ℳ d).1.obj X))
  PresheafOfModules.ofPresheaf (presheafInAddCommGrp 𝒜 ℳ d) fun _ _ _ _ _ ↦ rfl

/-- **Stacks 01M6** (the sheaf associated to a graded module): `M~(d)` as a sheaf of
`𝒪_{Proj 𝒜}`-modules.  For `ℳ = 𝒜` this is `ProjectiveSpectrum.Twist.twist`. -/
def tilde : (Proj 𝒜).Modules where
  val := presheafOfModules 𝒜 ℳ d
  isSheaf := (TopCat.Presheaf.isSheaf_iff_isSheaf_comp (forget AddCommGrpCat) _).2
    (sheafInType 𝒜 ℳ d).2

end

end ProjectiveSpectrum.TildeModule
