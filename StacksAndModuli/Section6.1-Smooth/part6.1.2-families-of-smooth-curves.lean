module

public import StacksAndModuli.«Section6.1-Smooth».«part6.1.1-curves»
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.2-examples»
public import StacksAndModuli.API.GeometricallyOverEtaleTargetLocal
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import StacksAndModuli.«Section2.1-Intro».«part2.1.2-the-grassmannian-functor»
public import StacksAndModuli.API.RelativeDifferentials
public import StacksAndModuli.API.SchemeModulesTensor
public import StacksAndModuli.API.PushforwardBaseChange

/-!
# Families of smooth curves of genus `g`

This module follows the subsection "Families of smooth curves" of §6.1 (Review of smooth
curves) of *Stacks and Moduli*, section
label `sec:smooth-curves`.

The book's definition reads: *a family of smooth curves (of genus `g`) over a scheme `S` is
a smooth and proper morphism `𝒞 → S` of schemes such that every geometric fiber is a
connected curve (of genus `g`)*. The parenthetical is the part supplied here: §3.4 already
carries the smooth-curve morphism property `smoothCurveProperty`
(`ex:moduli-prestack-of-smooth-curves`) together with the genus condition as an abstract
base-change-stable parameter `Q`; `genusProperty g` is that parameter, made concrete.

## Main result

- `AlgebraicGeometry.Scheme.isIso_unit_structureModule`: the currently formalized
  first part of Proposition 6.1.16, identifying `π_* 𝒪_𝒞` with `𝒪_S`.

## Supporting definitions and API

- `AlgebraicGeometry.Scheme.genusProperty`: every geometric fibre has genus `g`.
- `AlgebraicGeometry.Scheme.smoothCurveGenusProperty`: a family of smooth curves of
  genus `g`.

- base change stability of both, which is what lets them cut a full subprestack out of the
  prestack of families of smooth curves.
- `AlgebraicGeometry.Scheme.genus_pullback_of_genusProperty`: the defining property, read on
  the geometric fibre over a `K`-point of the base.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme

section PropFamiliesOfSmoothCurves

/-- **§6.1, "Families of smooth curves"** (unlabelled, preceding Proposition 6.1.16)
(the implicit genus condition): the morphism property
"every geometric fibre has genus `g`".

`Scheme.genus` is read over the fibre's own ring of global sections.  The quantification is
over algebraically closed fields, as in the book's phrase "geometric fibre"; the selected
structure map to the field spectrum is retained by `geometricallyOver`. -/
def genusGeometricFiberPredicate (g : ℕ) : GeometricFiberPredicate.{u} :=
  fun _ _ _ Z _ ↦ Z.genus = g

@[simp]
lemma genusGeometricFiberPredicate_apply (g : ℕ) (K : Type u) [Field K]
    [IsAlgClosed K] (Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of K))] :
    genusGeometricFiberPredicate g K Z ↔ Z.genus = g :=
  Iff.rfl

/-- Fixed intrinsic genus is invariant under isomorphisms over the geometric fibre's
field. -/
instance genusGeometricFiberPredicate_isClosedUnderIsomorphisms (g : ℕ) :
    (genusGeometricFiberPredicate.{u} g).IsClosedUnderIsomorphisms where
  of_iso e h :=
    (genus_eq_of_iso ((Over.forget _).mapIso e)).symm.trans h

/-- The morphism property that every geometric fibre has genus `g`. -/
def genusProperty (g : ℕ) : MorphismProperty Scheme.{u} :=
  geometricallyOver (genusGeometricFiberPredicate.{u} g)

lemma genusProperty_def (g : ℕ) :
    genusProperty.{u} g =
      geometricallyOver (genusGeometricFiberPredicate.{u} g) := rfl

/-- Having a fixed intrinsic genus is closed under isomorphisms of schemes. -/
instance genus_eq_isClosedUnderIsomorphisms (g : ℕ) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (C := Scheme.{u}) (fun Z ↦ Z.genus = g) :=
  ⟨fun e h ↦ (genus_eq_of_iso e).symm.trans h⟩

/-- The genus condition can be checked on the chosen pullback over every field-valued
point. -/
lemma genusProperty_iff {g : ℕ} {X Y : Scheme.{u}} {f : X ⟶ Y} :
    genusProperty g f ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (y : Spec (CommRingCat.of K) ⟶ Y),
        (Limits.pullback f y).genus = g := by
  rw [genusProperty_def, geometricallyOver_iff]
  simp only [genusGeometricFiberPredicate_apply]

/-- Having geometric fibres of genus `g` is preserved by arbitrary base change: it is a
`geometricallyOver` property. -/
instance genusProperty_isStableUnderBaseChange (g : ℕ) :
    (genusProperty.{u} g).IsStableUnderBaseChange :=
  inferInstanceAs (MorphismProperty.IsStableUnderBaseChange (geometricallyOver _))

/-- Fixed genus on geometric fibres is local on the target for the étale
precoverage. -/
instance genusProperty_isLocalAtTarget_etalePrecoverage (g : ℕ) :
    MorphismProperty.IsLocalAtTarget (genusProperty.{u} g)
      Scheme.etalePrecoverage :=
  geometricallyOver_isLocalAtTarget_etalePrecoverage _

/-- The defining property of `genusProperty`, read on a geometric fibre presented as a
pullback. -/
lemma genus_eq_of_genusProperty {g : ℕ} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : genusProperty g f) {K : Type u} [Field K] [IsAlgClosed K]
    (y : Spec (CommRingCat.of K) ⟶ Y)
    {Z : Scheme.{u}} (fst : Z ⟶ X) (snd : Z ⟶ Spec (CommRingCat.of K))
    (h : IsPullback fst snd f y) : Z.genus = g :=
  hf y fst snd h

/-- The defining property of `genusProperty`, read on the honest pullback. -/
lemma genus_pullback_of_genusProperty {g : ℕ} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : genusProperty g f) (K : Type u) [Field K] [IsAlgClosed K]
    (y : Spec (CommRingCat.of K) ⟶ Y) :
    (Limits.pullback f y).genus = g :=
  pullback_of_geometricallyOver hf K y

/-- **`genusProperty g` says what it should: every geometric fibre has `h¹ = g`.** For a
geometric fibre `Z` over an algebraically closed field `K` — presented as a pullback square
whose right-hand edge is the structure morphism `Z ↘ Spec K` — the intrinsic genus is the
book's `h¹(Z, 𝒪_Z) = dim_K H¹(Z, 𝒪_Z)`.

The hypotheses `IsIntegral Z` and `UniversallyClosed (Z ↘ Spec K)` are what
`Scheme.genusOver_eq_genus_of_isAlgClosed` needs; both hold for the geometric fibres of a
family of smooth curves. -/
lemma genusOver_eq_of_genusProperty {g : ℕ} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : genusProperty g f) (K : Type u) [Field K] [IsAlgClosed K]
    (y : Spec (CommRingCat.of K) ⟶ Y) {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))]
    (fst : Z ⟶ X) (h : IsPullback fst (Z ↘ Spec (CommRingCat.of K)) f y)
    [IsIntegral Z] [UniversallyClosed (Z ↘ Spec (CommRingCat.of K))] :
    genusOver K Z = g := by
  rw [genusOver_eq_genus_of_isAlgClosed K Z]
  exact genus_eq_of_genusProperty hf y fst _ h

/-- **The genus condition, read off a geometric fibre, with the hypotheses discharged.**
For a proper, geometrically integral morphism satisfying `genusProperty g` — which is what
a family of smooth curves of genus `g` is, once one knows that smooth plus geometrically
connected implies geometrically integral — every geometric fibre `Z` over an algebraically
closed field `K` satisfies `h¹(Z, 𝒪_Z) = g` in the book's sense.

`GeometricallyIntegral` is carried as a hypothesis rather than derived from
`SmoothOfRelativeDimension 1 ⊓ GeometricallyConnected`: Mathlib has neither
"smooth over a field implies reduced" nor "connected plus regular implies irreducible", so
the derivation is not available. See this folder's COMMENTARY.md. -/
lemma genusOver_eq_of_genusProperty_of_isProper {g : ℕ} {X Y : Scheme.{u}} {f : X ⟶ Y}
    [UniversallyClosed f] [GeometricallyIntegral f] (hf : genusProperty g f)
    (K : Type u) [Field K] [IsAlgClosed K] (y : Spec (CommRingCat.of K) ⟶ Y)
    {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))] (fst : Z ⟶ X)
    (h : IsPullback fst (Z ↘ Spec (CommRingCat.of K)) f y) :
    genusOver K Z = g := by
  haveI : IsIntegral Z :=
    GeometricallyIntegral.geometrically_isIntegral y fst _ h
  haveI : UniversallyClosed (Z ↘ Spec (CommRingCat.of K)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback h ‹UniversallyClosed f›
  exact genusOver_eq_of_genusProperty hf K y fst h

/-- **§6.1, "Families of smooth curves"** (unlabelled, preceding Proposition 6.1.16):
a *family of smooth curves of genus `g`* is a smooth and
proper morphism all of whose geometric fibres are connected curves of genus `g`.

The first three conditions are §3.4's `smoothCurveProperty`; the fourth is
`genusProperty g`. -/
def smoothCurveGenusProperty (g : ℕ) : MorphismProperty Scheme.{u} :=
  smoothCurveProperty.{u} ⊓ genusProperty.{u} g

lemma mem_smoothCurveGenusProperty_iff {g : ℕ} {X S : Scheme.{u}} (f : X ⟶ S) :
    smoothCurveGenusProperty g f ↔ smoothCurveProperty.{u} f ∧ genusProperty.{u} g f :=
  Iff.rfl

/-- A family of smooth curves of genus `g` stays one after arbitrary base change. -/
instance smoothCurveGenusProperty_isStableUnderBaseChange (g : ℕ) :
    (smoothCurveGenusProperty.{u} g).IsStableUnderBaseChange := by
  constructor
  intro X Y Y' S f g' f' g'' sq h
  exact ⟨(smoothCurveProperty_isStableUnderBaseChange).of_isPullback sq h.1,
    (genusProperty_isStableUnderBaseChange _).of_isPullback sq h.2⟩

/-- **Proposition 6.1.16** (`prop:families-of-smooth-curves`) (part (1)): for a family of
smooth curves `π : 𝒞 → S` of genus `g ≥ 2`, `π_* 𝒪_𝒞 = 𝒪_S`.

The equality of the book is the assertion that the *canonical* map `𝒪_S → π_* 𝒪_𝒞` is an
isomorphism, which is what is stated: the unit of the adjunction
`π^* ⊣ π_*` at `𝒪_S` is `𝒪_S ⟶ π_*(π^* 𝒪_S)`, and `π^* 𝒪_S` is `𝒪_𝒞`.

The proof (deferred) is Cohomology and Base Change (Theorem A.6.8), as spelled out in
Proposition A.6.11: the fibres are proper,
geometrically connected and geometrically reduced, so `H⁰(𝒞_s, 𝒪_{𝒞_s}) = κ(s)` for every
`s ∈ S`, and cohomology and base change upgrades this to the statement over `S`.

Parts (2)–(4) of the proposition — that `π_*(Ω_{𝒞/S}^{⊗ k})` is a vector bundle of rank
`g` for `k = 1` and `(2k-1)(g-1)` for `k > 1` with formation commuting with base change,
that `R¹π_* Ω_{𝒞/S}^{⊗ k}` is `𝒪_S` for `k = 1` and zero otherwise, and that
`Ω_{𝒞/S}^{⊗ k}` is relatively very ample for `k ≥ 3` — are still not stated, but the
obstruction is no longer the sheaf `Ω_{X/S}` itself: it is now constructed, as
`AlgebraicGeometry.Scheme.Hom.relativeDifferentials` in
`StacksAndModuli/API/RelativeDifferentials.lean`, with its universal property.  What is missing is
the affine-localization theory of that sheaf (recorded as the explicit hypotheses of the
`…_affineCompatibility` reductions in `StacksAndModuli/API/RelativeDifferentialsAffineComparison.lean`),
higher direct images `R¹π_*`, and relative very ampleness.  See this folder's
COMMENTARY.md. -/
theorem isIso_unit_structureModule {g : ℕ} (hg : 2 ≤ g) {C S : Scheme.{u}} (π : C ⟶ S)
    (hπ : smoothCurveGenusProperty g π) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app
      (structureModule S)) := by
  sorry

/-- Background definition for Proposition 6.1.16 (the implicit numerical data of part (2)):
the rank `r(k)` of `π_*(Ω_{𝒞/S}^{⊗ k})` for a family of smooth curves of genus `g`, namely
`g` for `k = 1` and `(2k-1)(g-1)` for `k > 1`. -/
def pluricanonicalRank (g k : ℕ) : ℕ := if k = 1 then g else (2 * k - 1) * (g - 1)

@[simp] lemma pluricanonicalRank_one (g : ℕ) : pluricanonicalRank g 1 = g := by
  simp [pluricanonicalRank]

lemma pluricanonicalRank_of_one_lt {g k : ℕ} (hk : 1 < k) :
    pluricanonicalRank g k = (2 * k - 1) * (g - 1) := by
  simp [pluricanonicalRank, hk.ne']

/-- **Proposition 6.1.16** (`prop:families-of-smooth-curves`) (part (2)): for a family of
smooth curves `π : 𝒞 → S` of genus `g ≥ 2` and `k ≥ 1`, the pushforward
`π_*(Ω_{𝒞/S}^{⊗ k})` is a vector bundle of rank `r(k)` — equal to `g` for `k = 1` and
`(2k-1)(g-1)` for `k > 1` — whose construction commutes with base change.

"Commutes with base change" is rendered as the base-change comparison map
`f^* π_*(Ω^{⊗ k}) ⟶ π_{T,*}(f'^* Ω^{⊗ k})` of `StacksAndModuli/API/PushforwardBaseChange.lean`
being an isomorphism for every cartesian square over `π`.  The book writes the right-hand
side as `π_{T,*}(Ω_{𝒞_T/T}^{⊗ k})`; the two agree because the formation of relative
differentials commutes with base change, which is a separate statement and is not assumed
here.  See this folder's COMMENTARY.md.

The proof (deferred) is Cohomology and Base Change (Theorem A.6.8) together with
Riemann–Roch on the fibres: `deg Ω_{𝒞_s}^{⊗ k} = k(2g-2)`, so `h⁰ = (2k-1)(g-1)` for
`k > 1` by Riemann–Roch and vanishing of `h¹`, and `h⁰ = g` for `k = 1` by Serre duality.
Theorem A.6.8 is not formalized — it needs the higher direct images `Rⁱ π_*` as
`𝒪_S`-modules — and neither Riemann–Roch nor Serre duality is available. -/
theorem isProjectiveOfRank_pushforward_pluricanonical {g : ℕ} (hg : 2 ≤ g)
    {C S : Scheme.{u}} (π : C ⟶ S) (hπ : smoothCurveGenusProperty g π) (k : ℕ)
    (hk : 1 ≤ k) :
    Modules.IsProjectiveOfRank (pluricanonicalRank g k)
        ((Modules.pushforward π).obj (Modules.tensorPower π.relativeDifferentials k)) ∧
      Modules.PushforwardCommutesWithBaseChange (f := π)
        (Modules.tensorPower π.relativeDifferentials k) := by
  sorry

end PropFamiliesOfSmoothCurves

end AlgebraicGeometry.Scheme
