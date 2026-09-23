module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import StacksAndModuli.Util.Precoverage

/-!
# Fpqc descent for morphisms of schemes

This module formalizes Proposition 3.1.7 (`prop:fpqc-descent-for-morphisms`) and
Corollary 3.1.10 (`cor:morXY-is-sheaf`) of §3.1 (Descent theory, `sec:descent-theory`) of
*Stacks and Moduli*. Per-label completeness is
tracked in this folder's STATUS.md.

Throughout, "`{f}` is an fpqc covering" is rendered as
`Presieve.singleton f ∈ Scheme.fpqcPrecoverage S`; in particular this holds for surjective
flat quasi-compact morphisms (`Scheme.Hom.singleton_mem_fpqcPrecoverage`). The results are
deduced from the subcanonicity of the fpqc topology (`Scheme.fpqcTopology.Subcanonical`),
which is Mathlib's form of `prop:schemes-are-sheaves-in-fpqc-topology`.

Base change of a singleton covering along any morphism is
`CategoryTheory.Precoverage.mem_singleton_of_isPullback`, in `StacksAndModuli.Util.Precoverage`.

The property `AlgebraicGeometry.Scheme.IsFpqcCover` of a morphism — that its singleton presieve
is an fpqc covering — lives in `StacksAndModuli.Util.FpqcCover` and is used by
`part3.1.4-descending-schemes`, `part3.1.5-descending-properties`, `part3.1.6-local-properties`
and `part3.3.3-morphisms-gluing-epimorphisms`.

Main results:
- `AlgebraicGeometry.Scheme.existsUnique_desc_of_singleton_mem_fpqcPrecoverage`: descent of
  morphisms along an fpqc covering (`prop:fpqc-descent-for-morphisms`);
- `AlgebraicGeometry.Scheme.existsUnique_desc_over_of_singleton_mem_fpqcPrecoverage`: the
  relative version, for morphisms over a base (`cor:morXY-is-sheaf` (1));
- `AlgebraicGeometry.Scheme.existsUnique_desc_pullback_of_singleton_mem_fpqcPrecoverage`:
  descent of morphisms between base changes (`cor:morXY-is-sheaf` (2)).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section PropFpqcDescentForMorphisms

open CategoryTheory Limits Opposite AlgebraicGeometry

universe v u

namespace AlgebraicGeometry.Scheme

variable {S' S : Scheme.{u}} (f : S' ⟶ S)

/-- **Proposition 3.1.7** (`prop:fpqc-descent-for-morphisms`): fpqc descent for morphisms.
Let `{f : S' ⟶ S}` be an fpqc covering of schemes (e.g. `f` surjective, flat, and
quasi-compact) and let `Y` be a scheme. Every morphism `g : S' ⟶ Y` whose two compositions
with the projections `S' ×_S S' ⇉ S'` agree descends to a unique morphism `h : S ⟶ Y` with
`f ≫ h = g`. -/
theorem existsUnique_desc_of_singleton_mem_fpqcPrecoverage
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S) {Y : Scheme.{u}} (g : S' ⟶ Y)
    (hg : pullback.fst f f ≫ g = pullback.snd f f ≫ g) :
    ∃! h : S ⟶ Y, f ≫ h = g := by
  have hY : Presieve.IsSheaf Scheme.fpqcTopology (yoneda.obj Y) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := Scheme.fpqcTopology) _
  have hsheaf : Presieve.IsSheafFor (yoneda.obj Y) (Presieve.singleton f) :=
    hY.isSheafFor_of_mem_precoverage hf
  -- the compatible family of elements determined by `g`
  let x : Presieve.FamilyOfElements (yoneda.obj Y) (Presieve.singleton f) :=
    fun Z k hk ↦ Presieve.singleton.rec (motive := fun Z k _ ↦ Z ⟶ Y) g hk
  have hx : x.Compatible := by
    rintro Z₁ Z₂ W g₁ g₂ k₁ k₂ ⟨⟩ ⟨⟩ w
    have h₁ : pullback.lift g₁ g₂ w ≫ pullback.fst f f = g₁ := pullback.lift_fst ..
    have h₂ : pullback.lift g₁ g₂ w ≫ pullback.snd f f = g₂ := pullback.lift_snd ..
    calc (g₁ ≫ g : W ⟶ _)
        = (pullback.lift g₁ g₂ w ≫ pullback.fst f f) ≫ g := by rw [h₁]
      _ = (pullback.lift g₁ g₂ w ≫ pullback.snd f f) ≫ g := by
          rw [Category.assoc, Category.assoc, hg]
      _ = g₂ ≫ g := by rw [h₂]
  obtain ⟨h, hh, huniq⟩ := hsheaf x hx
  refine ⟨h, hh f Presieve.singleton.mk, fun h' hh' ↦ huniq h' ?_⟩
  rintro Z k ⟨⟩
  exact hh'

end AlgebraicGeometry.Scheme

end PropFpqcDescentForMorphisms

section CorMorXYIsSheaf

open CategoryTheory Limits Opposite AlgebraicGeometry

universe v u

namespace AlgebraicGeometry.Scheme

variable {S' S : Scheme.{u}} (f : S' ⟶ S)

/-- **Corollary 3.1.10** (`cor:morXY-is-sheaf`) (part (1)): the relative version of fpqc
descent for morphisms. With `{f : S' ⟶ S}` an fpqc covering, `S` a scheme over `T`, and `Y`
a `T`-scheme, every `T`-morphism `g : S' ⟶ Y` equalizing the projections descends to a
unique `T`-morphism `h : S ⟶ Y`. -/
theorem existsUnique_desc_over_of_singleton_mem_fpqcPrecoverage
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    {T : Scheme.{u}} (pS : S ⟶ T) {Y : Scheme.{u}} (pY : Y ⟶ T) (g : S' ⟶ Y)
    (hgT : g ≫ pY = f ≫ pS)
    (hg : pullback.fst f f ≫ g = pullback.snd f f ≫ g) :
    ∃! h : S ⟶ Y, f ≫ h = g ∧ h ≫ pY = pS := by
  obtain ⟨h, hh, huniq⟩ := existsUnique_desc_of_singleton_mem_fpqcPrecoverage f hf g hg
  have hT : h ≫ pY = pS := by
    -- both descend the `T`-structure morphism of `S'`, so they agree by uniqueness
    have hgT' : pullback.fst f f ≫ (f ≫ pS) = pullback.snd f f ≫ (f ≫ pS) := by
      rw [← Category.assoc, ← Category.assoc, pullback.condition]
    obtain ⟨k, -, kuniq⟩ :=
      existsUnique_desc_of_singleton_mem_fpqcPrecoverage f hf (f ≫ pS) hgT'
    rw [kuniq (h ≫ pY) (show f ≫ (h ≫ pY) = f ≫ pS by rw [← Category.assoc, hh, hgT]),
      kuniq pS rfl]
  exact ⟨h, ⟨hh, hT⟩, fun h' hh' ↦ huniq h' hh'.1⟩

/-- **Corollary 3.1.10** (`cor:morXY-is-sheaf`) (part (2)): fpqc descent for morphisms
between base changes. Let `{f : S' ⟶ S}` be an fpqc covering and let `X` and `Y` be schemes
over `S`. An `S`-morphism `g : X ×_S S' ⟶ Y` whose two pullbacks to
`(X ×_S S') ×_X (X ×_S S')` agree descends to a unique `S`-morphism `u : X ⟶ Y` with
`pullback.fst ≫ u = g`. (Identifying `S'`-morphisms `X ×_S S' ⟶ Y ×_S S'` with
`S`-morphisms `X ×_S S' ⟶ Y`, this is the exactness of
`Mor_S(X, Y) → Mor_{S'}(X_{S'}, Y_{S'}) ⇉ Mor_{S''}(X_{S''}, Y_{S''})`.) -/
theorem existsUnique_desc_pullback_of_singleton_mem_fpqcPrecoverage
    (hf : Presieve.singleton f ∈ Scheme.fpqcPrecoverage S)
    {X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (g : pullback pX f ⟶ Y)
    (hgS : g ≫ pY = pullback.fst pX f ≫ pX)
    (hg : pullback.fst (pullback.fst pX f) (pullback.fst pX f) ≫ g =
      pullback.snd (pullback.fst pX f) (pullback.fst pX f) ≫ g) :
    ∃! u : X ⟶ Y, pullback.fst pX f ≫ u = g ∧ u ≫ pY = pX := by
  have hf' : Presieve.singleton (pullback.fst pX f) ∈ Scheme.fpqcPrecoverage X :=
    Precoverage.mem_singleton_of_isPullback hf (IsPullback.of_hasPullback pX f)
  exact existsUnique_desc_over_of_singleton_mem_fpqcPrecoverage (pullback.fst pX f) hf' pX
    pY g hgS hg

/- API reformulation of Proposition 3.1.7 (effective epimorphism, cf. Equation 3.1.8): an fpqc
morphism is an *effective epimorphism* of schemes. For a surjective, flat, quasi-compact
morphism this is an instance in Mathlib. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [Flat f] [QuasiCompact f] :
    EffectiveEpi f :=
  inferInstance

end AlgebraicGeometry.Scheme

end CorMorXYIsSheaf
