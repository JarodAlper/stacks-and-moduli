module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.Topology.Sets.CompactOpenCovered
public import StacksAndModuli.Util.Precoverage

/-!
# Singleton fpqc coverings

Supporting API with no Stacks Project counterpart of its own: the morphism property of being a
one-element fpqc covering family, packaged so that the descent statements of §3.1 and §3.3 can
be phrased as hypotheses on a single morphism.

Throughout §3.1, "`{f}` is an fpqc covering" is rendered as
`Presieve.singleton f ∈ Scheme.fpqcPrecoverage Y`. This module names that condition
`AlgebraicGeometry.Scheme.IsFpqcCover` and records the projections the descent proofs need.

Mathlib supplies everything used here: `Scheme.fpqcPrecoverage` is by definition
`qcPrecoverage ⊓ Scheme.precoverage @Flat`, its quasi-compactness component is
`QuasiCompactCover` (which Mathlib tags `@[stacks 022B]`, the Stacks Project's definition of an
fpqc covering), and `IsCompactOpenCovered.iff_of_unique` specialises the covering condition to a
one-element family.

Main declarations:
- `AlgebraicGeometry.Scheme.IsFpqcCover`: the morphism property;
- `IsFpqcCover.flat`, `.surjective`: the two component properties of the covering morphism;
- `IsFpqcCover.exists_compact_opens_image_eq`: over an affine open of the target, a
  quasi-compact open of the source surjects onto it — the Stacks 022B condition;
- `IsFpqcCover.of_flat_of_surjective_of_quasiCompact`, `IsFpqcCover.of_fppf`: the two ways
  such covers arise in the text.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

open CategoryTheory TopologicalSpace

universe u

-- `Scheme.fpqcPrecoverage` and friends are defined in Mathlib under this option (see
-- `Mathlib/AlgebraicGeometry/Sites/Fpqc.lean`); without it, `@Flat` will not unify with
-- `MorphismProperty Scheme` when unfolding `precoverage @Flat`.
set_option backward.isDefEq.respectTransparency.types false

/-- A morphism `f : X ⟶ Y` **is an fpqc cover** when the one-element family `{f}` is an fpqc
covering of `Y`, i.e. `Presieve.singleton f ∈ Scheme.fpqcPrecoverage Y`.

Since `fpqcPrecoverage = qcPrecoverage ⊓ precoverage @Flat`, an `IsFpqcCover` hypothesis
splits as `.1` (the quasi-compactness condition of Stacks 022B) and `.2` (joint surjectivity
together with flatness). -/
def IsFpqcCover : MorphismProperty Scheme.{u} :=
  fun _ Y f ↦ Presieve.singleton f ∈ Scheme.fpqcPrecoverage Y

namespace IsFpqcCover

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

lemma mem_precoverage_flat (hf : IsFpqcCover f) :
    Presieve.singleton f ∈ Scheme.precoverage @Flat Y := hf.2

/-- An fpqc cover is flat. -/
lemma flat (hf : IsFpqcCover f) : Flat f :=
  ((Scheme.singleton_mem_precoverage_iff (P := @Flat) f).mp hf.2).2

/-- An fpqc cover is surjective. -/
lemma surjective (hf : IsFpqcCover f) : Surjective f :=
  ⟨((Scheme.singleton_mem_precoverage_iff (P := @Flat) f).mp hf.2).1⟩

/-- **The quasi-compactness condition of an fpqc covering (Stacks 022B).** Over any affine open
`U` of the target there is a quasi-compact open of the source whose image is exactly `U`. -/
lemma exists_compact_opens_image_eq (hf : IsFpqcCover f) {U : Y.Opens} (hU : IsAffineOpen U) :
    ∃ V : X.Opens, IsCompact (V : Set X) ∧ f.base '' (V : Set X) = (U : Set Y) := by
  have := hf.surjective
  have hflat := hf.flat
  have hqc : QuasiCompactCover
      (Scheme.Hom.cover.{u, 0} (P := @Flat) f hflat).toPreZeroHypercover := by
    rw [← Scheme.presieve₀_mem_qcPrecoverage_iff, Scheme.Hom.presieve₀_cover]
    exact hf.1
  have h := QuasiCompactCover.isCompactOpenCovered_of_isAffineOpen
    (𝒰 := (Scheme.Hom.cover.{u, 0} (P := @Flat) f hflat).toPreZeroHypercover) hU
  rw [IsCompactOpenCovered.iff_of_unique] at h
  obtain ⟨V, hV, hVe⟩ := h
  exact ⟨V, hV, hVe⟩

end IsFpqcCover

/-- Being a singleton fpqc cover is stable under base change: Mathlib derives
`Precoverage.IsStableUnderBaseChange` for `fpqcPrecoverage`, and
`Precoverage.mem_singleton_of_isPullback` specialises it to singleton presieves. -/
instance : MorphismProperty.IsStableUnderBaseChange IsFpqcCover.{u} where
  of_isPullback sq hg := Precoverage.mem_singleton_of_isPullback hg sq.flip

namespace IsFpqcCover

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- A surjective, flat, quasi-compact morphism is an fpqc cover. -/
lemma of_flat_of_surjective_of_quasiCompact (f : X ⟶ Y) [Flat f] [Surjective f]
    [QuasiCompact f] : IsFpqcCover f :=
  Scheme.Hom.singleton_mem_fpqcPrecoverage f

/-- An fppf cover is an fpqc cover. -/
lemma of_fppf (f : X ⟶ Y) [Flat f] [Surjective f] [LocallyOfFinitePresentation f] :
    IsFpqcCover f :=
  Scheme.fppfPrecoverage_le_fpqcPrecoverage _ (Scheme.Hom.singleton_mem_fppfPrecoverage f)

end IsFpqcCover

end AlgebraicGeometry.Scheme
