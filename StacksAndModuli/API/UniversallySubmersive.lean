module

public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.Topology.LocalAtTarget

/-!
# Universally submersive morphisms of schemes

A morphism of schemes is universally submersive when every base change is a
quotient map on underlying topological spaces. This file supplies the definition
and its basic locality and base-change API.
-/

@[expose] public section

open Set TopologicalSpace CategoryTheory Limits

universe u

namespace Topology

/-- A continuous map whose restrictions over an open cover of its target are
quotient maps is itself a quotient map. -/
lemma IsQuotientMap.of_openCover {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {ι : Type u} (U : ι → Opens Y)
    (hU : IsOpenCover U) (hf : Continuous f)
    (H : ∀ i, IsQuotientMap ((U i : Set Y).restrictPreimage f)) :
    IsQuotientMap f := by
  refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen fun s ↦ ?_, ?_⟩
  · constructor
    · intro hs
      rw [hU.isOpen_iff_coe_preimage]
      intro i
      rw [← (H i).isOpen_preimage]
      exact continuous_subtype_val.isOpen_preimage _ hs
    · exact hf.isOpen_preimage s
  · intro y
    obtain ⟨i, hi⟩ := hU.exists_mem y
    obtain ⟨x, hx⟩ := (H i).surjective ⟨y, hi⟩
    exact ⟨x.1, congrArg Subtype.val hx⟩

end Topology

namespace AlgebraicGeometry

open CategoryTheory.MorphismProperty

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance : (topologically @Topology.IsQuotientMap :
    MorphismProperty Scheme.{u}).RespectsIso :=
  topologically_respectsIso _ (fun e ↦ e.isQuotientMap)
    (fun _ _ hf hg ↦ hg.comp hf)

/-- A morphism of schemes is universally submersive if every base change is a
quotient map on the underlying topological spaces. -/
@[mk_iff]
class UniversallySubmersive (f : X ⟶ Y) : Prop where
  universally_isQuotientMap :
    universally (topologically @Topology.IsQuotientMap) f

namespace UniversallySubmersive

theorem eq : @UniversallySubmersive =
    universally (topologically @Topology.IsQuotientMap) := by
  ext X Y f
  rw [universallySubmersive_iff]

instance : RespectsIso @UniversallySubmersive :=
  eq.symm ▸ inferInstance

instance : IsStableUnderBaseChange @UniversallySubmersive :=
  eq.symm ▸ inferInstance

instance : IsZariskiLocalAtTarget @UniversallySubmersive := by
  rw [eq]
  apply universally_isZariskiLocalAtTarget
  intro X Y f ι U hU H
  simp_rw [topologically, morphismRestrict_base] at H
  exact Topology.IsQuotientMap.of_openCover U hU f.continuous H

end UniversallySubmersive

end AlgebraicGeometry
