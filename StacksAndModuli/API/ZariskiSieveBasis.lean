module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!
# A locally directed open basis inside a Zariski covering sieve

Every covering sieve for the big Zariski topology contains an open cover.  The open
subsets of the base which are contained in one member of that cover form a basis.  When
ordered by inclusion, their canonical open subschemes give a locally directed open cover.

This is a convenient interface between sieve-indexed descent data and Mathlib's relative
gluing theorem, whose input is a locally directed open cover.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

/-- The open subsets of `S` contained in the range of some member of `𝒰`. -/
abbrev OpenCover.BasisIndex (𝒰 : S.OpenCover) :=
  { V : S.Opens // ∃ i : 𝒰.I₀, V ≤ (𝒰.f i).opensRange }

/-- Refining an open cover by all open subsets contained in one of its members. -/
@[simps I₀ X f]
def OpenCover.basisRefinement (𝒰 : S.OpenCover) : S.OpenCover where
  I₀ := 𝒰.BasisIndex
  X V := V.1
  f V := V.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun _ ↦ inferInstance⟩
    obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
    let V : S.Opens := (𝒰.f i).opensRange
    refine ⟨⟨V, i, le_rfl⟩, ⟨x, ?_⟩, rfl⟩
    rw [Scheme.Hom.mem_opensRange]
    exact ⟨y, hy⟩

/-- The ranges in `basisRefinement` form a basis of the topology of the base scheme. -/
lemma OpenCover.basisRefinement_isBasis (𝒰 : S.OpenCover) :
    Opens.IsBasis
      (Set.range fun i : 𝒰.basisRefinement.I₀ ↦
        (𝒰.basisRefinement.f i).opensRange) := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hxU
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq x
  have hxrange : x ∈ (𝒰.f i).opensRange := by
    rw [Scheme.Hom.mem_opensRange]
    exact ⟨y, hy⟩
  let V : S.Opens := U ⊓ (𝒰.f i).opensRange
  let j : 𝒰.basisRefinement.I₀ := ⟨V, i, inf_le_right⟩
  refine ⟨V, ⟨j, ?_⟩, ⟨hxU, hxrange⟩, inf_le_left⟩
  change (Scheme.Opens.ι (U ⊓ (𝒰.f i).opensRange)).opensRange =
    U ⊓ (𝒰.f i).opensRange
  exact Opens.opensRange_ι _

/-- The basis refinement is ordered by inclusion of its ranges. -/
instance OpenCover.basisRefinementPreorder (𝒰 : S.OpenCover) :
    Preorder 𝒰.basisRefinement.I₀ where
  le i j := i.1 ≤ j.1
  le_refl _ := le_rfl
  le_trans _ _ _ h h' := h.trans h'

lemma OpenCover.basisRefinement_le_iff (𝒰 : S.OpenCover)
    (i j : 𝒰.basisRefinement.I₀) :
    i ≤ j ↔ (𝒰.basisRefinement.f i).opensRange ≤
      (𝒰.basisRefinement.f j).opensRange := by
  change i.1 ≤ j.1 ↔ i.1.ι.opensRange ≤ j.1.ι.opensRange
  simp

/-- The basis refinement is locally directed, with transition maps induced by inclusion
of open subsets. -/
instance OpenCover.basisRefinementLocallyDirected (𝒰 : S.OpenCover) :
    𝒰.basisRefinement.LocallyDirected :=
  Cover.LocallyDirected.ofIsBasisOpensRange
    (fun {_ _} ↦ 𝒰.basisRefinement_le_iff _ _) 𝒰.basisRefinement_isBasis

/-- If every member of `𝒰` belongs to a sieve `R`, then every arrow of its basis
refinement also belongs to `R`. -/
lemma OpenCover.basisRefinement_mem_sieve (𝒰 : S.OpenCover) (R : Sieve S)
    (h𝒰 : Presieve.ofArrows 𝒰.X 𝒰.f ≤ R) (i : 𝒰.basisRefinement.I₀) :
    R (𝒰.basisRefinement.f i) := by
  obtain ⟨j, hij⟩ := i.property
  have hij' : Set.range (𝒰.basisRefinement.f i) ⊆ Set.range (𝒰.f j) := by
    intro x hx
    change x ∈ Set.range (Scheme.Opens.ι i.1) at hx
    rw [Opens.range_ι] at hx
    exact hij hx
  let g : 𝒰.basisRefinement.X i ⟶ 𝒰.X j :=
    IsOpenImmersion.lift (𝒰.f j) (𝒰.basisRefinement.f i) hij'
  have hj : Presieve.ofArrows 𝒰.X 𝒰.f (𝒰.f j) := by
    exact ⟨j⟩
  have hg := R.downward_closed (h𝒰 (𝒰.X j) (𝒰.f j) hj) g
  rw [IsOpenImmersion.lift_fac] at hg
  exact hg

/-- A chosen open cover contained in a covering sieve for the big Zariski topology. -/
noncomputable def zariskiOpenCoverOfSieve (R : Sieve S)
    (hR : R ∈ zariskiTopology S) : S.OpenCover :=
  (exists_cover_of_mem_grothendieckTopology hR).choose

/-- Every arrow of the chosen open cover belongs to the original sieve. -/
lemma zariskiOpenCoverOfSieve_le (R : Sieve S) (hR : R ∈ zariskiTopology S) :
    Presieve.ofArrows (zariskiOpenCoverOfSieve R hR).X
      (zariskiOpenCoverOfSieve R hR).f ≤ R :=
  (exists_cover_of_mem_grothendieckTopology hR).choose_spec

/-- The canonical locally directed basis refinement contained in a Zariski covering
sieve. -/
noncomputable abbrev zariskiBasisCoverOfSieve (R : Sieve S)
    (hR : R ∈ zariskiTopology S) : S.OpenCover :=
  (zariskiOpenCoverOfSieve R hR).basisRefinement

/-- Every arrow of the locally directed basis refinement belongs to the original
sieve. -/
lemma zariskiBasisCoverOfSieve_mem (R : Sieve S) (hR : R ∈ zariskiTopology S)
    (i : (zariskiBasisCoverOfSieve R hR).I₀) :
    R ((zariskiBasisCoverOfSieve R hR).f i) :=
  (zariskiOpenCoverOfSieve R hR).basisRefinement_mem_sieve R
    (zariskiOpenCoverOfSieve_le R hR) i

end AlgebraicGeometry.Scheme
