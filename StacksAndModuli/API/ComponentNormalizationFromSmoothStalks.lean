module

public import StacksAndModuli.API.ComponentGenericSections
public import StacksAndModuli.API.NormalizationComponents

/-!
# Component normalization from smooth stalks

An isomorphism of schemes may be checked on restrictions to an open neighbourhood of
every target point. Applying this to normalization shows that a reduced curve with
formally smooth stalks is already normal. The componentwise version equips a reduced
irreducible component with its inherited map to the base and applies the same argument.

## Main results

* `AlgebraicGeometry.isIso_of_exists_open_mem_isIso_morphismRestrict`: an isomorphism
  criterion from pointwise target neighbourhoods.
* `AlgebraicGeometry.isIso_morphismRestrict_of_isClosedImmersion_of_le_range`: a reduced
  open contained in the range of a closed immersion is unchanged by base change.
* `AlgebraicGeometry.Scheme.
    reducedIrreducibleComponent_formallySmooth_stalk_of_ambient`: formal smoothness
  passes from the ambient scheme to its unique reduced component at a smooth point.
* `AlgebraicGeometry.Scheme.normalizationMap_isIso_of_formallySmooth_stalks`: a reduced
  one-dimensional scheme with formally smooth stalks agrees with its normalization.
* `AlgebraicGeometry.Scheme.
    reducedIrreducibleComponent_normalizationMap_isIso_of_formallySmooth_stalks`: the
  corresponding criterion for a reduced irreducible component.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A scheme morphism is an isomorphism if its restriction to some open neighbourhood
of every target point is an isomorphism. -/
theorem isIso_of_exists_open_mem_isIso_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U)) :
    IsIso f := by
  choose U hyU hU using h
  rw [← MorphismProperty.isomorphisms.iff]
  apply IsZariskiLocalAtTarget.of_iSup_eq_top U
  · apply le_antisymm le_top
    intro y _
    exact (le_iSup U y) (hyU y)
  · intro y
    exact (MorphismProperty.isomorphisms.iff _).mpr (hU y)

/-- The restriction of a closed immersion over an open contained in its range is an
isomorphism when the target is reduced. -/
theorem isIso_morphismRestrict_of_isClosedImmersion_of_le_range
    {X Y : Scheme.{u}} [IsReduced Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (U : Y.Opens) (hU : (U : Set Y) ⊆ Set.range f) :
    IsIso (f ∣_ U) := by
  let _ : Surjective (f ∣_ U) := ⟨by
    intro y
    obtain ⟨x, hx⟩ := hU y.property
    let xU : f ⁻¹ᵁ U := ⟨x, by
      change f x ∈ U
      rw [hx]
      exact y.property⟩
    refine ⟨xU, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    change (f ∣_ U ≫ U.ι) xU = U.ι y
    rw [morphismRestrict_ι]
    exact hx⟩
  exact isIso_of_isClosedImmersion_of_surjective (f ∣_ U)

/-- If a morphism restricts to an isomorphism over an open containing the image of a
source point, then its stalk map at that point is an isomorphism. -/
theorem isIso_stalkMap_of_isIso_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (U : Y.Opens)
    (hx : f x ∈ U) [IsIso (f ∣_ U)] :
    IsIso (f.stalkMap x) := by
  let xU : f ⁻¹ᵁ U := ⟨x, hx⟩
  have hcomp : IsIso ((f ∣_ U ≫ U.ι).stalkMap xU) := by
    rw [Scheme.Hom.stalkMap_comp]
    infer_instance
  rw [morphismRestrict_ι, Scheme.Hom.stalkMap_comp] at hcomp
  let _ : IsIso
      (f.stalkMap x ≫ (f ⁻¹ᵁ U).ι.stalkMap xU) := hcomp
  exact IsIso.of_isIso_comp_right (f.stalkMap x)
    ((f ⁻¹ᵁ U).ι.stalkMap xU)

namespace Scheme

/-- Every specified base map on a scheme induces a base map on its reduced irreducible
components. -/
noncomputable instance reducedIrreducibleComponent_over
    {S X : Scheme.{u}} [X.Over S] (Z : irreducibleComponents X) :
    (X.reducedIrreducibleComponent Z).Over S :=
  ⟨X.reducedIrreducibleComponentι Z ≫ (X ↘ S)⟩

/-- A reduced scheme of dimension at most one whose stalk maps to a field are formally
smooth agrees with its normalization. -/
theorem normalizationMap_isIso_of_formallySmooth_stalks
    {K : Type u} [Field K] (X : Scheme.{u}) [IsReduced X]
    [Finite (irreducibleComponents X)] (f : X ⟶ Spec (.of K))
    [LocallyOfFinitePresentation f]
    (hformal : ∀ x : X, (f.stalkMap x).hom.FormallySmooth)
    (hdim : topologicalKrullDim X ≤ 1) : IsIso X.normalizationMap := by
  apply isIso_of_exists_open_mem_isIso_morphismRestrict
  intro x
  obtain ⟨U, _, hxU, hU⟩ :=
    X.exists_affineOpen_mem_isIso_normalizationMap_of_formallySmooth
      f x (hformal x) hdim
  exact ⟨U, hxU, hU⟩

/-- At an ambient formally smooth point, the stalk of the unique reduced irreducible
component through that point is formally smooth over the same field. -/
theorem reducedIrreducibleComponent_formallySmooth_stalk_of_ambient
    {K : Type u} [Field K] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K))] [IsReduced X]
    [Finite (irreducibleComponents X)]
    [LocallyOfFinitePresentation (X ↘ Spec (CommRingCat.of K))]
    (Z : irreducibleComponents X) (x : X.reducedIrreducibleComponent Z)
    (hx : ((X ↘ Spec (CommRingCat.of K)).stalkMap
      (X.reducedIrreducibleComponentι Z x)).hom.FormallySmooth) :
    ((X.reducedIrreducibleComponent Z ↘
      Spec (CommRingCat.of K)).stalkMap x).hom.FormallySmooth := by
  let q : X := X.reducedIrreducibleComponentι Z x
  have hqZ : q ∈ Z.1 := x.property
  obtain ⟨U, _, hqU, hU⟩ :=
    X.exists_affineOpen_mem_le_smoothPointComponent
      (X ↘ Spec (CommRingCat.of K)) q hx
  have hcomponent : X.smoothPointComponent
      (X ↘ Spec (CommRingCat.of K)) q hx = Z :=
    ((X.eq_smoothPointComponent_iff_mem
      (X ↘ Spec (CommRingCat.of K)) q hx Z).mpr hqZ).symm
  rw [hcomponent] at hU
  have hUrange : (U : Set X) ⊆
      Set.range (X.reducedIrreducibleComponentι Z) := by
    rw [X.range_reducedIrreducibleComponentι Z]
    exact hU
  let _ : IsIso (X.reducedIrreducibleComponentι Z ∣_ U) :=
    isIso_morphismRestrict_of_isClosedImmersion_of_le_range
      (X.reducedIrreducibleComponentι Z) U hUrange
  have hinc : IsIso
      ((X.reducedIrreducibleComponentι Z).stalkMap x) :=
    isIso_stalkMap_of_isIso_morphismRestrict
      (X.reducedIrreducibleComponentι Z) x U hqU
  let _ : IsIso
      ((X.reducedIrreducibleComponentι Z).stalkMap x) := hinc
  change ((X.reducedIrreducibleComponentι Z ≫
    (X ↘ Spec (CommRingCat.of K))).stalkMap x).hom.FormallySmooth
  rw [Scheme.Hom.stalkMap_comp]
  exact hx.comp <| RingHom.FormallySmooth.of_bijective
    (ConcreteCategory.bijective_of_isIso
      ((X.reducedIrreducibleComponentι Z).stalkMap x))

/-- A reduced irreducible component of a Noetherian one-dimensional scheme agrees with
its normalization if all stalk maps of the component to the ground field are formally
smooth. -/
theorem reducedIrreducibleComponent_normalizationMap_isIso_of_formallySmooth_stalks
    {K : Type u} [Field K] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of K))] [IsNoetherian X]
    [LocallyOfFinitePresentation (X ↘ Spec (CommRingCat.of K))]
    (Z : irreducibleComponents X)
    (hformal : ∀ x : X.reducedIrreducibleComponent Z,
      ((X.reducedIrreducibleComponent Z ↘ Spec (CommRingCat.of K)).stalkMap x).hom.FormallySmooth)
    (hdim : topologicalKrullDim X ≤ 1) :
    IsIso (X.reducedIrreducibleComponent Z).normalizationMap := by
  let _ : LocallyOfFinitePresentation
      (X.reducedIrreducibleComponentι Z) := inferInstance
  let _ : LocallyOfFinitePresentation
      (X.reducedIrreducibleComponent Z ↘ Spec (CommRingCat.of K)) := by
    change LocallyOfFinitePresentation
      (X.reducedIrreducibleComponentι Z ≫
        (X ↘ Spec (CommRingCat.of K)))
    infer_instance
  apply normalizationMap_isIso_of_formallySmooth_stalks
    (X.reducedIrreducibleComponent Z)
    (X.reducedIrreducibleComponent Z ↘ Spec (CommRingCat.of K)) hformal
  exact
    (X.reducedIrreducibleComponentι Z).isClosedEmbedding.isInducing.topologicalKrullDim_le.trans
      hdim

end Scheme

end AlgebraicGeometry

end
