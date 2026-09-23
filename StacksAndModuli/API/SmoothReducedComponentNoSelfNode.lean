module

public import StacksAndModuli.API.ComponentNormalizationFromSmoothStalks
public import StacksAndModuli.API.NodalCurveFiniteness
public import StacksAndModuli.API.SplitNodeIncidenceGraphConnected

/-!
# Smooth reduced components do not have self-nodes

If both formal branches of a split node belong to one irreducible component, then that
component is the unique irreducible component through the node.  A neighbourhood of the
node is therefore contained in the component, and reducedness identifies the ambient
scheme there with the reduced induced component.  Consequently a formally smooth reduced
component cannot contain such a self-node.

## Main results

* `AlgebraicGeometry.Scheme.IsNodalCurveOver.
    incidentComponents_ne_singleton_of_formallySmooth_reducedComponent`: pointwise
  formal smoothness of a reduced component excludes singleton branch incidence.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.
    incidentComponents_ne_singleton_of_smooth_reducedComponent`: the corresponding
  smooth-morphism criterion.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

namespace IsNodalCurveOver

/-- If the reduced induced structure on an irreducible component is formally smooth at
every point, the two formal branches of a split node cannot both be incident to that
component. -/
theorem incidentComponents_ne_singleton_of_formallySmooth_reducedComponent
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian C]
    (h : IsNodalCurveOver k C) (Z : irreducibleComponents C)
    (hformal : ∀ z : C.reducedIrreducibleComponent Z,
      ((C.reducedIrreducibleComponent Z ↘
        Spec (CommRingCat.of k)).stalkMap z).hom.FormallySmooth)
    (q : C.SplitNodePoints k) : q.incidentComponents ≠ {Z} := by
  let _ : IsNoetherian C := h.isNoetherian
  let _ : IsReduced C := h.isReduced
  intro hsingle
  have hZinc : Z ∈ q.incidentComponents := by
    rw [hsingle]
    simp
  have hqZ : q.1 ∈ Z.1 :=
    q.mem_component_of_inc Z
      ((splitNodeIncidenceGraph_inc_iff_mem_incidentComponents q Z).2 hZinc)
  have hunique : ∀ W : irreducibleComponents C, q.1 ∈ W.1 → W = Z := by
    intro W hqW
    have hWinc := q.mem_incidentComponents_of_mem W hqW
    rw [hsingle] at hWinc
    simpa using hWinc
  obtain ⟨U, _, hqU, hUZ⟩ :=
    C.exists_affineOpen_mem_le_component_of_unique Z q.1 hunique
  let i : C.reducedIrreducibleComponent Z ⟶ C :=
    C.reducedIrreducibleComponentι Z
  have hUrange : (U : Set C) ⊆ Set.range i := by
    rw [show Set.range i = Z.1 from C.range_reducedIrreducibleComponentι Z]
    exact hUZ
  let _ : IsIso (i ∣_ U) :=
    isIso_morphismRestrict_of_isClosedImmersion_of_le_range i U hUrange
  rw [← C.range_reducedIrreducibleComponentι Z] at hqZ
  obtain ⟨z, hz⟩ := hqZ
  have hzU : i z ∈ U := by
    rw [hz]
    exact hqU
  let _ : IsIso (i.stalkMap z) :=
    isIso_stalkMap_of_isIso_morphismRestrict i z U hzU
  have hcomp := hformal z
  change ((i ≫ (C ↘ Spec (CommRingCat.of k))).stalkMap z).hom.FormallySmooth at hcomp
  rw [Scheme.Hom.stalkMap_comp] at hcomp
  change ((i.stalkMap z).hom.comp
    ((C ↘ Spec (CommRingCat.of k)).stalkMap (i z)).hom).FormallySmooth at hcomp
  have hambient :
      ((C ↘ Spec (CommRingCat.of k)).stalkMap (i z)).hom.FormallySmooth :=
    (RingHom.FormallySmooth.respectsIso.cancel_right_isIso _ _).mp hcomp
  have hambient' :
      ((C ↘ Spec (CommRingCat.of k)).stalkMap q.1).hom.FormallySmooth := by
    rw [← hz]
    exact hambient
  exact h.not_formallySmooth_stalkMap_of_isSplitNodeAt q.2 hambient'

/-- A smooth reduced irreducible component of a nodal curve has two distinct incident
components at every split node. -/
theorem incidentComponents_ne_singleton_of_smooth_reducedComponent
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian C]
    (h : IsNodalCurveOver k C) (Z : irreducibleComponents C)
    [Smooth (C.reducedIrreducibleComponent Z ↘ Spec (CommRingCat.of k))]
    (q : C.SplitNodePoints k) : q.incidentComponents ≠ {Z} :=
  h.incidentComponents_ne_singleton_of_formallySmooth_reducedComponent Z
    (fun z ↦ (C.reducedIrreducibleComponent Z ↘
      Spec (CommRingCat.of k)).smoothLocus_eq_top.ge (Set.mem_univ z)) q

end IsNodalCurveOver

end AlgebraicGeometry.Scheme

end
