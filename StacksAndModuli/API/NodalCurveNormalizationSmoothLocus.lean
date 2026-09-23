module

public import StacksAndModuli.API.ComponentGenericSections
public import StacksAndModuli.API.NodalCurveFiniteness
public import StacksAndModuli.API.NodalCurveNormalization
public import StacksAndModuli.API.SchemeModuleStalkSupport

/-!
# Normalization of a nodal curve away from its nodes

The normalization of a nodal curve is locally an isomorphism at every smooth point.
More precisely, every such point has an affine neighbourhood on which the normalization
is an isomorphism and the cokernel of the structure-sheaf normalization unit vanishes.
Since smooth points are exactly the non-nodes, both conclusions are also exposed using
the intrinsic split-node predicate.

## Main results

* `AlgebraicGeometry.Scheme.IsNodalCurveOver.
    exists_affineOpen_mem_isIso_normalizationMap_of_formallySmooth`.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.
    exists_affineOpen_mem_isZero_normalizationDefect_of_formallySmooth`.
* The corresponding `..._of_not_isSplitNodeAt` formulations.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.
    normalizationDefect_stalkSupport_subset_splitNodeLocus`: the normalization defect is
  supported at the nodes.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

namespace IsNodalCurveOver

/-- Every formally smooth point of a nodal curve has an affine neighbourhood on which
the normalization morphism is an isomorphism. -/
theorem exists_affineOpen_mem_isIso_normalizationMap_of_formallySmooth
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) (x : C)
    (hx : ((C ↘ Spec (CommRingCat.of k)).stalkMap x).hom.FormallySmooth) :
    ∃ U : C.Opens, IsAffineOpen U ∧ x ∈ U ∧
      IsIso (h.normalizationMap ∣_ U) := by
  let _ : IsReduced C := h.isReduced
  let _ : IsNoetherian C := h.isNoetherian
  simpa only [IsNodalCurveOver.normalizationMap] using
    C.exists_affineOpen_mem_isIso_normalizationMap_of_formallySmooth
      (C ↘ Spec (CommRingCat.of k)) x hx h.isCurve.topologicalKrullDim_eq.le

/-- Every formally smooth point of a nodal curve has an affine neighbourhood on which
the cokernel of the structure-sheaf normalization unit vanishes. -/
theorem exists_affineOpen_mem_isZero_normalizationDefect_of_formallySmooth
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) (x : C)
    (hx : ((C ↘ Spec (CommRingCat.of k)).stalkMap x).hom.FormallySmooth) :
    ∃ U : C.Opens, IsAffineOpen U ∧ x ∈ U ∧
      IsZero ((Modules.restrictFunctor U.ι).obj
        (cokernel (SheafOfModules.unitToPushforwardObjUnit
          h.normalizationMap.toRingCatSheafHom))) := by
  let _ : IsReduced C := h.isReduced
  let _ : IsNoetherian C := h.isNoetherian
  simpa only [IsNodalCurveOver.normalizationMap] using
    C.exists_affineOpen_mem_isZero_normalizationDefect_of_formallySmooth
      (C ↘ Spec (CommRingCat.of k)) x hx h.isCurve.topologicalKrullDim_eq.le

/-- Every non-node of a nodal curve has an affine neighbourhood on which normalization
is an isomorphism. -/
theorem exists_affineOpen_mem_isIso_normalizationMap_of_not_isSplitNodeAt
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) (x : C)
    (hx : ¬ C.IsSplitNodeAt k x) :
    ∃ U : C.Opens, IsAffineOpen U ∧ x ∈ U ∧
      IsIso (h.normalizationMap ∣_ U) :=
  h.exists_affineOpen_mem_isIso_normalizationMap_of_formallySmooth x
    ((h.formallySmooth_iff_not_isSplitNodeAt x).mpr hx)

/-- Every non-node of a nodal curve has an affine neighbourhood on which the
normalization defect vanishes. -/
theorem exists_affineOpen_mem_isZero_normalizationDefect_of_not_isSplitNodeAt
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) (x : C)
    (hx : ¬ C.IsSplitNodeAt k x) :
    ∃ U : C.Opens, IsAffineOpen U ∧ x ∈ U ∧
      IsZero ((Modules.restrictFunctor U.ι).obj
        (cokernel (SheafOfModules.unitToPushforwardObjUnit
          h.normalizationMap.toRingCatSheafHom))) :=
  h.exists_affineOpen_mem_isZero_normalizationDefect_of_formallySmooth x
    ((h.formallySmooth_iff_not_isSplitNodeAt x).mpr hx)

/-- The stalk support of the normalization defect of a nodal curve is contained in the
split-node locus. -/
theorem normalizationDefect_stalkSupport_subset_splitNodeLocus
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    Modules.stalkSupport
      (cokernel (SheafOfModules.unitToPushforwardObjUnit
        h.normalizationMap.toRingCatSheafHom)) ⊆
      {x : C | C.IsSplitNodeAt k x} := by
  intro x hx
  by_contra hxnode
  obtain ⟨U, _hU, hxU, hzero⟩ :=
    h.exists_affineOpen_mem_isZero_normalizationDefect_of_not_isSplitNodeAt x hxnode
  exact hx (Modules.isZero_stalk_of_isZero_restrict _ U hzero ⟨x, hxU⟩)

end IsNodalCurveOver

end AlgebraicGeometry.Scheme

end
