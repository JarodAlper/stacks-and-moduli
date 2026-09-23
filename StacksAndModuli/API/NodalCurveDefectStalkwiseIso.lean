module

public import StacksAndModuli.API.NodalCurveGenusFormula
public import StacksAndModuli.API.NodalCurvePointSupportStalkSupport
public import StacksAndModuli.API.SchemeModuleStalkwiseIso

/-!
# Stalkwise comparison of a nodal normalization defect

Both the normalization-defect module of a nodal curve and its finite node-residue model
are supported on the split-node locus.  Therefore any global module morphism between
them is an isomorphism as soon as its maps on split-node stalks are isomorphisms.

This isolates the exact gluing datum still required by the local completed-node
calculation: the pointwise comparisons must be induced by one global module morphism.

## Main results

* `IsNodalCurveOver.isIso_normalizationDefectToNodeResidueSupport_of_stalkwise`: a
  global comparison is an isomorphism if it is so at every split node.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationDefectIsoNodeResidueSupportOfStalkwise`:
  the corresponding packaged module isomorphism.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A global comparison from the normalization defect to the node-residue module is an
isomorphism if it induces an isomorphism on every split-node stalk. -/
theorem IsNodalCurveOver.isIso_normalizationDefectToNodeResidueSupport_of_stalkwise
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (f : h.normalizationDefectModule ⟶ h.nodeResidueSupportModule)
    (hf : ∀ x : C, C.IsSplitNodeAt k x → IsIso
      ((Modules.toPresheaf C ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f)) :
    IsIso f :=
  Modules.isIso_of_stalkFunctor_map_iso_on_support f
    {x : C | C.IsSplitNodeAt k x}
    h.normalizationDefectModule_stalkSupport_subset_splitNodeLocus
    h.nodeResidueSupportModule_stalkSupport_subset_splitNodeLocus hf

/-- Package a global normalization-defect comparison that is an isomorphism on every
split-node stalk as an isomorphism with the node-residue module. -/
noncomputable def
    IsNodalCurveOver.normalizationDefectIsoNodeResidueSupportOfStalkwise
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k)
    (f : h.normalizationDefectModule ⟶ h.nodeResidueSupportModule)
    (hf : ∀ x : C, C.IsSplitNodeAt k x → IsIso
      ((Modules.toPresheaf C ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map f)) :
    h.normalizationDefectModule ≅ h.nodeResidueSupportModule := by
  let _ : IsIso f :=
    h.isIso_normalizationDefectToNodeResidueSupport_of_stalkwise f hf
  exact asIso f

end AlgebraicGeometry.Scheme

end
