module

public import StacksAndModuli.API.NodalCurvePointSupport
public import StacksAndModuli.API.PointSupportStalkSupport

/-!
# Stalk support of the node-residue module

The finite direct sum of residue-field modules attached to the split nodes of a nodal
curve is supported on its split-node locus.  Together with the corresponding support
theorem for the normalization defect, this reduces any globally defined comparison map
between the two modules to its maps on node stalks.

## Main result

* `IsNodalCurveOver.nodeResidueSupportModule_stalkSupport_subset_splitNodeLocus`: the
  node-residue module has no nonzero stalk away from the split nodes.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The finite residue-field module attached to the split nodes of a nodal curve is
supported on the split-node locus. -/
theorem IsNodalCurveOver.nodeResidueSupportModule_stalkSupport_subset_splitNodeLocus
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : C.IsNodalCurveOver k) :
    Modules.stalkSupport h.nodeResidueSupportModule ⊆
      {x : C | C.IsSplitNodeAt k x} := by
  let _ : Finite (C.SplitNodePoints k) := h.finite_splitNodePoints
  intro x hx
  have hxrange : x ∈ Set.range
      (fun q : C.SplitNodePoints k ↦ q.1) :=
    stalkSupport_finiteResiduePointSupportModule_subset_range C
      (fun q : C.SplitNodePoints k ↦ q.1) h.isClosed_splitNodePoint hx
  obtain ⟨q, rfl⟩ := hxrange
  exact q.2

end AlgebraicGeometry.Scheme

end
