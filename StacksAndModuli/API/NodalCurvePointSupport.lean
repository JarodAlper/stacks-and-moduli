module

public import StacksAndModuli.API.NodalCurveFiniteness
public import StacksAndModuli.API.PointSupportCohomology

/-!
# The point-supported node module of a nodal curve

For a nodal curve over an algebraically closed field, this file forms the finite direct
sum of the residue-field modules supported at its split nodes.  Its positive cohomology
vanishes and its degree-zero cohomology has dimension equal to the number of nodes.

This module is the expected model for the cokernel in the normalization sequence.  No
comparison with that cokernel is asserted here: such a comparison requires additional
normalization and completion results.

## Main definitions and results

* `AlgebraicGeometry.Scheme.IsNodalCurveOver.nodeResidueSupportModule`: one residue-field
  summand at every split node.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.subsingleton_H_nodeResidueSupportModule`:
  positive cohomology vanishes.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.finiteDimensional_H_nodeResidueSupportModule_zero`:
  degree-zero cohomology is finite dimensional.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.h_nodeResidueSupportModule_zero`: degree-zero
  cohomology counts the nodes.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The finite direct sum of canonical residue-field modules supported at all split nodes
of a nodal curve. -/
noncomputable def IsNodalCurveOver.nodeResidueSupportModule
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) : C.Modules :=
  let _ : Finite (C.SplitNodePoints k) := h.finite_splitNodePoints
  finiteResiduePointSupportModule C fun q : C.SplitNodePoints k ↦ q.1

/-- Every positive cohomology group of the residue-field module supported at all nodes is
trivial. -/
theorem IsNodalCurveOver.subsingleton_H_nodeResidueSupportModule
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) (n : ℕ) :
    Subsingleton (Modules.H h.nodeResidueSupportModule (n + 1)) := by
  let _ : Finite (C.SplitNodePoints k) := h.finite_splitNodePoints
  exact subsingleton_H_finiteResiduePointSupportModule C
    (fun q : C.SplitNodePoints k ↦ q.1) n

/-- Degree-zero cohomology of the residue-field module supported at all nodes is finite
dimensional. -/
theorem IsNodalCurveOver.finiteDimensional_H_nodeResidueSupportModule_zero
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    FiniteDimensional k (Modules.H h.nodeResidueSupportModule 0) := by
  let _ : Finite (C.SplitNodePoints k) := h.finite_splitNodePoints
  exact finiteDimensional_H_finiteResiduePointSupportModule_zero_of_isClosed
    (fun q : C.SplitNodePoints k ↦ q.1) h.isClosed_splitNodePoint

/-- Degree-zero cohomology of the residue-field module supported at all nodes has
dimension equal to the number of split nodes. -/
theorem IsNodalCurveOver.h_nodeResidueSupportModule_zero
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    Modules.h k h.nodeResidueSupportModule 0 =
      Nat.card (C.SplitNodePoints k) := by
  let _ : Finite (C.SplitNodePoints k) := h.finite_splitNodePoints
  let _ := Fintype.ofFinite (C.SplitNodePoints k)
  calc
    Modules.h k h.nodeResidueSupportModule 0 =
        Fintype.card (C.SplitNodePoints k) :=
      h_finiteResiduePointSupportModule_zero_of_isClosed
        (fun q : C.SplitNodePoints k ↦ q.1) h.isClosed_splitNodePoint
    _ = Nat.card (C.SplitNodePoints k) := by
      rw [Nat.card_eq_fintype_card]

end AlgebraicGeometry.Scheme
