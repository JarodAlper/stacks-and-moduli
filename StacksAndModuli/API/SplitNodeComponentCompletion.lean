module

public import StacksAndModuli.API.ComponentNormalizationFromSmoothStalks
public import StacksAndModuli.API.NodeRingBranchTarget
public import StacksAndModuli.API.RegularStalkSmooth

/-!
# Completed component branches at split nodes

This file isolates the exact completed-local comparison needed to prove that a reduced
irreducible component is smooth at an ambient split node.  A completed local ring `B` is a
branch target of the ambient completed local ring when there is a surjective algebra map
to `B` whose kernel is a minimal prime.  A split-node chart and the formal-branch quotient
calculation then identify `B` with `k[[t]]`.

For an actual reduced component, the downstream API
`ReducedComponentCompletionBranch` constructs this map at every non-self split node.
Exactness of Noetherian adic completion computes its kernel, while flatness and uniqueness
of the incident formal branch identify the extended component-stalk prime with a minimal
prime of the reduced ambient completion.  Thus no excellence or reducedness theorem for
the completed component stalk is required.

## Main definitions

* `AlgebraicGeometry.Scheme.CompletedLocalBranchTargetOver`: the completed-local
  surjection with minimal-prime kernel expressing that the target is one formal branch.

## Main results

* `IsSplitNodeAt.nonempty_completedLocalBranchTargetAlgEquivPowerSeries`: every completed
  branch target
  at a split node is `k[[t]]`.
* `IsSplitNodeAt.formallySmooth_stalk_of_completedLocalBranchTarget`: a Noetherian domain
  stalk with
  such a completed branch presentation is formally smooth over an algebraically closed
  field.
* `IsSplitNodeAt.reducedComponent_formallySmooth_stalk_of_completedLocalBranchTarget`: the
  specialization to a reduced irreducible component.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory
open scoped PowerSeries

universe u

namespace AlgebraicGeometry.Scheme

/-- A completed local ring over `k` is a formal-branch target of another completed local
ring when it is the target of a surjective `k`-algebra map with minimal-prime kernel.

At a split node, this says exactly that the target is one of the two reduced formal
branches. -/
def CompletedLocalBranchTargetOver
    (k : Type u) [Field k] {C Y : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] (x : C) (y : Y) : Prop :=
  letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  letI := completedLocalRingAlgebra (Y ↘ Spec (CommRingCat.of k)) y
  ∃ f : C.completedLocalRing x →ₐ[k] Y.completedLocalRing y,
    Function.Surjective f ∧ RingHom.ker f ∈ minimalPrimes (C.completedLocalRing x)

/-- The defining criterion for a completed local branch target. -/
theorem completedLocalBranchTargetOver_iff
    (k : Type u) [Field k] {C Y : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] (x : C) (y : Y) :
    CompletedLocalBranchTargetOver k x y ↔
      letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
      letI := completedLocalRingAlgebra (Y ↘ Spec (CommRingCat.of k)) y
      ∃ f : C.completedLocalRing x →ₐ[k] Y.completedLocalRing y,
        Function.Surjective f ∧
          RingHom.ker f ∈ minimalPrimes (C.completedLocalRing x) :=
  Iff.rfl

/-- A completed formal-branch target at a split node is algebra-equivalent to the
one-variable power-series ring. -/
theorem IsSplitNodeAt.nonempty_completedLocalBranchTargetAlgEquivPowerSeries
    {k : Type u} [Field k] {C Y : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] {x : C}
    (h : C.IsSplitNodeAt k x) (y : Y)
    (htarget : CompletedLocalBranchTargetOver k x y) :
    letI := completedLocalRingAlgebra (Y ↘ Spec (CommRingCat.of k)) y
    Nonempty (Y.completedLocalRing y ≃ₐ[k] PowerSeries k) := by
  let _ := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  let _ := completedLocalRingAlgebra (Y ↘ Spec (CommRingCat.of k)) y
  change ∃ f : C.completedLocalRing x →ₐ[k] Y.completedLocalRing y,
    Function.Surjective f ∧
      RingHom.ker f ∈ minimalPrimes (C.completedLocalRing x) at htarget
  obtain ⟨f, hf, hker⟩ := htarget
  change Nonempty (C.completedLocalRing x ≃ₐ[k] nodeRing k) at h
  obtain ⟨e⟩ := h
  exact nonempty_nodeSurjectiveTargetAlgEquivPowerSeries_of_algEquiv
    k (C.completedLocalRing x) (Y.completedLocalRing y) e f hf hker

/-- A Noetherian domain stalk whose completion is one branch of an ambient split node is
formally smooth over an algebraically closed ground field. -/
theorem IsSplitNodeAt.formallySmooth_stalk_of_completedLocalBranchTarget
    {k : Type u} [Field k] [IsAlgClosed k] {C Y : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFinitePresentation (Y ↘ Spec (CommRingCat.of k))]
    {x : C} (h : C.IsSplitNodeAt k x) (y : Y)
    [IsNoetherianRing (Y.presheaf.stalk y)]
    [IsDomain (Y.presheaf.stalk y)]
    (htarget : CompletedLocalBranchTargetOver k x y) :
    ((Y ↘ Spec (CommRingCat.of k)).stalkMap y).hom.FormallySmooth := by
  let _ := completedLocalRingAlgebra (Y ↘ Spec (CommRingCat.of k)) y
  obtain ⟨e⟩ := h.nonempty_completedLocalBranchTargetAlgEquivPowerSeries y htarget
  exact formallySmooth_stalk_of_adicCompletion_equiv_powerSeries_toSpec_isAlgClosed
    (Y ↘ Spec (CommRingCat.of k)) y e.toRingEquiv

/-- A reduced irreducible component is formally smooth at a split node as soon as its
completed stalk is a formal-branch target of the ambient completed local ring. -/
theorem IsSplitNodeAt.reducedComponent_formallySmooth_stalk_of_completedLocalBranchTarget
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] [IsNoetherian C]
    [LocallyOfFinitePresentation (C ↘ Spec (CommRingCat.of k))]
    (Z : irreducibleComponents C) (z : C.reducedIrreducibleComponent Z)
    (h : C.IsSplitNodeAt k (C.reducedIrreducibleComponentι Z z))
    (htarget : CompletedLocalBranchTargetOver k
      (C.reducedIrreducibleComponentι Z z) z) :
    ((C.reducedIrreducibleComponent Z ↘
      Spec (CommRingCat.of k)).stalkMap z).hom.FormallySmooth := by
  let _ : LocallyOfFinitePresentation
      (C.reducedIrreducibleComponentι Z) := inferInstance
  let _ : LocallyOfFinitePresentation
      (C.reducedIrreducibleComponent Z ↘ Spec (CommRingCat.of k)) := by
    change LocallyOfFinitePresentation
      (C.reducedIrreducibleComponentι Z ≫
        (C ↘ Spec (CommRingCat.of k)))
    infer_instance
  exact h.formallySmooth_stalk_of_completedLocalBranchTarget z htarget

end AlgebraicGeometry.Scheme

end
