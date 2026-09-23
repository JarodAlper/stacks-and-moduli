module

public import StacksAndModuli.API.NodeRingAxisSequence

/-!
# The coordinate-axis sequence at a split node

A chosen split-node chart transports the standard coordinate-axis embedding

`k[[x,y]]/(xy) ⟶ k[[x]] × k[[y]]`

to the completed local ring of the node.  The transported map is injective, its image is
the kernel of the difference of constant coefficients, and the resulting quotient defect
has dimension one over `k`.

The split-node predicate retains only the existence of a chart.  Accordingly, declarations
constructed directly from that predicate are explicitly named `chosen...`: their exactness
and defect dimension do not depend on the choice, but the maps themselves do.  Nothing here
identifies the product of the two formal axes with a stalk or fibre of the global
scheme-theoretic normalization.

## Main definitions

* `AlgebraicGeometry.Scheme.nodeAxisMapOfAlgEquiv`: transport of the standard axis map
  along a chosen algebra equivalence with the node ring.
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.chosenCompletedLocalNodeEquiv`: a chosen
  completed-local node chart supplied by the split-node property.
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.chosenCompletedLocalAxisMap`: the transported
  axis map on the completed local ring.
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.ChosenCompletedLocalAxisDefect`: the quotient by
  the image of that map.

## Main results

* `AlgebraicGeometry.Scheme.IsSplitNodeAt.chosenCompletedLocalAxisSequence_shortExact`:
  the transported axis sequence is short exact.
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.chosenCompletedLocalAxisDefect_finrank`: the
  transported defect has dimension one over the ground field.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped PowerSeries

universe u

namespace AlgebraicGeometry.Scheme

/-- Transport the standard node's coordinate-axis map along an algebra equivalence. -/
def nodeAxisMapOfAlgEquiv {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (e : A ≃ₐ[k] nodeRing k) :
    A →ₐ[k] PowerSeries k × PowerSeries k :=
  (nodeToAxes k).comp e.toAlgHom

/-- The transported axis map is the standard axis map after the chosen equivalence. -/
@[simp]
lemma nodeAxisMapOfAlgEquiv_apply {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] (e : A ≃ₐ[k] nodeRing k) (a : A) :
    nodeAxisMapOfAlgEquiv e a = nodeToAxes k (e a) :=
  rfl

/-- Transporting the standard node's axis map along an algebra equivalence preserves
injectivity. -/
theorem nodeAxisMapOfAlgEquiv_injective {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (e : A ≃ₐ[k] nodeRing k) :
    Function.Injective (nodeAxisMapOfAlgEquiv e) :=
  (nodeToAxes_injective k).comp e.injective

/-- The transported axis map is exact with the difference-of-constant-coefficients map. -/
theorem nodeAxisMapOfAlgEquiv_exact {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (e : A ≃ₐ[k] nodeRing k) :
    Function.Exact (nodeAxisMapOfAlgEquiv e).toLinearMap
      (nodeConstantDifference k) := by
  change Function.Exact
    ((nodeToAxes k).toLinearMap ∘ₗ e.toLinearEquiv.toLinearMap)
      (nodeConstantDifference k)
  rw [LinearEquiv.precomp_exact_iff_exact]
  exact nodeToAxes_exact k

/-- The image of a transported axis map is the kernel of the difference of constant
coefficients. -/
theorem nodeAxisMapOfAlgEquiv_range_eq_ker {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (e : A ≃ₐ[k] nodeRing k) :
    LinearMap.range (nodeAxisMapOfAlgEquiv e).toLinearMap =
      LinearMap.ker (nodeConstantDifference k) :=
  (nodeAxisMapOfAlgEquiv_exact e).linearMap_ker_eq.symm

/-- Transporting the node's axis embedding along an algebra equivalence yields a short
exact sequence. -/
theorem nodeAxisSequenceOfAlgEquiv_shortExact {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (e : A ≃ₐ[k] nodeRing k) :
    Function.Injective (nodeAxisMapOfAlgEquiv e) ∧
      Function.Exact (nodeAxisMapOfAlgEquiv e).toLinearMap
        (nodeConstantDifference k) ∧
      Function.Surjective (nodeConstantDifference k) :=
  ⟨nodeAxisMapOfAlgEquiv_injective e, nodeAxisMapOfAlgEquiv_exact e,
    nodeConstantDifference_surjective k⟩

/-- The coordinate-axis defect of an algebra identified with the standard node ring. -/
abbrev nodeAxisDefectOfAlgEquiv {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] (e : A ≃ₐ[k] nodeRing k) : Type u :=
  (PowerSeries k × PowerSeries k) ⧸
    LinearMap.range (nodeAxisMapOfAlgEquiv e).toLinearMap

/-- The coordinate-axis defect transported along an algebra equivalence is linearly
equivalent to the coefficient field. -/
def nodeAxisDefectLinearEquivOfAlgEquiv {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (e : A ≃ₐ[k] nodeRing k) :
    nodeAxisDefectOfAlgEquiv e ≃ₗ[k] k :=
  (Submodule.quotEquivOfEq _ _
      (nodeAxisMapOfAlgEquiv_range_eq_ker e)).trans
    ((nodeConstantDifference k).quotKerEquivOfSurjective
      (nodeConstantDifference_surjective k))

/-- On a quotient class, the transported defect equivalence is the difference of constant
coefficients. -/
@[simp]
lemma nodeAxisDefectLinearEquivOfAlgEquiv_mk {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (e : A ≃ₐ[k] nodeRing k)
    (p : PowerSeries k × PowerSeries k) :
    nodeAxisDefectLinearEquivOfAlgEquiv e (Submodule.Quotient.mk p) =
      nodeConstantDifference k p := by
  simp [nodeAxisDefectLinearEquivOfAlgEquiv]

/-- The coordinate-axis defect transported along an algebra equivalence has dimension one
over the coefficient field. -/
theorem nodeAxisDefectOfAlgEquiv_finrank {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (e : A ≃ₐ[k] nodeRing k) :
    Module.finrank k (nodeAxisDefectOfAlgEquiv e) = 1 := by
  rw [LinearEquiv.finrank_eq (nodeAxisDefectLinearEquivOfAlgEquiv e)]
  exact CommSemiring.finrank_self k

/-- A noncomputably chosen split-node coordinate chart on the completed local ring. -/
noncomputable def IsSplitNodeAt.chosenCompletedLocalNodeEquiv
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    C.completedLocalRing x ≃ₐ[k] nodeRing k := by
  letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  change Nonempty (C.completedLocalRing x ≃ₐ[k] nodeRing k) at h
  exact Classical.choice h

/-- The coordinate-axis map on the completed local ring, formed using a noncomputably
chosen split-node chart. -/
noncomputable def IsSplitNodeAt.chosenCompletedLocalAxisMap
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    C.completedLocalRing x →ₐ[k] PowerSeries k × PowerSeries k := by
  letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  exact nodeAxisMapOfAlgEquiv h.chosenCompletedLocalNodeEquiv

/-- The chosen completed-local axis map is the standard one after the chosen node chart. -/
@[simp]
lemma IsSplitNodeAt.chosenCompletedLocalAxisMap_apply
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x)
    (a : C.completedLocalRing x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    h.chosenCompletedLocalAxisMap a =
      nodeToAxes k (h.chosenCompletedLocalNodeEquiv a) := by
  let _ := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  rfl

/-- The chosen completed-local axis map at a split node is injective. -/
theorem IsSplitNodeAt.chosenCompletedLocalAxisMap_injective
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    Function.Injective h.chosenCompletedLocalAxisMap := by
  let _ := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  exact nodeAxisMapOfAlgEquiv_injective h.chosenCompletedLocalNodeEquiv

/-- The chosen completed-local axis map at a split node is exact with the difference of
constant coefficients. -/
theorem IsSplitNodeAt.chosenCompletedLocalAxisMap_exact
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    Function.Exact h.chosenCompletedLocalAxisMap.toLinearMap
      (nodeConstantDifference k) := by
  let _ := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  exact nodeAxisMapOfAlgEquiv_exact h.chosenCompletedLocalNodeEquiv

/-- The image of the chosen completed-local axis map is the kernel of the difference of
constant coefficients. -/
theorem IsSplitNodeAt.chosenCompletedLocalAxisMap_range_eq_ker
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    LinearMap.range h.chosenCompletedLocalAxisMap.toLinearMap =
      LinearMap.ker (nodeConstantDifference k) := by
  let _ := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  exact nodeAxisMapOfAlgEquiv_range_eq_ker h.chosenCompletedLocalNodeEquiv

/-- A chosen split-node chart transports the standard coordinate-axis short exact
sequence to the completed local ring. -/
theorem IsSplitNodeAt.chosenCompletedLocalAxisSequence_shortExact
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    Function.Injective h.chosenCompletedLocalAxisMap ∧
      Function.Exact h.chosenCompletedLocalAxisMap.toLinearMap
        (nodeConstantDifference k) ∧
      Function.Surjective (nodeConstantDifference k) := by
  let _ := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  exact nodeAxisSequenceOfAlgEquiv_shortExact h.chosenCompletedLocalNodeEquiv

/-- The coordinate-axis quotient defect of the completed local ring, formed using a
chosen split-node chart. -/
abbrev IsSplitNodeAt.ChosenCompletedLocalAxisDefect
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) : Type u :=
  letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  nodeAxisDefectOfAlgEquiv h.chosenCompletedLocalNodeEquiv

/-- The chosen coordinate-axis defect of a split node is linearly equivalent to the
ground field. -/
noncomputable def IsSplitNodeAt.chosenCompletedLocalAxisDefectLinearEquiv
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    h.ChosenCompletedLocalAxisDefect ≃ₗ[k] k := by
  letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  exact nodeAxisDefectLinearEquivOfAlgEquiv h.chosenCompletedLocalNodeEquiv

/-- On a quotient class, the chosen completed-local defect equivalence is the difference
of constant coefficients. -/
@[simp]
lemma IsSplitNodeAt.chosenCompletedLocalAxisDefectLinearEquiv_mk
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x)
    (p : PowerSeries k × PowerSeries k) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    h.chosenCompletedLocalAxisDefectLinearEquiv (Submodule.Quotient.mk p) =
      nodeConstantDifference k p := by
  let _ := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  exact nodeAxisDefectLinearEquivOfAlgEquiv_mk h.chosenCompletedLocalNodeEquiv p

/-- The chosen coordinate-axis quotient defect at a split node has dimension one over the
ground field. -/
theorem IsSplitNodeAt.chosenCompletedLocalAxisDefect_finrank
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    Module.finrank k h.ChosenCompletedLocalAxisDefect = 1 := by
  let _ := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  exact nodeAxisDefectOfAlgEquiv_finrank h.chosenCompletedLocalNodeEquiv

end AlgebraicGeometry.Scheme
