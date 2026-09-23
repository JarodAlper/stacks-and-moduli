module

public import StacksAndModuli.API.NodeRingNormalization
public import StacksAndModuli.API.SplitNodeAxisSequence

/-!
# Normalization of a completed local ring at a split node

A chosen split-node chart identifies the completed local ring with the standard node ring.
This file transports the standard node's normalization and total quotient ring along that
chart.  Thus the product of the two formal branch rings is the integral closure of the
completed local ring in the product of the branch fraction fields.

As in `SplitNodeAxisSequence`, constructions depending on the noncomputably chosen chart
are named `chosen...`.  The underlying branch fraction ring is always

`Frac(k[[x]]) × Frac(k[[y]])`,

while its algebra structure over the completed local ring records the chart.

## Main results

* `IsIntegralClosure.of_ringEquiv_left`: transport an integral-closure predicate along a
  ring equivalence of the base rings.
* `AlgebraicGeometry.Scheme.nodeAxes_isIntegralClosure_of_algEquiv`: transport the
  standard node normalization along an algebra equivalence.
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.chosenCompletedLocalAxes_isIntegralClosure`:
  the branch rings are the integral closure of the completed local ring at a split node.
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.chosenCompletedLocalBranchFractions_isFractionRing`:
  the branch fraction product is its total quotient ring.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped PowerSeries

universe u

/-- Transport an integral-closure predicate along an equivalence of the base rings whose
maps into the ambient ring agree. -/
theorem IsIntegralClosure.of_ringEquiv_left
    {R S A B : Type*} [CommRing R] [CommRing S] [CommSemiring A] [CommRing B]
    [Algebra R B] [Algebra S B] [Algebra A B]
    (e : R ≃+* S)
    (h : ∀ x, algebraMap R B x = algebraMap S B (e x))
    [IsIntegralClosure A S B] : IsIntegralClosure A R B := by
  refine ⟨IsIntegralClosure.algebraMap_injective A S B, ?_⟩
  intro x
  have he : (algebraMap S B).comp e.toRingHom = algebraMap R B := by
    ext r
    exact (h r).symm
  exact (e.isIntegral_iff he x).trans IsIntegralClosure.isIntegral_iff

namespace AlgebraicGeometry.Scheme

/-- Transport the standard node's map to its branch fraction fields along an algebra
equivalence. -/
def nodeToBranchFractionsOfAlgEquiv {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (e : A ≃ₐ[k] nodeRing k) :
    A →+* nodeBranchFractionRing k :=
  (nodeToBranchFractions k).comp e.toRingEquiv.toRingHom

/-- The transported branch-fraction map is the standard map after the chosen equivalence. -/
@[simp]
lemma nodeToBranchFractionsOfAlgEquiv_apply {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (e : A ≃ₐ[k] nodeRing k) (a : A) :
    nodeToBranchFractionsOfAlgEquiv e a = nodeToBranchFractions k (e a) :=
  rfl

/-- The algebra structure on the axes product transported from an algebra equivalence with
the standard node. -/
noncomputable abbrev nodeAxesAlgebraOfAlgEquiv {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (e : A ≃ₐ[k] nodeRing k) :
    Algebra A (PowerSeries k × PowerSeries k) :=
  (nodeAxisMapOfAlgEquiv e).toRingHom.toAlgebra

/-- The algebra map for `nodeAxesAlgebraOfAlgEquiv` is the transported axis map. -/
@[simp]
lemma algebraMap_nodeAxesAlgebraOfAlgEquiv {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (e : A ≃ₐ[k] nodeRing k) (a : A) :
    @algebraMap A (PowerSeries k × PowerSeries k) _ _
        (nodeAxesAlgebraOfAlgEquiv e) a = nodeAxisMapOfAlgEquiv e a :=
  rfl

/-- The algebra structure on the branch fraction product transported from an algebra
equivalence with the standard node. -/
noncomputable abbrev nodeBranchFractionsAlgebraOfAlgEquiv
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (e : A ≃ₐ[k] nodeRing k) : Algebra A (nodeBranchFractionRing k) :=
  (nodeToBranchFractionsOfAlgEquiv e).toAlgebra

/-- The algebra map for `nodeBranchFractionsAlgebraOfAlgEquiv` is the transported
branch-fraction map. -/
@[simp]
lemma algebraMap_nodeBranchFractionsAlgebraOfAlgEquiv
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (e : A ≃ₐ[k] nodeRing k) (a : A) :
    @algebraMap A (nodeBranchFractionRing k) _ _
        (nodeBranchFractionsAlgebraOfAlgEquiv e) a =
      nodeToBranchFractionsOfAlgEquiv e a :=
  rfl

/-- The transported coordinate-axis map is integral. -/
theorem nodeAxisMapOfAlgEquiv_isIntegral {k A : Type u} [Field k]
    [CommRing A] [Algebra k A] (e : A ≃ₐ[k] nodeRing k) :
    (nodeAxisMapOfAlgEquiv e).toRingHom.IsIntegral :=
  RingHom.IsIntegral.trans e.toRingEquiv.toRingHom (nodeToAxes k).toRingHom
    (e.toRingEquiv.toRingHom.isIntegral_of_surjective e.surjective)
    (nodeToAxes_isIntegral k)

/-- The axes product is integral for the algebra structure transported along the chosen
equivalence. -/
theorem nodeAxes_isIntegral_of_algEquiv
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (e : A ≃ₐ[k] nodeRing k) :
    let _ : Algebra A (PowerSeries k × PowerSeries k) :=
      nodeAxesAlgebraOfAlgEquiv e
    Algebra.IsIntegral A (PowerSeries k × PowerSeries k) := by
  dsimp only
  let _ : Algebra A (PowerSeries k × PowerSeries k) :=
    nodeAxesAlgebraOfAlgEquiv e
  exact ⟨nodeAxisMapOfAlgEquiv_isIntegral e⟩

/-- The product of branch fraction fields is the total quotient ring after transport along
an algebra equivalence with the standard node. -/
theorem nodeBranchFractions_isFractionRing_of_algEquiv
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (e : A ≃ₐ[k] nodeRing k) :
    let _ : Algebra A (nodeBranchFractionRing k) :=
      nodeBranchFractionsAlgebraOfAlgEquiv e
    IsFractionRing A (nodeBranchFractionRing k) := by
  dsimp only
  let _ : Algebra A (nodeBranchFractionRing k) :=
    nodeBranchFractionsAlgebraOfAlgEquiv e
  exact IsFractionRing.of_ringEquiv_left e.toRingEquiv (fun _ ↦ rfl)

/-- The axes product is the integral closure after transport along an algebra equivalence
with the standard node. -/
theorem nodeAxes_isIntegralClosure_of_algEquiv
    {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    (e : A ≃ₐ[k] nodeRing k) :
    let _ : Algebra A (nodeBranchFractionRing k) :=
      nodeBranchFractionsAlgebraOfAlgEquiv e
    IsIntegralClosure (PowerSeries k × PowerSeries k) A
      (nodeBranchFractionRing k) := by
  dsimp only
  let _ : Algebra A (nodeBranchFractionRing k) :=
    nodeBranchFractionsAlgebraOfAlgEquiv e
  exact IsIntegralClosure.of_ringEquiv_left e.toRingEquiv (fun _ ↦ rfl)

/-- The chosen product of the two branch fraction fields at a split node.  The underlying
ring is independent of the chart; its algebra structure below records the chart. -/
abbrev IsSplitNodeAt.ChosenCompletedLocalBranchFractionRing
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (_h : C.IsSplitNodeAt k x) :=
  nodeBranchFractionRing k

/-- The map from the completed local ring at a split node to the branch fraction product,
formed using a noncomputably chosen split-node chart. -/
noncomputable def IsSplitNodeAt.chosenCompletedLocalToBranchFractions
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    C.completedLocalRing x →+* h.ChosenCompletedLocalBranchFractionRing := by
  letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  exact nodeToBranchFractionsOfAlgEquiv h.chosenCompletedLocalNodeEquiv

/-- The chosen completed-local branch-fraction map is the standard map after the chosen
node chart. -/
@[simp]
lemma IsSplitNodeAt.chosenCompletedLocalToBranchFractions_apply
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x)
    (a : C.completedLocalRing x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    h.chosenCompletedLocalToBranchFractions a =
      nodeToBranchFractions k (h.chosenCompletedLocalNodeEquiv a) := by
  let _ := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  rfl

/-- The algebra structure on the chosen branch fraction product induced by the completed
local ring and the chosen split-node chart. -/
noncomputable abbrev IsSplitNodeAt.chosenCompletedLocalBranchFractionsAlgebra
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    Algebra (C.completedLocalRing x) h.ChosenCompletedLocalBranchFractionRing := by
  letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  exact nodeBranchFractionsAlgebraOfAlgEquiv h.chosenCompletedLocalNodeEquiv

/-- The algebra structure on the axes product induced by the completed local ring and the
chosen split-node chart. -/
noncomputable abbrev IsSplitNodeAt.chosenCompletedLocalAxesAlgebra
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    Algebra (C.completedLocalRing x) (PowerSeries k × PowerSeries k) := by
  letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  exact nodeAxesAlgebraOfAlgEquiv h.chosenCompletedLocalNodeEquiv

/-- The chosen completed-local axis map is integral. -/
theorem IsSplitNodeAt.chosenCompletedLocalAxisMap_isIntegral
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    h.chosenCompletedLocalAxisMap.toRingHom.IsIntegral := by
  let _ := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  exact nodeAxisMapOfAlgEquiv_isIntegral h.chosenCompletedLocalNodeEquiv

/-- The chosen branch fraction product is the total quotient ring of the completed local
ring at a split node. -/
theorem IsSplitNodeAt.chosenCompletedLocalBranchFractions_isFractionRing
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    letI : Algebra (C.completedLocalRing x)
        h.ChosenCompletedLocalBranchFractionRing :=
      h.chosenCompletedLocalBranchFractionsAlgebra
    IsFractionRing (C.completedLocalRing x)
      h.ChosenCompletedLocalBranchFractionRing := by
  let _ := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  let _ : Algebra (C.completedLocalRing x)
      h.ChosenCompletedLocalBranchFractionRing :=
    h.chosenCompletedLocalBranchFractionsAlgebra
  exact nodeBranchFractions_isFractionRing_of_algEquiv
    h.chosenCompletedLocalNodeEquiv

/-- The axes product is integral over the completed local ring for the algebra structure
induced by the chosen split-node chart. -/
theorem IsSplitNodeAt.chosenCompletedLocalAxes_isIntegral
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    letI : Algebra (C.completedLocalRing x) (PowerSeries k × PowerSeries k) :=
      h.chosenCompletedLocalAxesAlgebra
    Algebra.IsIntegral (C.completedLocalRing x)
      (PowerSeries k × PowerSeries k) := by
  let _ := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  let _ : Algebra (C.completedLocalRing x) (PowerSeries k × PowerSeries k) :=
    h.chosenCompletedLocalAxesAlgebra
  exact ⟨h.chosenCompletedLocalAxisMap_isIntegral⟩

/-- The product of the two formal branch rings is the integral closure of the completed
local ring at a split node in its chosen branch fraction product. -/
theorem IsSplitNodeAt.chosenCompletedLocalAxes_isIntegralClosure
    {k : Type u} [Field k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] {x : C} (h : C.IsSplitNodeAt k x) :
    letI := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
    letI : Algebra (C.completedLocalRing x)
        h.ChosenCompletedLocalBranchFractionRing :=
      h.chosenCompletedLocalBranchFractionsAlgebra
    IsIntegralClosure (PowerSeries k × PowerSeries k)
      (C.completedLocalRing x) h.ChosenCompletedLocalBranchFractionRing := by
  let _ := completedLocalRingAlgebra (C ↘ Spec (CommRingCat.of k)) x
  let _ : Algebra (C.completedLocalRing x)
      h.ChosenCompletedLocalBranchFractionRing :=
    h.chosenCompletedLocalBranchFractionsAlgebra
  exact nodeAxes_isIntegralClosure_of_algEquiv h.chosenCompletedLocalNodeEquiv

end AlgebraicGeometry.Scheme
