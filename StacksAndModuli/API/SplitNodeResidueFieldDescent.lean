module

public import StacksAndModuli.API.SplitNodeResidueField
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Descent of residue-field properties from split nodes

Suppose that a point becomes a split node over an extension field `K`. The residue field of
the original point embeds into the residue field upstairs, which is `K`. Consequently,
finiteness and separability descend from `K` to the original residue field.

The final two theorems give this conclusion for the literal scheme-theoretic base change.
Together they formalize the residue-field consequence of condition (5) in the book's
characterization of nodes. They do not prove that the geometric definition of a node admits
such a finite separable splitting extension.

## Main results

* `AlgebraicGeometry.Scheme.residueField_finiteDimensional_of_lift_to_splitNode`;
* `AlgebraicGeometry.Scheme.residueField_isSeparable_of_lift_to_splitNode`;
* `AlgebraicGeometry.Scheme.
  residueField_finiteDimensional_of_splitNode_after_baseChange`;
* `AlgebraicGeometry.Scheme.residueField_isSeparable_of_splitNode_after_baseChange`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- If a point lifts compatibly to a split node over a finite field extension, then its
residue field is finite-dimensional over the original field. -/
theorem residueField_finiteDimensional_of_lift_to_splitNode
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ X) [Y.Over (Spec (CommRingCat.of K))]
    [IsLocallyNoetherian Y]
    (hcompat : g ≫ f = (Y ↘ Spec (CommRingCat.of K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (y : Y) (h : Y.IsSplitNodeAt K y) :
    letI := residueFieldAlgebra f (g y)
    FiniteDimensional k (X.residueField (g y)) := by
  let _ := residueFieldAlgebra f (g y)
  let _ := residueFieldAlgebra
    ((Y ↘ Spec (CommRingCat.of K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K))) y
  let map := g.residueFieldMapAlgHomOfCompEq f _ hcompat y
  let _ : FiniteDimensional k (Y.residueField y) :=
    h.residueField_finiteDimensional_restrictScalars
  exact residueField_finiteDimensional_of_algHom f (g y) map

/-- If a point lifts compatibly to a split node over a separable field extension, then its
residue field is separable over the original field. -/
theorem residueField_isSeparable_of_lift_to_splitNode
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (g : Y ⟶ X) [Y.Over (Spec (CommRingCat.of K))]
    [IsLocallyNoetherian Y]
    (hcompat : g ≫ f = (Y ↘ Spec (CommRingCat.of K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (y : Y) (h : Y.IsSplitNodeAt K y) :
    letI := residueFieldAlgebra f (g y)
    Algebra.IsSeparable k (X.residueField (g y)) := by
  let _ := residueFieldAlgebra f (g y)
  let _ := residueFieldAlgebra
    ((Y ↘ Spec (CommRingCat.of K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K))) y
  let map := g.residueFieldMapAlgHomOfCompEq f _ hcompat y
  let _ : Algebra.IsSeparable k (Y.residueField y) :=
    h.residueField_isSeparable_restrictScalars
  exact residueField_isSeparable_of_algHom f (g y) map

/-- If a point of a base change to a finite extension is a split node, then the residue
field of its image downstairs is finite-dimensional over the original field. -/
theorem residueField_finiteDimensional_of_splitNode_after_baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsLocallyNoetherian (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))]
    (y : (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).carrier)
    (h : letI : (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Over
          (Spec (CommRingCat.of K)) :=
        ⟨pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
      (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap k K)))).IsSplitNodeAt K y) :
    letI := residueFieldAlgebra f
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) y)
    FiniteDimensional k (X.residueField
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) y)) := by
  let _ : (pullback f
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Over
      (Spec (CommRingCat.of K)) :=
    ⟨pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
  exact residueField_finiteDimensional_of_lift_to_splitNode f
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    pullback.condition y h

/-- If a point of a base change to a separable extension is a split node, then the residue
field of its image downstairs is separable over the original field. -/
theorem residueField_isSeparable_of_splitNode_after_baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsLocallyNoetherian (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))]
    (y : (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).carrier)
    (h : letI : (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Over
          (Spec (CommRingCat.of K)) :=
        ⟨pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
      (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap k K)))).IsSplitNodeAt K y) :
    letI := residueFieldAlgebra f
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) y)
    Algebra.IsSeparable k (X.residueField
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) y)) := by
  let _ : (pullback f
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Over
      (Spec (CommRingCat.of K)) :=
    ⟨pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))⟩
  exact residueField_isSeparable_of_lift_to_splitNode f
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    pullback.condition y h

end AlgebraicGeometry.Scheme
