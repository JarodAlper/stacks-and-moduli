module

public import StacksAndModuli.API.IntegralSchemeNormalization
public import StacksAndModuli.API.NodalCurveNormalization
public import StacksAndModuli.API.ReducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Geometric genera of irreducible components

This file realizes an irreducible component as a reduced closed subscheme, normalizes it,
and defines its geometric genus over a field.  These constructions supply the vertex-weight
function needed for the dual graph of a nodal curve.

Mathlib's `AlgebraicGeometry.Scheme.irreducibleComponent` deliberately retains the
scheme-theoretic multiplicity of a component.  Geometric genus instead uses the reduced
induced structure.  Here that structure is the subscheme cut out by the vanishing ideal of
the component's underlying closed set.  Its reducedness follows affine-locally because a
vanishing ideal is radical.

The component normalization uses `AlgebraicGeometry.Scheme.normalization` from
`StacksAndModuli/API/ReducedSchemeNormalization.lean`.  Its inherited morphism to the ambient
scheme supplies the base-field structure used by `genusOver`.

## Main definitions

* `AlgebraicGeometry.Scheme.reducedIrreducibleComponent`: the reduced induced closed
  subscheme on an irreducible component.
* `AlgebraicGeometry.Scheme.reducedIrreducibleComponentNormalization`: its normalization.
* `AlgebraicGeometry.Scheme.irreducibleComponentGeometricGenus`: the genus of that
  normalization over a field.
* `AlgebraicGeometry.Scheme.irreducibleComponentGeometricGenusWeight`: the resulting
  function from irreducible components to natural numbers.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.geometricGenusWeight`: the specialization to
  a nodal curve, with Noetherianity supplied by the nodality witness.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal`: the reduced
  induced closed subscheme is reduced.
* `AlgebraicGeometry.Scheme.range_reducedIrreducibleComponentι`: its underlying image is
  exactly the chosen component.
* `AlgebraicGeometry.Scheme.irreducibleComponentGeometricGenus_eq_genus`: over an
  algebraically closed field, the weight agrees with intrinsic genus whenever integrality
  of the normalization is available.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The closed set underlying an irreducible component. -/
def irreducibleComponentClosed (X : Scheme.{u})
    (Z : irreducibleComponents X) : Closeds X :=
  ⟨Z.1, isClosed_of_mem_irreducibleComponents Z.1 Z.2⟩

/-- An irreducible component with its reduced induced closed-subscheme structure. -/
noncomputable def reducedIrreducibleComponent (X : Scheme.{u})
    (Z : irreducibleComponents X) : Scheme.{u} :=
  (IdealSheafData.vanishingIdeal (X.irreducibleComponentClosed Z)).subscheme

/-- The closed immersion of the reduced induced irreducible component. -/
noncomputable def reducedIrreducibleComponentι (X : Scheme.{u})
    (Z : irreducibleComponents X) : X.reducedIrreducibleComponent Z ⟶ X :=
  (IdealSheafData.vanishingIdeal (X.irreducibleComponentClosed Z)).subschemeι

/-- The reduced component inclusion is the subtype inclusion on points. -/
@[simp]
theorem reducedIrreducibleComponentι_apply (X : Scheme.{u})
    (Z : irreducibleComponents X) (x : X.reducedIrreducibleComponent Z) :
    X.reducedIrreducibleComponentι Z x = x.1 :=
  rfl

/-- The image of the reduced component inclusion is exactly the chosen irreducible
component. -/
@[simp]
theorem range_reducedIrreducibleComponentι (X : Scheme.{u})
    (Z : irreducibleComponents X) :
    Set.range (X.reducedIrreducibleComponentι Z) = Z.1 := by
  exact (IdealSheafData.range_subschemeι
    (IdealSheafData.vanishingIdeal (X.irreducibleComponentClosed Z))).trans rfl

/-- The inclusion of a reduced irreducible component is a closed immersion. -/
instance reducedIrreducibleComponentι_isClosedImmersion (X : Scheme.{u})
    (Z : irreducibleComponents X) :
    IsClosedImmersion (X.reducedIrreducibleComponentι Z) := by
  dsimp only [reducedIrreducibleComponentι]
  infer_instance

/-- The reduced induced structure on an irreducible component is reduced. -/
noncomputable instance reducedIrreducibleComponent_isReduced (X : Scheme.{u})
    (Z : irreducibleComponents X) :
    IsReduced (X.reducedIrreducibleComponent Z) :=
  IdealSheafData.isReduced_subscheme_vanishingIdeal
    (X.irreducibleComponentClosed Z)

/-- The reduced induced structure on an irreducible component is irreducible. -/
instance reducedIrreducibleComponent_irreducibleSpace (X : Scheme.{u})
    (Z : irreducibleComponents X) :
    IrreducibleSpace (X.reducedIrreducibleComponent Z) :=
  Subtype.irreducibleSpace Z.2.1

/-- The reduced induced structure on an irreducible component is integral. -/
noncomputable instance reducedIrreducibleComponent_isIntegral (X : Scheme.{u})
    (Z : irreducibleComponents X) :
    IsIntegral (X.reducedIrreducibleComponent Z) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- A reduced irreducible component of a Noetherian scheme is Noetherian. -/
noncomputable instance reducedIrreducibleComponent_isNoetherian
    (X : Scheme.{u}) [IsNoetherian X] (Z : irreducibleComponents X) :
    IsNoetherian (X.reducedIrreducibleComponent Z) := by
  let _ : IsLocallyNoetherian (X.reducedIrreducibleComponent Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (X.reducedIrreducibleComponentι Z)
  let _ : CompactSpace (X.reducedIrreducibleComponent Z) :=
    QuasiCompact.compactSpace_of_compactSpace (X.reducedIrreducibleComponentι Z)
  exact IsNoetherian.mk

/-- The normalization of the reduced induced structure on an irreducible component. -/
noncomputable abbrev reducedIrreducibleComponentNormalization
    (X : Scheme.{u}) [IsNoetherian X] (Z : irreducibleComponents X) : Scheme.{u} :=
  (X.reducedIrreducibleComponent Z).normalization

/-- The normalization map of a reduced irreducible component, followed by its inclusion
into the ambient scheme. -/
noncomputable def reducedIrreducibleComponentNormalizationι
    (X : Scheme.{u}) [IsNoetherian X] (Z : irreducibleComponents X) :
    X.reducedIrreducibleComponentNormalization Z ⟶ X :=
  (X.reducedIrreducibleComponent Z).normalizationMap ≫
    X.reducedIrreducibleComponentι Z

/-- The normalization of a reduced irreducible component inherits every specified map from
the ambient scheme. -/
noncomputable instance reducedIrreducibleComponentNormalization_over
    {S X : Scheme.{u}} [X.Over S] [IsNoetherian X]
    (Z : irreducibleComponents X) :
    (X.reducedIrreducibleComponentNormalization Z).Over S :=
  ⟨X.reducedIrreducibleComponentNormalizationι Z ≫ (X ↘ S)⟩

/-- If the ambient structure map is universally closed, so is the inherited structure map
on the normalization of every reduced irreducible component. -/
noncomputable instance reducedIrreducibleComponentNormalization_universallyClosed
    {S X : Scheme.{u}} [X.Over S] [IsNoetherian X]
    [UniversallyClosed (X ↘ S)] (Z : irreducibleComponents X) :
    UniversallyClosed
      (X.reducedIrreducibleComponentNormalization Z ↘ S) := by
  change UniversallyClosed
    ((X.reducedIrreducibleComponent Z).normalizationMap ≫
      X.reducedIrreducibleComponentι Z ≫ (X ↘ S))
  infer_instance

/-- The geometric genus of an irreducible component: the genus over `k` of the
normalization of its reduced induced closed-subscheme structure. -/
noncomputable def irreducibleComponentGeometricGenus
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsNoetherian X]
    (Z : irreducibleComponents X) : ℕ :=
  genusOver k (X.reducedIrreducibleComponentNormalization Z)

/-- Over an algebraically closed field, the geometric-genus weight agrees with the
intrinsic genus of the component normalization. -/
theorem irreducibleComponentGeometricGenus_eq_genus
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsNoetherian X]
    [UniversallyClosed (X ↘ Spec (CommRingCat.of k))]
    (Z : irreducibleComponents X) :
    X.irreducibleComponentGeometricGenus k Z =
      (X.reducedIrreducibleComponentNormalization Z).genus :=
  genusOver_eq_genus_of_isAlgClosed k _

/-- The geometric-genus vertex weights of a Noetherian scheme over a field. -/
noncomputable def irreducibleComponentGeometricGenusWeight
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsNoetherian X] :
    irreducibleComponents X → ℕ :=
  X.irreducibleComponentGeometricGenus k

/-- Evaluating the geometric-genus weight function returns the geometric genus of that
component. -/
@[simp]
theorem irreducibleComponentGeometricGenusWeight_apply
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsNoetherian X]
    (Z : irreducibleComponents X) :
    X.irreducibleComponentGeometricGenusWeight k Z =
      X.irreducibleComponentGeometricGenus k Z :=
  rfl

/-- The geometric-genus weight function on the components of a nodal curve. -/
noncomputable def IsNodalCurveOver.geometricGenusWeight
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    irreducibleComponents C → ℕ :=
  letI := h.isNoetherian
  C.irreducibleComponentGeometricGenusWeight k

end AlgebraicGeometry.Scheme
