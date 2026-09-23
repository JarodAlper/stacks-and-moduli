module

public import StacksAndModuli.API.SheafCohomologyFiniteCoproduct
public import StacksAndModuli.API.IrreducibleComponentGeometricGenus
public import StacksAndModuli.API.NodalCurveGenusFormula
public import StacksAndModuli.API.NormalizationComponents
public import StacksAndModuli.API.NormalizationPushforwardCohomology
public import StacksAndModuli.API.SheafCohomologyPushforwardExact

/-!
# First cohomology of a normalization by components

For a reduced Noetherian scheme with finitely many irreducible components, its
normalization is the finite coproduct of the relative component normalizations.  This
file combines that decomposition with the finite-coproduct cohomology API and with the
comparison between a relative component normalization and the ordinary normalization of
the corresponding reduced component.

The finiteness of each component's first cohomology is an explicit hypothesis.  A general
proper-coherent-cohomology finiteness theorem is not yet available in the imported API.

## Main results

* `AlgebraicGeometry.Scheme.normalizationStructureCohomologyOneLinearEquiv`:
  first cohomology of the normalization is the product of first cohomologies of the
  normalized reduced irreducible components.
* `AlgebraicGeometry.Scheme.finiteDimensional_normalizationStructureCohomologyOne`:
  componentwise finite-dimensionality implies finite-dimensionality for the normalization.
* `finiteDimensional_reducedComponentNormalization_H_one_of_normalization`:
  finite-dimensionality of the normalization implies it for every component.
* `AlgebraicGeometry.Scheme.normalization_h_one_eq_sum_irreducibleComponentGeometricGenus`:
  the first-cohomology dimension of the normalization is the sum of component geometric
  genera.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationScheme_h_one_eq_sum_geometricGenusWeight`:
  the nodal-curve specialization.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.NormalizationPushforwardHOneComparison`:
  bijectivity of the canonical map needed to transfer the component computation to the
  normalization pushforward.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationPushforwardHOneComparison`:
  the canonical comparison, proved using a finite-discrete flasque resolution.
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.normalizationPushforwardHOneComparison_of_exact`:
  exactness of abelian-sheaf pushforward supplies that canonical comparison.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- First structure-sheaf cohomology of the normalization of a reduced Noetherian
scheme with finitely many irreducible components is the product of the first
cohomologies of the normalized reduced irreducible components. -/
noncomputable def normalizationStructureCohomologyOneLinearEquiv
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsReduced X] [IsNoetherian X]
    [Finite (irreducibleComponents X)] :
    letI : X.normalization.Over (Spec (CommRingCat.of k)) :=
      ⟨X.normalizationMap ≫ (X ↘ Spec (CommRingCat.of k))⟩
    Modules.H (structureModule X.normalization) 1 ≃ₗ[k]
      (∀ Z, Modules.H (structureModule
        (X.reducedIrreducibleComponentNormalization Z)) 1) := by
  let N := fun Z : irreducibleComponents X ↦
    X.relativeComponentNormalization Z
  letI : (∐ N : Scheme.{u}).Over (Spec (CommRingCat.of k)) :=
    sigmaOver N k
  letI : X.normalization.Over (Spec (CommRingCat.of k)) :=
    ⟨X.normalizationMap ≫ (X ↘ Spec (CommRingCat.of k))⟩
  exact ((structureCohomologyLinearEquivOfOverIso k
      X.relativeComponentNormalizationSigmaOverIso 1).symm.trans
    (structureCohomologySigmaOneLinearEquiv k N)).trans
      (LinearEquiv.piCongrRight fun Z ↦
        structureCohomologyLinearEquivOfOverIso k
          (X.relativeComponentNormalizationOverIsoReducedComponentNormalization Z) 1)

/-- If first structure-sheaf cohomology of a normalization is finite dimensional, then
the same holds for every normalized reduced irreducible component. -/
theorem finiteDimensional_reducedComponentNormalization_H_one_of_normalization
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsReduced X] [IsNoetherian X]
    [Finite (irreducibleComponents X)]
    (hfinite :
      letI : X.normalization.Over (Spec (CommRingCat.of k)) :=
        ⟨X.normalizationMap ≫ (X ↘ Spec (CommRingCat.of k))⟩
      FiniteDimensional k
        (Modules.H (structureModule X.normalization) 1))
    (Z : irreducibleComponents X) :
    FiniteDimensional k
      (Modules.H (structureModule
        (X.reducedIrreducibleComponentNormalization Z)) 1) := by
  letI : X.normalization.Over (Spec (CommRingCat.of k)) :=
    ⟨X.normalizationMap ≫ (X ↘ Spec (CommRingCat.of k))⟩
  let _ : FiniteDimensional k
      (Modules.H (structureModule X.normalization) 1) := hfinite
  let _ : FiniteDimensional k
      (∀ W, Modules.H (structureModule
        (X.reducedIrreducibleComponentNormalization W)) 1) :=
    Module.Finite.equiv
      (normalizationStructureCohomologyOneLinearEquiv k X)
  let projection :
      (∀ W, Modules.H (structureModule
        (X.reducedIrreducibleComponentNormalization W)) 1) →ₗ[k]
        Modules.H (structureModule
          (X.reducedIrreducibleComponentNormalization Z)) 1 :=
    LinearMap.proj Z
  exact Module.Finite.of_surjective projection
    (Function.surjective_eval Z)

/-- If the normalized reduced irreducible components have finite-dimensional first
cohomology, then so does the normalization of the ambient reduced Noetherian scheme. -/
theorem finiteDimensional_normalizationStructureCohomologyOne
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsReduced X] [IsNoetherian X]
    [Finite (irreducibleComponents X)]
    (hfinite : ∀ Z, FiniteDimensional k
      (Modules.H (structureModule
        (X.reducedIrreducibleComponentNormalization Z)) 1)) :
    letI : X.normalization.Over (Spec (CommRingCat.of k)) :=
      ⟨X.normalizationMap ≫ (X ↘ Spec (CommRingCat.of k))⟩
    FiniteDimensional k
      (Modules.H (structureModule X.normalization) 1) := by
  letI := Fintype.ofFinite (irreducibleComponents X)
  letI : ∀ Z, FiniteDimensional k
      (Modules.H (structureModule
        (X.reducedIrreducibleComponentNormalization Z)) 1) := hfinite
  letI : X.normalization.Over (Spec (CommRingCat.of k)) :=
    ⟨X.normalizationMap ≫ (X ↘ Spec (CommRingCat.of k))⟩
  exact Module.Finite.equiv
    (normalizationStructureCohomologyOneLinearEquiv k X).symm

/-- The first structure-sheaf cohomology dimension of the normalization is the sum of
the geometric genera of the irreducible components, provided those component
cohomologies are finite-dimensional. -/
theorem normalization_h_one_eq_sum_irreducibleComponentGeometricGenus
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsReduced X] [IsNoetherian X]
    [Finite (irreducibleComponents X)]
    (hfinite : ∀ Z, FiniteDimensional k
      (Modules.H (structureModule
        (X.reducedIrreducibleComponentNormalization Z)) 1)) :
    letI : X.normalization.Over (Spec (CommRingCat.of k)) :=
      ⟨X.normalizationMap ≫ (X ↘ Spec (CommRingCat.of k))⟩
    Modules.h k (structureModule X.normalization) 1 =
      letI := Fintype.ofFinite (irreducibleComponents X)
      ∑ Z, X.irreducibleComponentGeometricGenus k Z := by
  letI := Fintype.ofFinite (irreducibleComponents X)
  letI : ∀ Z, FiniteDimensional k
      (Modules.H (structureModule
        (X.reducedIrreducibleComponentNormalization Z)) 1) := hfinite
  letI : X.normalization.Over (Spec (CommRingCat.of k)) :=
    ⟨X.normalizationMap ≫ (X ↘ Spec (CommRingCat.of k))⟩
  let _ : FiniteDimensional k
      (Modules.H (structureModule X.normalization) 1) :=
    finiteDimensional_normalizationStructureCohomologyOne k X hfinite
  letI : ∀ Z, Module.Free k
      (Modules.H (structureModule
        (X.reducedIrreducibleComponentNormalization Z)) 1) := fun Z ↦ inferInstance
  exact (normalizationStructureCohomologyOneLinearEquiv k X).finrank_eq.trans
    (Module.finrank_pi_fintype k)

/-- Componentwise finite-dimensionality gives finite-dimensional first cohomology for
the normalization scheme of a nodal curve. -/
theorem IsNodalCurveOver.finiteDimensional_normalizationScheme_H_one
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    (hfinite :
      letI : IsNoetherian C := h.isNoetherian
      ∀ Z, FiniteDimensional k
        (Modules.H (structureModule
          (C.reducedIrreducibleComponentNormalization Z)) 1)) :
    FiniteDimensional k
      (Modules.H (structureModule h.normalizationScheme) 1) := by
  let _ : IsReduced C := h.isReduced
  let _ : IsNoetherian C := h.isNoetherian
  let _ : Finite (irreducibleComponents C) := inferInstance
  exact finiteDimensional_normalizationStructureCohomologyOne k C hfinite

/-- The first structure-sheaf cohomology dimension of a nodal curve's normalization
scheme is the sum of its irreducible-component geometric-genus weights, assuming the
component cohomologies are finite-dimensional. -/
theorem IsNodalCurveOver.normalizationScheme_h_one_eq_sum_geometricGenusWeight
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    (hfinite :
      letI : IsNoetherian C := h.isNoetherian
      ∀ Z, FiniteDimensional k
        (Modules.H (structureModule
          (C.reducedIrreducibleComponentNormalization Z)) 1)) :
    Modules.h k (structureModule h.normalizationScheme) 1 =
      letI : IsNoetherian C := h.isNoetherian
      letI := Fintype.ofFinite (irreducibleComponents C)
      ∑ Z, h.geometricGenusWeight Z := by
  let _ : IsReduced C := h.isReduced
  let _ : IsNoetherian C := h.isNoetherian
  let _ : Finite (irreducibleComponents C) := inferInstance
  exact normalization_h_one_eq_sum_irreducibleComponentGeometricGenus k C hfinite

/-- If first cohomology of a nodal curve's normalization scheme is finite dimensional,
its dimension is the sum of the irreducible-component geometric-genus weights. -/
theorem
    IsNodalCurveOver.normalizationScheme_h_one_eq_sum_geometricGenusWeight_of_finiteDimensional
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    (hfinite : FiniteDimensional k
      (Modules.H (structureModule h.normalizationScheme) 1)) :
    Modules.h k (structureModule h.normalizationScheme) 1 =
      letI : IsNoetherian C := h.isNoetherian
      letI := Fintype.ofFinite (irreducibleComponents C)
      ∑ Z, h.geometricGenusWeight Z := by
  let _ : IsReduced C := h.isReduced
  let _ : IsNoetherian C := h.isNoetherian
  let _ : Finite (irreducibleComponents C) := inferInstance
  let _ : Fintype (irreducibleComponents C) := Fintype.ofFinite _
  let _ : FiniteDimensional k
      (Modules.H (structureModule h.normalizationScheme) 1) := hfinite
  let hcomponent : ∀ Z, FiniteDimensional k
      (Modules.H (structureModule
        (C.reducedIrreducibleComponentNormalization Z)) 1) := fun Z ↦ by
    exact finiteDimensional_reducedComponentNormalization_H_one_of_normalization
      k C hfinite Z
  exact h.normalizationScheme_h_one_eq_sum_geometricGenusWeight hcomponent

/-- Bijectivity of the canonical first-cohomology map from a nodal curve's normalization
pushforward on the curve to the structure sheaf on the normalization scheme.

This property is isolated because it is the only pushforward-cohomology input not
supplied by the component decomposition. -/
abbrev IsNodalCurveOver.NormalizationPushforwardHOneComparison
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :=
  Function.Bijective
    (Modules.pushforwardCohomologyMap h.normalizationMap
      (structureModule h.normalizationScheme) 1)

/-- The canonical first-cohomology comparison for the normalization of a nodal
curve is bijective.

The proof resolves the normalization's structure sheaf using the finite
discrete scheme of component-generic points.  Affineness of the integral
normalization map makes pushforward preserve this quasicoherent resolution. -/
theorem IsNodalCurveOver.normalizationPushforwardHOneComparison
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C) :
    h.NormalizationPushforwardHOneComparison := by
  let _ : IsReduced C := h.isReduced
  let _ : IsNoetherian C := h.isNoetherian
  let _ : Finite (irreducibleComponents C) := inferInstance
  exact C.normalizationMap_pushforwardCohomologyMap_one_bijective

/-- Exactness of pushforward on abelian sheaves supplies the canonical first-cohomology
comparison for the normalization map.

This theorem does not assert that normalization pushforward is exact; it only consumes
an exactness instance supplied by the caller. -/
theorem IsNodalCurveOver.normalizationPushforwardHOneComparison_of_exact
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    [PreservesFiniteColimits
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.normalizationMap.base)] :
    h.NormalizationPushforwardHOneComparison :=
  Modules.pushforwardCohomologyMap_bijective_of_exact h.normalizationMap
    (structureModule h.normalizationScheme) 1

/-- The canonical first-cohomology map for normalization, upgraded to a linear
equivalence from a proof of bijectivity. -/
noncomputable def IsNodalCurveOver.normalizationPushforwardHOneLinearEquiv
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    (comparison : h.NormalizationPushforwardHOneComparison) :
    Modules.H h.normalizationPushforwardModule 1 ≃ₗ[k]
      Modules.H (structureModule h.normalizationScheme) 1 :=
  Modules.pushforwardCohomologyLinearEquivOfBijective
    h.normalizationMap k h.normalizationMap_over
      (structureModule h.normalizationScheme) 1 comparison

/-- Componentwise finite-dimensionality transfers to first cohomology of the
normalization pushforward once the pushforward comparison is supplied. -/
theorem IsNodalCurveOver.finiteDimensional_normalizationPushforward_H_one_of_comparison
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    (hfinite :
      letI : IsNoetherian C := h.isNoetherian
      ∀ Z, FiniteDimensional k
        (Modules.H (structureModule
          (C.reducedIrreducibleComponentNormalization Z)) 1))
    (comparison : h.NormalizationPushforwardHOneComparison) :
    FiniteDimensional k
      (Modules.H h.normalizationPushforwardModule 1) := by
  let _ : FiniteDimensional k
      (Modules.H (structureModule h.normalizationScheme) 1) :=
    h.finiteDimensional_normalizationScheme_H_one hfinite
  exact Module.Finite.equiv
    (h.normalizationPushforwardHOneLinearEquiv comparison).symm

/-- Componentwise finite-dimensionality transfers to first cohomology of the
normalization pushforward when its underlying abelian-sheaf pushforward is exact. -/
theorem IsNodalCurveOver.finiteDimensional_normalizationPushforward_H_one_of_exact
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    [PreservesFiniteColimits
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.normalizationMap.base)]
    (hfinite :
      letI : IsNoetherian C := h.isNoetherian
      ∀ Z, FiniteDimensional k
        (Modules.H (structureModule
          (C.reducedIrreducibleComponentNormalization Z)) 1)) :
    FiniteDimensional k
      (Modules.H h.normalizationPushforwardModule 1) :=
  h.finiteDimensional_normalizationPushforward_H_one_of_comparison hfinite
    h.normalizationPushforwardHOneComparison_of_exact

/-- Under the pushforward comparison, first cohomology of a nodal curve's normalization
pushforward has dimension equal to the sum of the component geometric genera. -/
theorem
    IsNodalCurveOver.normalizationPushforward_h_one_eq_sum_geometricGenusWeight_of_comparison
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    (hfinite :
      letI : IsNoetherian C := h.isNoetherian
      ∀ Z, FiniteDimensional k
        (Modules.H (structureModule
          (C.reducedIrreducibleComponentNormalization Z)) 1))
    (comparison : h.NormalizationPushforwardHOneComparison) :
    Modules.h k h.normalizationPushforwardModule 1 =
      letI : IsNoetherian C := h.isNoetherian
      letI := Fintype.ofFinite (irreducibleComponents C)
      ∑ Z, h.geometricGenusWeight Z := by
  exact (h.normalizationPushforwardHOneLinearEquiv comparison).finrank_eq.trans
    (h.normalizationScheme_h_one_eq_sum_geometricGenusWeight hfinite)

/-- Under exactness of abelian-sheaf pushforward, first cohomology of a nodal curve's
normalization pushforward has dimension equal to the sum of the component geometric
genera. -/
theorem
    IsNodalCurveOver.normalizationPushforward_h_one_eq_sum_geometricGenusWeight_of_exact
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    [C.Over (Spec (CommRingCat.of k))] (h : IsNodalCurveOver k C)
    [PreservesFiniteColimits
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.normalizationMap.base)]
    (hfinite :
      letI : IsNoetherian C := h.isNoetherian
      ∀ Z, FiniteDimensional k
        (Modules.H (structureModule
          (C.reducedIrreducibleComponentNormalization Z)) 1)) :
    Modules.h k h.normalizationPushforwardModule 1 =
      letI : IsNoetherian C := h.isNoetherian
      letI := Fintype.ofFinite (irreducibleComponents C)
      ∑ Z, h.geometricGenusWeight Z :=
  h.normalizationPushforward_h_one_eq_sum_geometricGenusWeight_of_comparison hfinite
    h.normalizationPushforwardHOneComparison_of_exact

end AlgebraicGeometry.Scheme

end
