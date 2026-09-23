module

public import StacksAndModuli.API.CompletedLocalRingResidueField
public import StacksAndModuli.«Section6.2-Nodal».«part6.2.1-nodes»
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# Residue fields of split nodes

The residue field of the standard split-node ring `k[[x,y]]/(xy)` is canonically `k`.
Completion preserves residue fields, so the same is true at every split node over `k`.
In particular, its residue field has degree one and is finite and separable over `k`.

## Main definitions and results

* `AlgebraicGeometry.Scheme.nodeRingConstantCoeff`;
* `AlgebraicGeometry.Scheme.nodeRingResidueFieldAlgEquiv`;
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.residueFieldAlgEquiv`;
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.residueFieldAlgEquiv_restrictScalars`;
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.residueField_finiteDimensional`;
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.residueField_isSeparable`;
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.algebraMap_residueField_bijective`;
* `AlgebraicGeometry.Scheme.IsSplitNodeAt.finrank_residueField_eq_one`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- Constant coefficient descends from the two-variable power series ring to the standard
split-node ring. -/
noncomputable def nodeRingConstantCoeff (k : Type u) [Field k] : nodeRing k →+* k :=
  Ideal.Quotient.lift (nodeIdeal k)
    (MvPowerSeries.constantCoeff (σ := Fin 2) (R := k)) (by
      intro f hf
      rw [nodeIdeal, Ideal.mem_span_singleton] at hf
      obtain ⟨f, rfl⟩ := hf
      simp)

/-- Constant coefficient on the class of a power series is its constant coefficient. -/
@[simp]
theorem nodeRingConstantCoeff_mk (k : Type u) [Field k]
    (f : MvPowerSeries (Fin 2) k) :
    nodeRingConstantCoeff k (Ideal.Quotient.mk (nodeIdeal k) f) =
      MvPowerSeries.constantCoeff f :=
  rfl

/-- Constant coefficient on the standard split-node ring is surjective. -/
theorem nodeRingConstantCoeff_surjective (k : Type u) [Field k] :
    Function.Surjective (nodeRingConstantCoeff k) := by
  intro a
  refine ⟨Ideal.Quotient.mk (nodeIdeal k) (MvPowerSeries.C (σ := Fin 2) a), ?_⟩
  simp [nodeRingConstantCoeff]

/-- The standard split-node ring over a field is nontrivial. -/
instance nodeRing_nontrivial (k : Type u) [Field k] : Nontrivial (nodeRing k) :=
  (nodeRingConstantCoeff_surjective k).nontrivial

/-- The standard split-node ring over a field is local. -/
instance nodeRing_isLocalRing (k : Type u) [Field k] : IsLocalRing (nodeRing k) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (nodeIdeal k))
    Ideal.Quotient.mk_surjective

/-- Constant coefficient from the standard split-node ring to the ground field is local. -/
instance nodeRingConstantCoeff_isLocalHom (k : Type u) [Field k] :
    IsLocalHom (nodeRingConstantCoeff k) :=
  IsLocalHom.of_surjective (nodeRingConstantCoeff k)
    (nodeRingConstantCoeff_surjective k)

/-- Constant coefficient identifies the residue field of the standard split-node ring with
the ground field as a ring. -/
noncomputable def nodeRingResidueFieldRingEquiv (k : Type u) [Field k] :
    IsLocalRing.ResidueField (nodeRing k) ≃+* k :=
  RingEquiv.ofBijective (IsLocalRing.ResidueField.lift (nodeRingConstantCoeff k)) (by
    constructor
    · exact RingHom.injective _
    · intro a
      obtain ⟨b, rfl⟩ := nodeRingConstantCoeff_surjective k a
      exact ⟨IsLocalRing.residue (nodeRing k) b, rfl⟩)

/-- Constant coefficient identifies the residue field of the standard split-node ring with
the ground field as a `k`-algebra. -/
noncomputable def nodeRingResidueFieldAlgEquiv (k : Type u) [Field k] :
    IsLocalRing.ResidueField (nodeRing k) ≃ₐ[k] k :=
  AlgEquiv.ofRingEquiv (f := nodeRingResidueFieldRingEquiv k) (by
    intro a
    change IsLocalRing.ResidueField.lift (nodeRingConstantCoeff k)
      (algebraMap k (IsLocalRing.ResidueField (nodeRing k)) a) = a
    rw [IsScalarTower.algebraMap_apply k (nodeRing k)]
    change IsLocalRing.ResidueField.lift (nodeRingConstantCoeff k)
      (IsLocalRing.residue (nodeRing k) (algebraMap k (nodeRing k) a)) = a
    rw [IsLocalRing.ResidueField.lift_residue_apply]
    change nodeRingConstantCoeff k
      (Ideal.Quotient.mk (nodeIdeal k) (MvPowerSeries.C (σ := Fin 2) a)) = a
    simp [nodeRingConstantCoeff])

/-- The residue field of a split node is canonically equivalent to the ground field. -/
noncomputable def IsSplitNodeAt.residueFieldAlgEquiv
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X] {x : X}
    (h : X.IsSplitNodeAt k x) :
    letI := residueFieldAlgebra (X ↘ Spec (CommRingCat.of k)) x
    X.residueField x ≃ₐ[k] k := by
  letI := stalkAlgebra (X ↘ Spec (CommRingCat.of k)) x
  letI := residueFieldAlgebra (X ↘ Spec (CommRingCat.of k)) x
  letI := completedLocalRingResidueFieldAlgebra
    (X ↘ Spec (CommRingCat.of k)) x
  let e := Classical.choice h
  exact (completedLocalRingResidueFieldAlgEquiv
    (X ↘ Spec (CommRingCat.of k)) x).trans
      ((IsLocalRing.ResidueField.mapAlgEquiv e).trans
        (nodeRingResidueFieldAlgEquiv k))

/-- If a split node is defined over an extension field, its residue field is equivalent to
that extension field after restriction of scalars to the smaller ground ring. -/
noncomputable def IsSplitNodeAt.residueFieldAlgEquiv_restrictScalars
    {R K : Type u} [CommRing R] [Field K] [Algebra R K]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    [IsLocallyNoetherian X] {x : X} (h : X.IsSplitNodeAt K x) :
    letI := residueFieldAlgebra
      ((X ↘ Spec (CommRingCat.of K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K))) x
    X.residueField x ≃ₐ[R] K := by
  letI := residueFieldAlgebra
    ((X ↘ Spec (CommRingCat.of K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R K))) x
  letI := residueFieldAlgebra (X ↘ Spec (CommRingCat.of K)) x
  letI : IsScalarTower R K (X.residueField x) :=
    residueField_isScalarTower (X ↘ Spec (CommRingCat.of K)) x
  exact h.residueFieldAlgEquiv.restrictScalars R

/-- The residue field of a split node is finite-dimensional over the ground field. -/
theorem IsSplitNodeAt.residueField_finiteDimensional
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X] {x : X}
    (h : X.IsSplitNodeAt k x) :
    letI := residueFieldAlgebra (X ↘ Spec (CommRingCat.of k)) x
    FiniteDimensional k (X.residueField x) := by
  let _ := residueFieldAlgebra (X ↘ Spec (CommRingCat.of k)) x
  exact Module.Finite.equiv h.residueFieldAlgEquiv.symm.toLinearEquiv

/-- The residue field of a split node is separable over the ground field. -/
theorem IsSplitNodeAt.residueField_isSeparable
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X] {x : X}
    (h : X.IsSplitNodeAt k x) :
    letI := residueFieldAlgebra (X ↘ Spec (CommRingCat.of k)) x
    Algebra.IsSeparable k (X.residueField x) := by
  let _ := residueFieldAlgebra (X ↘ Spec (CommRingCat.of k)) x
  exact AlgEquiv.Algebra.isSeparable h.residueFieldAlgEquiv.symm

/-- Over a smaller field, the residue field of a split node over a finite extension remains
finite-dimensional. -/
theorem IsSplitNodeAt.residueField_finiteDimensional_restrictScalars
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    [IsLocallyNoetherian X] {x : X} (h : X.IsSplitNodeAt K x) :
    letI := residueFieldAlgebra
      ((X ↘ Spec (CommRingCat.of K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K))) x
    FiniteDimensional k (X.residueField x) := by
  let _ := residueFieldAlgebra
    ((X ↘ Spec (CommRingCat.of K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K))) x
  exact Module.Finite.equiv
    h.residueFieldAlgEquiv_restrictScalars.symm.toLinearEquiv

/-- Over a smaller field, the residue field of a split node over a separable extension
remains separable. -/
theorem IsSplitNodeAt.residueField_isSeparable_restrictScalars
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of K))]
    [IsLocallyNoetherian X] {x : X} (h : X.IsSplitNodeAt K x) :
    letI := residueFieldAlgebra
      ((X ↘ Spec (CommRingCat.of K)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k K))) x
    Algebra.IsSeparable k (X.residueField x) := by
  let _ := residueFieldAlgebra
    ((X ↘ Spec (CommRingCat.of K)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap k K))) x
  exact AlgEquiv.Algebra.isSeparable
    h.residueFieldAlgEquiv_restrictScalars.symm

/-- At a split node, the ground-field map to the residue field is bijective. -/
theorem IsSplitNodeAt.algebraMap_residueField_bijective
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X] {x : X}
    (h : X.IsSplitNodeAt k x) :
    letI := residueFieldAlgebra (X ↘ Spec (CommRingCat.of k)) x
    Function.Bijective (algebraMap k (X.residueField x)) := by
  let _ := residueFieldAlgebra (X ↘ Spec (CommRingCat.of k)) x
  let e := h.residueFieldAlgEquiv
  refine ⟨RingHom.injective _, fun y ↦ ⟨e y, ?_⟩⟩
  rw [← e.symm.commutes]
  exact e.symm_apply_apply y

/-- The residue field of a split node has degree one over the ground field. -/
theorem IsSplitNodeAt.finrank_residueField_eq_one
    {k : Type u} [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X] {x : X}
    (h : X.IsSplitNodeAt k x) :
    letI := residueFieldAlgebra (X ↘ Spec (CommRingCat.of k)) x
    Module.finrank k (X.residueField x) = 1 := by
  let _ := residueFieldAlgebra (X ↘ Spec (CommRingCat.of k)) x
  exact h.residueFieldAlgEquiv.toLinearEquiv.finrank_eq.trans (Module.finrank_self k)

end AlgebraicGeometry.Scheme
