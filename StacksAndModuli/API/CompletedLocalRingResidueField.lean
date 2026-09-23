module

public import StacksAndModuli.API.CompletedLocalRing
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# Residue fields and completed local rings

This file equips residue fields of schemes over affine bases with their canonical algebra
structures. It records functoriality under morphisms and the fact that completion at the
maximal ideal does not change the residue field of a locally Noetherian scheme.

The algebra structures depend on the chosen structural morphism, so they are definitions
rather than global instances. Install them locally with
`letI := Scheme.residueFieldAlgebra f x` and
`letI := Scheme.completedLocalRingResidueFieldAlgebra f x`.

## Main definitions and results

* `AlgebraicGeometry.Scheme.residueFieldAlgebra`;
* `AlgebraicGeometry.Scheme.Hom.residueFieldMapAlgHom`;
* `AlgebraicGeometry.Scheme.Hom.residueFieldMapAlgHomOfCompEq`;
* `AlgebraicGeometry.Scheme.residueField_isScalarTower`;
* `AlgebraicGeometry.Scheme.residueField_finiteDimensional_of_algHom`;
* `AlgebraicGeometry.Scheme.residueField_isSeparable_of_algHom`;
* `AlgebraicGeometry.Scheme.completedLocalRingResidueFieldAlgebra`;
* `AlgebraicGeometry.Scheme.completedLocalRingResidueFieldAlgEquiv`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical algebra structure on the residue field of a point of a scheme over an
affine base. -/
@[instance_reducible]
noncomputable def residueFieldAlgebra
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    Algebra R (X.residueField x) := by
  letI := stalkAlgebra f x
  exact IsLocalRing.ResidueField.algebra (X.presheaf.stalk x)

/-- A morphism of schemes induces an algebra homomorphism on residue fields over any affine
base of its target. -/
noncomputable def Hom.residueFieldMapAlgHom
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (g : X ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of R)) (x : X) :
    letI := residueFieldAlgebra p (g x)
    letI := residueFieldAlgebra (g ≫ p) x
    Y.residueField (g x) →ₐ[R] X.residueField x := by
  letI := stalkAlgebra p (g x)
  letI := stalkAlgebra (g ≫ p) x
  letI := residueFieldAlgebra p (g x)
  letI := residueFieldAlgebra (g ≫ p) x
  exact
    { (g.residueFieldMap x).hom with
      commutes' := fun r ↦ by
        change IsLocalRing.ResidueField.map (g.stalkMap x).hom
            (IsLocalRing.residue (Y.presheaf.stalk (g x))
              (baseToStalk p (g x) r)) =
          IsLocalRing.residue (X.presheaf.stalk x)
            (baseToStalk (g ≫ p) x r)
        rw [IsLocalRing.ResidueField.map_residue]
        congr 1
        exact DFunLike.congr_fun
          (CommRingCat.hom_ext_iff.mp (baseToStalk_comp_stalkMap g p x)) r }

/-- The underlying function of the algebra homomorphism on residue fields is the usual
residue-field map. -/
@[simp]
theorem Hom.residueFieldMapAlgHom_apply
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (g : X ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of R)) (x : X)
    (a : Y.residueField (g x)) :
    g.residueFieldMapAlgHom p x a = g.residueFieldMap x a :=
  rfl

/-- A morphism of schemes induces an algebra homomorphism on residue fields for an
explicitly equal choice of structural morphism on its source. -/
noncomputable def Hom.residueFieldMapAlgHomOfCompEq
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (g : X ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of R))
    (q : X ⟶ Spec (CommRingCat.of R)) (h : g ≫ p = q) (x : X) :
    letI := residueFieldAlgebra p (g x)
    letI := residueFieldAlgebra q x
    Y.residueField (g x) →ₐ[R] X.residueField x := by
  subst q
  exact g.residueFieldMapAlgHom p x

/-- The underlying function of the residue-field algebra homomorphism for an equal
structural composite is the usual residue-field map. -/
@[simp]
theorem Hom.residueFieldMapAlgHomOfCompEq_apply
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (g : X ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of R))
    (q : X ⟶ Spec (CommRingCat.of R)) (h : g ≫ p = q) (x : X)
    (a : Y.residueField (g x)) :
    g.residueFieldMapAlgHomOfCompEq p q h x a = g.residueFieldMap x a := by
  subst q
  rfl

/-- The residue-field algebra structures induced by a tower of affine bases form a scalar
tower. -/
theorem residueField_isScalarTower
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (x : X) :
    letI := residueFieldAlgebra
      (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) x
    letI := residueFieldAlgebra f x
    IsScalarTower R S (X.residueField x) := by
  let _ := stalkAlgebra
    (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) x
  let _ := stalkAlgebra f x
  let _ := residueFieldAlgebra
    (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) x
  let _ := residueFieldAlgebra f x
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change IsLocalRing.residue (X.presheaf.stalk x)
      (baseToStalk
        (f ≫ Spec.map (CommRingCat.ofHom (algebraMap R S))) x a) =
    IsLocalRing.residue (X.presheaf.stalk x)
      (baseToStalk f x (algebraMap R S a))
  congr 1
  exact DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp
      (baseToStalk_comp (CommRingCat.ofHom (algebraMap R S)) f x)) a |>.symm

/-- A residue field that embeds over the base into a finite-dimensional field extension is
finite-dimensional over the base. -/
theorem residueField_finiteDimensional_of_algHom
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X)
    {K : Type u} [Field K] [Algebra k K] [FiniteDimensional k K]
    (g : letI := residueFieldAlgebra f x
      X.residueField x →ₐ[k] K) :
    letI := residueFieldAlgebra f x
    FiniteDimensional k (X.residueField x) := by
  let _ := residueFieldAlgebra f x
  exact FiniteDimensional.of_injective g.toLinearMap g.injective

/-- A residue field that embeds over the base into a separable field extension is separable
over the base. -/
theorem residueField_isSeparable_of_algHom
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X)
    {K : Type u} [Field K] [Algebra k K] [Algebra.IsSeparable k K]
    (g : letI := residueFieldAlgebra f x
      X.residueField x →ₐ[k] K) :
    letI := residueFieldAlgebra f x
    Algebra.IsSeparable k (X.residueField x) := by
  let _ := residueFieldAlgebra f x
  exact Algebra.IsSeparable.of_algHom k K g

/-- The canonical algebra structure on the residue field of the completed local ring of a
point of a locally Noetherian scheme over an affine base. -/
@[instance_reducible]
noncomputable def completedLocalRingResidueFieldAlgebra
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsLocallyNoetherian X] (x : X) :
    Algebra R (IsLocalRing.ResidueField (X.completedLocalRing x)) := by
  letI := stalkAlgebra f x
  exact IsLocalRing.ResidueField.algebra (X.completedLocalRing x)

/-- Completion at the maximal ideal preserves the residue field, compatibly with the
algebra structure induced by a structural morphism to the spectrum of a field. -/
noncomputable def completedLocalRingResidueFieldAlgEquiv
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [IsLocallyNoetherian X] (x : X) :
    letI := residueFieldAlgebra f x
    letI := completedLocalRingResidueFieldAlgebra f x
    X.residueField x ≃ₐ[k] IsLocalRing.ResidueField (X.completedLocalRing x) := by
  letI := stalkAlgebra f x
  letI := residueFieldAlgebra f x
  letI := completedLocalRingResidueFieldAlgebra f x
  let g : X.presheaf.stalk x →ₐ[k] X.completedLocalRing x :=
    { X.toCompletedLocalRing x with
      commutes' := fun a ↦ (algebraMap_completedLocalRingAlgebra f x a).symm }
  letI : IsLocalHom g := by
    have hlocal : IsLocalHom (X.toCompletedLocalRing x) := by
      rw [show X.toCompletedLocalRing x =
        algebraMap (X.presheaf.stalk x) (X.completedLocalRing x) from rfl]
      infer_instance
    constructor
    intro a ha
    exact hlocal.map_nonunit a ha
  exact AlgEquiv.ofBijective (IsLocalRing.ResidueField.mapAlgHom g)
    (AdicCompletion.residueField_map_bijective (X.presheaf.stalk x))

end AlgebraicGeometry.Scheme
