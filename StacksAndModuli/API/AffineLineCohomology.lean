module

public import StacksAndModuli.API.GenericPrincipalPartsWeakApproximation
public import StacksAndModuli.API.PolynomialWeakApproximation
public import StacksAndModuli.API.ProjectiveLineCohomologyReduction
public import StacksAndModuli.«Section6.1-Smooth».«part6.1.1-curves»
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Structure-sheaf cohomology of the affine and projective lines

Weak approximation for rational functions on `Spec k[X]` implies that its generic
principal-parts map is surjective and hence that `H¹(Spec k[X], 𝒪) = 0`. The two
standard charts of polynomial `Proj` are explicitly isomorphic to `Spec k[X]`, so the
standard-cover calculation then gives `H¹(ℙ¹_k, 𝒪) = 0` and genus zero.

The affine argument works over an arbitrary field. In particular, it does not classify
closed points or require them to be rational: the PID structure of `k[X]` supplies weak
approximation at arbitrary prime ideals.

## Main results

* `AlgebraicGeometry.Scheme.polynomialAffineLine_hasFiniteLocalWeakApproximation`;
* `AlgebraicGeometry.Scheme.polynomialAffineLine_H_one_subsingleton`;
* `AlgebraicGeometry.Proj.projectiveLineChartZero_H_one_subsingleton` and
  `AlgebraicGeometry.Proj.projectiveLineChartOne_H_one_subsingleton`;
* `AlgebraicGeometry.ProjectiveSpace.Cohomology.projectiveLine_H_one_subsingleton`;
* `AlgebraicGeometry.ProjectiveSpace.Cohomology.projectiveLine_genusOver_eq_zero`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped Polynomial
open AlgebraicGeometry ProjectiveSpectrum HomogeneousLocalization

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

/-- The polynomial presentation `Spec k[X]` of the affine line over `k`. -/
abbrev polynomialAffineLine : Scheme.{u} := Spec (CommRingCat.of k[X])

@[instance_reducible]
noncomputable local instance polynomialAffineLineLocalAlgebra
    (p : polynomialAffineLine k) :
    Algebra k[X] ((polynomialAffineLine k).presheaf.stalk p) :=
  (StructureSheaf.toStalk k[X] p).hom.toAlgebra

@[instance_reducible]
noncomputable local instance polynomialAffineLineFunctionAlgebra :
    Algebra k[X] (polynomialAffineLine k).functionField :=
  (StructureSheaf.toStalk k[X]
    (genericPoint (polynomialAffineLine k))).hom.toAlgebra

/-- The map from the coordinate ring to a local ring, followed by specialization to
the generic point, is the coordinate-ring map to the function field. -/
lemma polynomialAffineLine_toStalk_stalkSpecializes
    (p : polynomialAffineLine k) :
    StructureSheaf.toStalk k[X] p ≫
        (polynomialAffineLine k).presheaf.stalkSpecializes
          ((genericPoint_spec (polynomialAffineLine k)).specializes trivial) =
      StructureSheaf.toStalk k[X]
        (genericPoint (polynomialAffineLine k)) :=
  StructureSheaf.toStalk_stalkSpecializes
    ((genericPoint_spec (polynomialAffineLine k)).specializes trivial)

/-- Algebraic regularity of a rational function at a prime of `k[X]` is equivalent
to belonging to the image of the corresponding local ring in the function field. -/
theorem polynomial_isRegularAtPrime_iff_exists_stalk_algebraMap_eq
    (p : polynomialAffineLine k) (z : (polynomialAffineLine k).functionField) :
    Polynomial.IsRegularAtPrime p z ↔
      ∃ t : (polynomialAffineLine k).presheaf.stalk p,
        algebraMap ((polynomialAffineLine k).presheaf.stalk p)
          (polynomialAffineLine k).functionField t = z := by
  let _ : p.asIdeal.IsPrime := p.2
  let _ : IsLocalization p.asIdeal.primeCompl
      ((polynomialAffineLine k).presheaf.stalk p) :=
    StructureSheaf.IsLocalization.to_stalk k[X] p
  let _ : IsFractionRing k[X] (polynomialAffineLine k).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of k[X])
  let _ : IsScalarTower k[X] ((polynomialAffineLine k).presheaf.stalk p)
      (polynomialAffineLine k).functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    simp_rw [RingHom.algebraMap_toAlgebra]
    exact congrArg CommRingCat.Hom.hom
      (polynomialAffineLine_toStalk_stalkSpecializes k p).symm
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    let t := IsLocalization.mk' ((polynomialAffineLine k).presheaf.stalk p)
      a ⟨b, show b ∈ p.asIdeal.primeCompl from hb⟩
    refine ⟨t, ?_⟩
    have ht := congrArg
      (algebraMap ((polynomialAffineLine k).presheaf.stalk p)
        (polynomialAffineLine k).functionField)
      (IsLocalization.mk'_spec ((polynomialAffineLine k).presheaf.stalk p)
        a ⟨b, show b ∈ p.asIdeal.primeCompl from hb⟩)
    have hb0 : algebraMap k[X] (polynomialAffineLine k).functionField b ≠ 0 :=
      (map_ne_zero_iff _
        (IsFractionRing.injective k[X]
          (polynomialAffineLine k).functionField)).mpr
          (fun h ↦ hb (h ▸ p.asIdeal.zero_mem))
    rw [map_mul,
      ← IsScalarTower.algebraMap_apply k[X]
        ((polynomialAffineLine k).presheaf.stalk p)
          (polynomialAffineLine k).functionField,
      ← IsScalarTower.algebraMap_apply k[X]
        ((polynomialAffineLine k).presheaf.stalk p)
          (polynomialAffineLine k).functionField] at ht
    exact (eq_div_iff hb0).mpr ht
  · rintro ⟨t, rfl⟩
    obtain ⟨a, b, rfl⟩ :=
      IsLocalization.exists_mk'_eq p.asIdeal.primeCompl t
    refine ⟨a, b, b.2, ?_⟩
    have ht := congrArg
      (algebraMap ((polynomialAffineLine k).presheaf.stalk p)
        (polynomialAffineLine k).functionField)
      (IsLocalization.mk'_spec
        ((polynomialAffineLine k).presheaf.stalk p) a b)
    have hb0 :
        algebraMap k[X] (polynomialAffineLine k).functionField b.1 ≠ 0 :=
      (map_ne_zero_iff _
        (IsFractionRing.injective k[X]
          (polynomialAffineLine k).functionField)).mpr
          (fun h ↦ b.2 (h ▸ p.asIdeal.zero_mem))
    rw [map_mul,
      ← IsScalarTower.algebraMap_apply k[X]
        ((polynomialAffineLine k).presheaf.stalk p)
          (polynomialAffineLine k).functionField,
      ← IsScalarTower.algebraMap_apply k[X]
        ((polynomialAffineLine k).presheaf.stalk p)
          (polynomialAffineLine k).functionField] at ht
    exact (eq_div_iff hb0).mpr ht

/-- The polynomial affine line satisfies finite local weak approximation in its
function field. -/
theorem polynomialAffineLine_hasFiniteLocalWeakApproximation :
    (polynomialAffineLine k).HasFiniteLocalWeakApproximation := by
  let _ : IsFractionRing k[X] (polynomialAffineLine k).functionField :=
    functionField_isFractionRing_of_affine (CommRingCat.of k[X])
  intro s z
  obtain ⟨r, hmatch, haway⟩ :=
    Polynomial.exists_isRegularAtPrime_sub_and_regular_outside s z
  refine ⟨r, ?_, ?_⟩
  · intro x
    exact
      (polynomial_isRegularAtPrime_iff_exists_stalk_algebraMap_eq
        k x.1 (z x - r)).mp (hmatch x)
  · intro x hx
    exact
      (polynomial_isRegularAtPrime_iff_exists_stalk_algebraMap_eq
        k x r).mp (haway x hx)

/-- The polynomial affine line has topological Krull dimension at most one. -/
theorem topologicalKrullDim_polynomialAffineLine_le_one :
    topologicalKrullDim (polynomialAffineLine k) ≤ 1 := by
  change topologicalKrullDim (PrimeSpectrum k[X]) ≤ 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    Polynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field]
  simp only [zero_add]
  exact le_rfl

/-- The first structure-sheaf cohomology of the polynomial affine line vanishes. -/
theorem polynomialAffineLine_H_one_subsingleton :
    Subsingleton
      (Modules.H (structureModule (polynomialAffineLine k)) 1) := by
  apply subsingleton_H_one_structureModule_of_weakApproximation
    (polynomialAffineLine k)
  · exact topologicalKrullDim_polynomialAffineLine_le_one k
  · exact polynomialAffineLine_hasFiniteLocalWeakApproximation k

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k]

/-- The zero-coordinate standard chart of the projective line is the polynomial
affine line. -/
noncomputable def projectiveLineChartZeroIsoPolynomialAffineLine :
    (projectiveLineChartZero k).toScheme ≅ Scheme.polynomialAffineLine k :=
  basicOpenIsoSpec (lineGrading k) (MvPolynomial.X (0 : Fin 2))
      (X_zero_mem_lineGrading k) Nat.one_pos ≪≫
    Scheme.Spec.mapIso
      (chartZeroPolynomialEquivAway k).toCommRingCatIso.op

/-- The one-coordinate standard chart of the projective line is the polynomial
affine line. -/
noncomputable def projectiveLineChartOneIsoPolynomialAffineLine :
    (projectiveLineChartOne k).toScheme ≅ Scheme.polynomialAffineLine k :=
  basicOpenIsoSpec (lineGrading k) (MvPolynomial.X (1 : Fin 2))
      (X_one_mem_lineGrading k) Nat.one_pos ≪≫
    Scheme.Spec.mapIso
      (chartOnePolynomialEquivAway k).toCommRingCatIso.op

/-- The first structure-sheaf cohomology of the zero-coordinate standard chart of
the projective line vanishes. -/
theorem projectiveLineChartZero_H_one_subsingleton :
    Subsingleton (Scheme.Modules.H
      (Scheme.structureModule (projectiveLineChartZero k).toScheme) 1) :=
  let _ := Scheme.polynomialAffineLine_H_one_subsingleton k
  (Scheme.structureCohomologyAddEquivOfIso
      (projectiveLineChartZeroIsoPolynomialAffineLine k) 1).toEquiv.subsingleton

/-- The first structure-sheaf cohomology of the one-coordinate standard chart of
the projective line vanishes. -/
theorem projectiveLineChartOne_H_one_subsingleton :
    Subsingleton (Scheme.Modules.H
      (Scheme.structureModule (projectiveLineChartOne k).toScheme) 1) :=
  let _ := Scheme.polynomialAffineLine_H_one_subsingleton k
  (Scheme.structureCohomologyAddEquivOfIso
      (projectiveLineChartOneIsoPolynomialAffineLine k) 1).toEquiv.subsingleton

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

variable {k : Type u} [Field k]

/-- The first structure-sheaf cohomology of the relative projective line over a field
vanishes. -/
theorem projectiveLine_H_one_subsingleton :
    Subsingleton
      (Scheme.Modules.H
        (Scheme.structureModule
          (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))) 1) := by
  let _ := Proj.projectiveLineChartZero_H_one_subsingleton k
  let _ := Proj.projectiveLineChartOne_H_one_subsingleton k
  exact projectiveLine_H_one_subsingleton_of_chart_H_one (k := k)

/-- The structure-sheaf `h¹` of the relative projective line is zero for any chosen
`k`-scheme structure. -/
theorem projectiveLine_h_one_eq_zero
    [Scheme.Over
      (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))
      (Spec (CommRingCat.of k))] :
    Scheme.Modules.h k
      (Scheme.structureModule
        (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))) 1 = 0 :=
  Scheme.Modules.h_eq_zero_of_subsingleton k _ 1
    (projectiveLine_H_one_subsingleton (k := k))

/-- The relative projective line has genus zero for any chosen `k`-scheme structure. -/
theorem projectiveLine_genusOver_eq_zero
    [Scheme.Over
      (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))
      (Spec (CommRingCat.of k))] :
    Scheme.genusOver k
      (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k))) = 0 :=
  projectiveLine_h_one_eq_zero (k := k)

end AlgebraicGeometry.ProjectiveSpace.Cohomology

end
