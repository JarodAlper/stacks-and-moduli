module

public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.1-representability-by-a-scheme»
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Rank-one Grassmannians and projective space

Supporting material for Section 2.2 (Projectivity of the Grassmannian, label
`sec:grassmannian`) of Chapter 2 of *Stacks and Moduli*:
the comparison between the rank-one Grassmannian
`Gr(1, n+1) = ℙ(O^{⊕(n+1)})` used as the Plücker target in `prop:grassmannian-projective`
and the `Proj` construction of projective space.  The intended first step packages the
standard-chart trivializations of the Serre twisting sheaves as the constant-rank
vector-bundle statement needed by the relative Grassmannian functor.

## Main declarations

Currently live: the rank-one chart index/coordinate bookkeeping
(`Proj.rankOneGrassmannianChartIndex`, `Proj.rankOneGrassmannianChartCoordinateEquiv`),
the degree-one chart cover (`Proj.iSup_basicOpen_X_eq_top`), the
dehomogenization/homogenization calculus on the standard charts `D₊(Xᵢ)`
(`Proj.projectiveSpaceDehomogenize`, `Proj.projectiveSpaceChartHomogenize` and their
lemmas), and the **chart coordinate-ring comparison**: the polynomial ring on the
non-pivot variables is the coordinate ring of the standard chart
(`Proj.projectiveSpaceChartPolynomialEquivAway`, via the inverse map
`Proj.projectiveSpaceAwayToChartPolynomial` descended from dehomogenization through
`Localization.awayLift`), and its rank-one Grassmannian matrix-coordinate variant
`Proj.rankOneGrassmannianChartPolynomialEquivAway` (with the sign convention forced by
the kernel encoding, `Proj.grassmannianChartSignEquiv`).

Also live: the chart *scheme* isomorphisms built on Mathlib's `Proj.basicOpenIsoSpec` —
`Proj.projectiveSpaceChartIsoRankOneGrassmannianChart` identifies the standard chart
`D₊(Xᵢ)` with the represented rank-one Grassmannian chart (an affine space), and
`Proj.projectiveSpaceChartToRankOneGrassmannian` is the induced morphism from the chart
into the glued Grassmannian.

The remainder of the comparison — the twist bundle statements, the agreement of the
chart morphisms on overlaps, and the resulting global isomorphism `Proj ≅ Gr(1, n+1)` —
was invalidated by upstream Mathlib drift and is retained commented out as recorded
obligations; see OBLIGATIONS.md.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.ProjectiveSpectrum

attribute [local instance] MvPolynomial.gradedAlgebra

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The degree-one coordinate basic opens cover projective space defined from the
standard grading on a multivariate polynomial ring. -/
theorem Proj.iSup_basicOpen_X_eq_top (I : Type*) (R : Type u) [CommRing R] :
    ⨆ i : I, Proj.basicOpen (MvPolynomial.homogeneousSubmodule I R)
      (MvPolynomial.X i) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  intro p hp
  simp only [Set.mem_iUnion] at hp
  obtain ⟨k, hk, hp⟩ := hp
  rw [show Ideal.span (Set.range (MvPolynomial.X : I → MvPolynomial I R)) =
      MvPolynomial.idealOfVars I R from rfl,
    MvPolynomial.idealOfVars_eq_restrictSupportIdeal]
  intro m hm
  have hdeg : m.degree = k :=
    ((show p.IsHomogeneous k from hp).degree_eq_sum_deg_support hm).symm
  exact Nat.one_le_iff_ne_zero.mpr (by rw [hdeg]; exact Nat.ne_of_gt hk)

/-- The singleton chart index `{i}` of the rank-one Grassmannian `Gr(1, n+1)` (the
Plücker target of Proposition 2.2.8), corresponding to the standard
projective chart `D₊(Xᵢ)` with pivot `i`. -/
def Proj.rankOneGrassmannianChartIndex (n : ℕ) (i : Fin (n + 1)) :
    Scheme.grassmannianChartCoverIndex.{u} 1 (n + 1) :=
  ULift.up ⟨{i}, by simp⟩

/-- Matrix coordinates on the rank-one chart with pivot `i` are canonically indexed
by the remaining homogeneous coordinates. -/
def Proj.rankOneGrassmannianChartCoordinateEquiv (n : ℕ) (i : Fin (n + 1)) :
    ULift.{u} (↑({i} : Finset (Fin (n + 1))) ×
      ↑(({i} : Finset (Fin (n + 1)))ᶜ)) ≃
      ULift.{u} {j : Fin (n + 1) // j ≠ i} where
  toFun x := ULift.up ⟨x.down.2.1,
    fun h ↦ (Finset.mem_compl.mp x.down.2.2)
      (Finset.mem_singleton.mpr h)⟩
  invFun j := ULift.up
    ⟨⟨i, by simp⟩, ⟨j.down.1,
      Finset.mem_compl.mpr (fun h ↦
        j.down.2 (Finset.mem_singleton.mp h))⟩⟩
  left_inv x := by
    apply ULift.ext
    apply Prod.ext
    · apply Subtype.ext
      exact (Finset.mem_singleton.mp x.down.1.2).symm
    · rfl
  right_inv j := by
    apply ULift.ext
    apply Subtype.ext
    rfl

/-- The coordinate-ring renaming induced by the identification of matrix coordinates
on a rank-one Grassmannian chart with the non-pivot homogeneous coordinates. -/
noncomputable def Proj.rankOneGrassmannianChartPolynomialEquiv
    (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial
        (ULift.{u} (↑({i} : Finset (Fin (n + 1))) ×
          ↑(({i} : Finset (Fin (n + 1)))ᶜ))) (ULift.{u} ℤ) ≃ₐ[ULift.{u} ℤ]
      MvPolynomial (ULift.{u} {j : Fin (n + 1) // j ≠ i}) (ULift.{u} ℤ) :=
  MvPolynomial.renameEquiv (ULift.{u} ℤ)
    (Proj.rankOneGrassmannianChartCoordinateEquiv n i)

/-- On the standard projective chart `D₊(Xᵢ)`, the non-pivot coordinate `j` is
the homogeneous fraction `Xⱼ / Xᵢ`. -/
noncomputable def Proj.projectiveSpaceChartCoordinate
    (n : ℕ) (i : Fin (n + 1))
    (j : ULift.{u} {j : Fin (n + 1) // j ≠ i}) :
    HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i) :=
  HomogeneousLocalization.Away.mk
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i) 1
    (MvPolynomial.X j.down.1)
    (by simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j.down.1)

/-- The polynomial coordinate ring of the standard affine-space chart maps to the
degree-zero homogeneous localization by sending each variable to `Xⱼ / Xᵢ`. -/
noncomputable def Proj.projectiveSpaceChartPolynomialToAway
    (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial (ULift.{u} {j : Fin (n + 1) // j ≠ i}) (ULift.{u} ℤ) →+*
      HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) :=
  MvPolynomial.eval₂Hom
    ((HomogeneousLocalization.fromZeroRingHom
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (Submonoid.powers (MvPolynomial.X i))).comp
        (MvPolynomial.degreeZeroRingEquiv (Fin (n + 1)) (ULift.{u} ℤ)).toRingHom)
    (Proj.projectiveSpaceChartCoordinate n i)

/-- A finite product of localization fractions is represented by the products of
their numerators and denominators. -/
lemma Localization.prod_mk {R : Type*} [CommRing R] (M : Submonoid R)
    {ι : Type*} (s : Finset ι) (a : ι → R) (b : ι → M) :
    ∏ j ∈ s, Localization.mk (a j) (b j) =
      Localization.mk (∏ j ∈ s, a j) (∏ j ∈ s, b j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Localization.mk_one.symm
  | @insert j s hj ih =>
      simp only [Finset.prod_insert hj]
      rw [ih, Localization.mk_mul]

/-- A finite sum of localization fractions with a common denominator is represented
by the sum of their numerators. -/
lemma Localization.sum_mk {R : Type*} [CommRing R] (M : Submonoid R)
    {ι : Type*} (s : Finset ι) (a : ι → R) (b : M) :
    ∑ j ∈ s, Localization.mk (a j) b =
      Localization.mk (∑ j ∈ s, a j) b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      rw [Localization.mk_eq_mk', IsLocalization.mk'_zero]
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      rw [ih, Localization.add_mk_self]

/-- The embedding of a homogeneous localization into the ordinary localization
preserves finite products. -/
lemma HomogeneousLocalization.val_prod {R σ : Type*} [CommRing R] [SetLike σ R]
    [AddSubgroupClass σ R] {𝒶 : ℕ → σ} [GradedRing 𝒶] (M : Submonoid R)
    {ι : Type*} (s : Finset ι) (f : ι → HomogeneousLocalization 𝒶 M) :
    HomogeneousLocalization.val (∏ j ∈ s, f j) =
      ∏ j ∈ s, HomogeneousLocalization.val (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact HomogeneousLocalization.val_one
  | @insert j s hj ih =>
      simp only [Finset.prod_insert hj, HomogeneousLocalization.val_mul, ih]

/-- The embedding of a homogeneous localization into the ordinary localization
preserves finite sums. -/
lemma HomogeneousLocalization.val_sum {R σ : Type*} [CommRing R] [SetLike σ R]
    [AddSubgroupClass σ R] {𝒶 : ℕ → σ} [GradedRing 𝒶] (M : Submonoid R)
    {ι : Type*} (s : Finset ι) (f : ι → HomogeneousLocalization 𝒶 M) :
    HomogeneousLocalization.val (∑ j ∈ s, f j) =
      ∑ j ∈ s, HomogeneousLocalization.val (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact HomogeneousLocalization.val_zero
  | @insert j s hj ih =>
      simp only [Finset.sum_insert hj, HomogeneousLocalization.val_add, ih]

@[simp]
lemma Proj.projectiveSpaceChartPolynomialToAway_X
    (n : ℕ) (i : Fin (n + 1))
    (j : ULift.{u} {j : Fin (n + 1) // j ≠ i}) :
    Proj.projectiveSpaceChartPolynomialToAway n i (MvPolynomial.X j) =
      Proj.projectiveSpaceChartCoordinate n i j := by
  simp [Proj.projectiveSpaceChartPolynomialToAway]

@[simp]
lemma Proj.projectiveSpaceChartCoordinate_val
    (n : ℕ) (i : Fin (n + 1))
    (j : ULift.{u} {j : Fin (n + 1) // j ≠ i}) :
    (Proj.projectiveSpaceChartCoordinate n i j).val =
      Localization.mk (MvPolynomial.X j.down.1)
        ⟨MvPolynomial.X i ^ 1, by use 1⟩ := by
  rfl

@[simp]
lemma Proj.projectiveSpaceChartCoordinate_pow_val
    (n : ℕ) (i : Fin (n + 1))
    (j : ULift.{u} {j : Fin (n + 1) // j ≠ i}) (e : ℕ) :
    ((Proj.projectiveSpaceChartCoordinate n i j) ^ e).val =
      Localization.mk (MvPolynomial.X j.down.1 ^ e)
        ⟨MvPolynomial.X i ^ e, by use e⟩ := by
  rw [HomogeneousLocalization.val_pow,
    Proj.projectiveSpaceChartCoordinate_val, Localization.mk_pow]
  congr 1
  apply Subtype.ext
  simp

@[simp]
lemma Proj.projectiveSpaceChartPolynomialToAway_C_val
    (n : ℕ) (i : Fin (n + 1)) (r : ULift.{u} ℤ) :
    (Proj.projectiveSpaceChartPolynomialToAway n i (MvPolynomial.C r)).val =
      Localization.mk (MvPolynomial.C r) ⟨1, Submonoid.one_mem _⟩ := by
  simp only [Proj.projectiveSpaceChartPolynomialToAway,
    HomogeneousLocalization.fromZeroRingHom, MvPolynomial.eval₂Hom_C]
  refine (HomogeneousLocalization.val_mk _).trans ?_
  simp [MvPolynomial.degreeZeroRingEquiv_apply_coe]

/-- Each variable factor in a dehomogenized monomial contributes the fraction
`Xⱼ^e / Xᵢ^e`; for the pivot variable this is the unit fraction. -/
lemma Proj.projectiveSpaceChartMonomialFactor_val
    (n : ℕ) (i j : Fin (n + 1)) (e : ℕ) :
    ((Proj.projectiveSpaceChartPolynomialToAway n i)
      (if h : j = i then 1 else MvPolynomial.X (ULift.up ⟨j, h⟩)) ^ e).val =
      Localization.mk (MvPolynomial.X j ^ e)
        ⟨MvPolynomial.X i ^ e, by use e⟩ := by
  by_cases h : j = i
  · subst j
    rw [Localization.mk_eq_mk', IsLocalization.mk'_self]
    simp [Proj.projectiveSpaceChartPolynomialToAway]
  · rw [dif_neg h, Proj.projectiveSpaceChartPolynomialToAway_X,
      Proj.projectiveSpaceChartCoordinate_pow_val]

/-- Dehomogenization on the chart `D₊(Xᵢ)`: the pivot variable is sent to `1`
and every other homogeneous variable becomes the corresponding affine coordinate. -/
noncomputable def Proj.projectiveSpaceDehomogenize
    (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ) →+*
      MvPolynomial (ULift.{u} {j : Fin (n + 1) // j ≠ i}) (ULift.{u} ℤ) :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun j ↦
    if h : j = i then 1 else MvPolynomial.X (ULift.up ⟨j, h⟩)

@[simp]
lemma Proj.projectiveSpaceDehomogenize_X_pivot
    (n : ℕ) (i : Fin (n + 1)) :
    Proj.projectiveSpaceDehomogenize n i (MvPolynomial.X i) = 1 := by
  simp [Proj.projectiveSpaceDehomogenize]

@[simp]
lemma Proj.projectiveSpaceDehomogenize_X_nonpivot
    (n : ℕ) (i : Fin (n + 1)) (j : Fin (n + 1)) (h : j ≠ i) :
    Proj.projectiveSpaceDehomogenize n i (MvPolynomial.X j) =
      MvPolynomial.X (ULift.up ⟨j, h⟩) := by
  simp [Proj.projectiveSpaceDehomogenize, h]

@[simp]
lemma Proj.projectiveSpaceDehomogenize_C
    (n : ℕ) (i : Fin (n + 1)) (r : ULift.{u} ℤ) :
    Proj.projectiveSpaceDehomogenize n i (MvPolynomial.C r) =
      MvPolynomial.C r := by
  simp [Proj.projectiveSpaceDehomogenize]

/-- Regard an affine chart polynomial as a homogeneous-coordinate polynomial using
only the non-pivot variables.  This is a section of dehomogenization. -/
noncomputable def Proj.projectiveSpaceChartPolynomialToHomogeneous
    (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial (ULift.{u} {j : Fin (n + 1) // j ≠ i}) (ULift.{u} ℤ) →+*
      MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ) :=
  (MvPolynomial.rename fun j ↦ j.down.1).toRingHom

/-- Dehomogenization is split-surjective: reinterpreting an affine polynomial in the
non-pivot homogeneous variables and then setting the pivot variable to one recovers
the original polynomial. -/
lemma Proj.projectiveSpaceChartPolynomialToHomogeneous_comp_dehomogenize
    (n : ℕ) (i : Fin (n + 1)) :
    (Proj.projectiveSpaceDehomogenize n i).comp
      (Proj.projectiveSpaceChartPolynomialToHomogeneous n i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [Proj.projectiveSpaceChartPolynomialToHomogeneous,
      Proj.projectiveSpaceDehomogenize]
  · intro j
    simp [Proj.projectiveSpaceChartPolynomialToHomogeneous,
      Proj.projectiveSpaceDehomogenize, j.down.2]

/-- In particular, chart dehomogenization is surjective. -/
lemma Proj.projectiveSpaceDehomogenize_surjective
    (n : ℕ) (i : Fin (n + 1)) :
    Function.Surjective (Proj.projectiveSpaceDehomogenize n i) := by
  intro p
  refine ⟨Proj.projectiveSpaceChartPolynomialToHomogeneous n i p, ?_⟩
  exact DFunLike.congr_fun
    (Proj.projectiveSpaceChartPolynomialToHomogeneous_comp_dehomogenize n i) p

/-- Homogenize an affine-chart polynomial to its total degree by inserting the
required power of the pivot coordinate in each homogeneous component. -/
noncomputable def Proj.projectiveSpaceChartHomogenize
    (n : ℕ) (i : Fin (n + 1))
    (p : MvPolynomial (ULift.{u} {j : Fin (n + 1) // j ≠ i}) (ULift.{u} ℤ)) :
    MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ) :=
  ∑ d ∈ Finset.range (p.totalDegree + 1),
    Proj.projectiveSpaceChartPolynomialToHomogeneous n i
      (MvPolynomial.homogeneousComponent d p) *
        MvPolynomial.X i ^ (p.totalDegree - d)

/-- Chart homogenization is homogeneous of the total degree of the original
affine polynomial. -/
lemma Proj.projectiveSpaceChartHomogenize_isHomogeneous
    (n : ℕ) (i : Fin (n + 1))
    (p : MvPolynomial (ULift.{u} {j : Fin (n + 1) // j ≠ i}) (ULift.{u} ℤ)) :
    (Proj.projectiveSpaceChartHomogenize n i p).IsHomogeneous p.totalDegree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  rw [Finset.mem_range] at hd
  have hdle : d ≤ p.totalDegree := Nat.lt_succ_iff.mp hd
  convert ((MvPolynomial.homogeneousComponent_isHomogeneous (n := d) (φ := p)).rename_isHomogeneous
      (f := fun j : ULift.{u} {j : Fin (n + 1) // j ≠ i} ↦ j.down.1)).mul
        (MvPolynomial.isHomogeneous_X_pow i (p.totalDegree - d)) using 1
  · rfl
  · exact (Nat.add_sub_of_le hdle).symm

/-- Setting the pivot coordinate to one after chart homogenization recovers the
original affine polynomial. -/
lemma Proj.projectiveSpaceDehomogenize_chartHomogenize
    (n : ℕ) (i : Fin (n + 1))
    (p : MvPolynomial (ULift.{u} {j : Fin (n + 1) // j ≠ i}) (ULift.{u} ℤ)) :
    Proj.projectiveSpaceDehomogenize n i
      (Proj.projectiveSpaceChartHomogenize n i p) = p := by
  have hcomp (q : MvPolynomial (ULift.{u} {j : Fin (n + 1) // j ≠ i}) (ULift.{u} ℤ)) :
      Proj.projectiveSpaceDehomogenize n i
        (Proj.projectiveSpaceChartPolynomialToHomogeneous n i q) = q :=
    DFunLike.congr_fun
      (Proj.projectiveSpaceChartPolynomialToHomogeneous_comp_dehomogenize n i) q
  simp only [Proj.projectiveSpaceChartHomogenize, map_sum, map_mul, map_pow,
    Proj.projectiveSpaceDehomogenize_X_pivot, one_pow, mul_one, hcomp]
  exact MvPolynomial.sum_homogeneousComponent p

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- The dehomogenization map on the pivot coordinate is a unit. -/
lemma Proj.isUnit_projectiveSpaceDehomogenize_X_pivot (n : ℕ) (i : Fin (n + 1)) :
    IsUnit (Proj.projectiveSpaceDehomogenize.{u} n i (MvPolynomial.X i)) := by
  rw [Proj.projectiveSpaceDehomogenize_X_pivot]
  exact isUnit_one

/-- Dehomogenization descends from the homogeneous localization away from `Xᵢ` to the
polynomial ring on the non-pivot variables: `Xⱼ/Xᵢ ↦ Xⱼ`, using that the pivot
dehomogenizes to `1`. -/
noncomputable def Proj.projectiveSpaceAwayToChartPolynomial (n : ℕ) (i : Fin (n + 1)) :
    HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) →+*
      MvPolynomial (ULift.{u} {j : Fin (n + 1) // j ≠ i}) (ULift.{u} ℤ) :=
  (Localization.awayLift (Proj.projectiveSpaceDehomogenize.{u} n i) (MvPolynomial.X i)
      (Proj.isUnit_projectiveSpaceDehomogenize_X_pivot n i)).comp
    (algebraMap _ _)

lemma Proj.projectiveSpaceAwayToChartPolynomial_apply (n : ℕ) (i : Fin (n + 1))
    (z : HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i)) :
    Proj.projectiveSpaceAwayToChartPolynomial n i z =
      Localization.awayLift (Proj.projectiveSpaceDehomogenize.{u} n i)
        (MvPolynomial.X i)
        (Proj.isUnit_projectiveSpaceDehomogenize_X_pivot n i) z.val :=
  rfl

/-- The value of the descended dehomogenization on an honest fraction `a / Xᵢ^m`. -/
lemma Proj.projectiveSpaceAwayLift_mk (n : ℕ) (i : Fin (n + 1))
    (a : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) (m : ℕ) :
    Localization.awayLift (Proj.projectiveSpaceDehomogenize.{u} n i) (MvPolynomial.X i)
        (Proj.isUnit_projectiveSpaceDehomogenize_X_pivot n i)
        (Localization.mk a ⟨MvPolynomial.X i ^ m, by use m⟩) =
      Proj.projectiveSpaceDehomogenize.{u} n i a := by
  set L := Localization.awayLift (Proj.projectiveSpaceDehomogenize.{u} n i)
    (MvPolynomial.X i) (Proj.isUnit_projectiveSpaceDehomogenize_X_pivot n i) with hL
  have hden : L ((algebraMap (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))
      (Localization (Submonoid.powers (MvPolynomial.X i
        (R := ULift.{u} ℤ) (σ := Fin (n + 1)))))) (MvPolynomial.X i ^ m)) = 1 := by
    rw [hL, Localization.awayLift, IsLocalization.Away.lift_eq, map_pow,
      Proj.projectiveSpaceDehomogenize_X_pivot, one_pow]
  have hmk : (Localization.mk a ⟨MvPolynomial.X i ^ m, by use m⟩ :
        Localization (Submonoid.powers (MvPolynomial.X i
          (R := ULift.{u} ℤ) (σ := Fin (n + 1))))) *
      (algebraMap (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) _)
        (MvPolynomial.X i ^ m) =
      (algebraMap (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) _) a := by
    rw [Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ a ⟨MvPolynomial.X i ^ m, by use m⟩
  have happ : L (Localization.mk a ⟨MvPolynomial.X i ^ m, by use m⟩) * 1 =
      Proj.projectiveSpaceDehomogenize.{u} n i a := by
    rw [← hden, ← map_mul, hmk, hL, Localization.awayLift,
      IsLocalization.Away.lift_eq]
  rw [← happ, mul_one]

/-- The value of the descended dehomogenization on `Away.mk`. -/
lemma Proj.projectiveSpaceAwayToChartPolynomial_mk (n : ℕ) (i : Fin (n + 1))
    (m : ℕ) (a : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))
    (ha : a ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) (m • 1)) :
    Proj.projectiveSpaceAwayToChartPolynomial n i
        (HomogeneousLocalization.Away.mk
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i) m a ha) =
      Proj.projectiveSpaceDehomogenize.{u} n i a := by
  have hval : (HomogeneousLocalization.Away.mk
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i) m a ha).val =
      Localization.mk a ⟨MvPolynomial.X i ^ m, by use m⟩ :=
    HomogeneousLocalization.Away.val_mk _ _ _ _ _
  rw [Proj.projectiveSpaceAwayToChartPolynomial_apply, hval]
  exact Proj.projectiveSpaceAwayLift_mk n i a m

/-- Dehomogenizing the canonical chart coordinates recovers the polynomial variables:
the composition of `projectiveSpaceChartPolynomialToAway` with
`projectiveSpaceAwayToChartPolynomial` is the identity. -/
lemma Proj.projectiveSpaceAwayToChartPolynomial_comp_toAway (n : ℕ) (i : Fin (n + 1)) :
    (Proj.projectiveSpaceAwayToChartPolynomial.{u} n i).comp
        (Proj.projectiveSpaceChartPolynomialToAway.{u} n i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply, RingHom.id_apply]
    have hval := Proj.projectiveSpaceChartPolynomialToAway_C_val.{u} n i r
    rw [Proj.projectiveSpaceAwayToChartPolynomial_apply, hval,
      show (⟨1, Submonoid.one_mem _⟩ : Submonoid.powers (MvPolynomial.X i
        (R := ULift.{u} ℤ) (σ := Fin (n + 1)))) =
      ⟨MvPolynomial.X i ^ 0, by use 0⟩ from Subtype.ext (pow_zero _).symm,
      Proj.projectiveSpaceAwayLift_mk n i _ 0, Proj.projectiveSpaceDehomogenize_C]
  · intro j
    rw [RingHom.comp_apply, RingHom.id_apply,
      Proj.projectiveSpaceChartPolynomialToAway_X]
    have hval := Proj.projectiveSpaceChartCoordinate_val.{u} n i j
    rw [Proj.projectiveSpaceAwayToChartPolynomial_apply, hval,
      Proj.projectiveSpaceAwayLift_mk n i _ 1,
      Proj.projectiveSpaceDehomogenize_X_nonpivot n i j.down.1 j.down.2]

/-- Monomial form of the homogenization identity: mapping the dehomogenized monomial
back into the homogeneous localization recovers the fraction `monomial/Xᵢ^degree`. -/
lemma Proj.projectiveSpaceChartPolynomialToAway_dehomogenize_monomial
    (n : ℕ) (i : Fin (n + 1)) (d : Fin (n + 1) →₀ ℕ)
    (r : ULift.{u} ℤ) (m : ℕ) (hd : d.degree = m) :
    (Proj.projectiveSpaceChartPolynomialToAway.{u} n i
        (Proj.projectiveSpaceDehomogenize.{u} n i (MvPolynomial.monomial d r))).val =
      Localization.mk (MvPolynomial.monomial d r)
        ⟨MvPolynomial.X i ^ m, by use m⟩ := by
  classical
  -- dehomogenization of a monomial
  have hdehom : Proj.projectiveSpaceDehomogenize.{u} n i (MvPolynomial.monomial d r) =
      MvPolynomial.C r * ∏ j ∈ d.support,
        (if h : j = i then 1 else MvPolynomial.X (ULift.up ⟨j, h⟩)) ^ d j := by
    rw [show (MvPolynomial.monomial d r :
        MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) =
      MvPolynomial.C r * d.prod fun j e ↦ MvPolynomial.X j ^ e from
        MvPolynomial.monomial_eq]
    rw [map_mul, Proj.projectiveSpaceDehomogenize_C]
    congr 1
    rw [Finsupp.prod, map_prod]
    apply Finset.prod_congr rfl
    intro j _
    rw [map_pow]
    by_cases h : j = i
    · subst h
      rw [Proj.projectiveSpaceDehomogenize_X_pivot]
      simp
    · rw [Proj.projectiveSpaceDehomogenize_X_nonpivot n i j h]
      simp [h]
  rw [hdehom, map_mul, map_prod, HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_prod]
  have hfactor : ∀ j ∈ d.support,
      ((Proj.projectiveSpaceChartPolynomialToAway.{u} n i)
        ((if h : j = i then 1 else MvPolynomial.X (ULift.up ⟨j, h⟩)) ^ d j)).val =
      Localization.mk (MvPolynomial.X j ^ d j)
        ⟨MvPolynomial.X i ^ d j, by use d j⟩ := by
    intro j _
    rw [map_pow]
    exact Proj.projectiveSpaceChartMonomialFactor_val n i j (d j)
  rw [Finset.prod_congr rfl hfactor,
    Proj.projectiveSpaceChartPolynomialToAway_C_val,
    Localization.prod_mk, Localization.mk_mul]
  have hnum : MvPolynomial.C r * ∏ j ∈ d.support,
      (MvPolynomial.X j : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) ^ d j =
      MvPolynomial.monomial d r := by
    rw [show (MvPolynomial.monomial d r :
        MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) =
      MvPolynomial.C r * d.prod fun j e ↦ MvPolynomial.X j ^ e from
        MvPolynomial.monomial_eq]
    rfl
  have hsum : ∑ j ∈ d.support, d j = m := hd
  have hden : ((1 : Submonoid.powers (MvPolynomial.X i
        (R := ULift.{u} ℤ) (σ := Fin (n + 1)))) *
      ∏ j ∈ d.support, (⟨MvPolynomial.X i ^ d j, by use d j⟩ :
        Submonoid.powers (MvPolynomial.X i
          (R := ULift.{u} ℤ) (σ := Fin (n + 1))))) =
      ⟨MvPolynomial.X i ^ m, by use m⟩ := by
    apply Subtype.ext
    push_cast
    rw [one_mul, Finset.prod_pow_eq_pow_sum, hsum]
  rw [show (⟨1, Submonoid.one_mem _⟩ : Submonoid.powers (MvPolynomial.X i
      (R := ULift.{u} ℤ) (σ := Fin (n + 1)))) = 1 from rfl, hden, hnum]

/-- The homogenization identity: `projectiveSpaceChartPolynomialToAway` inverts
dehomogenization on homogeneous polynomials. -/
lemma Proj.projectiveSpaceChartPolynomialToAway_dehomogenize
    (n : ℕ) (i : Fin (n + 1))
    (a : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) (m : ℕ)
    (ha : a.IsHomogeneous m) :
    (Proj.projectiveSpaceChartPolynomialToAway.{u} n i
        (Proj.projectiveSpaceDehomogenize.{u} n i a)).val =
      Localization.mk a ⟨MvPolynomial.X i ^ m, by use m⟩ := by
  classical
  conv_lhs => rw [a.as_sum]
  rw [map_sum, map_sum, HomogeneousLocalization.val_sum]
  have hterm : ∀ d ∈ a.support,
      ((Proj.projectiveSpaceChartPolynomialToAway.{u} n i)
        (Proj.projectiveSpaceDehomogenize.{u} n i
          (MvPolynomial.monomial d (MvPolynomial.coeff d a)))).val =
      Localization.mk (MvPolynomial.monomial d (MvPolynomial.coeff d a))
        ⟨MvPolynomial.X i ^ m, by use m⟩ := by
    intro d hd
    apply Proj.projectiveSpaceChartPolynomialToAway_dehomogenize_monomial
    exact (ha.degree_eq_sum_deg_support hd).symm
  rw [Finset.sum_congr rfl hterm, Localization.sum_mk]
  congr 1
  exact a.as_sum.symm

/-- The affine-chart coordinate ring maps onto the homogeneous localization. -/
theorem Proj.projectiveSpaceChartPolynomialToAway_surjective (n : ℕ) (i : Fin (n + 1)) :
    Function.Surjective (Proj.projectiveSpaceChartPolynomialToAway.{u} n i) := by
  intro z
  obtain ⟨m, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i) z
  refine ⟨Proj.projectiveSpaceDehomogenize.{u} n i a, ?_⟩
  apply HomogeneousLocalization.val_injective
  rw [Proj.projectiveSpaceChartPolynomialToAway_dehomogenize n i a m (by
    simpa [MvPolynomial.mem_homogeneousSubmodule] using ha),
    HomogeneousLocalization.Away.val_mk]

/-- The affine-chart coordinate ring embeds into the homogeneous localization. -/
theorem Proj.projectiveSpaceChartPolynomialToAway_injective (n : ℕ) (i : Fin (n + 1)) :
    Function.Injective (Proj.projectiveSpaceChartPolynomialToAway.{u} n i) := by
  have hleft := Proj.projectiveSpaceAwayToChartPolynomial_comp_toAway.{u} n i
  intro p q hpq
  have := congrArg (Proj.projectiveSpaceAwayToChartPolynomial.{u} n i) hpq
  rwa [← RingHom.comp_apply, ← RingHom.comp_apply, hleft, RingHom.id_apply,
    RingHom.id_apply] at this

/-- **The chart coordinate ring of projective space**: the polynomial ring on the
non-pivot variables is isomorphic to the degree-zero homogeneous localization at the
pivot coordinate — the coordinate ring of the standard chart `D₊(Xᵢ) ⊆ ℙⁿ`. -/
noncomputable def Proj.projectiveSpaceChartPolynomialEquivAway (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial (ULift.{u} {j : Fin (n + 1) // j ≠ i}) (ULift.{u} ℤ) ≃+*
      HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) :=
  RingEquiv.ofBijective (Proj.projectiveSpaceChartPolynomialToAway.{u} n i)
    ⟨Proj.projectiveSpaceChartPolynomialToAway_injective n i,
      Proj.projectiveSpaceChartPolynomialToAway_surjective n i⟩

/-- The involution of a polynomial ring sending every variable to its negative. -/
noncomputable def Proj.grassmannianChartSignRingHom (m : Type u) :
    MvPolynomial m (ULift.{u} ℤ) →+* MvPolynomial m (ULift.{u} ℤ) :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j ↦ -MvPolynomial.X j)

@[simp]
lemma Proj.grassmannianChartSignRingHom_C (m : Type u) (r : ULift.{u} ℤ) :
    Proj.grassmannianChartSignRingHom m (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [Proj.grassmannianChartSignRingHom]

@[simp]
lemma Proj.grassmannianChartSignRingHom_X (m : Type u) (j : m) :
    Proj.grassmannianChartSignRingHom m (MvPolynomial.X j) = -MvPolynomial.X j := by
  simp [Proj.grassmannianChartSignRingHom]

/-- Negating every polynomial variable is an involutive ring equivalence. -/
noncomputable def Proj.grassmannianChartSignEquiv (m : Type u) :
    MvPolynomial m (ULift.{u} ℤ) ≃+* MvPolynomial m (ULift.{u} ℤ) := by
  let φ := Proj.grassmannianChartSignRingHom m
  have hφ : φ.comp φ = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [φ]
    · intro j
      simp [φ]
  have hleft : Function.LeftInverse φ φ := fun p ↦ by
    simpa only [RingHom.comp_apply, RingHom.id_apply] using DFunLike.congr_fun hφ p
  exact RingEquiv.ofBijective φ ⟨hleft.injective, hleft.surjective⟩

@[simp]
lemma Proj.grassmannianChartSignEquiv_X (m : Type u) (j : m) :
    Proj.grassmannianChartSignEquiv m (MvPolynomial.X j) = -MvPolynomial.X j := by
  change Proj.grassmannianChartSignRingHom m (MvPolynomial.X j) = _
  simp

/-- The matrix-coordinate ring of the rank-one Grassmannian chart is the degree-zero
homogeneous localization defining the corresponding projective chart. -/
noncomputable def Proj.rankOneGrassmannianChartPolynomialEquivAway
    (n : ℕ) (i : Fin (n + 1)) :
    MvPolynomial
        (ULift.{u} (↑({i} : Finset (Fin (n + 1))) ×
          ↑(({i} : Finset (Fin (n + 1)))ᶜ))) (ULift.{u} ℤ) ≃+*
      HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) :=
  (Proj.grassmannianChartSignEquiv _).trans
    ((Proj.rankOneGrassmannianChartPolynomialEquiv n i).toRingEquiv.trans
      (Proj.projectiveSpaceChartPolynomialEquivAway n i))

/-- Under the comparison, a Grassmannian graph coordinate is the negative of the
corresponding homogeneous quotient coordinate.  The sign is forced by the convention
that `coordinateGraph` describes the kernel rather than the quotient matrix. -/
@[simp]
lemma Proj.rankOneGrassmannianChartPolynomialEquivAway_X
    (n : ℕ) (i : Fin (n + 1))
    (j : ULift.{u} (↑({i} : Finset (Fin (n + 1))) ×
      ↑(({i} : Finset (Fin (n + 1)))ᶜ))) :
    Proj.rankOneGrassmannianChartPolynomialEquivAway n i (MvPolynomial.X j) =
      -Proj.projectiveSpaceChartCoordinate n i
        (Proj.rankOneGrassmannianChartCoordinateEquiv n i j) := by
  change Proj.projectiveSpaceChartPolynomialToAway.{u} n i
      ((Proj.rankOneGrassmannianChartPolynomialEquiv n i)
        (Proj.grassmannianChartSignEquiv _ (MvPolynomial.X j))) = _
  rw [Proj.grassmannianChartSignEquiv_X, map_neg, map_neg]
  rw [show (Proj.rankOneGrassmannianChartPolynomialEquiv n i) (MvPolynomial.X j) =
    MvPolynomial.X (Proj.rankOneGrassmannianChartCoordinateEquiv n i j) from by
      simp [Proj.rankOneGrassmannianChartPolynomialEquiv]]
  rw [Proj.projectiveSpaceChartPolynomialToAway_X]

/-- Affine space carries an isomorphism of base schemes to an isomorphism. -/
noncomputable def AffineSpace.mapIso (m : Type u) {S T : Scheme.{u}} (e : S ≅ T) :
    AffineSpace m S ≅ AffineSpace m T where
  hom := AffineSpace.map m e.hom
  inv := AffineSpace.map m e.inv
  hom_inv_id := by rw [← AffineSpace.map_comp, e.hom_inv_id, AffineSpace.map_id]
  inv_hom_id := by rw [← AffineSpace.map_comp, e.inv_hom_id, AffineSpace.map_id]

/-- The represented rank-one Grassmannian chart is canonically the spectrum of
its matrix-coordinate polynomial ring. -/
noncomputable def Proj.rankOneGrassmannianChartSchemeIsoSpec
    (n : ℕ) (i : Fin (n + 1)) :
    Scheme.grassmannianChartCoverScheme 1 (n + 1)
        (Proj.rankOneGrassmannianChartIndex n i) ≅
      Spec (CommRingCat.of (MvPolynomial
        (ULift.{u} (↑({i} : Finset (Fin (n + 1))) ×
          ↑(({i} : Finset (Fin (n + 1)))ᶜ))) (ULift.{u} ℤ))) :=
  AffineSpace.mapIso _
      (terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal) ≪≫
    AffineSpace.SpecIso _ (CommRingCat.of (ULift.{u} ℤ))

/-- The standard projective chart is isomorphic to the represented rank-one
Grassmannian chart with the same pivot coordinate. -/
noncomputable def Proj.projectiveSpaceChartIsoRankOneGrassmannianChart
    (n : ℕ) (i : Fin (n + 1)) :
    (Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i)).toScheme ≅
      Scheme.grassmannianChartCoverScheme 1 (n + 1)
        (Proj.rankOneGrassmannianChartIndex n i) :=
  Proj.basicOpenIsoSpec
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos ≪≫
    Scheme.Spec.mapIso
      (Proj.rankOneGrassmannianChartPolynomialEquivAway n i).toCommRingCatIso.op ≪≫
    (Proj.rankOneGrassmannianChartSchemeIsoSpec n i).symm

/-- The canonical morphism from a standard projective chart to the glued rank-one
Grassmannian, through the chart isomorphism. -/
noncomputable def Proj.projectiveSpaceChartToRankOneGrassmannian
    (n : ℕ) (i : Fin (n + 1)) :
    (Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i)).toScheme ⟶
      (Scheme.grassmannianGlueData 1 (n + 1)).glued :=
  (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).hom ≫
    (Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
      (Proj.rankOneGrassmannianChartIndex n i)

/-- A morphism through a represented standard chart is classified by the
corresponding chart point after inclusion into the Grassmannian functor. -/
lemma Scheme.grassmannianGluedRepresentation_comp_openCover
    (q n : ℕ) (I : Scheme.grassmannianChartCoverIndex.{u} q n)
    {T : Scheme.{u}}
    (f : T ⟶ Scheme.grassmannianChartCoverScheme q n I) :
    (Scheme.grassmannianGluedRepresentation q n).homEquiv
        (f ≫ (Scheme.grassmannianGlueData q n).openCover.f I) =
      ((Scheme.grassmannianChartCoverRepresentation q n I).homEquiv f).1 := by
  have h := Scheme.yoneda_map_grassmannianGlueData_openCover.{u} q n I
  have h2 := congrArg (fun η ↦ η.app (op T) f) h
  simp only [NatTrans.comp_app, types_comp_apply] at h2
  have hL : ((Scheme.grassmannianGluedRepresentation q n).toIso.hom.app (op T))
      ((yoneda.map ((Scheme.grassmannianGlueData q n).openCover.f I)).app (op T) f) =
      (Scheme.grassmannianGluedRepresentation q n).homEquiv
        (f ≫ (Scheme.grassmannianGlueData q n).openCover.f I) := rfl
  have hR : (Scheme.grassmannianRepresentableChartMap q n I).app (op T) f =
      ((Scheme.grassmannianChartCoverRepresentation q n I).homEquiv f).1 := rfl
  rw [hL] at h2
  exact h2.trans hR

/-- The morphism from a standard projective chart to the glued Grassmannian is
classified by the chart point of the comparison isomorphism. -/
theorem Proj.grassmannianGluedRepresentation_projectiveSpaceChartToRankOneGrassmannian
    (n : ℕ) (i : Fin (n + 1)) :
    (Scheme.grassmannianGluedRepresentation 1 (n + 1)).homEquiv
        (Proj.projectiveSpaceChartToRankOneGrassmannian n i) =
      ((Scheme.grassmannianChartCoverRepresentation 1 (n + 1)
        (Proj.rankOneGrassmannianChartIndex n i)).homEquiv
          (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).hom).1 :=
  Scheme.grassmannianGluedRepresentation_comp_openCover 1 (n + 1)
    (Proj.rankOneGrassmannianChartIndex n i)
    (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).hom

-- Cross-pivot comparison machinery for the overlap agreement of the chart
-- morphisms (support for the comparison `ℙⁿ ≅ Gr(1, n+1)`).
end AlgebraicGeometry.ProjectiveSpectrum

namespace AlgebraicGeometry.Scheme

/-- Membership in a rank-one coordinate graph, rewritten through the total function
extending the coordinate matrix by zero at the pivot. -/
lemma mem_coordinateGraph_singleton_iff_total {R : Type*} [CommRing R] {n : ℕ}
    {i : Fin n}
    (bi : (i' : ↑({i} : Finset (Fin n))) → (k : ↑(({i} : Finset (Fin n))ᶜ)) → R)
    (v : Fin n → R) :
    v ∈ coordinateGraph ({i} : Finset (Fin n)) bi ↔
      v i = ∑ k, (if h : k = i then 0
        else bi ⟨i, Finset.mem_singleton_self i⟩
          ⟨k, Finset.mem_compl.mpr (by simp [h])⟩) * v k := by
  classical
  set ci : Fin n → R := fun k ↦ if h : k = i then 0
    else bi ⟨i, Finset.mem_singleton_self i⟩
      ⟨k, Finset.mem_compl.mpr (by simp [h])⟩ with hci
  have hstep1 : ∑ k : ↑(({i} : Finset (Fin n))ᶜ),
      bi ⟨i, Finset.mem_singleton_self i⟩ k * v k.1 =
      ∑ k : ↑(({i} : Finset (Fin n))ᶜ), ci k.1 * v k.1 := by
    apply Finset.sum_congr rfl
    intro k _
    have hk : k.1 ≠ i := by
      have h2 := k.2
      rw [Finset.mem_compl, Finset.mem_singleton] at h2
      exact h2
    rw [hci]
    simp only [hk]
    simp
  have hstep2 : ∑ k : ↑(({i} : Finset (Fin n))ᶜ), ci k.1 * v k.1 =
      ∑ k ∈ ({i} : Finset (Fin n))ᶜ, ci k * v k :=
    Finset.sum_coe_sort (({i} : Finset (Fin n))ᶜ) (fun k ↦ ci k * v k)
  have hstep3 : ∑ k ∈ ({i} : Finset (Fin n)), ci k * v k = 0 := by
    rw [Finset.sum_singleton, hci]
    simp
  have hsum : ∑ k : ↑(({i} : Finset (Fin n))ᶜ),
      bi ⟨i, Finset.mem_singleton_self i⟩ k * v k.1 = ∑ k, ci k * v k := by
    rw [hstep1, hstep2, ← Finset.sum_add_sum_compl ({i} : Finset (Fin n))
      (fun k ↦ ci k * v k), hstep3, zero_add]
  constructor
  · intro hv
    rw [← hsum]
    exact hv i (Finset.mem_singleton_self i)
  · intro hv i' hi'
    rw [Finset.mem_singleton] at hi'
    subst hi'
    rw [hsum]
    exact hv

/-- The elementary form of the cross-pivot inclusion: if the total coordinate
functions of two rank-one graphs are compatible, a solution of the pivot-`i`
equation solves the pivot-`j` equation. -/
lemma pivot_equation_of_pivot_equation {R : Type*} [CommRing R] {n : ℕ}
    {i j : Fin n} (hij : i ≠ j) (ci cj : Fin n → R)
    (h0i : ci i = 0) (h0j : cj j = 0) (h1 : ci j * cj i = 1)
    (h2 : ∀ k, k ≠ i → k ≠ j → ci j * cj k = -ci k)
    (v : Fin n → R) (hv : v i = ∑ k, ci k * v k) :
    v j = ∑ k, cj k * v k := by
  classical
  have hF : ∑ k, ((ci j * cj k) + ci k) * v k = v i + ci j * v j := by
    rw [Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij
      (fun c _ hc ↦ by rw [h2 c hc.1 hc.2]; ring)]
    rw [h1, h0i, h0j]
    ring
  have hexp : ∑ k, ((ci j * cj k) + ci k) * v k =
      ci j * ∑ k, cj k * v k + ∑ k, ci k * v k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h3 : ci j * ∑ k, cj k * v k + ∑ k, ci k * v k = v i + ci j * v j := by
    rw [← hexp, hF]
  rw [← hv] at h3
  rw [add_comm (ci j * ∑ k, cj k * v k) (v i)] at h3
  have h4 : ci j * ∑ k, cj k * v k = ci j * v j := add_left_cancel h3
  have h5 : cj i * (ci j * ∑ k, cj k * v k) = cj i * (ci j * v j) := by rw [h4]
  rw [← mul_assoc, ← mul_assoc, mul_comm (cj i) (ci j), h1, one_mul, one_mul] at h5
  exact h5.symm

/-- **Cross-pivot comparison of rank-one coordinate graphs**: two rank-one graphs with
pivots `i ≠ j` agree as soon as the cross-entries multiply to `1` and the remaining
entries are proportional (with the sign forced by the graph convention). -/
lemma coordinateGraph_singleton_eq_of_mul {R : Type*} [CommRing R] {n : ℕ}
    {i j : Fin n} (hij : i ≠ j)
    (bi : (i' : ↑({i} : Finset (Fin n))) → (k : ↑(({i} : Finset (Fin n))ᶜ)) → R)
    (bj : (j' : ↑({j} : Finset (Fin n))) → (k : ↑(({j} : Finset (Fin n))ᶜ)) → R)
    (h1 : bi ⟨i, Finset.mem_singleton_self i⟩
        ⟨j, Finset.mem_compl.mpr (by simp [hij.symm])⟩ *
      bj ⟨j, Finset.mem_singleton_self j⟩
        ⟨i, Finset.mem_compl.mpr (by simp [hij])⟩ = 1)
    (h2 : ∀ (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j),
      bi ⟨i, Finset.mem_singleton_self i⟩
          ⟨j, Finset.mem_compl.mpr (by simp [hij.symm])⟩ *
        bj ⟨j, Finset.mem_singleton_self j⟩
          ⟨k, Finset.mem_compl.mpr (by simp [hkj])⟩ =
      -bi ⟨i, Finset.mem_singleton_self i⟩
        ⟨k, Finset.mem_compl.mpr (by simp [hki])⟩) :
    coordinateGraph ({i} : Finset (Fin n)) bi =
      coordinateGraph ({j} : Finset (Fin n)) bj := by
  classical
  have hji : j ≠ i := hij.symm
  ext v
  rw [mem_coordinateGraph_singleton_iff_total bi v,
    mem_coordinateGraph_singleton_iff_total bj v]
  constructor
  · intro hv
    refine pivot_equation_of_pivot_equation hij _ _ ?_ ?_ ?_ ?_ v hv
    · simp
    · simp
    · simp only [dif_neg hji, dif_neg hij]
      exact h1
    · intro k hki hkj
      simp only [dif_neg hji, dif_neg hkj, dif_neg hki]
      exact h2 k hki hkj
  · intro hv
    refine pivot_equation_of_pivot_equation hji _ _ ?_ ?_ ?_ ?_ v hv
    · simp
    · simp
    · simp only [dif_neg hji, dif_neg hij]
      rw [mul_comm]
      exact h1
    · intro k hkj hki
      simp only [dif_neg hij, dif_neg hkj, dif_neg hki]
      -- derive the symmetric proportionality from `h1` and `h2`
      have hstep := h2 k hki hkj
      have hmul := congrArg (fun t ↦ bj ⟨j, Finset.mem_singleton_self j⟩
        ⟨i, Finset.mem_compl.mpr (by simp [hij])⟩ * t) hstep
      rw [← mul_assoc, mul_comm (bj ⟨j, Finset.mem_singleton_self j⟩
          ⟨i, Finset.mem_compl.mpr (by simp [hij])⟩)
          (bi ⟨i, Finset.mem_singleton_self i⟩
            ⟨j, Finset.mem_compl.mpr (by simp [hij.symm])⟩),
        h1, one_mul, mul_neg] at hmul
      rw [hmul]
      ring

/-- **Cross-pivot comparison of rank-one graph data**: the scheme-level form of
`coordinateGraph_singleton_eq_of_mul`, with the compatibility hypotheses imposed on
global sections. -/
lemma coordinateGraphData_singleton_eq_of_mul {X : Scheme.{u}} {n : ℕ}
    {i j : Fin n} (hij : i ≠ j)
    (ai : (i' : ↑({i} : Finset (Fin n))) → (k : ↑(({i} : Finset (Fin n))ᶜ)) → Γ(X, ⊤))
    (aj : (j' : ↑({j} : Finset (Fin n))) → (k : ↑(({j} : Finset (Fin n))ᶜ)) → Γ(X, ⊤))
    (h1 : ai ⟨i, Finset.mem_singleton_self i⟩
        ⟨j, Finset.mem_compl.mpr (by simp [hij.symm])⟩ *
      aj ⟨j, Finset.mem_singleton_self j⟩
        ⟨i, Finset.mem_compl.mpr (by simp [hij])⟩ = 1)
    (h2 : ∀ (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j),
      ai ⟨i, Finset.mem_singleton_self i⟩
          ⟨j, Finset.mem_compl.mpr (by simp [hij.symm])⟩ *
        aj ⟨j, Finset.mem_singleton_self j⟩
          ⟨k, Finset.mem_compl.mpr (by simp [hkj])⟩ =
      -ai ⟨i, Finset.mem_singleton_self i⟩
        ⟨k, Finset.mem_compl.mpr (by simp [hki])⟩) :
    coordinateGraphData X ({i} : Finset (Fin n)) ai =
      coordinateGraphData X ({j} : Finset (Fin n)) aj := by
  apply SubmoduleSheafData.ext
  funext U
  rw [coordinateGraphData_submodule, coordinateGraphData_submodule]
  set ρ := (X.presheaf.map (homOfLE (le_top (a := U.1))).op).hom with hρ
  apply coordinateGraph_singleton_eq_of_mul hij
  · change ρ _ * ρ _ = 1
    rw [← map_mul, ← map_one ρ]
    exact congrArg ρ h1
  · intro k hki hkj
    change ρ _ * ρ _ = -ρ _
    rw [← map_mul, ← map_neg ρ]
    exact congrArg ρ (h2 k hki hkj)
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProjectiveSpectrum

attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicGeometry.Scheme

/-- The realization of the homogeneous localization at a pivot coordinate as global
sections of the standard chart scheme. -/
noncomputable def Proj.awayToChartSections (n : ℕ) (i : Fin (n + 1)) :
    CommRingCat.of (HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i)) ⟶
      Γ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i)).toScheme, ⊤) :=
  AlgebraicGeometry.Proj.awayToSection _ (MvPolynomial.X i) ≫
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i)).topIso.inv

/-- The coordinate through the chart-scheme/Spec identification. -/
lemma Proj.rankOneGrassmannianChartSchemeIsoSpec_inv_appTop_coord
    (n : ℕ) (i : Fin (n + 1))
    (p : ULift.{u} (↑({i} : Finset (Fin (n + 1))) ×
      ↑(({i} : Finset (Fin (n + 1)))ᶜ))) :
    ((Proj.rankOneGrassmannianChartSchemeIsoSpec n i).inv.appTop).hom
      (AffineSpace.coord (⊤_ Scheme.{u}) p) =
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial
      (ULift.{u} (↑({i} : Finset (Fin (n + 1))) ×
        ↑(({i} : Finset (Fin (n + 1)))ᶜ))) (ULift.{u} ℤ)))).inv
      (MvPolynomial.X p) := by
  show ((AffineSpace.SpecIso _ (CommRingCat.of (ULift.{u} ℤ))).inv ≫
      AffineSpace.map _
        (terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal).inv).appTop.hom
    (AffineSpace.coord (⊤_ Scheme.{u}) p) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  rw [show ((AffineSpace.map _
      (terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal).inv).appTop).hom
      (AffineSpace.coord (⊤_ Scheme.{u}) p) =
    AffineSpace.coord (Spec (CommRingCat.of (ULift.{u} ℤ))) p from
      AffineSpace.map_appTop_coord _ p]
  exact AffineSpace.SpecIso_inv_appTop_coord (CommRingCat.of (ULift.{u} ℤ)) p

/-- The coordinate pullback along the chart isomorphism: the affine-space coordinate
pulls back to the section of the corresponding matrix-coordinate fraction. -/
lemma Proj.chartIso_hom_appTop_coord (n : ℕ) (i : Fin (n + 1))
    (p : ULift.{u} (↑({i} : Finset (Fin (n + 1))) ×
      ↑(({i} : Finset (Fin (n + 1)))ᶜ))) :
    (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).hom.appTop.hom
      (AffineSpace.coord (⊤_ Scheme.{u}) p) =
    (Proj.awayToChartSections n i).hom
      (Proj.rankOneGrassmannianChartPolynomialEquivAway n i (MvPolynomial.X p)) := by
  -- unfold the composite isomorphism
  have hhom : (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).hom =
      (Proj.basicOpenIsoSpec
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos).hom ≫
        Spec.map (CommRingCat.ofHom
          (Proj.rankOneGrassmannianChartPolynomialEquivAway n i).toRingHom) ≫
        (Proj.rankOneGrassmannianChartSchemeIsoSpec n i).inv := rfl
  rw [hhom]
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply]
  rw [Proj.rankOneGrassmannianChartSchemeIsoSpec_inv_appTop_coord]
  -- step 2: naturality of the global-sections isomorphism
  have hstep2 : ((Spec.map (CommRingCat.ofHom
      (Proj.rankOneGrassmannianChartPolynomialEquivAway n i).toRingHom)).appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial
        (ULift.{u} (↑({i} : Finset (Fin (n + 1))) ×
          ↑(({i} : Finset (Fin (n + 1)))ᶜ))) (ULift.{u} ℤ)))).inv
        (MvPolynomial.X p)) =
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i)))).inv
        (Proj.rankOneGrassmannianChartPolynomialEquivAway n i (MvPolynomial.X p)) := by
    have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (Proj.rankOneGrassmannianChartPolynomialEquivAway n i).toRingHom)
    have h2 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hnat)
      (MvPolynomial.X p)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    exact h2.symm
  rw [hstep2]
  -- step 3: through the basic-open/Spec identification into chart sections
  have hstep3 : (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i)))).inv ≫
      (Proj.basicOpenIsoSpec
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i)
        Nat.one_pos).hom.appTop = Proj.awayToChartSections n i := by
    rw [Proj.basicOpenIsoSpec_hom
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos,
      AlgebraicGeometry.Proj.basicOpenToSpec, Scheme.Hom.comp_appTop]
    rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      Scheme.Opens.toSpecΓ_appTop, Iso.inv_hom_id_assoc]
    rfl
  rw [← CommRingCat.comp_apply, hstep3]

/-- The classified point of a morphism into a standard chart scheme is the coordinate
graph of the pulled-back affine coordinates. -/
lemma homEquiv_grassmannianChartCoverRepresentation {q n : ℕ}
    (I : Scheme.grassmannianChartCoverIndex.{u} q n) {X : Scheme.{u}}
    (g : X ⟶ Scheme.grassmannianChartCoverScheme q n I) :
    (Scheme.grassmannianChartCoverRepresentation q n I).homEquiv g =
      Scheme.coordinateMatrixChartPoint q n I.down.1 X I.down.2
        (fun i' j' ↦ g.appTop.hom
          (AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (i', j')))) :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Restriction along `homOfLE` on top sections is the presheaf restriction, through
the top-sections isomorphisms. -/
lemma topIso_inv_homOfLE_appTop {X : Scheme.{u}} {U V : X.Opens} (e : V ≤ U) :
    U.topIso.inv ≫ (X.homOfLE e).appTop =
      X.presheaf.map (homOfLE e).op ≫ V.topIso.inv := by
  rw [Scheme.Hom.appTop, Scheme.homOfLE_app]
  simp only [Scheme.Opens.topIso_inv]
  exact ((X.presheaf.map_comp _ _).symm.trans
    (Eq.trans (by congr 1) (X.presheaf.map_comp _ _)))

/-- The transport of a chart coordinate to the overlap localization: under
`awayMap` into the localization at `Xᵢ Xⱼ`, the fraction `Xₖ/Xᵢ` becomes
`XₖXⱼ/XᵢXⱼ`. -/
lemma Proj.awayMap_projectiveSpaceChartCoordinate (n : ℕ) (i j : Fin (n + 1))
    {x : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)}
    (hx : x = MvPolynomial.X i * MvPolynomial.X j)
    (k : ULift.{u} {k : Fin (n + 1) // k ≠ i}) :
    (HomogeneousLocalization.awayMap
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) hx
        (Proj.projectiveSpaceChartCoordinate n i k)).val =
      Localization.mk (MvPolynomial.X k.down.1 * MvPolynomial.X j)
        ⟨x ^ 1, by use 1⟩ := by
  have h := HomogeneousLocalization.val_awayMap_mk
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) hx
    ((1 : ℕ) • (1 : ℕ)) ⟨MvPolynomial.X k.down.1, by
      simpa using MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) k.down.1⟩ 1
    (SetLike.pow_mem_graded 1 (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i))
  refine Eq.trans ?_ (Eq.trans h ?_)
  · rfl
  · congr 1
    rw [pow_one]

/-- The cross-product identity on the overlap: `(Xⱼ/Xᵢ)·(Xᵢ/Xⱼ) = 1` in the
localization at `XᵢXⱼ`. -/
lemma Proj.awayMap_chartCoordinate_mul_cross (n : ℕ) {i j : Fin (n + 1)}
    (hij : i ≠ j) :
    HomogeneousLocalization.awayMap
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j)
        (rfl : MvPolynomial.X i * MvPolynomial.X j = _)
        (Proj.projectiveSpaceChartCoordinate n i (ULift.up ⟨j, hij.symm⟩)) *
      HomogeneousLocalization.awayMap
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)
        (mul_comm (MvPolynomial.X i (R := ULift.{u} ℤ) (σ := Fin (n + 1)))
          (MvPolynomial.X j))
        (Proj.projectiveSpaceChartCoordinate n j (ULift.up ⟨i, hij⟩)) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one,
    Proj.awayMap_projectiveSpaceChartCoordinate n i j rfl,
    Proj.awayMap_projectiveSpaceChartCoordinate n j i
      (mul_comm (MvPolynomial.X i) (MvPolynomial.X j)),
    Localization.mk_mul]
  rw [show (1 : Localization (Submonoid.powers
      (MvPolynomial.X i * MvPolynomial.X j
        (R := ULift.{u} ℤ) (σ := Fin (n + 1))))) =
    Localization.mk 1 1 from Localization.mk_one.symm]
  rw [Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  push_cast
  ring

/-- The transitivity identity on the overlap: `(Xⱼ/Xᵢ)·(Xₖ/Xⱼ) = Xₖ/Xᵢ` in the
localization at `XᵢXⱼ`. -/
lemma Proj.awayMap_chartCoordinate_mul_trans (n : ℕ) {i j k : Fin (n + 1)}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    HomogeneousLocalization.awayMap
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j)
        (rfl : MvPolynomial.X i * MvPolynomial.X j = _)
        (Proj.projectiveSpaceChartCoordinate n i (ULift.up ⟨j, hij.symm⟩)) *
      HomogeneousLocalization.awayMap
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)
        (mul_comm (MvPolynomial.X i (R := ULift.{u} ℤ) (σ := Fin (n + 1)))
          (MvPolynomial.X j))
        (Proj.projectiveSpaceChartCoordinate n j (ULift.up ⟨k, hkj⟩)) =
      HomogeneousLocalization.awayMap
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j)
        (rfl : MvPolynomial.X i * MvPolynomial.X j = _)
        (Proj.projectiveSpaceChartCoordinate n i (ULift.up ⟨k, hki⟩)) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul,
    Proj.awayMap_projectiveSpaceChartCoordinate n i j rfl,
    Proj.awayMap_projectiveSpaceChartCoordinate n j i
      (mul_comm (MvPolynomial.X i) (MvPolynomial.X j)),
    Proj.awayMap_projectiveSpaceChartCoordinate n i j rfl,
    Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  push_cast
  ring

/-- The section of the overlap `D₊(XᵢXⱼ)` attached to an element of the homogeneous
localization at `XᵢXⱼ`. -/
noncomputable def Proj.overlapToSections (n : ℕ) (i j : Fin (n + 1)) :
    CommRingCat.of (HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i * MvPolynomial.X j)) ⟶
      Γ((Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i * MvPolynomial.X j)).toScheme, ⊤) :=
  AlgebraicGeometry.Proj.awayToSection _ (MvPolynomial.X i * MvPolynomial.X j) ≫
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i * MvPolynomial.X j)).topIso.inv

/-- Restriction of a pivot-chart section to the overlap: the chart-sections
realization commutes with `awayMap` into the overlap localization. -/
lemma Proj.homOfLE_appTop_awayToChartSections (n : ℕ) (i j : Fin (n + 1))
    (hle : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ)) (MvPolynomial.X i * MvPolynomial.X j) ≤
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i))
    (z : HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i)) :
    ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE hle).appTop.hom
      ((Proj.awayToChartSections n i).hom z) =
    (Proj.overlapToSections n i j).hom
      (HomogeneousLocalization.awayMap
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) rfl z) := by
  -- restriction through the top-sections isomorphism
  have h1 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (topIso_inv_homOfLE_appTop (X := Proj (MvPolynomial.homogeneousSubmodule
      (Fin (n + 1)) (ULift.{u} ℤ))) hle))
    ((AlgebraicGeometry.Proj.awayToSection _ (MvPolynomial.X i)).hom z)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
  change ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ))).homOfLE hle).appTop.hom
    ((Proj.basicOpen _ (MvPolynomial.X i)).topIso.inv.hom
      ((AlgebraicGeometry.Proj.awayToSection _ (MvPolynomial.X i)).hom z)) = _
  rw [h1]
  -- the presheaf restriction of `awayToSection` is `awayToSection` of `awayMap`
  have h2 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (AlgebraicGeometry.Proj.awayMap_awayToSection
      (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j)
      (rfl : MvPolynomial.X i * MvPolynomial.X j = _))) z
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  have h3 : ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ))).presheaf.map (homOfLE hle).op).hom
      ((AlgebraicGeometry.Proj.awayToSection _ (MvPolynomial.X i)).hom z) =
      (AlgebraicGeometry.Proj.awayToSection _
        (MvPolynomial.X i * MvPolynomial.X j)).hom
        (HomogeneousLocalization.awayMap
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) rfl z) := by
    rw [show (homOfLE hle : (Proj.basicOpen (MvPolynomial.homogeneousSubmodule
        (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i * MvPolynomial.X j)) ⟶
        Proj.basicOpen _ (MvPolynomial.X i)) =
      homOfLE (AlgebraicGeometry.Proj.basicOpen_mono _ _ _
        ⟨MvPolynomial.X j, rfl⟩) from rfl]
    exact h2.symm
  rw [h3]
  rfl

/-- Variant of `homOfLE_appTop_awayToChartSections` for the second pivot of the
overlap. -/
lemma Proj.homOfLE_appTop_awayToChartSections' (n : ℕ) (i j : Fin (n + 1))
    (hle : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ)) (MvPolynomial.X i * MvPolynomial.X j) ≤
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X j))
    (z : HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X j)) :
    ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE hle).appTop.hom
      ((Proj.awayToChartSections n j).hom z) =
    (Proj.overlapToSections n i j).hom
      (HomogeneousLocalization.awayMap
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)
        (mul_comm (MvPolynomial.X i (R := ULift.{u} ℤ) (σ := Fin (n + 1)))
          (MvPolynomial.X j)) z) := by
  have h1 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (topIso_inv_homOfLE_appTop (X := Proj (MvPolynomial.homogeneousSubmodule
      (Fin (n + 1)) (ULift.{u} ℤ))) hle))
    ((AlgebraicGeometry.Proj.awayToSection _ (MvPolynomial.X j)).hom z)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
  change ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ))).homOfLE hle).appTop.hom
    ((Proj.basicOpen _ (MvPolynomial.X j)).topIso.inv.hom
      ((AlgebraicGeometry.Proj.awayToSection _ (MvPolynomial.X j)).hom z)) = _
  rw [h1]
  have h2 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (AlgebraicGeometry.Proj.awayMap_awayToSection
      (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)
      (mul_comm (MvPolynomial.X i (R := ULift.{u} ℤ) (σ := Fin (n + 1)))
        (MvPolynomial.X j)))) z
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  have h3 : ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ))).presheaf.map (homOfLE hle).op).hom
      ((AlgebraicGeometry.Proj.awayToSection _ (MvPolynomial.X j)).hom z) =
      (AlgebraicGeometry.Proj.awayToSection _
        (MvPolynomial.X i * MvPolynomial.X j)).hom
        (HomogeneousLocalization.awayMap
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)
          (mul_comm (MvPolynomial.X i (R := ULift.{u} ℤ) (σ := Fin (n + 1)))
            (MvPolynomial.X j)) z) := by
    rw [show (homOfLE hle : (Proj.basicOpen (MvPolynomial.homogeneousSubmodule
        (Fin (n + 1)) (ULift.{u} ℤ)) (MvPolynomial.X i * MvPolynomial.X j)) ⟶
        Proj.basicOpen _ (MvPolynomial.X j)) =
      homOfLE (AlgebraicGeometry.Proj.basicOpen_mono _ _ _
        ⟨MvPolynomial.X i, mul_comm (MvPolynomial.X i
          (R := ULift.{u} ℤ) (σ := Fin (n + 1))) (MvPolynomial.X j)⟩) from rfl]
    exact h2.symm
  rw [h3]
  rfl

/-- The restricted chart matrix entry on the overlap, in terms of the overlap
localization. -/
lemma Proj.overlap_chart_entry (n : ℕ) (i j : Fin (n + 1))
    (hle : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ)) (MvPolynomial.X i * MvPolynomial.X j) ≤
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i))
    (i' : ↑({i} : Finset (Fin (n + 1)))) (k : ↑(({i} : Finset (Fin (n + 1)))ᶜ)) :
    (((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE hle ≫
      (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).hom).appTop).hom
        (AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (i', k))) =
      -(Proj.overlapToSections n i j).hom
        (HomogeneousLocalization.awayMap
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) rfl
          (Proj.projectiveSpaceChartCoordinate n i
            (ULift.up ⟨k.1, by
              have h2 := k.2
              rw [Finset.mem_compl, Finset.mem_singleton] at h2
              exact h2⟩))) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  refine Eq.trans (congrArg _ (Proj.chartIso_hom_appTop_coord n i
    (ULift.up (i', k)))) ?_
  refine Eq.trans (congrArg _ (congrArg _
    (Proj.rankOneGrassmannianChartPolynomialEquivAway_X n i (ULift.up (i', k))))) ?_
  rw [map_neg, map_neg]
  exact congrArg Neg.neg (Proj.homOfLE_appTop_awayToChartSections n i j hle _)

/-- Variant of `overlap_chart_entry` for the second pivot. -/
lemma Proj.overlap_chart_entry' (n : ℕ) (i j : Fin (n + 1))
    (hle : Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ)) (MvPolynomial.X i * MvPolynomial.X j) ≤
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X j))
    (j' : ↑({j} : Finset (Fin (n + 1)))) (k : ↑(({j} : Finset (Fin (n + 1)))ᶜ)) :
    (((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE hle ≫
      (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n j).hom).appTop).hom
        (AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (j', k))) =
      -(Proj.overlapToSections n i j).hom
        (HomogeneousLocalization.awayMap
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)
          (mul_comm (MvPolynomial.X i (R := ULift.{u} ℤ) (σ := Fin (n + 1)))
            (MvPolynomial.X j))
          (Proj.projectiveSpaceChartCoordinate n j
            (ULift.up ⟨k.1, by
              have h2 := k.2
              rw [Finset.mem_compl, Finset.mem_singleton] at h2
              exact h2⟩))) := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  refine Eq.trans (congrArg _ (Proj.chartIso_hom_appTop_coord n j
    (ULift.up (j', k)))) ?_
  refine Eq.trans (congrArg _ (congrArg _
    (Proj.rankOneGrassmannianChartPolynomialEquivAway_X n j (ULift.up (j', k))))) ?_
  rw [map_neg, map_neg]
  exact congrArg Neg.neg (Proj.homOfLE_appTop_awayToChartSections' n i j hle _)

/-- **Overlap compatibility of the chart morphisms**: on the overlap `D₊(XᵢXⱼ)`, the
chart morphisms of the pivots `i` and `j` into the glued rank-one Grassmannian
agree. -/
theorem Proj.chartToRankOneGrassmannian_overlap (n : ℕ) {i j : Fin (n + 1)}
    (hij : i ≠ j) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))).homOfLE
        (AlgebraicGeometry.Proj.basicOpen_mono _ _ _
          ⟨MvPolynomial.X j, rfl⟩) ≫
      Proj.projectiveSpaceChartToRankOneGrassmannian n i =
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))).homOfLE
        (AlgebraicGeometry.Proj.basicOpen_mono _ _ _
          ⟨MvPolynomial.X i, mul_comm (MvPolynomial.X i (R := ULift.{u} ℤ)
            (σ := Fin (n + 1))) (MvPolynomial.X j)⟩) ≫
      Proj.projectiveSpaceChartToRankOneGrassmannian n j := by
  set hlei := AlgebraicGeometry.Proj.basicOpen_mono
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (MvPolynomial.X i) (MvPolynomial.X i * MvPolynomial.X j)
    ⟨MvPolynomial.X j, rfl⟩ with hlei_def
  set hlej := AlgebraicGeometry.Proj.basicOpen_mono
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (MvPolynomial.X j) (MvPolynomial.X i * MvPolynomial.X j)
    ⟨MvPolynomial.X i, mul_comm (MvPolynomial.X i (R := ULift.{u} ℤ)
      (σ := Fin (n + 1))) (MvPolynomial.X j)⟩ with hlej_def
  rw [Proj.projectiveSpaceChartToRankOneGrassmannian,
    Proj.projectiveSpaceChartToRankOneGrassmannian]
  refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _)
  refine Scheme.LocalRepresentability.comp_toGlued_eq _ _ _ ?_
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, yonedaEquiv_comp, yonedaEquiv_yoneda_map,
    yonedaEquiv_yoneda_map]
  have hL : ∀ (I : Scheme.grassmannianChartCoverIndex.{u} 1 (n + 1))
      (W : Scheme.{u}) (g : W ⟶ Scheme.grassmannianChartCoverScheme 1 (n + 1) I),
      (Scheme.grassmannianRepresentableChartMap 1 (n + 1) I).app (op W) g =
      ((Scheme.grassmannianChartCoverRepresentation 1 (n + 1) I).homEquiv g).1 :=
    fun I W g ↦ rfl
  rw [hL, hL]
  apply Subtype.ext
  rw [homEquiv_grassmannianChartCoverRepresentation,
    homEquiv_grassmannianChartCoverRepresentation]
  show Scheme.coordinateGraphData _ ({i} : Finset (Fin (n + 1))) _ =
    Scheme.coordinateGraphData _ ({j} : Finset (Fin (n + 1))) _
  apply coordinateGraphData_singleton_eq_of_mul hij
  · -- the cross-entries multiply to one
    rw [Proj.overlap_chart_entry n i j hlei, Proj.overlap_chart_entry' n i j hlej,
      neg_mul_neg, ← map_mul, Proj.awayMap_chartCoordinate_mul_cross n hij,
      map_one]
  · -- the remaining entries are proportional
    intro k hki hkj
    rw [Proj.overlap_chart_entry n i j hlei, Proj.overlap_chart_entry' n i j hlej,
      Proj.overlap_chart_entry n i j hlei, neg_mul_neg, ← map_mul,
      Proj.awayMap_chartCoordinate_mul_trans n hij hki hkj, neg_neg]

/-- The standard coordinate charts `D₊(Xᵢ)` form an open cover of projective space. -/
noncomputable def Proj.projectiveSpaceCoordinateOpenCover (n : ℕ) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ))).OpenCover :=
  (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
    (ULift.{u} ℤ))).openCoverOfIsOpenCover
      (fun i : ULift.{u} (Fin (n + 1)) ↦ Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i.down))
      (by
        rw [TopologicalSpace.IsOpenCover]
        apply top_unique
        intro x _
        have hx : x ∈ (⨆ i : Fin (n + 1), Proj.basicOpen
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
            (MvPolynomial.X i)) := by
          rw [Proj.iSup_basicOpen_X_eq_top]
          trivial
        rw [TopologicalSpace.Opens.mem_iSup] at hx ⊢
        obtain ⟨i, hi⟩ := hx
        exact ⟨ULift.up i, hi⟩)

/-- The unit module on an affine scheme is quasi-coherent. -/
theorem Scheme.Modules.unit_isQuasicoherent_of_isAffine (X : Scheme.{u}) [IsAffine X] :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := by
  let e : Spec Γ(X, ⊤) ≅ X := X.isoSpec.symm
  let _ : (SheafOfModules.unit (Spec Γ(X, ⊤)).ringCatSheaf).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (AlgebraicGeometry.tildeSelf (R := Γ(X, ⊤))) inferInstance
  let _ : ((Scheme.Modules.restrictFunctor e.hom).obj
      (SheafOfModules.unit X.ringCatSheaf)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (Scheme.Modules.restrictUnitIso e.hom).symm inferInstance
  exact Scheme.Modules.FreeQuotient.isQuasicoherent_of_restrict_iso e
    (SheafOfModules.unit X.ringCatSheaf)

/-- Generalized overlap compatibility: the chart morphisms agree after restriction to
any common sub-open. -/
theorem Proj.chartToRankOneGrassmannian_overlap' (n : ℕ) {i j : Fin (n + 1)}
    (hij : i ≠ j)
    {W : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ))).Opens}
    (e₁ : W ≤ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ)) (MvPolynomial.X i))
    (e₂ : W ≤ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ)) (MvPolynomial.X j)) :
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE e₁ ≫
      Proj.projectiveSpaceChartToRankOneGrassmannian n i =
    (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE e₂ ≫
      Proj.projectiveSpaceChartToRankOneGrassmannian n j := by
  have hW : W ≤ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ)) (MvPolynomial.X i * MvPolynomial.X j) := by
    rw [AlgebraicGeometry.Proj.basicOpen_mul]
    exact le_inf e₁ e₂
  have hkey := congrArg (fun t ↦ (Proj (MvPolynomial.homogeneousSubmodule
    (Fin (n + 1)) (ULift.{u} ℤ))).homOfLE hW ≫ t)
    (Proj.chartToRankOneGrassmannian_overlap n hij)
  have hfuse1 : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ))).homOfLE hW ≫
      ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE (AlgebraicGeometry.Proj.basicOpen_mono _ _ _
          ⟨MvPolynomial.X j, rfl⟩) ≫
        Proj.projectiveSpaceChartToRankOneGrassmannian n i) =
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE e₁ ≫
        Proj.projectiveSpaceChartToRankOneGrassmannian n i := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    congr 1
    exact Scheme.homOfLE_homOfLE _ _ _
  have hfuse2 : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ))).homOfLE hW ≫
      ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE (AlgebraicGeometry.Proj.basicOpen_mono _ _ _
          ⟨MvPolynomial.X i, mul_comm (MvPolynomial.X i (R := ULift.{u} ℤ)
            (σ := Fin (n + 1))) (MvPolynomial.X j)⟩) ≫
        Proj.projectiveSpaceChartToRankOneGrassmannian n j) =
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE e₂ ≫
        Proj.projectiveSpaceChartToRankOneGrassmannian n j := by
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    congr 1
    exact Scheme.homOfLE_homOfLE _ _ _
  exact (hfuse1.symm.trans hkey).trans hfuse2

/-- Compatibility of the chart morphisms in the pullback form required for gluing. -/
lemma Proj.chartToRankOneGrassmannian_pullback_compat (n : ℕ)
    (x y : ULift.{u} (Fin (n + 1))) :
    pullback.fst
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ)) (MvPolynomial.X x.down)).ι
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ)) (MvPolynomial.X y.down)).ι ≫
      Proj.projectiveSpaceChartToRankOneGrassmannian n x.down =
    pullback.snd
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ)) (MvPolynomial.X x.down)).ι
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ)) (MvPolynomial.X y.down)).ι ≫
      Proj.projectiveSpaceChartToRankOneGrassmannian n y.down := by
  by_cases hxy : x = y
  · subst hxy
    have hfst : pullback.fst
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ)) (MvPolynomial.X x.down)).ι
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ)) (MvPolynomial.X x.down)).ι =
        pullback.snd
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
            (ULift.{u} ℤ)) (MvPolynomial.X x.down)).ι
          (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
            (ULift.{u} ℤ)) (MvPolynomial.X x.down)).ι :=
      (cancel_mono _).mp pullback.condition
    rw [hfst]
  · have hij : x.down ≠ y.down := fun h ↦ hxy (ULift.ext _ _ h)
    have hpb := AlgebraicGeometry.isPullback_opens_inf
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ)) (MvPolynomial.X x.down))
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ)) (MvPolynomial.X y.down))
    rw [← cancel_epi hpb.isoPullback.hom]
    refine Eq.trans (Category.assoc _ _ _).symm (Eq.trans ?_ (Category.assoc _ _ _))
    rw [hpb.isoPullback_hom_fst, hpb.isoPullback_hom_snd]
    exact Proj.chartToRankOneGrassmannian_overlap' n hij inf_le_left inf_le_right

/-- **The comparison morphism**: projective space maps to the glued rank-one
Grassmannian, by gluing the chart morphisms over the standard coordinate cover. -/
noncomputable def Proj.projectiveSpaceToRankOneGrassmannian (n : ℕ) :
    Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) ⟶
      (Scheme.grassmannianGlueData 1 (n + 1)).glued :=
  (Proj.projectiveSpaceCoordinateOpenCover n).glueMorphisms
    (fun x ↦ Proj.projectiveSpaceChartToRankOneGrassmannian n x.down)
    (fun x y ↦ Proj.chartToRankOneGrassmannian_pullback_compat n x y)

/-- The comparison morphism restricts to the chart morphisms. -/
lemma Proj.ι_projectiveSpaceToRankOneGrassmannian (n : ℕ)
    (x : ULift.{u} (Fin (n + 1))) :
    (Proj.projectiveSpaceCoordinateOpenCover n).f x ≫
      Proj.projectiveSpaceToRankOneGrassmannian n =
    Proj.projectiveSpaceChartToRankOneGrassmannian n x.down :=
  (Proj.projectiveSpaceCoordinateOpenCover n).ι_glueMorphisms _ _ x
-- (An earlier draft of the inverse construction, superseded by the sections below,
-- was removed here; see git history before 2026-08-23 for the scaffolding.)

end AlgebraicGeometry.ProjectiveSpectrum

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

/-- If the coordinate graph over the pivot `i` is complementary to the coordinate
line at `j` (the rank-one chart condition at `j`), then the `(i, j)` matrix entry
is a unit: the graph generator at `j` is `e_j + a_{ij}·e_i`, and expressing `e_i`
through the sum decomposition forces `a_{ij}` to divide `1`. -/
lemma coordinateGraph_isUnit_of_sup_pi {R : Type*} [CommRing R] {n : ℕ}
    {i j : Fin n} (hij : i ≠ j)
    (a : (i' : ↑({i} : Finset (Fin n))) → (j' : ↑(({i} : Finset (Fin n))ᶜ)) → R)
    (h : coordinateGraph {i} a ⊔
        Submodule.pi (((({j} : Finset (Fin n))ᶜ : Finset (Fin n)) : Set (Fin n)))
          (fun _ ↦ (⊥ : Submodule R R)) = ⊤) :
    IsUnit (a ⟨i, Finset.mem_singleton_self i⟩
      ⟨j, Finset.mem_compl.mpr (fun hj ↦ hij (Finset.mem_singleton.mp hj).symm)⟩) := by
  classical
  have hmem : (Pi.single i (1 : R) : Fin n → R) ∈
      coordinateGraph {i} a ⊔
        Submodule.pi (((({j} : Finset (Fin n))ᶜ : Finset (Fin n)) : Set (Fin n)))
          (fun _ ↦ (⊥ : Submodule R R)) := by
    rw [h]; trivial
  obtain ⟨w, hw, s, hs, hws⟩ := Submodule.mem_sup.mp hmem
  -- `s` is supported at the coordinate `j`
  have hs0 : ∀ k : Fin n, k ≠ j → s k = 0 := by
    intro k hk
    have := hs k (by
      simpa [Finset.mem_coe, Finset.mem_compl] using hk)
    simpa using this
  -- the graph condition on `w` at the pivot `i`
  have hgw := (mem_coordinateGraph.mp hw) i (Finset.mem_singleton_self i)
  -- the sum collapses to the single index `j`
  set jc : ↑(({i} : Finset (Fin n))ᶜ) :=
    ⟨j, Finset.mem_compl.mpr (fun hj ↦ hij (Finset.mem_singleton.mp hj).symm)⟩ with hjc
  have hcollapse :
      (∑ k : ↑(({i} : Finset (Fin n))ᶜ),
        a ⟨i, Finset.mem_singleton_self i⟩ k * w k.1) =
      a ⟨i, Finset.mem_singleton_self i⟩ jc * w j := by
    refine Finset.sum_eq_single_of_mem jc (Finset.mem_univ _) ?_
    intro b _ hb
    have hbj : b.1 ≠ j := fun hbj ↦ hb (Subtype.ext hbj)
    have hbi : b.1 ≠ i := fun hbi ↦
      (Finset.mem_compl.mp b.2) (Finset.mem_singleton.mpr hbi)
    have hwb : w b.1 = 0 := by
      have := congrFun hws b.1
      simp only [Pi.add_apply] at this
      have hsingle : (Pi.single i (1 : R) : Fin n → R) b.1 = 0 :=
        Pi.single_eq_of_ne hbi 1
      have hsb : s b.1 = 0 := hs0 b.1 hbj
      rw [hsingle, hsb, add_zero] at this
      exact this
    rw [hwb, mul_zero]
  -- compute `w i` and `w j` from the decomposition
  have hwi : w i = 1 := by
    have := congrFun hws i
    simp only [Pi.add_apply] at this
    rw [hs0 i hij, add_zero, Pi.single_eq_same] at this
    exact this
  have hwj : w j = -s j := by
    have := congrFun hws j
    simp only [Pi.add_apply] at this
    have hsingle : (Pi.single i (1 : R) : Fin n → R) j = 0 :=
      Pi.single_eq_of_ne (Ne.symm hij) 1
    rw [hsingle] at this
    exact eq_neg_of_add_eq_zero_left this
  rw [hcollapse, hwi, hwj] at hgw
  exact isUnit_iff_exists_inv.mpr ⟨-s j, hgw.symm⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProjectiveSpectrum

attribute [local instance] MvPolynomial.gradedAlgebra

open AlgebraicGeometry.Scheme

/-- A scheme mapping into two distinct rank-one charts of the glued Grassmannian
pulls the cross coordinate back to a unit: the classified point is simultaneously a
graph over the pivot `i` and a chart-`j` point, so the `(i, j)` entry of its matrix
is invertible on every affine open. -/
lemma Proj.isUnit_coord_of_comp_rankOneChart_eq (n : ℕ) {i j : Fin (n + 1)}
    (hij : i ≠ j) {T : Scheme.{u}}
    (g₁ : T ⟶ Scheme.grassmannianChartCoverScheme 1 (n + 1)
      (Proj.rankOneGrassmannianChartIndex n i))
    (g₂ : T ⟶ Scheme.grassmannianChartCoverScheme 1 (n + 1)
      (Proj.rankOneGrassmannianChartIndex n j))
    (hcomp : g₁ ≫ (Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n i) =
      g₂ ≫ (Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n j))
    (U : T.affineOpens) :
    IsUnit ((T.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom (g₁.appTop.hom
      (AffineSpace.coord (⊤_ Scheme.{u})
        (ULift.up (⟨i, Finset.mem_singleton_self i⟩,
          ⟨j, Finset.mem_compl.mpr
            (fun hj ↦ hij (Finset.mem_singleton.mp hj).symm)⟩))))) := by
  classical
  -- the two classified functor points agree
  have h1 := Scheme.grassmannianGluedRepresentation_comp_openCover 1 (n + 1)
    (Proj.rankOneGrassmannianChartIndex n i) g₁
  have h2 := Scheme.grassmannianGluedRepresentation_comp_openCover 1 (n + 1)
    (Proj.rankOneGrassmannianChartIndex n j) g₂
  have heq : ((Scheme.grassmannianChartCoverRepresentation 1 (n + 1)
        (Proj.rankOneGrassmannianChartIndex n i)).homEquiv g₁).1 =
      ((Scheme.grassmannianChartCoverRepresentation 1 (n + 1)
        (Proj.rankOneGrassmannianChartIndex n j)).homEquiv g₂).1 := by
    rw [← h1, ← h2, hcomp]
  rw [homEquiv_grassmannianChartCoverRepresentation,
    homEquiv_grassmannianChartCoverRepresentation] at heq
  -- extract the equality of kernel data
  have hdata : Scheme.coordinateGraphData T ({i} : Finset (Fin (n + 1)))
        (fun i' j' ↦ g₁.appTop.hom
          (AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (i', j')))) =
      Scheme.coordinateGraphData T ({j} : Finset (Fin (n + 1)))
        (fun i' j' ↦ g₂.appTop.hom
          (AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (i', j')))) :=
    congrArg Subtype.val heq
  -- the chart-`j` complement condition transports to the graph over `{i}`
  have hcond := Scheme.coordinateGraphData_isComplementOfCoords T
    ({j} : Finset (Fin (n + 1)))
    (fun i' j' ↦ g₂.appTop.hom
      (AffineSpace.coord (⊤_ Scheme.{u}) (ULift.up (i', j'))))
  rw [← hdata] at hcond
  have hsup := (hcond U).sup_eq_top
  rw [Scheme.coordinateGraphData_submodule] at hsup
  exact Scheme.coordinateGraph_isUnit_of_sup_pi hij _ hsup

/-- The represented rank-one chart maps to the spectrum of the pivot localization,
through the matrix-coordinate polynomial presentation. -/
noncomputable def Proj.rankOneChartToSpecAway (n : ℕ) (i : Fin (n + 1)) :
    Scheme.grassmannianChartCoverScheme 1 (n + 1)
        (Proj.rankOneGrassmannianChartIndex n i) ⟶
      Spec (CommRingCat.of (HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i))) :=
  (Proj.rankOneGrassmannianChartSchemeIsoSpec n i).hom ≫
    Spec.map (CommRingCat.ofHom
      (Proj.rankOneGrassmannianChartPolynomialEquivAway n i).symm.toRingHom)

/-- The chart isomorphism composed with the localization presentation is the basic
open chart of `Proj`. -/
lemma Proj.chartIso_hom_rankOneChartToSpecAway (n : ℕ) (i : Fin (n + 1)) :
    (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).hom ≫
      Proj.rankOneChartToSpecAway n i =
    (Proj.basicOpenIsoSpec
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos).hom := by
  show ((Proj.basicOpenIsoSpec
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos).hom ≫
      Spec.map (CommRingCat.ofHom
        (Proj.rankOneGrassmannianChartPolynomialEquivAway n i).toRingHom) ≫
      (Proj.rankOneGrassmannianChartSchemeIsoSpec n i).inv) ≫
      ((Proj.rankOneGrassmannianChartSchemeIsoSpec n i).hom ≫
        Spec.map (CommRingCat.ofHom
          (Proj.rankOneGrassmannianChartPolynomialEquivAway n i).symm.toRingHom)) = _
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [show (Proj.rankOneGrassmannianChartPolynomialEquivAway n i).toRingHom.comp
      (Proj.rankOneGrassmannianChartPolynomialEquivAway n i).symm.toRingHom =
      RingHom.id _ from
    RingHom.ext fun z ↦ (Proj.rankOneGrassmannianChartPolynomialEquivAway
      n i).apply_symm_apply z]
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]

/-- Through the localization presentation, the chart scheme maps onto the standard
open `D₊(Xᵢ)` of projective space by the inverse chart isomorphism. -/
lemma Proj.rankOneChartToSpecAway_awayι (n : ℕ) (i : Fin (n + 1)) :
    Proj.rankOneChartToSpecAway n i ≫
      AlgebraicGeometry.Proj.awayι
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos =
    (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).inv ≫
      (Proj.basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i)).ι := by
  have hτ : Proj.rankOneChartToSpecAway n i =
      (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).inv ≫
        (Proj.basicOpenIsoSpec
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos).hom := by
    rw [← Proj.chartIso_hom_rankOneChartToSpecAway n i, Iso.inv_hom_id_assoc]
  rw [hτ, Category.assoc, ← AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos,
    Iso.hom_inv_id_assoc]

/-- The affine coordinate of the rank-one chart is pulled back from the matrix
fraction on the pivot localization. -/
lemma Proj.coord_eq_rankOneChartToSpecAway_appTop (n : ℕ) (i : Fin (n + 1))
    (p : ULift.{u} (↑({i} : Finset (Fin (n + 1))) ×
      ↑(({i} : Finset (Fin (n + 1)))ᶜ))) :
    AffineSpace.coord (⊤_ Scheme.{u}) p =
      (Proj.rankOneChartToSpecAway n i).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X i)))).inv
        (Proj.rankOneGrassmannianChartPolynomialEquivAway n i
          (MvPolynomial.X p))) := by
  rw [Proj.rankOneChartToSpecAway, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  -- naturality of `ΓSpecIso` along the presentation
  have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
    (Proj.rankOneGrassmannianChartPolynomialEquivAway n i).symm.toRingHom)
  have h2 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hnat)
    ((Proj.rankOneGrassmannianChartPolynomialEquivAway n i) (MvPolynomial.X p))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [← h2]
  rw [show (CommRingCat.ofHom
      (Proj.rankOneGrassmannianChartPolynomialEquivAway n i).symm.toRingHom).hom
      ((Proj.rankOneGrassmannianChartPolynomialEquivAway n i) (MvPolynomial.X p)) =
    MvPolynomial.X p from
    (Proj.rankOneGrassmannianChartPolynomialEquivAway n i).symm_apply_apply _]
  rw [← Proj.rankOneGrassmannianChartSchemeIsoSpec_inv_appTop_coord n i p]
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  rw [show (Proj.rankOneGrassmannianChartSchemeIsoSpec n i).hom ≫
      (Proj.rankOneGrassmannianChartSchemeIsoSpec n i).inv = 𝟙 _ from
    Iso.hom_inv_id _]
  rfl

/-- On the pivot localization `Spec (A_{(Xᵢ)})`, the preimage of the standard open
`D₊(Xⱼ)` is the basic open of the matrix fraction `Xⱼ/Xᵢ`: localizing further at
that fraction presents `A_{(XᵢXⱼ)}`. -/
lemma Proj.awayι_preimage_basicOpen (n : ℕ) {i j : Fin (n + 1)} (hji : j ≠ i) :
    AlgebraicGeometry.Proj.awayι
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X j) =
    PrimeSpectrum.basicOpen
      (Proj.projectiveSpaceChartCoordinate n i (ULift.up ⟨j, hji⟩)) := by
  classical
  -- the further localization presenting `A_{(XᵢXⱼ)}`
  letI := (HomogeneousLocalization.awayMap
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j)
    (rfl : MvPolynomial.X i * MvPolynomial.X j =
      MvPolynomial.X i * MvPolynomial.X j)).toAlgebra
  haveI hloc := HomogeneousLocalization.Away.isLocalization_mul
    (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (f := MvPolynomial.X i) (g := MvPolynomial.X j)
    (x := MvPolynomial.X i * MvPolynomial.X j)
    (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)
    (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j)
    (hx := rfl) one_ne_zero
  -- the localization element is the chart coordinate
  have hcoord : HomogeneousLocalization.Away.isLocalizationElem
      (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)
      (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j) =
      Proj.projectiveSpaceChartCoordinate n i (ULift.up ⟨j, hji⟩) := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, Proj.projectiveSpaceChartCoordinate,
      HomogeneousLocalization.Away.val_mk]
    congr 1
    exact pow_one _
  rw [← hcoord]
  -- the image of the further localization is the basic open of the fraction
  have hrange : Set.range (fun y ↦ PrimeSpectrum.comap
      (HomogeneousLocalization.awayMap
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j)
        (rfl : MvPolynomial.X i * MvPolynomial.X j =
          MvPolynomial.X i * MvPolynomial.X j)) y) =
      ↑(PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem
        (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (f := MvPolynomial.X i) (g := MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j))) := by
    have := PrimeSpectrum.localization_away_comap_range
      (S := HomogeneousLocalization.Away
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i * MvPolynomial.X j))
      (HomogeneousLocalization.Away.isLocalizationElem
        (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (f := MvPolynomial.X i) (g := MvPolynomial.X j)
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j))
    rw [← this, RingHom.algebraMap_toAlgebra]
  have hcomp := AlgebraicGeometry.Proj.SpecMap_awayMap_awayι
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (f_deg := MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)
    (hm := Nat.one_pos)
    (g_deg := MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j)
    (hx := rfl (a := MvPolynomial.X i * MvPolynomial.X j))
  apply Opens.ext
  ext q
  simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · -- membership in `D₊(Xⱼ)` puts the image inside the joint chart
    intro hq
    have hmem : (AlgebraicGeometry.Proj.awayι
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos).base q ∈
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ)) (MvPolynomial.X i * MvPolynomial.X j) := by
      rw [AlgebraicGeometry.Proj.basicOpen_mul]
      refine ⟨?_, hq⟩
      have hrangei : (AlgebraicGeometry.Proj.awayι
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i)
          Nat.one_pos).base q ∈ (AlgebraicGeometry.Proj.awayι
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i)
          Nat.one_pos).opensRange := ⟨q, rfl⟩
      rwa [AlgebraicGeometry.Proj.opensRange_awayι] at hrangei
    rw [← AlgebraicGeometry.Proj.opensRange_awayι
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i * MvPolynomial.X j)
      ((MvPolynomial.isHomogeneous_X _ i).mul (MvPolynomial.isHomogeneous_X _ j))
      (by norm_num)] at hmem
    obtain ⟨y, hy⟩ := hmem
    have h1 : (AlgebraicGeometry.Proj.awayι
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos).base
        ((Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j)
          (rfl : MvPolynomial.X i * MvPolynomial.X j =
            MvPolynomial.X i * MvPolynomial.X j)))).base y) =
        (AlgebraicGeometry.Proj.awayι
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i)
          Nat.one_pos).base q := by
      rw [← Scheme.Hom.comp_apply, hcomp]
      exact hy
    have h2 := (AlgebraicGeometry.Proj.awayι
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i)
        Nat.one_pos).isOpenEmbedding.injective h1
    have h2' : PrimeSpectrum.comap (HomogeneousLocalization.awayMap
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j)
        (rfl : MvPolynomial.X i * MvPolynomial.X j =
          MvPolynomial.X i * MvPolynomial.X j)) y = q := h2
    have hq2 : q ∈ (↑(PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem
          (𝒜 := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (f := MvPolynomial.X i) (g := MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)
          (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j))) :
        Set (PrimeSpectrum (HomogeneousLocalization.Away
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X i)))) := hrange ▸ ⟨y, h2'⟩
    exact hq2
  · -- conversely, the smaller chart sits inside `D₊(Xⱼ)`
    intro hq
    have hq' : q ∈ Set.range (fun y ↦ PrimeSpectrum.comap
        (HomogeneousLocalization.awayMap
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j)
          (rfl : MvPolynomial.X i * MvPolynomial.X j =
            MvPolynomial.X i * MvPolynomial.X j)) y) := by
      rw [hrange]; exact hq
    obtain ⟨y, rfl⟩ := hq'
    have hy : (AlgebraicGeometry.Proj.awayι
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos).base
        ((Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j)
          (rfl : MvPolynomial.X i * MvPolynomial.X j =
            MvPolynomial.X i * MvPolynomial.X j)))).base y) ∈
        (AlgebraicGeometry.Proj.awayι
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X i * MvPolynomial.X j)
          (SetLike.mul_mem_graded (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) i)
            (MvPolynomial.isHomogeneous_X (ULift.{u} ℤ) j))
          (Nat.one_pos.trans_le (Nat.le_add_right 1 1))).opensRange := by
      rw [← Scheme.Hom.comp_apply, hcomp]
      exact ⟨y, rfl⟩
    rw [AlgebraicGeometry.Proj.opensRange_awayι,
      AlgebraicGeometry.Proj.basicOpen_mul] at hy
    exact hy.2

/-- The restriction of a chart morphism to the standard overlap `D₊(XᵢXⱼ)`. -/
noncomputable def Proj.overlapToRankOneGrassmannian (n : ℕ) (i j : Fin (n + 1)) :
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i * MvPolynomial.X j)).toScheme ⟶
      (Scheme.grassmannianGlueData 1 (n + 1)).glued :=
  (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))).homOfLE
      (AlgebraicGeometry.Proj.basicOpen_mono _ _ _ ⟨MvPolynomial.X j, rfl⟩) ≫
    Proj.projectiveSpaceChartToRankOneGrassmannian n i

/-- Points of an isomorphism round-trip. -/
private lemma iso_hom_base_inv_base {A B : Scheme.{u}} (e : A ≅ B) (b : B) :
    e.hom.base (e.inv.base b) = b := by
  have h := congrArg (fun (m : B ⟶ B) ↦ m.base b) e.inv_hom_id
  simpa using h

/-- **The overlap is the whole chart intersection**: any point of the glued rank-one
Grassmannian lying in two distinct chart images comes from `D₊(XᵢXⱼ)`. -/
theorem Proj.range_inter_subset_overlapToRankOneGrassmannian (n : ℕ)
    {i j : Fin (n + 1)} (hij : i ≠ j) :
    Set.range ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n i)).base ∩
      Set.range ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n j)).base ⊆
    Set.range (Proj.overlapToRankOneGrassmannian.{u} n i j).base := by
  classical
  haveI hoi := (Scheme.grassmannianGlueData 1 (n + 1)).openCover.map_prop
    (Proj.rankOneGrassmannianChartIndex n i)
  haveI hoj := (Scheme.grassmannianGlueData 1 (n + 1)).openCover.map_prop
    (Proj.rankOneGrassmannianChartIndex n j)
  intro z hz
  rw [← IsOpenImmersion.range_pullback_to_base_of_left
    ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
      (Proj.rankOneGrassmannianChartIndex n i))
    ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
      (Proj.rankOneGrassmannianChartIndex n j))] at hz
  obtain ⟨x, hx⟩ := hz
  -- an affine neighbourhood of the pullback point
  obtain ⟨k, y, hy⟩ := (pullback
    ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
      (Proj.rankOneGrassmannianChartIndex n i))
    ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
      (Proj.rankOneGrassmannianChartIndex n j))).affineCover.exists_eq x
  -- the cross coordinate is a unit near `x`, hence `x` lies in its basic open
  have hunit := Proj.isUnit_coord_of_comp_rankOneChart_eq n hij
    (pullback.fst _ _) (pullback.snd _ _) pullback.condition
    ⟨((pullback
      ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n i))
      ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n j))).affineCover.f k).opensRange,
      isAffineOpen_opensRange _⟩
  have hbasic := (pullback
    ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
      (Proj.rankOneGrassmannianChartIndex n i))
    ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
      (Proj.rankOneGrassmannianChartIndex n j))).basicOpen_of_isUnit hunit
  rw [Scheme.basicOpen_res] at hbasic
  have hxin : x ∈ ((pullback
      ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n i))
      ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n j))).affineCover.f k).opensRange :=
    ⟨y, hy⟩
  have hxmem := hbasic.symm.le hxin
  have hmem1 := hxmem.2
  -- express the coordinate as a pullback from the pivot localization
  rw [Proj.coord_eq_rankOneChartToSpecAway_appTop n i] at hmem1
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop] at hmem1
  rw [← Scheme.preimage_basicOpen_top] at hmem1
  have hq := (Scheme.Hom.mem_preimage _).mp hmem1
  rw [AlgebraicGeometry.basicOpen_eq_of_affine] at hq
  rw [Proj.rankOneGrassmannianChartPolynomialEquivAway_X n i] at hq
  -- remove the sign
  have hq' : (pullback.fst
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n i))
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n j)) ≫ Proj.rankOneChartToSpecAway n i).base x ∈
      PrimeSpectrum.basicOpen (Proj.projectiveSpaceChartCoordinate n i
        (Proj.rankOneGrassmannianChartCoordinateEquiv n i
          (ULift.up (⟨i, Finset.mem_singleton_self i⟩,
            ⟨j, Finset.mem_compl.mpr
              (fun hj ↦ hij (Finset.mem_singleton.mp hj).symm)⟩)))) := by
    rw [PrimeSpectrum.mem_basicOpen] at hq ⊢
    intro hcontra
    exact hq (neg_mem_iff.mpr hcontra)
  -- transport through the pivot localization into `Proj`
  have hproj := Proj.awayι_preimage_basicOpen n
    (hji := fun h ↦ hij h.symm) (i := i) (j := j)
  rw [show Proj.rankOneGrassmannianChartCoordinateEquiv n i
      (ULift.up (⟨i, Finset.mem_singleton_self i⟩,
        ⟨j, Finset.mem_compl.mpr
          (fun hj ↦ hij (Finset.mem_singleton.mp hj).symm)⟩)) =
      ULift.up ⟨j, fun h ↦ hij h.symm⟩ from rfl] at hq'
  rw [← hproj] at hq'
  have hjmem : (AlgebraicGeometry.Proj.awayι
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos).base
      ((pullback.fst
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n i))
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n j)) ≫ Proj.rankOneChartToSpecAway n i).base x) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ)) (MvPolynomial.X j) :=
    (Scheme.Hom.mem_preimage _).mp hq'
  have himem : (AlgebraicGeometry.Proj.awayι
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos).base
      ((pullback.fst
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n i))
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n j)) ≫ Proj.rankOneChartToSpecAway n i).base x) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ)) (MvPolynomial.X i) := by
    rw [← AlgebraicGeometry.Proj.opensRange_awayι
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos]
    exact ⟨_, rfl⟩
  have hijmem : (AlgebraicGeometry.Proj.awayι
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos).base
      ((pullback.fst
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n i))
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n j)) ≫ Proj.rankOneChartToSpecAway n i).base x) ∈
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ)) (MvPolynomial.X i * MvPolynomial.X j) := by
    rw [AlgebraicGeometry.Proj.basicOpen_mul]
    exact ⟨himem, hjmem⟩
  refine ⟨⟨_, hijmem⟩, ?_⟩
  -- the point of `D₊(Xᵢ)` underlying the localization point
  have hpoint : ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ))).homOfLE
      (AlgebraicGeometry.Proj.basicOpen_mono _ _ _ ⟨MvPolynomial.X j, rfl⟩)).base
      ⟨_, hijmem⟩ =
      (Proj.basicOpenIsoSpec
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i)
        Nat.one_pos).inv.base
      ((pullback.fst
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n i))
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n j)) ≫ Proj.rankOneChartToSpecAway n i).base x) := by
    apply Subtype.ext
    rw [Scheme.homOfLE_apply]
    show (AlgebraicGeometry.Proj.awayι
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos).base
        ((pullback.fst
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n i))
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n j)) ≫ Proj.rankOneChartToSpecAway n i).base x) = _
    rw [← AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i) Nat.one_pos]
    rfl
  -- the chart isomorphism carries this point back to `pullback.fst x`
  have hτ : Proj.rankOneChartToSpecAway n i =
      (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).inv ≫
        (Proj.basicOpenIsoSpec
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
          (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i)
          Nat.one_pos).hom := by
    rw [← Proj.chartIso_hom_rankOneChartToSpecAway n i, Iso.inv_hom_id_assoc]
  have hmor : (pullback.fst
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n i))
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n j)) ≫ Proj.rankOneChartToSpecAway n i) ≫
      (Proj.basicOpenIsoSpec
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i)
        Nat.one_pos).inv ≫
      (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).hom =
      pullback.fst
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n i))
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n j)) := by
    rw [hτ, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hchart := congrArg
    (fun (m : _ ⟶ Scheme.grassmannianChartCoverScheme 1 (n + 1)
      (Proj.rankOneGrassmannianChartIndex n i)) ↦ m.base x) hmor
  simp only at hchart
  -- assemble
  show (Proj.overlapToRankOneGrassmannian n i j).base ⟨_, hijmem⟩ = z
  have hfactor : (Proj.overlapToRankOneGrassmannian n i j).base ⟨_, hijmem⟩ =
      ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n i)).base
        ((Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).hom.base
          (((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
            (ULift.{u} ℤ))).homOfLE
            (AlgebraicGeometry.Proj.basicOpen_mono _ _ _
              ⟨MvPolynomial.X j, rfl⟩)).base ⟨_, hijmem⟩)) := rfl
  rw [hfactor, hpoint]
  have hinner : (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).hom.base
      ((Proj.basicOpenIsoSpec
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X _ i)
        Nat.one_pos).inv.base
      ((pullback.fst
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n i))
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n j)) ≫ Proj.rankOneChartToSpecAway n i).base x)) =
      (pullback.fst
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n i))
        ((Scheme.grassmannianGlueData 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n j))).base x := hchart
  rw [hinner]
  exact hx

/-- The scheme-theoretic overlap of two distinct rank-one chart images is the
standard overlap `D₊(XᵢXⱼ)` of projective charts. -/
lemma Proj.range_pullback_eq_overlapToRankOneGrassmannian (n : ℕ)
    {i j : Fin (n + 1)} (hij : i ≠ j) :
    Set.range (⇑(pullback.fst
        ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n i))
        ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n j)) ≫
      (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n i))) =
    Set.range (⇑(Proj.overlapToRankOneGrassmannian.{u} n i j)) := by
  haveI hoi := (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.map_prop
    (Proj.rankOneGrassmannianChartIndex n i)
  haveI hoj := (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.map_prop
    (Proj.rankOneGrassmannianChartIndex n j)
  rw [IsOpenImmersion.range_pullback_to_base_of_left]
  apply Set.Subset.antisymm
  · exact Proj.range_inter_subset_overlapToRankOneGrassmannian n hij
  · rintro _ ⟨w, rfl⟩
    constructor
    · exact ⟨(Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).hom.base
        (((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ))).homOfLE
          (AlgebraicGeometry.Proj.basicOpen_mono _ _ _
            ⟨MvPolynomial.X j, rfl⟩)).base w), rfl⟩
    · refine ⟨(Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n j).hom.base
        (((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ))).homOfLE
          (AlgebraicGeometry.Proj.basicOpen_mono _ _ _
            ⟨MvPolynomial.X i, mul_comm (MvPolynomial.X i (R := ULift.{u} ℤ)
              (σ := Fin (n + 1))) (MvPolynomial.X j)⟩)).base w), ?_⟩
      have hover : Proj.overlapToRankOneGrassmannian.{u} n i j =
          (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
            (ULift.{u} ℤ))).homOfLE
            (AlgebraicGeometry.Proj.basicOpen_mono _ _ _
              ⟨MvPolynomial.X i, mul_comm (MvPolynomial.X i (R := ULift.{u} ℤ)
                (σ := Fin (n + 1))) (MvPolynomial.X j)⟩) ≫
            Proj.projectiveSpaceChartToRankOneGrassmannian n j := by
        rw [Proj.overlapToRankOneGrassmannian]
        exact Proj.chartToRankOneGrassmannian_overlap n hij
      rw [hover]
      rfl

instance Proj.overlapToRankOneGrassmannian_isOpenImmersion (n : ℕ)
    (i j : Fin (n + 1)) :
    IsOpenImmersion (Proj.overlapToRankOneGrassmannian.{u} n i j) := by
  haveI := (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.map_prop
    (Proj.rankOneGrassmannianChartIndex n i)
  show IsOpenImmersion ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ))).homOfLE
      (AlgebraicGeometry.Proj.basicOpen_mono _ _ _ ⟨MvPolynomial.X j, rfl⟩) ≫
    (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).hom ≫
    (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
      (Proj.rankOneGrassmannianChartIndex n i))
  infer_instance

/-- The pullback of two distinct rank-one chart inclusions is the standard
projective overlap. -/
noncomputable def Proj.overlapIsoPullback (n : ℕ) {i j : Fin (n + 1)}
    (hij : i ≠ j) :
    pullback
      ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n i))
      ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n j)) ≅
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ)) (MvPolynomial.X i * MvPolynomial.X j)).toScheme :=
  haveI hoi := (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.map_prop
    (Proj.rankOneGrassmannianChartIndex n i)
  haveI hoj := (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.map_prop
    (Proj.rankOneGrassmannianChartIndex n j)
  IsOpenImmersion.isoOfRangeEq
    (pullback.fst _ _ ≫ (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
      (Proj.rankOneGrassmannianChartIndex n i))
    (Proj.overlapToRankOneGrassmannian.{u} n i j)
    (Proj.range_pullback_eq_overlapToRankOneGrassmannian n hij)

/-- The comparison of the overlap with the pullback commutes with the first
projection. -/
lemma Proj.overlapIsoPullback_hom_fst (n : ℕ) {i j : Fin (n + 1)} (hij : i ≠ j) :
    (Proj.overlapIsoPullback n hij).hom ≫
      ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE
        (AlgebraicGeometry.Proj.basicOpen_mono _ _ _ ⟨MvPolynomial.X j, rfl⟩) ≫
      (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n i).hom) =
    pullback.fst
      ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n i))
      ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n j)) := by
  haveI hoi := (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.map_prop
    (Proj.rankOneGrassmannianChartIndex n i)
  haveI hoj := (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.map_prop
    (Proj.rankOneGrassmannianChartIndex n j)
  rw [← cancel_mono ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
    (Proj.rankOneGrassmannianChartIndex n i))]
  have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac
    (pullback.fst _ _ ≫ (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
      (Proj.rankOneGrassmannianChartIndex n i))
    (Proj.overlapToRankOneGrassmannian.{u} n i j)
    (Proj.range_pullback_eq_overlapToRankOneGrassmannian n hij)
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m ↦ (Proj.overlapIsoPullback n hij).hom ≫ m)
    (Category.assoc _ _ _)) ?_
  exact hfac

/-- The comparison of the overlap with the pullback commutes with the second
projection. -/
lemma Proj.overlapIsoPullback_hom_snd (n : ℕ) {i j : Fin (n + 1)} (hij : i ≠ j) :
    (Proj.overlapIsoPullback n hij).hom ≫
      ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE
        (AlgebraicGeometry.Proj.basicOpen_mono _ _ _
          ⟨MvPolynomial.X i, mul_comm (MvPolynomial.X i (R := ULift.{u} ℤ)
            (σ := Fin (n + 1))) (MvPolynomial.X j)⟩) ≫
      (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n j).hom) =
    pullback.snd
      ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n i))
      ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n j)) := by
  haveI hoi := (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.map_prop
    (Proj.rankOneGrassmannianChartIndex n i)
  haveI hoj := (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.map_prop
    (Proj.rankOneGrassmannianChartIndex n j)
  rw [← cancel_mono ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
    (Proj.rankOneGrassmannianChartIndex n j))]
  have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac
    (pullback.fst _ _ ≫ (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
      (Proj.rankOneGrassmannianChartIndex n i))
    (Proj.overlapToRankOneGrassmannian.{u} n i j)
    (Proj.range_pullback_eq_overlapToRankOneGrassmannian n hij)
  have hover : Proj.overlapToRankOneGrassmannian.{u} n i j =
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE
        (AlgebraicGeometry.Proj.basicOpen_mono _ _ _
          ⟨MvPolynomial.X i, mul_comm (MvPolynomial.X i (R := ULift.{u} ℤ)
            (σ := Fin (n + 1))) (MvPolynomial.X j)⟩) ≫
        Proj.projectiveSpaceChartToRankOneGrassmannian n j := by
    rw [Proj.overlapToRankOneGrassmannian]
    exact Proj.chartToRankOneGrassmannian_overlap n hij
  have hfac2 := hfac.symm.trans (congrArg
    (fun m ↦ (Proj.overlapIsoPullback n hij).hom ≫ m) hover)
  have hcond : pullback.fst
      ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n i))
      ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n j)) ≫
      (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n i) =
      pullback.snd _ _ ≫ (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n j) := pullback.condition
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun m ↦ (Proj.overlapIsoPullback n hij).hom ≫ m)
    (Category.assoc _ _ _)) ?_
  exact (hcond.symm.trans hfac2).symm

/-- Restricting through a chart isomorphism and back collapses to the open
inclusion. -/
lemma Proj.homOfLE_chartIso_hom_inv_ι (n : ℕ) (k : Fin (n + 1))
    {W : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ))).Opens}
    (e : W ≤ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ)) (MvPolynomial.X k)) :
    ((Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ))).homOfLE e ≫
      (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n k).hom) ≫
      ((Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n k).inv ≫
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ)) (MvPolynomial.X k)).ι) = W.ι := by
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  exact Scheme.homOfLE_ι _ e

/-- The rank-one chart cover of the glued Grassmannian, indexed by the pivot
coordinate. -/
noncomputable def Scheme.rankOneGrassmannianGluedCover (n : ℕ) :
    ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).glued).OpenCover :=
  Scheme.Cover.mkOfCovers (ULift.{u} (Fin (n + 1)))
    (fun x ↦ Scheme.grassmannianChartCoverScheme 1 (n + 1)
      (Proj.rankOneGrassmannianChartIndex n x.down))
    (fun x ↦ (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
      (Proj.rankOneGrassmannianChartIndex n x.down))
    (fun z ↦ by
      obtain ⟨I, w, hw⟩ :=
        (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.exists_eq z
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.down.2
      have hI : Proj.rankOneGrassmannianChartIndex n a = I :=
        ULift.ext _ _ (Subtype.ext ha.symm)
      refine ⟨ULift.up a, ?_⟩
      rw [hI]
      exact ⟨w, hw⟩)
    (fun x ↦ (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.map_prop
      (Proj.rankOneGrassmannianChartIndex n x.down))

/-- Compatibility of the inverse chart morphisms on overlaps. -/
lemma Proj.rankOneChartInverse_compat (n : ℕ) (x y : ULift.{u} (Fin (n + 1))) :
    pullback.fst
        ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n x.down))
        ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n y.down)) ≫
      ((Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n x.down).inv ≫
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ)) (MvPolynomial.X x.down)).ι) =
    pullback.snd
        ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n x.down))
        ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n y.down)) ≫
      ((Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n y.down).inv ≫
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ)) (MvPolynomial.X y.down)).ι) := by
  haveI hox := (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.map_prop
    (Proj.rankOneGrassmannianChartIndex n x.down)
  haveI hoy := (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.map_prop
    (Proj.rankOneGrassmannianChartIndex n y.down)
  by_cases hxy : x = y
  · subst hxy
    have hfst : pullback.fst
        ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n x.down))
        ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
          (Proj.rankOneGrassmannianChartIndex n x.down)) =
        pullback.snd
          ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
            (Proj.rankOneGrassmannianChartIndex n x.down))
          ((Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
            (Proj.rankOneGrassmannianChartIndex n x.down)) :=
      (cancel_mono _).mp pullback.condition
    rw [hfst]
  · have hij : x.down ≠ y.down := fun h ↦ hxy (ULift.ext _ _ h)
    rw [← Proj.overlapIsoPullback_hom_fst n hij,
      ← Proj.overlapIsoPullback_hom_snd n hij]
    refine Eq.trans (Category.assoc _ _ _)
      (Eq.trans ?_ (Category.assoc _ _ _).symm)
    refine congrArg (fun m ↦ (Proj.overlapIsoPullback n hij).hom ≫ m) ?_
    rw [Proj.homOfLE_chartIso_hom_inv_ι n x.down,
      Proj.homOfLE_chartIso_hom_inv_ι n y.down]

/-- **The inverse comparison morphism**: the glued rank-one Grassmannian maps to
projective space by gluing the inverse chart isomorphisms. -/
noncomputable def Proj.rankOneGrassmannianToProjectiveSpace (n : ℕ) :
    (Scheme.grassmannianGlueData.{u} 1 (n + 1)).glued ⟶
      Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
  (Scheme.rankOneGrassmannianGluedCover n).glueMorphisms
    (fun x ↦ (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n x.down).inv ≫
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ)) (MvPolynomial.X x.down)).ι)
    (fun x y ↦ Proj.rankOneChartInverse_compat n x y)

/-- The inverse comparison restricts to the inverse chart isomorphisms. -/
lemma Proj.f_rankOneGrassmannianToProjectiveSpace (n : ℕ)
    (x : ULift.{u} (Fin (n + 1))) :
    (Scheme.grassmannianGlueData.{u} 1 (n + 1)).openCover.f
        (Proj.rankOneGrassmannianChartIndex n x.down) ≫
      Proj.rankOneGrassmannianToProjectiveSpace n =
    (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n x.down).inv ≫
      (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
        (ULift.{u} ℤ)) (MvPolynomial.X x.down)).ι :=
  (Scheme.rankOneGrassmannianGluedCover n).ι_glueMorphisms _ _ x

/-- The comparison morphism and its inverse compose to the identity of projective
space. -/
lemma Proj.projectiveSpaceToRankOneGrassmannian_comp_inv (n : ℕ) :
    Proj.projectiveSpaceToRankOneGrassmannian.{u} n ≫
      Proj.rankOneGrassmannianToProjectiveSpace n =
    𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))) := by
  apply (Proj.projectiveSpaceCoordinateOpenCover n).hom_ext
  intro x
  rw [Category.comp_id, ← Category.assoc,
    Proj.ι_projectiveSpaceToRankOneGrassmannian n x,
    Proj.projectiveSpaceChartToRankOneGrassmannian, Category.assoc,
    Proj.f_rankOneGrassmannianToProjectiveSpace n x, Iso.hom_inv_id_assoc]
  rfl

/-- The inverse and the comparison morphism compose to the identity of the glued
Grassmannian. -/
lemma Proj.rankOneGrassmannianToProjectiveSpace_comp (n : ℕ) :
    Proj.rankOneGrassmannianToProjectiveSpace n ≫
      Proj.projectiveSpaceToRankOneGrassmannian.{u} n =
    𝟙 (Scheme.grassmannianGlueData.{u} 1 (n + 1)).glued := by
  apply (Scheme.rankOneGrassmannianGluedCover n).hom_ext
  intro x
  rw [Category.comp_id, ← Category.assoc]
  have hf : (Scheme.rankOneGrassmannianGluedCover n).f x ≫
      Proj.rankOneGrassmannianToProjectiveSpace n =
      (Proj.projectiveSpaceChartIsoRankOneGrassmannianChart n x.down).inv ≫
        (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
          (ULift.{u} ℤ)) (MvPolynomial.X x.down)).ι :=
    Proj.f_rankOneGrassmannianToProjectiveSpace n x
  rw [hf, Category.assoc]
  have hι : (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1))
      (ULift.{u} ℤ)) (MvPolynomial.X x.down)).ι ≫
      Proj.projectiveSpaceToRankOneGrassmannian.{u} n =
      Proj.projectiveSpaceChartToRankOneGrassmannian n x.down :=
    Proj.ι_projectiveSpaceToRankOneGrassmannian n x
  rw [hι, Proj.projectiveSpaceChartToRankOneGrassmannian, Iso.inv_hom_id_assoc]
  rfl

instance Proj.projectiveSpaceToRankOneGrassmannian_isIso (n : ℕ) :
    IsIso (Proj.projectiveSpaceToRankOneGrassmannian.{u} n) :=
  ⟨Proj.rankOneGrassmannianToProjectiveSpace n,
    Proj.projectiveSpaceToRankOneGrassmannian_comp_inv n,
    Proj.rankOneGrassmannianToProjectiveSpace_comp n⟩

/-- **Projective space is the rank-one Grassmannian**: `ℙⁿ` represents the
Grassmannian functor `Gr(1, n+1)`. -/
noncomputable def Proj.projectiveSpaceGrassmannianRepresentation (n : ℕ) :
    (Scheme.grassmannianFunctor.{u} 1 (n + 1)).RepresentableBy
      (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))) :=
  (Scheme.grassmannianGluedRepresentation.{u} 1 (n + 1)).ofIsoObj
    (asIso (Proj.projectiveSpaceToRankOneGrassmannian.{u} n))

end AlgebraicGeometry.ProjectiveSpectrum

#min_imports
