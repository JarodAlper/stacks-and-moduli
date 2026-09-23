module

public import StacksAndModuli.API.PolynomialVectorRankGrowth
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNextDegree
public import Mathlib.Algebra.MvPolynomial.Coeff
public import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Binary forms as bounded univariate polynomials

Dehomogenization on the standard chart `X₀ = 1` identifies binary forms of degree `e`
with univariate polynomials of degree strictly less than `e + 1`.  Under this
identification, multiplication by `X₀` is the inclusion into the next bounded-degree
piece, while multiplication by `X₁` is multiplication by the univariate variable `X`.

The vector-valued version therefore identifies the span of the two projective-variable
images of a subspace with `Submodule.forwardSpan` for coordinatewise multiplication by
`X`.  This is the homogeneous-to-univariate bridge used by the growth-one edge of the
projective-line Gotzmann argument.

Main declarations:

* `MvPolynomial.binaryDehomogenize`;
* `MvPolynomial.binaryDehomogenizeDegreeEquiv`;
* `MvPolynomial.binaryDehomogenizeVector`;
* `MvPolynomial.binaryNextSpan_map_binaryDehomogenizeVector`;
* `MvPolynomial.finrank_binaryNextSpan_eq_add_one_of_eq_add_one`;
* `MvPolynomial.finrank_binaryNextSpan_eq_add_of_large`;
* `MvPolynomial.finrank_binaryNextSpan_add_nextQuotientRank_of_large`.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

open Polynomial

namespace MvPolynomial

variable (K : Type*) [Field K]

/-- Set `X₀ = 1` and rename `X₁` as the univariate variable `X`. -/
noncomputable def binaryDehomogenize :
    MvPolynomial (Fin 2) K →ₐ[K] K[X] :=
  MvPolynomial.aeval fun i ↦ Fin.cases 1 (fun _ ↦ Polynomial.X) i

@[simp]
theorem binaryDehomogenize_X_zero :
    binaryDehomogenize K (MvPolynomial.X (0 : Fin 2)) = 1 := by
  simp [binaryDehomogenize]

@[simp]
theorem binaryDehomogenize_X_one :
    binaryDehomogenize K (MvPolynomial.X (1 : Fin 2)) = Polynomial.X := by
  simp only [binaryDehomogenize, MvPolynomial.aeval_def, MvPolynomial.eval₂_X]
  change Fin.cases (1 : K[X]) (fun _ : Fin 1 ↦ (Polynomial.X : K[X]))
      (Fin.succ (0 : Fin 1)) = Polynomial.X
  rfl

/-- Dehomogenizing a binary monomial retains precisely its `X₁` exponent. -/
theorem binaryDehomogenize_monomial (d : Fin 2 →₀ ℕ) (a : K) :
    binaryDehomogenize K (MvPolynomial.monomial d a) =
      Polynomial.monomial (d 1) a := by
  rw [MvPolynomial.monomial_fin_two]
  simp [Polynomial.C_mul_X_pow_eq_monomial]

/-- A binary form of degree `e` dehomogenizes to a polynomial of degree less than
`e + 1`. -/
theorem binaryDehomogenize_mem_degreeLT {e : ℕ}
    {p : MvPolynomial (Fin 2) K} (hp : p.IsHomogeneous e) :
    binaryDehomogenize K p ∈ Polynomial.degreeLT K (e + 1) := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp [binaryDehomogenize]
  | add p q hp hq ihp ihq =>
      simpa only [map_add] using
        (Polynomial.degreeLT K (e + 1)).add_mem ihp ihq
  | monomial d a hd =>
      have hone : (fun _ : Fin 2 ↦ (1 : ℕ)) = (1 : Fin 2 → ℕ) := by
        ext
        rfl
      have hdegree : d.degree = e := by
        rw [Finsupp.degree_eq_weight_one, hone]
        exact hd
      have hde : d (1 : Fin 2) ≤ e :=
        (Finsupp.le_degree (1 : Fin 2) d).trans_eq hdegree
      rw [binaryDehomogenize_monomial]
      exact Polynomial.mem_degreeLT.mpr <|
        (Polynomial.degree_monomial_le _ _).trans_lt <|
          WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hde)

/-- Degree-`e` binary forms dehomogenize linearly into the bounded univariate
polynomials of degree less than `e + 1`. -/
noncomputable def binaryDehomogenizeDegree (e : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 2) K e →ₗ[K]
      Polynomial.degreeLT K (e + 1) :=
  LinearMap.codRestrict (Polynomial.degreeLT K (e + 1))
    ((binaryDehomogenize K).toLinearMap.comp
      (MvPolynomial.homogeneousSubmodule (Fin 2) K e).subtype)
    fun p ↦ binaryDehomogenize_mem_degreeLT K p.2

@[simp]
theorem binaryDehomogenizeDegree_apply_val (e : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) K e) :
    ((binaryDehomogenizeDegree K e p : Polynomial.degreeLT K (e + 1)) : K[X]) =
      binaryDehomogenize K p.1 :=
  rfl

/-- Every polynomial of degree less than `e + 1` is the dehomogenization of a binary
form of degree `e`. -/
theorem binaryDehomogenizeDegree_surjective (e : ℕ) :
    Function.Surjective (binaryDehomogenizeDegree K e) := by
  classical
  intro q
  let p : MvPolynomial (Fin 2) K :=
    ∑ i : Fin (e + 1),
      MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) (e - (i : ℕ)) +
          Finsupp.single (1 : Fin 2) (i : ℕ))
        (q.1.coeff i)
  have hp : p ∈ MvPolynomial.homogeneousSubmodule (Fin 2) K e := by
    dsimp only [p]
    apply Submodule.sum_mem
    intro i _
    exact MvPolynomial.isHomogeneous_monomial _ (by
      rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
      omega)
  refine ⟨⟨p, hp⟩, ?_⟩
  apply Subtype.ext
  change binaryDehomogenize K p = q.1
  have hexponent (i : Fin (e + 1)) :
      (Finsupp.single (0 : Fin 2) (e - (i : ℕ)) +
        Finsupp.single (1 : Fin 2) (i : ℕ)) (1 : Fin 2) = i := by
    simp
  dsimp only [p]
  simp_rw [map_sum, binaryDehomogenize_monomial, hexponent]
  simpa using q.1.sum_fin (Polynomial.monomial ·) (by simp)
    (Polynomial.mem_degreeLT.mp q.2)

/-- The source and target of degreewise binary dehomogenization have the same finite
dimension. -/
theorem finrank_binaryDehomogenizeDegree (K : Type*) [Field K] (e : ℕ) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin 2) K e) =
      Module.finrank K (Polynomial.degreeLT K (e + 1)) := by
  rw [Module.finrank_eq_card_basis
      (MvPolynomial.homogeneousSubmoduleFinBasis 1 K e),
    Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K (e + 1))]
  simp
  omega

/-- Degreewise binary dehomogenization is injective over a field. -/
theorem binaryDehomogenizeDegree_injective (K : Type*) [Field K] (e : ℕ) :
    Function.Injective (binaryDehomogenizeDegree K e) := by
  letI : Module.Finite K
      (MvPolynomial.homogeneousSubmodule (Fin 2) K e) :=
    Module.Finite.of_basis (MvPolynomial.homogeneousSubmoduleFinBasis 1 K e)
  letI : Module.Finite K (Polynomial.degreeLT K (e + 1)) :=
    Module.Finite.of_basis (Polynomial.degreeLT.basis K (e + 1))
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (finrank_binaryDehomogenizeDegree K e)).mpr
      (binaryDehomogenizeDegree_surjective K e)

/-- Binary forms of degree `e` are linearly equivalent to univariate polynomials of
degree less than `e + 1`. -/
noncomputable def binaryDehomogenizeDegreeEquiv (K : Type*) [Field K] (e : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 2) K e ≃ₗ[K]
      Polynomial.degreeLT K (e + 1) :=
  LinearEquiv.ofBijective (binaryDehomogenizeDegree K e)
    ⟨binaryDehomogenizeDegree_injective K e,
      binaryDehomogenizeDegree_surjective K e⟩

@[simp]
theorem binaryDehomogenizeDegreeEquiv_apply_val (K : Type*) [Field K] (e : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) K e) :
    (((binaryDehomogenizeDegreeEquiv K e p : Polynomial.degreeLT K (e + 1)) :
        K[X])) = binaryDehomogenize K p.1 :=
  rfl

/-- Multiplication by one binary variable between consecutive homogeneous pieces. -/
noncomputable def binaryMulDegree (e : ℕ) (j : Fin 2) :
    MvPolynomial.homogeneousSubmodule (Fin 2) K e →ₗ[K]
      MvPolynomial.homogeneousSubmodule (Fin 2) K (e + 1) :=
  LinearMap.codRestrict
    (MvPolynomial.homogeneousSubmodule (Fin 2) K (e + 1))
    ((LinearMap.mulLeft K (MvPolynomial.X j)).comp
      (MvPolynomial.homogeneousSubmodule (Fin 2) K e).subtype)
    fun p ↦ by
      change (MvPolynomial.X j * p.1).IsHomogeneous (e + 1)
      simpa only [Nat.add_comm] using
        (MvPolynomial.isHomogeneous_X K j).mul p.2

@[simp]
theorem binaryDehomogenizeDegree_mul_zero (e : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) K e) :
    (((binaryDehomogenizeDegree K (e + 1)
        (binaryMulDegree K e 0 p) : Polynomial.degreeLT K (e + 2)) : K[X])) =
      ((binaryDehomogenizeDegree K e p : Polynomial.degreeLT K (e + 1)) : K[X]) := by
  change binaryDehomogenize K (MvPolynomial.X 0 * p.1) =
    binaryDehomogenize K p.1
  rw [map_mul, binaryDehomogenize_X_zero, one_mul]

@[simp]
theorem binaryDehomogenizeDegree_mul_one (e : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin 2) K e) :
    (((binaryDehomogenizeDegree K (e + 1)
        (binaryMulDegree K e 1 p) : Polynomial.degreeLT K (e + 2)) : K[X])) =
      Polynomial.X *
        ((binaryDehomogenizeDegree K e p : Polynomial.degreeLT K (e + 1)) : K[X]) := by
  change binaryDehomogenize K (MvPolynomial.X 1 * p.1) =
    Polynomial.X * binaryDehomogenize K p.1
  rw [map_mul, binaryDehomogenize_X_one]

/-- Coordinatewise dehomogenization of binary-form vectors. -/
noncomputable def binaryDehomogenizeVector (I : Type*) (e : ℕ) :
    (I → MvPolynomial.homogeneousSubmodule (Fin 2) K e) →ₗ[K]
      (I → K[X]) :=
  LinearMap.pi fun i ↦
    ((binaryDehomogenize K).toLinearMap.comp
      (MvPolynomial.homogeneousSubmodule (Fin 2) K e).subtype).comp
        (LinearMap.proj i)

@[simp]
theorem binaryDehomogenizeVector_apply (I : Type*) (e : ℕ)
    (p : I → MvPolynomial.homogeneousSubmodule (Fin 2) K e) (i : I) :
    binaryDehomogenizeVector K I e p i = binaryDehomogenize K (p i).1 :=
  rfl

/-- Coordinatewise dehomogenization is injective over a field. -/
theorem binaryDehomogenizeVector_injective (K : Type*) [Field K]
    (I : Type*) (e : ℕ) :
    Function.Injective (binaryDehomogenizeVector K I e) := by
  intro p q hpq
  funext i
  apply binaryDehomogenizeDegree_injective K e
  apply Subtype.ext
  exact congrFun hpq i

/-- A dehomogenized degree-`e` vector has every coordinate of degree less than
`e + 1`. -/
theorem binaryDehomogenizeVector_mem_vectorDegreeLT (I : Type*) (e : ℕ)
    (p : I → MvPolynomial.homogeneousSubmodule (Fin 2) K e) :
    binaryDehomogenizeVector K I e p ∈
      Polynomial.vectorDegreeLT K I (e + 1) := by
  rw [Polynomial.mem_vectorDegreeLT]
  intro i
  exact binaryDehomogenize_mem_degreeLT K (p i).2

/-- Coordinatewise multiplication by one binary variable. -/
noncomputable def binaryMulVector (I : Type*) (e : ℕ) (j : Fin 2) :
    (I → MvPolynomial.homogeneousSubmodule (Fin 2) K e) →ₗ[K]
      (I → MvPolynomial.homogeneousSubmodule (Fin 2) K (e + 1)) :=
  LinearMap.pi fun i ↦ (binaryMulDegree K e j).comp (LinearMap.proj i)

@[simp]
theorem binaryMulVector_apply (I : Type*) (e : ℕ) (j : Fin 2)
    (p : I → MvPolynomial.homogeneousSubmodule (Fin 2) K e) (i : I) :
    binaryMulVector K I e j p i = binaryMulDegree K e j (p i) :=
  rfl

/-- Dehomogenization intertwines coordinatewise multiplication by `X₀` with the
identity. -/
theorem binaryDehomogenizeVector_comp_mul_zero (I : Type*) (e : ℕ) :
    (binaryDehomogenizeVector K I (e + 1)).comp
        (binaryMulVector K I e 0) =
      binaryDehomogenizeVector K I e := by
  apply LinearMap.ext
  intro p
  funext i
  change binaryDehomogenize K (MvPolynomial.X 0 * (p i).1) =
    binaryDehomogenize K (p i).1
  rw [map_mul, binaryDehomogenize_X_zero, one_mul]

/-- Dehomogenization intertwines coordinatewise multiplication by `X₁` with
coordinatewise multiplication by the univariate `X`. -/
theorem binaryDehomogenizeVector_comp_mul_one (I : Type*) (e : ℕ) :
    (binaryDehomogenizeVector K I (e + 1)).comp
        (binaryMulVector K I e 1) =
      (Polynomial.xMulVector K I).comp
        (binaryDehomogenizeVector K I e) := by
  apply LinearMap.ext
  intro p
  funext i
  change binaryDehomogenize K (MvPolynomial.X 1 * (p i).1) =
    Polynomial.X * binaryDehomogenize K (p i).1
  rw [map_mul, binaryDehomogenize_X_one]

/-- The span of the `X₀`- and `X₁`-multiples of a binary-form subspace. -/
abbrev binaryNextSpan {I : Type*} {e : ℕ}
    (V : Submodule K
      (I → MvPolynomial.homogeneousSubmodule (Fin 2) K e)) :
    Submodule K
      (I → MvPolynomial.homogeneousSubmodule (Fin 2) K (e + 1)) :=
  V.map (binaryMulVector K I e 0) ⊔ V.map (binaryMulVector K I e 1)

/-- The dehomogenized image of a binary-form subspace. -/
abbrev binaryDehomogenizedSubmodule {I : Type*} {e : ℕ}
    (V : Submodule K
      (I → MvPolynomial.homogeneousSubmodule (Fin 2) K e)) :
    Submodule K (I → K[X]) :=
  V.map (binaryDehomogenizeVector K I e)

/-- Dehomogenization carries the two-variable successor span to the univariate
forward span. -/
theorem binaryNextSpan_map_binaryDehomogenizeVector {I : Type*} {e : ℕ}
    (V : Submodule K
      (I → MvPolynomial.homogeneousSubmodule (Fin 2) K e)) :
    (binaryNextSpan K V).map (binaryDehomogenizeVector K I (e + 1)) =
      (binaryDehomogenizedSubmodule K V).forwardSpan
        (Polynomial.xMulVector K I) := by
  change
    (V.map (binaryMulVector K I e 0) ⊔
        V.map (binaryMulVector K I e 1)).map
          (binaryDehomogenizeVector K I (e + 1)) =
      V.map (binaryDehomogenizeVector K I e) ⊔
        (V.map (binaryDehomogenizeVector K I e)).map
          (Polynomial.xMulVector K I)
  rw [Submodule.map_sup, ← Submodule.map_comp, ← Submodule.map_comp,
    binaryDehomogenizeVector_comp_mul_zero,
    binaryDehomogenizeVector_comp_mul_one, Submodule.map_comp]

/-- The dehomogenized image of a degree-`e` binary-form subspace is bounded by
univariate degree `e`. -/
theorem binaryDehomogenizedSubmodule_le_vectorDegreeLT {I : Type*} {e : ℕ}
    (V : Submodule K
      (I → MvPolynomial.homogeneousSubmodule (Fin 2) K e)) :
    binaryDehomogenizedSubmodule K V ≤
      Polynomial.vectorDegreeLT K I (e + 1) := by
  rintro q ⟨p, hp, rfl⟩
  exact binaryDehomogenizeVector_mem_vectorDegreeLT K I e p

/-- Injective vector dehomogenization preserves the finite dimension of every
binary-form subspace. -/
theorem finrank_binaryDehomogenizedSubmodule {I : Type*} {e : ℕ}
    (V : Submodule K
      (I → MvPolynomial.homogeneousSubmodule (Fin 2) K e))
    [FiniteDimensional K V] :
    Module.finrank K (binaryDehomogenizedSubmodule K V) =
      Module.finrank K V :=
  Submodule.finrank_map_eq_of_injective V
    (binaryDehomogenizeVector K I e)
    (binaryDehomogenizeVector_injective K I e)

/-- Growth by one of the two-variable successor span persists for one further
degree.

This is the binary homogeneous form of the growth-one edge of Gotzmann
persistence.  It is valid over every field and for arbitrary vector rank `I`; no
infinitude hypothesis on the field is used. -/
theorem finrank_binaryNextSpan_eq_add_one_of_eq_add_one
    (I : Type*) (e : ℕ)
    (V : Submodule K
      (I → MvPolynomial.homogeneousSubmodule (Fin 2) K e))
    [FiniteDimensional K V]
    (hgrowth : Module.finrank K (binaryNextSpan K V) =
      Module.finrank K V + 1) :
    Module.finrank K (binaryNextSpan K (binaryNextSpan K V)) =
      Module.finrank K (binaryNextSpan K V) + 1 := by
  let W := binaryNextSpan K V
  let D := binaryDehomogenizedSubmodule K V
  letI : FiniteDimensional K (V.map (binaryMulVector K I e 0)) :=
    Module.Finite.map V (binaryMulVector K I e 0)
  letI : FiniteDimensional K (V.map (binaryMulVector K I e 1)) :=
    Module.Finite.map V (binaryMulVector K I e 1)
  letI : FiniteDimensional K W := by
    dsimp only [W, binaryNextSpan]
    exact Submodule.finiteDimensional_sup
      (V.map (binaryMulVector K I e 0))
      (V.map (binaryMulVector K I e 1))
  letI : FiniteDimensional K D :=
    Module.Finite.map V (binaryDehomogenizeVector K I e)
  letI : FiniteDimensional K
      (W.map (binaryMulVector K I (e + 1) 0)) :=
    Module.Finite.map W (binaryMulVector K I (e + 1) 0)
  letI : FiniteDimensional K
      (W.map (binaryMulVector K I (e + 1) 1)) :=
    Module.Finite.map W (binaryMulVector K I (e + 1) 1)
  letI : FiniteDimensional K (binaryNextSpan K W) := by
    dsimp only [binaryNextSpan]
    exact Submodule.finiteDimensional_sup
      (W.map (binaryMulVector K I (e + 1) 0))
      (W.map (binaryMulVector K I (e + 1) 1))
  have hDfinrank : Module.finrank K D = Module.finrank K V :=
    finrank_binaryDehomogenizedSubmodule K V
  have hWfinrank :
      Module.finrank K
          (W.map (binaryDehomogenizeVector K I (e + 1))) =
        Module.finrank K W :=
    Submodule.finrank_map_eq_of_injective W
      (binaryDehomogenizeVector K I (e + 1))
      (binaryDehomogenizeVector_injective K I (e + 1))
  have hbridge :
      W.map (binaryDehomogenizeVector K I (e + 1)) =
        D.forwardSpan (Polynomial.xMulVector K I) := by
    simpa only [W, D] using
      binaryNextSpan_map_binaryDehomogenizeVector K V
  have hgrowthD :
      Module.finrank K (D.forwardSpan (Polynomial.xMulVector K I)) =
        Module.finrank K D + 1 := by
    rw [← hbridge, hWfinrank, hDfinrank]
    exact hgrowth
  have hdegreeD :
      D.forwardSpan (Polynomial.xMulVector K I) ≤
        Polynomial.vectorDegreeLT K I (e + 2) := by
    rw [← hbridge]
    exact binaryDehomogenizedSubmodule_le_vectorDegreeLT K W
  have hpersist :=
    Polynomial.finrank_forwardSpan_xMulVector_eq_add_one
      K I D (e + 2) hgrowthD hdegreeD
  have hbridgeNext :
      (binaryNextSpan K W).map
          (binaryDehomogenizeVector K I (e + 2)) =
        (D.forwardSpan (Polynomial.xMulVector K I)).forwardSpan
          (Polynomial.xMulVector K I) := by
    rw [← hbridge]
    exact binaryNextSpan_map_binaryDehomogenizeVector K W
  have hnextFinrank :
      Module.finrank K
          ((binaryNextSpan K W).map
            (binaryDehomogenizeVector K I (e + 2))) =
        Module.finrank K (binaryNextSpan K W) :=
    Submodule.finrank_map_eq_of_injective (binaryNextSpan K W)
      (binaryDehomogenizeVector K I (e + 2))
      (binaryDehomogenizeVector_injective K I (e + 2))
  change Module.finrank K (binaryNextSpan K W) =
    Module.finrank K W + 1
  calc
    Module.finrank K (binaryNextSpan K W) =
        Module.finrank K
          ((binaryNextSpan K W).map
            (binaryDehomogenizeVector K I (e + 2))) := hnextFinrank.symm
    _ = Module.finrank K
        ((D.forwardSpan (Polynomial.xMulVector K I)).forwardSpan
          (Polynomial.xMulVector K I)) :=
      congrArg
        (fun U : Submodule K (I → K[X]) ↦ Module.finrank K U)
        hbridgeNext
    _ = Module.finrank K
        (D.forwardSpan (Polynomial.xMulVector K I)) + 1 := hpersist
    _ = Module.finrank K W + 1 := by
      rw [← hbridge, hWfinrank]

/-- Growth by an arbitrary amount of the two-variable successor span persists for one
further degree once the first successor space is too large to have polynomial-module
rank below that amount.

The largeness hypothesis is essential for increments greater than one.  After binary
dehomogenization it is exactly the capacity inequality needed by
`Polynomial.finrank_forwardSpan_xMulVector_eq_add_of_large`. -/
theorem finrank_binaryNextSpan_eq_add_of_large
    (I : Type*) [Finite I] (e : ℕ)
    (V : Submodule K
      (I → MvPolynomial.homogeneousSubmodule (Fin 2) K e))
    [FiniteDimensional K V] (s : ℕ)
    (hgrowth : Module.finrank K (binaryNextSpan K V) =
      Module.finrank K V + s)
    (hlarge : (s - 1) * (e + 2) <
      Module.finrank K (binaryNextSpan K V)) :
    Module.finrank K (binaryNextSpan K (binaryNextSpan K V)) =
      Module.finrank K (binaryNextSpan K V) + s := by
  let W := binaryNextSpan K V
  let D := binaryDehomogenizedSubmodule K V
  letI : FiniteDimensional K (V.map (binaryMulVector K I e 0)) :=
    Module.Finite.map V (binaryMulVector K I e 0)
  letI : FiniteDimensional K (V.map (binaryMulVector K I e 1)) :=
    Module.Finite.map V (binaryMulVector K I e 1)
  letI : FiniteDimensional K W := by
    dsimp only [W, binaryNextSpan]
    exact Submodule.finiteDimensional_sup
      (V.map (binaryMulVector K I e 0))
      (V.map (binaryMulVector K I e 1))
  letI : FiniteDimensional K D :=
    Module.Finite.map V (binaryDehomogenizeVector K I e)
  letI : FiniteDimensional K
      (W.map (binaryMulVector K I (e + 1) 0)) :=
    Module.Finite.map W (binaryMulVector K I (e + 1) 0)
  letI : FiniteDimensional K
      (W.map (binaryMulVector K I (e + 1) 1)) :=
    Module.Finite.map W (binaryMulVector K I (e + 1) 1)
  letI : FiniteDimensional K (binaryNextSpan K W) := by
    dsimp only [binaryNextSpan]
    exact Submodule.finiteDimensional_sup
      (W.map (binaryMulVector K I (e + 1) 0))
      (W.map (binaryMulVector K I (e + 1) 1))
  have hDfinrank : Module.finrank K D = Module.finrank K V :=
    finrank_binaryDehomogenizedSubmodule K V
  have hWfinrank :
      Module.finrank K
          (W.map (binaryDehomogenizeVector K I (e + 1))) =
        Module.finrank K W :=
    Submodule.finrank_map_eq_of_injective W
      (binaryDehomogenizeVector K I (e + 1))
      (binaryDehomogenizeVector_injective K I (e + 1))
  have hbridge :
      W.map (binaryDehomogenizeVector K I (e + 1)) =
        D.forwardSpan (Polynomial.xMulVector K I) := by
    simpa only [W, D] using
      binaryNextSpan_map_binaryDehomogenizeVector K V
  have hgrowthD :
      Module.finrank K (D.forwardSpan (Polynomial.xMulVector K I)) =
        Module.finrank K D + s := by
    rw [← hbridge, hWfinrank, hDfinrank]
    exact hgrowth
  have hdegreeD :
      D.forwardSpan (Polynomial.xMulVector K I) ≤
        Polynomial.vectorDegreeLT K I (e + 2) := by
    rw [← hbridge]
    exact binaryDehomogenizedSubmodule_le_vectorDegreeLT K W
  have hlargeD : (s - 1) * (e + 2) <
      Module.finrank K
        (D.forwardSpan (Polynomial.xMulVector K I)) := by
    rw [← hbridge, hWfinrank]
    exact hlarge
  have hpersist :=
    Polynomial.finrank_forwardSpan_xMulVector_eq_add_of_large
      K I D s (e + 2) hgrowthD hdegreeD hlargeD
  have hbridgeNext :
      (binaryNextSpan K W).map
          (binaryDehomogenizeVector K I (e + 2)) =
        (D.forwardSpan (Polynomial.xMulVector K I)).forwardSpan
          (Polynomial.xMulVector K I) := by
    rw [← hbridge]
    exact binaryNextSpan_map_binaryDehomogenizeVector K W
  have hnextFinrank :
      Module.finrank K
          ((binaryNextSpan K W).map
            (binaryDehomogenizeVector K I (e + 2))) =
        Module.finrank K (binaryNextSpan K W) :=
    Submodule.finrank_map_eq_of_injective (binaryNextSpan K W)
      (binaryDehomogenizeVector K I (e + 2))
      (binaryDehomogenizeVector_injective K I (e + 2))
  change Module.finrank K (binaryNextSpan K W) =
    Module.finrank K W + s
  calc
    Module.finrank K (binaryNextSpan K W) =
        Module.finrank K
          ((binaryNextSpan K W).map
            (binaryDehomogenizeVector K I (e + 2))) := hnextFinrank.symm
    _ = Module.finrank K
        ((D.forwardSpan (Polynomial.xMulVector K I)).forwardSpan
          (Polynomial.xMulVector K I)) :=
      congrArg
        (fun U : Submodule K (I → K[X]) ↦ Module.finrank K U)
        hbridgeNext
    _ = Module.finrank K
        (D.forwardSpan (Polynomial.xMulVector K I)) + s := hpersist
    _ = Module.finrank K W + s := by
      rw [← hbridge, hWfinrank]

/-- Subtraction-free quotient-rank form of binary Gotzmann persistence.

Suppose the relation spaces in degrees `e` and `e + 1` have complementary
quotient ranks `q₀` and `q₁` in `I` copies of the binary forms.  If the quotient
rank grows by `a`, the ambient rank splits as `a + s`, and the numerical largeness
condition holds, then the next relation space has complementary quotient rank
`q₁ + a`.  This formulation avoids truncated natural-number subtraction and is the
form used by the projective-line Quot-scheme seed argument. -/
theorem finrank_binaryNextSpan_add_nextQuotientRank_of_large
    (I : Type*) [Fintype I] (e : ℕ)
    (V : Submodule K
      (I → MvPolynomial.homogeneousSubmodule (Fin 2) K e))
    [FiniteDimensional K V] (q₀ q₁ a s : ℕ)
    (hV : Module.finrank K V + q₀ = Fintype.card I * (e + 1))
    (hnext : Module.finrank K (binaryNextSpan K V) + q₁ =
      Fintype.card I * (e + 2))
    (hquotientGrowth : q₁ = q₀ + a)
    (hambientSplit : Fintype.card I = a + s)
    (hs : 0 < s)
    (hlarge : q₁ < (a + 1) * (e + 2)) :
    Module.finrank K (binaryNextSpan K (binaryNextSpan K V)) + (q₁ + a) =
      Fintype.card I * (e + 3) := by
  have hambientStep :
      Fintype.card I * (e + 2) =
        Fintype.card I * (e + 1) + Fintype.card I := by
    ring
  have hgrowth : Module.finrank K (binaryNextSpan K V) =
      Module.finrank K V + s := by
    apply Nat.add_right_cancel (m := q₁)
    calc
      Module.finrank K (binaryNextSpan K V) + q₁ =
          Fintype.card I * (e + 2) := hnext
      _ = Fintype.card I * (e + 1) + Fintype.card I := hambientStep
      _ = (Module.finrank K V + q₀) + (a + s) := by
        rw [hV, hambientSplit]
      _ = (Module.finrank K V + s) + (q₀ + a) := by omega
      _ = (Module.finrank K V + s) + q₁ := by
        rw [hquotientGrowth]
  have hsum :
      (a + 1) * (e + 2) + (s - 1) * (e + 2) =
        (a + s) * (e + 2) := by
    rw [← Nat.add_mul]
    congr 1
    omega
  have hlargeAugmented :=
    Nat.add_lt_add_right hlarge ((s - 1) * (e + 2))
  rw [hsum, ← hambientSplit, ← hnext] at hlargeAugmented
  have hrelationLarge :
      (s - 1) * (e + 2) < Module.finrank K (binaryNextSpan K V) := by
    omega
  have hpersist := finrank_binaryNextSpan_eq_add_of_large
    K I e V s hgrowth hrelationLarge
  calc
    Module.finrank K (binaryNextSpan K (binaryNextSpan K V)) + (q₁ + a) =
        (Module.finrank K (binaryNextSpan K V) + s) + (q₁ + a) := by
      rw [hpersist]
    _ = (Module.finrank K (binaryNextSpan K V) + q₁) + (a + s) := by
      omega
    _ = Fintype.card I * (e + 2) + Fintype.card I := by
      rw [hnext, ← hambientSplit]
    _ = Fintype.card I * (e + 3) := by ring

end MvPolynomial

end
