module

public import Mathlib.Topology.Semicontinuity.Defs
public import StacksAndModuli.API.BoundedComplexEulerChar
public import StacksAndModuli.API.FibrewiseRankSemicontinuous
public import StacksAndModuli.API.ModuleFibreRank

/-!
# Semicontinuity for the fibres of a bounded complex of finite projective modules

Let `R` be a commutative ring and

`K⁰ →[d 0] K¹ →[d 1] ⋯ →[d (n-1)] Kⁿ → 0`

a bounded complex of finite projective `R`-modules.  For every point `p` of `Spec R` the
fibre complex `K⁰ ⊗ κ(p) → K¹ ⊗ κ(p) → ⋯` is a bounded complex of finite-dimensional
`κ(p)`-vector spaces, and this file proves the two semicontinuity statements about how its
cohomology varies with `p`:

* `AlgebraicGeometry.FibrewiseRank.upperSemicontinuous_finrank_cohomology_fibre` (in
  positive degree) and `…upperSemicontinuous_finrank_ker_fibreDiff` (in degree zero, where
  the cohomology of the fibre complex is the kernel of its first differential): each
  `p ↦ dim_{κ(p)} Hⁱ(K^• ⊗ κ(p))` is upper semicontinuous, equivalently
  (`…isClosed_setOf_le_finrank_cohomology_fibre`) each of its jumping loci is closed;
* `AlgebraicGeometry.FibrewiseRank.isLocallyConstant_eulerChar_fibre`: the alternating sum
  of those dimensions is locally constant.

These are exactly the two conclusions of the Semicontinuity Theorem (**Theorem A.6.4** of
*Stacks and Moduli*) once **Theorem A.6.2** (Cohomology and Base Change I, Stacks tag
`07VK`) has replaced `R^i f_* F` by such a complex: A.6.2 produces a bounded complex `K^•`
of finite locally free `A`-modules with `Hⁱ(X_y, F_y) = Hⁱ(K^• ⊗_A κ(y))` for every
`y ∈ Spec A`, and the geometric statement then *is* the statement proved here.  That
reduction, and the scheme-level statement of A.6.4 itself, are in
`StacksAndModuli/SectionA.6-CBC/partA.6.1-linear-algebra.lean`
(`semicontinuity_of_cohomologyComputedByComplex`,
`semicontinuity_of_fibreCohomologyLocallyComputedByComplex`,
`Scheme.Hom.upperSemicontinuous_fibreH`, `Scheme.Hom.isLocallyConstant_fibreEulerChar`),
where A.6.2 is the single recorded obligation.  The content below is the complete algebraic
core of the theorem, with no geometry and no `sorry`.

The engine of the first statement is lower semicontinuity of the fibre rank of a map
(`AlgebraicGeometry.FibrewiseRank.isOpen_setOf_le_rankAt`, itself resting on Stacks tag
`00O0`), applied to the two differentials adjacent to degree `i` through the book's
Equation A.6.5

`hⁱ = dim (Kⁱ ⊗ κ) − rank (dⁱ ⊗ κ) − rank (d^{i-1} ⊗ κ)`,

which is `finrank_cohomology_fibre` below.  The engine of the second is the cancellation of
the differentials in the alternating sum
(`AlgebraicGeometry.BoundedComplex.alternating_sum_finrank_eq_alternating_sum_finrank_cohomology`),
which turns the Euler characteristic into `∑ (-1)^i dim (Kⁱ ⊗ κ)`, a sum of locally constant
functions by `Module.isLocallyConstant_fibreFinrank`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open Module TensorProduct

namespace AlgebraicGeometry.FibrewiseRank

universe u v

section Semicontinuity

variable {R : Type u} [CommRing R] (K : ℕ → Type v) [∀ i, AddCommGroup (K i)]
  [∀ i, Module R (K i)] (d : ∀ i, K i →ₗ[R] K (i + 1))

/-- The fibre of the `i`-th term of the complex `K` at a point of the spectrum. -/
abbrev fibre (p : PrimeSpectrum R) (i : ℕ) : Type max u v := p.residueField ⊗[R] K i

/-- The fibre of the `i`-th differential of the complex `K` at a point of the spectrum. -/
noncomputable abbrev fibreDiff (p : PrimeSpectrum R) (i : ℕ) :
    fibre K p i →ₗ[p.residueField] fibre K p (i + 1) :=
  (d i).baseChange p.residueField

variable {K d}

/-- Base change preserves the complex condition: the fibre of a complex is a complex. -/
theorem range_fibreDiff_le_ker (hd : ∀ j, d (j + 1) ∘ₗ d j = 0) (p : PrimeSpectrum R)
    (i : ℕ) :
    LinearMap.range (fibreDiff K d p i) ≤ LinearMap.ker (fibreDiff K d p (i + 1)) := by
  rw [LinearMap.range_le_ker_iff]
  change (d (i + 1)).baseChange p.residueField ∘ₗ (d i).baseChange p.residueField = 0
  rw [← LinearMap.baseChange_comp, hd i, LinearMap.baseChange_zero]

/-- Base change preserves the vanishing of the last differential. -/
theorem range_fibreDiff_eq_bot (n : ℕ) (hn : d n = 0) (p : PrimeSpectrum R) :
    LinearMap.range (fibreDiff K d p n) = ⊥ := by
  change LinearMap.range ((d n).baseChange p.residueField) = ⊥
  rw [hn, LinearMap.baseChange_zero, LinearMap.range_zero]

variable [∀ i, Module.FinitePresentation R (K i)] [∀ i, Module.Projective R (K i)]

omit [∀ i, Module.Projective R (K i)] in
/-- **Equation A.6.5**: the dimension of the `(i+1)`-st cohomology of the fibre complex is
the dimension of the `(i+1)`-st term minus the ranks of the two adjacent differentials.

This is the identity that converts the two semicontinuity statements below into statements
about the rank of a map of finite projective modules. -/
theorem finrank_cohomology_fibre (hd : ∀ j, d (j + 1) ∘ₗ d j = 0) (p : PrimeSpectrum R)
    (i : ℕ) :
    (finrank p.residueField (BoundedComplex.cohomology (fibreDiff K d p) i) : ℤ) =
      (Module.fibreFinrank R (K (i + 1)) p : ℤ) - rankAt (d (i + 1)) p - rankAt (d i) p := by
  have hcoh := BoundedComplex.finrank_cohomology (fibreDiff K d p) i
    (range_fibreDiff_le_ker hd p i)
  have hrk := LinearMap.finrank_range_add_finrank_ker (fibreDiff K d p (i + 1))
  have hA : Module.fibreFinrank R (K (i + 1)) p =
      finrank p.residueField (fibre K p (i + 1)) := rfl
  have hB : rankAt (d (i + 1)) p =
      finrank p.residueField (LinearMap.range (fibreDiff K d p (i + 1))) := rfl
  have hC : rankAt (d i) p =
      finrank p.residueField (LinearMap.range (fibreDiff K d p i)) := rfl
  rw [hA, hB, hC]
  omega

omit [∀ i, Module.Projective R (K i)] in
/-- The dimension of the kernel of the `i`-th fibre differential is the dimension of the
`i`-th term minus the rank of that differential.  This is the degree-zero companion of
Equation A.6.5: `H⁰` of the fibre complex is the kernel of `d⁰ ⊗ κ`. -/
theorem finrank_ker_fibreDiff (p : PrimeSpectrum R) (i : ℕ) :
    (finrank p.residueField (LinearMap.ker (fibreDiff K d p i)) : ℤ) =
      (Module.fibreFinrank R (K i) p : ℤ) - rankAt (d i) p := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (fibreDiff K d p i)
  have hA : Module.fibreFinrank R (K i) p = finrank p.residueField (fibre K p i) := rfl
  have hB : rankAt (d i) p =
      finrank p.residueField (LinearMap.range (fibreDiff K d p i)) := rfl
  rw [hA, hB]
  omega

/-- An integer-valued function that does not exceed its value at a point on some
neighbourhood of that point is upper semicontinuous. -/
theorem upperSemicontinuous_of_eventually_le {α : Type*} [TopologicalSpace α] {g : α → ℤ}
    (h : ∀ x, ∀ᶠ y in nhds x, g y ≤ g x) : UpperSemicontinuous g :=
  fun x _ hxy ↦ (h x).mono fun _ hz ↦ lt_of_le_of_lt hz hxy

/-- **The fibrewise cohomology dimension does not jump up near a point.**  This is the
local form of part (1) of the Semicontinuity Theorem (Theorem A.6.4), from which both the
`UpperSemicontinuous` statement and the closedness of the jumping loci follow.

The proof is the book's: by Equation A.6.5 the dimension is a locally constant term minus
two lower semicontinuous ones. -/
theorem eventually_finrank_cohomology_fibre_le (hd : ∀ j, d (j + 1) ∘ₗ d j = 0) (i : ℕ)
    (p : PrimeSpectrum R) :
    ∀ᶠ q in nhds p,
      (finrank q.residueField (BoundedComplex.cohomology (fibreDiff K d q) i) : ℤ) ≤
        (finrank p.residueField (BoundedComplex.cohomology (fibreDiff K d p) i) : ℤ) := by
  have hA : ∀ᶠ q in nhds p,
      Module.fibreFinrank R (K (i + 1)) q = Module.fibreFinrank R (K (i + 1)) p :=
    (Module.isLocallyConstant_fibreFinrank (R := R) (M := K (i + 1))).eventually_eq p
  have hB : ∀ᶠ q in nhds p, rankAt (d (i + 1)) p ≤ rankAt (d (i + 1)) q :=
    (isOpen_setOf_le_rankAt (d (i + 1)) (rankAt (d (i + 1)) p)).mem_nhds
      (Set.mem_ofPred.mpr le_rfl)
  have hC : ∀ᶠ q in nhds p, rankAt (d i) p ≤ rankAt (d i) q :=
    (isOpen_setOf_le_rankAt (d i) (rankAt (d i) p)).mem_nhds (Set.mem_ofPred.mpr le_rfl)
  filter_upwards [hA, hB, hC] with q hq hqB hqC
  rw [finrank_cohomology_fibre hd q i, finrank_cohomology_fibre hd p i, hq]
  omega

/-- **Upper semicontinuity of the fibrewise cohomology dimension.**  For a bounded complex
of finite projective modules, the dimension of the `(i+1)`-st cohomology of the fibre can
only jump up on closed subsets of `Spec R`.

This is part (1) of the Semicontinuity Theorem (Theorem A.6.4), in the algebraic form
supplied by Theorem A.6.2. -/
theorem upperSemicontinuous_finrank_cohomology_fibre
    (hd : ∀ j, d (j + 1) ∘ₗ d j = 0) (i : ℕ) :
    UpperSemicontinuous fun p : PrimeSpectrum R ↦
      (finrank p.residueField (BoundedComplex.cohomology (fibreDiff K d p) i) : ℤ) :=
  upperSemicontinuous_of_eventually_le (eventually_finrank_cohomology_fibre_le hd i)

/-- **The jumping loci of the fibrewise cohomology dimension are closed.**  This is the
form in which part (1) of the Semicontinuity Theorem is applied: it is what makes a
condition such as `h⁰ ≥ 1` cut out a closed subset of the base. -/
theorem isClosed_setOf_le_finrank_cohomology_fibre
    (hd : ∀ j, d (j + 1) ∘ₗ d j = 0) (i : ℕ) (c : ℤ) :
    IsClosed {p : PrimeSpectrum R |
      c ≤ (finrank p.residueField (BoundedComplex.cohomology (fibreDiff K d p) i) : ℤ)} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p hp
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hp
  filter_upwards [eventually_finrank_cohomology_fibre_le hd i p] with q hq
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  exact lt_of_le_of_lt hq hp

/-- The dimension of the kernel of a fibre differential does not jump up near a point:
a locally constant term minus a lower semicontinuous one. -/
theorem eventually_finrank_ker_fibreDiff_le (i : ℕ) (p : PrimeSpectrum R) :
    ∀ᶠ q in nhds p,
      (finrank q.residueField (LinearMap.ker (fibreDiff K d q i)) : ℤ) ≤
        (finrank p.residueField (LinearMap.ker (fibreDiff K d p i)) : ℤ) := by
  have hA : ∀ᶠ q in nhds p, Module.fibreFinrank R (K i) q = Module.fibreFinrank R (K i) p :=
    (Module.isLocallyConstant_fibreFinrank (R := R) (M := K i)).eventually_eq p
  have hB : ∀ᶠ q in nhds p, rankAt (d i) p ≤ rankAt (d i) q :=
    (isOpen_setOf_le_rankAt (d i) (rankAt (d i) p)).mem_nhds (Set.mem_ofPred.mpr le_rfl)
  filter_upwards [hA, hB] with q hq hqB
  rw [finrank_ker_fibreDiff q i, finrank_ker_fibreDiff p i, hq]
  omega

/-- **Upper semicontinuity of the dimension of `H⁰` of the fibre complex.**  Taken with
`upperSemicontinuous_finrank_cohomology_fibre` this covers every degree, since `H⁰` of the
fibre complex is the kernel of its first differential. -/
theorem upperSemicontinuous_finrank_ker_fibreDiff (i : ℕ) :
    UpperSemicontinuous fun p : PrimeSpectrum R ↦
      (finrank p.residueField (LinearMap.ker (fibreDiff K d p i)) : ℤ) :=
  upperSemicontinuous_of_eventually_le (eventually_finrank_ker_fibreDiff_le i)

/-- **Local constancy of the Euler characteristic of the fibre complex.**  For a bounded
complex of finite projective modules whose last differential vanishes, the alternating sum
of the dimensions of the cohomology of the fibre is a locally constant function on
`Spec R`.

This is part (2) of the Semicontinuity Theorem (Theorem A.6.4), in the algebraic form
supplied by Theorem A.6.2.  The proof is the book's: the alternating sum telescopes to
`∑ (-1)^i dim_{κ(p)} (Kⁱ ⊗ κ(p))`, in which the differentials no longer appear, and each
term is locally constant because `Kⁱ` is finite projective. -/
theorem isLocallyConstant_eulerChar_fibre (n : ℕ) (hd : ∀ j, d (j + 1) ∘ₗ d j = 0)
    (hn : d n = 0) :
    IsLocallyConstant fun p : PrimeSpectrum R ↦
      (finrank p.residueField (LinearMap.ker (fibreDiff K d p 0)) : ℤ) +
        ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) *
          finrank p.residueField (BoundedComplex.cohomology (fibreDiff K d p) i) := by
  have hfun : (fun p : PrimeSpectrum R ↦
      (finrank p.residueField (LinearMap.ker (fibreDiff K d p 0)) : ℤ) +
        ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) *
          finrank p.residueField (BoundedComplex.cohomology (fibreDiff K d p) i)) =
      fun p : PrimeSpectrum R ↦
        ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * Module.rankAtStalk (K i) p := by
    funext p
    rw [← BoundedComplex.alternating_sum_finrank_eq_alternating_sum_finrank_cohomology
      (fibreDiff K d p) n (range_fibreDiff_le_ker hd p) (range_fibreDiff_eq_bot n hn p)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    have hbridge : Module.fibreFinrank R (K i) p = Module.rankAtStalk (K i) p :=
      Module.fibreFinrank_eq_rankAtStalk R (K i) p
    exact_mod_cast hbridge
  rw [hfun]
  exact BoundedComplex.isLocallyConstant_alternating_sum_rankAtStalk n K

end Semicontinuity

end AlgebraicGeometry.FibrewiseRank
