module

public import StacksAndModuli.API.DeterminantalFibreRank
public import StacksAndModuli.API.RelativeFibreExactnessInterface

/-!
# Expected ranks and determinantal grade loci for finite free complexes

This file records a finite free chain complex by matrices in chosen standard bases.  It
packages the numerical expected ranks used in the Buchsbaum--Eisenbud acyclicity criterion,
the scheme-theoretic upper bounds on the ranks of its differentials, and their compatibility
with coefficient extension and residue-field rank.

For a relative fibre over a ring map `R → S`, it also defines the simultaneous locus on
which the ideal of expected-size minors in homological degree `i` either becomes the unit
ideal or contains an `i`-term sequence regular on the localized fibre.  The final theorem
assembles fixed-sequence relative openness degree by degree into openness of this full
determinantal locus.  This is the finite-complex bookkeeping between the fixed-sequence
input of Stacks Project tag 00RA and the still-missing Buchsbaum--Eisenbud implication in
tag 00RB.

No acyclicity criterion is asserted here.

Main declarations:

* `Matrix.FiniteFreeComplex`;
* `Matrix.FiniteFreeComplex.toChainComplex`;
* `Matrix.FiniteFreeComplex.ExpectedRanks`;
* `Matrix.FiniteFreeComplex.HasExpectedRankBounds`;
* `Matrix.FiniteFreeComplex.rank_residueField_le_expectedRank`;
* `Matrix.FiniteFreeComplex.relativeFibreBuchsbaumEisenbudLocus`;
* `Matrix.FiniteFreeComplex.isOpen_relativeFibreBuchsbaumEisenbudLocus`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory

universe u v

namespace Matrix

/-- A chain complex of finite free modules, recorded by matrices in fixed standard bases.
The matrix `differential i` represents the map in homological degree `i + 1 ⟶ i`. -/
structure FiniteFreeComplex (R : Type u) [CommRing R] where
  termRank : ℕ → ℕ
  differential : (i : ℕ) →
    Matrix (Fin (termRank i)) (Fin (termRank (i + 1))) R
  differential_sq : ∀ i : ℕ, differential i * differential (i + 1) = 0

namespace FiniteFreeComplex

variable {R : Type u} [CommRing R]

/-- Change coefficients in a matrix finite free complex. -/
def map {S : Type v} [CommRing S] (C : FiniteFreeComplex R) (f : R →+* S) :
    FiniteFreeComplex S where
  termRank := C.termRank
  differential i := (C.differential i).map f
  differential_sq i := by
    rw [← Matrix.map_mul, C.differential_sq]
    exact Matrix.map_zero f (map_zero f)

@[simp]
theorem map_termRank {S : Type v} [CommRing S] (C : FiniteFreeComplex R)
    (f : R →+* S) (i : ℕ) :
    (C.map f).termRank i = C.termRank i :=
  rfl

@[simp]
theorem map_differential {S : Type v} [CommRing S] (C : FiniteFreeComplex R)
    (f : R →+* S) (i : ℕ) :
    (C.map f).differential i = (C.differential i).map f :=
  rfl

/-- The chain complex of modules represented by a matrix finite free complex. -/
noncomputable def toChainComplex (C : FiniteFreeComplex R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of
    (fun i ↦ ModuleCat.of R (Fin (C.termRank i) → R))
    (fun i ↦ ModuleCat.ofHom (Matrix.toLin' (C.differential i)))
    (fun i ↦ by
      apply ModuleCat.Hom.ext
      change (Matrix.toLin' (C.differential i)).comp
        (Matrix.toLin' (C.differential (i + 1))) = 0
      rw [← Matrix.toLin'_mul, C.differential_sq]
      simp)

@[simp]
theorem toChainComplex_X (C : FiniteFreeComplex R) (i : ℕ) :
    (C.toChainComplex.X i : Type u) = (Fin (C.termRank i) → R) :=
  rfl

@[simp]
theorem toChainComplex_d (C : FiniteFreeComplex R) (i : ℕ) :
    (C.toChainComplex.d (i + 1) i).hom = Matrix.toLin' (C.differential i) := by
  simp [toChainComplex]

/-- The matrix complex is zero above `N`. -/
def IsBoundedAbove (C : FiniteFreeComplex R) (N : ℕ) : Prop :=
  ∀ i : ℕ, N < i → C.termRank i = 0

/-- A rank function satisfying the alternating expected-rank recursion from the top.

The value `rank i` is the expected rank of `differential i`, hence of the map in degree
`i + 1 ⟶ i`.  The equations say `rank i + rank (i + 1) = termRank (i + 1)`, with the
virtual differential above the bound having rank zero. -/
structure ExpectedRanks (C : FiniteFreeComplex R) (N : ℕ) where
  rank : ℕ → ℕ
  terminal : rank N = 0
  add_succ : ∀ i : ℕ, i < N →
    rank i + rank (i + 1) = C.termRank (i + 1)

namespace ExpectedRanks

variable {C : FiniteFreeComplex R} {N : ℕ}

/-- Expected ranks are unchanged by coefficient extension. -/
def map {S : Type v} [CommRing S] (r : C.ExpectedRanks N) (f : R →+* S) :
    (C.map f).ExpectedRanks N where
  rank := r.rank
  terminal := r.terminal
  add_succ := r.add_succ

@[simp]
theorem map_rank {S : Type v} [CommRing S] (r : C.ExpectedRanks N)
    (f : R →+* S) (i : ℕ) :
    (r.map f).rank i = r.rank i :=
  rfl

end ExpectedRanks

/-- Every differential has rank at most its expected rank, expressed scheme-theoretically
by vanishing of the minors one size larger. -/
def HasExpectedRankBounds (C : FiniteFreeComplex R) {N : ℕ}
    (r : C.ExpectedRanks N) : Prop :=
  ∀ i : ℕ, i < N → Matrix.minorIdeal (C.differential i) (r.rank i + 1) = ⊥

/-- Expected-rank upper bounds are preserved by arbitrary coefficient extension. -/
theorem HasExpectedRankBounds.map {S : Type v} [CommRing S]
    {C : FiniteFreeComplex R} {N : ℕ} (r : C.ExpectedRanks N)
    (h : C.HasExpectedRankBounds r) (f : R →+* S) :
    (C.map f).HasExpectedRankBounds (r.map f) := by
  intro i hi
  rw [map_differential, ExpectedRanks.map_rank, Matrix.minorIdeal_map,
    h i hi, Ideal.map_bot]

/-- The scheme-theoretic expected-rank bound gives the corresponding rank upper bound on
every residue-field matrix. -/
theorem rank_residueField_le_expectedRank
    {C : FiniteFreeComplex R} {N : ℕ} (r : C.ExpectedRanks N)
    (h : C.HasExpectedRankBounds r) (i : ℕ) (hi : i < N)
    (q : PrimeSpectrum R) :
    ((C.differential i).map
      (algebraMap R q.asIdeal.ResidueField)).rank ≤ r.rank i := by
  have hminor : Matrix.minorIdeal (C.differential i) (r.rank i + 1) ≤ q.asIdeal := by
    rw [h i hi]
    exact bot_le
  have hlt := (Matrix.minorIdeal_le_iff_rank_residueField_lt
    (C.differential i) (r.rank i + 1) q).mp hminor
  omega

/-- A sequence from the coefficient ring is regular on the localized relative fibre at
`q` after applying the canonical map to that local fibre ring. -/
def IsRelativeFibreRegularSequenceAt
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {d : ℕ} (q : PrimeSpectrum S) (f : Fin d → S) : Prop :=
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
  RingTheory.Sequence.IsRegular (Localization.AtPrime qf.asIdeal)
    (List.ofFn fun j ↦
      algebraMap S (Localization.AtPrime qf.asIdeal) (f j))

/-- The simultaneous expected-minor grade locus of a bounded matrix complex on relative
fibres.  At degree `i + 1`, it asks for grade at least `i + 1` of the ideal of
`rank i`-minors of `differential i`. -/
def relativeFibreBuchsbaumEisenbudLocus
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (C : FiniteFreeComplex S) {N : ℕ} (r : C.ExpectedRanks N) :
    Set (PrimeSpectrum S) :=
  ⋂ i ∈ Finset.range N,
    Matrix.determinantalGradeLocus (C.differential i) (r.rank i) (i + 1)
      (fun q f ↦ IsRelativeFibreRegularSequenceAt (R := R) q f)

@[simp]
theorem mem_relativeFibreBuchsbaumEisenbudLocus
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (C : FiniteFreeComplex S) {N : ℕ} (r : C.ExpectedRanks N)
    (q : PrimeSpectrum S) :
    q ∈ relativeFibreBuchsbaumEisenbudLocus (R := R) C r ↔
      ∀ i : ℕ, i < N →
        q ∈ Matrix.determinantalGradeLocus
          (C.differential i) (r.rank i) (i + 1)
          (fun q f ↦ IsRelativeFibreRegularSequenceAt (R := R) q f) := by
  simp [relativeFibreBuchsbaumEisenbudLocus]

/-- Fixed-sequence relative openness in every displayed degree makes the simultaneous
expected-minor grade locus open.  This is the finite-complex assembly of the 00RA input
used in the determinantal proof of 00RB. -/
theorem isOpen_relativeFibreBuchsbaumEisenbudLocus
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (C : FiniteFreeComplex S) {N : ℕ} (r : C.ExpectedRanks N)
    (hopen : ∀ (i : ℕ), i < N →
      ∀ (f : Fin (i + 1) → S),
        (∀ j, f j ∈ Matrix.minorIdeal (C.differential i) (r.rank i)) →
        IsOpen {q : PrimeSpectrum.zeroLocus (Set.range f) |
          IsRelativeFibreRegularSequenceAt (R := R) q.1 f}) :
    IsOpen (relativeFibreBuchsbaumEisenbudLocus (R := R) C r) := by
  apply isOpen_biInter_finset
  intro i hi
  apply Matrix.isOpen_determinantalGradeLocus_of_isOpen_subtype
  exact hopen i (Finset.mem_range.mp hi)

end FiniteFreeComplex

end Matrix

end
