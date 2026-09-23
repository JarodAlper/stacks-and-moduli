module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import StacksAndModuli.API.NoetherianExactnessLocus

/-!
# Interface for relative fibre exactness loci

For a prime `q` of an `R`-algebra `S`, let `p` be its contraction to `R`.  The prime `q`
induces a prime of the fibre ring `κ(p) ⊗[R] S`.  This file defines exactness of a pair of
maps, and exactness in positive degrees of a chain complex, after base change to the
localization of that fibre ring at the induced prime.

For a bounded complex of finite free `S`-modules, openness of the resulting positive-degree
exactness locus is precisely the conclusion used from Stacks Project tag 00RB.  The predicate
`ChainComplex.HasOpenRelativeFibreExactInPositiveDegreesLocus` isolates that conclusion
without asserting it.  Its equivalent basic-neighbourhood formulation is proved here.

The ordinary exactness-spreading step is supplied by
`LinearMap.isOpen_exactLocalizationLocus`.  What remains for 00RB is genuinely relative:
the contracted prime and hence the residue field vary.  The Stacks proof uses determinantal
rank ideals, a Buchsbaum–Eisenbud exactness criterion, and openness of regular sequences in
equidimensional Cohen–Macaulay fibres.  Mathlib currently has matrices, determinants, and
regular sequences, but not that criterion or a Cohen–Macaulay fibre API.

Main declarations:

* `PrimeSpectrum.relativeFibrePrime`;
* `LinearMap.relativeFibreExactLocus`;
* `ChainComplex.relativeFibreExactInPositiveDegreesLocus`;
* `ChainComplex.HasOpenRelativeFibreExactInPositiveDegreesLocus`;
* `ChainComplex.hasOpenRelativeFibreExactInPositiveDegreesLocus_iff_basicNeighborhoods`;
* `ChainComplex.hasOpenRelativeFibreExactInPositiveDegreesLocus_of_bounded_of_pairwise`.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

universe u v w

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- The prime of the fibre ring `κ(q ∩ R) ⊗[R] S` induced by a prime `q` of `S`. -/
def relativeFibrePrime (q : PrimeSpectrum S) :
    PrimeSpectrum ((q.comap (algebraMap R S)).asIdeal.Fiber S) :=
  PrimeSpectrum.preimageEquivFiber R S
    (q.comap (algebraMap R S)) ⟨q, rfl⟩

/-- The induced fibre prime contracts back to the original prime along the right tensor
factor. -/
theorem relativeFibrePrime_comap_includeRight (q : PrimeSpectrum S) :
    (relativeFibrePrime (R := R) q).asIdeal.comap
      Algebra.TensorProduct.includeRight.toRingHom = q.asIdeal := by
  let p := q.comap (algebraMap R S)
  let E := PrimeSpectrum.preimageEquivFiber R S p
  have h := E.left_inv ⟨q, rfl⟩
  exact congrArg (fun x ↦ x.1.asIdeal) h

end PrimeSpectrum

namespace LinearMap

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M N P : Type w}
variable [AddCommGroup M] [Module S M]
variable [AddCommGroup N] [Module S N]
variable [AddCommGroup P] [Module S P]

/-- Two consecutive `S`-linear maps are exact on the localized fibre at `q`.  The local
`S`-algebra structure on the fibre ring is the right tensor-factor structure. -/
def IsRelativeFibreExactAt
    (f : M →ₗ[S] N) (g : N →ₗ[S] P) (q : PrimeSpectrum S) : Prop :=
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
  Function.Exact
    (f.baseChange (Localization.AtPrime qf.asIdeal))
    (g.baseChange (Localization.AtPrime qf.asIdeal))

/-- The locus where two consecutive maps are exact on the localized relative fibre. -/
def relativeFibreExactLocus
    (f : M →ₗ[S] N) (g : N →ₗ[S] P) :
    Set (PrimeSpectrum S) :=
  {q | IsRelativeFibreExactAt (R := R) f g q}

@[simp]
theorem mem_relativeFibreExactLocus
    (f : M →ₗ[S] N) (g : N →ₗ[S] P) (q : PrimeSpectrum S) :
    q ∈ relativeFibreExactLocus (R := R) f g ↔
      IsRelativeFibreExactAt (R := R) f g q :=
  Iff.rfl

/-- Openness of the relative fibre-exactness locus for two consecutive maps.  This is an
interface predicate and makes no existence claim. -/
def HasOpenRelativeFibreExactLocus
    (f : M →ₗ[S] N) (g : N →ₗ[S] P) : Prop :=
  IsOpen (relativeFibreExactLocus (R := R) f g)

end LinearMap

namespace ChainComplex

open CategoryTheory

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Exactness at one positive-degree spot of a chain complex after localization on the
relative fibre at `q`.  This is the individual condition whose finite intersection gives
the locus for a bounded complex. -/
def IsRelativeFibreExactAtDegree
    (C : ChainComplex (ModuleCat.{w} S) ℕ)
    (q : PrimeSpectrum S) (i : ℕ) : Prop :=
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
  Function.Exact
    ((C.d (i + 1) i).hom.baseChange
      (Localization.AtPrime qf.asIdeal))
    ((C.d i (i - 1)).hom.baseChange
      (Localization.AtPrime qf.asIdeal))

/-- The locus where a chain complex is exact in one specified degree on the localized
relative fibre. -/
def relativeFibreExactAtDegreeLocus
    (C : ChainComplex (ModuleCat.{w} S) ℕ) (i : ℕ) :
    Set (PrimeSpectrum S) :=
  {q | IsRelativeFibreExactAtDegree (R := R) C q i}

@[simp]
theorem mem_relativeFibreExactAtDegreeLocus
    (C : ChainComplex (ModuleCat.{w} S) ℕ)
    (q : PrimeSpectrum S) (i : ℕ) :
    q ∈ relativeFibreExactAtDegreeLocus (R := R) C i ↔
      IsRelativeFibreExactAtDegree (R := R) C q i :=
  Iff.rfl

/-- The degreewise locus of a complex is the relative fibre-exactness locus of its two
adjacent differentials. -/
theorem relativeFibreExactAtDegreeLocus_eq
    (C : ChainComplex (ModuleCat.{w} S) ℕ) (i : ℕ) :
    relativeFibreExactAtDegreeLocus (R := R) C i =
      LinearMap.relativeFibreExactLocus (R := R)
        (C.d (i + 1) i).hom (C.d i (i - 1)).hom :=
  rfl

/-- A zero middle term is automatically exact at that degree after every localized
relative-fibre base change. -/
theorem isRelativeFibreExactAtDegree_of_isZero
    (C : ChainComplex (ModuleCat.{w} S) ℕ)
    (q : PrimeSpectrum S) (i : ℕ)
    (hzero : CategoryTheory.Limits.IsZero (C.X i)) :
    IsRelativeFibreExactAtDegree (R := R) C q i := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) := Algebra.TensorProduct.rightAlgebra
  letI : Subsingleton (C.X i) := ModuleCat.subsingleton_of_isZero hzero
  change Function.Exact
    ((C.d (i + 1) i).hom.baseChange
      (Localization.AtPrime qf.asIdeal))
    ((C.d i (i - 1)).hom.baseChange
      (Localization.AtPrime qf.asIdeal))
  intro y
  constructor
  · intro _hy
    exact ⟨0, Subsingleton.elim _ _⟩
  · intro _hy
    rw [Subsingleton.elim y 0, map_zero]

/-- A chain complex is exact in every positive degree on the localized relative fibre at
`q`.  Degree zero is deliberately excluded: in the truncated resolution used for 00RB its
homology is the module being resolved. -/
def IsRelativeFibreExactInPositiveDegreesAt
    (C : ChainComplex (ModuleCat.{w} S) ℕ)
    (q : PrimeSpectrum S) : Prop :=
  ∀ i : ℕ, 0 < i → IsRelativeFibreExactAtDegree (R := R) C q i

/-- The locus where a chain complex is exact in every positive degree on the localized
relative fibre. -/
def relativeFibreExactInPositiveDegreesLocus
    (C : ChainComplex (ModuleCat.{w} S) ℕ) :
    Set (PrimeSpectrum S) :=
  {q | IsRelativeFibreExactInPositiveDegreesAt (R := R) C q}

@[simp]
theorem mem_relativeFibreExactInPositiveDegreesLocus
    (C : ChainComplex (ModuleCat.{w} S) ℕ)
    (q : PrimeSpectrum S) :
    q ∈ relativeFibreExactInPositiveDegreesLocus (R := R) C ↔
      IsRelativeFibreExactInPositiveDegreesAt (R := R) C q :=
  Iff.rfl

/-- Openness of the positive-degree relative fibre-exactness locus.  For a bounded finite
free complex under the hypotheses of 00RB, that lemma supplies this property. -/
def HasOpenRelativeFibreExactInPositiveDegreesLocus
    (C : ChainComplex (ModuleCat.{w} S) ℕ) : Prop :=
  IsOpen (relativeFibreExactInPositiveDegreesLocus (R := R) C)

/-- Basic-open-neighbourhood form of relative fibre-exactness spreading. -/
def HasRelativeFibreExactBasicNeighborhoods
    (C : ChainComplex (ModuleCat.{w} S) ℕ) : Prop :=
  ∀ q : PrimeSpectrum S,
    IsRelativeFibreExactInPositiveDegreesAt (R := R) C q →
      ∃ a ∉ q.asIdeal, ∀ q' : PrimeSpectrum S, a ∉ q'.asIdeal →
        IsRelativeFibreExactInPositiveDegreesAt (R := R) C q'

/-- Openness of the relative fibre-exactness locus supplies a basic exactness neighbourhood
at each point of the locus. -/
theorem HasOpenRelativeFibreExactInPositiveDegreesLocus.basicNeighborhoods
    (C : ChainComplex (ModuleCat.{w} S) ℕ)
    (h : HasOpenRelativeFibreExactInPositiveDegreesLocus (R := R) C) :
    HasRelativeFibreExactBasicNeighborhoods (R := R) C := by
  intro q hq
  obtain ⟨V, hVsub, hVopen, hqV⟩ :=
    (isOpen_iff_forall_mem_open.mp h) q hq
  obtain ⟨W, ⟨a, rfl⟩, hqW, hWsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqV hVopen
  exact ⟨a, hqW, fun q' hq' ↦ hVsub (hWsub hq')⟩

/-- Openness of the positive-degree relative fibre-exactness locus is equivalent to the
basic-neighbourhood formulation used in spreading arguments. -/
theorem hasOpenRelativeFibreExactInPositiveDegreesLocus_iff_basicNeighborhoods
    (C : ChainComplex (ModuleCat.{w} S) ℕ) :
    HasOpenRelativeFibreExactInPositiveDegreesLocus (R := R) C ↔
      HasRelativeFibreExactBasicNeighborhoods (R := R) C := by
  constructor
  · exact HasOpenRelativeFibreExactInPositiveDegreesLocus.basicNeighborhoods C
  · intro h
    change IsOpen (relativeFibreExactInPositiveDegreesLocus (R := R) C)
    rw [isOpen_iff_forall_mem_open]
    intro q hq
    obtain ⟨a, ha, hbasic⟩ := h q hq
    refine ⟨PrimeSpectrum.basicOpen a, ?_, (PrimeSpectrum.basicOpen a).2, ha⟩
    exact fun q' hq' ↦ hbasic q' hq'

/-- For an eventually automatically exact complex, openness of the finitely many remaining
degreewise loci gives openness of the full positive-degree relative fibre-exactness locus.

This is the finite-intersection bookkeeping needed to apply the bounded-complex theorem
00RB: the theorem itself only has to provide openness one displayed degree at a time. -/
theorem hasOpenRelativeFibreExactInPositiveDegreesLocus_of_eventually
    (C : ChainComplex (ModuleCat.{w} S) ℕ) (N : ℕ)
    (hopen : ∀ i, 0 < i → i ≤ N →
      IsOpen (relativeFibreExactAtDegreeLocus (R := R) C i))
    (heventual : ∀ (q : PrimeSpectrum S) (i : ℕ), N < i →
      IsRelativeFibreExactAtDegree (R := R) C q i) :
    HasOpenRelativeFibreExactInPositiveDegreesLocus (R := R) C := by
  let U : Set (PrimeSpectrum S) :=
    ⋂ i ∈ Finset.Icc 1 N,
      relativeFibreExactAtDegreeLocus (R := R) C i
  have hU : IsOpen U := by
    apply isOpen_biInter_finset
    intro i hi
    exact hopen i (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hi).2
  change IsOpen (relativeFibreExactInPositiveDegreesLocus (R := R) C)
  rw [show relativeFibreExactInPositiveDegreesLocus (R := R) C = U by
    ext q
    constructor
    · intro h
      simp only [U, Set.mem_iInter]
      intro i hi
      exact h i (Finset.mem_Icc.mp hi).1
    · intro h i hi
      by_cases hiN : i ≤ N
      · have hiIcc : i ∈ Finset.Icc 1 N :=
          Finset.mem_Icc.mpr ⟨hi, hiN⟩
        have h' : ∀ j ∈ Finset.Icc 1 N,
            q ∈ relativeFibreExactAtDegreeLocus (R := R) C j := by
          simpa only [U, Set.mem_iInter] using h
        exact h' i hiIcc
      · exact heventual q i (Nat.lt_of_not_ge hiN)]
  exact hU

/-- For a complex which is zero above `N`, openness of its positive-degree relative
fibre-exactness locus is reduced to openness in the finitely many degrees `1, …, N`. -/
theorem hasOpenRelativeFibreExactInPositiveDegreesLocus_of_bounded
    (C : ChainComplex (ModuleCat.{w} S) ℕ) (N : ℕ)
    (hopen : ∀ i, 0 < i → i ≤ N →
      IsOpen (relativeFibreExactAtDegreeLocus (R := R) C i))
    (hzero : ∀ i, N < i → CategoryTheory.Limits.IsZero (C.X i)) :
    HasOpenRelativeFibreExactInPositiveDegreesLocus (R := R) C := by
  apply hasOpenRelativeFibreExactInPositiveDegreesLocus_of_eventually C N hopen
  intro q i hi
  exact isRelativeFibreExactAtDegree_of_isZero C q i (hzero i hi)

/-- Pairwise relative fibre-exactness openness for the displayed differentials of a
bounded complex supplies openness of the full exactness locus. -/
theorem hasOpenRelativeFibreExactInPositiveDegreesLocus_of_bounded_of_pairwise
    (C : ChainComplex (ModuleCat.{w} S) ℕ) (N : ℕ)
    (hopen : ∀ i, 0 < i → i ≤ N →
      LinearMap.HasOpenRelativeFibreExactLocus (R := R)
        (C.d (i + 1) i).hom (C.d i (i - 1)).hom)
    (hzero : ∀ i, N < i → CategoryTheory.Limits.IsZero (C.X i)) :
    HasOpenRelativeFibreExactInPositiveDegreesLocus (R := R) C := by
  apply hasOpenRelativeFibreExactInPositiveDegreesLocus_of_bounded C N
  · intro i hi hiN
    rw [relativeFibreExactAtDegreeLocus_eq]
    exact hopen i hi hiN
  · exact hzero

end ChainComplex

end
