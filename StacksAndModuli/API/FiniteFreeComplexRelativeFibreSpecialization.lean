module

public import StacksAndModuli.API.FiniteFreeComplexExactExpectedRanks
public import StacksAndModuli.API.IdealLocalizationSurjectiveRegularSequence
public import StacksAndModuli.API.LocalizedRelativeFibrePushout
public import StacksAndModuli.API.PolynomialModelBaseChange

/-!
# Finite free complexes on localized relative fibres

For a prime `q` of an `R`-algebra `S`, the relative-fibre exactness predicate is stated
using tensor-product scalar extension of the associated chain complex.  A local
Buchsbaum--Eisenbud criterion, on the other hand, is naturally stated for the matrices
obtained by mapping their coefficients to the local ring of the relative fibre.

This file identifies those two models.  It also identifies membership in the relative
Buchsbaum--Eisenbud grade locus with the corresponding local condition: each expected-minor
ideal is either the unit ideal or contains a regular sequence of the required length.
The reverse direction uses that the local fibre ring is a quotient of the localization of
`S` at the contracted prime, so regular-sequence witnesses can be lifted and their
denominators cleared.

No acyclicity criterion is asserted here.  Combining the two comparisons with the local
noetherian Buchsbaum--Eisenbud theorem gives the pointwise identification of the grade and
relative-fibre exactness loci.

Main declarations:

* `Matrix.FiniteFreeComplex.HasLocalizedRelativeFibreBuchsbaumEisenbudGradeAt`;
* `Matrix.FiniteFreeComplex.mem_relativeFibreBuchsbaumEisenbudLocus_iff_localized`;
* `Matrix.FiniteFreeComplex.isRelativeFibreExactInPositiveDegreesAt_iff_map`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory

universe u v

namespace PrimeSpectrum

/-- The local ring of a relative fibre is a quotient of the localization of the source at
the contraction of the fibre prime.  In particular, the resulting algebra map is
surjective. -/
theorem relativeFibreLocalization_algebraMap_surjective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    let p := q.comap (algebraMap R S)
    let qf := relativeFibrePrime (R := R) q
    letI : Algebra S (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.rightAlgebra
    let r := qf.asIdeal.comap
      Algebra.TensorProduct.includeRight.toRingHom
    let Sr := Localization.AtPrime r
    let A := Localization.AtPrime qf.asIdeal
    letI : qf.asIdeal.LiesOver r := ⟨rfl⟩
    letI : Algebra Sr A :=
      Localization.AtPrime.algebraOfLiesOver r qf.asIdeal
    Function.Surjective (algebraMap Sr A) := by
  let p := q.comap (algebraMap R S)
  let qf := relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  let r := qf.asIdeal.comap
    Algebra.TensorProduct.includeRight.toRingHom
  let Sr := Localization.AtPrime r
  let A := Localization.AtPrime qf.asIdeal
  haveI : qf.asIdeal.LiesOver r := ⟨rfl⟩
  letI : Algebra Sr A :=
    Localization.AtPrime.algebraOfLiesOver r qf.asIdeal
  let Ip := (p.asIdeal.map (algebraMap R S)).map (algebraMap S Sr)
  let e := Ideal.Fiber.localizationAlgEquivQuotientOverLocalizedSource
    p.asIdeal qf.asIdeal
  change A ≃ₐ[Sr] Sr ⧸ Ip at e
  change Function.Surjective (algebraMap Sr A)
  intro z
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e z)
  refine ⟨x, e.injective ?_⟩
  rw [e.commutes]
  exact hx

end PrimeSpectrum

namespace Ideal

/-- Extension to the local ring of the relative fibre is the unit ideal precisely when
the original ideal is not contained in the source prime. -/
theorem map_relativeFibreLocalization_eq_top_iff
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) (q : PrimeSpectrum S) :
    let p := q.comap (algebraMap R S)
    let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
    letI : Algebra S (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.rightAlgebra
    I.map (algebraMap S (Localization.AtPrime qf.asIdeal)) = ⊤ ↔
      ¬ I ≤ q.asIdeal := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  let r := qf.asIdeal.comap
    Algebra.TensorProduct.includeRight.toRingHom
  let Sr := Localization.AtPrime r
  let A := Localization.AtPrime qf.asIdeal
  haveI : qf.asIdeal.LiesOver r := ⟨rfl⟩
  letI : Algebra Sr A :=
    Localization.AtPrime.algebraOfLiesOver r qf.asIdeal
  have hr : r = q.asIdeal :=
    PrimeSpectrum.relativeFibrePrime_comap_includeRight (R := R) q
  have hmap : I.map (algebraMap S A) =
      (I.map (algebraMap S Sr)).map (algebraMap Sr A) := by
    rw [Ideal.map_map, IsScalarTower.algebraMap_eq S Sr A]
  constructor
  · intro htop hle
    have hIr : I ≤ r := by simpa only [hr] using hle
    have hloc : I.map (algebraMap S Sr) ≤
        IsLocalRing.maximalIdeal Sr := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.map_mono hIr
    have hlocal : I.map (algebraMap S A) ≤
        IsLocalRing.maximalIdeal A := by
      rw [hmap]
      exact (Ideal.map_mono hloc).trans
        (IsLocalRing.map_maximalIdeal_le (algebraMap Sr A))
    rw [htop] at hlocal
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_unique hlocal)
  · intro hnot
    have hIr : ¬ I ≤ r := by simpa only [hr] using hnot
    have hloc : I.map (algebraMap S Sr) = ⊤ :=
      (Ideal.map_atPrime_eq_top_iff_not_le I r).mpr hIr
    rw [hmap, hloc, Ideal.map_top]

/-- A regular sequence in the extension of an ideal to a localized relative fibre can be
replaced by the images of elements of the original ideal. -/
theorem exists_family_mem_and_isRegular_relativeFibreLocalization_iff
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) (d : ℕ) (q : PrimeSpectrum S) :
    let p := q.comap (algebraMap R S)
    let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
    letI : Algebra S (p.asIdeal.Fiber S) :=
      Algebra.TensorProduct.rightAlgebra
    let A := Localization.AtPrime qf.asIdeal
    (∃ f : Fin d → S, (∀ i, f i ∈ I) ∧
      RingTheory.Sequence.IsRegular A
        (List.ofFn fun i ↦ algebraMap S A (f i))) ↔
      ∃ g : Fin d → A, (∀ i, g i ∈ I.map (algebraMap S A)) ∧
        RingTheory.Sequence.IsRegular A (List.ofFn g) := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  let r := qf.asIdeal.comap
    Algebra.TensorProduct.includeRight.toRingHom
  let Sr := Localization.AtPrime r
  let A := Localization.AtPrime qf.asIdeal
  haveI : qf.asIdeal.LiesOver r := ⟨rfl⟩
  letI : Algebra Sr A :=
    Localization.AtPrime.algebraOfLiesOver r qf.asIdeal
  constructor
  · rintro ⟨f, hfI, hreg⟩
    refine ⟨fun i ↦ algebraMap S A (f i), ?_, hreg⟩
    intro i
    exact Ideal.mem_map_of_mem (algebraMap S A) (hfI i)
  · rintro ⟨g, hgI, hreg⟩
    exact Ideal.exists_family_mem_and_isRegular_map_of_isRegular_of_localization_surjective
      r.primeCompl
      (PrimeSpectrum.relativeFibreLocalization_algebraMap_surjective
        (R := R) q)
      I d g hgI hreg

end Ideal

namespace Matrix.FiniteFreeComplex

/-- Exactness through a fixed bound after mapping the differential matrices to the local
ring of a relative fibre. -/
def IsExactOnLocalizedRelativeFibreUpTo
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (C : FiniteFreeComplex S) (N : ℕ) (q : PrimeSpectrum S) : Prop :=
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  IsExactInPositiveDegreesUpTo
    (C.map (S := Localization.AtPrime qf.asIdeal)
      (algebraMap S (Localization.AtPrime qf.asIdeal))) N

/-- The local determinantal-grade condition for a finite free complex at a point of a
relative fibre.  Each expected-minor ideal in the local fibre ring is either the unit ideal
or contains a regular sequence whose length is the corresponding positive homological
degree. -/
def HasLocalizedRelativeFibreBuchsbaumEisenbudGradeAt
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (C : FiniteFreeComplex S) {N : ℕ} (r : C.ExpectedRanks N)
    (q : PrimeSpectrum S) : Prop :=
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  let A := Localization.AtPrime qf.asIdeal
  ∀ i : ℕ, i < N →
    let I := minorIdeal
      ((C.differential i).map (algebraMap S A)) (r.rank i)
    I = ⊤ ∨
      ∃ f : Fin (i + 1) → A, (∀ j, f j ∈ I) ∧
        RingTheory.Sequence.IsRegular A (List.ofFn f)

/-- Membership in the relative Buchsbaum--Eisenbud locus is exactly the local
determinantal-grade condition after mapping the differential matrices to the local ring of
the relative fibre. -/
theorem mem_relativeFibreBuchsbaumEisenbudLocus_iff_localized
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (C : FiniteFreeComplex S) {N : ℕ} (r : C.ExpectedRanks N)
    (q : PrimeSpectrum S) :
    q ∈ relativeFibreBuchsbaumEisenbudLocus (R := R) C r ↔
      C.HasLocalizedRelativeFibreBuchsbaumEisenbudGradeAt (R := R) r q := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  let A := Localization.AtPrime qf.asIdeal
  have hdegree (i : ℕ) :
      q ∈ Matrix.determinantalGradeLocus
          (C.differential i) (r.rank i) (i + 1)
          (fun q f ↦ IsRelativeFibreRegularSequenceAt (R := R) q f) ↔
        let I := minorIdeal
          ((C.differential i).map (algebraMap S A)) (r.rank i)
        I = ⊤ ∨
          ∃ f : Fin (i + 1) → A, (∀ j, f j ∈ I) ∧
            RingTheory.Sequence.IsRegular A (List.ofFn f) := by
    rw [Matrix.mem_determinantalGradeLocus]
    have hunit : minorIdeal
          ((C.differential i).map (algebraMap S A)) (r.rank i) = ⊤ ↔
        ¬ minorIdeal (C.differential i) (r.rank i) ≤ q.asIdeal := by
      rw [Matrix.minorIdeal_map]
      exact Ideal.map_relativeFibreLocalization_eq_top_iff
        (R := R) (minorIdeal (C.differential i) (r.rank i)) q
    have hwitness :
        (∃ f : Fin (i + 1) → S,
            (∀ j, f j ∈ minorIdeal (C.differential i) (r.rank i)) ∧
              IsRelativeFibreRegularSequenceAt (R := R) q f) ↔
          ∃ g : Fin (i + 1) → A,
            (∀ j, g j ∈ minorIdeal
              ((C.differential i).map (algebraMap S A)) (r.rank i)) ∧
              RingTheory.Sequence.IsRegular A (List.ofFn g) := by
      simpa only [IsRelativeFibreRegularSequenceAt, Matrix.minorIdeal_map] using
        (Ideal.exists_family_mem_and_isRegular_relativeFibreLocalization_iff
          (R := R) (minorIdeal (C.differential i) (r.rank i)) (i + 1) q)
    exact or_congr hunit.symm hwitness
  rw [mem_relativeFibreBuchsbaumEisenbudLocus]
  change (∀ i : ℕ, i < N →
      q ∈ Matrix.determinantalGradeLocus
        (C.differential i) (r.rank i) (i + 1)
        (fun q f ↦ IsRelativeFibreRegularSequenceAt (R := R) q f)) ↔ _
  constructor
  · intro h i hi
    exact (hdegree i).mp (h i hi)
  · intro h i hi
    exact (hdegree i).mpr (h i hi)

/-- Scalar extension of a matrix map to the local ring of a relative fibre is conjugate
to the linear map of the coefficientwise-extended matrix. -/
theorem isRelativeFibreExactAtDegree_succ_iff_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (C : FiniteFreeComplex S) (q : PrimeSpectrum S) (i : ℕ) :
    ChainComplex.IsRelativeFibreExactAtDegree
        (R := R) C.toChainComplex q (i + 1) ↔
      let p := q.comap (algebraMap R S)
      let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
      letI : Algebra S (p.asIdeal.Fiber S) :=
        Algebra.TensorProduct.rightAlgebra
      let A := Localization.AtPrime qf.asIdeal
      Function.Exact
        (Matrix.toLin' ((C.differential (i + 1)).map (algebraMap S A)))
        (Matrix.toLin' ((C.differential i).map (algebraMap S A))) := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  let A := Localization.AtPrime qf.asIdeal
  let e₀ := TensorProduct.piScalarRight S A A (Fin (C.termRank i))
  let e₁ := TensorProduct.piScalarRight S A A (Fin (C.termRank (i + 1)))
  let e₂ := TensorProduct.piScalarRight S A A (Fin (C.termRank (i + 2)))
  dsimp only [ChainComplex.IsRelativeFibreExactAtDegree]
  rw [show i + 1 - 1 = i by omega]
  simp only [toChainComplex_d]
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (f₁₂ := (Matrix.toLin' (C.differential (i + 1))).baseChange A)
    (f₂₃ := (Matrix.toLin' (C.differential i)).baseChange A)
    (g₁₂ := Matrix.toLin'
      ((C.differential (i + 1)).map (algebraMap S A)))
    (g₂₃ := Matrix.toLin'
      ((C.differential i).map (algebraMap S A)))
    (e₁ := e₂) (e₂ := e₁) (e₃ := e₀)
    (Matrix.piScalarRight_toLin_map (A := A) (C.differential (i + 1))).symm
    (Matrix.piScalarRight_toLin_map (A := A) (C.differential i)).symm).symm

/-- For a bounded finite free complex, exactness in positive degrees on the localized
relative fibre is exactly matrix exactness after mapping coefficients to that local fibre
ring. -/
theorem isRelativeFibreExactInPositiveDegreesAt_iff_map
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (C : FiniteFreeComplex S) (N : ℕ) (hbounded : C.IsBoundedAbove N)
    (q : PrimeSpectrum S) :
    ChainComplex.IsRelativeFibreExactInPositiveDegreesAt
        (R := R) C.toChainComplex q ↔
      C.IsExactOnLocalizedRelativeFibreUpTo (R := R) N q := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  change (∀ j : ℕ, 0 < j →
      ChainComplex.IsRelativeFibreExactAtDegree
        (R := R) C.toChainComplex q j) ↔
    IsExactInPositiveDegreesUpTo
      (C.map (S := Localization.AtPrime qf.asIdeal)
        (algebraMap S (Localization.AtPrime qf.asIdeal))) N
  constructor
  · intro h i hi
    exact (C.isRelativeFibreExactAtDegree_succ_iff_map
      (R := R) q i).mp (h (i + 1) (Nat.succ_pos i))
  · intro h j hj
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
    by_cases hi : i < N
    · exact (C.isRelativeFibreExactAtDegree_succ_iff_map
        (R := R) q i).mpr (h i hi)
    · apply ChainComplex.isRelativeFibreExactAtDegree_of_isZero
      have hzero : C.termRank (i + 1) = 0 :=
        hbounded (i + 1) (by omega)
      letI : Subsingleton (C.toChainComplex.X (i + 1)) := by
        change Subsingleton (Fin (C.termRank (i + 1)) → S)
        rw [hzero]
        infer_instance
      exact ModuleCat.isZero_of_subsingleton _

/-- Once a local Buchsbaum--Eisenbud acyclicity criterion is available, the two
specialization comparisons identify relative-fibre exactness with membership in the
determinantal-grade locus at the given point. -/
theorem isRelativeFibreExactInPositiveDegreesAt_iff_mem_buchsbaumEisenbudLocus_of_local
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (C : FiniteFreeComplex S) (N : ℕ) (hbounded : C.IsBoundedAbove N)
    (r : C.ExpectedRanks N) (q : PrimeSpectrum S)
    (hlocal : C.IsExactOnLocalizedRelativeFibreUpTo (R := R) N q ↔
      C.HasLocalizedRelativeFibreBuchsbaumEisenbudGradeAt (R := R) r q) :
    ChainComplex.IsRelativeFibreExactInPositiveDegreesAt
        (R := R) C.toChainComplex q ↔
      q ∈ relativeFibreBuchsbaumEisenbudLocus (R := R) C r :=
  (C.isRelativeFibreExactInPositiveDegreesAt_iff_map
    (R := R) N hbounded q).trans
      (hlocal.trans
        (C.mem_relativeFibreBuchsbaumEisenbudLocus_iff_localized
          (R := R) r q).symm)

end Matrix.FiniteFreeComplex

end
