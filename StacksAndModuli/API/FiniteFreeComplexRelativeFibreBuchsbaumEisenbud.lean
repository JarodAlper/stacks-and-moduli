module

public import StacksAndModuli.API.FiniteFreeComplexBuchsbaumEisenbud
public import StacksAndModuli.API.FiniteFreeComplexBuchsbaumEisenbudConverse
public import StacksAndModuli.API.FiniteFreeComplexExactExpectedRankBounds
public import StacksAndModuli.API.FiniteFreeComplexRelativeFibreSpecialization
public import StacksAndModuli.API.RelativeFibreFlatCokernel

/-!
# Relative-fibre exactness via the Buchsbaum--Eisenbud criterion

This file combines the local Buchsbaum--Eisenbud criterion with the specialization and
ordinary-localization interfaces for bounded finite free complexes.

Without a global expected-rank-bound hypothesis, the relative-fibre exactness locus is not
identified with the determinantal-grade locus alone.  The faithful pointwise statement is
that relative-fibre exactness is equivalent to ordinary exactness after localization at the
source prime together with membership in the relative Buchsbaum--Eisenbud grade locus.  In
the reverse direction, ordinary localized exactness supplies the expected-rank bounds over
the source local ring; these bounds are then mapped to the local ring of the relative fibre
before applying the local acyclicity criterion.

The resulting set equality expresses the relative-fibre exactness locus as the intersection
of a finite ordinary localization-exactness locus and the relative determinantal-grade
locus.  Consequently, the fixed-sequence openness input isolated by the determinantal-grade
API gives the bounded-complex openness conclusion used in the determinantal proof of Stacks
Project tag 00RB.

Main declarations:

* `Matrix.FiniteFreeComplex.
    isRelativeFibreExactInPositiveDegreesAt_iff_exactLocalization_and_buchsbaumEisenbudGrade`;
* `Matrix.FiniteFreeComplex.exactLocalizationInPositiveDegreesUpToLocus`;
* `Matrix.FiniteFreeComplex.
    relativeFibreExactInPositiveDegreesLocus_eq_exactLocalization_inter_buchsbaumEisenbudGrade`;
* `Matrix.FiniteFreeComplex.
    hasOpenRelativeFibreExactInPositiveDegreesLocus_of_buchsbaumEisenbudGrade`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

namespace Matrix.FiniteFreeComplex

/-- Relative-fibre exactness of a bounded finite free complex at a point is equivalent to
ordinary localized exactness of every displayed pair together with the relative
Buchsbaum--Eisenbud grade condition at that point. -/
theorem
    isRelativeFibreExactInPositiveDegreesAt_iff_exactLocalization_and_buchsbaumEisenbudGrade
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] [Module.Flat R S]
    (C : FiniteFreeComplex S) (N : ℕ) (hbounded : C.IsBoundedAbove N)
    (r : C.ExpectedRanks N) (q : PrimeSpectrum S) :
    ChainComplex.IsRelativeFibreExactInPositiveDegreesAt
        (R := R) C.toChainComplex q ↔
      ((∀ i : ℕ, i < N →
          q ∈ LinearMap.exactLocalizationLocus
            (Matrix.toLin' (C.differential (i + 1)))
            (Matrix.toLin' (C.differential i))) ∧
        q ∈ C.relativeFibreBuchsbaumEisenbudLocus (R := R) r) := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  let Sq := Localization.AtPrime q.asIdeal
  let commRingSq : CommRing Sq := inferInstance
  letI : CommRing Sq := commRingSq
  letI : CommSemiring Sq := commRingSq.toCommSemiring
  letI : Semiring Sq := commRingSq.toCommSemiring.toSemiring
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  let A := Localization.AtPrime qf.asIdeal
  let commRingA : CommRing A := inferInstance
  letI : CommRing A := commRingA
  letI : CommSemiring A := commRingA.toCommSemiring
  letI : Semiring A := commRingA.toCommSemiring.toSemiring
  letI : IsNoetherianRing (p.asIdeal.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing
      p.asIdeal.ResidueField (p.asIdeal.Fiber S)
  letI : IsNoetherianRing A := inferInstance
  have hqf : qf.asIdeal.LiesOver q.asIdeal := ⟨by
    rw [Ideal.under_def, Algebra.TensorProduct.algebraMap_eq_includeRight]
    exact (PrimeSpectrum.relativeFibrePrime_comap_includeRight
      (R := R) q).symm⟩
  letI : qf.asIdeal.LiesOver q.asIdeal := hqf
  letI : Algebra Sq A :=
    Localization.AtPrime.algebraOfLiesOver q.asIdeal qf.asIdeal
  constructor
  · intro hfibre
    have hlocal : C.IsExactOnLocalizedRelativeFibreUpTo (R := R) N q :=
      (C.isRelativeFibreExactInPositiveDegreesAt_iff_map
        (R := R) N hbounded q).mp hfibre
    constructor
    · intro i hi
      rw [LinearMap.mem_exactLocalizationLocus]
      have hfibreDegree := hfibre (i + 1) (Nat.succ_pos i)
      dsimp only [ChainComplex.IsRelativeFibreExactAtDegree] at hfibreDegree
      rw [show i + 1 - 1 = i by omega] at hfibreDegree
      letI : Module.Finite S (C.toChainComplex.X (i + 1)) := by
        change Module.Finite S (Fin (C.termRank (i + 1)) → S)
        infer_instance
      letI : Module.Finite S (C.toChainComplex.X i) := by
        change Module.Finite S (Fin (C.termRank i) → S)
        infer_instance
      letI : Module.Projective S (C.toChainComplex.X i) := by
        change Module.Projective S (Fin (C.termRank i) → S)
        infer_instance
      have hbase :=
        LinearMap.exact_baseChange_at_sourcePrime_of_isRelativeFibreExactAt
          (R := R) q
          (C.toChainComplex.d ((i + 1) + 1) (i + 1)).hom
          (C.toChainComplex.d (i + 1) i).hom
          (congrArg ModuleCat.Hom.hom
            (C.toChainComplex.d_comp_d ((i + 1) + 1) (i + 1) i))
          hfibreDegree
      have hlocalized :=
        (LinearMap.exact_localizedMap_iff_baseChange
          q.asIdeal.primeCompl
          (C.toChainComplex.d ((i + 1) + 1) (i + 1)).hom
          (C.toChainComplex.d (i + 1) i).hom).mpr hbase
      rw [← C.toChainComplex_d (i + 1), ← C.toChainComplex_d i]
      exact hlocalized
    · rw [C.mem_relativeFibreBuchsbaumEisenbudLocus_iff_localized
          (R := R) r q]
      have hlocalA :
          (C.map (algebraMap S A)).IsExactInPositiveDegreesUpTo N := by
        simpa only [IsExactOnLocalizedRelativeFibreUpTo] using hlocal
      have hgradeA := buchsbaumEisenbudGrade_of_isExactInPositiveDegreesUpTo
        (C.map (algebraMap S A)) (r.map (algebraMap S A))
          (hbounded.map (algebraMap S A)) hlocalA
      simpa only [HasLocalizedRelativeFibreBuchsbaumEisenbudGradeAt,
        HasBuchsbaumEisenbudGrade, map_differential,
        ExpectedRanks.map_rank] using hgradeA
  · rintro ⟨hordinary, hgradeLocus⟩
    apply (C.isRelativeFibreExactInPositiveDegreesAt_iff_map
      (R := R) N hbounded q).mpr
    have hSq : (C.map (algebraMap S Sq)).IsExactInPositiveDegreesUpTo N := by
      intro i hi
      exact (C.exact_localizedMap_iff_map_atPrime i q).mp (hordinary i hi)
    have hboundsSq :
        (C.map (algebraMap S Sq)).HasExpectedRankBounds
          (r.map (algebraMap S Sq)) :=
      (C.map (algebraMap S Sq)).hasExpectedRankBounds_of_isExactInPositiveDegreesUpTo
        N (r.map (algebraMap S Sq))
        (hbounded.map (algebraMap S Sq)) hSq
    have hboundsA' := HasExpectedRankBounds.map
      (r.map (algebraMap S Sq)) hboundsSq (algebraMap Sq A)
    have hboundsA :
        (C.map (algebraMap S A)).HasExpectedRankBounds
          (r.map (algebraMap S A)) := by
      intro i hi
      simpa only [map_differential, ExpectedRanks.map_rank,
        Matrix.minorIdeal_map, Ideal.map_map,
        IsScalarTower.algebraMap_eq S Sq A, Ideal.map_bot] using
          hboundsA' i hi
    have hgrade :
        (C.map (algebraMap S A)).HasBuchsbaumEisenbudGrade
          (r.map (algebraMap S A)) := by
      have hgradeLocal :=
        (C.mem_relativeFibreBuchsbaumEisenbudLocus_iff_localized
          (R := R) r q).mp hgradeLocus
      simpa only [HasLocalizedRelativeFibreBuchsbaumEisenbudGradeAt,
        HasBuchsbaumEisenbudGrade, map_differential,
        ExpectedRanks.map_rank] using hgradeLocal
    exact isExactInPositiveDegreesUpTo_of_buchsbaumEisenbudGrade
      (C.map (algebraMap S A)) N (r.map (algebraMap S A))
        (hbounded.map (algebraMap S A)) hboundsA hgrade

/-- The locus where every displayed pair of differentials of a finite free complex is
exact after ordinary localization at the source prime. -/
def exactLocalizationInPositiveDegreesUpToLocus
    {S : Type u} [CommRing S] (C : FiniteFreeComplex S) (N : ℕ) :
    Set (PrimeSpectrum S) :=
  ⋂ i ∈ Finset.range N,
    LinearMap.exactLocalizationLocus
      (Matrix.toLin' (C.differential (i + 1)))
      (Matrix.toLin' (C.differential i))

@[simp]
theorem mem_exactLocalizationInPositiveDegreesUpToLocus
    {S : Type u} [CommRing S] (C : FiniteFreeComplex S) (N : ℕ)
    (q : PrimeSpectrum S) :
    q ∈ C.exactLocalizationInPositiveDegreesUpToLocus N ↔
      ∀ i : ℕ, i < N →
        q ∈ LinearMap.exactLocalizationLocus
          (Matrix.toLin' (C.differential (i + 1)))
          (Matrix.toLin' (C.differential i)) := by
  simp only [exactLocalizationInPositiveDegreesUpToLocus,
    Set.mem_iInter, Finset.mem_range]

/-- The relative-fibre exactness locus of a bounded finite free complex is the intersection
of its ordinary localization-exactness locus with its relative
Buchsbaum--Eisenbud grade locus. -/
theorem
    relativeFibreExactInPositiveDegreesLocus_eq_exactLocalization_inter_buchsbaumEisenbudGrade
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] [Module.Flat R S]
    (C : FiniteFreeComplex S) (N : ℕ) (hbounded : C.IsBoundedAbove N)
    (r : C.ExpectedRanks N) :
    ChainComplex.relativeFibreExactInPositiveDegreesLocus
        (R := R) C.toChainComplex =
      C.exactLocalizationInPositiveDegreesUpToLocus N ∩
        C.relativeFibreBuchsbaumEisenbudLocus (R := R) r := by
  ext q
  rw [ChainComplex.mem_relativeFibreExactInPositiveDegreesLocus,
    C.isRelativeFibreExactInPositiveDegreesAt_iff_exactLocalization_and_buchsbaumEisenbudGrade
      N hbounded r q]
  simp only [mem_exactLocalizationInPositiveDegreesUpToLocus,
    Set.mem_inter_iff]

/-- The finite ordinary localization-exactness locus of a bounded display is open over a
Noetherian coefficient ring. -/
theorem isOpen_exactLocalizationInPositiveDegreesUpToLocus
    {S : Type u} [CommRing S] [IsNoetherianRing S]
    (C : FiniteFreeComplex S) (N : ℕ) :
    IsOpen (C.exactLocalizationInPositiveDegreesUpToLocus N) := by
  apply isOpen_biInter_finset
  intro i hi
  apply LinearMap.isOpen_exactLocalizationLocus
  change (Matrix.toLin' (C.differential i)).comp
      (Matrix.toLin' (C.differential (i + 1))) = 0
  rw [← Matrix.toLin'_mul, C.differential_sq]
  simp

/-- Fixed-sequence openness for the expected-minor grade conditions implies openness of the
positive-degree relative-fibre exactness locus of a bounded finite free complex.  This is
the finite-complex determinantal 00RB conclusion conditional on its 00RA input. -/
theorem hasOpenRelativeFibreExactInPositiveDegreesLocus_of_buchsbaumEisenbudGrade
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] [Module.Flat R S]
    (C : FiniteFreeComplex S) (N : ℕ) (hbounded : C.IsBoundedAbove N)
    (r : C.ExpectedRanks N)
    (hopen : ∀ (i : ℕ), i < N →
      ∀ (f : Fin (i + 1) → S),
        (∀ j, f j ∈ Matrix.minorIdeal (C.differential i) (r.rank i)) →
        IsOpen {q : PrimeSpectrum.zeroLocus (Set.range f) |
          IsRelativeFibreRegularSequenceAt (R := R) q.1 f}) :
    ChainComplex.HasOpenRelativeFibreExactInPositiveDegreesLocus
      (R := R) C.toChainComplex := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  change IsOpen (ChainComplex.relativeFibreExactInPositiveDegreesLocus
    (R := R) C.toChainComplex)
  rw [C.relativeFibreExactInPositiveDegreesLocus_eq_exactLocalization_inter_buchsbaumEisenbudGrade
    N hbounded r]
  exact (C.isOpen_exactLocalizationInPositiveDegreesUpToLocus N).inter
    (C.isOpen_relativeFibreBuchsbaumEisenbudLocus r hopen)

end Matrix.FiniteFreeComplex

end
