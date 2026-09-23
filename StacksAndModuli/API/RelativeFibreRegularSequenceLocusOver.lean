module

public import StacksAndModuli.API.FiniteFreeComplexDeterminantalGrade
public import StacksAndModuli.API.RelativeFibreRegularSequenceLocus

/-!
# Relative regular sequences on a fixed fibre

This file identifies the regular-sequence predicate used by the relative
Buchsbaum--Eisenbud locus with ordinary local regularity on the appropriate fibre ring.
Consequently, for a finite-type ring map, the locus for each fixed coefficient sequence is
open on its zero locus inside every fixed set-theoretic fibre.

This is the exact fixed-fibre input to the determinantal grade-locus patching argument.  It
does not produce an ambient open neighbourhood meeting fibres over nearby base primes; that
is the remaining equidimensional Cohen--Macaulay variation in Stacks Project tag 00RA.

Main declarations:

* `Matrix.FiniteFreeComplex.isRelativeFibreRegularSequenceAt_iff_isRegularAfterLocalizationAt`;
* `Matrix.FiniteFreeComplex.relativeFibreRegularSequenceLocusOver`;
* `Matrix.FiniteFreeComplex.isOpen_relativeFibreRegularSequenceLocusOver`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

open scoped Pointwise TensorProduct

universe u v

namespace Matrix.FiniteFreeComplex

/-- The relative regular-sequence predicate is ordinary local regularity after mapping the
sequence to the fibre ring over the contracted prime. -/
theorem isRelativeFibreRegularSequenceAt_iff_isRegularAfterLocalizationAt
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {d : ℕ} (q : PrimeSpectrum S) (f : Fin d → S) :
    IsRelativeFibreRegularSequenceAt (R := R) q f ↔
      let p := q.comap (algebraMap R S)
      let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
      letI : Algebra S (p.asIdeal.Fiber S) :=
        Algebra.TensorProduct.rightAlgebra
      RingTheory.Sequence.IsRegularAfterLocalizationAt
        (List.ofFn fun j ↦
          Algebra.TensorProduct.includeRight (f j)) qf := by
  let p := q.comap (algebraMap R S)
  let qf := PrimeSpectrum.relativeFibrePrime (R := R) q
  letI : Algebra S (p.asIdeal.Fiber S) :=
    Algebra.TensorProduct.rightAlgebra
  let T := p.asIdeal.Fiber S
  let A := Localization.AtPrime qf.asIdeal
  change RingTheory.Sequence.IsRegular A
      (List.ofFn fun j ↦ algebraMap S A (f j)) ↔
    RingTheory.Sequence.IsRegular A
      (List.map (algebraMap T A)
        (List.ofFn fun j ↦ Algebra.TensorProduct.includeRight (f j)))
  have hfun : (fun j ↦ algebraMap S A (f j)) =
      (algebraMap T A) ∘
        (fun j ↦ Algebra.TensorProduct.includeRight (f j)) := by
    funext j
    exact (IsScalarTower.algebraMap_apply S T A (f j)).symm
  rw [List.map_ofFn, ← hfun]

/-- The locus on the zero set of `f` in the fixed fibre over `p` where the relative
regular-sequence predicate holds. -/
def relativeFibreRegularSequenceLocusOver
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {d : ℕ} (p : PrimeSpectrum R) (f : Fin d → S) :
    Set (Ideal.Fiber.fixedFibreZeroLocus p (List.ofFn f)) :=
  {q | IsRelativeFibreRegularSequenceAt (R := R) q.1.1 f}

/-- Under the fixed-fibre homeomorphism, the relative predicate locus is exactly the
ordinary local regular-sequence locus in the fibre ring. -/
theorem relativeFibreRegularSequenceLocusOver_eq_fixedFibreRegularSequenceLocus
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    {d : ℕ} (p : PrimeSpectrum R) (f : Fin d → S) :
    relativeFibreRegularSequenceLocusOver (R := R) p f =
      Ideal.Fiber.fixedFibreRegularSequenceLocus p (List.ofFn f) := by
  ext q
  rcases q with ⟨⟨qS, hp⟩, hzero⟩
  subst p
  rw [Ideal.Fiber.mem_fixedFibreRegularSequenceLocus]
  change IsRelativeFibreRegularSequenceAt (R := R) qS f ↔ _
  rw [isRelativeFibreRegularSequenceAt_iff_isRegularAfterLocalizationAt]
  have hprime :
      ((Ideal.Fiber.fixedFibreZeroLocusHomeomorph
        (qS.comap (algebraMap R S)) (List.ofFn f))
          ⟨⟨qS, rfl⟩, hzero⟩).1 =
        PrimeSpectrum.relativeFibrePrime (R := R) qS := rfl
  change RingTheory.Sequence.IsRegularAfterLocalizationAt
      (List.ofFn fun j ↦ Algebra.TensorProduct.includeRight (f j))
      (PrimeSpectrum.relativeFibrePrime (R := R) qS) ↔
    RingTheory.Sequence.IsRegularAfterLocalizationAt
      (List.map Algebra.TensorProduct.includeRight (List.ofFn f)) _
  rw [hprime]
  rw [List.map_ofFn]
  change RingTheory.Sequence.IsRegularAfterLocalizationAt
      (List.ofFn fun j ↦ Algebra.TensorProduct.includeRight (f j))
      (PrimeSpectrum.relativeFibrePrime (R := R) qS) ↔
    RingTheory.Sequence.IsRegularAfterLocalizationAt
      (List.ofFn fun j ↦ Algebra.TensorProduct.includeRight (f j))
      (PrimeSpectrum.relativeFibrePrime (R := R) qS)
  exact Iff.rfl

/-- For a finite-type map, the relative regular-sequence locus for a fixed coefficient
sequence is open on its zero locus inside each fixed set-theoretic fibre. -/
theorem isOpen_relativeFibreRegularSequenceLocusOver
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S]
    {d : ℕ} (p : PrimeSpectrum R) (f : Fin d → S) :
    IsOpen (relativeFibreRegularSequenceLocusOver (R := R) p f) := by
  rw [relativeFibreRegularSequenceLocusOver_eq_fixedFibreRegularSequenceLocus]
  exact Ideal.Fiber.isOpen_fixedFibreRegularSequenceLocus p (List.ofFn f)

end Matrix.FiniteFreeComplex

end

end
