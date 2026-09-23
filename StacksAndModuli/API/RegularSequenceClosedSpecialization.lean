module

public import StacksAndModuli.API.PrimeSpectrumBasicOpenNeighborhood
public import StacksAndModuli.API.RegularSequencePrimeSpecialization
public import StacksAndModuli.API.RelativeFibreRegularSequenceLocus

/-!
# Closed specializations preserving local regularity

In a finite-type algebra over a field, the localization-regularity locus of a finite
sequence is open on its zero locus and the ring is Jacobson.  Hence every regular prime
has a maximal specialization which stays in that regularity locus.  This lets arguments
about relative dimension move from an arbitrary fibre point to a closed fibre point and
then return by stability of open sets under generization.

Main declaration:

* `RingTheory.Sequence.exists_isMaximal_specialization_isRegularAfterLocalizationAt`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

namespace RingTheory.Sequence

/-- In a finite-type algebra over a field, a sequence regular at a prime remains regular
at some maximal specialization of that prime. -/
theorem exists_isMaximal_specialization_isRegularAfterLocalizationAt
    (K : Type u) (T : Type v) [Field K] [CommRing T] [Nontrivial T]
    [Algebra K T] [Algebra.FiniteType K T]
    (rs : List T) (q : PrimeSpectrum T)
    (hmem : ∀ x ∈ rs, x ∈ q.asIdeal)
    (hreg : IsRegularAfterLocalizationAt rs q) :
    ∃ m : Ideal T, ∃ hm : m.IsMaximal,
      q.asIdeal ≤ m ∧
        letI : m.IsPrime := hm.isPrime
        IsRegularAfterLocalizationAt rs ⟨m, inferInstance⟩ := by
  let Z := PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set T)
  have hIq : Ideal.ofList rs ≤ q.asIdeal := Ideal.span_le.mpr hmem
  let qZ : Z := ⟨q, hIq⟩
  let L : Set Z := regularAfterLocalizationOnZeroLocus rs
  letI : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing K T
  have hopen : IsOpen L := isOpen_regularAfterLocalizationOnZeroLocus rs
  obtain ⟨U, hUopen, hUL⟩ := isOpen_induced_iff.mp hopen
  have hqU : q ∈ U := by
    have hqL : qZ ∈ L := hreg
    rw [← hUL] at hqL
    exact hqL
  let Uopen : TopologicalSpace.Opens (PrimeSpectrum T) := ⟨U, hUopen⟩
  obtain ⟨g, hqg, hgU⟩ :=
    PrimeSpectrum.exists_basicOpen_le_of_mem q Uopen hqU
  letI : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := K)
  obtain ⟨m, hm, hqm, hgm⟩ :=
    Ideal.exists_isMaximal_over_notMem_of_isJacobsonRing q.asIdeal hqg
  letI : m.IsPrime := hm.isPrime
  let mPoint : PrimeSpectrum T := ⟨m, inferInstance⟩
  have hIm : Ideal.ofList rs ≤ m := hIq.trans hqm
  let mZ : Z := ⟨mPoint, hIm⟩
  have hmU : mPoint ∈ U := hgU hgm
  have hmL : mZ ∈ L := by
    rw [← hUL]
    exact hmU
  exact ⟨m, hm, hqm, hmL⟩

end RingTheory.Sequence

end

end
