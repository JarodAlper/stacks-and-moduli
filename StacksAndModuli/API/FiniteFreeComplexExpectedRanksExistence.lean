module

public import StacksAndModuli.API.FiniteFreeComplexAssociatedPrimeExactness

/-!
# Existence of expected ranks for exact finite free complexes

An exact bounded finite free complex over a nonzero Noetherian ring has an expected-rank
function.  Choose an associated prime of the ring, localize there, and pass to the residue
field.  Exactness survives this specialization, so the actual ranks over that field satisfy
the expected-rank recursion.  Since coefficient extension does not change the term ranks,
the same natural-number function supplies expected ranks for the original complex.

Main declaration:

* `Matrix.FiniteFreeComplex.nonempty_expectedRanks_of_exact`.
-/

@[expose] public section

noncomputable section

universe u

namespace Matrix.FiniteFreeComplex

set_option linter.style.haveILetI false in
/-- A bounded exact finite free complex over a nonzero Noetherian ring admits an
expected-rank function. -/
theorem nonempty_expectedRanks_of_exact
    {R : Type u} [CommRing R] [Nontrivial R] [IsNoetherianRing R]
    (C : Matrix.FiniteFreeComplex R) (N : ℕ)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N) :
    Nonempty (C.ExpectedRanks N) := by
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R R
  letI : p.IsPrime := IsAssociatedPrime.isPrime hp
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  let Rp := Localization.AtPrime q.asIdeal
  let K := q.asIdeal.ResidueField
  let Ck := (C.map (algebraMap R Rp)).map (algebraMap Rp K)
  have hboundedK : Ck.IsBoundedAbove N :=
    (hbounded.map (algebraMap R Rp)).map (algebraMap Rp K)
  have hexactK : Ck.IsExactInPositiveDegreesUpTo N := by
    exact hexact.map_localization_residueField_of_mem_associatedPrimes
      hbounded q hp
  let rK : Ck.ExpectedRanks N :=
    Ck.expectedRanksOfExact N hboundedK hexactK
  exact ⟨{
    rank := rK.rank
    terminal := rK.terminal
    add_succ := rK.add_succ }⟩

end Matrix.FiniteFreeComplex

end
