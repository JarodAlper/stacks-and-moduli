module

public import StacksAndModuli.API.FiniteFreeComplexExactExpectedRanks

/-!
# Tails of finite free complexes

Dropping the degree-zero term of a matrix finite free complex shifts every term and
differential down by one.  This file records the resulting complex and transports the
boundedness, expected-rank, rank-bound, and exactness data used in induction on the length
of a Buchsbaum--Eisenbud complex.

Main declarations:

* `Matrix.FiniteFreeComplex.tail`;
* `Matrix.FiniteFreeComplex.ExpectedRanks.tail`;
* `Matrix.FiniteFreeComplex.IsExactInPositiveDegreesUpTo.tail`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

namespace Matrix.FiniteFreeComplex

variable {R : Type u} [CommRing R]

/-- The tail of a finite free complex, obtained by deleting its term in degree zero. -/
def tail (C : FiniteFreeComplex R) : FiniteFreeComplex R where
  termRank i := C.termRank (i + 1)
  differential i := C.differential (i + 1)
  differential_sq i := C.differential_sq (i + 1)

@[simp]
theorem tail_termRank (C : FiniteFreeComplex R) (i : ℕ) :
    C.tail.termRank i = C.termRank (i + 1) :=
  rfl

@[simp]
theorem tail_differential (C : FiniteFreeComplex R) (i : ℕ) :
    C.tail.differential i = C.differential (i + 1) :=
  rfl

/-- Taking the tail commutes with coefficient extension. -/
@[simp]
theorem tail_map {S : Type v} [CommRing S]
    (C : FiniteFreeComplex R) (f : R →+* S) :
    (C.map f).tail = C.tail.map f :=
  rfl

/-- Deleting the degree-zero term lowers an upper bound by one. -/
theorem IsBoundedAbove.tail {C : FiniteFreeComplex R} {N : ℕ}
    (h : C.IsBoundedAbove (N + 1)) : C.tail.IsBoundedAbove N := by
  intro i hi
  exact h (i + 1) (by omega)

namespace ExpectedRanks

/-- Expected ranks on a complex restrict to expected ranks on its tail. -/
def tail {C : FiniteFreeComplex R} {N : ℕ}
    (r : C.ExpectedRanks (N + 1)) : C.tail.ExpectedRanks N where
  rank i := r.rank (i + 1)
  terminal := by simpa only [Nat.add_comm] using r.terminal
  add_succ i hi := by
    simpa only [tail_termRank, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      r.add_succ (i + 1) (by omega)

@[simp]
theorem tail_rank {C : FiniteFreeComplex R} {N : ℕ}
    (r : C.ExpectedRanks (N + 1)) (i : ℕ) :
    r.tail.rank i = r.rank (i + 1) :=
  rfl

/-- Restricting expected ranks to a tail commutes with coefficient extension. -/
@[simp]
theorem tail_map {S : Type v} [CommRing S]
    {C : FiniteFreeComplex R} {N : ℕ} (r : C.ExpectedRanks (N + 1))
    (f : R →+* S) :
    (r.map f).tail = r.tail.map f :=
  rfl

end ExpectedRanks

/-- Expected-rank upper bounds restrict to the tail complex. -/
theorem HasExpectedRankBounds.tail
    {C : FiniteFreeComplex R} {N : ℕ} (r : C.ExpectedRanks (N + 1))
    (h : C.HasExpectedRankBounds r) :
    C.tail.HasExpectedRankBounds r.tail := by
  intro i hi
  simpa only [tail_differential, ExpectedRanks.tail_rank] using
    h (i + 1) (by omega)

/-- Exactness of a bounded range restricts to the corresponding range of the tail. -/
theorem IsExactInPositiveDegreesUpTo.tail
    {C : FiniteFreeComplex R} {N : ℕ}
    (h : C.IsExactInPositiveDegreesUpTo (N + 1)) :
    C.tail.IsExactInPositiveDegreesUpTo N := by
  intro i hi
  change Function.Exact
    (Matrix.toLin' (C.differential ((i + 1) + 1)))
    (Matrix.toLin' (C.differential (i + 1)))
  exact h (i + 1) (by omega)

end Matrix.FiniteFreeComplex

end

end
