module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Descending reducedness along a faithfully flat ring map

Stacks Project tag **033F**, label `algebra-lemma-descent-reduced`, in `algebra.tex`,
§`033D` (Descending properties).

> Let `R → S` be a ring map. Assume that (1) `R → S` is faithfully flat, and (2) `S` is
> reduced. Then `R` is reduced.

The Stacks proof is one line: a faithfully flat ring map is (universally) injective — Stacks
`05CK` — and a subring of a reduced ring is reduced. Mathlib has both halves:
`Module.FaithfullyFlat.faithfulSMul` gives `FaithfulSMul R S`, whence
`FaithfulSMul.algebraMap_injective`, and `isReduced_of_injective` transports reducedness back.
-/

@[expose] public section

universe u v

/-- **Stacks 033F** (`algebra-lemma-descent-reduced`). If `R → S` is faithfully flat and `S` is
reduced, then `R` is reduced. -/
@[stacks 033F]
theorem isReduced_of_faithfullyFlat (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] [IsReduced S] : IsReduced R :=
  isReduced_of_injective (algebraMap R S) (FaithfulSMul.algebraMap_injective R S)
