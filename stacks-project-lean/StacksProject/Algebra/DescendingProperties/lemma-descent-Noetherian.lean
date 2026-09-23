module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Descending the Noetherian property along a faithfully flat ring map

Stacks Project tag **033E**, label `algebra-lemma-descent-Noetherian`, in
`algebra.tex`, §`033D` (Descending properties).

> Let `R → S` be a ring map. Assume that (1) `R → S` is faithfully flat, and (2) `S` is
> Noetherian. Then `R` is Noetherian.

Mathlib proves the underlying module statement as
`Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat`, via the order
embedding of submodules under base change; the ring statement is the case `M = R`.
-/

@[expose] public section

open TensorProduct

universe u v

/-- **Stacks 033E** (`algebra-lemma-descent-Noetherian`). If `R → S` is faithfully flat and `S`
is Noetherian, then `R` is Noetherian. -/
@[stacks 033E]
theorem isNoetherianRing_of_faithfullyFlat (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] [IsNoetherianRing S] : IsNoetherianRing R := by
  have h : IsNoetherian S (S ⊗[R] R) :=
    isNoetherian_of_linearEquiv (TensorProduct.AlgebraTensorModule.rid R S S).symm
  exact Submodule.IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat h
