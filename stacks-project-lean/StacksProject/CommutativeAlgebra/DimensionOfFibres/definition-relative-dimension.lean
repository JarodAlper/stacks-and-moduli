module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import StacksProject.Topology.KrullDimension.«definition-Krull»

/-!
# Relative dimension at a prime

Stacks Project tag **00QD**, label `definition-relative-dimension`, in `algebra.tex`,
§`00QC` (Dimension of fibres).

For a finite-type ring map `R → S` and a prime `q` of `S`, the relative dimension at
`q` is the topological dimension at the corresponding point of the fibre over `q ∩ R`.

Main declaration:

* `Algebra.relativeKrullDimAt`.
-/

@[expose] public section

noncomputable section

universe u v

namespace Algebra

/-- **Stacks 00QD** (`definition-relative-dimension`).  The relative dimension of a
finite-type algebra `S/R` at a prime `q` is the topological Krull dimension at the
corresponding point of the residue fibre over `q ∩ R`. -/
@[stacks 00QD]
noncomputable def relativeKrullDimAt
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (q : PrimeSpectrum S) : WithBot ℕ∞ :=
  topologicalKrullDimAtPoint
    (PrimeSpectrum ((q.comap (algebraMap R S)).asIdeal.Fiber S))
    (PrimeSpectrum.preimageEquivFiber R S
      (q.comap (algebraMap R S)) ⟨q, rfl⟩)

end Algebra

end

end
