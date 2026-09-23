module

public import StacksAndModuli.API.PrimeSpectrumBasicOpenNeighborhood
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Residue fibres after principal localization

Principal localization commutes with passage to a residue fibre.  In concrete terms,
the fibre of `S[1/s]` over a prime `p` of the coefficient ring is the localization of
`κ(p) ⊗[R] S` away from `1 ⊗ s`.  This file also records the resulting Krull-dimension
identity with the corresponding principal open in the original fibre.

Main declarations:

* `Ideal.Fiber.awayAlgEquiv`;
* `Ideal.Fiber.ringKrullDim_away_eq_topologicalKrullDim_basicOpen`.
-/

@[expose] public section

noncomputable section

universe u v

open TensorProduct

namespace Ideal.Fiber

/-- The Krull dimension of a residue fibre is independent of the proof-level spelling
of its coefficient prime.  Keeping this transport behind a lemma avoids dependent
elimination failures caused by the `IsPrime` instance carried by `Ideal.Fiber`. -/
theorem ringKrullDim_congr_ideal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (h : p = q) :
    ringKrullDim (p.Fiber S) = ringKrullDim (q.Fiber S) := by
  subst q
  rfl

/-- Formation of a residue fibre commutes with localization away from one target
element. -/
noncomputable def awayAlgEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (s : S) :
    p.Fiber (Localization.Away s) ≃ₐ[p.ResidueField]
      Localization.Away
        (1 ⊗ₜ[R] s : p.Fiber S) :=
  IsLocalization.Away.tensorProductEquivTMulRight
    R p.ResidueField s (Localization.Away s)

/-- The Krull dimension of the fibre after principal localization is the topological
Krull dimension of the corresponding principal open in the original fibre. -/
theorem ringKrullDim_away_eq_topologicalKrullDim_basicOpen
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (s : S) :
    ringKrullDim (p.Fiber (Localization.Away s)) =
      topologicalKrullDim
        (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] s : p.Fiber S)) := by
  calc
    ringKrullDim (p.Fiber (Localization.Away s)) =
        ringKrullDim
          (Localization.Away (1 ⊗ₜ[R] s : p.Fiber S)) :=
      ringKrullDim_eq_of_ringEquiv (awayAlgEquiv p s).toRingEquiv
    _ = topologicalKrullDim
          (PrimeSpectrum.basicOpen (1 ⊗ₜ[R] s : p.Fiber S)) :=
      (PrimeSpectrum.topologicalKrullDim_basicOpen_eq_ringKrullDim_away _).symm

end Ideal.Fiber

end

end
