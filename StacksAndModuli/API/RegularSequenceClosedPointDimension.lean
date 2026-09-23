module

public import StacksAndModuli.API.AffineClosedPointDimension
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Dimension drop by a regular sequence at a closed point

Localization commutes with quotienting: the local ring of `R / I` at the prime induced
by `p ⊇ I` is the quotient of `Rₚ` by the extension of `I`.  Consequently, a regular
sequence in `Rₚ` lowers the dimension of this quotient local ring by its length.

Over a finite-type algebra over a field, pointwise topological dimension at a closed point
is the dimension of the local ring.  The local calculation therefore gives the analogous
pointwise topological dimension drop.  This is the closed-point form of the dimension
calculation used in relative regular-sequence openness.

Main declarations:

* `Ideal.localizationAtPrimeQuotientEquiv`;
* `RingTheory.Sequence.ringKrullDim_localizationAtPrime_quotient_add_length_eq_of_isRegular`;
* `PrimeSpectrum.topologicalKrullDimAtPoint_quotient_add_length_eq_of_isRegular`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

namespace PrimeSpectrum

/-- The prime of a quotient induced by a prime containing the quotient ideal. -/
noncomputable def quotientOfLE
    {R : Type u} [CommRing R] (I : Ideal R) (p : PrimeSpectrum R)
    (hIp : I ≤ p.asIdeal) : PrimeSpectrum (R ⧸ I) :=
  ⟨p.asIdeal.map (Ideal.Quotient.mk I),
    Ideal.isPrime_map_quotientMk_of_isPrime hIp⟩

@[simp]
theorem quotientOfLE_asIdeal
    {R : Type u} [CommRing R] (I : Ideal R) (p : PrimeSpectrum R)
    (hIp : I ≤ p.asIdeal) :
    (quotientOfLE I p hIp).asIdeal =
      p.asIdeal.map (Ideal.Quotient.mk I) :=
  rfl

@[simp]
theorem comap_quotientOfLE
    {R : Type u} [CommRing R] (I : Ideal R) (p : PrimeSpectrum R)
    (hIp : I ≤ p.asIdeal) :
    PrimeSpectrum.comap (Ideal.Quotient.mk I) (quotientOfLE I p hIp) = p := by
  exact PrimeSpectrum.ext
    (Ideal.comap_map_mk (I := I) (J := p.asIdeal) hIp)

end PrimeSpectrum

namespace Ideal

/-- The local ring of `R / I` at a prime lying over `p` is the quotient of `Rₚ` by the
extension of `I`. -/
noncomputable def localizationAtPrimeQuotientEquiv
    {R : Type u} [CommRing R] (I p : Ideal R) [p.IsPrime]
    (q : Ideal (R ⧸ I)) [q.IsPrime] [q.LiesOver p] :
    Localization.AtPrime q ≃ₐ[R ⧸ I]
      (Localization.AtPrime p ⧸
        I.map (algebraMap R (Localization.AtPrime p))) := by
  let Rp := Localization.AtPrime p
  let Q := Rp ⧸ I.map (algebraMap R Rp)
  have hM : Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl =
      q.primeCompl :=
    Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective
      (p := p) (P := q) Ideal.Quotient.mk_surjective
  letI : IsLocalization q.primeCompl Q := by
    rw [← hM]
    infer_instance
  exact IsLocalization.algEquiv q.primeCompl _ _

end Ideal

namespace RingTheory.Sequence

/-- A regular sequence in the local ring at `p` lowers the dimension of the local ring of
the corresponding quotient by the length of the sequence. -/
theorem ringKrullDim_localizationAtPrime_quotient_add_length_eq_of_isRegular
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (p : PrimeSpectrum R) (rs : List R)
    (hmem : ∀ x ∈ rs, x ∈ p.asIdeal)
    (hreg : IsRegular (Localization.AtPrime p.asIdeal)
      (rs.map (algebraMap R (Localization.AtPrime p.asIdeal)))) :
    let I := Ideal.ofList rs
    let hIp : I ≤ p.asIdeal := Ideal.span_le.mpr hmem
    let pbar := PrimeSpectrum.quotientOfLE I p hIp
    ringKrullDim (Localization.AtPrime pbar.asIdeal) + rs.length =
      ringKrullDim (Localization.AtPrime p.asIdeal) := by
  let I := Ideal.ofList rs
  have hIp : I ≤ p.asIdeal := Ideal.span_le.mpr hmem
  let pbar := PrimeSpectrum.quotientOfLE I p hIp
  let Rp := Localization.AtPrime p.asIdeal
  let rsRp : List Rp := rs.map (algebraMap R Rp)
  letI : pbar.asIdeal.LiesOver p.asIdeal := ⟨by
    dsimp only [pbar, PrimeSpectrum.quotientOfLE,
      PrimeSpectrum.asIdeal, I]
    exact (Ideal.comap_map_mk
      (I := Ideal.ofList rs) (J := p.asIdeal) hIp).symm⟩
  let e := Ideal.localizationAtPrimeQuotientEquiv
    I p.asIdeal pbar.asIdeal
  have hmap : I.map (algebraMap R Rp) = Ideal.ofList rsRp := by
    exact Ideal.map_ofList (algebraMap R Rp) rs
  calc
    ringKrullDim (Localization.AtPrime pbar.asIdeal) + rs.length =
        ringKrullDim
            (Rp ⧸ I.map (algebraMap R Rp)) + rs.length := by
      rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
    _ = ringKrullDim (Rp ⧸ Ideal.ofList rsRp) + rsRp.length := by
      rw [hmap, List.length_map]
    _ = ringKrullDim Rp := by
      exact ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rsRp hreg

end RingTheory.Sequence

namespace PrimeSpectrum

/-- At a closed point of a finite-type algebra over a field, quotienting by a sequence
which is regular in the local ring lowers pointwise topological dimension by the length
of the sequence. -/
theorem topologicalKrullDimAtPoint_quotient_add_length_eq_of_isRegular
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A]
    (p : PrimeSpectrum A) [p.asIdeal.IsMaximal] (rs : List A)
    (hmem : ∀ x ∈ rs, x ∈ p.asIdeal)
    (hreg : RingTheory.Sequence.IsRegular
      (Localization.AtPrime p.asIdeal)
      (rs.map (algebraMap A (Localization.AtPrime p.asIdeal)))) :
    let I := Ideal.ofList rs
    let hIp : I ≤ p.asIdeal := Ideal.span_le.mpr fun x hx ↦ hmem x hx
    let pbar := quotientOfLE I p hIp
    topologicalKrullDimAtPoint (PrimeSpectrum (A ⧸ I)) pbar + rs.length =
      topologicalKrullDimAtPoint (PrimeSpectrum A) p := by
  let I := Ideal.ofList rs
  have hIp : I ≤ p.asIdeal := Ideal.span_le.mpr hmem
  let pbar := quotientOfLE I p hIp
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  letI : Nontrivial (A ⧸ I) := pbar.nontrivial
  letI : pbar.asIdeal.IsMaximal := by
    dsimp only [pbar, quotientOfLE, PrimeSpectrum.asIdeal]
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective
      (by simpa only [I, Ideal.mk_ker] using hIp)
  change topologicalKrullDimAtPoint (PrimeSpectrum (A ⧸ I)) pbar + rs.length =
    topologicalKrullDimAtPoint (PrimeSpectrum A) p
  rw [topologicalKrullDimAtPoint_eq_ringKrullDim_localizationAtPrime
      k A p,
    topologicalKrullDimAtPoint_eq_ringKrullDim_localizationAtPrime
      k (A ⧸ I) pbar]
  exact
    RingTheory.Sequence.ringKrullDim_localizationAtPrime_quotient_add_length_eq_of_isRegular
      p rs hmem hreg

end PrimeSpectrum

end

end
