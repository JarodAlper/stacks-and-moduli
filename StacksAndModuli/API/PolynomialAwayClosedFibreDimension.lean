module

public import StacksAndModuli.API.FibreAwayBaseChange
public import StacksAndModuli.API.PolynomialFibrePureDimension
public import StacksAndModuli.API.PolynomialMaximalLocalizationDimension
public import StacksAndModuli.API.RelativeFibreRegularSequenceClosedPointDimension

/-!
# Dimension at closed points of localized polynomial fibres

The residue fibre of a principal localization of a polynomial algebra is a principal
localization of a polynomial ring over a field.  A maximal ideal in that localization
contracts to a maximal ideal of the polynomial ring, because polynomial rings over fields
are Jacobson.  Its height, and hence the dimension of its local ring, is therefore the
number of polynomial variables.

This gives the ambient relative-dimension calculation at fibre-closed points used in the
polynomial specialization of relative regular-sequence openness.

Main declarations:

* `Ideal.Fiber.isRegularLocalRing_localizationAtPrime_mvPolynomial_away`;
* `Ideal.Fiber.height_eq_natCard_mvPolynomial_away_of_isMaximal`;
* `MvPolynomial.relativeKrullDimAt_away_eq_natCard_of_closedFibrePoint`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

open TensorProduct

namespace Ideal.Fiber

/-- A residue fibre of a principal localization of a polynomial algebra is a regular
ring. -/
theorem isRegularRing_mvPolynomial_away
    {A : Type u} {sigma : Type v} [CommRing A] [Finite sigma]
    (p : Ideal A) [p.IsPrime] (a : MvPolynomial sigma A) :
    IsRegularRing (p.Fiber (Localization.Away a)) := by
  let K := p.ResidueField
  let T := p.Fiber (MvPolynomial sigma A)
  let b : T := 1 ⊗ₜ[A] a
  let L := Localization.Away b
  let commRingL : CommRing L := inferInstance
  letI : CommRing L := commRingL
  letI : CommSemiring L := commRingL.toCommSemiring
  letI : Semiring L := commRingL.toCommSemiring.toSemiring
  let e : p.Fiber (Localization.Away a) ≃+* L :=
    (Ideal.Fiber.awayAlgEquiv p a).toRingEquiv
  let ePolynomial : T ≃+* MvPolynomial sigma K :=
    (MvPolynomial.algebraTensorAlgEquiv A K).toRingEquiv
  letI : IsRegularRing (MvPolynomial sigma K) := inferInstance
  letI : IsRegularRing T :=
    IsRegularRing.of_ringEquiv ePolynomial.symm
  letI : IsNoetherianRing L :=
    IsLocalization.isNoetherianRing (Submonoid.powers b) L inferInstance
  have hL : IsRegularRing L := by
    rw [isRegularRing_iff]
    intro q hq
    let Tq := Localization.AtPrime (q.under T)
    let commRingTq : CommRing Tq := inferInstance
    letI : CommRing Tq := commRingTq
    letI : CommSemiring Tq := commRingTq.toCommSemiring
    letI : Semiring Tq := commRingTq.toCommSemiring.toSemiring
    let Lq := Localization.AtPrime q
    let commRingLq : CommRing Lq := inferInstance
    letI : CommRing Lq := commRingLq
    letI : CommSemiring Lq := commRingLq.toCommSemiring
    letI : Semiring Lq := commRingLq.toCommSemiring.toSemiring
    let eLocal : Tq ≃+* Lq :=
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (Submonoid.powers b) q).toRingEquiv
    exact IsRegularLocalRing.of_ringEquiv eLocal
  letI : IsRegularRing L := hL
  exact IsRegularRing.of_ringEquiv e.symm

/-- Every local ring of a residue fibre of a principal localization of a polynomial
algebra is regular local. -/
theorem isRegularLocalRing_localizationAtPrime_mvPolynomial_away
    {A : Type u} {sigma : Type v} [CommRing A] [Finite sigma]
    (p : Ideal A) [p.IsPrime] (a : MvPolynomial sigma A)
    (q : Ideal (p.Fiber (Localization.Away a))) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  letI : IsRegularRing (p.Fiber (Localization.Away a)) :=
    isRegularRing_mvPolynomial_away p a
  infer_instance

/-- A maximal ideal in a polynomial residue fibre has height equal to the number of
variables. -/
theorem height_eq_natCard_mvPolynomial_of_isMaximal
    {A : Type u} {sigma : Type v} [CommRing A] [Finite sigma]
    (p : Ideal A) [p.IsPrime]
    (m : Ideal (p.Fiber (MvPolynomial sigma A))) [m.IsMaximal] :
    m.height = (Nat.card sigma : ℕ∞) := by
  let K := p.ResidueField
  let e : p.Fiber (MvPolynomial sigma A) ≃+* MvPolynomial sigma K :=
    (MvPolynomial.algebraTensorAlgEquiv A K).toRingEquiv
  let m' : Ideal (MvPolynomial sigma K) := m.map e
  letI : m'.IsMaximal := Ideal.map_isMaximal_of_equiv e
  calc
    m.height = m'.height := (e.height_map m).symm
    _ = (Nat.card sigma : ℕ∞) :=
      MvPolynomial.height_eq_natCard_of_isMaximal K sigma m'

/-- A maximal ideal in the residue fibre of a principal localization of a polynomial
algebra has height equal to the number of variables. -/
theorem height_eq_natCard_mvPolynomial_away_of_isMaximal
    {A : Type u} {sigma : Type v} [CommRing A] [Finite sigma]
    (p : Ideal A) [p.IsPrime] (a : MvPolynomial sigma A)
    (m : Ideal (p.Fiber (Localization.Away a))) [m.IsMaximal] :
    m.height = (Nat.card sigma : ℕ∞) := by
  let K := p.ResidueField
  let T := p.Fiber (MvPolynomial sigma A)
  let b : T := 1 ⊗ₜ[A] a
  let L := Localization.Away b
  let e : p.Fiber (Localization.Away a) ≃+* L :=
    (Ideal.Fiber.awayAlgEquiv p a).toRingEquiv
  let mL : Ideal L := m.map e
  letI : mL.IsMaximal := Ideal.map_isMaximal_of_equiv e
  let mT : Ideal T := mL.under T
  letI : Algebra.FiniteType K T := inferInstance
  letI : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := K)
  have hmT : mT.IsMaximal :=
    ((IsLocalization.isMaximal_iff_isMaximal_disjoint L b mL).mp inferInstance).1
  letI : mT.IsMaximal := hmT
  calc
    m.height = mL.height := (e.height_map m).symm
    _ = mT.height :=
      (IsLocalization.height_under (Submonoid.powers b) mL).symm
    _ = (Nat.card sigma : ℕ∞) :=
      height_eq_natCard_mvPolynomial_of_isMaximal p mT

/-- The local ring at a maximal ideal of a localized polynomial residue fibre has
dimension equal to the number of variables. -/
theorem ringKrullDim_localizationAtPrime_mvPolynomial_away_eq_natCard
    {A : Type u} {sigma : Type v} [CommRing A] [Finite sigma]
    (p : Ideal A) [p.IsPrime] (a : MvPolynomial sigma A)
    (m : Ideal (p.Fiber (Localization.Away a))) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) =
      (Nat.card sigma : WithBot ℕ∞) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m
      (Localization.AtPrime m),
    height_eq_natCard_mvPolynomial_away_of_isMaximal p a m]
  exact ENat.WithBot.coe_eq_natCast _

end Ideal.Fiber

namespace MvPolynomial

/-- At a point closed in its residue fibre, a principal localization of a polynomial
algebra has relative dimension equal to the number of polynomial variables. -/
theorem relativeKrullDimAt_away_eq_natCard_of_closedFibrePoint
    {A : Type u} {sigma : Type v} [CommRing A] [Finite sigma]
    (a : MvPolynomial sigma A)
    (q : PrimeSpectrum (Localization.Away a))
    (hclosed :
      (PrimeSpectrum.relativeFibrePrime (R := A) q).asIdeal.IsMaximal) :
    Algebra.relativeKrullDimAt A (Localization.Away a) q =
      (Nat.card sigma : WithBot ℕ∞) := by
  let p : PrimeSpectrum A := q.comap (algebraMap A (Localization.Away a))
  let K := p.asIdeal.ResidueField
  let T := p.asIdeal.Fiber (Localization.Away a)
  let qF : PrimeSpectrum T :=
    PrimeSpectrum.relativeFibrePrime (R := A) q
  letI : Nontrivial T := qF.nontrivial
  letI : Algebra.FiniteType K T := inferInstance
  letI : qF.asIdeal.IsMaximal := hclosed
  change topologicalKrullDimAtPoint (PrimeSpectrum T) qF =
    (Nat.card sigma : WithBot ℕ∞)
  rw [PrimeSpectrum.topologicalKrullDimAtPoint_eq_ringKrullDim_localizationAtPrime
      K T qF]
  exact
    Ideal.Fiber.ringKrullDim_localizationAtPrime_mvPolynomial_away_eq_natCard
      p.asIdeal a qF.asIdeal

end MvPolynomial

end

end
