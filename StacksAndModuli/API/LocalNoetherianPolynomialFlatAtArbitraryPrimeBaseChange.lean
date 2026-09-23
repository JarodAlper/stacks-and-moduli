module

public import StacksAndModuli.API.LocalNoetherianPolynomialFlatAtArbitraryPrime
public import StacksAndModuli.API.PolynomialModelBaseChange

/-!
# Functorial local polynomial stages at arbitrary primes

The arbitrary-prime local approximation theorem can use the explicit scalar extension of the
original polynomial presentation.  This strengthens the earlier existential formulation by
retaining the generators, relations, and coefficientwise relation-matrix map.  That provenance
is needed when the resulting local Noetherian stage is compared with the canonical system of
finitely generated coefficient subalgebras of the original coefficient ring.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open IsLocalRing TensorProduct

universe u v

namespace Module.FinitePresentation.PolynomialModel

variable {A M : Type u} {sigma : Type v} [CommRing A]
variable [AddCommGroup M] [Module (MvPolynomial sigma A) M]

/-- At an arbitrary polynomial prime, the explicit base-changed presentation has a later
local Noetherian stage which is coefficient-flat at the contracted extended prime. -/
theorem exists_later_flat_baseChangeLocalSystemStage_at_arbitraryPrime [Finite sigma]
    (D : PolynomialModel A sigma M)
    (q : PrimeSpectrum (MvPolynomial sigma A))
    (hflat :
      letI : Module A M := Module.compHom M
        (algebraMap A (MvPolynomial sigma A))
      Module.Flat A M) :
    let Aq := MvPolynomial.coefficientLocalization q
    let Sq := MvPolynomial.polynomialCoefficientLocalization q
    letI : Algebra (MvPolynomial sigma A) Sq :=
      MvPolynomial.algebraMvPolynomial
    let Mq := Sq ⊗[MvPolynomial sigma A] M
    let Dq : PolynomialModel Aq sigma Mq := D.baseChange
    ∃ j : LocalNoetherianApproximation.Later Aq Dq.localIndex,
      ∃ _hij : LocalNoetherianApproximation.initialLater Aq Dq.localIndex ≤ j,
        Module.Flat (LocalNoetherianApproximation.coefficient Aq j.1)
          (Localization.AtPrime
              (LocalNoetherianApproximation.polynomialPrimeAtStage
                (MvPolynomial.coefficientLocalizedPrime q).asIdeal j.1) ⊗[
            LocalNoetherianApproximation.polynomial Aq sigma j]
              Dq.localSystemStage j) := by
  let Aq := MvPolynomial.coefficientLocalization q
  let Sq := MvPolynomial.polynomialCoefficientLocalization q
  let S := MvPolynomial sigma A
  letI : Algebra S Sq := MvPolynomial.algebraMvPolynomial
  let Mq := Sq ⊗[S] M
  let Dq : PolynomialModel Aq sigma Mq := D.baseChange
  change ∃ j : LocalNoetherianApproximation.Later Aq Dq.localIndex,
    ∃ _hij : LocalNoetherianApproximation.initialLater Aq Dq.localIndex ≤ j,
      Module.Flat (LocalNoetherianApproximation.coefficient Aq j.1)
        (Localization.AtPrime
            (LocalNoetherianApproximation.polynomialPrimeAtStage
              (MvPolynomial.coefficientLocalizedPrime q).asIdeal j.1) ⊗[
          LocalNoetherianApproximation.polynomial Aq sigma j]
            Dq.localSystemStage j)
  letI : Module A M := Module.compHom M (algebraMap A S)
  letI : IsScalarTower A S M := IsScalarTower.of_compHom A S M
  let _ : Module.Flat A M := hflat
  apply Dq.exists_later_flat_localSystemStage_atPrime
    (MvPolynomial.coefficientLocalizedPrime q).asIdeal
  · simpa only [MvPolynomial.algebraMap_eq] using
      MvPolynomial.coefficientLocalizedPrime_comap_C q
  · have hmodule :
        Module.compHom Mq (algebraMap Aq Sq) =
          (TensorProduct.leftModule : Module Aq Mq) := by
      apply Module.ext'
      intro a x
      change (algebraMap Aq Sq a : Sq) • x = _
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, smul_zero]
      | add x y hx hy => rw [smul_add, smul_add, hx, hy]
      | tmul s m =>
          rw [TensorProduct.smul_tmul']
          exact congrArg (fun t : Sq => t ⊗ₜ[S] m)
            (IsScalarTower.algebraMap_smul Sq a s)
    rw [hmodule]
    exact Module.Flat.baseChange_of_isPushout A Aq S Sq M

end Module.FinitePresentation.PolynomialModel

end

end
