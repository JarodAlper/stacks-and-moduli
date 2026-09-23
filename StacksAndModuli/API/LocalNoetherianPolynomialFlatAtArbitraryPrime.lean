module

public import StacksAndModuli.API.LocalNoetherianPolynomialFlatAtPrime
public import StacksAndModuli.API.PolynomialPrimeCoefficientLocalization
public import StacksAndModuli.API.SemilinearTransport

/-!
# Local Noetherian polynomial stages at arbitrary primes

Given a prime `q` of `A[x_i]`, first localize `A` at `q ∩ A` and base change the
polynomial module.  The extended prime then lies over the closed point of the new local
coefficient ring.  The closed-point approximation theorem consequently supplies a later
local Noetherian polynomial stage whose localization at the contracted prime is flat over
its coefficient ring.

This is the per-prime approximation step toward Stacks Project tag 02JO.  It does not
assert that one coefficient stage works simultaneously near every prime; that further step
requires openness of the flat locus and quasi-compactness.

Main declaration:
- `PolynomialModel.exists_later_flat_localSystemStage_at_arbitraryPrime`.
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u v

namespace Module.FinitePresentation.PolynomialModel

variable {A : Type u} [CommRing A]
variable {sigma : Type v}
variable {M : Type u} [AddCommGroup M] [Module (MvPolynomial sigma A) M]

/-- Finite free presentation data certifies that its target module is finitely
presented. -/
theorem finitePresentation_of_model (D : PolynomialModel A sigma M) :
    Module.FinitePresentation (MvPolynomial sigma A) M := by
  apply Module.finitePresentation_of_surjective D.quotient D.quotient_surjective
  rw [D.exact.linearMap_ker_eq]
  exact Submodule.fg_range D.relation

/-- At an arbitrary polynomial prime, localizing the coefficient ring at the contracted
prime and base changing a coefficient-flat finitely presented module produces a local
Noetherian approximation stage that is flat after localization at the corresponding
contracted polynomial prime. -/
theorem exists_later_flat_localSystemStage_at_arbitraryPrime [Finite sigma]
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
    ∃ Dq : PolynomialModel Aq sigma Mq,
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
  change ∃ Dq : PolynomialModel Aq sigma Mq,
    ∃ j : LocalNoetherianApproximation.Later Aq Dq.localIndex,
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
  let _ : Module.FinitePresentation S M := D.finitePresentation_of_model
  let _ : Module.FinitePresentation Sq Mq := inferInstance
  let Dq : PolynomialModel Aq sigma Mq := PolynomialModel.ofFinitePresentation
  refine ⟨Dq, ?_⟩
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
