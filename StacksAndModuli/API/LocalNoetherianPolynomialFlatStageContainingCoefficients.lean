module

public import StacksAndModuli.API.LocalNoetherianPolynomialFlatAtArbitraryPrimeBaseChange
public import StacksAndModuli.API.PolynomialMatrixCoefficientBaseChange

/-!
# Local polynomial flat stages containing original presentation coefficients

For an explicit coefficient base change of a polynomial presentation, the image of the
original coefficient ring is a finitely generated coefficient stage.  The coefficient ring
of the base-changed presentation lies in that image.  Thus it is an object of the later-stage
local Noetherian system attached to the base-changed presentation.

The finite tensor obstruction used to produce a flat local stage remains zero after every
further transition.  Consequently the flat stage at a contracted polynomial prime can be
chosen above any prescribed later stage, and in particular above the image of the original
coefficient ring.  This keeps the original relation coefficients available when the local
Noetherian stage is subsequently compared with coefficient stages before localization.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open IsLocalRing TensorProduct

universe u v w

namespace Module.FinitePresentation.PolynomialModel

open LocalNoetherianApproximation

variable {A B M : Type u} {sigma : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module (MvPolynomial sigma A) M]

/-- The local-system index given by the image of the original presentation's coefficient
ring after a coefficient base change. -/
noncomputable def baseChangeCoefficientImageIndex
    (D : PolynomialModel A sigma M) : Index B :=
  ⟨Subalgebra.map (algebraMap A B).toIntAlgHom
      (D.coefficientRing (R := ℤ)),
    (D.coefficientRing_fg (R := ℤ)).map
      (algebraMap A B).toIntAlgHom⟩

/-- The canonical coefficient index of the explicit base-changed presentation precedes the
index given by the image of the original coefficient ring. -/
theorem baseChange_localIndex_le_coefficientImageIndex
    (D : PolynomialModel A sigma M) :
    letI : Algebra (MvPolynomial sigma A) (MvPolynomial sigma B) :=
      MvPolynomial.algebraMvPolynomial
    (D.baseChange (B := B)).localIndex ≤ D.baseChangeCoefficientImageIndex := by
  letI : Algebra (MvPolynomial sigma A) (MvPolynomial sigma B) :=
    MvPolynomial.algebraMvPolynomial
  exact D.coefficientRing_baseChange_le_map

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {N : Type w} [AddCommGroup N] [Module (MvPolynomial sigma R) N]

/-- Vanishing of the initial finite tensor obstruction at one local-system stage gives
flatness at the contracted limit prime at every later stage. -/
theorem flat_localSystemStage_atPrime_of_later_of_transition_comp_eq_zero [Finite sigma]
    (D : PolynomialModel R sigma N)
    (j k : Later R D.localIndex) (hjk : j ≤ k)
    (q : Ideal (MvPolynomial sigma R)) [q.IsPrime]
    (hq : q.comap (algebraMap R (MvPolynomial sigma R)) = maximalIdeal R)
    (hzero :
      (D.localSystemTensorObstructionTransition
        (initialLater R D.localIndex) j j.2).comp
          D.localInitialTensorKernelMap = 0) :
    Module.Flat (coefficient R k.1)
      (Localization.AtPrime (polynomialPrimeAtStage q k.1) ⊗[
        polynomial R sigma k] D.localSystemStage k) := by
  have hzeroK :
      (D.localSystemTensorObstructionTransition
        (initialLater R D.localIndex) k k.2).comp
          D.localInitialTensorKernelMap = 0 := by
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun hzero x
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hx ⊢
    calc
      D.localSystemTensorObstructionTransition
          (initialLater R D.localIndex) k k.2
          (D.localInitialTensorKernelMap x) =
          D.localSystemTensorObstructionTransition j k hjk
            (D.localSystemTensorObstructionTransition
              (initialLater R D.localIndex) j j.2
              (D.localInitialTensorKernelMap x)) := by
            symm
            exact DirectedSystem.map_map'
              (D.localSystemTensorObstructionTransition) j.2 hjk _
      _ = 0 := by rw [hx, map_zero]
  apply D.flat_localSystemStage_atPrime_of_transition_comp_eq_zero
    k (polynomialPrimeAtStage q k.1)
    (polynomialPrimeAtStage_comap_algebraMap q k.1 hq)
  exact hzeroK

/-- At a prime over the closed point, the flat local Noetherian stage supplied by the finite
tensor obstruction can be chosen above any prescribed later coefficient stage.

The proof uses more than persistence of a bare flatness instance: the transitioned finite
tensor obstruction is zero at the first stage and remains zero at every later stage. -/
theorem exists_later_flat_localSystemStage_atPrime_above [Finite sigma]
    (D : PolynomialModel R sigma N)
    (i : Later R D.localIndex)
    (q : Ideal (MvPolynomial sigma R)) [q.IsPrime]
    (hq : q.comap (algebraMap R (MvPolynomial sigma R)) = maximalIdeal R)
    (hflat :
      letI : Module R N := Module.compHom N
        (algebraMap R (MvPolynomial sigma R))
      Module.Flat R N) :
    ∃ k : Later R D.localIndex, i ≤ k ∧
      Module.Flat (coefficient R k.1)
        (Localization.AtPrime (polynomialPrimeAtStage q k.1) ⊗[
          polynomial R sigma k] D.localSystemStage k) := by
  obtain ⟨j, hij, hzero⟩ :=
    D.exists_later_localInitialTensorKernelMap_eq_zero hflat
  obtain ⟨k, hjk, hik⟩ := exists_ge_ge j i
  exact ⟨k, hik,
    D.flat_localSystemStage_atPrime_of_later_of_transition_comp_eq_zero
      j k hjk q hq hzero⟩

set_option maxHeartbeats 800000 in
-- The nested localization and explicit tensor base-change endpoint exceeds the default limit.
/-- At an arbitrary polynomial prime, the explicit base-changed presentation has a flat
local Noetherian stage whose underlying finitely generated coefficient subalgebra contains
the image of every coefficient of the original presentation. -/
theorem exists_later_flat_baseChangeLocalSystemStage_containing_originalCoefficients
    [Finite sigma]
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
    ∃ k : Later Aq Dq.localIndex,
      (D.baseChangeCoefficientImageIndex (B := Aq)).1 ≤ k.1.1 ∧
        Module.Flat (coefficient Aq k.1)
          (Localization.AtPrime
              (polynomialPrimeAtStage
                (MvPolynomial.coefficientLocalizedPrime q).asIdeal k.1) ⊗[
            polynomial Aq sigma k] Dq.localSystemStage k) := by
  let Aq := MvPolynomial.coefficientLocalization q
  let Sq := MvPolynomial.polynomialCoefficientLocalization q
  let S := MvPolynomial sigma A
  letI : Algebra S Sq := MvPolynomial.algebraMvPolynomial
  let Mq := Sq ⊗[S] M
  let Dq : PolynomialModel Aq sigma Mq := D.baseChange
  let i : Later Aq Dq.localIndex :=
    ⟨D.baseChangeCoefficientImageIndex (B := Aq),
      D.baseChange_localIndex_le_coefficientImageIndex (B := Aq)⟩
  change ∃ k : Later Aq Dq.localIndex,
    (D.baseChangeCoefficientImageIndex (B := Aq)).1 ≤ k.1.1 ∧
      Module.Flat (coefficient Aq k.1)
        (Localization.AtPrime
            (polynomialPrimeAtStage
              (MvPolynomial.coefficientLocalizedPrime q).asIdeal k.1) ⊗[
          polynomial Aq sigma k] Dq.localSystemStage k)
  letI : Module A M := Module.compHom M (algebraMap A S)
  letI : IsScalarTower A S M := IsScalarTower.of_compHom A S M
  let _ : Module.Flat A M := hflat
  have hMq :
      letI : Module Aq Mq := Module.compHom Mq (algebraMap Aq Sq)
      Module.Flat Aq Mq := by
    have hmodule :
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
  obtain ⟨k, hik, hkflat⟩ :=
    Dq.exists_later_flat_localSystemStage_atPrime_above i
      (MvPolynomial.coefficientLocalizedPrime q).asIdeal
      (by simpa only [MvPolynomial.algebraMap_eq] using
        MvPolynomial.coefficientLocalizedPrime_comap_C q)
      hMq
  exact ⟨k, hik, hkflat⟩

end Module.FinitePresentation.PolynomialModel

end

end
