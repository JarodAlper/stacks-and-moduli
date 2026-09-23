module

public import StacksAndModuli.API.LocalNoetherianPolynomialTensorKernelComparison
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Flat local polynomial stages from a killed tensor obstruction

The finite obstruction associated to a local polynomial model is killed at one later
coefficient stage by `exists_later_localInitialTensorKernelMap_eq_zero`.  The comparison
theorem `tensorMul_injective_of_transition_comp_eq_zero` then makes multiplication by the
maximal ideal of that coefficient ring injective.

This file connects those results to the Noetherian local flatness criterion.  The criterion
applies whenever the stage module is finite over a local Noetherian algebra over the
coefficient ring.  In particular, it applies with that algebra equal to the coefficient ring
itself when the stage module is coefficient-finite.

The residue-fibre flatness input used by the tensor-kernel comparison is automatic: the raw
quotient by the maximal ideal is the residue field, and every vector space is free.
-/

@[expose] public section

open IsLocalRing TensorProduct

universe u v w

namespace Module.FinitePresentation.PolynomialModel

open LocalNoetherianApproximation

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {sigma : Type v}
variable {M : Type w} [AddCommGroup M] [Module (MvPolynomial sigma R) M]

/-- The closed fibre of a local polynomial model is flat over the residue field of its
coefficient ring. -/
theorem localModelClosedFibre_flat (D : PolynomialModel R sigma M) :
    Module.Flat
      (D.localCoefficient ⧸ maximalIdeal D.localCoefficient)
      ((D.localCoefficient ⧸ maximalIdeal D.localCoefficient) ⊗[
        D.localCoefficient] D.localModelModule) := by
  change Module.Flat (IsLocalRing.ResidueField D.localCoefficient)
    ((IsLocalRing.ResidueField D.localCoefficient) ⊗[
      D.localCoefficient] D.localModelModule)
  exact Module.Flat.of_free

/-- If a later polynomial stage is finite over a local Noetherian algebra over its
coefficient ring, vanishing of the transitioned tensor obstruction makes that stage flat
over the coefficient ring. -/
theorem flat_localSystemStage_of_transition_comp_eq_zero
    (D : PolynomialModel R sigma M) (j : Later R D.localIndex)
    (S : Type u) [CommRing S] [Algebra (coefficient R j.1) S]
    [IsNoetherianRing S] [IsLocalRing S]
    [IsLocalHom (algebraMap (coefficient R j.1) S)]
    [Module S (D.localSystemStage j)]
    [IsScalarTower (coefficient R j.1) S (D.localSystemStage j)]
    [Module.Finite S (D.localSystemStage j)]
    (hzero :
      (D.localSystemTensorObstructionTransition
        (initialLater R D.localIndex) j j.2).comp
          D.localInitialTensorKernelMap = 0) :
    Module.Flat (coefficient R j.1) (D.localSystemStage j) := by
  let _ : Module.Flat
      (D.localCoefficient ⧸ maximalIdeal D.localCoefficient)
      ((D.localCoefficient ⧸ maximalIdeal D.localCoefficient) ⊗[
        D.localCoefficient] D.localModelModule) := D.localModelClosedFibre_flat
  apply Module.Flat.of_maximalIdeal_rTensor_injective_of_finite S
  exact (Ideal.tensorMul_injective_iff_rTensor_injective
    (R := coefficient R j.1) (S := polynomial R sigma j)
    (M := D.localSystemStage j) (maximalIdeal (coefficient R j.1))).mp
      (D.tensorMul_injective_of_transition_comp_eq_zero j hzero)

/-- Coefficient-finite specialization of
`flat_localSystemStage_of_transition_comp_eq_zero`. -/
theorem flat_localSystemStage_of_transition_comp_eq_zero_of_finite
    (D : PolynomialModel R sigma M) (j : Later R D.localIndex)
    [Module.Finite (coefficient R j.1) (D.localSystemStage j)]
    (hzero :
      (D.localSystemTensorObstructionTransition
        (initialLater R D.localIndex) j j.2).comp
          D.localInitialTensorKernelMap = 0) :
    Module.Flat (coefficient R j.1) (D.localSystemStage j) := by
  exact D.flat_localSystemStage_of_transition_comp_eq_zero
    j (coefficient R j.1) hzero

/-- A flat polynomial module over the original local ring has a later coefficient-flat
model provided the later polynomial models are finite over their coefficient rings. -/
theorem exists_later_flat_localSystemStage_of_finite_over_coefficient [Finite sigma]
    (D : PolynomialModel R sigma M)
    (hflat :
      letI : Module R M := Module.compHom M
        (algebraMap R (MvPolynomial sigma R))
      Module.Flat R M)
    (hfinite : ∀ j : Later R D.localIndex,
      Module.Finite (coefficient R j.1) (D.localSystemStage j)) :
    ∃ j : Later R D.localIndex,
      ∃ _ : initialLater R D.localIndex ≤ j,
        Module.Flat (coefficient R j.1) (D.localSystemStage j) := by
  obtain ⟨j, hij, hzero⟩ :=
    D.exists_later_localInitialTensorKernelMap_eq_zero hflat
  let _ : Module.Finite (coefficient R j.1) (D.localSystemStage j) :=
    hfinite j
  exact ⟨j, hij, D.flat_localSystemStage_of_transition_comp_eq_zero_of_finite j hzero⟩

end Module.FinitePresentation.PolynomialModel
