module

public import StacksAndModuli.API.LocalNoetherianPolynomialModel
public import StacksAndModuli.API.LocalNoetherianPolynomialSystem

/-!
# Direct-limit system attached to a local polynomial presentation

A finite presentation over a polynomial ring on a local base descends to one local
Noetherian coefficient stage.  Scalar-extending that fixed descended presentation through
all later coefficient stages gives a directed system whose limit is the original module.

This packages the concrete ring-and-module system used in the local approximation argument
of Stacks Project tags 00QX and 00R6.  Eventual flatness of a stage is not asserted here.
-/

@[expose] public section

universe u v w

namespace Module.FinitePresentation.PolynomialModel

open LocalNoetherianApproximation TensorProduct

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {σ : Type v}
variable {M : Type w} [AddCommGroup M] [Module (MvPolynomial σ R) M]

/-- The scalar extension of a local Noetherian polynomial model to a later coefficient
stage. -/
noncomputable abbrev localSystemStage (D : PolynomialModel R σ M)
    (j : Later R D.localIndex) : Type max u v :=
  polynomialBaseChange R σ D.localIndex D.localModelModule j

/-- Transition map between later scalar extensions of the local polynomial model. -/
noncomputable abbrev localSystemTransition (D : PolynomialModel R σ M)
    (j k : Later R D.localIndex) (h : j ≤ k) :
    D.localSystemStage j →ₗ[MvPolynomial σ D.localCoefficient]
      D.localSystemStage k :=
  polynomialBaseChangeTransition R σ D.localIndex D.localModelModule j k h

/-- Every later scalar extension of the local model remains finitely presented over its
polynomial ring. -/
theorem localSystemStage_finitePresentation (D : PolynomialModel R σ M)
    (j : Later R D.localIndex) :
    Module.FinitePresentation (polynomial R σ j) (D.localSystemStage j) := by
  letI : Module.FinitePresentation
      (MvPolynomial σ D.localCoefficient) D.localModelModule :=
    D.localModelModule_finitePresentation
  infer_instance

/-- Every later scalar extension of the local model is finite over its polynomial ring. -/
theorem localSystemStage_finite (D : PolynomialModel R σ M)
    (j : Later R D.localIndex) :
    Module.Finite (polynomial R σ j) (D.localSystemStage j) := by
  letI : Module.FinitePresentation (polynomial R σ j) (D.localSystemStage j) :=
    D.localSystemStage_finitePresentation j
  infer_instance

/-- The direct limit of the later scalar extensions of a local polynomial presentation is
the original module, after restricting scalars to the initial polynomial stage. -/
noncomputable def localSystemLimitEquiv (D : PolynomialModel R σ M) :
    letI : Algebra D.localCoefficient R := D.localCoefficientAlgebra
    letI : Algebra (MvPolynomial σ D.localCoefficient) (MvPolynomial σ R) :=
      MvPolynomial.algebraMvPolynomial
    letI : Module (MvPolynomial σ D.localCoefficient) M :=
      Module.compHom M
        (algebraMap (MvPolynomial σ D.localCoefficient) (MvPolynomial σ R))
    Module.DirectLimit
        (fun j : Later R D.localIndex ↦ D.localSystemStage j)
        (fun j k h ↦ D.localSystemTransition j k h) ≃ₗ[
          MvPolynomial σ D.localCoefficient] M := by
  letI : Algebra D.localCoefficient R := D.localCoefficientAlgebra
  letI : Algebra (MvPolynomial σ D.localCoefficient) (MvPolynomial σ R) :=
    MvPolynomial.algebraMvPolynomial
  letI : Module (MvPolynomial σ D.localCoefficient) M :=
    Module.compHom M
      (algebraMap (MvPolynomial σ D.localCoefficient) (MvPolynomial σ R))
  letI : IsScalarTower (MvPolynomial σ D.localCoefficient)
      (MvPolynomial σ R) M :=
    IsScalarTower.of_compHom (MvPolynomial σ D.localCoefficient)
      (MvPolynomial σ R) M
  letI : IsScalarTower (MvPolynomial σ D.localCoefficient)
      (MvPolynomial σ R)
      ((MvPolynomial σ R) ⊗[MvPolynomial σ D.localCoefficient]
        D.localModelModule) :=
    IsScalarTower.of_algebraMap_smul fun a x => by
      induction x with
      | zero => rw [TensorProduct.smul_zero, TensorProduct.smul_zero]
      | add x y hx hy =>
        rw [TensorProduct.smul_add, TensorProduct.smul_add, hx, hy]
      | tmul s m => simp [Algebra.smul_def, TensorProduct.smul_tmul']
  exact polynomialBaseChangeLimitEquiv R σ D.localIndex D.localModelModule ≪≫ₗ
    (D.localBaseChangeEquiv.restrictScalars
      (MvPolynomial σ D.localCoefficient))

end Module.FinitePresentation.PolynomialModel
