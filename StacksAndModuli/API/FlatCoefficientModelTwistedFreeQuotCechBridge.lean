module

public import StacksAndModuli.API.FlatCoefficientModelGradedCechBridge
public import StacksAndModuli.API.TwistedFreeQuotNoetherianCechModel

/-!
# Flat coefficient models as affine Quot Čech models

This file applies the algebraic flat-coefficient-model bridge chart by chart to the
scheme-level input used by the arbitrary-base Quot projectivity argument.  The predicate
`HasAffineFlatCoefficientGradedCechRealization` asks for exactly the extra data not retained
by an ordinary polynomial-module model: on each affine chart, its descended module carries
a compatible grading and the required field-fibre positive Čech vanishing.

The main theorem turns these chartwise algebraic witnesses into
`HasAffineNoetherianTwistedFreeQuotCechModel`.  No separate noetherianity, finite-generation,
or Čech-flatness assumption is required: those are supplied by the flat coefficient model
and the graded realization bridge.

Main declaration:

* `HasAffineFlatCoefficientGradedCechRealization.toNoetherianCechModel`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Chartwise flat polynomial coefficient models whose ordinary descended modules admit
the grading, base-change comparison, and field-fibre vanishing needed by the Quot Čech model.

The polynomial presentation and flat coefficient model are existential because neither is
canonical.  Their noetherian and flat consequences are derived by the algebraic bridge. -/
def HasAffineFlatCoefficientGradedCechRealization
    (n r : ℕ) (l : ℤ) {T : Scheme.{u}}
    (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ) : Prop :=
  ∀ U : T.affineOpens,
    let A := Γ(U.1.toScheme, ⊤)
    let gU : Spec (CommRingCat.of A) ⟶ T := U.1.toScheme.isoSpec.inv ≫ U.1.ι
    let mU := Scheme.projectiveSpaceOverMap n gU
    let qU := (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l gU).inv ≫
      (Scheme.Modules.pullback mU).map q
    let pU := (Scheme.Modules.pullback (projectiveSpaceOverSpecIso n A).inv).map qU
    let M := Proj.kernelQuotientModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
      (projSpecπ n A) (stdVars n A) pU
    ∃ D : _root_.Module.FinitePresentation.PolynomialModel
        A (Fin (n + 1)) M.Total,
      ∃ E : _root_.Module.FinitePresentation.PolynomialModel.FlatCoefficientModel
          (R := ℤ) D,
        E.toNoetherianFlatPolynomialModel.HasGradedCechRealization M (d : ℤ)

/-- Chartwise algebraic flat coefficient models with compatible graded realizations supply
the affine noetherian Čech-model hypothesis used by Quot projectivity. -/
theorem HasAffineFlatCoefficientGradedCechRealization.toNoetherianCechModel
    (n r : ℕ) (l : ℤ) {T : Scheme.{u}}
    (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q) (d : ℕ)
    (H : HasAffineFlatCoefficientGradedCechRealization n r l Q q d) :
    HasAffineNoetherianTwistedFreeQuotCechModel n r l Q q d := by
  intro U
  obtain ⟨D, E, hE⟩ := H U
  obtain ⟨N⟩ := E.toNoetherianCechModel_of_hasGradedCechRealization hE
  exact ⟨N.toCechComplexModel⟩

end AlgebraicGeometry.ProjectiveSpace

end

end
