module

public import StacksAndModuli.API.PolynomialModelPrimewiseFlatCoefficientStage

/-!
# Noetherian endpoint of flat polynomial coefficient spreading

`Module.FinitePresentation.PolynomialModel.FlatCoefficientModel` already contains the
finite relation matrix, coefficient-flatness, and polynomial base-change comparison produced
by the ring-theoretic spreading argument.  When the ambient base for its coefficient
subalgebra is noetherian, finite generation makes that coefficient ring noetherian.  This
file packages those derived facts as `NoetherianFlatPolynomialModel`.

The package is deliberately an *ungraded* polynomial-module model.  It is therefore the full
algebraic output of the existing `FlatCoefficientModel` API, but it does not by itself produce
either a descended quotient sheaf on projective space or a
`GradedModule.NoetherianCechModel`: those require compatible descent of the grading,
quotient map, and fibrewise Hilbert-polynomial/Čech-exactness data.

Main declarations:

* `NoetherianFlatPolynomialModel`;
* `FlatCoefficientModel.toNoetherianFlatPolynomialModel`;
* `exists_noetherianFlatPolynomialModel_of_flat_of_openFlatOverLoci`;
* `exists_noetherianFlatPolynomialModel_of_flat_of_regularSequence`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v w

namespace Module.FinitePresentation.PolynomialModel

open TensorProduct

/-- A noetherian coefficient model of a finitely presented polynomial module which is flat
over its coefficient ring and recovers the original module after polynomial base change.

This is the exact noetherian, ungraded module-theoretic payload of a
`FlatCoefficientModel` over an integer coefficient subalgebra. -/
structure NoetherianFlatPolynomialModel
    (A M : Type u) (sigma : Type v) [CommRing A] [AddCommGroup M]
    [Module (MvPolynomial sigma A) M] where
  /-- The noetherian coefficient ring. -/
  coefficientRing : Type u
  [coefficientRingCommRing : CommRing coefficientRing]
  [coefficientRingNoetherian : IsNoetherianRing coefficientRing]
  [coefficientAlgebra : Algebra coefficientRing A]
  /-- The descended module over the polynomial ring on the coefficient ring. -/
  model : Type max u v
  [modelAddCommGroup : AddCommGroup model]
  [modelModule : Module (MvPolynomial sigma coefficientRing) model]
  /-- The descended polynomial module is finitely presented. -/
  modelFinitePresentation :
    Module.FinitePresentation (MvPolynomial sigma coefficientRing) model
  /-- The descended polynomial module is flat over the coefficient ring. -/
  modelFlat :
    letI : Module coefficientRing model :=
      Module.compHom model
        (algebraMap coefficientRing (MvPolynomial sigma coefficientRing))
    Module.Flat coefficientRing model
  /-- Polynomial scalar extension recovers the original module. -/
  baseChangeEquiv :
    letI : Algebra (MvPolynomial sigma coefficientRing) (MvPolynomial sigma A) :=
      MvPolynomial.algebraMvPolynomial
    (MvPolynomial sigma A) ⊗[MvPolynomial sigma coefficientRing] model
      ≃ₗ[MvPolynomial sigma A] M

namespace FlatCoefficientModel

variable {R : Type w} {A M : Type u} {sigma : Type v}
variable [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M]
variable [Module (MvPolynomial sigma A) M]
variable {D : PolynomialModel A sigma M}

/-- A finitely generated subalgebra of a noetherian coefficient ring is noetherian. -/
theorem coefficientRing_isNoetherian (E : FlatCoefficientModel (R := R) D) :
    IsNoetherianRing E.coefficientRing := by
  letI : Algebra.FiniteType R E.coefficientRing :=
    (Subalgebra.fg_iff_finiteType E.coefficientRing).mp E.coefficientRing_fg
  exact Algebra.FiniteType.isNoetherianRing R E.coefficientRing

/-- Forgetting the chosen relation matrix but retaining all of its consequences turns a flat
coefficient model into a noetherian flat polynomial model. -/
noncomputable def toNoetherianFlatPolynomialModel
    (E : FlatCoefficientModel (R := R) D) :
    NoetherianFlatPolynomialModel A M sigma := by
  letI : IsNoetherianRing E.coefficientRing := E.coefficientRing_isNoetherian
  exact
    { coefficientRing := E.coefficientRing
      coefficientRingCommRing := inferInstance
      coefficientRingNoetherian := inferInstance
      coefficientAlgebra := inferInstance
      model := E.modelModule
      modelAddCommGroup := inferInstance
      modelModule := inferInstance
      modelFinitePresentation := E.modelModule_finitePresentation
      modelFlat := E.flat
      baseChangeEquiv := E.baseChangeEquiv }

end FlatCoefficientModel

/-- A flat coefficient model over a noetherian base already gives the corresponding
noetherian flat polynomial model. -/
theorem exists_noetherianFlatPolynomialModel_of_flatCoefficientModel
    {R : Type w} {A M : Type u} {sigma : Type v}
    [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M]
    [Module (MvPolynomial sigma A) M]
    (D : PolynomialModel A sigma M)
    (hE : Nonempty (FlatCoefficientModel (R := R) D)) :
    Nonempty (NoetherianFlatPolynomialModel A M sigma) := by
  obtain ⟨E⟩ := hE
  exact ⟨E.toNoetherianFlatPolynomialModel⟩

/-- Relative-flat-locus openness at the canonical coefficient stages supplies a noetherian
flat polynomial model for every finitely presented polynomial module which is coefficient-flat.

All pointwise localization, denominator clearing, persistence, finite extraction, and
local-to-global flatness are discharged by the existing coefficient-spreading API; the only
remaining hypothesis here is the 00RC openness input. -/
theorem exists_noetherianFlatPolynomialModel_of_flat_of_openFlatOverLoci
    {A sigma M : Type u} [CommRing A] [AddCommGroup M]
    [Module (MvPolynomial sigma A) M] [Finite sigma]
    (D : PolynomialModel A sigma M)
    (hflat :
      letI : Module A M :=
        Module.compHom M (algebraMap A (MvPolynomial sigma A))
      Module.Flat A M)
    (hopen : CanonicalStagesHaveOpenFlatOverLoci (R := ℤ) D) :
    Nonempty (NoetherianFlatPolynomialModel A M sigma) := by
  apply exists_noetherianFlatPolynomialModel_of_flatCoefficientModel (R := ℤ) D
  apply D.exists_flatCoefficientModel_of_stageFlatPoints_of_openFlatOverLoci
  · exact D.hasCoefficientStageFlatPointAtEveryPrime_of_flat hflat
  · exact hopen

/-- Relative regular-sequence openness after principal localization at every canonical
integer coefficient stage supplies a noetherian flat polynomial model for every finitely
presented polynomial module which is coefficient-flat. -/
theorem exists_noetherianFlatPolynomialModel_of_flat_of_regularSequence
    {A sigma M : Type u} [CommRing A] [AddCommGroup M]
    [Module (MvPolynomial sigma A) M] [Finite sigma]
    (D : PolynomialModel A sigma M)
    (hflat :
      letI : Module A M :=
        Module.compHom M (algebraMap A (MvPolynomial sigma A))
      Module.Flat A M)
    (hregular : ∀ i : CoefficientStage (R := ℤ) D,
      MvPolynomial.HasOpenRelativeFibreRegularSequenceLociAfterAway i.1 sigma) :
    Nonempty (NoetherianFlatPolynomialModel A M sigma) := by
  apply exists_noetherianFlatPolynomialModel_of_flatCoefficientModel (R := ℤ) D
  apply D.exists_flatCoefficientModel_of_stageFlatPoints_of_regularSequence
  · exact D.hasCoefficientStageFlatPointAtEveryPrime_of_flat hflat
  · exact hregular

end Module.FinitePresentation.PolynomialModel

end

end
