module

public import StacksAndModuli.API.FlatCoefficientModelNoetherian
public import StacksAndModuli.API.PolynomialAwayRelativeFibreRegularSequenceLocus

/-!
# Unconditional noetherian flat polynomial coefficient models

Relative-fibre regular-sequence loci are open after every principal localization of a
finite-variable polynomial algebra.  Consequently, the regular-sequence hypothesis in
the coefficient-spreading construction is automatic: every finitely presented polynomial
module which is flat over its coefficient ring admits a noetherian flat polynomial model
over a finitely generated integer coefficient subalgebra.

Main declaration:

* `Module.FinitePresentation.PolynomialModel.exists_flatCoefficientModel_of_flat`;
* `Module.FinitePresentation.PolynomialModel.exists_noetherianFlatPolynomialModel_of_flat`.
-/

@[expose] public section

noncomputable section

universe u v

namespace Module.FinitePresentation.PolynomialModel

/-- Every coefficient-flat finitely presented module over a polynomial ring in finitely
many variables admits a flat polynomial coefficient model.  This version retains the
chosen relation matrix needed by homogeneous-presentation consumers. -/
theorem exists_flatCoefficientModel_of_flat
    {A M : Type u} {sigma : Type v} [CommRing A] [AddCommGroup M]
    [Module (MvPolynomial sigma A) M] [Finite sigma]
    (D : PolynomialModel A sigma M)
    (hflat :
      letI : Module A M :=
        Module.compHom M (algebraMap A (MvPolynomial sigma A))
      Module.Flat A M) :
    Nonempty (FlatCoefficientModel (R := ℤ) D) := by
  apply D.exists_flatCoefficientModel_of_stageFlatPoints_of_regularSequence
  · exact D.hasCoefficientStageFlatPointAtEveryPrime_of_flat hflat
  · intro i
    exact MvPolynomial.hasOpenRelativeFibreRegularSequenceLociAfterAway i.1 sigma

/-- Every coefficient-flat finitely presented module over a polynomial ring in finitely
many variables admits a noetherian flat polynomial coefficient model. -/
theorem exists_noetherianFlatPolynomialModel_of_flat
    {A M : Type u} {sigma : Type v} [CommRing A] [AddCommGroup M]
    [Module (MvPolynomial sigma A) M] [Finite sigma]
    (D : PolynomialModel A sigma M)
    (hflat :
      letI : Module A M :=
        Module.compHom M (algebraMap A (MvPolynomial sigma A))
      Module.Flat A M) :
    Nonempty (NoetherianFlatPolynomialModel A M sigma) := by
  apply exists_noetherianFlatPolynomialModel_of_flatCoefficientModel (R := ℤ) D
  exact exists_flatCoefficientModel_of_flat D hflat

end Module.FinitePresentation.PolynomialModel

end

end
