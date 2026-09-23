module

public import StacksAndModuli.API.FiniteFreeComplexRelativeFibreResolution
public import StacksAndModuli.API.FlatCoefficientModelSpreading
public import StacksAndModuli.API.PolynomialMatrixRelativeFibreExactLocus
public import StacksAndModuli.API.RelativeFlatLocusExactness

/-!
# Primewise basic neighbourhoods in the canonical coefficient system

This file separates the two local ingredients used before the finite-extraction theorem in
`FlatCoefficientModelSpreading`.

For a polynomial presentation and a prime of the limit polynomial ring, the first ingredient
is a canonical finitely generated coefficient stage at whose contracted prime the descended
cokernel is coefficient-flat.  The second is the basic-neighbourhood form of openness of the
relative flat locus at every canonical stage.  Together they produce the one-stage primewise
flat basic neighbourhood required by the spreading assembly.

The remaining openness input is also expressed in the concrete form supplied by 00RB: for
each stage relation map `g`, the relative-fibre exactness locus of
`(ker g).subtype` followed by `g` is open.  Over a noetherian base with finitely many
polynomial variables, `CanonicalStagesHaveOpenRelativeFibreKernelExactLoci.haveOpenFlatOverLoci`
identifies its consequence with the stagewise relative flat-locus input above.

The bounded finite-free determinantal theorem, the anchored partial-resolution compiler,
and the local-to-global argument are assembled in
`Matrix.hasOpenRelativeFibreExactLocus_kernel_toLin_mvPolynomial_of_regularSequence`.
Consequently, the sole remaining input at this layer is relative regular-sequence openness
after principal localization (Stacks Project tag 00RA).
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe uR u v

namespace Module.FinitePresentation.PolynomialModel

variable {R : Type uR} {A M : Type u} {sigma : Type v}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module (MvPolynomial sigma A) M]

/-- The contraction of a prime of the limit polynomial ring to one canonical coefficient
stage. -/
noncomputable def coefficientStagePrime (D : PolynomialModel A sigma M)
    (q : PrimeSpectrum (MvPolynomial sigma A))
    (i : CoefficientStage (R := R) D) :
    PrimeSpectrum (MvPolynomial sigma i.1) :=
  q.comap (coefficientStageToLimit D i)

/-- Every prime of the limit polynomial ring is coefficient-flat at its contraction to
some canonical finitely generated coefficient stage. -/
def HasCoefficientStageFlatPointAtEveryPrime
    (D : PolynomialModel A sigma M) : Prop :=
  ∀ q : PrimeSpectrum (MvPolynomial sigma A),
    ∃ i : CoefficientStage (R := R) D,
      Module.Flat i.1
        (TensorProduct (MvPolynomial sigma i.1)
          (Localization.AtPrime (coefficientStagePrime D q i).asIdeal)
          (polynomialMatrixCokernel (coefficientStageRelation D i)))

/-- Every canonical coefficient stage has basic flat neighbourhoods at all points of its
relative flat locus.  This is the basic-open form of openness used by the spreading
argument. -/
def CanonicalStagesHaveFlatBasicNeighborhoods
    (D : PolynomialModel A sigma M) : Prop :=
  ∀ i : CoefficientStage (R := R) D,
    Module.FinitePresentation.HasFlatBasicNeighborhoods
      (R := i.1) (S := MvPolynomial sigma i.1)
      (M := polynomialMatrixCokernel (coefficientStageRelation D i))

/-- Every canonical coefficient stage has an open relative flat locus.  Stacks Project tag
00RC supplies this property because the polynomial algebra and its matrix cokernel are both
finitely presented. -/
def CanonicalStagesHaveOpenFlatOverLoci
    (D : PolynomialModel A sigma M) : Prop :=
  ∀ i : CoefficientStage (R := R) D,
    Module.FinitePresentation.HasOpenFlatOverLocus
      (R := i.1) (S := MvPolynomial sigma i.1)
      (M := polynomialMatrixCokernel (coefficientStageRelation D i))

/-- Every canonical coefficient-stage relation has open relative-fibre exactness locus for
the canonical kernel inclusion followed by its relation map.  This is the concrete 00RB
input whose flat-locus consequence is used by coefficient spreading. -/
def CanonicalStagesHaveOpenRelativeFibreKernelExactLoci
    (D : PolynomialModel A sigma M) : Prop :=
  ∀ i : CoefficientStage (R := R) D,
    let S := MvPolynomial sigma i.1
    let commRingS : CommRing S := inferInstance
    letI : CommRing S := commRingS
    letI : CommSemiring S := commRingS.toCommSemiring
    let g : (Fin D.relations → S) →ₗ[S] (Fin D.generators → S) :=
      Matrix.toLin' (coefficientStageRelation D i)
    LinearMap.HasOpenRelativeFibreExactLocus
      (R := i.1) (LinearMap.ker g).subtype g

/-- Relative regular-sequence openness after principal localization at every canonical
coefficient stage gives the exactness-locus input required by coefficient spreading. -/
theorem canonicalStagesHaveOpenRelativeFibreKernelExactLoci_of_regularSequence
    [IsNoetherianRing R] [Finite sigma]
    (D : PolynomialModel A sigma M)
    (hregular : ∀ i : CoefficientStage (R := R) D,
      MvPolynomial.HasOpenRelativeFibreRegularSequenceLociAfterAway i.1 sigma) :
    CanonicalStagesHaveOpenRelativeFibreKernelExactLoci (R := R) D := by
  intro i
  letI : Algebra.FiniteType R i.1 :=
    (Subalgebra.fg_iff_finiteType i.1).mp i.2.1
  letI : IsNoetherianRing i.1 :=
    Algebra.FiniteType.isNoetherianRing R i.1
  exact
    Matrix.hasOpenRelativeFibreExactLocus_kernel_toLin_mvPolynomial_of_regularSequence
      (coefficientStageRelation D i) (hregular i)

/-- Open relative-fibre exactness loci for the canonical kernel presentations give open
relative flat loci for all canonical coefficient-stage cokernels. -/
theorem CanonicalStagesHaveOpenRelativeFibreKernelExactLoci.haveOpenFlatOverLoci
    [IsNoetherianRing R] [Finite sigma]
    (D : PolynomialModel A sigma M)
    (hopen : CanonicalStagesHaveOpenRelativeFibreKernelExactLoci (R := R) D) :
    CanonicalStagesHaveOpenFlatOverLoci (R := R) D := by
  intro i
  letI : Algebra.FiniteType R i.1 :=
    (Subalgebra.fg_iff_finiteType i.1).mp i.2.1
  letI : IsNoetherianRing i.1 :=
    Algebra.FiniteType.isNoetherianRing R i.1
  let S := MvPolynomial sigma i.1
  let commRingS : CommRing S := inferInstance
  letI : CommRing S := commRingS
  letI : CommSemiring S := commRingS.toCommSemiring
  letI : Semiring S := commRingS.toCommSemiring.toSemiring
  let g : (Fin D.relations → S) →ₗ[S] (Fin D.generators → S) :=
    Matrix.toLin' (coefficientStageRelation D i)
  letI : Module.Free S S := Module.Free.self S
  letI : Module.Free S (Fin D.generators → S) :=
    Module.Free.function (Fin D.generators) S S
  letI : Module.Projective S (Fin D.generators → S) :=
    Module.Projective.of_free
  exact LinearMap.HasOpenRelativeFibreExactLocus.hasOpenFlatOverLocus_of_exact
    (R := i.1) (g := g) (hopen i)
    (LinearMap.exact_subtype_ker_map g)

/-- Open relative flat loci at the canonical stages give the basic flat neighbourhoods used
by the coefficient-spreading argument. -/
theorem CanonicalStagesHaveOpenFlatOverLoci.haveFlatBasicNeighborhoods
    (D : PolynomialModel A sigma M)
    (hopen : CanonicalStagesHaveOpenFlatOverLoci (R := R) D) :
    CanonicalStagesHaveFlatBasicNeighborhoods (R := R) D :=
  fun i ↦ (hopen i).hasFlatBasicNeighborhoods

/-- A flat contracted point and basic-neighbourhood openness at the corresponding canonical
stage produce a one-stage flat basic neighbourhood avoiding the original limit prime. -/
theorem HasCoefficientStageFlatPointAtEveryPrime.toPrimewiseFlatCoefficientNeighborhoods
    (D : PolynomialModel A sigma M)
    (hpoint : HasCoefficientStageFlatPointAtEveryPrime (R := R) D)
    (hopen : CanonicalStagesHaveFlatBasicNeighborhoods (R := R) D) :
    HasPrimewiseFlatCoefficientNeighborhoods (R := R) D := by
  intro q
  obtain ⟨i, hi⟩ := hpoint q
  let qi := coefficientStagePrime D q i
  obtain ⟨f, hf, hflat⟩ := hopen i qi hi
  refine ⟨i, f, ?_, hflat⟩
  exact hf

/-- Canonical-stage pointwise flatness and basic-neighbourhood openness produce a globally
flat coefficient model.  Persistence under coefficient extension is automatic. -/
theorem exists_flatCoefficientModel_of_stageFlatPoints
    (D : PolynomialModel A sigma M)
    (hpoint : HasCoefficientStageFlatPointAtEveryPrime (R := R) D)
    (hopen : CanonicalStagesHaveFlatBasicNeighborhoods (R := R) D) :
    Nonempty (FlatCoefficientModel (R := R) D) :=
  (hpoint.toPrimewiseFlatCoefficientNeighborhoods D hopen).exists_flatCoefficientModel D

/-- Canonical-stage pointwise flatness and openness of every canonical relative flat locus
produce a globally flat coefficient model. -/
theorem exists_flatCoefficientModel_of_stageFlatPoints_of_openFlatOverLoci
    (D : PolynomialModel A sigma M)
    (hpoint : HasCoefficientStageFlatPointAtEveryPrime (R := R) D)
    (hopen : CanonicalStagesHaveOpenFlatOverLoci (R := R) D) :
    Nonempty (FlatCoefficientModel (R := R) D) :=
  D.exists_flatCoefficientModel_of_stageFlatPoints hpoint
    (hopen.haveFlatBasicNeighborhoods D)

/-- Canonical-stage pointwise flatness together with open relative-fibre exactness loci for
the canonical kernel presentations produces a globally flat coefficient model. -/
theorem exists_flatCoefficientModel_of_stageFlatPoints_of_openRelativeFibreKernelExactLoci
    [IsNoetherianRing R] [Finite sigma]
    (D : PolynomialModel A sigma M)
    (hpoint : HasCoefficientStageFlatPointAtEveryPrime (R := R) D)
    (hopen : CanonicalStagesHaveOpenRelativeFibreKernelExactLoci (R := R) D) :
    Nonempty (FlatCoefficientModel (R := R) D) :=
  D.exists_flatCoefficientModel_of_stageFlatPoints_of_openFlatOverLoci hpoint
    (hopen.haveOpenFlatOverLoci D)

/-- Canonical-stage pointwise flatness together with relative regular-sequence openness
after principal localization produces a globally flat coefficient model. -/
theorem exists_flatCoefficientModel_of_stageFlatPoints_of_regularSequence
    [IsNoetherianRing R] [Finite sigma]
    (D : PolynomialModel A sigma M)
    (hpoint : HasCoefficientStageFlatPointAtEveryPrime (R := R) D)
    (hregular : ∀ i : CoefficientStage (R := R) D,
      MvPolynomial.HasOpenRelativeFibreRegularSequenceLociAfterAway i.1 sigma) :
    Nonempty (FlatCoefficientModel (R := R) D) :=
  D.exists_flatCoefficientModel_of_stageFlatPoints_of_openRelativeFibreKernelExactLoci
    hpoint
    (canonicalStagesHaveOpenRelativeFibreKernelExactLoci_of_regularSequence D hregular)

end Module.FinitePresentation.PolynomialModel

end

end
