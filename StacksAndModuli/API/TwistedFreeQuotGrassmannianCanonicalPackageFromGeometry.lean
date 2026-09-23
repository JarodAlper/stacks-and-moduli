module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianReflectionEquivalence
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFlatteningFibreCanonical
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalCompatibility
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianCanonicalPackage

/-!
# Constructing the canonical Quot-to-Grassmannian package from geometry

This file assembles the reflection and finite-fibre constructions for the canonical
Quot-to-Grassmannian transformation.  After the fixed-degree inputs have constructed
the transformation, four geometric facts suffice: ambient reconstruction coherence,
surjectivity of the twisted kernel map, a flattening presentation for each reconstructed
Grassmannian family, and the strict universal quotient comparison on that flattening
locus.  The resulting package supplies the exact W6 immersion input used by the
representability and projectivity argument.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

variable {S : Scheme.{u}} {n r m q : ℕ} {l : ℤ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
  {σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- Relative global generation of the degree-`d` kernel in the literal form needed by
the Quot reconstruction argument: the pullback--pushforward evaluation map is
epimorphic. -/
def TwistedFreeQuotKernelIsGloballyGenerated
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d : ℕ) : Prop :=
  Epi ((Modules.pullbackPushforwardAdjunction
    (projectiveSpaceOverπ n T)).counit.app
      (kernel (Modules.tensorMapLeft p
        (projectiveSpaceOverTwist n T (d : ℤ)))))

/-- Relative global generation of the twisted kernel implies the kernel-map
epimorphism used by reconstruction.  The ambient monomial comparison is already an
unconditional isomorphism. -/
theorem quotGrassmannianTwistedKernelMap_epi_of_isGloballyGenerated
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ)
    {Q : (projectiveSpaceOver n T).Modules}
    (p : (∐ fun _ : ULift.{u} (Fin r) ↦ projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hgen : TwistedFreeQuotKernelIsGloballyGenerated n T l r p d) :
    Epi (quotGrassmannianTwistedKernelMap n T l r p d e he) := by
  letI : Epi ((Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOverπ n T)).counit.app
        (kernel (Modules.tensorMapLeft p
          (projectiveSpaceOverTwist n T (d : ℤ))))) := hgen
  exact quotGrassmannianTwistedKernelMap_epi_of_ambient_isIso_of_counit_epi
    n T l r p d e he

namespace TwistedFreeQuotGrassmannianCanonicalPackage

/-- The canonical fixed-degree inputs, together with the remaining geometric
reconstruction and flattening facts, construct the complete package used by the
Quot representability and projectivity endpoint. -/
noncomputable def ofCanonicalGeometry
    (I : TwistedFreeQuotGrassmannianCanonicalInputs
      n S l r P d e he m q σ)
    (hambient : ∀ X : Scheme.{u},
      TwistedFreeAmbientReconstructionCompatibility n X l r d e he)
    (hkernel : ∀ (T : Over S)
      (a : Modules.QuotientPullbackData
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l))
        (projectiveSpaceOverπ n S) T),
      a.HasFiberwiseHilbertPolynomial P →
        Epi (quotGrassmannianTwistedKernelMap n T.left l r
          (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
          d e he))
    (hflattening : ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m),
      Modules.ProjectiveFlatteningHasFiniteRankPresentation n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g) (P := P))
    (huniversal : ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m),
      Nonempty (GrassmannianPointUniversalFreeQuotientComparison
        I.natTransData T g (hflattening T g))) :
    TwistedFreeQuotGrassmannianCanonicalPackage
      n S l r P d e he m q σ where
  toTwistedFreeQuotGrassmannianCanonicalInputs := I
  reflectsQuotientEquivalence :=
    I.natTransData.reflectsQuotientEquivalence_of_reconstructedRelationPresentsKernel
      (fun T a hP ↦ by
        let p :=
          Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a
        letI : Epi (quotGrassmannianTwistedKernelMap n T.left l r p d e he) :=
          hkernel T a hP
        exact quotGrassmannianReconstructedRelationPresentsKernelOfTwistedKernelEpi
          n T.left l r p d e he (hambient T.left))
  finiteFibreLoci :=
    hasFiniteImmersionFibreLoci_ofCanonicalComparison
      I.natTransData hflattening huniversal hambient
        (fun _T _g Y x _a _h ↦
          hkernel (unop Y)
            (TwistedFreeQuotGrassmannianNatTransData.representative x)
            (TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial
              x))

/-- The canonical package constructor after the strict universal comparison has been
discharged by ambient reconstruction coherence.  Thus the actual geometric inputs are
the ambient comparison, eventual generation of the twisted kernel, and a finite-rank
presentation of the projective flattening condition. -/
noncomputable def ofCanonicalGeometryOfAmbient
    (I : TwistedFreeQuotGrassmannianCanonicalInputs
      n S l r P d e he m q σ)
    (hambient : ∀ X : Scheme.{u},
      TwistedFreeAmbientReconstructionCompatibility n X l r d e he)
    (hkernel : ∀ (T : Over S)
      (a : Modules.QuotientPullbackData
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l))
        (projectiveSpaceOverπ n S) T),
      a.HasFiberwiseHilbertPolynomial P →
        Epi (quotGrassmannianTwistedKernelMap n T.left l r
          (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
          d e he))
    (hflattening : ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m),
      Modules.ProjectiveFlatteningHasFiniteRankPresentation n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g) (P := P)) :
    TwistedFreeQuotGrassmannianCanonicalPackage
      n S l r P d e he m q σ :=
  ofCanonicalGeometry I hambient hkernel hflattening
    (fun T g ↦
      grassmannianPointUniversalFreeQuotientComparison_nonempty_of_ambient
        I.natTransData T g (hflattening T g) (hambient T.left))

/-- Fixed-degree constructor in the form produced by relative Serre generation: the
pullback--pushforward evaluation of the twisted kernel is epimorphic.  Ambient
reconstruction turns that evaluation statement into the kernel epimorphism used by
the reflection and fibre arguments. -/
noncomputable def ofCanonicalGeometryOfGlobalGeneration
    (I : TwistedFreeQuotGrassmannianCanonicalInputs
      n S l r P d e he m q σ)
    (hambient : ∀ X : Scheme.{u},
      TwistedFreeAmbientReconstructionCompatibility n X l r d e he)
    (hkernel : ∀ (T : Over S)
      (a : Modules.QuotientPullbackData
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l))
        (projectiveSpaceOverπ n S) T),
      a.HasFiberwiseHilbertPolynomial P →
        TwistedFreeQuotKernelIsGloballyGenerated n T.left l r
          (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
          d)
    (hflattening : ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m),
      Modules.ProjectiveFlatteningHasFiniteRankPresentation n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g) (P := P)) :
    TwistedFreeQuotGrassmannianCanonicalPackage
      n S l r P d e he m q σ :=
  ofCanonicalGeometryOfAmbient I hambient
    (fun T a hP ↦
      quotGrassmannianTwistedKernelMap_epi_of_isGloballyGenerated
        n T.left l r
          (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a)
          d e he (hkernel T a hP))
    hflattening

end TwistedFreeQuotGrassmannianCanonicalPackage

end AlgebraicGeometry.Scheme

end

end
