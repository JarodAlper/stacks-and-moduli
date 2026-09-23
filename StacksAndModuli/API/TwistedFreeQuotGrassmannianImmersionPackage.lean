module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianCanonicalPackage
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFlatteningWitnessFibreCanonical
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalFlatteningLocus

/-!
# The intrinsic Quot-to-Grassmannian immersion package

The projectivity and determinant arguments consume the canonical fixed-degree inputs
and the conclusion that their natural transformation is relatively representable by
immersions.  They do not depend on how its fibres were presented.  This file records
that minimal interface, allowing either a finite list of rank strata or a directly
represented projective flattening locus to supply the immersion.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The minimal fixed-degree package used by the Quot projectivity and Plucker
arguments: canonical inputs together with relative representability by immersions. -/
structure TwistedFreeQuotGrassmannianImmersionPackage
    (n : ℕ) (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)) (m q : ℕ)
    (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n))
    : Type (u + 1)
    extends TwistedFreeQuotGrassmannianCanonicalInputs
      n S l r P d e he m q σ where
  /-- The intrinsic canonical transformation is relatively representable by
  immersions. -/
  relativeIsImmersion :
    MorphismProperty.relative uliftYoneda.{u + 1}
      (MorphismProperty.over
        (@IsImmersion : MorphismProperty Scheme.{u}))
      toTwistedFreeQuotGrassmannianCanonicalInputs.natTransData.natTrans

namespace TwistedFreeQuotGrassmannianImmersionPackage

variable {n : ℕ} {S : Scheme.{u}} {l : ℤ} {r : ℕ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)} {m q : ℕ}
  {σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- The intrinsic natural-transformation data carried by the package. -/
noncomputable def natTransData
    (C : TwistedFreeQuotGrassmannianImmersionPackage
      n S l r P d e he m q σ) :
    TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ :=
  C.toTwistedFreeQuotGrassmannianCanonicalInputs.natTransData

/-- The immersion package closes the exact twisted-free W6 predicate. -/
theorem w6
    (C : TwistedFreeQuotGrassmannianImmersionPackage
      n S l r P d e he m q σ) :
    TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P :=
  twistedFreeQuotHasFreeGrassmannianImmersion_of_relative
    n S l r P q m C.rank_le C.natTransData.natTrans C.relativeIsImmersion

/-- The determinant of the normalized universal fixed-degree pushforward is the
pullback of the Plucker line bundle and hence relatively very ample. -/
theorem determinant_isRelativelyVeryAmple
    (C : TwistedFreeQuotGrassmannianImmersionPackage
      n S l r P d e he m q σ)
    {Q : Over S}
    (h : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).RepresentableBy Q) :
    IsRelativelyVeryAmple Q.hom
      (Modules.exteriorPower
        (twistedFreeQuotientTwistPushforward n S l r
          (h.homEquiv (CategoryStruct.id Q)).1.out d) q) :=
  C.natTransData.isRelativelyVeryAmple_exteriorPower_twistedFreeUniversalPushforward
    C.relativeIsImmersion h

/-- Forget the chosen finite-intersection presentation in a canonical package. -/
noncomputable def ofCanonicalPackage
    (C : TwistedFreeQuotGrassmannianCanonicalPackage
      n S l r P d e he m q σ) :
    TwistedFreeQuotGrassmannianImmersionPackage
      n S l r P d e he m q σ where
  toTwistedFreeQuotGrassmannianCanonicalInputs :=
    C.toTwistedFreeQuotGrassmannianCanonicalInputs
  relativeIsImmersion := C.relative_isImmersion

/-- Construct the minimal package directly from represented flattening loci and
canonical reconstruction data. -/
noncomputable def ofCanonicalWitnessCompatibility
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
      Modules.ProjectiveFlatteningLocusWitness n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g) P)
    (huniversal : ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m),
      let H := hflattening T g
      let Z := H.representative
      I.natTransData.natTrans.app (op ((Over.map T.hom).obj Z))
        (grassmannianPointFlatteningUniversalQuotPointOfWitness
          (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
            (d := d) (e := e) (he := he) (σ := σ) T g H) =
        (uliftYoneda.map (fibreLocusMap T Z) ≫ g).app
          (op ((Over.map T.hom).obj Z))
          (ULift.up (𝟙 ((Over.map T.hom).obj Z)))) :
    TwistedFreeQuotGrassmannianImmersionPackage
      n S l r P d e he m q σ where
  toTwistedFreeQuotGrassmannianCanonicalInputs := I
  relativeIsImmersion := by
    let D := I.natTransData
    have hreflect : D.ReflectsQuotientEquivalence :=
      D.reflectsQuotientEquivalence_of_reconstructedRelationPresentsKernel
        (fun T a hP ↦ by
          let p :=
            Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver T a
          letI : Epi (quotGrassmannianTwistedKernelMap n T.left l r p d e he) :=
            hkernel T a hP
          exact quotGrassmannianReconstructedRelationPresentsKernelOfTwistedKernelEpi
            n T.left l r p d e he (hambient T.left))
    apply relative_over_isImmersion_of_fibreLoci D.natTrans
      (D.natTrans_pointwise_injective_of_reflectsQuotientEquivalence hreflect)
    apply immersionFibreLociOfCanonicalWitnessCompatibility
      D hflattening huniversal hambient
    intro T _g Y x _a _h
    exact hkernel (unop Y)
      (TwistedFreeQuotGrassmannianNatTransData.representative x)
      (TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial x)

/-- One represented flattening locus on the universal free-Grassmannian
reconstruction constructs the complete intrinsic immersion package. -/
noncomputable def ofUniversalFlatteningLocus
    (I : TwistedFreeQuotGrassmannianCanonicalInputs
      n S l r P d e he m q σ)
    (H : Modules.ProjectiveFlatteningLocusWitness n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ)
          (grassmannianOverRepresentation S q m)
          (freeGrassmannianUniversalPoint S q m)) P)
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
          d e he)) :
    TwistedFreeQuotGrassmannianImmersionPackage
      n S l r P d e he m q σ :=
  ofCanonicalWitnessCompatibility I hambient hkernel
    (grassmannianPointFlatteningLocusWitnessOfUniversal H hambient)
    (grassmannianPointUniversalCompatibilityOfUniversalFlatteningLocus
      I.natTransData H hambient)

end TwistedFreeQuotGrassmannianImmersionPackage

end AlgebraicGeometry.Scheme

end

end
