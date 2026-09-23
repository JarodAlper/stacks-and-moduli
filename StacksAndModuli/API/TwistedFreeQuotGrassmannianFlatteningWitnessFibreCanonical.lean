module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFlatteningFibreCanonical
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFlatteningWitnessFibre
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianReflectionEquivalence
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianCanonicalPackage

/-!
# Canonical Quot fibres from represented flattening loci

This file connects the geometric flattening-witness fibre construction to the
canonical Quot-to-Grassmannian transformation.  Ambient reconstruction coherence and
generation of the twisted kernel supply the compatible-family half exactly as in the
finite-rank presentation route; only the representation of the flattening condition is
changed.
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

/-- Canonical reconstruction and kernel generation complete a represented
flattening-witness fibre package once the universal point is known to map back to the
chosen Grassmannian point. -/
noncomputable def TwistedFreeQuotGrassmannianFlatteningWitnessFibreData.ofCanonicalCompatibility
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    (hflattening : Modules.ProjectiveFlatteningLocusWitness n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) P)
    (huniversal :
      let Z := hflattening.representative
      D.natTrans.app (op ((Over.map T.hom).obj Z))
        (grassmannianPointFlatteningUniversalQuotPointOfWitness
          (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
            (d := d) (e := e) (he := he) (σ := σ) T g hflattening) =
        (uliftYoneda.map (fibreLocusMap T Z) ≫ g).app
          (op ((Over.map T.hom).obj Z))
          (ULift.up (𝟙 ((Over.map T.hom).obj Z))))
    (hambient : ∀ X : Scheme.{u},
      TwistedFreeAmbientReconstructionCompatibility n X l r d e he)
    (hkernel : ∀ (Y : (Over S)ᵒᵖ)
      (x : (quotFunctorP
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l)) P).obj Y)
      (a : (uliftYoneda.{u + 1}.obj T).obj Y),
      D.natTrans.app Y x = g.app Y a →
        Epi (quotGrassmannianTwistedKernelMap n (unop Y).left l r
          (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
            (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x))
          d e he)) :
    TwistedFreeQuotGrassmannianFlatteningWitnessFibreData D T g where
  flattening := hflattening
  universalCompatibility := huniversal
  compatibleFlattening := by
    intro Y x a hxa
    let p :=
      Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
        (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x)
    letI : Epi (quotGrassmannianTwistedKernelMap n (unop Y).left l r
        p d e he) := hkernel Y x a hxa
    exact grassmannianPointCompatibleFlatteningOfCanonicalBaseChange
      D T g x a hxa (hambient T.left) (hambient (unop Y).left)
        (quotGrassmannianReconstructedRelationPresentsKernelOfTwistedKernelEpi
          n (unop Y).left l r p d e he (hambient (unop Y).left))

/-- Uniform represented flattening loci, their universal compatibility, and relative
kernel generation give all immersion fibre loci for the canonical transformation. -/
noncomputable def immersionFibreLociOfCanonicalWitnessCompatibility
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
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
      D.natTrans.app (op ((Over.map T.hom).obj Z))
        (grassmannianPointFlatteningUniversalQuotPointOfWitness
          (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
            (d := d) (e := e) (he := he) (σ := σ) T g H) =
        (uliftYoneda.map (fibreLocusMap T Z) ≫ g).app
          (op ((Over.map T.hom).obj Z))
          (ULift.up (𝟙 ((Over.map T.hom).obj Z))))
    (hambient : ∀ X : Scheme.{u},
      TwistedFreeAmbientReconstructionCompatibility n X l r d e he)
    (hkernel : ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
      (Y : (Over S)ᵒᵖ)
      (x : (quotFunctorP
        (Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l)) P).obj Y)
      (a : (uliftYoneda.{u + 1}.obj T).obj Y),
      D.natTrans.app Y x = g.app Y a →
        Epi (quotGrassmannianTwistedKernelMap n (unop Y).left l r
          (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
            (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x))
          d e he)) :
    ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m),
      ImmersionFibreLocus D.natTrans T g := by
  apply TwistedFreeQuotGrassmannianFlatteningWitnessFibreData.immersionFibreLoci
  intro T g
  exact ⟨TwistedFreeQuotGrassmannianFlatteningWitnessFibreData.ofCanonicalCompatibility
    D T g (hflattening T g) (huniversal T g) hambient (hkernel T g)⟩

/-- Canonical fixed-degree inputs close the W6 immersion predicate from represented
flattening loci.  Compared with the finite-presentation package, the only flattening
input here is the intrinsic geometric representative and its universal compatibility. -/
theorem twistedFreeQuotHasFreeGrassmannianImmersion_of_canonicalWitnessCompatibility
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
    TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P := by
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
  apply twistedFreeQuotHasFreeGrassmannianImmersion_of_relative
    n S l r P q m I.rank_le D.natTrans
  apply relative_over_isImmersion_of_fibreLoci D.natTrans
    (D.natTrans_pointwise_injective_of_reflectsQuotientEquivalence hreflect)
  apply immersionFibreLociOfCanonicalWitnessCompatibility
    D hflattening huniversal hambient
  intro T _g Y x _a _h
  exact hkernel (unop Y)
    (TwistedFreeQuotGrassmannianNatTransData.representative x)
    (TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial x)

end AlgebraicGeometry.Scheme

end

end
