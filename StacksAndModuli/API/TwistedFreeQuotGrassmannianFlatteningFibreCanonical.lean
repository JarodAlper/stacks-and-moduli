module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFibreReflectionCanonical
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianAmbientCoherence

/-!
# Canonical inputs for Quot-to-Grassmannian flattening fibres

Base change and finite-free reindexing in the compatible-family part of the
Quot-to-Grassmannian fibre are canonical.  This file also isolates the exact
fixed-degree comparison needed on the universal flattening family: its strict
monomial quotient must be equivalent to the pullback of the original Grassmannian
quotient.  Once that target isomorphism and its quotient-map triangle are supplied,
the universal compatibility equality is formal.
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

/-- The strict quotient selected by the intrinsic Quot-to-Grassmannian map for the
universal reconstructed Quot point on a projective flattening locus. -/
noncomputable def grassmannianPointFlatteningUniversalFreeQuotient
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    (h : Modules.ProjectiveFlatteningHasFiniteRankPresentation n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P)) :
    Modules.FreeQuotient q (ULift.{u} (Fin m))
      ((Over.map T.hom).obj
        (Modules.projectiveFlatteningRepresentative n
          (grassmannianPointReconstructedQuotient
            (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
              (he := he) (σ := σ) T g) (P := P) h)).left :=
  D.representativeFreeQuotient
    (grassmannianPointFlatteningUniversalQuotPoint
      (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
        (d := d) (e := e) (he := he) (σ := σ) T g h)

/-- The strict quotient classifying the given Grassmannian point, pulled back to the
universal projective flattening locus. -/
noncomputable def grassmannianPointFreeQuotientPullbackToFlattening
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    (h : Modules.ProjectiveFlatteningHasFiniteRankPresentation n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P)) :
    Modules.FreeQuotient q (ULift.{u} (Fin m))
      (Modules.projectiveFlatteningRepresentative n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g) (P := P) h).left :=
  (grassmannianPointFreeQuotient (q := q) T g).pullback
    (Modules.projectiveFlatteningRepresentative n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P) h).hom

/-- The remaining fixed-degree comparison on the universal flattening family.

Its target isomorphism identifies the degree-`d` quotient produced by applying the
intrinsic transformation to the reconstructed family with the original pulled-back
Grassmannian quotient, and `π_comp` records the required generator triangle. -/
structure GrassmannianPointUniversalFreeQuotientComparison
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    (h : Modules.ProjectiveFlatteningHasFiniteRankPresentation n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P)) : Type (u + 1) where
  /-- Isomorphism between the two strict quotient targets. -/
  targetIso :
    (grassmannianPointFlatteningUniversalFreeQuotient D T g h).Q ≅
      (grassmannianPointFreeQuotientPullbackToFlattening T g h).Q
  /-- The target isomorphism respects the maps from the canonical finite free sheaf. -/
  π_comp :
    (grassmannianPointFlatteningUniversalFreeQuotient D T g h).π ≫
        targetIso.hom =
      (grassmannianPointFreeQuotientPullbackToFlattening T g h).π

/-- A strict fixed-degree comparison gives the universal compatibility field of the
projective-flattening fibre package. -/
lemma GrassmannianPointUniversalFreeQuotientComparison.universalCompatibility
    {D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ}
    {T : Over S}
    {g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m}
    {h : Modules.ProjectiveFlatteningHasFiniteRankPresentation n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P)}
    (C : GrassmannianPointUniversalFreeQuotientComparison D T g h) :
    let Z := Modules.projectiveFlatteningRepresentative n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P) h
    D.natTrans.app (op ((Over.map T.hom).obj Z))
      (grassmannianPointFlatteningUniversalQuotPoint
        (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
          (d := d) (e := e) (he := he) (σ := σ) T g h) =
      (uliftYoneda.map (fibreLocusMap T Z) ≫ g).app
        (op ((Over.map T.hom).obj Z))
        (ULift.up (𝟙 ((Over.map T.hom).obj Z))) := by
  let Z := Modules.projectiveFlatteningRepresentative n
    (grassmannianPointReconstructedQuotient
      (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
        (he := he) (σ := σ) T g) (P := P) h
  let x := grassmannianPointFlatteningUniversalQuotPoint
    (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
      (d := d) (e := e) (he := he) (σ := σ) T g h
  let q₁ := grassmannianPointFlatteningUniversalFreeQuotient D T g h
  let q₂ := grassmannianPointFreeQuotientPullbackToFlattening T g h
  have hq : q₁.kernelPoint = q₂.kernelPoint :=
    Modules.FreeQuotient.kernelPoint_eq_of_r ⟨C.targetIso, C.π_comp⟩
  change ULift.up q₁.kernelPoint = _
  apply ULift.ext
  change q₁.kernelPoint =
    (g.app (op ((Over.map T.hom).obj Z))
      (ULift.up (fibreLocusMap T Z))).down
  rw [hq]
  exact grassmannianPointFreeQuotient_pullback_kernelPoint T g
    (ULift.up (fibreLocusMap T Z))

/-- The ambient multiplication/cancellation coherence used by twisted-free
reconstruction on one base scheme. -/
def TwistedFreeAmbientReconstructionCompatibility
    (n : ℕ) (X : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) : Prop :=
  (freeTensorTwistIso n X
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
      twistedFreeMonomialHom n X l r d e he =
    Modules.tensorMapLeft
        (twistedFreeMonomialMap n X l r d e he)
        (projectiveSpaceOverTwist n X (-(d : ℤ))) ≫
      (projectiveSpaceOverTwistModule_cancelIso_nat n X
        (∐ fun _ : ULift.{u} (Fin r) ↦
          projectiveSpaceOverTwist n X (-l)) d).hom

/-- The ambient multiplication/cancellation compatibility required by twisted-free
reconstruction is canonical. -/
theorem twistedFreeAmbientReconstructionCompatibility
    (n : ℕ) (X : Scheme.{u}) (l : ℤ) (r d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) :
    TwistedFreeAmbientReconstructionCompatibility n X l r d e he := by
  exact twistedFreeMonomialHom_eq_tensorMapLeft_cancel_of_single
    n X l r d e he (fun i ↦
      twistMonomialMulHom_eq_tensor_twistedSection_cancel
        n X l d e he i)

/-- Construct the complete flattening-fibre package from the two remaining geometric
inputs: the universal fixed-degree quotient comparison and relative global generation
of the degree-`d` quotient kernel for compatible Quot families. -/
noncomputable def TwistedFreeQuotGrassmannianFlatteningFibreData.ofCanonicalComparison
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    (hflattening : Modules.ProjectiveFlatteningHasFiniteRankPresentation n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P))
    (huniversal : GrassmannianPointUniversalFreeQuotientComparison
      D T g hflattening)
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
    TwistedFreeQuotGrassmannianFlatteningFibreData D T g where
  flattening := hflattening
  universalCompatibility := huniversal.universalCompatibility
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

/-- Uniform canonical comparison and kernel-generation inputs give all finite immersed
fibre loci for the intrinsic Quot-to-Grassmannian transformation. -/
theorem hasFiniteImmersionFibreLoci_ofCanonicalComparison
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (hflattening : ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m),
      Modules.ProjectiveFlatteningHasFiniteRankPresentation n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g) (P := P))
    (huniversal : ∀ (T : Over S)
      (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m),
      Nonempty (GrassmannianPointUniversalFreeQuotientComparison
        D T g (hflattening T g)))
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
    HasFiniteImmersionFibreLoci D.natTrans := by
  apply TwistedFreeQuotGrassmannianFlatteningFibreData.hasFiniteImmersionFibreLoci
  intro T g
  exact ⟨TwistedFreeQuotGrassmannianFlatteningFibreData.ofCanonicalComparison
    D T g (hflattening T g) (Classical.choice (huniversal T g))
      hambient (hkernel T g)⟩

end AlgebraicGeometry.Scheme

end

end
