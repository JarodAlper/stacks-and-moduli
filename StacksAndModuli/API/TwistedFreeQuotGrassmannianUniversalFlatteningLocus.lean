module

public import StacksAndModuli.API.ProjectiveFlatteningLocusBaseChange
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFlatteningWitnessFibreCanonical
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalCompatibility

/-!
# Universal flattening locus for twisted-free Grassmannian reconstruction

The reconstructed quotient attached to an arbitrary point of the free
Grassmannian is the pullback of the reconstructed quotient attached to the
universal point, up to the harmless choice of a strict representative of the
finite-free quotient.  Consequently, one represented immersed flattening
locus on the Grassmannian transports to every Grassmannian-valued test point.

The construction has three layers:

* `freeGrassmannianUniversalPoint` and `freeGrassmannianClassifyingHom` package
  the canonical universal point and the classifying morphism;
* `freeGrassmannianUniversalReconstructedQuotientPullbackIso` compares the
  universal reconstruction after pullback with the reconstruction at a test
  point;
* `grassmannianPointFlatteningLocusWitnessOfUniversal` transports one
  `ProjectiveFlatteningLocusWitness` on the universal reconstruction to every
  test point;
* `grassmannianPointUniversalCompatibilityOfUniversalFlatteningLocus`
  supplies the corresponding universal compatibility equality;
* `twistedFreeQuotHasFreeGrassmannianImmersion_of_universalFlatteningLocus`
  packages these constructions into the canonical W6 endpoint.
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

open Modules.QuotientPullbackData

variable {S : Scheme.{u}} {n r m q : ℕ} {l : ℤ} {P : Polynomial ℚ}
  {d e : ℕ} {he : (d : ℤ) - l = (e : ℤ)}
  {σ : ULift.{u} (Fin m) ≃
    ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- The canonical universal point of the free Grassmannian, expressed as a
natural transformation from the represented functor. -/
noncomputable def freeGrassmannianUniversalPoint
    (S : Scheme.{u}) (q m : ℕ) :
    uliftYoneda.{u + 1}.obj
        (grassmannianOverRepresentation S q m) ⟶
      Modules.grassmannianFunctorOver S q m :=
  uliftYonedaEquiv.symm
    ((grassmannianFunctorOverRepresentableBy S q m).homEquiv
      (𝟙 (grassmannianOverRepresentation S q m)))

/-- The morphism to the free Grassmannian classifying a Grassmannian-valued
point on a test scheme. -/
noncomputable def freeGrassmannianClassifyingHom
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m) :
    T ⟶ grassmannianOverRepresentation S q m :=
  (grassmannianFunctorOverRepresentableBy S q m).homEquiv.symm
    (uliftYonedaEquiv g)

/-- Evaluating the universal point on its classifying morphism recovers the
classified Grassmannian point. -/
lemma freeGrassmannianUniversalPoint_app_classifyingHom
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m) :
    (freeGrassmannianUniversalPoint S q m).app
        (op T) (ULift.up (freeGrassmannianClassifyingHom T g)) =
      uliftYonedaEquiv g := by
  simp only [freeGrassmannianUniversalPoint,
    uliftYonedaEquiv_symm_apply_app]
  change (Modules.grassmannianFunctorOver S q m).map
      (freeGrassmannianClassifyingHom T g).op
      ((grassmannianFunctorOverRepresentableBy S q m).homEquiv
        (𝟙 (grassmannianOverRepresentation S q m))) = _
  rw [← (grassmannianFunctorOverRepresentableBy S q m).homEquiv_comp]
  simp only [Category.comp_id]
  dsimp only [freeGrassmannianClassifyingHom]
  rw [Equiv.apply_symm_apply]

/-- The strict quotient classified by the universal Grassmannian point,
pulled back along a classifying morphism, has the same kernel point as the
chosen strict quotient at the test point. -/
lemma freeGrassmannianUniversalFreeQuotientPullback_kernelPoint
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m) :
    ((grassmannianPointFreeQuotient (q := q)
        (grassmannianOverRepresentation S q m)
        (freeGrassmannianUniversalPoint S q m)).pullback
      (freeGrassmannianClassifyingHom T g).left).kernelPoint =
      (grassmannianPointFreeQuotient (q := q) T g).kernelPoint := by
  calc
    _ = ((freeGrassmannianUniversalPoint S q m).app
        (op T) (ULift.up (freeGrassmannianClassifyingHom T g))).down :=
      grassmannianPointFreeQuotient_pullback_kernelPoint
        (grassmannianOverRepresentation S q m)
        (freeGrassmannianUniversalPoint S q m)
        (ULift.up (freeGrassmannianClassifyingHom T g))
    _ = (uliftYonedaEquiv g).down := congrArg ULift.down
      (freeGrassmannianUniversalPoint_app_classifyingHom T g)
    _ = _ := (grassmannianPointFreeQuotient_kernelPoint T g).symm

/-- The two strict finite-free quotient presentations above are equivalent. -/
lemma freeGrassmannianUniversalFreeQuotientPullback_r
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m) :
    (Modules.FreeQuotient.setoid q (ULift.{u} (Fin m)) T.left).r
      ((grassmannianPointFreeQuotient (q := q)
        (grassmannianOverRepresentation S q m)
        (freeGrassmannianUniversalPoint S q m)).pullback
          (freeGrassmannianClassifyingHom T g).left)
      (grassmannianPointFreeQuotient (q := q) T g) :=
  Modules.FreeQuotient.r_of_kernelPoint_eq
    (freeGrassmannianUniversalFreeQuotientPullback_kernelPoint T g)

/-- The chosen target isomorphism between the pullback of the universal strict
quotient and the strict quotient chosen at a test point. -/
noncomputable def freeGrassmannianUniversalFreeQuotientPullbackIso
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m) :
    ((grassmannianPointFreeQuotient (q := q)
        (grassmannianOverRepresentation S q m)
        (freeGrassmannianUniversalPoint S q m)).pullback
      (freeGrassmannianClassifyingHom T g).left).Q ≅
      (grassmannianPointFreeQuotient (q := q) T g).Q :=
  Classical.choose (freeGrassmannianUniversalFreeQuotientPullback_r T g)

/-- The chosen target isomorphism respects the maps from the canonical finite
free sheaf. -/
lemma freeGrassmannianUniversalFreeQuotientPullback_π_comp_iso_hom
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m) :
    ((grassmannianPointFreeQuotient (q := q)
        (grassmannianOverRepresentation S q m)
        (freeGrassmannianUniversalPoint S q m)).pullback
      (freeGrassmannianClassifyingHom T g).left).π ≫
        (freeGrassmannianUniversalFreeQuotientPullbackIso T g).hom =
      (grassmannianPointFreeQuotient (q := q) T g).π :=
  Classical.choose_spec
    (freeGrassmannianUniversalFreeQuotientPullback_r T g)

/-- Reindexing by the product monomial basis preserves the quotient-map
triangle for the universal strict quotient. -/
lemma freeGrassmannianUniversalPulledMonomialQuotientMap_comp_iso_hom
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m) :
    grassmannianPointPulledMonomialQuotientMap
        (n := n) (r := r) (q := q) (e := e) (σ := σ)
        (grassmannianOverRepresentation S q m)
        (freeGrassmannianUniversalPoint S q m)
        (ULift.up (freeGrassmannianClassifyingHom T g)) ≫
      (freeGrassmannianUniversalFreeQuotientPullbackIso T g).hom =
    grassmannianPointMonomialQuotientMap
      (n := n) (r := r) (q := q) (e := e) (σ := σ) T g := by
  dsimp only [grassmannianPointPulledMonomialQuotientMap,
    grassmannianPointMonomialQuotientMap]
  exact (Category.assoc _ _ _).trans (congrArg
    (fun k ↦ SheafOfModules.freeMap
      (R := T.left.ringCatSheaf) σ.symm ≫ k)
    (freeGrassmannianUniversalFreeQuotientPullback_π_comp_iso_hom T g))

/-- Pulling back the quotient reconstructed from the universal Grassmannian
point gives the quotient reconstructed from the classified point. -/
noncomputable def freeGrassmannianUniversalReconstructedQuotientPullbackIso
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m)
    (hambientG : TwistedFreeAmbientReconstructionCompatibility n
      (grassmannianOverRepresentation S q m).left l r d e he)
    (hambientT : TwistedFreeAmbientReconstructionCompatibility
      n T.left l r d e he) :
    Modules.projectiveFamilyAt n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ)
            (grassmannianOverRepresentation S q m)
            (freeGrassmannianUniversalPoint S q m))
        (Over.mk (freeGrassmannianClassifyingHom T g).left) ≅
      grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g :=
  grassmannianPointReconstructedQuotientPullbackIso
      (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
        (he := he) (σ := σ)
      (grassmannianOverRepresentation S q m)
      (freeGrassmannianUniversalPoint S q m)
      (ULift.up (freeGrassmannianClassifyingHom T g)) hambientG hambientT ≪≫
    reconstructedQuotientIsoOfTargetIso n T.left l r d e he
      (grassmannianPointPulledMonomialQuotientMap
        (n := n) (r := r) (q := q) (e := e) (σ := σ)
        (grassmannianOverRepresentation S q m)
        (freeGrassmannianUniversalPoint S q m)
        (ULift.up (freeGrassmannianClassifyingHom T g)))
      (grassmannianPointMonomialQuotientMap
        (n := n) (r := r) (q := q) (e := e) (σ := σ) T g)
      (freeGrassmannianUniversalFreeQuotientPullbackIso T g)
      (freeGrassmannianUniversalPulledMonomialQuotientMap_comp_iso_hom T g)

/-- One represented immersed flattening locus for the universal reconstructed
quotient pulls back to a represented immersed flattening locus for every
Grassmannian-valued point. -/
noncomputable def grassmannianPointFlatteningLocusWitnessOfUniversal
    (H : Modules.ProjectiveFlatteningLocusWitness n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ)
          (grassmannianOverRepresentation S q m)
          (freeGrassmannianUniversalPoint S q m)) P)
    (hambient : ∀ X : Scheme.{u},
      TwistedFreeAmbientReconstructionCompatibility n X l r d e he)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m) :
    Modules.ProjectiveFlatteningLocusWitness n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) P :=
  Modules.ProjectiveFlatteningLocusWitness.baseChangeOfIso n
    (grassmannianPointReconstructedQuotient
      (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
        (he := he) (σ := σ)
        (grassmannianOverRepresentation S q m)
        (freeGrassmannianUniversalPoint S q m)) P H
    (freeGrassmannianClassifyingHom T g).left
    (freeGrassmannianUniversalReconstructedQuotientPullbackIso
      T g (hambient _) (hambient _))

/-- The strict quotient selected by the intrinsic Quot-to-Grassmannian map for
the universal Quot point on an arbitrary represented flattening locus. -/
noncomputable def grassmannianPointFlatteningUniversalFreeQuotientOfWitness
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m)
    (H : Modules.ProjectiveFlatteningLocusWitness n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) P) :
    Modules.FreeQuotient q (ULift.{u} (Fin m))
      ((Over.map T.hom).obj H.representative).left :=
  D.representativeFreeQuotient
    (grassmannianPointFlatteningUniversalQuotPointOfWitness
      (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
        (d := d) (e := e) (he := he) (σ := σ) T g H)

/-- The strict quotient classified by a Grassmannian point, pulled back to an
arbitrary represented flattening locus. -/
noncomputable def grassmannianPointFreeQuotientPullbackToFlatteningOfWitness
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m)
    (H : Modules.ProjectiveFlatteningLocusWitness n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) P) :
    Modules.FreeQuotient q (ULift.{u} (Fin m)) H.representative.left :=
  (grassmannianPointFreeQuotient (q := q) T g).pullback
    H.representative.hom

/-- Fixed-degree comparison for the universal Quot point on an arbitrary
represented flattening locus. -/
structure GrassmannianPointUniversalFreeQuotientComparisonOfWitness
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m)
    (H : Modules.ProjectiveFlatteningLocusWitness n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) P) : Type (u + 1) where
  /-- Isomorphism between the two strict quotient targets. -/
  targetIso :
    (grassmannianPointFlatteningUniversalFreeQuotientOfWitness
      D T g H).Q ≅
      (grassmannianPointFreeQuotientPullbackToFlatteningOfWitness
        T g H).Q
  /-- The target isomorphism respects the maps from the finite free sheaf. -/
  π_comp :
    (grassmannianPointFlatteningUniversalFreeQuotientOfWitness
      D T g H).π ≫ targetIso.hom =
      (grassmannianPointFreeQuotientPullbackToFlatteningOfWitness T g H).π

/-- A strict fixed-degree comparison supplies the exact universal
compatibility equality required by the represented-witness fibre package. -/
lemma GrassmannianPointUniversalFreeQuotientComparisonOfWitness.universalCompatibility
    {D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ}
    {T : Over S}
    {g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m}
    {H : Modules.ProjectiveFlatteningLocusWitness n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) P}
    (C : GrassmannianPointUniversalFreeQuotientComparisonOfWitness D T g H) :
    let Z := H.representative
    D.natTrans.app (op ((Over.map T.hom).obj Z))
      (grassmannianPointFlatteningUniversalQuotPointOfWitness
        (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
          (d := d) (e := e) (he := he) (σ := σ) T g H) =
      (uliftYoneda.map (fibreLocusMap T Z) ≫ g).app
        (op ((Over.map T.hom).obj Z))
        (ULift.up (𝟙 ((Over.map T.hom).obj Z))) := by
  let Z := H.representative
  let x := grassmannianPointFlatteningUniversalQuotPointOfWitness
    (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
      (d := d) (e := e) (he := he) (σ := σ) T g H
  let q₁ := grassmannianPointFlatteningUniversalFreeQuotientOfWitness D T g H
  let q₂ := grassmannianPointFreeQuotientPullbackToFlatteningOfWitness T g H
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

set_option maxHeartbeats 400000 in
-- The dependent normalization and representative-transport pasting is elaboration-heavy.
/-- Ambient reconstruction coherence constructs the fixed-degree comparison
for the universal Quot point on an arbitrary represented flattening locus. -/
noncomputable def
    grassmannianPointUniversalFreeQuotientComparisonOfWitnessOfAmbient
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m)
    (H : Modules.ProjectiveFlatteningLocusWitness n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) P)
    (hambient : TwistedFreeAmbientReconstructionCompatibility
      n T.left l r d e he) :
    GrassmannianPointUniversalFreeQuotientComparisonOfWitness D T g H := by
  let Q := grassmannianPointReconstructedQuotient
    (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
      (he := he) (σ := σ) T g
  let Z := H.representative
  let E := H.representableBy
  let hz := E.homEquiv (𝟙 Z)
  let QZ := Modules.projectiveFamilyAt n Q Z
  let pZ : (∐ fun _ : ULift.{u} (Fin r) ↦
      projectiveSpaceOverTwist n Z.left (-l)) ⟶ QZ :=
    (projectiveSpaceOverTwistedFree_pullbackIso n r l Z.hom).inv ≫
      (Modules.pullback (projectiveSpaceOverMap n Z.hom)).map
        (grassmannianPointReconstructedQuotientMap
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g)
  let b := Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace
    (n := n) (r := r) (l := l) ((Over.map T.hom).obj Z) QZ
      (by infer_instance) hz.down.down.1 pZ
  let x := grassmannianPointFlatteningUniversalQuotPointOfWitness
    (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
      (d := d) (e := e) (he := he) (σ := σ) T g H
  have hxb : Quotient.mk _ b = x.1 := by
    rfl
  let a := TwistedFreeQuotGrassmannianNatTransData.representative x
  have hab : (Modules.QuotientPullbackData.setoid
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) ((Over.map T.hom).obj Z)).r a b := by
    apply Quotient.exact
    exact (TwistedFreeQuotGrassmannianNatTransData.representative_mk x).trans
      hxb.symm
  let hPb :=
    ofTwistedFreeQuotientOnProjectiveSpace_hasFiberwiseHilbertPolynomial
      ((Over.map T.hom).obj Z) QZ (by infer_instance) hz.down.down.1 pZ P
        hz.down.down.2
  let hMb := D.isProjectiveOfRank ((Over.map T.hom).obj Z) b hPb
  let hsb := D.surjective ((Over.map T.hom).obj Z) b hPb
  let qB := twistedFreeQuotGrassmannianFreeQuotient
    n S l r b d e he σ hMb hsb
  let q₂ := grassmannianPointFreeQuotientPullbackToFlatteningOfWitness
    (n := n) (r := r) (q := q) (l := l) (P := P)
      (d := d) (e := e) (he := he) (σ := σ) T g H
  letI : (grassmannianPointFreeQuotient (q := q) T g).Q.IsQuasicoherent :=
    (grassmannianPointFreeQuotient (q := q) T g).isQuasicoherent
  let u := grassmannianPointMonomialQuotientMap
    (n := n) (r := r) (q := q) (e := e) (σ := σ) T g
  letI : Epi u := by
    letI : IsIso (SheafOfModules.freeMap
        (R := T.left.ringCatSheaf) σ.symm) :=
      Modules.freeMap_isIso_of_equiv σ.symm
    letI : Epi (grassmannianPointFreeQuotient (q := q) T g).π :=
      (grassmannianPointFreeQuotient (q := q) T g).epi
    dsimp only [u, grassmannianPointMonomialQuotientMap]
    infer_instance
  let uZ := pullbackFreeQuotientMap Z.hom u
  let vZ := quotGrassmannianFreeMap n Z.left l r pZ d e he
  let MZ : Z.left.Modules :=
    (Modules.pushforward (projectiveSpaceOverπ n Z.left)).obj
      (projectiveSpaceOverTwistModule QZ (d : ℤ))
  let Eβ :=
    (Modules.pushforward (projectiveSpaceOverπ n Z.left)).mapIso
      (Modules.tensorLeftIso
        (Modules.QuotientPullbackData.ofTwistedFreeQuotientOnProjectiveSpace_quotDataIso
          (n := n) (r := r) (l := l) ((Over.map T.hom).obj Z)
            QZ (by infer_instance) hz.down.down.1 pZ)
        (projectiveSpaceOverTwist n Z.left (d : ℤ)))
  letI : q₂.Q.IsQuasicoherent := q₂.isQuasicoherent
  letI : qB.Q.IsQuasicoherent := qB.isQuasicoherent
  letI : MZ.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent Z.left.ringCatSheaf).prop_of_iso
      Eβ qB.isQuasicoherent
  have hu : uZ = SheafOfModules.freeMap
        (R := Z.left.ringCatSheaf) σ.symm ≫ q₂.π := by
    dsimp only [uZ, u, q₂,
      grassmannianPointFreeQuotientPullbackToFlatteningOfWitness,
      Modules.FreeQuotient.pullback, grassmannianPointMonomialQuotientMap]
    exact pullbackFreeQuotientMap_freeMap Z.hom σ.symm
      (grassmannianPointFreeQuotient (q := q) T g).π
  have hv : SheafOfModules.freeMap
        (R := Z.left.ringCatSheaf) σ.symm ≫ qB.π ≫ Eβ.hom = vZ := by
    exact denormalized_twistedFreeQuotGrassmannianFreeMap_reindex
      n l r ((Over.map T.hom).obj Z) QZ (by infer_instance)
        hz.down.down.1 pZ d e he σ
  letI : Epi uZ := by
    rw [hu]
    letI : IsIso (SheafOfModules.freeMap
        (R := Z.left.ringCatSheaf) σ.symm) :=
      Modules.freeMap_isIso_of_equiv σ.symm
    letI : Epi q₂.π := q₂.epi
    infer_instance
  letI : Epi vZ := by
    rw [← hv]
    letI : IsIso (SheafOfModules.freeMap
        (R := Z.left.ringCatSheaf) σ.symm) :=
      Modules.freeMap_isIso_of_equiv σ.symm
    letI : Epi qB.π := qB.epi
    infer_instance
  have hzero : kernel.ι uZ ≫ vZ =
      @Zero.zero (kernel uZ ⟶ MZ)
        (Limits.HasZeroMorphisms.zero (C := Z.left.Modules) (kernel uZ) MZ) := by
    exact kernel_ι_comp_quotGrassmannianFreeMap_reconstructedPullback_eq_zero
      n l r d e he Z.hom u
        (grassmannianPointFreeQuotient
          (q := q) T g).isProjectiveOfRank.isFiniteLocallyFree
        hambient
  have huRank : Modules.IsProjectiveOfRank q
      ((Modules.pullback Z.hom).obj
        (grassmannianPointFreeQuotient (q := q) T g).Q) := by
    exact q₂.isProjectiveOfRank
  have hvRank : Modules.IsProjectiveOfRank q MZ := by
    exact hMb.of_iso Eβ
  let C := Modules.freeQuotientTargetIsoOfKernelVanishing
    uZ vZ hzero huRank hvRank
  have hC : uZ ≫ C.hom = vZ :=
    Modules.freeQuotientTargetIsoOfKernelVanishing_comp
      uZ vZ hzero huRank hvRank
  have hq₂B : q₂.π ≫ C.hom = qB.π ≫ Eβ.hom := by
    let w := SheafOfModules.freeMap (R := Z.left.ringCatSheaf) σ.symm
    letI : IsIso w := Modules.freeMap_isIso_of_equiv σ.symm
    apply (cancel_epi w).1
    calc
      w ≫ (q₂.π ≫ C.hom) = uZ ≫ C.hom := by rw [hu]; rfl
      _ = vZ := hC
      _ = w ≫ (qB.π ≫ Eβ.hom) := by rw [hv]
  let EB₂ : qB.Q ≅ q₂.Q := Eβ ≪≫ C.symm
  have hEB₂ : qB.π ≫ EB₂.hom = q₂.π := by
    dsimp only [EB₂, Iso.trans_hom, Iso.symm_hom]
    rw [← Category.assoc, ← hq₂B]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let hPa :=
    TwistedFreeQuotGrassmannianNatTransData.representative_hasFiberwiseHilbertPolynomial x
  let q₁ := grassmannianPointFlatteningUniversalFreeQuotientOfWitness D T g H
  have hr : (Modules.FreeQuotient.setoid q (ULift.{u} (Fin m)) Z.left).r
      q₁ qB := by
    exact twistedFreeQuotGrassmannianFreeQuotient_r_of_r
      n S l r hab d e he σ
        (D.isProjectiveOfRank ((Over.map T.hom).obj Z) a hPa)
        (D.surjective ((Over.map T.hom).obj Z) a hPa)
        hMb hsb
  let EaB : q₁.Q ≅ qB.Q := Classical.choose hr
  have hEaB : q₁.π ≫ EaB.hom = qB.π := Classical.choose_spec hr
  exact {
    targetIso := EaB ≪≫ EB₂
    π_comp := by
      dsimp only [q₁, q₂, Iso.trans_hom]
      rw [← Category.assoc, hEaB, hEB₂]
  }

/-- Ambient reconstruction coherence gives the universal compatibility
equality for any represented immersed flattening locus. -/
theorem grassmannianPointUniversalCompatibilityOfWitness_of_ambient
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m)
    (H : Modules.ProjectiveFlatteningLocusWitness n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) P)
    (hambient : TwistedFreeAmbientReconstructionCompatibility
      n T.left l r d e he) :
    let Z := H.representative
    D.natTrans.app (op ((Over.map T.hom).obj Z))
      (grassmannianPointFlatteningUniversalQuotPointOfWitness
        (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
          (d := d) (e := e) (he := he) (σ := σ) T g H) =
      (uliftYoneda.map (fibreLocusMap T Z) ≫ g).app
        (op ((Over.map T.hom).obj Z))
        (ULift.up (𝟙 ((Over.map T.hom).obj Z))) :=
  (grassmannianPointUniversalFreeQuotientComparisonOfWitnessOfAmbient
    D T g H hambient).universalCompatibility

/-- A single universal represented flattening locus supplies both the
flattening witness and its universal compatibility at every test point. -/
theorem grassmannianPointUniversalCompatibilityOfUniversalFlatteningLocus
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (H : Modules.ProjectiveFlatteningLocusWitness n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ)
          (grassmannianOverRepresentation S q m)
          (freeGrassmannianUniversalPoint S q m)) P)
    (hambient : ∀ X : Scheme.{u},
      TwistedFreeAmbientReconstructionCompatibility n X l r d e he)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m) :
    let HT := grassmannianPointFlatteningLocusWitnessOfUniversal
      H hambient T g
    let Z := HT.representative
    D.natTrans.app (op ((Over.map T.hom).obj Z))
      (grassmannianPointFlatteningUniversalQuotPointOfWitness
        (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
          (d := d) (e := e) (he := he) (σ := σ) T g HT) =
      (uliftYoneda.map (fibreLocusMap T Z) ≫ g).app
        (op ((Over.map T.hom).obj Z))
        (ULift.up (𝟙 ((Over.map T.hom).obj Z))) :=
  grassmannianPointUniversalCompatibilityOfWitness_of_ambient
    D T g (grassmannianPointFlatteningLocusWitnessOfUniversal
      H hambient T g) (hambient T.left)

/-- A single represented immersed flattening locus on the universal free
Grassmannian reconstruction supplies the flattening inputs in the canonical
twisted-free W6 criterion. -/
theorem twistedFreeQuotHasFreeGrassmannianImmersion_of_universalFlatteningLocus
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
    TwistedFreeQuotHasFreeGrassmannianImmersion n S l r P :=
  twistedFreeQuotHasFreeGrassmannianImmersion_of_canonicalWitnessCompatibility
    I hambient hkernel
      (grassmannianPointFlatteningLocusWitnessOfUniversal H hambient)
      (grassmannianPointUniversalCompatibilityOfUniversalFlatteningLocus
        I.natTransData H hambient)

end AlgebraicGeometry.Scheme

end

end
