module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFibreReflection
public import StacksAndModuli.API.TwistedFreeReconstructionBaseChange

/-!
# Canonical reconstruction comparison on Quot-to-Grassmannian fibres

The generic positive-twist base-change theorem for `reconstructedQuotient'` supplies the
explicit comparison retained as a hypothesis in the fibre-reflection API.  The only
specialized coherence is that reindexing the strict Grassmannian quotient by the product
monomial basis commutes with normalized pullback.
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

/-- Pulling back the product-indexed Grassmannian quotient is the normalized pullback
of the product-indexed quotient on the original base. -/
lemma pullbackFreeQuotientMap_grassmannianPointMonomialQuotientMap
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    {Y : (Over S)ᵒᵖ}
    (a : (uliftYoneda.{u + 1}.obj T).obj Y) :
    pullbackFreeQuotientMap a.down.left
        (grassmannianPointMonomialQuotientMap
          (n := n) (r := r) (q := q) (e := e) (σ := σ) T g) =
      grassmannianPointPulledMonomialQuotientMap
        (n := n) (r := r) (q := q) (e := e) (σ := σ) T g a := by
  dsimp only [grassmannianPointMonomialQuotientMap,
    grassmannianPointPulledMonomialQuotientMap,
    Modules.FreeQuotient.pullback]
  exact pullbackFreeQuotientMap_freeMap a.down.left σ.symm
    (grassmannianPointFreeQuotient (q := q) T g).π

/-- Reindexing the strict quotient attached to a Quot point back to the product
monomial basis recovers the unreindexed monomial quotient map. -/
lemma representativeFreeQuotient_reindex_π
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    {Y : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj Y) :
    SheafOfModules.freeMap
          (R := (unop Y).left.ringCatSheaf) σ.symm ≫
        (D.representativeFreeQuotient x).π =
      quotGrassmannianFreeMap n (unop Y).left l r
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
          (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x))
        d e he := by
  dsimp only [TwistedFreeQuotGrassmannianQuotientNatTransData.representativeFreeQuotient,
    twistedFreeQuotGrassmannianFreeQuotient,
    twistedFreeQuotGrassmannianFreeMap, quotGrassmannianFreeMap]
  rw [Modules.freeMap_comp_freeHomOfSections]
  congr 1
  funext i
  simp only [Equiv.apply_symm_apply]

/-- The canonical base-change comparison for the quotient reconstructed from a
Grassmannian point. -/
noncomputable def grassmannianPointReconstructedQuotientPullbackIso
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    {Y : (Over S)ᵒᵖ}
    (a : (uliftYoneda.{u + 1}.obj T).obj Y)
    (hambientT :
      (freeTensorTwistIso n T.left
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T.left l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T.left l r d e he)
            (projectiveSpaceOverTwist n T.left (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T.left
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n T.left (-l)) d).hom)
    (hambientY :
      (freeTensorTwistIso n (unop Y).left
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n (unop Y).left l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n (unop Y).left l r d e he)
            (projectiveSpaceOverTwist n (unop Y).left (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n (unop Y).left
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n (unop Y).left (-l)) d).hom) :
    Modules.projectiveFamilyAt n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g) (Over.mk a.down.left) ≅
      reconstructedQuotient' n (unop Y).left l r d e he
        (grassmannianPointPulledMonomialQuotientMap
          (n := n) (r := r) (q := q) (e := e) (σ := σ) T g a) := by
  let x := grassmannianPointFreeQuotient (q := q) T g
  let u := grassmannianPointMonomialQuotientMap
    (n := n) (r := r) (q := q) (e := e) (σ := σ) T g
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  letI : Epi x.π := x.epi
  letI : IsIso (SheafOfModules.freeMap
      (R := T.left.ringCatSheaf) σ.symm) :=
    Modules.freeMap_isIso_of_equiv σ.symm
  letI : Epi u := by
    dsimp only [u, grassmannianPointMonomialQuotientMap]
    infer_instance
  let E := reconstructedQuotient'PullbackIso n l r d e he
    a.down.left u x.isProjectiveOfRank.isFiniteLocallyFree
      hambientT hambientY
  exact E ≪≫ eqToIso (congrArg
    (fun v ↦ reconstructedQuotient' n (unop Y).left l r d e he v)
    (pullbackFreeQuotientMap_grassmannianPointMonomialQuotientMap
      (n := n) (r := r) (q := q) (e := e) (σ := σ) T g a))

/-- Canonical reconstruction on a compatible fibre point: base change and basis
reindexing are discharged internally, leaving only the geometric kernel presentation. -/
noncomputable def grassmannianPointProjectiveFamilyIsoRepresentativeOfCanonicalBaseChange
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    {Y : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj Y)
    (a : (uliftYoneda.{u + 1}.obj T).obj Y)
    (h : D.natTrans.app Y x = g.app Y a)
    (hambientT :
      (freeTensorTwistIso n T.left
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T.left l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T.left l r d e he)
            (projectiveSpaceOverTwist n T.left (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T.left
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n T.left (-l)) d).hom)
    (hambientY :
      (freeTensorTwistIso n (unop Y).left
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n (unop Y).left l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n (unop Y).left l r d e he)
            (projectiveSpaceOverTwist n (unop Y).left (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n (unop Y).left
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n (unop Y).left (-l)) d).hom)
    (R : ReconstructedRelationPresentsKernel n (unop Y).left l r d e he
      (quotGrassmannianFreeMap n (unop Y).left l r
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
          (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x))
        d e he)
      (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
        (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x))) :
    Modules.projectiveFamilyAt n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g) (Over.mk a.down.left) ≅
      twistedFreeQuotientSheaf n S l r
        (TwistedFreeQuotGrassmannianNatTransData.representative x) :=
  grassmannianPointProjectiveFamilyIsoRepresentativeOfReconstruction
    D T g x a h
      (grassmannianPointReconstructedQuotientPullbackIso
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g a hambientT hambientY)
      (grassmannianPointPulledMonomialQuotientMap_comp_isoRepresentative_hom
        D T g x a h (representativeFreeQuotient_reindex_π D x))
      R

/-- The canonical base-change comparison and reindexing reduce compatible-family
flatness to the kernel-presentation input used by reflection. -/
noncomputable def grassmannianPointCompatibleFlatteningOfCanonicalBaseChange
    (D : TwistedFreeQuotGrassmannianQuotientNatTransData
      n S l r P d e he m q σ)
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    {Y : (Over S)ᵒᵖ}
    (x : (quotFunctorP
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l)) P).obj Y)
    (a : (uliftYoneda.{u + 1}.obj T).obj Y)
    (h : D.natTrans.app Y x = g.app Y a)
    (hambientT :
      (freeTensorTwistIso n T.left
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n T.left l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n T.left l r d e he)
            (projectiveSpaceOverTwist n T.left (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n T.left
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n T.left (-l)) d).hom)
    (hambientY :
      (freeTensorTwistIso n (unop Y).left
          (ULift.{u} (Fin r) × Fin ((n + e).choose n)) (-(d : ℤ))).hom ≫
          twistedFreeMonomialHom n (unop Y).left l r d e he =
        Modules.tensorMapLeft
            (twistedFreeMonomialMap n (unop Y).left l r d e he)
            (projectiveSpaceOverTwist n (unop Y).left (-(d : ℤ))) ≫
          (projectiveSpaceOverTwistModule_cancelIso_nat n (unop Y).left
            (∐ fun _ : ULift.{u} (Fin r) ↦
              projectiveSpaceOverTwist n (unop Y).left (-l)) d).hom)
    (R : ReconstructedRelationPresentsKernel n (unop Y).left l r d e he
      (quotGrassmannianFreeMap n (unop Y).left l r
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
          (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x))
        d e he)
      (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
        (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x))) :
    (Modules.projectiveFlatteningFunctor n
      (grassmannianPointReconstructedQuotient
        (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
          (he := he) (σ := σ) T g) (P := P)).obj
      (op (Over.mk a.down.left)) :=
  grassmannianPointCompatibleFlatteningOfIso
    (n := n) (r := r) (m := m) (q := q) (l := l) (P := P)
      (d := d) (e := e) (he := he) (σ := σ) T g x a
    (grassmannianPointProjectiveFamilyIsoRepresentativeOfCanonicalBaseChange
      D T g x a h hambientT hambientY R)

end AlgebraicGeometry.Scheme

end

end
