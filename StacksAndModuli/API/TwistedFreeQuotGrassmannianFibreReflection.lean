module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianFlatteningFibre

/-!
# Reflection on a fibre of the Quot-to-Grassmannian map

This file packages the formal composition needed to identify a pullback of the
Grassmannian reconstruction with a compatible fixed-polynomial Quot family.  Pullback
of `reconstructedQuotient'` is deliberately retained as an explicit isomorphism: once
that base-change comparison is supplied, invariance under a compatible isomorphism of
finite-free quotient targets and reflection from a kernel presentation are automatic.
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

/-- The product-monomial-indexed quotient obtained by pulling the strict quotient
classified by a Grassmannian point to a test scheme. -/
noncomputable def grassmannianPointPulledMonomialQuotientMap
    (T : Over S)
    (g : uliftYoneda.{u + 1}.obj T ⟶ Modules.grassmannianFunctorOver S q m)
    {Y : (Over S)ᵒᵖ}
    (a : (uliftYoneda.{u + 1}.obj T).obj Y) :
    SheafOfModules.free (R := (unop Y).left.ringCatSheaf)
        (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶
      ((grassmannianPointFreeQuotient (q := q) T g).pullback
        a.down.left).Q :=
  SheafOfModules.freeMap (R := (unop Y).left.ringCatSheaf) σ.symm ≫
    ((grassmannianPointFreeQuotient (q := q) T g).pullback
      a.down.left).π

/-- Compatibility of the pulled product-indexed quotient with the chosen strict Quot
representative reduces to the corresponding reindexing identity for that representative.
-/
lemma grassmannianPointPulledMonomialQuotientMap_comp_isoRepresentative_hom
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
    (hreindex : SheafOfModules.freeMap
          (R := (unop Y).left.ringCatSheaf) σ.symm ≫
        (D.representativeFreeQuotient x).π =
      quotGrassmannianFreeMap n (unop Y).left l r
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
          (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x))
        d e he) :
    grassmannianPointPulledMonomialQuotientMap
        (n := n) (r := r) (q := q) (e := e) (σ := σ) T g a ≫
        (grassmannianPointFreeQuotientPullbackIsoRepresentative
          D T g x a h).hom =
      quotGrassmannianFreeMap n (unop Y).left l r
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
          (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x))
        d e he := by
  dsimp only [grassmannianPointPulledMonomialQuotientMap]
  rw [Category.assoc,
    grassmannianPointFreeQuotientPullback_π_comp_isoRepresentative_hom
      D T g x a h]
  exact hreindex

/-- A pullback comparison for reconstruction, followed by transport of the finite-free
quotient target and a kernel presentation, identifies the reconstructed family with the
normalized sheaf of a compatible Quot point. -/
noncomputable def grassmannianPointProjectiveFamilyIsoRepresentativeOfReconstruction
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
    (Ebc : Modules.projectiveFamilyAt n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g) (Over.mk a.down.left) ≅
      reconstructedQuotient' n (unop Y).left l r d e he
        (grassmannianPointPulledMonomialQuotientMap
          (n := n) (r := r) (q := q) (e := e) (σ := σ) T g a))
    (hmap : grassmannianPointPulledMonomialQuotientMap
        (n := n) (r := r) (q := q) (e := e) (σ := σ) T g a ≫
        (grassmannianPointFreeQuotientPullbackIsoRepresentative
          D T g x a h).hom =
      quotGrassmannianFreeMap n (unop Y).left l r
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
          (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x))
        d e he)
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
        (TwistedFreeQuotGrassmannianNatTransData.representative x) := by
  let p := Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
    (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x)
  letI : Epi p :=
    Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver_epi
      (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x)
  exact Ebc ≪≫
      reconstructedQuotientIsoOfTargetIso n (unop Y).left l r d e he
        (grassmannianPointPulledMonomialQuotientMap
          (n := n) (r := r) (q := q) (e := e) (σ := σ) T g a)
        (quotGrassmannianFreeMap n (unop Y).left l r p d e he)
        (grassmannianPointFreeQuotientPullbackIsoRepresentative D T g x a h)
        hmap ≪≫
      R.quotientIso

/-- The same reconstruction inputs produce the point of the projective flattening
functor attached to a compatible point of the Quot-to-Grassmannian fibre. -/
noncomputable def grassmannianPointCompatibleFlatteningOfReconstruction
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
    (Ebc : Modules.projectiveFamilyAt n
        (grassmannianPointReconstructedQuotient
          (n := n) (r := r) (q := q) (l := l) (d := d) (e := e)
            (he := he) (σ := σ) T g) (Over.mk a.down.left) ≅
      reconstructedQuotient' n (unop Y).left l r d e he
        (grassmannianPointPulledMonomialQuotientMap
          (n := n) (r := r) (q := q) (e := e) (σ := σ) T g a))
    (hmap : grassmannianPointPulledMonomialQuotientMap
        (n := n) (r := r) (q := q) (e := e) (σ := σ) T g a ≫
        (grassmannianPointFreeQuotientPullbackIsoRepresentative
          D T g x a h).hom =
      quotGrassmannianFreeMap n (unop Y).left l r
        (Modules.QuotientPullbackData.twistedFreeQuotientOnProjectiveSpaceOver
          (unop Y) (TwistedFreeQuotGrassmannianNatTransData.representative x))
        d e he)
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
    (grassmannianPointProjectiveFamilyIsoRepresentativeOfReconstruction
      D T g x a h Ebc hmap R)

end AlgebraicGeometry.Scheme

end

end
