module

public import StacksAndModuli.«Section6.2-Nodal».«part6.2.1-nodes»
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso

/-!
# Coefficient change for split nodes

This file transports multivariate power-series rings and the standard node ring across
an equivalence of coefficient fields. It then applies that transport to split completed
local rings. Over an algebraically closed field, the canonical map to Mathlib's chosen
algebraic closure is an equivalence; consequently the geometric and split definitions of
a node, and the corresponding nodal-curve predicates, agree.

## Main definitions and results

* `MvPowerSeries.mapAlgEquiv`;
* `AlgebraicGeometry.Scheme.nodeRingMapAlgEquiv`;
* `AlgebraicGeometry.Scheme.isSplitNodeAt_comp_fieldEquiv_iff`;
* `AlgebraicGeometry.Scheme.isNodeAt_iff_isSplitNodeAt`;
* `AlgebraicGeometry.Scheme.isGeometricallyNodalCurveOver_iff_isNodalCurveOver`;
* `AlgebraicGeometry.Scheme.IsGeometricallyNodalCurveOver.isNodalCurveOver`;
* `AlgebraicGeometry.Scheme.IsNodalCurveOver.isGeometricallyNodalCurveOver`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u v

namespace MvPowerSeries

/-- An algebra equivalence of coefficient rings induces an algebra equivalence of
multivariate formal power-series rings. -/
noncomputable def mapAlgEquiv
    {R A B : Type u} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (σ : Type v) :
    MvPowerSeries σ A ≃ₐ[R] MvPowerSeries σ B :=
  AlgEquiv.ofBijective (mapAlgHom (σ := σ) e.toAlgHom) ⟨by
    intro f g h
    ext n
    apply e.injective
    exact congrArg (coeff n) h, by
    intro f
    refine ⟨map e.symm.toRingEquiv.toRingHom f, ?_⟩
    ext n
    change e (e.symm (coeff n f)) = coeff n f
    simp⟩

/-- Coefficient change on formal power series applies the coefficient equivalence to
every coefficient. -/
@[simp]
theorem mapAlgEquiv_apply
    {R A B : Type u} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (σ : Type v)
    (f : MvPowerSeries σ A) :
    mapAlgEquiv e σ f = map e.toRingEquiv.toRingHom f :=
  rfl

end MvPowerSeries

namespace AlgebraicGeometry.Scheme

/-- The coefficient equivalence carries the standard node ideal to the standard node
ideal over the target field. -/
theorem nodeIdeal_map_mvPowerSeriesMapAlgEquiv
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (e : k ≃ₐ[k] K) :
    (nodeIdeal k).map
        (MvPowerSeries.mapAlgEquiv e (Fin 2)).toRingEquiv.toRingHom =
      nodeIdeal K := by
  rw [nodeIdeal, nodeIdeal, Ideal.map_span, Set.image_singleton]
  have hX (i : Fin 2) :
      (MvPowerSeries.mapAlgEquiv e (Fin 2)).toRingEquiv.toRingHom
          (MvPowerSeries.X i) = MvPowerSeries.X i := by
    change MvPowerSeries.map e.toRingEquiv.toRingHom (MvPowerSeries.X i) = _
    exact MvPowerSeries.map_X _ _
  rw [map_mul, hX, hX]

/-- An equivalence of coefficient fields induces an equivalence of their standard node
rings, viewed as algebras over the source field. -/
noncomputable def nodeRingMapAlgEquiv
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (e : k ≃ₐ[k] K) : nodeRing k ≃ₐ[k] nodeRing K :=
  Ideal.quotientEquivAlg (nodeIdeal k) (nodeIdeal K)
    (MvPowerSeries.mapAlgEquiv e (Fin 2))
    (nodeIdeal_map_mvPowerSeriesMapAlgEquiv e).symm

/-- The algebra map into a completed local ring is compatible with composing the
structure morphism with a map of affine bases. -/
theorem algebraMap_completedLocalRingAlgebra_comp_apply
    {R S : Type u} [CommRing R] [CommRing S]
    (g : R →+* S) {C : Scheme.{u}} (q : C ⟶ Spec (CommRingCat.of S))
    (x : C) (r : R) :
    letI := completedLocalRingAlgebra q x
    letI := completedLocalRingAlgebra
      (q ≫ Spec.map (CommRingCat.ofHom g)) x
    @algebraMap R (C.completedLocalRing x) _ _
        (completedLocalRingAlgebra
          (q ≫ Spec.map (CommRingCat.ofHom g)) x) r =
      @algebraMap S (C.completedLocalRing x) _ _
        (completedLocalRingAlgebra q x) (g r) := by
  let _ := completedLocalRingAlgebra q x
  let _ := completedLocalRingAlgebra
    (q ≫ Spec.map (CommRingCat.ofHom g)) x
  change C.toCompletedLocalRing x
      (baseToStalk (q ≫ Spec.map (CommRingCat.ofHom g)) x r) =
    C.toCompletedLocalRing x (baseToStalk q x (g r))
  congr 1
  exact (DFunLike.congr_fun
    (CommRingCat.hom_ext_iff.mp
      (baseToStalk_comp (CommRingCat.ofHom g) q x)) r).symm

/-- Split-node completed-local coordinates are unchanged when the coefficient field is
replaced by an equivalent field and the structure morphism is composed accordingly. -/
theorem isSplitNodeAt_comp_fieldEquiv_iff
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (e : k ≃ₐ[k] K) (C : Scheme.{u})
    (q : C ⟶ Spec (CommRingCat.of K)) (x : C) :
    (letI : C.Over (Spec (CommRingCat.of k)) :=
        ⟨q ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))⟩;
      C.IsSplitNodeAt k x) ↔
      (letI : C.Over (Spec (CommRingCat.of K)) := ⟨q⟩;
        C.IsSplitNodeAt K x) := by
  let _ : C.Over (Spec (CommRingCat.of k)) :=
    ⟨q ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))⟩
  let _ : C.Over (Spec (CommRingCat.of K)) := ⟨q⟩
  let _ := stalkAlgebra
    (q ≫ Spec.map (CommRingCat.ofHom (algebraMap k K))) x
  let _ := stalkAlgebra q x
  change Nonempty (C.completedLocalRing x ≃ₐ[k] nodeRing k) ↔
    Nonempty (C.completedLocalRing x ≃ₐ[K] nodeRing K)
  constructor
  · rintro ⟨h⟩
    let f : C.completedLocalRing x ≃ₐ[k] nodeRing K :=
      h.trans (nodeRingMapAlgEquiv e)
    refine ⟨AlgEquiv.ofRingEquiv (R := K) (f := f.toRingEquiv) fun b ↦ ?_⟩
    obtain ⟨a, rfl⟩ := e.surjective b
    have he : e a = algebraMap k K a := by
      simpa using e.commutes a
    rw [he, ← algebraMap_completedLocalRingAlgebra_comp_apply
      (algebraMap k K) q x a]
    change f (algebraMap k (C.completedLocalRing x) a) = _
    rw [f.commutes]
    exact IsScalarTower.algebraMap_apply k K (nodeRing K) a
  · rintro ⟨h⟩
    let f : C.completedLocalRing x ≃ₐ[k] nodeRing K :=
      AlgEquiv.ofRingEquiv (R := k) (f := h.toRingEquiv) fun a ↦ by
        rw [algebraMap_completedLocalRingAlgebra_comp_apply
          (algebraMap k K) q x a]
        change h (algebraMap K (C.completedLocalRing x) (algebraMap k K a)) = _
        rw [h.commutes]
        exact (IsScalarTower.algebraMap_apply k K (nodeRing K) a).symm
    exact ⟨f.trans (nodeRingMapAlgEquiv e).symm⟩

/-- When `k` is algebraically closed, its canonical map to Mathlib's chosen algebraic
closure is an algebra equivalence. -/
noncomputable def algClosedAlgebraicClosureAlgEquiv
    (k : Type u) [Field k] [IsAlgClosed k] : k ≃ₐ[k] AlgebraicClosure k :=
  AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- API lemma for Definition 6.2.1 (algebraically closed specialization): over an
algebraically closed field, the geometric node predicate agrees with the split-node
predicate on the original curve. -/
theorem isNodeAt_iff_isSplitNodeAt
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] (x : C) :
    C.IsNodeAt k x ↔ C.IsSplitNodeAt k x := by
  let e := algClosedAlgebraicClosureAlgEquiv k
  let _ : IsIso
      (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) :=
    e.toRingEquiv.toCommRingCatIso.isIso_hom
  let _ : IsIso (Spec.map
      (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) :=
    inferInstance
  let _ : IsIso (geometricBaseChangeProjection k C) := inferInstance
  let G := geometricBaseChange k C
  let q : G ⟶ Spec (CommRingCat.of (AlgebraicClosure k)) :=
    G ↘ Spec (CommRingCat.of (AlgebraicClosure k))
  let _ : G.Over (Spec (CommRingCat.of k)) :=
    ⟨q ≫ Spec.map
      (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))⟩
  let E : G ≅ C := asIso (geometricBaseChangeProjection k C)
  let Eover : G.asOver (Spec (CommRingCat.of k)) ≅
      C.asOver (Spec (CommRingCat.of k)) :=
    Over.isoMk E (by
      change pullback.fst _ _ ≫ (C ↘ Spec (CommRingCat.of k)) =
        pullback.snd _ _ ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap k (AlgebraicClosure k)))
      exact pullback.condition)
  constructor
  · rintro ⟨y, hyx, hy⟩
    have hyk : G.IsSplitNodeAt k y :=
      (isSplitNodeAt_comp_fieldEquiv_iff e G q y).mpr hy
    have htarget := (isSplitNodeAt_isoOver_iff Eover y).mp hyk
    change C.IsSplitNodeAt k (geometricBaseChangeProjection k C y) at htarget
    rwa [hyx] at htarget
  · intro hx
    let y : G := E.inv x
    have hyx : geometricBaseChangeProjection k C y = x := by
      change E.hom (E.inv x) = x
      exact (Scheme.homeoOfIso E).apply_symm_apply x
    have htarget : C.IsSplitNodeAt k (E.hom y) := by
      rwa [show E.hom y = x from (Scheme.homeoOfIso E).apply_symm_apply x]
    have hyk : G.IsSplitNodeAt k y :=
      (isSplitNodeAt_isoOver_iff Eover y).mpr htarget
    have hy : G.IsSplitNodeAt (AlgebraicClosure k) y :=
      (isSplitNodeAt_comp_fieldEquiv_iff e G q y).mp hyk
    exact ⟨y, hyx, hy⟩

/-- API lemma for Definition 6.2.1 (algebraically closed specialization): the exact
arbitrary-field nodal-curve predicate agrees with the established split-node predicate
over an algebraically closed field. -/
theorem isGeometricallyNodalCurveOver_iff_isNodalCurveOver
    (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) [C.Over (Spec (CommRingCat.of k))] :
    IsGeometricallyNodalCurveOver k C ↔ IsNodalCurveOver k C := by
  constructor
  · intro h
    refine ⟨h.isCurve, h.pureDimensionOne, fun x hx ↦ ?_⟩
    exact (h.smooth_or_isNode x hx).imp_right
      ((isNodeAt_iff_isSplitNodeAt k C x).mp)
  · intro h
    refine ⟨h.isCurve, h.pureDimensionOne, fun x hx ↦ ?_⟩
    exact (h.smooth_or_isSplitNode x hx).imp_right
      ((isNodeAt_iff_isSplitNodeAt k C x).mpr)

/-- API lemma for Definition 6.2.1 (algebraically closed specialization): an
arbitrary-field geometric nodal-curve witness gives the established split nodal-curve
witness over an algebraically closed field. -/
theorem IsGeometricallyNodalCurveOver.isNodalCurveOver
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsGeometricallyNodalCurveOver k C) : IsNodalCurveOver k C :=
  (isGeometricallyNodalCurveOver_iff_isNodalCurveOver k C).mp h

/-- API lemma for Definition 6.2.1 (algebraically closed specialization): an
established split nodal-curve witness gives the exact arbitrary-field geometric
nodal-curve witness over an algebraically closed field. -/
theorem IsNodalCurveOver.isGeometricallyNodalCurveOver
    {k : Type u} [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k))]
    (h : IsNodalCurveOver k C) : IsGeometricallyNodalCurveOver k C :=
  (isGeometricallyNodalCurveOver_iff_isNodalCurveOver k C).mpr h

end AlgebraicGeometry.Scheme
