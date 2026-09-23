module

public import StacksAndModuli.API.AlgebraicSpaceCartesianFamily
public import StacksAndModuli.API.PresheafPrestackMapPullback

/-!
# Base change of unpointed algebraic-space families

`AlgebraicGeometry.MarkedAlgebraicSpaceOver.unpointedBaseChange` pulls an unpointed
algebraic-space family back along a morphism of base schemes, as a pullback of functors of
points.  This file collects what such a base change does to the data attached to the
family.

The geometric-fibre part is proved here in full: pasting the two pullback squares
identifies the fibre of the base change over a field-valued point `s` of the new base with
the fibre of the original family over `s ≫ f`, compatibly with the recovered structure
morphism to `Spec K`.  Consequently a scheme presentation of a geometric fibre transports,
and every presented-geometric-fibre condition is inherited by the base change.

The conditions on the structure morphism — properness, flatness and finite presentation of
the associated morphism of prestacks — are recorded here as separate obligations, one per
property.  Each is the standard statement that the property of a morphism of algebraic
stacks is stable under base change, specialized to a base change formed as a pullback of
functors of points.  `toBaseFunctor_unpointedBaseChange` puts that specialization in the
standard form: the structure morphism of the base change is, after precomposition with the
canonical equivalence `unpointedBaseChangeComparison`, the second projection of the
prestack fiber product.

## Main declarations

* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.fiberPresheafUnpointedBaseChangeIso`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.PresentedGeometricFiber.unpointedBaseChange`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.hasPresentedGeometricFibers_unpointedBaseChange`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.unpointedBaseChangeComparison`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.toBaseFunctor_unpointedBaseChange`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.isProper_unpointedBaseChange`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.flat_unpointedBaseChange`;
* `AlgebraicGeometry.MarkedAlgebraicSpaceOver.finitePresentation_unpointedBaseChange`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace MarkedAlgebraicSpaceOver

variable {S T : Scheme.{u}}

/-- Pasting the base-change square with the fibre square: the fibre of a base-changed
family over a field-valued point `s` of the new base is a fibre product of the original
family along `s ≫ f`. -/
theorem isPullback_fiberPresheaf_unpointedBaseChange
    (F : MarkedAlgebraicSpaceOver (Fin 0) S) (f : T ⟶ S) (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ T) :
    IsPullback
      (pullback.fst (F.unpointedBaseChange f).hom (yoneda.map s) ≫
        pullback.fst F.hom (yoneda.map f))
      (pullback.snd (F.unpointedBaseChange f).hom (yoneda.map s)) F.hom
      (yoneda.map (s ≫ f)) := by
  have h :=
    (IsPullback.of_hasPullback (F.unpointedBaseChange f).hom (yoneda.map s)).paste_horiz
      (F.isPullback_unpointedBaseChange f)
  rwa [← yoneda.map_comp] at h

/-- The geometric fibre of a base-changed family over a field-valued point `s` of the new
base is the geometric fibre of the original family over `s ≫ f`. -/
def fiberPresheafUnpointedBaseChangeIso (F : MarkedAlgebraicSpaceOver (Fin 0) S)
    (f : T ⟶ S) (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T) :
    (F.unpointedBaseChange f).fiberPresheaf K s ≅ F.fiberPresheaf K (s ≫ f) :=
  (F.isPullback_fiberPresheaf_unpointedBaseChange f K s).isoPullback

@[reassoc (attr := simp)]
theorem fiberPresheafUnpointedBaseChangeIso_inv_snd
    (F : MarkedAlgebraicSpaceOver (Fin 0) S) (f : T ⟶ S) (K : Type u) [Field K]
    (s : Spec (CommRingCat.of K) ⟶ T) :
    (F.fiberPresheafUnpointedBaseChangeIso f K s).inv ≫
        pullback.snd (F.unpointedBaseChange f).hom (yoneda.map s) =
      pullback.snd F.hom (yoneda.map (s ≫ f)) :=
  IsPullback.isoPullback_inv_snd _

namespace PresentedGeometricFiber

variable {F : MarkedAlgebraicSpaceOver (Fin 0) S} {K : Type u} [Field K]
  {s : Spec (CommRingCat.of K) ⟶ T}

/-- A scheme presentation of the geometric fibre of a family over `s ≫ f` presents the
geometric fibre of the base-changed family over `s`. -/
def unpointedBaseChange (f : T ⟶ S) (P : F.PresentedGeometricFiber K (s ≫ f)) :
    (F.unpointedBaseChange f).PresentedGeometricFiber K s where
  scheme := P.scheme
  iso := P.iso ≪≫ (F.fiberPresheafUnpointedBaseChangeIso f K s).symm

@[simp]
theorem scheme_unpointedBaseChange (f : T ⟶ S)
    (P : F.PresentedGeometricFiber K (s ≫ f)) :
    (P.unpointedBaseChange f).scheme = P.scheme :=
  rfl

/-- Transporting a presentation to the base-changed family does not change the recovered
structure morphism to the residue field. -/
@[simp]
theorem toBase_unpointedBaseChange (f : T ⟶ S)
    (P : F.PresentedGeometricFiber K (s ≫ f)) :
    (P.unpointedBaseChange f).toBase = P.toBase := by
  apply yoneda.map_injective
  rw [MarkedAlgebraicSpaceOver.PresentedGeometricFiber.yoneda_map_toBase,
    MarkedAlgebraicSpaceOver.PresentedGeometricFiber.yoneda_map_toBase]
  change (P.iso ≪≫ (F.fiberPresheafUnpointedBaseChangeIso f K s).symm).hom ≫ _ = _
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    fiberPresheafUnpointedBaseChangeIso_inv_snd]

end PresentedGeometricFiber

/-- A condition imposed on presented geometric fibres is inherited by every base change:
each geometric fibre of the base change is a geometric fibre of the original family. -/
theorem hasPresentedGeometricFibers_unpointedBaseChange
    {F : MarkedAlgebraicSpaceOver (Fin 0) S}
    {Q : MarkedGeometricFiberPredicate.{0, u} (Fin 0)}
    (h : F.HasPresentedGeometricFibers Q) (f : T ⟶ S) :
    (F.unpointedBaseChange f).HasPresentedGeometricFibers Q := by
  intro K _ _ s
  obtain ⟨P, hP⟩ := h K (s ≫ f)
  refine ⟨P.unpointedBaseChange f, ?_⟩
  have key : ∀ {t : P.scheme ⟶ Spec (CommRingCat.of K)}, t = P.toBase →
      ∀ m : Fin 0 → @Scheme.SectionOver P.scheme (Spec (CommRingCat.of K)) ⟨t⟩,
        @Q K _ _ P.scheme ⟨t⟩ m := by
    rintro t rfl m
    have hm : m = P.marking := funext fun i ↦ i.elim0
    rw [hm]
    exact hP
  exact key (P.toBase_unpointedBaseChange f) _

/-- The comparison from the prestack of the base-changed family to the prestack fiber
product of its structure morphism with the base morphism. -/
abbrev unpointedBaseChangeComparison (F : MarkedAlgebraicSpaceOver (Fin 0) S) (f : T ⟶ S) :
    BasedCategory.ofPresheaf (F.unpointedBaseChange f).total ⥤ᵇ
      BasedCategory.fiberProduct F.toBaseFunctor
        (BasedCategory.ofPresheaf.map (yoneda.map f)) :=
  BasedCategory.ofPresheafMapPullbackLift

/-- The comparison of a base change with the prestack fiber product is an equivalence. -/
theorem isEquivalence_unpointedBaseChangeComparison
    (F : MarkedAlgebraicSpaceOver (Fin 0) S) (f : T ⟶ S) :
    (F.unpointedBaseChangeComparison f).toFunctor.IsEquivalence :=
  BasedCategory.isEquivalence_ofPresheafMapPullbackLift

/-- The structure morphism of a base-changed family is the second projection of the
prestack fiber product of the structure morphism and the base morphism, precomposed with
the canonical equivalence of the previous lemma.  This puts a base change of families in
the standard form to which base-change stability of properties of morphisms of algebraic
stacks applies. -/
theorem toBaseFunctor_unpointedBaseChange (F : MarkedAlgebraicSpaceOver (Fin 0) S)
    (f : T ⟶ S) :
    (F.unpointedBaseChange f).toBaseFunctor =
      (F.unpointedBaseChangeComparison f).comp
        (BasedCategory.fiberProductSnd F.toBaseFunctor
          (BasedCategory.ofPresheaf.map (yoneda.map f))) :=
  rfl

/-- Properness of the structure morphism of an unpointed algebraic-space family is
inherited by every base change of the family.

Recorded obligation: properness of a morphism of algebraic stacks is stable under base
change.  By `toBaseFunctor_unpointedBaseChange` and
`isEquivalence_unpointedBaseChangeComparison` this is exactly the two general facts that
`AlgebraicGeometry.BasedFunctor.IsProper` passes to `BasedCategory.fiberProductSnd` and is
unchanged by precomposition with an equivalence of prestacks; neither is available in the
library today. -/
theorem isProper_unpointedBaseChange (F : MarkedAlgebraicSpaceOver (Fin 0) S) (f : T ⟶ S)
    (h : BasedFunctor.IsProper F.toBaseFunctor) :
    BasedFunctor.IsProper (F.unpointedBaseChange f).toBaseFunctor := by
  sorry

/-- Flatness of the structure morphism of an unpointed algebraic-space family is inherited
by every base change of the family.

Recorded obligation: flatness of a morphism of algebraic stacks is stable under base
change.  Through `toBaseFunctor_unpointedBaseChange` this asks that
`AlgebraicGeometry.BasedFunctor.HasProperty` for the smooth-local scheme property of
flatness passes to `BasedCategory.fiberProductSnd` and is unchanged by precomposition with
an equivalence of prestacks. -/
theorem flat_unpointedBaseChange (F : MarkedAlgebraicSpaceOver (Fin 0) S) (f : T ⟶ S)
    (h : BasedFunctor.Flat F.toBaseFunctor) :
    BasedFunctor.Flat (F.unpointedBaseChange f).toBaseFunctor := by
  sorry

/-- Finite presentation of the structure morphism of an unpointed algebraic-space family
is inherited by every base change of the family.

Recorded obligation: finite presentation of a morphism of algebraic stacks is stable under
base change.  Through `toBaseFunctor_unpointedBaseChange` this splits into the same
statement for local finite presentation, for quasi-compactness — where
`AlgebraicGeometry.BasedFunctor.QuasiCompact.fiberProductSnd` already supplies the base
change half — and for quasi-separatedness. -/
theorem finitePresentation_unpointedBaseChange (F : MarkedAlgebraicSpaceOver (Fin 0) S)
    (f : T ⟶ S) (h : BasedFunctor.FinitePresentation F.toBaseFunctor) :
    BasedFunctor.FinitePresentation (F.unpointedBaseChange f).toBaseFunctor := by
  sorry

end MarkedAlgebraicSpaceOver

end AlgebraicGeometry
