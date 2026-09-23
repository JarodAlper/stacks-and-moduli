module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Reduced closed subschemes

This file packages the reduced induced subscheme on an arbitrary closed subset of a
scheme.  It also gives a scheme-theoretic predicate saying that a morphism is a single
reduced point at a specified point of its target.

## Main definitions

* `AlgebraicGeometry.Scheme.reducedClosedSubscheme`: the reduced induced subscheme on a
  closed subset.
* `AlgebraicGeometry.Scheme.reducedClosedSubschemeι`: its canonical closed immersion.
* `AlgebraicGeometry.Scheme.Hom.IsSingleReducedPointAt`: a morphism identified with the
  canonical residue-field point at a specified target point.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal`: the
  vanishing-ideal subscheme of a closed set is reduced.
* `AlgebraicGeometry.Scheme.Hom.range_eq_singleton_of_isSingleReducedPointAt`: a single
  reduced point has the expected singleton range.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The subscheme cut out by the vanishing ideal of a closed set is reduced. -/
theorem IdealSheafData.isReduced_subscheme_vanishingIdeal
    {X : Scheme.{u}} (Z : Closeds X) :
    IsReduced (IdealSheafData.vanishingIdeal Z).subscheme := by
  let I := IdealSheafData.vanishingIdeal Z
  have hU (U : X.affineOpens) :
      IsReduced (I.subschemeCover.openCover.X U) := by
    change IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
    have hradical : (I.ideal U).IsRadical := by
      rw [show I.ideal U = PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' Z) from
        IdealSheafData.vanishingIdeal_ideal Z U]
      exact PrimeSpectrum.isRadical_vanishingIdeal _
    let _ : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mp hradical
    infer_instance
  let _ (U : I.subschemeCover.openCover.I₀) :
      IsReduced (I.subschemeCover.openCover.X U) := hU U
  exact IsReduced.of_openCover I.subscheme I.subschemeCover.openCover

/-- The reduced induced closed subscheme on a closed subset of a scheme. -/
def reducedClosedSubscheme (X : Scheme.{u}) (Z : Closeds X) : Scheme.{u} :=
  (IdealSheafData.vanishingIdeal Z).subscheme

/-- The canonical inclusion of a reduced induced closed subscheme. -/
def reducedClosedSubschemeι (X : Scheme.{u}) (Z : Closeds X) :
    X.reducedClosedSubscheme Z ⟶ X :=
  (IdealSheafData.vanishingIdeal Z).subschemeι

/-- The inclusion of a reduced induced closed subscheme is the subtype inclusion on
points. -/
@[simp]
theorem reducedClosedSubschemeι_apply (X : Scheme.{u}) (Z : Closeds X)
    (x : X.reducedClosedSubscheme Z) :
    X.reducedClosedSubschemeι Z x = x.1 :=
  rfl

/-- The image of the reduced induced closed subscheme is its prescribed closed set. -/
@[simp]
theorem range_reducedClosedSubschemeι (X : Scheme.{u}) (Z : Closeds X) :
    Set.range (X.reducedClosedSubschemeι Z) = Z := by
  exact (IdealSheafData.range_subschemeι
    (IdealSheafData.vanishingIdeal Z)).trans
      (IdealSheafData.coe_support_vanishingIdeal Z)

/-- The canonical inclusion of a reduced induced closed subscheme is a closed
immersion. -/
instance reducedClosedSubschemeι_isClosedImmersion (X : Scheme.{u}) (Z : Closeds X) :
    IsClosedImmersion (X.reducedClosedSubschemeι Z) := by
  dsimp only [reducedClosedSubschemeι]
  infer_instance

/-- The reduced induced closed subscheme is reduced. -/
instance reducedClosedSubscheme_isReduced (X : Scheme.{u}) (Z : Closeds X) :
    IsReduced (X.reducedClosedSubscheme Z) :=
  IdealSheafData.isReduced_subscheme_vanishingIdeal Z

/-- A morphism `f : Z ⟶ X` is the single reduced point at `x : X` when its source is
isomorphic to `Spec κ(x)` compatibly with the canonical residue-field morphism to `X`.

The compatibility makes this stronger than merely asking that the set-theoretic range
of `f` be the singleton `{x}`: it records the reduced scheme structure. -/
def Hom.IsSingleReducedPointAt {Z X : Scheme.{u}} (f : Z ⟶ X) (x : X) : Prop :=
  ∃ e : Z ≅ Spec (X.residueField x),
    e.hom ≫ X.fromSpecResidueField x = f

/-- The defining residue-field-point characterization of a single reduced point. -/
lemma Hom.isSingleReducedPointAt_iff {Z X : Scheme.{u}} (f : Z ⟶ X) (x : X) :
    f.IsSingleReducedPointAt x ↔
      ∃ e : Z ≅ Spec (X.residueField x),
        e.hom ≫ X.fromSpecResidueField x = f :=
  Iff.rfl

/-- A morphism which is the single reduced point at `x` has singleton range `{x}`. -/
theorem Hom.range_eq_singleton_of_isSingleReducedPointAt {Z X : Scheme.{u}}
    {f : Z ⟶ X} {x : X} (h : f.IsSingleReducedPointAt x) :
    Set.range f = {x} := by
  obtain ⟨e, he⟩ := h
  rw [← he]
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    simp
  · intro hy
    have hyx : y = x := Set.mem_singleton_iff.mp hy
    subst y
    let z : Z := e.inv (IsLocalRing.closedPoint (X.residueField x))
    refine ⟨z, ?_⟩
    simp [z]

end AlgebraicGeometry.Scheme
