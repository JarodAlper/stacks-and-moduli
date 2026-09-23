module

public import StacksAndModuli.API.ProperImmersion
public import StacksAndModuli.API.RepresentableValuativeCriterion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# The DVR-valuative criterion and specialization lifting

Mathlib's valuative criterion quantifies over all valuation rings.  The noetherian
criterion used in *Stacks and Moduli* instead quantifies over discrete valuation rings.
This file packages the part of that comparison which is independent of the difficult
existence theorem for DVRs realizing specializations:

* `DVRValuativeCriterion f` says that every DVR-valuative square over `f` has a unique
  lift;
* `DVRValuativeCriterion.of_comp_of_isSeparated` transfers this property from a
  composite `f ≫ g` to `f` when `g` is separated;
* `DVRRealizesSpecializations f` is the geometric input supplied by Proposition A.4.4
  (`prop:geometry-dvrs`) for finite-type morphisms of noetherian schemes;
* combining these two properties makes `f` specializing, and hence makes a
  quasi-compact immersion a closed immersion;
* a representation transports bijectivity of restriction from a DVR to its fraction
  field into the DVR-valuative criterion.

Thus the noetherian DVR reduction needed for projectivity of Hilbert and Quot is
isolated to the single geometric property `DVRRealizesSpecializations`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u v

/-- The unique-lifting part of the noetherian valuative criterion, restricted to
discrete valuation rings. -/
def DVRValuativeCriterion : MorphismProperty Scheme.{u} :=
  fun _ _ f ↦ ∀ sq : ValuativeCommSq f, IsDiscreteValuationRing sq.R →
    Nonempty (Unique sq.commSq.LiftStruct)

namespace DVRValuativeCriterion

/-- If a composite `f ≫ g` has unique DVR-valuative lifts and `g` is separated, then
`f` has unique DVR-valuative lifts.  Existence comes from the composite; separatedness
forces its proposed lift to agree with the given bottom morphism into the middle
scheme. -/
theorem of_comp_of_isSeparated {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated g] (h : DVRValuativeCriterion (f ≫ g)) :
    DVRValuativeCriterion f := by
  intro sq hdvr
  let _ : IsDiscreteValuationRing sq.R := hdvr
  let sqComp : ValuativeCommSq (f ≫ g) :=
    { R := sq.R
      K := sq.K
      i₁ := sq.i₁
      i₂ := sq.i₂ ≫ g
      commSq := ⟨by
        simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ g) sq.commSq.w⟩ }
  obtain ⟨U⟩ := h sqComp hdvr
  let sqG : ValuativeCommSq g :=
    { R := sq.R
      K := sq.K
      i₁ := sq.i₁ ≫ f
      i₂ := sq.i₂ ≫ g
      commSq := ⟨by
        simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ g) sq.commSq.w⟩ }
  let bottomLift : sqG.commSq.LiftStruct :=
    ⟨sq.i₂, sq.commSq.w.symm, rfl⟩
  let compositeLift : sqG.commSq.LiftStruct :=
    ⟨U.default.l ≫ f, by rw [← Category.assoc, U.default.fac_left],
      by rw [Category.assoc, U.default.fac_right]⟩
  have heq : compositeLift = bottomLift :=
    (IsSeparated.valuativeCriterion g sqG).allEq _ _
  have hright : U.default.l ≫ f = sq.i₂ :=
    congrArg CommSq.LiftStruct.l heq
  let default : sq.commSq.LiftStruct :=
    ⟨U.default.l, U.default.fac_left, hright⟩
  refine ⟨{ default := default, uniq := ?_ }⟩
  intro L
  let Lcomp : sqComp.commSq.LiftStruct :=
    ⟨L.l, L.fac_left, by
      simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ g) L.fac_right⟩
  refine CommSq.LiftStruct.ext ?_
  change L.l = U.default.l
  exact congrArg CommSq.LiftStruct.l (U.uniq Lcomp)

end DVRValuativeCriterion

/-- A realization by a DVR of one specialization `f(x) ⇝ y`: the generic point
maps to `x`, and the closed point maps to `y`. -/
structure DVRRealization {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y) where
  /-- The valuative square realizing the specialization. -/
  sq : ValuativeCommSq f
  /-- Its valuation ring is discrete. -/
  dvr : IsDiscreteValuationRing sq.R
  /-- The generic point maps to the prescribed point of the source. -/
  generic_eq : sq.i₁ (IsLocalRing.closedPoint sq.K) = x
  /-- The closed point maps to the prescribed specialization in the target. -/
  closed_eq : sq.i₂ (IsLocalRing.closedPoint sq.R) = y

/-- Background definition for Proposition A.4.4: every specialization out of an image point
of `f` is realized by a DVR-valuative square over `f`. The proposition supplies this property
for a finite-type morphism of noetherian schemes. -/
def DVRRealizesSpecializations {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  ∀ (x : X) (y : Y), Specializes (f x) y → Nonempty (DVRRealization f x y)

/-- DVR realization of specializations plus existence of DVR lifts makes a morphism
specializing. -/
theorem SpecializingMap.of_dvrValuativeCriterion {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hreal : DVRRealizesSpecializations f)
    (hvc : DVRValuativeCriterion f) :
    SpecializingMap f := by
  intro x y hxy
  obtain ⟨⟨sq, hdvr, hgeneric, hclosed⟩⟩ := hreal x y hxy
  let _ : IsDiscreteValuationRing sq.R := hdvr
  obtain ⟨U⟩ := hvc sq hdvr
  let l := U.default.l
  refine ⟨l (IsLocalRing.closedPoint sq.R), ?_, ?_⟩
  · have hs := (IsLocalRing.specializes_closedPoint
      (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))
        (IsLocalRing.closedPoint sq.K))).map l.continuous
    have hlb := congrArg (fun q ↦ q.base) U.default.fac_left
    have hlp := CategoryTheory.congr_fun hlb (IsLocalRing.closedPoint sq.K)
    change l (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))
      (IsLocalRing.closedPoint sq.K)) = sq.i₁ (IsLocalRing.closedPoint sq.K) at hlp
    exact (hlp.trans hgeneric) ▸ hs
  · have hlb := congrArg (fun q ↦ q.base) U.default.fac_right
    have hlp := CategoryTheory.congr_fun hlb (IsLocalRing.closedPoint sq.R)
    change f (l (IsLocalRing.closedPoint sq.R)) =
      sq.i₂ (IsLocalRing.closedPoint sq.R) at hlp
    exact hlp.trans hclosed

/-- A quasi-compact immersion satisfying the DVR criterion is closed as soon as DVRs
realize its specializations. -/
theorem IsClosedImmersion.of_dvrValuativeCriterion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] [QuasiCompact f]
    (hreal : DVRRealizesSpecializations f)
    (hvc : DVRValuativeCriterion f) :
    IsClosedImmersion f := by
  apply IsClosedImmersion.of_isPreimmersion f
  rw [← Set.image_univ]
  exact ((isClosedMap_iff_specializingMap f).mpr
    (SpecializingMap.of_dvrValuativeCriterion hreal hvc)) Set.univ isClosed_univ

namespace Scheme

/-- A representation turns bijectivity of restriction across every DVR generic point
into the DVR-valuative criterion for the representing scheme. -/
theorem dvrValuativeCriterion_of_representableBy_map_bijective
    {S : Scheme.{u}} {F : CategoryTheory.Functor (Over S)ᵒᵖ (Type v)} {Q : Over S}
    (h : F.RepresentableBy Q)
    (hbij : ∀ sq : ValuativeCommSq Q.hom, IsDiscreteValuationRing sq.R →
      Function.Bijective (F.map (valuativeOverFractionRingMap sq).op)) :
    DVRValuativeCriterion Q.hom :=
  fun sq hdvr ↦ nonempty_unique_lift_of_representableBy_map_bijective h sq (hbij sq hdvr)

end Scheme

end AlgebraicGeometry
