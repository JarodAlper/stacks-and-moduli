module

public import StacksAndModuli.API.RepresentableByTransport
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Valuative criteria for represented presheaves

For a presheaf on schemes over `S` represented by `Q`, restriction from a valuation
ring to its fraction field is bijective exactly when the structure morphism of `Q`
satisfies the valuative criterion.  This packages the Yoneda bookkeeping common to
moduli-space properness arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe u v

namespace Scheme

/-- The morphism in `Over S` from the generic point of a valuative square to its
valuation-ring point. -/
noncomputable def valuativeOverFractionRingMap {S : Scheme.{u}} {Q : Over S}
    (sq : ValuativeCommSq Q.hom) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.i₂) ⟶
      Over.mk sq.i₂ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) rfl

/-- For one valuative square, a representation turns bijectivity on its generic-point
restriction map into a unique lift. -/
theorem nonempty_unique_lift_of_representableBy_map_bijective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v} {Q : Over S}
    (h : F.RepresentableBy Q) (sq : ValuativeCommSq Q.hom)
    (hbij : Function.Bijective (F.map (valuativeOverFractionRingMap sq).op)) :
    Nonempty (Unique sq.commSq.LiftStruct) := by
  let j := valuativeOverFractionRingMap sq
  let xK : Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K)) ≫ sq.i₂) ⟶ Q :=
    Over.homMk sq.i₁ sq.commSq.w
  have hj := (h.map_bijective_iff_precomp j).mp hbij
  obtain ⟨l, hl⟩ := hj.2 xK
  refine ⟨{ default := ⟨l.left, ?_, l.w⟩, uniq := ?_ }⟩
  · have hl' := congrArg CommaMorphism.left hl
    exact hl'
  · intro l'
    apply CommSq.LiftStruct.ext
    let lOver' : Over.mk sq.i₂ ⟶ Q := Over.homMk l'.l l'.fac_right
    change lOver'.left = l.left
    apply congrArg CommaMorphism.left
    apply hj.1
    apply CostructuredArrow.hom_ext
    have hl' := congrArg CommaMorphism.left hl
    exact l'.fac_left.trans hl'.symm

/-- A representation turns bijectivity on every valuation-ring generic point into the
valuative criterion for the representing scheme. -/
theorem valuativeCriterion_of_representableBy_map_bijective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v} {Q : Over S}
    (h : F.RepresentableBy Q)
    (hbij : ∀ sq : ValuativeCommSq Q.hom,
      Function.Bijective (F.map (valuativeOverFractionRingMap sq).op)) :
    ValuativeCriterion Q.hom :=
  fun sq ↦ nonempty_unique_lift_of_representableBy_map_bijective h sq (hbij sq)

/-- A represented presheaf with bijective restriction across every valuation ring is
represented by a proper scheme as soon as the standard finiteness hypotheses hold. -/
theorem isProper_of_representableBy_map_bijective
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v} {Q : Over S}
    [QuasiCompact Q.hom] [QuasiSeparated Q.hom] [LocallyOfFiniteType Q.hom]
    (h : F.RepresentableBy Q)
    (hbij : ∀ sq : ValuativeCommSq Q.hom,
      Function.Bijective (F.map (valuativeOverFractionRingMap sq).op)) :
    IsProper Q.hom :=
  IsProper.of_valuativeCriterion Q.hom
    (valuativeCriterion_of_representableBy_map_bijective h hbij)

end Scheme

end AlgebraicGeometry
