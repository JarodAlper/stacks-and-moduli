module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# The pushforward adjunction for sheaves of modules on schemes

Supporting API with no Stacks Project counterpart. Mathlib provides
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` and, from it, the instance
`(Scheme.Modules.pushforward f).IsRightAdjoint`. The §2.1 and §3.1 files work directly with the
underlying `SheafOfModules.pushforward f.toRingCatSheafHom`, whose `IsRightAdjoint` instance is
stated in `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean` under hypotheses
that instance search does not discharge in the scheme setting.

Restating it here, once, removes the need for a local `letI` at every use site.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

/-- The pushforward of sheaves of modules along a morphism of schemes is a right adjoint. -/
instance AlgebraicGeometry.Scheme.Hom.sheafOfModules_pushforward_isRightAdjoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  inferInstanceAs ((AlgebraicGeometry.Scheme.Modules.pushforward f).IsRightAdjoint)

/-- The preimage functor on opens along any continuous map is final: every comma category
`StructuredArrow U (Opens.map f)` is connected, since it contains `⊤` and every object maps
to it. This is the `[F.Final]` hypothesis of Mathlib's
`IsIso (SheafOfModules.pullbackObjUnitToUnit φ)`. -/
instance TopologicalSpace.Opens.final_map {X Y : TopCat.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f).Final where
  out d := by
    letI : Nonempty (StructuredArrow d (TopologicalSpace.Opens.map f)) :=
      ⟨StructuredArrow.mk
        (homOfLE le_top : d ⟶ (TopologicalSpace.Opens.map f).obj ⊤)⟩
    apply IsConnected.of_induct
      (j₀ := StructuredArrow.mk
        (homOfLE le_top : d ⟶ (TopologicalSpace.Opens.map f).obj ⊤))
    intro p hp₀ hstep j
    exact (hstep (StructuredArrow.homMk (homOfLE le_top)
      (Subsingleton.elim _ _))).mpr hp₀

/-- Pullback of the unit module sheaf along a morphism of schemes is the unit.

Mathlib proves `IsIso (SheafOfModules.pullbackObjUnitToUnit φ)` under a `[F.Final]`
hypothesis on the site functor; `TopologicalSpace.Opens.final_map` discharges it. -/
instance isIso_pullbackObjUnitToUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
  inferInstance

/-- For an open immersion, pullback of sheaves of modules is fully faithful, so the counit of
the pullback–pushforward adjunction is an isomorphism.

OBLIGATION. This is the module-sheaf analogue of `IsOpenImmersion` being fully faithful on
quasi-coherent data. Mathlib has the adjunction
(`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`) but not this invertibility.
Proof route: over an open `U ⊆ X`, `f_* f^* M` agrees with `M` on opens contained in `U`, and
both the unit and counit are computed sectionwise there. -/
instance isIso_counit_pullbackPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : X.Modules) :
    IsIso ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M) := by
  haveI : IsIso (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).counit :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).counit_isIso_of_R_fully_faithful
  infer_instance
