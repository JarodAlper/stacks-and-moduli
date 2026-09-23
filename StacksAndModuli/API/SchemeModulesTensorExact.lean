module

public import StacksAndModuli.API.SchemeModulesTensorFiniteCoproduct
public import StacksAndModuli.API.SchemeModulesTensorLocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Exactness of tensoring by a locally trivial module sheaf

Tensoring sheaves of modules on a scheme is right exact without a flatness hypothesis.
This file proves that the functor `tensorRightFunctor L` preserves all small colimits.
The proof compares tensoring after module sheafification with sheafification after
presheaf tensoring; the comparison is invertible because tensor products preserve the
local equivalences inverted by sheafification.

If `L` is trivial on an open cover, tensoring by `L` also preserves monomorphisms.  The
standard abelian-category criterion then shows that it preserves homology and finite
limits, hence sends short exact sequences to short exact sequences.

Main declarations:
- `AlgebraicGeometry.Scheme.Modules.tensorRightFunctorSheafificationIso`;
- `AlgebraicGeometry.Scheme.Modules.tensorRightFunctor_preservesColimits`;
- `AlgebraicGeometry.Scheme.Modules.tensorRightFunctor_preservesFiniteLimits_of_iSup_iso_unit`;
- `CategoryTheory.ShortComplex.ShortExact.map_tensorRightFunctor_of_iSup_iso_unit`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Comparing the two orders of tensoring a module presheaf with a sheaf and applying
module sheafification.  Its components are sheafifications of the sheafification unit
tensor the fixed right factor. -/
noncomputable def tensorRightFunctorSheafificationComparison (L : X.Modules) :
    tensorRight L.val ⋙ sheafification X ⟶
      sheafification X ⋙ tensorRightFunctor L where
  app P := (sheafification X).map
    ((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P ▷ L.val)
  naturality {P Q} f := by
    change (sheafification X).map (f ▷ L.val) ≫
        (sheafification X).map
          ((_root_.PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app Q ▷ L.val) =
      (sheafification X).map
          ((_root_.PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app P ▷ L.val) ≫
        (sheafification X).map (((sheafification X).map f).val ▷ L.val)
    rw [← (sheafification X).map_comp, ← (sheafification X).map_comp]
    congr 1
    rw [← MonoidalCategory.comp_whiskerRight,
      ← MonoidalCategory.comp_whiskerRight]
    exact congrArg (fun k ↦ k ▷ L.val)
      ((_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.naturality f)

/-- Sheafifying after presheaf tensoring is naturally isomorphic to tensoring after
module sheafification. -/
noncomputable def tensorRightFunctorSheafificationIso (L : X.Modules) :
    tensorRight L.val ⋙ sheafification X ≅
      sheafification X ⋙ tensorRightFunctor L := by
  let W : MorphismProperty X.PresheafOfModules :=
    (Opens.grothendieckTopology X).W.inverseImage
      (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)
  letI : W.IsMonoidal := by
    exact _root_.PresheafOfModules.localEquivalencesIsMonoidal X.presheaf
  letI : (sheafification X).IsLocalization W :=
    inferInstanceAs ((_root_.PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).IsLocalization
        ((Opens.grothendieckTopology X).W.inverseImage
          (_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj)))
  letI (P : X.PresheafOfModules) :
      IsIso ((tensorRightFunctorSheafificationComparison L).app P) := by
    let adj := _root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)
    have hu : W (adj.unit.app P) := by
      change (Opens.grothendieckTopology X).W
        ((_root_.PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
          (adj.unit.app P))
      simpa [adj] using
        (Opens.grothendieckTopology X).W_toSheafify P.presheaf
    have huL : W (adj.unit.app P ▷ L.val) :=
      W.whiskerRight_mem (adj.unit.app P) hu L.val
    exact Localization.inverts (sheafification X) W
      (adj.unit.app P ▷ L.val) huL
  letI : IsIso (tensorRightFunctorSheafificationComparison L) := by
    apply NatIso.isIso_of_isIso_app
  exact asIso (tensorRightFunctorSheafificationComparison L)

/-- Tensoring sheaves of modules in the right factor preserves all small colimits.

Colimits of module sheaves are obtained by reflecting presheaf colimits.  The comparison
isomorphism above reduces preservation to presheaf tensoring and sheafification, both left
adjoints. -/
noncomputable instance tensorRightFunctor_preservesColimits (L : X.Modules) :
    PreservesColimitsOfSize.{u, u} (tensorRightFunctor L) := by
  letI : (sheafification X).IsLeftAdjoint :=
    (_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).isLeftAdjoint
  letI (G : X.PresheafOfModules) :
      PreservesColimitsOfSize.{u, u} (tensorRight G) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u}
      (tensorRight (show _root_.PresheafOfModules.{u}
        (X.presheaf ⋙ forget₂ CommRingCat RingCat) from G)))
  constructor
  intro J _
  constructor
  intro K
  let R := SheafOfModules.forget X.ringCatSheaf
  let T := tensorRight L.val ⋙ sheafification X
  letI : PreservesColimit (K ⋙ R) T := inferInstance
  letI : PreservesColimit (K ⋙ R)
      (sheafification X ⋙ tensorRightFunctor L) :=
    preservesColimit_of_natIso (K ⋙ R)
      (tensorRightFunctorSheafificationIso L)
  letI : PreservesColimit (K ⋙ R)
      (reflector R ⋙ tensorRightFunctor L) := by
    change PreservesColimit (K ⋙ R)
      (sheafification X ⋙ tensorRightFunctor L)
    infer_instance
  exact CategoryTheory.Limits.preservesColimit_of_reflector_comp
    R (tensorRightFunctor L) K

/-- If the right tensor factor is trivial on an open cover, its tensor functor preserves
monomorphisms. -/
theorem tensorRightFunctor_preservesMonomorphisms_of_iSup_iso_unit
    (L : X.Modules) {J : Type u} (U : J → X.Opens) (hU : IsOpenCover U)
    (e : ∀ j, (restrictFunctor (U j).ι).obj L ≅
      SheafOfModules.unit (U j).toScheme.ringCatSheaf) :
    (tensorRightFunctor L).PreservesMonomorphisms where
  preserves f _ := by
    change Mono (tensorMapLeft f L)
    exact tensorMapLeft_mono_of_iSup_iso_unit f U hU e

/-- If the right tensor factor is trivial on an open cover, its tensor functor preserves
homology. -/
theorem tensorRightFunctor_preservesHomology_of_iSup_iso_unit
    (L : X.Modules) {J : Type u} (U : J → X.Opens) (hU : IsOpenCover U)
    (e : ∀ j, (restrictFunctor (U j).ι).obj L ≅
      SheafOfModules.unit (U j).toScheme.ringCatSheaf) :
    (tensorRightFunctor L).PreservesHomology := by
  letI : (tensorRightFunctor L).PreservesMonomorphisms :=
    tensorRightFunctor_preservesMonomorphisms_of_iSup_iso_unit L U hU e
  exact (tensorRightFunctor L).preservesHomology_of_preservesMonos_and_cokernels

/-- If the right tensor factor is trivial on an open cover, its tensor functor preserves
finite limits. -/
theorem tensorRightFunctor_preservesFiniteLimits_of_iSup_iso_unit
    (L : X.Modules) {J : Type u} (U : J → X.Opens) (hU : IsOpenCover U)
    (e : ∀ j, (restrictFunctor (U j).ι).obj L ≅
      SheafOfModules.unit (U j).toScheme.ringCatSheaf) :
    PreservesFiniteLimits (tensorRightFunctor L) := by
  letI : (tensorRightFunctor L).PreservesHomology :=
    tensorRightFunctor_preservesHomology_of_iSup_iso_unit L U hU e
  exact (tensorRightFunctor L).preservesFiniteLimits_of_preservesHomology

end AlgebraicGeometry.Scheme.Modules

namespace CategoryTheory.ShortComplex.ShortExact

/-- Tensoring a short exact sequence of module sheaves by a sheaf which is trivial on an
open cover gives another short exact sequence. -/
theorem map_tensorRightFunctor_of_iSup_iso_unit {X : Scheme.{u}}
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (L : X.Modules) {J : Type u} (U : J → X.Opens) (hU : IsOpenCover U)
    (e : ∀ j, (Scheme.Modules.restrictFunctor (U j).ι).obj L ≅
      SheafOfModules.unit (U j).toScheme.ringCatSheaf) :
    (S.map (Scheme.Modules.tensorRightFunctor L)).ShortExact := by
  letI : PreservesFiniteLimits (Scheme.Modules.tensorRightFunctor L) :=
    Scheme.Modules.tensorRightFunctor_preservesFiniteLimits_of_iSup_iso_unit
      L U hU e
  exact hS.map_of_exact (Scheme.Modules.tensorRightFunctor L)

end CategoryTheory.ShortComplex.ShortExact

end
