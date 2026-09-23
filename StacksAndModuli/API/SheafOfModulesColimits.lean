module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Monad.Limits
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Finite colimits of sheaves of modules

Mathlib constructs sheafification for presheaves of modules and proves that it is left
adjoint to the fully faithful inclusion of sheaves of modules into presheaves of modules.
This makes sheaves of modules a reflective subcategory.  The general reflective-subcategory
construction therefore supplies their colimits.

This file also proves that forgetting a sheaf of modules to its underlying sheaf of abelian
groups preserves finite colimits.  The key point is that module sheafification followed by
forgetting is naturally isomorphic to ordinary abelian-group sheafification, while the
underlying-abelian-presheaf functor preserves colimits.

Main declarations:
- `CategoryTheory.Limits.preservesColimit_of_reflector_comp`: descent of preservation from
  the composite with a reflector.
- the `Reflective`, `HasFiniteColimits`, and `PreservesFiniteColimits` instances for
  `SheafOfModules.forget` and `SheafOfModules.toSheaf`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace CategoryTheory.Limits

universe vJ uJ vC uC vD uD vE uE

/-- Let `R : D ⥤ C` exhibit `D` as a reflective subcategory, and let `F : D ⥤ E`.
If `reflector R ⋙ F` preserves the colimit of the ambient diagram `K ⋙ R`, then `F`
preserves the colimit of `K`.

The proof compares `K` with its reflected ambient diagram by the (invertible) counit, and
then transports the preserved colimit across the resulting isomorphisms of cocones. -/
theorem preservesColimit_of_reflector_comp
    {C : Type uC} {D : Type uD} {E : Type uE} {J : Type uJ}
    [Category.{vC} C] [Category.{vD} D] [Category.{vE} E] [Category.{vJ} J]
    (R : D ⥤ C) [Reflective R] (F : D ⥤ E) (K : J ⥤ D)
    [HasColimit (K ⋙ R)] [PreservesColimit (K ⋙ R) (reflector R ⋙ F)] :
    PreservesColimit K F :=
  { preserves := fun {c} hc => by
      let L := reflector R
      let cC := colimit.cocone (K ⋙ R)
      let cL := L.mapCocone cC
      let e : K ⋙ R ⋙ L ≅ K :=
        (Functor.isoWhiskerLeft K (asIso (reflectorAdjunction R).counit) :) ≪≫
          K.rightUnitor
      let cK := (Cocone.precompose e.inv).obj cL
      have hcL : IsColimit cL := isColimitOfPreserves L (colimit.isColimit _)
      have hcK : IsColimit cK := (IsColimit.precomposeInvEquiv e cL).symm hcL
      let cLF := (L ⋙ F).mapCocone cC
      have hcLF : IsColimit cLF :=
        isColimitOfPreserves (L ⋙ F) (colimit.isColimit _)
      let eF : (K ⋙ R ⋙ L) ⋙ F ≅ K ⋙ F := Functor.isoWhiskerRight e F
      let cKF := (Cocone.precompose eF.inv).obj cLF
      have hcKF : IsColimit cKF :=
        (IsColimit.precomposeInvEquiv eF cLF).symm hcLF
      have hi : cKF ≅ F.mapCocone cK := by
        refine Cocone.ext (Iso.refl _) ?_
        intro j
        simp [cKF, cLF, cK, eF, e]
        rfl
      have hmapcK : IsColimit (F.mapCocone cK) := hcKF.ofIsoColimit hi
      exact ⟨hmapcK.ofIsoColimit
        ((Cocone.functoriality K F).mapIso (hcK.uniqueUpToIso hc))⟩ }

end CategoryTheory.Limits

namespace SheafOfModules

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

/-- Sheaves of modules form a reflective subcategory of presheaves of modules. -/
noncomputable instance reflectiveForget : Reflective (forget.{u} R) where
  L := PresheafOfModules.sheafification (𝟙 R.obj)
  adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)

/-- Sheaves of modules have finite colimits, obtained by sheafifying the corresponding
colimits of presheaves of modules. -/
noncomputable instance hasFiniteColimits : HasFiniteColimits (SheafOfModules.{u} R) :=
  ⟨fun _ => CategoryTheory.hasColimitsOfShape_of_reflective (forget.{u} R)⟩

/-- Module sheafification followed by forgetting to abelian sheaves preserves finite
colimits. -/
noncomputable instance sheafificationCompToSheafPreservesFiniteColimits :
    PreservesFiniteColimits
      (PresheafOfModules.sheafification (𝟙 R.obj) ⋙ toSheaf R) := by
  apply preservesFiniteColimits_of_natIso
    (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm

/-- Forgetting a sheaf of modules to its underlying sheaf of abelian groups preserves
finite colimits. -/
noncomputable instance toSheafPreservesFiniteColimits :
    PreservesFiniteColimits (toSheaf.{u} R) where
  preservesFiniteColimits J := by
    intros
    constructor
    intro K
    letI : PreservesColimit (K ⋙ forget.{u} R)
        (reflector (forget.{u} R) ⋙ toSheaf.{u} R) := by
      change PreservesColimit (K ⋙ forget.{u} R)
        (PresheafOfModules.sheafification (𝟙 R.obj) ⋙ toSheaf R)
      infer_instance
    exact CategoryTheory.Limits.preservesColimit_of_reflector_comp
      (forget.{u} R) (toSheaf.{u} R) K

end SheafOfModules
