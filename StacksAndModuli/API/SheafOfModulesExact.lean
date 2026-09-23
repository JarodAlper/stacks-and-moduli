module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The forgetful functor from sheaves of modules to abelian sheaves is exact

Mathlib registers `PreservesFiniteLimits (SheafOfModules.toSheaf R)`
(`Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean`) but not the colimit half, so
`ShortComplex.ShortExact.map_of_exact` does not apply and a short exact sequence of sheaves
of modules cannot be transported to abelian sheaves — which is what every cohomological
argument needs, since `CategoryTheory.Sheaf.H` is defined on abelian sheaves.

This file supplies the missing half. The proof is short once the right three facts are
lined up:

* `SheafOfModules R` is reflective in `PresheafOfModules R.obj`: the counit of
  `PresheafOfModules.sheafificationAdjunction` is an isomorphism, so every diagram
  `F : K ⥤ SheafOfModules R` is isomorphic to `(F ⋙ forget R) ⋙ sheafification`.
* `PresheafOfModules.sheafificationCompToSheaf` says
  `sheafification ⋙ toSheaf ≅ toPresheaf ⋙ presheafToSheaf` — and it is `Iso.refl`.
* Both `PresheafOfModules.toPresheaf` (finite colimits, Mathlib instance) and
  `presheafToSheaf` (all colimits, being a left adjoint) preserve colimits.

## Main results

* `CategoryTheory.Limits.preservesColimit_comp_left`: if `H` preserves the colimit of `D`
  and `H ⋙ G` does too, then `G` preserves the colimit of `D ⋙ H`. This is the converse
  direction of `comp_preservesColimit`, and is what transports colimit preservation across
  a reflection.
* `SheafOfModules.toSheaf_preservesFiniteColimits`.
* `SheafOfModules.shortExact_map_toSheaf`: a short exact sequence of sheaves of modules
  stays short exact after forgetting the module structure.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe w' w v v' u' u

open CategoryTheory Limits

namespace CategoryTheory.Limits

/-- The converse of `comp_preservesColimit`: if `H` preserves the colimit of `D`, and the
composite `H ⋙ G` preserves it as well, then `G` preserves the colimit of `D ⋙ H`.

This is what lets colimit preservation be checked upstream of a reflection: to see that
`G` preserves colimits on a reflective subcategory it suffices to see that `L ⋙ G` does,
where `L` is the reflector. -/
lemma preservesColimit_comp_left {K : Type*} [Category K] {A : Type*} [Category A]
    {B : Type*} [Category B] {E : Type*} [Category E]
    (D : K ⥤ A) (H : A ⥤ B) (G : B ⥤ E) [HasColimit D]
    [PreservesColimit D H] [PreservesColimit D (H ⋙ G)] :
    PreservesColimit (D ⋙ H) G := by
  refine preservesColimit_of_preserves_colimit_cocone
    (isColimitOfPreserves H (colimit.isColimit D)) ?_
  exact isColimitOfPreserves (H ⋙ G) (colimit.isColimit D)

end CategoryTheory.Limits

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **The forgetful functor to abelian sheaves preserves finite colimits.** -/
noncomputable instance toSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{v} R) where
  preservesFiniteColimits K _ _ := by
    constructor
    intro F
    have e : F ≅ (F ⋙ SheafOfModules.forget R) ⋙
        PresheafOfModules.sheafification (𝟙 R.obj) :=
      Functor.isoWhiskerLeft F
        (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm
    have : PreservesColimit (F ⋙ SheafOfModules.forget R)
        (PresheafOfModules.sheafification (𝟙 R.obj) ⋙ SheafOfModules.toSheaf.{v} R) :=
      preservesColimit_of_natIso _ (PresheafOfModules.sheafificationCompToSheaf _).symm
    have : PreservesColimit ((F ⋙ SheafOfModules.forget R) ⋙
        PresheafOfModules.sheafification (𝟙 R.obj)) (SheafOfModules.toSheaf.{v} R) :=
      preservesColimit_comp_left _ _ _
    exact preservesColimit_of_iso_diagram _ e.symm

/-- **The forgetful functor to abelian sheaves is exact**, so a short exact sequence of
sheaves of modules stays short exact after forgetting the module structure. -/
lemma shortExact_map_toSheaf {S : ShortComplex (SheafOfModules.{v} R)}
    (hS : S.ShortExact) : (S.map (SheafOfModules.toSheaf.{v} R)).ShortExact :=
  hS.map_of_exact _

end SheafOfModules
