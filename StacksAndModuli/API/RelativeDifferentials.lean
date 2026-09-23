module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Relative differentials of schemes

For a morphism of schemes `f : X ⟶ S`, the inverse-image presheaf of
`\mathcal O_S` maps to `\mathcal O_X`.  Applying the presheaf-level Kähler
differential construction and then sheafifying gives the relative differential
sheaf `\Omega_{X/S}`.

Mathlib supplies all three categorical ingredients separately: pullback of
presheaves, Kähler differentials of a morphism of ring-valued presheaves, and
sheafification of presheaves of modules.  This file assembles them for schemes.

Main declarations:

* `AlgebraicGeometry.Scheme.Hom.relativeBasePresheaf`: the inverse-image
  presheaf `f^{-1}\mathcal O_S`;
* `AlgebraicGeometry.Scheme.Hom.relativeStructureMap`: the canonical map
  `f^{-1}\mathcal O_S ⟶ \mathcal O_X`;
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsPresheaf`: the presheaf of
  Kähler differentials of this map;
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`: its sheafification,
  the sheaf `\Omega_{X/S}`;
* `AlgebraicGeometry.Scheme.Hom.relativeDifferentialsDerivation`: the universal
  derivation into `\Omega_{X/S}`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

namespace Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The inverse-image presheaf of rings `f^{-1}\mathcal O_S` on `X`.

This is the left adjoint pullback of presheaves along the continuous map
underlying `f`; it is deliberately a presheaf, since sheafification is performed
only after forming Kähler differentials. -/
noncomputable def relativeBasePresheaf :
    TopCat.Presheaf CommRingCat X :=
  (TopCat.Presheaf.pullback CommRingCat f.base).obj S.presheaf

/-- The canonical morphism `f^{-1}\mathcal O_S ⟶ \mathcal O_X`, obtained by
adjunction from the structure morphism `\mathcal O_S ⟶ f_*\mathcal O_X` of
the scheme map `f`. -/
noncomputable def relativeStructureMap :
    f.relativeBasePresheaf ⟶ X.presheaf :=
  (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).homEquiv
    S.presheaf X.presheaf |>.symm f.c

/-- The structure map from the inverse-image presheaf is adjoint to the
structure map of the scheme morphism. -/
lemma pullbackUnit_comp_relativeStructureMap :
    (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app
        S.presheaf ≫
      (TopCat.Presheaf.pushforward CommRingCat f.base).map
        f.relativeStructureMap =
      f.c := by
  dsimp only [relativeStructureMap, relativeBasePresheaf]
  let adj := TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base
  calc
    _ = adj.homEquiv S.presheaf X.presheaf
        ((adj.homEquiv S.presheaf X.presheaf).symm f.c) :=
      (adj.homEquiv_unit S.presheaf X.presheaf _).symm
    _ = f.c := Equiv.apply_symm_apply _ _

/-- The presheaf of Kähler differentials of
`f^{-1}\mathcal O_S ⟶ \mathcal O_X`. -/
noncomputable def relativeDifferentialsPresheaf : X.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
    f.relativeStructureMap

/-- The relative differential sheaf `\Omega_{X/S}`: the sheafification of the
presheaf of Kähler differentials of
`f^{-1}\mathcal O_S ⟶ \mathcal O_X`. -/
noncomputable def relativeDifferentials : X.Modules :=
  (_root_.PresheafOfModules.sheafification
    (𝟙 X.ringCatSheaf.obj)).obj f.relativeDifferentialsPresheaf

/-- An `\mathcal O_S`-linear derivation from `\mathcal O_X` into an
`\mathcal O_X`-module sheaf. -/
abbrev RelativeDerivation (M : X.Modules) :=
  M.val.Derivation' f.relativeStructureMap

/-- The canonical relative derivation
`d : \mathcal O_X ⟶ \Omega_{X/S}`. -/
noncomputable def relativeDifferentialsDerivation :
    f.RelativeDerivation f.relativeDifferentials :=
  (PresheafOfModules.DifferentialsConstruction.derivation'
      f.relativeStructureMap).postcomp
    ((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app f.relativeDifferentialsPresheaf)

/-- The universal property of `\Omega_{X/S}`: morphisms from the relative
differential sheaf to an `\mathcal O_X`-module sheaf are equivalent to relative
derivations with values in that sheaf. -/
noncomputable def relativeDifferentialsHomEquiv (M : X.Modules) :
    (f.relativeDifferentials ⟶ M) ≃ f.RelativeDerivation M where
  toFun α :=
    (PresheafOfModules.DifferentialsConstruction.derivation'
      f.relativeStructureMap).postcomp
      ((_root_.PresheafOfModules.sheafificationHomEquiv
        (𝟙 X.ringCatSheaf.obj)) α)
  invFun d :=
    (_root_.PresheafOfModules.sheafificationHomEquiv
      (𝟙 X.ringCatSheaf.obj)).symm
      ((PresheafOfModules.DifferentialsConstruction.isUniversal'
        f.relativeStructureMap).desc d)
  left_inv α := by
    apply (_root_.PresheafOfModules.sheafificationHomEquiv
      (𝟙 X.ringCatSheaf.obj)).injective
    rw [Equiv.apply_symm_apply]
    apply (PresheafOfModules.DifferentialsConstruction.isUniversal'
      f.relativeStructureMap).postcomp_injective
    rw [(PresheafOfModules.DifferentialsConstruction.isUniversal'
      f.relativeStructureMap).fac]
    rfl
  right_inv d := by
    change (PresheafOfModules.DifferentialsConstruction.derivation'
      f.relativeStructureMap).postcomp
        ((_root_.PresheafOfModules.sheafificationHomEquiv
          (𝟙 X.ringCatSheaf.obj))
          ((_root_.PresheafOfModules.sheafificationHomEquiv
            (𝟙 X.ringCatSheaf.obj)).symm
            ((PresheafOfModules.DifferentialsConstruction.isUniversal'
              f.relativeStructureMap).desc d))) = d
    rw [Equiv.apply_symm_apply]
    exact (PresheafOfModules.DifferentialsConstruction.isUniversal'
      f.relativeStructureMap).fac d

/-- Under the universal-property equivalence, the identity of
`\Omega_{X/S}` corresponds to the canonical derivation. -/
@[simp]
lemma relativeDifferentialsHomEquiv_id :
    f.relativeDifferentialsHomEquiv f.relativeDifferentials
        (𝟙 f.relativeDifferentials) =
      f.relativeDifferentialsDerivation :=
  rfl

end Hom

end AlgebraicGeometry.Scheme
