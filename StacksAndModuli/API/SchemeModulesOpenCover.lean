module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Detecting isomorphisms and monomorphisms on an open cover

This file records local-to-global criteria for isomorphisms and monomorphisms of module
sheaves on a scheme. They are useful whenever a morphism can be computed after restriction
to a standard affine cover.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism of module sheaves that becomes an isomorphism on every member of a
scheme open cover is an isomorphism. -/
theorem isIso_of_restrict_openCover {Y : Scheme.{u}} {P Q : Y.Modules}
    (a : P ⟶ Q) (𝒰 : Y.OpenCover)
    (hlocal : ∀ i, IsIso ((restrictFunctor (𝒰.f i)).map a)) : IsIso a := by
  have hstalk (x : Y) :
      IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        a.mapPresheaf) := by
    obtain ⟨y, hy⟩ := 𝒰.covers x
    let j := 𝒰.f (𝒰.idx x)
    let b := (restrictFunctor j).map a
    letI : IsIso b := hlocal (𝒰.idx x)
    letI : IsIso ((toPresheaf (𝒰.X (𝒰.idx x))).map b) :=
      Functor.map_isIso (toPresheaf (𝒰.X (𝒰.idx x))) b
    have hbpre : IsIso b.mapPresheaf := by
      change IsIso ((toPresheaf (𝒰.X (𝒰.idx x))).map b)
      infer_instance
    letI : IsIso b.mapPresheaf := hbpre
    haveI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        b.mapPresheaf) := inferInstance
    let l := (restrictFunctor j ⋙ toPresheaf (𝒰.X (𝒰.idx x)) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map a
    have hl : IsIso l := by
      change IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        b.mapPresheaf)
      infer_instance
    letI : IsIso l := hl
    rw [← hy]
    exact IsIso.of_isIso_fac_left
      ((restrictStalkNatIso j y).hom.naturality a).symm
  have hsheaf : IsIso ((SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map a) := by
    letI : ∀ x : Y, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        ((SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map a).1) := hstalk
    exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso
      ((SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map a)
  haveI : IsIso ((SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map a) := hsheaf
  haveI : (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).ReflectsIsomorphisms :=
    inferInstance
  exact isIso_of_reflects_iso a (SheafOfModules.toSheaf.{u} Y.ringCatSheaf)

/-- A morphism of module sheaves that becomes a monomorphism on every member of a
scheme open cover is a monomorphism. -/
theorem mono_of_restrict_openCover {Y : Scheme.{u}} {P Q : Y.Modules}
    (a : P ⟶ Q) (U : Y.OpenCover)
    (hlocal : ∀ i, Mono ((restrictFunctor (U.f i)).map a)) : Mono a := by
  have hstalk (x : Y) :
      Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        a.mapPresheaf) := by
    obtain ⟨y, hy⟩ := U.covers x
    let j := U.f (U.idx x)
    let b := (restrictFunctor j).map a
    letI : Mono b := hlocal (U.idx x)
    let bAb := (SheafOfModules.toSheaf (U.X (U.idx x)).ringCatSheaf).map b
    letI : Mono bAb := Functor.map_mono
      (SheafOfModules.toSheaf (U.X (U.idx x)).ringCatSheaf) b
    let l := (restrictFunctor j ⋙ toPresheaf (U.X (U.idx x)) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map a
    have hl : Mono l := by
      change Mono ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        b.mapPresheaf)
      exact TopCat.Presheaf.stalk_mono_of_mono bAb y
    letI : Mono l := hl
    rw [← hy]
    change Mono ((toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j.base y)).map a)
    let g := (toPresheaf Y ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (j.base y)).map a
    have hnat := (restrictStalkNatIso j y).hom.naturality a
    have hleft : Mono (l ≫ (restrictStalkNatIso j y).hom.app Q) := inferInstance
    letI : Mono (l ≫ (restrictStalkNatIso j y).hom.app Q) := hleft
    have hright : Mono ((restrictStalkNatIso j y).hom.app P ≫ g) := by
      rw [← hnat]
      infer_instance
    letI := hright
    change Mono g
    rw [show g = (restrictStalkNatIso j y).inv.app P ≫
        ((restrictStalkNatIso j y).hom.app P ≫ g) by simp]
    infer_instance
  have hAb : Mono ((SheafOfModules.toSheaf Y.ringCatSheaf).map a) := by
    rw [TopCat.Presheaf.mono_iff_stalk_mono]
    exact hstalk
  exact Functor.mono_of_mono_map (SheafOfModules.toSheaf Y.ringCatSheaf) hAb

end AlgebraicGeometry.Scheme.Modules

end
