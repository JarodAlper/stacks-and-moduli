module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Sheafification against a locally bijective comparison

Supporting API with no Stacks Project counterpart of its own: if `M₀` is a presheaf of
modules, `F` a sheaf of modules, and `ψ : M₀ ⟶ F` a morphism that is locally bijective on
underlying presheaves of abelian groups, then the induced morphism from the sheafification
of `M₀` to `F` is an isomorphism.  This is the universal tool for computing sheafifications:
exhibit a sheaf receiving a locally bijective comparison and the sheafification is
identified with it.

Consumed by the exterior-power sheaf of §2.2, where the comparison from the exterior-power
presheaf into the tilde of the exterior power of the module of global sections is locally
bijective on the basic-open basis of an affine scheme.

Main declarations:
- `PresheafOfModules.isIso_sheafifyHomEquiv_symm`;
- `PresheafOfModules.sheafifyIsoOfLocallyBijective`.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{u}} {R : Sheaf J RingCat.{u}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  {M₀ : PresheafOfModules.{v} R₀} {A : Sheaf J AddCommGrpCat.{v}}
  (φ : M₀.presheaf ⟶ A.obj)
  [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

omit [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- A morphism of sheaves of modules that is locally bijective on underlying presheaves
of abelian groups is an isomorphism. -/
lemma _root_.SheafOfModules.isIso_of_isLocallyBijective
    [J.HasSheafCompose (forget AddCommGrpCat.{v})]
    {F G : SheafOfModules.{v} R} (g : F ⟶ G)
    (hI : Presheaf.IsLocallyInjective J
      ((toPresheaf R.obj).map ((SheafOfModules.forget R).map g)))
    (hS : Presheaf.IsLocallySurjective J
      ((toPresheaf R.obj).map ((SheafOfModules.forget R).map g))) :
    IsIso g := by
  have hS' : Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf R).map g).hom := hS
  have hI' : Presheaf.IsLocallyInjective J ((SheafOfModules.toSheaf R).map g).hom := hI
  suffices h : IsIso ((SheafOfModules.toSheaf R).map g) by
    exact isIso_of_reflects_iso g (SheafOfModules.toSheaf R)
  rw [← Sheaf.isLocallyBijective_iff_isIso (A := AddCommGrpCat.{v})]
  exact ⟨hI', hS'⟩

omit [J.WEqualsLocallyBijective AddCommGrpCat.{v}] in
/-- A morphism of sheaves of modules that is locally surjective on underlying presheaves
of abelian groups is an epimorphism. -/
lemma _root_.SheafOfModules.epi_of_isLocallySurjective
    [J.HasSheafCompose (forget AddCommGrpCat.{v})]
    {F G : SheafOfModules.{v} R} (g : F ⟶ G)
    (hS : Presheaf.IsLocallySurjective J
      ((toPresheaf R.obj).map ((SheafOfModules.forget R).map g))) :
    Epi g := by
  have hS' : Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf R).map g).hom := hS
  haveI : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map g) := hS'
  haveI : Epi ((SheafOfModules.toSheaf R).map g) := Sheaf.epi_of_isLocallySurjective _
  exact (SheafOfModules.toSheaf R).epi_of_epi_map inferInstance

/-- A locally bijective comparison from a presheaf of modules to a sheaf of modules
exhibits that sheaf as the sheafification: the induced morphism out of `sheafify` is an
isomorphism. -/
lemma isIso_sheafifyHomEquiv_symm [J.HasSheafCompose (forget AddCommGrpCat.{v})]
    {F : SheafOfModules.{v} R}
    (ψ : M₀ ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F))
    (hi : Presheaf.IsLocallyInjective J ((toPresheaf R₀).map ψ))
    (hs : Presheaf.IsLocallySurjective J ((toPresheaf R₀).map ψ)) :
    IsIso ((sheafifyHomEquiv α φ).symm ψ) := by
  set g : sheafify α φ ⟶ F := (sheafifyHomEquiv α φ).symm ψ with hg
  have hval : (SheafOfModules.forget R).map g =
      (sheafifyHomEquiv' α φ F.isSheaf).symm ψ := by
    rw [hg]
    rfl
  have fac : φ ≫ (toPresheaf R.obj).map ((SheafOfModules.forget R).map g) =
      (toPresheaf R₀).map ψ := by
    rw [hval]
    exact comp_toPresheaf_map_sheafifyHomEquiv'_symm_hom α φ F.isSheaf ψ
  haveI hsurj : Presheaf.IsLocallySurjective J
      (φ ≫ (toPresheaf R.obj).map ((SheafOfModules.forget R).map g)) := by
    rw [fac]
    exact hs
  haveI hinj : Presheaf.IsLocallyInjective J
      (φ ≫ (toPresheaf R.obj).map ((SheafOfModules.forget R).map g)) := by
    rw [fac]
    exact hi
  exact SheafOfModules.isIso_of_isLocallyBijective g
    (Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective J φ _)
    (Presheaf.isLocallySurjective_of_isLocallySurjective J φ _)

/-- The isomorphism from the sheafification of a presheaf of modules to a sheaf of
modules receiving a locally bijective comparison. -/
noncomputable def sheafifyIsoOfLocallyBijective [J.HasSheafCompose (forget AddCommGrpCat.{v})]
    {F : SheafOfModules.{v} R}
    (ψ : M₀ ⟶ (restrictScalars α).obj ((SheafOfModules.forget _).obj F))
    (hi : Presheaf.IsLocallyInjective J ((toPresheaf R₀).map ψ))
    (hs : Presheaf.IsLocallySurjective J ((toPresheaf R₀).map ψ)) :
    sheafify α φ ≅ F :=
  letI := isIso_sheafifyHomEquiv_symm α φ ψ hi hs
  asIso ((sheafifyHomEquiv α φ).symm ψ)

end PresheafOfModules

end
