module

public import StacksAndModuli.API.SchemeModulesOpenCover
public import StacksAndModuli.API.SchemeModulesPullbackTensor
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Tensoring by a locally trivial module sheaf preserves monomorphisms

The tensor product of module sheaves is defined by sheafifying the presheaf tensor
product.  This file proves directly that tensoring in the right variable by a module
sheaf which is locally isomorphic to the structure sheaf preserves monomorphisms.

The proof identifies tensoring by the structure sheaf with the identity, transports
that fact across a local trivialization, and then detects monomorphisms on an open
cover.
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

/-- The right-unit identification for the tensor product of module sheaves is natural
in the left module. -/
lemma tensorUnitIso_naturality {F F' : X.Modules} (f : F ⟶ F') :
    tensorMapLeft f (SheafOfModules.unit X.ringCatSheaf) ≫
        (tensorUnitIso F').hom =
      (tensorUnitIso F).hom ≫ f := by
  have hρ :
      ((SheafOfModules.forget X.ringCatSheaf).map f ▷
          (SheafOfModules.unit X.ringCatSheaf).val) ≫
          (ρ_ F'.val).hom =
        (ρ_ F.val).hom ≫
          (SheafOfModules.forget X.ringCatSheaf).map f := by
    exact MonoidalCategory.rightUnitor_naturality
      ((SheafOfModules.forget X.ringCatSheaf).map f)
  dsimp only [tensorMapLeft, tensorUnitIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  slice_lhs 1 2 => rw [← (sheafification X).map_comp]
  rw [hρ]
  rw [(sheafification X).map_comp, Category.assoc]
  let adj := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  have hε :
      (sheafification X).map
          ((SheafOfModules.forget X.ringCatSheaf).map f) ≫
          ((asIso adj.counit).app F').hom =
        ((asIso adj.counit).app F).hom ≫ f := by
    have hmap :
        (sheafification X).map
            ((SheafOfModules.forget X.ringCatSheaf).map f) =
          (((SheafOfModules.forget X.ringCatSheaf ⋙
              _root_.PresheafOfModules.restrictScalars
                (𝟙 X.ringCatSheaf.obj)) ⋙
              _root_.PresheafOfModules.sheafification
                (𝟙 X.ringCatSheaf.obj)).map f) := rfl
    rw [hmap]
    simpa only [Functor.comp_map, Functor.id_map, asIso_hom, Iso.app_hom]
      using adj.counit.naturality f
  rw [hε]
  rfl

/-- Tensoring a monomorphism on the right by the structure sheaf is again a
monomorphism. -/
lemma tensorMapLeft_unit_mono {F F' : X.Modules} (f : F ⟶ F') [Mono f] :
    Mono (tensorMapLeft f (SheafOfModules.unit X.ringCatSheaf)) := by
  have h := tensorUnitIso_naturality f
  have hm : Mono
      (tensorMapLeft f (SheafOfModules.unit X.ringCatSheaf) ≫
        (tensorUnitIso F').hom) := by
    rw [h]
    infer_instance
  exact @mono_of_mono _ _ _ _ _ _ _ hm

/-- Tensoring a monomorphism on the right by a module isomorphic to the structure
sheaf is again a monomorphism. -/
lemma tensorMapLeft_mono_of_iso_unit {F F' L : X.Modules}
    (f : F ⟶ F') [Mono f]
    (e : L ≅ SheafOfModules.unit X.ringCatSheaf) :
    Mono (tensorMapLeft f L) := by
  let a := tensorMapLeft f L
  let t := tensorMapRight F' e.hom
  have ht : IsIso t := by
    change IsIso (tensorRightIso F' e).hom
    infer_instance
  letI : IsIso t := ht
  have hfu : Mono
      (tensorMapLeft f (SheafOfModules.unit X.ringCatSheaf)) :=
    tensorMapLeft_unit_mono f
  letI : Mono
      (tensorMapLeft f (SheafOfModules.unit X.ringCatSheaf)) := hfu
  have he : IsIso (tensorMapRight F e.hom) := by
    change IsIso (tensorRightIso F e).hom
    infer_instance
  letI : IsIso (tensorMapRight F e.hom) := he
  have hb : Mono
      (tensorMapRight F e.hom ≫
        tensorMapLeft f (SheafOfModules.unit X.ringCatSheaf)) := by
    infer_instance
  have h := tensorMap_exchange f e.hom
  have hat : Mono (a ≫ t) := by
    rw [← h]
    exact hb
  exact @mono_of_mono _ _ _ _ _ _ _ hat

/-- Restriction of module sheaves along an open immersion preserves
monomorphisms. -/
lemma restrictFunctor_map_mono
    {Y Z : Scheme.{u}} (j : Z ⟶ Y) [IsOpenImmersion j]
    {F F' : Y.Modules} (f : F ⟶ F') [Mono f] :
    Mono ((restrictFunctor j).map f) := by
  have hf : Mono f.val :=
    Functor.map_mono (SheafOfModules.forget Y.ringCatSheaf) f
  letI : Mono f.val := hf
  have hj : Mono
      ((SheafOfModules.forget Z.ringCatSheaf).map
        ((restrictFunctor j).map f)) := by
    change Mono (((restrictFunctor j).map f).val)
    apply PresheafOfModules.mono_of_injective
    intro U
    change Function.Injective (f.app (j.opensFunctor.op.obj U).unop).hom
    exact PresheafOfModules.injective_of_mono f.val
      (j.opensFunctor.op.obj U)
  exact Functor.mono_of_mono_map
    (SheafOfModules.forget Z.ringCatSheaf) hj

/-- Restriction of module sheaves along an open immersion preserves all
monomorphisms. -/
noncomputable instance restrictFunctor_preservesMonomorphisms
    {Y Z : Scheme.{u}} (j : Z ⟶ Y) [IsOpenImmersion j] :
    (restrictFunctor j).PreservesMonomorphisms where
  preserves f _ := restrictFunctor_map_mono j f

/-- Restriction of module sheaves along an open immersion is additive. -/
noncomputable instance restrictFunctor_additive
    {Y Z : Scheme.{u}} (j : Z ⟶ Y) [IsOpenImmersion j] :
    (restrictFunctor j).Additive := by
  letI : PreservesBinaryBiproducts (restrictFunctor j) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- Restriction of module sheaves along an open immersion preserves homology.

Restriction is a left adjoint, hence preserves cokernels, and it preserves
monomorphisms by the stalkwise argument above. -/
noncomputable instance restrictFunctor_preservesHomology
    {Y Z : Scheme.{u}} (j : Z ⟶ Y) [IsOpenImmersion j] :
    (restrictFunctor j).PreservesHomology :=
  (restrictFunctor j).preservesHomology_of_preservesMonos_and_cokernels

/-- Restriction of module sheaves along an open immersion preserves finite
limits. -/
noncomputable instance restrictFunctor_preservesFiniteLimits
    {Y Z : Scheme.{u}} (j : Z ⟶ Y) [IsOpenImmersion j] :
    PreservesFiniteLimits (restrictFunctor j) :=
  (restrictFunctor j).preservesFiniteLimits_of_preservesHomology

/-- On an open where the right tensor factor is trivial, restriction of tensoring a
monomorphism remains a monomorphism. -/
lemma restrict_tensorMapLeft_mono_of_iso_unit
    {Y Z : Scheme.{u}} (j : Z ⟶ Y) [IsOpenImmersion j]
    {F F' L : Y.Modules} (f : F ⟶ F') [Mono f]
    (e : (restrictFunctor j).obj L ≅
      SheafOfModules.unit Z.ringCatSheaf) :
    Mono ((restrictFunctor j).map (tensorMapLeft f L)) := by
  let fZ := (restrictFunctor j).map f
  letI : Mono fZ := restrictFunctor_map_mono j f
  let b := tensorMapLeft fZ ((restrictFunctor j).obj L)
  have hb : Mono b := tensorMapLeft_mono_of_iso_unit fZ e
  letI : Mono b := hb
  let a := (restrictFunctor j).map (tensorMapLeft f L)
  let eF := restrictTensorIso j F L
  let eF' := restrictTensorIso j F' L
  have h₀ := restrictTensorIso_naturality j f (𝟙 L)
  have hid : (restrictFunctor j).map (𝟙 L) =
      𝟙 ((restrictFunctor j).obj L) := (restrictFunctor j).map_id L
  have hs : tensorMapLeft f L ≫ tensorMapRight F' (𝟙 L) =
      tensorMapLeft f L := by rw [tensorMapRight_id, Category.comp_id]
  have ht : tensorMapLeft fZ ((restrictFunctor j).obj L) ≫
      tensorMapRight ((restrictFunctor j).obj F')
        ((restrictFunctor j).map (𝟙 L)) = b := by
    rw [hid, tensorMapRight_id, Category.comp_id]
  have h : a ≫ eF'.hom = eF.hom ≫ b := by
    rw [hs, ht] at h₀
    exact h₀
  have ha : Mono (a ≫ eF'.hom) := by
    rw [h]
    infer_instance
  exact @mono_of_mono _ _ _ _ _ _ _ ha

/-- Tensoring on the right by a module sheaf which is trivial on an open cover
preserves monomorphisms. -/
theorem tensorMapLeft_mono_of_iSup_iso_unit
    {F F' L : X.Modules} (f : F ⟶ F') [Mono f]
    {J : Type u} (U : J → X.Opens) (hU : IsOpenCover U)
    (e : ∀ j, (restrictFunctor (U j).ι).obj L ≅
      SheafOfModules.unit (U j).toScheme.ringCatSheaf) :
    Mono (tensorMapLeft f L) := by
  let 𝒰 := X.openCoverOfIsOpenCover U hU
  apply mono_of_restrict_openCover (tensorMapLeft f L) 𝒰
  intro j
  exact restrict_tensorMapLeft_mono_of_iso_unit (𝒰.f j) f (e j)

end AlgebraicGeometry.Scheme.Modules

end
