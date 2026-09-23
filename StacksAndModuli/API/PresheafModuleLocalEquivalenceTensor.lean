module

public import StacksAndModuli.API.PresheafModuleStalkTensor
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Tensor stability of local equivalences of module presheaves

On a topological space, a morphism of presheaves of abelian groups becomes an
isomorphism after sheafification exactly when it is an isomorphism on every stalk.
Using the filtered-colimit tensor comparison, this file proves that the corresponding
local equivalences of presheaves of modules are stable under tensor products.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  TopologicalSpace Opposite

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {F G : X.Presheaf AddCommGrpCat.{u}}

/-- On a topological space, the local equivalences inverted by sheafification are
exactly the morphisms inducing isomorphisms on all stalks. -/
lemma grothendieckTopology_W_iff_stalkFunctor_map_iso (f : F ⟶ G) :
    (Opens.grothendieckTopology X).W f ↔
      ∀ x : X, IsIso ((stalkFunctor AddCommGrpCat x).map f) := by
  let J := Opens.grothendieckTopology X
  constructor
  · intro hf x
    letI : IsIso ((presheafToSheaf J AddCommGrpCat).map f) :=
      (J.W_iff f).mp hf
    letI : IsIso (sheafifyMap J f) := by
      change IsIso ((sheafToPresheaf J AddCommGrpCat).map
        ((presheafToSheaf J AddCommGrpCat).map f))
      infer_instance
    letI : IsIso ((stalkFunctor AddCommGrpCat x).map
        (CategoryTheory.toSheafify J G)) :=
      stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat G
    letI : IsIso ((stalkFunctor AddCommGrpCat x).map
        (CategoryTheory.toSheafify J F)) :=
      stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat F
    letI : IsIso ((stalkFunctor AddCommGrpCat x).map f ≫
        (stalkFunctor AddCommGrpCat x).map (CategoryTheory.toSheafify J G)) := by
      rw [← Functor.map_comp, CategoryTheory.toSheafify_naturality, Functor.map_comp]
      infer_instance
    exact IsIso.of_isIso_comp_right
      ((stalkFunctor AddCommGrpCat x).map f)
      ((stalkFunctor AddCommGrpCat x).map (CategoryTheory.toSheafify J G))
  · intro hf
    rw [J.W_iff]
    letI (x : X) : IsIso ((stalkFunctor AddCommGrpCat x).map
        ((presheafToSheaf J AddCommGrpCat).map f).hom) := by
      change IsIso ((stalkFunctor AddCommGrpCat x).map (sheafifyMap J f))
      letI : IsIso ((stalkFunctor AddCommGrpCat x).map f) := hf x
      letI : IsIso ((stalkFunctor AddCommGrpCat x).map
          (CategoryTheory.toSheafify J G)) :=
        stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat G
      letI : IsIso ((stalkFunctor AddCommGrpCat x).map
          (CategoryTheory.toSheafify J F)) :=
        stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat F
      letI : IsIso ((stalkFunctor AddCommGrpCat x).map
          (CategoryTheory.toSheafify J F) ≫
          (stalkFunctor AddCommGrpCat x).map (sheafifyMap J f)) := by
        rw [← Functor.map_comp, ← CategoryTheory.toSheafify_naturality,
          Functor.map_comp]
        infer_instance
      exact IsIso.of_isIso_comp_left
        ((stalkFunctor AddCommGrpCat x).map (CategoryTheory.toSheafify J F))
        ((stalkFunctor AddCommGrpCat x).map (sheafifyMap J f))
    exact isIso_of_stalkFunctor_map_iso ((presheafToSheaf J AddCommGrpCat).map f)

end TopCat.Presheaf

namespace PresheafOfModules

variable {X : TopCat.{u}} (R : X.Presheaf CommRingCat.{u})

/-- Local equivalences of presheaves of modules on a topological space are stable
under tensor products. -/
noncomputable instance localEquivalencesIsMonoidal :
    ((Opens.grothendieckTopology X).W.inverseImage
      (toPresheaf (R ⋙ forget₂ CommRingCat RingCat))).IsMonoidal := by
  apply MorphismProperty.IsMonoidal.mk'
  intro M M' N N' f g hf hg
  change (Opens.grothendieckTopology X).W
    ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map (f ⊗ₘ g))
  rw [TopCat.Presheaf.grothendieckTopology_W_iff_stalkFunctor_map_iso]
  intro x
  have hfx := (TopCat.Presheaf.grothendieckTopology_W_iff_stalkFunctor_map_iso
    ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f)).mp hf x
  have hgx := (TopCat.Presheaf.grothendieckTopology_W_iff_stalkFunctor_map_iso
    ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map g)).mp hg x
  letI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map f)) := hfx
  letI : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((toPresheaf (R ⋙ forget₂ CommRingCat RingCat)).map g)) := hgx
  letI : IsIso (StalkTensor.colimitMap R x f) :=
    StalkTensor.colimitMap_isIso R x f
  letI : IsIso (StalkTensor.colimitMap R x g) :=
    StalkTensor.colimitMap_isIso R x g
  letI : IsIso (StalkTensor.colimitMap R x f ⊗ₘ
      StalkTensor.colimitMap R x g) := inferInstance
  letI : IsIso (StalkTensor.colimitMap R x (f ⊗ₘ g) ≫
      (StalkTensor.comparisonIso R x M' N').hom) := by
    rw [← StalkTensor.comparisonIso_hom_naturality R x f g]
    infer_instance
  letI : IsIso (StalkTensor.colimitMap R x (f ⊗ₘ g)) :=
    IsIso.of_isIso_comp_right (StalkTensor.colimitMap R x (f ⊗ₘ g))
      (StalkTensor.comparisonIso R x M' N').hom
  rw [← StalkTensor.forget_colimitMap R x (f ⊗ₘ g)]
  infer_instance

end PresheafOfModules
