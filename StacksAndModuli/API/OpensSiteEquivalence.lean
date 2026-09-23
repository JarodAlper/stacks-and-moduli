module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import StacksAndModuli.API.ExtEquivalence
public import StacksAndModuli.API.SheafCohomologyFlasque

/-!
# A homeomorphism is an equivalence of the sites of opens

`TopologicalSpace.Opens.mapMapIso H : Opens Y ≌ Opens X` is the equivalence of poset
categories attached to an isomorphism `H : X ≅ Y` of topological spaces.  This file supplies
the missing `IsDenseSubsite` instance, so that `CategoryTheory.Equivalence.sheafCongr`
applies and the categories of sheaves on `X` and on `Y` are equivalent.

The topology on `Opens T` is pointwise — `S ∈ grothendieckTopology T U` iff every point of `U`
lies in some member of `S` (`Opens.mem_grothendieckTopology`) — so the verification is a direct
transport of points along the homeomorphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite

namespace TopologicalSpace.Opens

variable {X Y : TopCat.{u}} (H : X ≅ Y)

instance isEquivalence_map_inv : (Opens.map H.inv).IsEquivalence :=
  inferInstanceAs ((Opens.mapMapIso H).inverse.IsEquivalence)

lemma inv_hom_apply (x : X) :
    (ConcreteCategory.hom H.inv) ((ConcreteCategory.hom H.hom) x) = x := by
  simp [← ConcreteCategory.comp_apply, H.hom_inv_id]

/-- Pulling opens back along the inverse of a homeomorphism is a dense subsite morphism. -/
instance isDenseSubsite_map_inv :
    (Opens.map H.inv).IsDenseSubsite (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) where
  functorPushforward_mem_iff {U S} := by
    constructor
    · intro hS x hx
      have hy : (ConcreteCategory.hom H.hom) x ∈ (Opens.map H.inv).obj U := by
        show (ConcreteCategory.hom H.inv) ((ConcreteCategory.hom H.hom) x) ∈ U
        rw [inv_hom_apply]
        exact hx
      obtain ⟨W, g, hg, hW⟩ := hS _ hy
      obtain ⟨V, f, h, hf, -⟩ := hg
      refine ⟨V, f, hf, ?_⟩
      have hmem : (ConcreteCategory.hom H.hom) x ∈ (Opens.map H.inv).obj V := (leOfHom h) hW
      have hmem' : (ConcreteCategory.hom H.inv) ((ConcreteCategory.hom H.hom) x) ∈ V := hmem
      rwa [inv_hom_apply] at hmem'
    · intro hS y hy
      obtain ⟨V, f, hf, hV⟩ := hS _ hy
      exact ⟨(Opens.map H.inv).obj V, (Opens.map H.inv).map f,
        ⟨V, f, 𝟙 _, hf, by simp⟩, hV⟩

/-- The equivalence of categories of abelian sheaves induced by a homeomorphism. -/
noncomputable def sheafEquivOfIso :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≌
      CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  Functor.IsDenseSubsite.sheafEquiv (Opens.grothendieckTopology X)
    (Opens.grothendieckTopology Y) (Opens.map H.inv) AddCommGrpCat.{u}

noncomputable def isTerminalMapTop :
    Limits.IsTerminal ((Opens.map H.inv).obj (⊤ : Opens X)) := by
  rw [Opens.map_top]
  exact Limits.isTerminalTop

instance additive_sheafEquivOfIso_inverse : (sheafEquivOfIso H).inverse.Additive where
  map_add := by intros; rfl

instance additive_sheafEquivOfIso_symm_functor :
    (sheafEquivOfIso H).symm.functor.Additive :=
  additive_sheafEquivOfIso_inverse H

instance additive_sheafEquivOfIso_functor : (sheafEquivOfIso H).functor.Additive := by
  have hf : (sheafEquivOfIso H).symm.functor.Additive := additive_sheafEquivOfIso_inverse H
  exact Equivalence.inverse_additive (sheafEquivOfIso H).symm

/-- The constant sheaf corresponds to the constant sheaf under a homeomorphism. -/
noncomputable def constantSheafIso :
    (sheafEquivOfIso H).functor.obj
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  (CategoryTheory.equivCommuteConstant (Opens.grothendieckTopology X)
    AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.map H.inv)
    Limits.isTerminalTop (isTerminalMapTop H)).app _

/-- **Sheaf cohomology is invariant under a homeomorphism.** -/
theorem subsingleton_H_sheafEquivOfIso
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (n : ℕ)
    (h : Subsingleton (F.H n)) :
    Subsingleton (((sheafEquivOfIso H).functor.obj F).H n) :=
  Abelian.Ext.subsingleton_of_iso_left (constantSheafIso H) n
    (Equivalence.subsingleton_Ext_map (sheafEquivOfIso H) _ F n h)

/-- The constant sheaf corresponds to the constant sheaf under the inverse equivalence. -/
noncomputable def constantSheafIsoInverse :
    (sheafEquivOfIso H).inverse.obj
        ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  ((CategoryTheory.equivCommuteConstant' (Opens.grothendieckTopology X)
    AddCommGrpCat.{u} (Opens.grothendieckTopology Y) (Opens.map H.inv)
    Limits.isTerminalTop (isTerminalMapTop H)).app _).symm

/-- **Sheaf cohomology is invariant under a homeomorphism**, in the direction that transports
a vanishing theorem *back* along the homeomorphism. -/
theorem subsingleton_H_sheafEquivOfIso_inverse
    (G : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (n : ℕ)
    (h : Subsingleton (G.H n)) :
    Subsingleton (((sheafEquivOfIso H).inverse.obj G).H n) :=
  Abelian.Ext.subsingleton_of_iso_left (constantSheafIsoInverse H) n
    (Equivalence.subsingleton_Ext_map (sheafEquivOfIso H).symm _ G n h)

end TopologicalSpace.Opens
