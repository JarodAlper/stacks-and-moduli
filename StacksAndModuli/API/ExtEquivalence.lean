module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# `Ext` is invariant under an equivalence of abelian categories

Mathlib's `CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects` says that a
full, faithful, exact functor preserving injective objects induces a bijection on `Ext`.  An
equivalence of abelian categories satisfies every one of those hypotheses, so:

`Ext X Y n ≃ Ext (e.functor.obj X) (e.functor.obj Y) n`.

This is the mechanism by which sheaf cohomology transports along an isomorphism of the
underlying space: `Hⁿ` and `H'ⁿ` are `Ext` in the category of abelian sheaves, and a
homeomorphism induces an equivalence of those categories.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe w w' v v' u u'

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace CategoryTheory.Equivalence

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable (e : C ≌ D) [e.functor.Additive]
variable [HasExt.{w} C] [HasExt.{w'} D] [EnoughInjectives C]

/-- **An equivalence of abelian categories induces a bijection on `Ext` groups.** -/
theorem bijective_mapExt (X Y : C) (n : ℕ) :
    Function.Bijective (e.functor.mapExtAddHom X Y n) :=
  Functor.mapExt_bijective_of_preservesInjectiveObjects e.functor X Y n

/-- Vanishing of `Ext` transports across an equivalence. -/
theorem subsingleton_Ext_map (X Y : C) (n : ℕ) (h : Subsingleton (Ext.{w} X Y n)) :
    Subsingleton (Ext.{w'} (e.functor.obj X) (e.functor.obj Y) n) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := (bijective_mapExt e X Y n).2 a
  obtain ⟨b', rfl⟩ := (bijective_mapExt e X Y n).2 b
  rw [@Subsingleton.elim _ h a' b']

/-- Vanishing of `Ext` reflects across an equivalence. -/
theorem subsingleton_Ext_of_map (X Y : C) (n : ℕ)
    (h : Subsingleton (Ext.{w'} (e.functor.obj X) (e.functor.obj Y) n)) :
    Subsingleton (Ext.{w} X Y n) :=
  ⟨fun _ _ => (bijective_mapExt e X Y n).1 (@Subsingleton.elim _ h _ _)⟩

end CategoryTheory.Equivalence

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Vanishing of `Ext` transports along an isomorphism in the **first** variable. -/
theorem subsingleton_of_iso_left {A A' B : C} (e : A ≅ A') (n : ℕ)
    (h : Subsingleton (Ext.{w} A B n)) : Subsingleton (Ext.{w} A' B n) := by
  have hinj : Function.Injective
      (fun x : Ext.{w} A' B n => (Ext.mk₀ e.hom).comp x (zero_add n)) := by
    intro x y hxy
    have key : ∀ z : Ext.{w} A' B n,
        (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp z (zero_add n)) (zero_add n) = z := by
      intro z
      rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
    rw [← key x, ← key y]
    exact congrArg (fun t => (Ext.mk₀ e.inv).comp t (zero_add n)) hxy
  exact ⟨fun a b => hinj (@Subsingleton.elim _ h _ _)⟩

end CategoryTheory.Abelian.Ext
