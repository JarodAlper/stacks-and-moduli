module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksAndModuli.API.ExtEquivalence

/-!
# Sheaf cohomology transports along an equivalence of sites

If `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)` and the induced pushforward on
sheaves is an equivalence, then `Hⁿ` on `(C, J)` and on `(D, K)` agree.  Concretely, vanishing
transports in both directions.

Every ingredient is already in Mathlib:

* `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` — the equivalence of sheaf categories;
* `CategoryTheory.equivCommuteConstant` / `equivCommuteConstant'` — it carries the constant
  sheaf to the constant sheaf, which is exactly what `Sheaf.H` (an `Ext` out of the constant
  sheaf on `ULift ℤ`) needs;
* `CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`, packaged in
  `StacksAndModuli/API/ExtEquivalence.lean` — `Ext` is bijective across an equivalence of abelian
  categories.

The one thing to know is that the *inverse* of `sheafEquiv` is precomposition with `G.op`, so
its additivity is `rfl`, and the functor's additivity comes from
`Equivalence.inverse_additive` — instance search will not unfold `e.symm.functor` to
`e.inverse`, so that instance is stated separately.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe w v v' u u'

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor.IsDenseSubsite

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
variable [G.IsDenseSubsite J K]
variable [∀ X : Dᵒᵖ, HasLimitsOfShape (StructuredArrow X G.op) AddCommGrpCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

instance additive_sheafEquiv_inverse :
    (sheafEquiv J K G AddCommGrpCat.{w}).inverse.Additive where
  map_add := by intros; rfl

instance additive_sheafEquiv_symm_functor :
    (sheafEquiv J K G AddCommGrpCat.{w}).symm.functor.Additive :=
  additive_sheafEquiv_inverse J K G

instance additive_sheafEquiv_functor :
    (sheafEquiv J K G AddCommGrpCat.{w}).functor.Additive :=
  Equivalence.inverse_additive (sheafEquiv J K G AddCommGrpCat.{w}).symm

variable {T : C} (hT : IsTerminal T) (hT' : IsTerminal (G.obj T))
variable [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
variable [HasExt.{w} (Sheaf J AddCommGrpCat.{w})] [HasExt.{w} (Sheaf K AddCommGrpCat.{w})]
variable [EnoughInjectives (Sheaf J AddCommGrpCat.{w})]
variable [EnoughInjectives (Sheaf K AddCommGrpCat.{w})]

omit [EnoughInjectives (Sheaf K AddCommGrpCat.{w})] in
include hT hT' in
/-- **Vanishing of sheaf cohomology transports across an equivalence of sites.** -/
theorem subsingleton_H_sheafEquiv_functor
    (F : Sheaf J AddCommGrpCat.{w}) (n : ℕ) (h : Subsingleton (F.H n)) :
    Subsingleton (((sheafEquiv J K G AddCommGrpCat.{w}).functor.obj F).H n) :=
  Ext.subsingleton_of_iso_left
    ((equivCommuteConstant J AddCommGrpCat.{w} K G hT hT').app _) n
    (Equivalence.subsingleton_Ext_map (sheafEquiv J K G AddCommGrpCat.{w}) _ F n h)

omit [EnoughInjectives (Sheaf J AddCommGrpCat.{w})] in
include hT hT' in
/-- The same, in the direction that reads a vanishing theorem on `(D, K)` back on `(C, J)`. -/
theorem subsingleton_H_sheafEquiv_inverse
    (F : Sheaf K AddCommGrpCat.{w}) (n : ℕ) (h : Subsingleton (F.H n)) :
    Subsingleton (((sheafEquiv J K G AddCommGrpCat.{w}).inverse.obj F).H n) :=
  Ext.subsingleton_of_iso_left
    (((equivCommuteConstant' J AddCommGrpCat.{w} K G hT hT').app _).symm) n
    (Equivalence.subsingleton_Ext_map (sheafEquiv J K G AddCommGrpCat.{w}).symm _ F n h)

end CategoryTheory.Functor.IsDenseSubsite
