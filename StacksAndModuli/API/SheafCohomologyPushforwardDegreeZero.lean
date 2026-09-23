module

public import StacksAndModuli.API.FlasqueVanishing
public import StacksAndModuli.API.SheafCohomologyPushforward

/-!
# Degree-zero canonical pushforward cohomology

For a continuous map `g : S ⟶ T` and an abelian sheaf `F` on `S`, this file gives the
sheaf-level canonical map

`Hⁿ(T, g_* F) ⟶ Hⁿ(S, F)`

and proves that it is bijective in degree zero.  The inverse is the ordinary
inverse-image--pushforward adjunction on morphisms, conjugated by the canonical
identification between the inverse image of the constant sheaf and the constant sheaf.

The scheme-module map in `SheafCohomologyPushforward.lean` is definitionally this
construction on the underlying abelian sheaf.  Consequently its degree-zero instance is
bijective for every scheme morphism and every module, with no affine or quasicoherence
hypothesis.

This does not settle the positive-degree affine-quasicoherent comparison.  The generic
Ext-adjunction theorem would require pushforward to be exact on the whole category of
abelian sheaves, whereas affine pushforward is exact only on quasicoherent coefficients.
Using that fact here still requires affine quasicoherent acyclicity, or equivalently a
comparison between derived Ext in the quasicoherent full subcategory and ambient sheaf
cohomology; neither comparison is currently present in the imported API.

## Main results

* `TopCat.Sheaf.pushforwardCohomologyMap`: the sheaf-level canonical map in every degree.
* `TopCat.Sheaf.pushforwardCohomologyMapZeroAddEquiv`: its degree-zero additive
  equivalence.
* `TopCat.Sheaf.pushforwardCohomologyMap_succ_bijective_of_isFlasque`: the canonical
  map is bijective in every positive degree for a flasque coefficient sheaf.
* `AlgebraicGeometry.Scheme.Modules.pushforwardCohomologyMap_zero_bijective`: the
  degree-zero canonical scheme-module map is bijective.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace CategoryTheory.Abelian.Ext

/-- Applying the degree-zero Ext-to-Hom equivalence after embedding a morphism back into
degree-zero Ext recovers that morphism. -/
lemma homEquiv₀_mk₀_apply {C : Type u} [Category.{v} C] [Abelian C]
    [HasExt.{w} C] {X Y : C} (q : X ⟶ Y) :
    homEquiv₀ (mk₀ q) = q := by
  apply (mk₀_bijective X Y).injective
  rw [mk₀_homEquiv₀_apply]

end CategoryTheory.Abelian.Ext

namespace TopCat.Sheaf

variable {S T : TopCat.{u}} (g : S ⟶ T)

/-- The canonical cohomology map from the pushforward of an abelian sheaf.

It applies exact inverse image to an Ext class, precomposes with the canonical
constant-sheaf comparison, and postcomposes with the inverse-image--pushforward counit.
-/
noncomputable def pushforwardCohomologyMap
    (F : Sheaf AddCommGrpCat.{u} S) (n : ℕ) :
    CategoryTheory.Sheaf.H ((pushforward AddCommGrpCat.{u} g).obj F) n →+
      CategoryTheory.Sheaf.H F n := by
  let c := (pullbackConstantAddCommGrpIso g).app
    (AddCommGrpCat.of (ULift ℤ))
  let ε := (pullbackPushforwardAdjunction AddCommGrpCat.{u} g).counit.app F
  exact ((Abelian.Ext.mk₀ ε).postcomp _ (add_zero n)).comp
    (((Abelian.Ext.mk₀ c.inv).precomp _ (zero_add n)).comp
      ((pullback AddCommGrpCat.{u} g).mapExtAddHom _ _ n))

/-- In degree zero, the canonical pushforward cohomology map is the ordinary sheaf
adjunction on morphisms, conjugated by the inverse-image comparison for the constant
sheaf. -/
lemma pushforwardCohomologyMap_zero_homEquiv₀
    (F : Sheaf AddCommGrpCat.{u} S)
    (x : CategoryTheory.Sheaf.H
      ((pushforward AddCommGrpCat.{u} g).obj F) 0) :
    Abelian.Ext.homEquiv₀ (pushforwardCohomologyMap g F 0 x) =
      ((pullbackConstantAddCommGrpIso g).app
          (AddCommGrpCat.of (ULift ℤ))).inv ≫
        ((pullbackPushforwardAdjunction AddCommGrpCat.{u} g).homEquiv _ _).symm
          (Abelian.Ext.homEquiv₀ x) := by
  change Abelian.Ext.homEquiv₀
      (((Abelian.Ext.mk₀
          ((pullbackConstantAddCommGrpIso g).app
            (AddCommGrpCat.of (ULift ℤ))).inv).comp
        (x.mapExactFunctor (pullback AddCommGrpCat.{u} g)) (zero_add 0)).comp
          (Abelian.Ext.mk₀
            ((pullbackPushforwardAdjunction
              AddCommGrpCat.{u} g).counit.app F)) (add_zero 0)) = _
  rw [Abelian.Ext.mapExactFunctor₀]
  apply (Abelian.Ext.mk₀_bijective _ _).injective
  simp only [Function.comp_apply, Abelian.Ext.mk₀_homEquiv₀_apply,
    Abelian.Ext.homEquiv₀_symm_apply, Abelian.Ext.mk₀_comp_mk₀]
  rw [CategoryTheory.Adjunction.homEquiv_counit]
  rw [Category.assoc]

/-- The canonical degree-zero pushforward cohomology map as an additive equivalence. -/
noncomputable def pushforwardCohomologyMapZeroAddEquiv
    (F : Sheaf AddCommGrpCat.{u} S) :
    CategoryTheory.Sheaf.H
        ((pushforward AddCommGrpCat.{u} g).obj F) 0 ≃+
      CategoryTheory.Sheaf.H F 0 where
  toFun := pushforwardCohomologyMap g F 0
  invFun y := Abelian.Ext.mk₀
    ((pullbackPushforwardAdjunction AddCommGrpCat.{u} g).homEquiv _ _
      (((pullbackConstantAddCommGrpIso g).app
        (AddCommGrpCat.of (ULift ℤ))).hom ≫ Abelian.Ext.homEquiv₀ y))
  left_inv x := by
    apply Abelian.Ext.homEquiv₀.injective
    simp only [Abelian.Ext.homEquiv₀_mk₀_apply]
    rw [pushforwardCohomologyMap_zero_homEquiv₀]
    simp only [Iso.hom_inv_id_assoc, Equiv.apply_symm_apply]
  right_inv y := by
    apply Abelian.Ext.homEquiv₀.injective
    rw [pushforwardCohomologyMap_zero_homEquiv₀]
    simp only [Abelian.Ext.homEquiv₀_mk₀_apply,
      Equiv.symm_apply_apply, Iso.inv_hom_id_assoc]
  map_add' := (pushforwardCohomologyMap g F 0).map_add

/-- The canonical pushforward cohomology map is bijective in degree zero. -/
lemma pushforwardCohomologyMap_zero_bijective
    (F : Sheaf AddCommGrpCat.{u} S) :
    Function.Bijective (pushforwardCohomologyMap g F 0) :=
  (pushforwardCohomologyMapZeroAddEquiv g F).bijective

/-- For a flasque coefficient sheaf, the canonical pushforward cohomology map is
bijective in every positive degree: both its source and target vanish. -/
lemma pushforwardCohomologyMap_succ_bijective_of_isFlasque
    (F : Sheaf AddCommGrpCat.{u} S) [F.IsFlasque] (n : ℕ) :
    Function.Bijective (pushforwardCohomologyMap g F (n + 1)) := by
  let _ : Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) :=
    subsingleton_H_of_isFlasque n F
  let _ : Subsingleton (CategoryTheory.Sheaf.H
      ((pushforward AddCommGrpCat.{u} g).obj F) (n + 1)) :=
    subsingleton_H_of_isFlasque n _
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _,
    fun y ↦ ⟨0, Subsingleton.elim _ y⟩⟩

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Modules

/-- For every scheme morphism and every module, the canonical pushforward cohomology map
is bijective in degree zero. -/
lemma pushforwardCohomologyMap_zero_bijective
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    Function.Bijective (pushforwardCohomologyMap f M 0) := by
  change Function.Bijective
    (TopCat.Sheaf.pushforwardCohomologyMap f.base
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) 0)
  exact TopCat.Sheaf.pushforwardCohomologyMap_zero_bijective f.base _

/-- If the underlying abelian sheaf of a scheme module is flasque, its canonical
pushforward cohomology map is bijective in every positive degree. -/
lemma pushforwardCohomologyMap_succ_bijective_of_isFlasque
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    [TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)]
    (n : ℕ) :
    Function.Bijective (pushforwardCohomologyMap f M (n + 1)) := by
  change Function.Bijective
    (TopCat.Sheaf.pushforwardCohomologyMap f.base
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) (n + 1))
  exact TopCat.Sheaf.pushforwardCohomologyMap_succ_bijective_of_isFlasque
    f.base _ n

end AlgebraicGeometry.Scheme.Modules
