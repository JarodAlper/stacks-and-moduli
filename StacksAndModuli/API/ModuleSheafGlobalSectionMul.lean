module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Multiplication by a global section of a module sheaf

A global function on a scheme acts compatibly on the sections of every module sheaf.
This file bundles that action as an endomorphism in the category of module sheaves.

Main declaration:

* `Scheme.Modules.mulByGlobalSection`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A morphism of module sheaves is a monomorphism if it is injective on sections
over every affine open. -/
lemma mono_of_app_injective_affine {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (h : ∀ U : X.affineOpens, Function.Injective (f.app U.1).hom) : Mono f := by
  apply Functor.mono_of_mono_map (SheafOfModules.forget X.ringCatSheaf)
  apply _root_.PresheafOfModules.mono_of_injective
  intro U
  change Function.Injective (f.app U.unop).hom
  intro s₁ s₂ hs
  refine M.isSheaf.section_ext (U := U) ?_
  intro x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU : W ≤ U.unop⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.unop.2
  refine ⟨W, hWU, hxW, ?_⟩
  apply h ⟨W, hW⟩
  calc
    (f.app W).hom ((M.presheaf.map (homOfLE hWU).op).hom s₁) =
        (N.presheaf.map (homOfLE hWU).op).hom ((f.app U.unop).hom s₁) :=
      CategoryTheory.congr_fun
        (f.mapPresheaf.naturality (homOfLE hWU).op) s₁
    _ = (N.presheaf.map (homOfLE hWU).op).hom ((f.app U.unop).hom s₂) :=
      congrArg (N.presheaf.map (homOfLE hWU).op).hom hs
    _ = (f.app W).hom ((M.presheaf.map (homOfLE hWU).op).hom s₂) :=
      (CategoryTheory.congr_fun
        (f.mapPresheaf.naturality (homOfLE hWU).op) s₂).symm

/-- Multiplication by a global function, as an endomorphism of a sheaf of modules. -/
noncomputable def mulByGlobalSection {X : Scheme.{u}} (M : X.Modules)
    (t : Γ(X, ⊤)) : M ⟶ M :=
  ⟨{
    app := fun U ↦ ModuleCat.ofHom (LinearMap.lsmul
      Γ(X, U.unop) Γ(M, U.unop)
      ((X.presheaf.map
        (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom t))
    naturality := by
      intro U V i
      apply (forget₂ _ AddCommGrpCat).map_injective
      change M.presheaf.map i.unop.op ≫
          M.smul ((X.presheaf.map
            (homOfLE (show V.unop ≤ ⊤ from le_top)).op).hom t) =
        M.smul ((X.presheaf.map
            (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom t) ≫
          M.presheaf.map i.unop.op
      rw [M.map_comp_smul i.unop]
      congr 1
      congr 1
      symm
      rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
      congr 1
  }⟩

@[simp]
lemma mulByGlobalSection_app {X : Scheme.{u}} (M : X.Modules)
    (t : Γ(X, ⊤)) (U : X.Opens) :
    (mulByGlobalSection M t).val.app (op U) =
      ModuleCat.ofHom (LinearMap.lsmul Γ(X, U) Γ(M, U)
        ((X.presheaf.map (homOfLE le_top).op).hom t)) := rfl

@[simp]
lemma mulByGlobalSection_app_apply {X : Scheme.{u}} (M : X.Modules)
    (t : Γ(X, ⊤)) (U : X.Opens) (x : Γ(M, U)) :
    ((mulByGlobalSection M t).val.app (op U)).hom x =
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom t • x := rfl

@[simp]
lemma mulByGlobalSection_app_top {X : Scheme.{u}} (M : X.Modules)
    (t : Γ(X, ⊤)) :
    (mulByGlobalSection M t).val.app (op ⊤) =
      ModuleCat.ofHom (LinearMap.lsmul Γ(X, ⊤) Γ(M, ⊤) t) := by
  rw [mulByGlobalSection_app]
  congr 1
  simpa using X.presheaf.map_id t

@[simp]
lemma mulByGlobalSection_app_top_apply {X : Scheme.{u}} (M : X.Modules)
    (t : Γ(X, ⊤)) (x : Γ(M, ⊤)) :
    ((mulByGlobalSection M t).val.app (op ⊤)).hom x = t • x := by
  rw [mulByGlobalSection_app_apply]
  congr 1
  simpa using X.presheaf.map_id t

/-- Multiplication by a global function is a monomorphism if the function has no
torsion on sections over affine opens. -/
lemma mulByGlobalSection_mono_of_smul_eq_zero_affine {X : Scheme.{u}}
    (M : X.Modules) (t : Γ(X, ⊤))
    (h : ∀ (U : X.affineOpens) (x : Γ(M, U.1)),
      (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom t • x = 0 →
        x = 0) : Mono (mulByGlobalSection M t) := by
  apply mono_of_app_injective_affine
  intro U x y hxy
  apply sub_eq_zero.mp
  apply h U (x - y)
  rw [smul_sub]
  change (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom t • x =
    (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom t • y at hxy
  rw [hxy, sub_self]

end AlgebraicGeometry.Scheme.Modules

end
