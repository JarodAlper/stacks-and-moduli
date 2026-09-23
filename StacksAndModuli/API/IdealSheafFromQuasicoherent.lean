module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.0-pullback-quasicoherent»
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Ideal sheaves from morphisms of quasicoherent modules

Given a morphism from the structure sheaf to a quasicoherent module, its kernels on
affine opens form an `IdealSheafData`.  The nontrivial point is the localization axiom:
surjectivity after localization is proved by clearing a denominator and then using
quasicoherence to clear the remaining vanishing after restriction to a basic open.

This is supporting API with no direct Stacks Project counterpart.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {M : X.Modules}

namespace Modules.Hom

/-- The ideal of sections killed by a morphism from the structure sheaf. -/
noncomputable def kernelIdeal
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (U : X.affineOpens) : Ideal Γ(X, U) where
  __ := LinearMap.ker ((φ.val.app (.op U.1)).hom)

@[simp]
lemma mem_kernelIdeal_iff
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (U : X.affineOpens) (x : Γ(X, U)) :
    x ∈ kernelIdeal φ U ↔
      AlgebraicGeometry.Scheme.Modules.Hom.app φ U.1 x = 0 := by
  rfl

/-- The affine-local kernels of a morphism from the structure sheaf to a
quasicoherent module form a quasicoherent ideal sheaf. -/
noncomputable def kernelIdealSheafData (M : X.Modules) [M.IsQuasicoherent]
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) : X.IdealSheafData where
  ideal := kernelIdeal φ
  map_ideal_basicOpen U r := by
    let resR := (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
    let resM := (M.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
    have hnat (x : Γ(X, U)) :
        resM (AlgebraicGeometry.Scheme.Modules.Hom.app φ U.1 x) =
          AlgebraicGeometry.Scheme.Modules.Hom.app φ (X.basicOpen r) (resR x) := by
      have hraw := (ConcreteCategory.congr_hom
        ((AlgebraicGeometry.Scheme.Modules.Hom.mapPresheaf φ).naturality
          (homOfLE (X.basicOpen_le r)).op) x).symm
      change resM (AlgebraicGeometry.Scheme.Modules.Hom.app φ U.1 x) =
        AlgebraicGeometry.Scheme.Modules.Hom.app φ (X.basicOpen r) (resR x) at hraw
      exact hraw
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change AlgebraicGeometry.Scheme.Modules.Hom.app φ U.1 x = 0 at hx
      change AlgebraicGeometry.Scheme.Modules.Hom.app φ (X.basicOpen r) (resR x) = 0
      rw [← hnat, hx, map_zero]
    · intro y hy
      let _ := U.2.isLocalization_basicOpen r
      obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers r) y
      have hresR : resR = algebraMap Γ(X, U) Γ(X, X.basicOpen r) := rfl
      change IsLocalization.mk' Γ(X, X.basicOpen r) x s ∈
        Ideal.map (algebraMap Γ(X, U) Γ(X, X.basicOpen r)) (kernelIdeal φ U)
      rw [IsLocalization.mk'_mem_map_algebraMap_iff]
      have hy' : AlgebraicGeometry.Scheme.Modules.Hom.app φ (X.basicOpen r)
          (IsLocalization.mk' Γ(X, X.basicOpen r) x s) = 0 := hy
      have hxres : resM (AlgebraicGeometry.Scheme.Modules.Hom.app φ U.1 x) = 0 := by
        rw [hnat]
        have hmul : resR s.1 • IsLocalization.mk' Γ(X, X.basicOpen r) x s = resR x := by
          change resR s.1 * IsLocalization.mk' Γ(X, X.basicOpen r) x s = resR x
          rw [hresR]
          exact IsLocalization.mk'_spec' Γ(X, X.basicOpen r) x s
        rw [← hmul, AlgebraicGeometry.Scheme.Modules.Hom.app_smul, hy', smul_zero]
      obtain ⟨n, hn⟩ :=
        Scheme.Modules.exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero
          M U.2 r (AlgebraicGeometry.Scheme.Modules.Hom.app φ U.1 x) hxres
      refine ⟨r ^ n, ⟨n, rfl⟩, ?_⟩
      change AlgebraicGeometry.Scheme.Modules.Hom.app φ U.1 (r ^ n * x) = 0
      change AlgebraicGeometry.Scheme.Modules.Hom.app φ U.1 (r ^ n • x) = 0
      rw [AlgebraicGeometry.Scheme.Modules.Hom.app_smul]
      exact hn

@[simp]
lemma kernelIdealSheafData_ideal (M : X.Modules) [M.IsQuasicoherent]
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ M) :
    (kernelIdealSheafData M φ).ideal = kernelIdeal φ := rfl

end Modules.Hom

end AlgebraicGeometry.Scheme
