module

public import StacksAndModuli.API.SheafFlatteningProjectiveRank
public import StacksAndModuli.API.SchemeModuleStalkwiseIso
public import StacksAndModuli.API.SchemeModulesGlobalSectionsIso
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Rank zero for zero scheme modules

A zero sheaf of modules is finite locally free of rank zero.  This elementary
bridge is useful when a geometric construction produces a cokernel: an
epimorphism makes that cokernel a zero object, while flattening strata record
the same conclusion as projectivity of rank zero.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.isProjectiveOfRank_zero_of_isZero`;
* `AlgebraicGeometry.Scheme.Modules.isZero_of_isProjectiveOfRank_zero`;
* `AlgebraicGeometry.Scheme.Modules.cokernel_isProjectiveOfRank_zero_iff_epi`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A zero sheaf of modules is finite locally free of rank zero. -/
theorem isProjectiveOfRank_zero_of_isZero (M : X.Modules) (hM : IsZero M) :
    IsProjectiveOfRank 0 M := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  haveI : Subsingleton Γ(M, U) := by
    constructor
    intro a b
    have hid : (𝟙 M : M ⟶ M) = 0 := hM.eq_of_src _ _
    have ha : a = 0 := by
      calc
        a = ((𝟙 M : M ⟶ M).app U).hom a := by simp
        _ = ((0 : M ⟶ M).app U).hom a := by rw [hid]
        _ = 0 := by simp
    have hb : b = 0 := by
      calc
        b = ((𝟙 M : M ⟶ M).app U).hom b := by simp
        _ = ((0 : M ⟶ M).app U).hom b := by rw [hid]
        _ = 0 := by simp
    exact ha.trans hb.symm
  refine ⟨⟨U, hU⟩, hxU, ?_, ?_, ?_⟩
  · change Module.Finite Γ(X, U) Γ(M, U)
    infer_instance
  · change Module.Projective Γ(X, U) Γ(M, U)
    infer_instance
  · intro p
    change Module.rankAtStalk Γ(M, U) p = 0
    exact congrFun Module.rankAtStalk_eq_zero_of_subsingleton p

/-- A quasicoherent sheaf which is finite locally free of rank zero is a zero
object. -/
theorem isZero_of_isProjectiveOfRank_zero (M : X.Modules)
    [M.IsQuasicoherent] (hM : IsProjectiveOfRank 0 M) : IsZero M := by
  rw [isZero_iff_stalkSupport_eq_empty]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x
  obtain ⟨U, hxU, hfin, hproj, hrank⟩ := hM x
  let N := affineCoordinateSheaf M U
  obtain ⟨hfin', hproj', hrank'⟩ :=
    affineCoordinateModule_finite_projective_rank M U hfin hproj hrank
  letI : Module.Finite Γ(X, U.1) (affineCoordinateModule M U) := hfin'
  letI : Module.Projective Γ(X, U.1) (affineCoordinateModule M U) := hproj'
  letI : Subsingleton (affineCoordinateModule M U) :=
    Module.rankAtStalk_eq_zero_iff_subsingleton.mp (funext hrank')
  have hCoordinateModule : IsZero (moduleSpecΓFunctor.obj N) := by
    rw [ModuleCat.isZero_iff_subsingleton]
    change Subsingleton (affineCoordinateModule M U)
    infer_instance
  have hTilde : IsZero ((tilde.functor (.of Γ(X, U.1))).obj
      (moduleSpecΓFunctor.obj N)) :=
    Functor.map_isZero _ hCoordinateModule
  haveI : IsIso N.fromTildeΓ :=
    isIso_fromTildeΓ_of_isQuasicoherent N
  have hN : IsZero N := hTilde.of_iso (asIso N.fromTildeΓ).symm
  let MU := (pullback U.1.ι).obj M
  have hMU : IsZero MU := by
    change IsZero ((pullback U.2.isoSpec.inv).obj MU) at hN
    exact IsZero.of_full_of_faithful_of_isZero
      (pullback U.2.isoSpec.inv) MU hN
  have hRestrict : IsZero ((restrictFunctor U.1.ι).obj M) :=
    hMU.of_iso ((restrictFunctorIsoPullback U.1.ι).app M)
  exact not_mem_stalkSupport_of_isZero_restrict M U.1 hRestrict hxU

/-- The cokernel of an epimorphism is finite locally free of rank zero. -/
theorem cokernel_isProjectiveOfRank_zero_of_epi {M N : X.Modules}
    (f : M ⟶ N) [Epi f] : IsProjectiveOfRank 0 (cokernel f) :=
  isProjectiveOfRank_zero_of_isZero _ (isZero_cokernel_of_epi f)

/-- For a quasicoherent cokernel, the rank-zero condition is equivalent to
surjectivity of the original morphism. -/
theorem cokernel_isProjectiveOfRank_zero_iff_epi {M N : X.Modules}
    (f : M ⟶ N) [(cokernel f).IsQuasicoherent] :
    IsProjectiveOfRank 0 (cokernel f) ↔ Epi f := by
  constructor
  · intro h
    exact Preadditive.epi_of_isZero_cokernel f
      (isZero_of_isProjectiveOfRank_zero (cokernel f) h)
  · intro h
    letI : Epi f := h
    exact cokernel_isProjectiveOfRank_zero_of_epi f

end AlgebraicGeometry.Scheme.Modules

end
