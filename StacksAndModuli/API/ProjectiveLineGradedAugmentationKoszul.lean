module

public import StacksAndModuli.API.ProjectiveLineGradedCechHgrKoszul
public import StacksAndModuli.API.ProjectiveGradedCechAugmentationMultiplication

/-!
# Transporting the projective-line Koszul recurrence through the Čech augmentation

The Čech augmentation intertwines the signed diagonal and multiplication maps.  Hence its
degreewise bijectivity transports injectivity and middle exactness from Čech `H⁰` back to
the original graded module.  This applies in particular to `Proj.gammaStar`, whose
augmentation is bijective in every degree.

Main declarations:

* `GradedModule.injective_lineKoszulF_of_bijective_cechAug`;
* `GradedModule.exact_lineKoszulF_lineKoszulG_of_bijective_cechAug`;
* `GradedModule.surjective_lineKoszulG_of_bijective_cechAug`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {R : Type u} [CommRing R]

theorem cechAug_lineKoszulF_apply (M : GradedModule R 1) (d : ℤ)
    (x : M.obj d) (i : Fin 2) :
    (M.cechAug (d + 1)).hom (lineKoszulF M d x i) =
      lineKoszulF (M.cechHgr 0) d ((M.cechAug d).hom x) i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change (M.cechAug (d + 1)).hom (-((M.mulX 1 d).hom x)) =
      -(((M.cechHgr 0).mulX 1 d).hom ((M.cechAug d).hom x))
    rw [map_neg]
    have h := congrArg ModuleCat.Hom.hom
      (cechAug_comp_mulX' M 1 d (d + 1) rfl)
    simp only [mulX', eqToHom_refl, Category.comp_id, ModuleCat.hom_comp] at h
    exact congrArg Neg.neg (LinearMap.congr_fun h x).symm
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change (M.cechAug (d + 1)).hom ((M.mulX 0 d).hom x) =
      ((M.cechHgr 0).mulX 0 d).hom ((M.cechAug d).hom x)
    have h := congrArg ModuleCat.Hom.hom
      (cechAug_comp_mulX' M 0 d (d + 1) rfl)
    simp only [mulX', eqToHom_refl, Category.comp_id, ModuleCat.hom_comp] at h
    exact (LinearMap.congr_fun h x).symm

theorem cechAug_lineKoszulG_apply (M : GradedModule R 1) (d : ℤ)
    (y : Fin 2 → M.obj (d + 1)) :
    (M.cechAug ((d + 1) + 1)).hom (lineKoszulG M d y) =
      lineKoszulG (M.cechHgr 0) d
        (fun i ↦ (M.cechAug (d + 1)).hom (y i)) := by
  change (M.cechAug ((d + 1) + 1)).hom
      ((M.mulX 0 (d + 1)).hom (y 0) + (M.mulX 1 (d + 1)).hom (y 1)) =
    ((M.cechHgr 0).mulX 0 (d + 1)).hom ((M.cechAug (d + 1)).hom (y 0)) +
      ((M.cechHgr 0).mulX 1 (d + 1)).hom ((M.cechAug (d + 1)).hom (y 1))
  rw [map_add]
  congr 1
  · have h := congrArg ModuleCat.Hom.hom
      (cechAug_comp_mulX' M 0 (d + 1) ((d + 1) + 1) rfl)
    simp only [mulX', eqToHom_refl, Category.comp_id, ModuleCat.hom_comp] at h
    exact (LinearMap.congr_fun h (y 0)).symm
  · have h := congrArg ModuleCat.Hom.hom
      (cechAug_comp_mulX' M 1 (d + 1) ((d + 1) + 1) rfl)
    simp only [mulX', eqToHom_refl, Category.comp_id, ModuleCat.hom_comp] at h
    exact (LinearMap.congr_fun h (y 1)).symm

theorem injective_lineKoszulF_of_bijective_cechAug
    (M : GradedModule R 1) (d : ℤ)
    (hd : Function.Bijective ((M.cechAug d).hom)) :
    Function.Injective (lineKoszulF M d) := by
  intro x y hxy
  apply hd.1
  apply injective_lineKoszulF_cechHgr_zero M d
  funext i
  rw [← cechAug_lineKoszulF_apply M d x i,
    ← cechAug_lineKoszulF_apply M d y i, hxy]

theorem exact_lineKoszulF_lineKoszulG_of_bijective_cechAug
    (M : GradedModule R 1) (d : ℤ)
    (hd : Function.Bijective ((M.cechAug d).hom))
    (hd1 : Function.Bijective ((M.cechAug (d + 1)).hom)) :
    Function.Exact (lineKoszulF M d) (lineKoszulG M d) := by
  intro y
  constructor
  · intro hy
    have hyH : lineKoszulG (M.cechHgr 0) d
        (fun i ↦ (M.cechAug (d + 1)).hom (y i)) = 0 := by
      rw [← cechAug_lineKoszulG_apply M d y, hy, map_zero]
    obtain ⟨xH, hxH⟩ :=
      (exact_lineKoszulF_lineKoszulG_cechHgr M 0 d _).mp hyH
    obtain ⟨x, hx⟩ := hd.2 xH
    refine ⟨x, funext fun i ↦ hd1.1 ?_⟩
    rw [cechAug_lineKoszulF_apply M d x i, hx]
    exact congrFun hxH i
  · rintro ⟨x, rfl⟩
    have h := LinearMap.congr_fun (lineKoszulG_comp_lineKoszulF M d) x
    simpa using h

/-- Surjectivity of the projective-line Koszul map on Čech `H⁰` transports back
through bijective Čech augmentations in the two degrees which occur in its source and
target. -/
theorem surjective_lineKoszulG_of_bijective_cechAug
    (M : GradedModule R 1) (d : ℤ)
    (hd1 : Function.Bijective ((M.cechAug (d + 1)).hom))
    (hd2 : Function.Bijective ((M.cechAug ((d + 1) + 1)).hom))
    (hG : Function.Surjective (lineKoszulG (M.cechHgr 0) d)) :
    Function.Surjective (lineKoszulG M d) := by
  intro z
  obtain ⟨yH, hyH⟩ := hG ((M.cechAug ((d + 1) + 1)).hom z)
  choose y hy using fun i ↦ hd1.2 (yH i)
  refine ⟨y, hd2.1 ?_⟩
  rw [cechAug_lineKoszulG_apply]
  have hy' : (fun i ↦ (M.cechAug (d + 1)).hom (y i)) = yH :=
    funext hy
  rw [hy', hyH]

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
