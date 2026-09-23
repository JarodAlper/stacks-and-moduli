module

public import StacksAndModuli.API.ProjectiveLineGradedCechKoszul

/-!
# The Koszul recurrence on projective-line Čech cohomology

The short exact Čech-cochain recurrence is transported through the finite-sum comparison
to the standard signed Koszul maps on graded Čech cohomology.  In particular the first map
is injective on `H⁰`, and the two maps are exact in the middle on every `H^q`.

Main declarations:

* `GradedModule.injective_lineKoszulF_cechHgr_zero`;
* `GradedModule.exact_lineKoszulF_lineKoszulG_cechHgr`.
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

theorem homologyMap_lineCechKoszulF_comp_cechHgrPowIso
    (M : GradedModule R 1) (q : ℕ) (d : ℤ) :
    HomologicalComplex.homologyMap (lineCechKoszulF M d) q ≫
        (cechHgrPowIso M 2 q (d + 1)).hom =
      ModuleCat.ofHom (lineKoszulF (M.cechHgr q) d) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ funext fun i ↦ ?_)
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · change
      (HomologicalComplex.homologyMap
          (cechComplexMap (M.powProj 2 0) (d + 1)) q).hom
          ((HomologicalComplex.homologyMap (lineCechKoszulF M d) q).hom x) =
        -((HomologicalComplex.homologyMap (M.cechMulX 1 d) q).hom x)
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      ← HomologicalComplex.homologyMap_comp,
      lineCechKoszulF_comp_powProj_zero,
      HomologicalComplex.homologyMap_neg]
    rfl
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change
      (HomologicalComplex.homologyMap
          (cechComplexMap (M.powProj 2 1) (d + 1)) q).hom
          ((HomologicalComplex.homologyMap (lineCechKoszulF M d) q).hom x) =
        (HomologicalComplex.homologyMap (M.cechMulX 0 d) q).hom x
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      ← HomologicalComplex.homologyMap_comp,
      lineCechKoszulF_comp_powProj_one]

theorem cechComplexMap_powCoord_zero_comp_lineCechKoszulG
    (M : GradedModule R 1) (d : ℤ) :
    cechComplexMap (M.powCoord 2 0) (d + 1) ≫ lineCechKoszulG M d =
      M.cechMulX 0 (d + 1) := by
  rw [lineCechKoszulG]
  simp only [Preadditive.comp_add]
  rw [← Category.assoc, ← Category.assoc]
  rw [← cechComplexMap_comp,
    M.powCoord_powProj 2 0, cechComplexMap_id, Category.id_comp]
  rw [← cechComplexMap_comp,
    cechComplexMap_powCoord_powProj_ne M 2 (by decide : (0 : Fin 2) ≠ 1) (d + 1),
    zero_comp, add_zero]

theorem cechComplexMap_powCoord_one_comp_lineCechKoszulG
    (M : GradedModule R 1) (d : ℤ) :
    cechComplexMap (M.powCoord 2 1) (d + 1) ≫ lineCechKoszulG M d =
      M.cechMulX 1 (d + 1) := by
  rw [lineCechKoszulG]
  simp only [Preadditive.comp_add]
  rw [← Category.assoc, ← Category.assoc]
  rw [← cechComplexMap_comp,
    cechComplexMap_powCoord_powProj_ne M 2 (by decide : (1 : Fin 2) ≠ 0) (d + 1),
    zero_comp, zero_add]
  rw [← cechComplexMap_comp,
    M.powCoord_powProj 2 1, cechComplexMap_id, Category.id_comp]

theorem cechHgrPowIso_inv_comp_homologyMap_lineCechKoszulG
    (M : GradedModule R 1) (q : ℕ) (d : ℤ) :
    (cechHgrPowIso M 2 q (d + 1)).inv ≫
        HomologicalComplex.homologyMap (lineCechKoszulG M d) q =
      ModuleCat.ofHom (lineKoszulG (M.cechHgr q) d) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  change
    (HomologicalComplex.homologyMap (lineCechKoszulG M d) q).hom
        ((∑ ρ : Fin 2,
          (HomologicalComplex.homologyMap
            (cechComplexMap (M.powCoord 2 ρ) (d + 1)) q).hom ∘ₗ
          LinearMap.proj (R := R)
            (φ := fun _ : Fin 2 => (M.cechComplex (d + 1)).homology q) ρ) x) =
      (HomologicalComplex.homologyMap (M.cechMulX 0 (d + 1)) q).hom (x 0) +
        (HomologicalComplex.homologyMap (M.cechMulX 1 (d + 1)) q).hom (x 1)
  rw [LinearMap.sum_apply, map_sum]
  simp only [Fin.sum_univ_two, LinearMap.comp_apply]
  congr 1
  · rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      ← HomologicalComplex.homologyMap_comp,
      cechComplexMap_powCoord_zero_comp_lineCechKoszulG]
    rfl
  · rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      ← HomologicalComplex.homologyMap_comp,
      cechComplexMap_powCoord_one_comp_lineCechKoszulG]
    rfl

theorem injective_lineKoszulF_cechHgr_zero
    (M : GradedModule R 1) (d : ℤ) :
    Function.Injective (lineKoszulF (M.cechHgr 0) d) := by
  intro x y hxy
  apply injective_homologyMap_lineCechKoszulF_zero M d
  apply (cechHgrPowIso M 2 0 (d + 1)).toLinearEquiv.injective
  have h := congrArg ModuleCat.Hom.hom
    (homologyMap_lineCechKoszulF_comp_cechHgrPowIso M 0 d)
  have hx := LinearMap.congr_fun h x
  have hy := LinearMap.congr_fun h y
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx hy
  exact Eq.trans hx (Eq.trans hxy hy.symm)

theorem exact_lineKoszulF_lineKoszulG_cechHgr
    (M : GradedModule R 1) (q : ℕ) (d : ℤ) :
    Function.Exact (lineKoszulF (M.cechHgr q) d)
      (lineKoszulG (M.cechHgr q) d) := by
  let e := cechHgrPowIso M 2 q (d + 1)
  let f := HomologicalComplex.homologyMap (lineCechKoszulF M d) q
  let g := HomologicalComplex.homologyMap (lineCechKoszulG M d) q
  have hf : f ≫ e.hom = ModuleCat.ofHom (lineKoszulF (M.cechHgr q) d) :=
    homologyMap_lineCechKoszulF_comp_cechHgrPowIso M q d
  have hg : e.inv ≫ g = ModuleCat.ofHom (lineKoszulG (M.cechHgr q) d) :=
    cechHgrPowIso_inv_comp_homologyMap_lineCechKoszulG M q d
  have hex : Function.Exact f.hom g.hom :=
    exact_homologyMap_lineCechKoszulF_lineCechKoszulG M q d
  intro y
  constructor
  · intro hy
    have hgy : g.hom (e.inv.hom y) = 0 := by
      have h := congrArg ModuleCat.Hom.hom hg
      have hy' := LinearMap.congr_fun h y
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hy'
      exact Eq.trans hy' hy
    obtain ⟨x, hx⟩ := (hex (e.inv.hom y)).mp hgy
    refine ⟨x, ?_⟩
    have h := congrArg ModuleCat.Hom.hom hf
    have hx' := LinearMap.congr_fun h x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx'
    have hei := congrArg ModuleCat.Hom.hom e.inv_hom_id
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at hei
    have heiy := LinearMap.congr_fun hei y
    exact Eq.trans hx'.symm (Eq.trans
      (congrArg e.hom.hom hx)
      heiy)
  · rintro ⟨x, rfl⟩
    have hzero : g.hom (f.hom x) = 0 :=
      (hex (f.hom x)).mpr ⟨x, rfl⟩
    have hfapp := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hf) x
    have hgapp := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hg)
      (lineKoszulF (M.cechHgr q) d x)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hfapp hgapp
    have hinv : e.inv.hom (lineKoszulF (M.cechHgr q) d x) = f.hom x := by
      have hei := congrArg ModuleCat.Hom.hom e.hom_inv_id
      simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at hei
      have heix := LinearMap.congr_fun hei (f.hom x)
      exact Eq.trans (congrArg e.inv.hom hfapp.symm)
        heix
    exact Eq.trans hgapp.symm (Eq.trans (congrArg g.hom hinv) hzero)

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
