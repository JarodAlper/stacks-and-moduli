module

public import StacksAndModuli.API.ProjectiveLineGradedKoszul

/-!
# The Čech Koszul recurrence on projective one-space

The localized two-variable Koszul recurrence is degreewise short exact on the standard
Čech complex.  This file packages those maps as a short exact sequence of cochain
complexes and derives injectivity and middle exactness on Čech cohomology.  These are the
cohomological inputs for the projective-line flatness-persistence argument.

Main declarations:

* `GradedModule.lineCechKoszulShortComplex_shortExact`;
* `GradedModule.injective_homologyMap_lineCechKoszulF_zero`;
* `GradedModule.exact_homologyMap_lineCechKoszulF_lineCechKoszulG`.
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

theorem locPowProj_eq_locMap_powProj (M : GradedModule R 1)
    (l : List (Fin 2)) (r : ℕ) (ρ : Fin r) (d : ℤ) :
    M.locPowProj l r ρ d = (locMap l (M.powProj r ρ)).app d := by
  refine ModuleCat.hom_ext ?_
  refine Module.DirectLimit.hom_ext fun j ↦ ?_
  refine LinearMap.ext fun x ↦ ?_
  change (M.locPowProj l r ρ d).hom (((M.pow r).locIncl l d j).hom x) =
    ((locMap l (M.powProj r ρ)).app d).hom (((M.pow r).locIncl l d j).hom x)
  rw [M.locIncl_locPowProj l r ρ d j x,
    locMap_locIncl_apply (M.pow r) l (M.powProj r ρ) d j x]
  rfl

noncomputable def cechCochainPowIso (M : GradedModule R 1)
    (r p : ℕ) (d : ℤ) :
    (M.pow r).cechCochain p d ≅
      ModuleCat.of R (Fin r → M.cechCochain p d) where
  hom := ModuleCat.ofHom
    { toFun := fun c ρ τ ↦ (M.locPowIso τ.toList r d).hom.hom (c τ) ρ
      map_add' := fun c c' ↦ by
        funext ρ τ
        simp
      map_smul' := fun a c ↦ by
        funext ρ τ
        simp }
  inv := ModuleCat.ofHom
    { toFun := fun c τ ↦ (M.locPowIso τ.toList r d).inv.hom (fun ρ ↦ c ρ τ)
      map_add' := fun c c' ↦ by
        funext τ
        change (M.locPowIso τ.toList r d).inv.hom
            ((fun ρ ↦ c ρ τ) + (fun ρ ↦ c' ρ τ)) = _
        rw [map_add]
        rfl
      map_smul' := fun a c ↦ by
        funext τ
        change (M.locPowIso τ.toList r d).inv.hom
            (a • (fun ρ ↦ c ρ τ)) = _
        rw [map_smul]
        rfl }
  hom_inv_id := by
    refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ funext fun τ ↦ ?_)
    exact (M.locPowIso τ.toList r d).hom_inv_id_apply (c τ)
  inv_hom_id := by
    refine ModuleCat.hom_ext (LinearMap.ext fun c ↦ funext fun ρ ↦ funext fun τ ↦ ?_)
    have h := (M.locPowIso τ.toList r d).inv_hom_id_apply (fun σ ↦ c σ τ)
    exact congrFun h ρ

theorem cechCochainPowIso_hom_apply (M : GradedModule R 1)
    (r p : ℕ) (d : ℤ) (c : (M.pow r).cechCochain p d)
    (ρ : Fin r) (τ : CechIdx 1 p) :
    (cechCochainPowIso M r p d).hom.hom c ρ τ =
      ((cechComplexMap (M.powProj r ρ) d).f p).hom c τ := by
  change (M.locPowToPi τ.toList r d).hom (c τ) ρ =
    ((locMap τ.toList (M.powProj r ρ)).app d).hom (c τ)
  change (M.locPowProj τ.toList r ρ d).hom (c τ) = _
  rw [locPowProj_eq_locMap_powProj]

noncomputable def lineCechKoszulF (M : GradedModule R 1) (d : ℤ) :
    M.cechComplex d ⟶ (M.pow 2).cechComplex (d + 1) :=
  -(M.cechMulX 1 d ≫ cechComplexMap (M.powCoord 2 0) (d + 1)) +
    (M.cechMulX 0 d ≫ cechComplexMap (M.powCoord 2 1) (d + 1))

noncomputable def lineCechKoszulG (M : GradedModule R 1) (d : ℤ) :
    (M.pow 2).cechComplex (d + 1) ⟶ M.cechComplex ((d + 1) + 1) :=
  cechComplexMap (M.powProj 2 0) (d + 1) ≫ M.cechMulX 0 (d + 1) +
    cechComplexMap (M.powProj 2 1) (d + 1) ≫ M.cechMulX 1 (d + 1)

theorem lineCechKoszulF_comp_lineCechKoszulG
    (M : GradedModule R 1) (d : ℤ) :
    lineCechKoszulF M d ≫ lineCechKoszulG M d = 0 := by
  rw [lineCechKoszulF, lineCechKoszulG]
  simp only [Preadditive.neg_comp, Preadditive.add_comp, Preadditive.comp_add,
    Category.assoc]
  rw [← Category.assoc (cechComplexMap (M.powCoord 2 0) (d + 1))
    (cechComplexMap (M.powProj 2 0) (d + 1))]
  rw [← cechComplexMap_comp,
    M.powCoord_powProj 2 0, cechComplexMap_id, Category.id_comp]
  rw [← Category.assoc (cechComplexMap (M.powCoord 2 1) (d + 1))
    (cechComplexMap (M.powProj 2 0) (d + 1))]
  rw [← cechComplexMap_comp,
    cechComplexMap_powCoord_powProj_ne M 2 (by decide : (1 : Fin 2) ≠ 0) (d + 1),
    zero_comp, comp_zero, add_zero]
  rw [← Category.assoc (cechComplexMap (M.powCoord 2 0) (d + 1))
    (cechComplexMap (M.powProj 2 1) (d + 1))]
  rw [← cechComplexMap_comp,
    cechComplexMap_powCoord_powProj_ne M 2 (by decide : (0 : Fin 2) ≠ 1) (d + 1),
    zero_comp, comp_zero, neg_zero, zero_add]
  rw [← Category.assoc (cechComplexMap (M.powCoord 2 1) (d + 1))
    (cechComplexMap (M.powProj 2 1) (d + 1))]
  rw [← cechComplexMap_comp,
    M.powCoord_powProj 2 1, cechComplexMap_id, Category.id_comp]
  rw [M.cechMulX_comm 1 0 d]
  exact neg_add_cancel _

theorem lineCechKoszulF_comp_powProj_zero
    (M : GradedModule R 1) (d : ℤ) :
    lineCechKoszulF M d ≫ cechComplexMap (M.powProj 2 0) (d + 1) =
      -M.cechMulX 1 d := by
  rw [lineCechKoszulF]
  simp only [Preadditive.neg_comp, Preadditive.add_comp, Category.assoc]
  rw [← cechComplexMap_comp,
    M.powCoord_powProj 2 0, cechComplexMap_id, Category.comp_id]
  rw [← cechComplexMap_comp,
    cechComplexMap_powCoord_powProj_ne M 2 (by decide : (1 : Fin 2) ≠ 0) (d + 1),
    comp_zero, add_zero]

theorem lineCechKoszulF_comp_powProj_one
    (M : GradedModule R 1) (d : ℤ) :
    lineCechKoszulF M d ≫ cechComplexMap (M.powProj 2 1) (d + 1) =
      M.cechMulX 0 d := by
  rw [lineCechKoszulF]
  simp only [Preadditive.neg_comp, Preadditive.add_comp, Category.assoc]
  rw [← cechComplexMap_comp,
    cechComplexMap_powCoord_powProj_ne M 2 (by decide : (0 : Fin 2) ≠ 1) (d + 1),
    comp_zero, neg_zero, zero_add]
  rw [← cechComplexMap_comp,
    M.powCoord_powProj 2 1, cechComplexMap_id, Category.comp_id]

theorem cechCochainPowIso_lineCechKoszulF_apply
    (M : GradedModule R 1) (p : ℕ) (d : ℤ)
    (c : M.cechCochain p d) (i : Fin 2) (τ : CechIdx 1 p) :
    (cechCochainPowIso M 2 p (d + 1)).hom.hom
        (((lineCechKoszulF M d).f p).hom c) i τ =
      lineKoszulF (M.loc τ.toList) d (c τ) i := by
  rw [cechCochainPowIso_hom_apply]
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · have h := congrArg (fun f ↦ f.f p)
      (lineCechKoszulF_comp_powProj_zero M d)
    have h' := congrArg ModuleCat.Hom.hom h
    have hc := LinearMap.congr_fun h' c
    exact congrFun hc τ
  · have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have h := congrArg (fun f ↦ f.f p)
      (lineCechKoszulF_comp_powProj_one M d)
    have h' := congrArg ModuleCat.Hom.hom h
    have hc := LinearMap.congr_fun h' c
    exact congrFun hc τ

theorem lineCechKoszulG_apply
    (M : GradedModule R 1) (p : ℕ) (d : ℤ)
    (c : (M.pow 2).cechCochain p (d + 1)) (τ : CechIdx 1 p) :
    ((lineCechKoszulG M d).f p).hom c τ =
      lineKoszulG (M.loc τ.toList) d
        (fun i ↦ (cechCochainPowIso M 2 p (d + 1)).hom.hom c i τ) := by
  change ((M.loc τ.toList).mulX 0 (d + 1)).hom
        (((locMap τ.toList (M.powProj 2 0)).app (d + 1)).hom (c τ)) +
      ((M.loc τ.toList).mulX 1 (d + 1)).hom
        (((locMap τ.toList (M.powProj 2 1)).app (d + 1)).hom (c τ)) = _
  change _ + _ =
    ((M.loc τ.toList).mulX 0 (d + 1)).hom
        ((cechCochainPowIso M 2 p (d + 1)).hom.hom c 0 τ) +
      ((M.loc τ.toList).mulX 1 (d + 1)).hom
        ((cechCochainPowIso M 2 p (d + 1)).hom.hom c 1 τ)
  exact congrArg₂ (fun x y ↦ x + y)
    (congrArg (fun x ↦ ((M.loc τ.toList).mulX 0 (d + 1)).hom x)
      (cechCochainPowIso_hom_apply M 2 p (d + 1) c 0 τ).symm)
    (congrArg (fun x ↦ ((M.loc τ.toList).mulX 1 (d + 1)).hom x)
      (cechCochainPowIso_hom_apply M 2 p (d + 1) c 1 τ).symm)

lemma cechIdx_toList_ne_nil (p : ℕ) (τ : CechIdx 1 p) : τ.toList ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  rw [τ.length_eq] at hlen
  simp at hlen

theorem injective_lineCechKoszulF_f
    (M : GradedModule R 1) (p : ℕ) (d : ℤ) :
    Function.Injective ((lineCechKoszulF M d).f p).hom := by
  intro c c' hcc'
  funext τ
  apply (lineKoszul_shortExact_loc M τ.toList (cechIdx_toList_ne_nil p τ) d).1
  funext i
  calc
    lineKoszulF (M.loc τ.toList) d (c τ) i =
        (cechCochainPowIso M 2 p (d + 1)).hom.hom
          (((lineCechKoszulF M d).f p).hom c) i τ :=
      (cechCochainPowIso_lineCechKoszulF_apply M p d c i τ).symm
    _ = (cechCochainPowIso M 2 p (d + 1)).hom.hom
          (((lineCechKoszulF M d).f p).hom c') i τ := by rw [hcc']
    _ = lineKoszulF (M.loc τ.toList) d (c' τ) i :=
      cechCochainPowIso_lineCechKoszulF_apply M p d c' i τ

theorem surjective_lineCechKoszulG_f
    (M : GradedModule R 1) (p : ℕ) (d : ℤ) :
    Function.Surjective ((lineCechKoszulG M d).f p).hom := by
  intro z
  have hτ : ∀ τ : CechIdx 1 p, ∃ y : Fin 2 → (M.loc τ.toList).obj (d + 1),
      lineKoszulG (M.loc τ.toList) d y = z τ := by
    intro τ
    exact (lineKoszul_shortExact_loc M τ.toList (cechIdx_toList_ne_nil p τ) d).2.2 (z τ)
  choose y hy using hτ
  let Y : Fin 2 → M.cechCochain p (d + 1) := fun i τ ↦ y τ i
  let c : (M.pow 2).cechCochain p (d + 1) :=
    (cechCochainPowIso M 2 p (d + 1)).inv.hom Y
  refine ⟨c, funext fun τ ↦ ?_⟩
  rw [lineCechKoszulG_apply]
  have hc := (cechCochainPowIso M 2 p (d + 1)).inv_hom_id_apply Y
  calc
    lineKoszulG (M.loc τ.toList) d
        (fun i ↦ (cechCochainPowIso M 2 p (d + 1)).hom.hom c i τ) =
      lineKoszulG (M.loc τ.toList) d (y τ) := by
        congr 1
        funext i
        exact congrFun (congrFun hc i) τ
    _ = z τ := hy τ

theorem exact_lineCechKoszulF_f_lineCechKoszulG_f
    (M : GradedModule R 1) (p : ℕ) (d : ℤ) :
    Function.Exact ((lineCechKoszulF M d).f p).hom
      ((lineCechKoszulG M d).f p).hom := by
  intro c
  constructor
  · intro hc
    have hτ : ∀ τ : CechIdx 1 p, ∃ x : (M.loc τ.toList).obj d,
        lineKoszulF (M.loc τ.toList) d x =
          fun i ↦ (cechCochainPowIso M 2 p (d + 1)).hom.hom c i τ := by
      intro τ
      exact ((lineKoszul_shortExact_loc M τ.toList
        (cechIdx_toList_ne_nil p τ) d).2.1 _).mp (by
          rw [← lineCechKoszulG_apply]
          exact congrFun hc τ)
    choose x hx using hτ
    let z : (M.cechComplex d).X p := fun τ ↦ x τ
    refine ⟨z, ?_⟩
    apply (cechCochainPowIso M 2 p (d + 1)).toLinearEquiv.injective
    funext i τ
    exact Eq.trans
      (cechCochainPowIso_lineCechKoszulF_apply M p d z i τ)
      (congrFun (hx τ) i)
  · rintro ⟨z, rfl⟩
    have h := congrArg (fun f ↦ f.f p)
      (lineCechKoszulF_comp_lineCechKoszulG M d)
    have h' := congrArg ModuleCat.Hom.hom h
    exact LinearMap.congr_fun h' z

/-- The degree-`d` line Koszul short complex on Čech cochains. -/
noncomputable def lineCechKoszulShortComplex (M : GradedModule R 1) (d : ℤ) :
    CategoryTheory.ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  CategoryTheory.ShortComplex.mk (lineCechKoszulF M d) (lineCechKoszulG M d)
    (lineCechKoszulF_comp_lineCechKoszulG M d)

/-- The line Koszul short complex on Čech cochains is short exact. -/
theorem lineCechKoszulShortComplex_shortExact
    (M : GradedModule R 1) (d : ℤ) :
    (lineCechKoszulShortComplex M d).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro p
  exact
    { exact := by
        rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
        change LinearMap.range ((lineCechKoszulF M d).f p).hom =
          LinearMap.ker ((lineCechKoszulG M d).f p).hom
        exact (LinearMap.exact_iff.mp
          (exact_lineCechKoszulF_f_lineCechKoszulG_f M p d)).symm
      mono_f := (ModuleCat.mono_iff_injective _).mpr
        (injective_lineCechKoszulF_f M p d)
      epi_g := (ModuleCat.epi_iff_surjective _).mpr
        (surjective_lineCechKoszulG_f M p d) }

/-- The line Koszul map is injective on zeroth Čech cohomology. -/
theorem injective_homologyMap_lineCechKoszulF_zero
    (M : GradedModule R 1) (d : ℤ) :
    Function.Injective
      (HomologicalComplex.homologyMap (lineCechKoszulF M d) 0).hom := by
  letI : Mono ((lineCechKoszulF M d).f 0) :=
    (ModuleCat.mono_iff_injective _).mpr
      (injective_lineCechKoszulF_f M 0 d)
  have hm := HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
    (lineCechKoszulF M d) 0 (fun i ↦ by simp)
  exact (ModuleCat.mono_iff_injective _).mp hm

/-- The two line Koszul maps are exact on Čech cohomology. -/
theorem exact_homologyMap_lineCechKoszulF_lineCechKoszulG
    (M : GradedModule R 1) (q : ℕ) (d : ℤ) :
    Function.Exact
      (HomologicalComplex.homologyMap (lineCechKoszulF M d) q).hom
      (HomologicalComplex.homologyMap (lineCechKoszulG M d) q).hom := by
  have h := (lineCechKoszulShortComplex_shortExact M d).homology_exact₂ q
  rw [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
  exact h

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
