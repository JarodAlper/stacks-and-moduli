module

public import StacksAndModuli.API.ProjectiveGradedH0

/-!
# The augmentation `M_d ⟶ H⁰(ℙⁿ, M~(d))` on twists and free modules

Supporting API with no Stacks Project counterpart.

Naturality of the augmentation, its behaviour on `M(a)` and `M^{⊕r}`, and its bijectivity on
the free graded modules `⨁_r S(a)` in the range `d + a ≥ 0`.

These statements hold over an **arbitrary commutative base ring** — they were originally
proved in `StacksAndModuli/API/ProjectiveGradedH0Large.lean` in a `Field` context, but nothing in
them (or in `cocycle_structureModule`, which is the substance) uses inversion.  Splitting
them out is what lets the graded side of the scheme comparison
`RelativeCohomology.SchemeGlobalSectionsComparison` be constructed over the base ring of the
family rather than over a residue field.

Main declarations:
- `GradedModule.cechAug_naturality`;
- `GradedModule.bijective_cechAug_structureModule`;
- `GradedModule.bijective_cechAug_free`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable {k : Type u} [CommRing k] {n : ℕ}

/-! ## Naturality of the augmentation -/

lemma app_eqToHom {M N : GradedModule k n} (φ : M ⟶ N) {e₁ e₂ : ℤ} (h : e₁ = e₂)
    (x : M.obj e₁) :
    (φ.app e₂).hom ((eqToHom (congrArg M.obj h)).hom x)
      = (eqToHom (congrArg N.obj h)).hom ((φ.app e₁).hom x) := by
  subst h
  simp

lemma locOf_locMap_apply {M N : GradedModule k n} (φ : M ⟶ N) (l : List (Fin (n + 1)))
    (d : ℤ) (x : M.obj d) :
    ((locMap l φ).app d).hom (((M.locOf l).app d).hom x)
      = ((N.locOf l).app d).hom ((φ.app d).hom x) := by
  rw [locOf_app, locOf_app]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [locMap_locIncl_apply,
    app_eqToHom φ (show d = locDeg l d 0 by rw [locDeg_def]; push_cast; ring)]

lemma cechAug₀_naturality {M N : GradedModule k n} (φ : M ⟶ N) (d : ℤ) :
    M.cechAug₀ d ≫ cechCochainMap φ 0 d = φ.app d ≫ N.cechAug₀ d := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun τ => ?_)
  exact locOf_locMap_apply φ τ.toList d x

/-! ## Naturality of the augmentation into `H⁰` -/

lemma cechAug_naturality {M N : GradedModule k n} (φ : M ⟶ N) (d : ℤ) :
    M.cechAug d ≫ (cechHgrMap φ 0).app d = φ.app d ≫ N.cechAug d := by
  show (M.cechComplex d).liftCycles (M.cechAug₀ d) 1 (by simp)
        (by rw [M.cechComplex_d_zero_one d]; exact M.cechAug₀_comp_cechD d) ≫
      (M.cechComplex d).homologyπ 0 ≫
      HomologicalComplex.homologyMap (cechComplexMap φ d) 0
    = φ.app d ≫ (N.cechComplex d).liftCycles (N.cechAug₀ d) 1 (by simp)
        (by rw [N.cechComplex_d_zero_one d]; exact N.cechAug₀_comp_cechD d) ≫
      (N.cechComplex d).homologyπ 0
  rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap, ← Category.assoc]
  congr 1
  refine (cancel_mono ((N.cechComplex d).iCycles 0)).mp ?_
  rw [HomologicalComplex.liftCycles_i, Category.assoc,
    HomologicalComplex.liftCycles_i]
  exact cechAug₀_naturality φ d

/-! ## The augmentation on a twist -/

lemma twistLocToLoc_locOf (M : GradedModule k n) (l : List (Fin (n + 1))) (a d : ℤ) :
    ((M.twist a).locOf l).app d ≫ twistLocToLoc M l a d = (M.locOf l).app (d + a) := by
  rw [locOf_app, Category.assoc, locIncl_twistLocToLoc, ← Category.assoc, locOf_app]
  congr 1
  simp

lemma cechAug₀_twist (M : GradedModule k n) (a d : ℤ) :
    (M.twist a).cechAug₀ d ≫ (cechCochainTwistIso M a 0 d).hom
      = M.cechAug₀ (d + a) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => funext fun τ => ?_)
  show (twistLocToLoc M τ.toList a d).hom
      ((((M.twist a).locOf τ.toList).app d).hom x)
    = ((M.locOf τ.toList).app (d + a)).hom x
  have h1 := congrArg ModuleCat.Hom.hom (twistLocToLoc_locOf M τ.toList a d)
  simp only [ModuleCat.hom_comp] at h1
  exact LinearMap.congr_fun h1 x

lemma cechAug_twist (M : GradedModule k n) (a d : ℤ) :
    (M.twist a).cechAug d ≫ (cechHgrTwistIso M a 0 d).hom = M.cechAug (d + a) := by
  show (((M.twist a).cechComplex d).liftCycles ((M.twist a).cechAug₀ d) 1 (by simp)
        (by rw [(M.twist a).cechComplex_d_zero_one d]
            exact (M.twist a).cechAug₀_comp_cechD d) ≫
      ((M.twist a).cechComplex d).homologyπ 0) ≫
      HomologicalComplex.homologyMap (cechComplexTwistIso M a d).hom 0
    = (M.cechComplex (d + a)).liftCycles (M.cechAug₀ (d + a)) 1 (by simp)
        (by rw [M.cechComplex_d_zero_one (d + a)]; exact M.cechAug₀_comp_cechD (d + a)) ≫
      (M.cechComplex (d + a)).homologyπ 0
  rw [Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc,
    HomologicalComplex.liftCycles_comp_cyclesMap]
  congr 1
  refine (cancel_mono ((M.cechComplex (d + a)).iCycles 0)).mp ?_
  rw [HomologicalComplex.liftCycles_i, HomologicalComplex.liftCycles_i]
  exact cechAug₀_twist M a d

/-! ## The augmentation on the free modules of the presentation -/

lemma bijective_cechAug_twist (M : GradedModule k n) (a d : ℤ)
    (h : Function.Bijective ((M.cechAug (d + a)).hom)) :
    Function.Bijective (((M.twist a).cechAug d).hom) := by
  have hfac : (M.twist a).cechAug d
      = M.cechAug (d + a) ≫ (cechHgrTwistIso M a 0 d).inv := by
    rw [← cechAug_twist M a d, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hinv : Function.Bijective ((cechHgrTwistIso M a 0 d).inv.hom) :=
    ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
      (ModuleCat.epi_iff_surjective _).mp inferInstance⟩
  rw [hfac]
  exact hinv.comp h

lemma cechAug_pow_apply (M : GradedModule k n) (r : ℕ) (d : ℤ)
    (x : (M.pow r).obj d) (ρ : Fin r) :
    ((cechHgrPowIso M r 0 d).hom.hom (((M.pow r).cechAug d).hom x)) ρ
      = (M.cechAug d).hom (x ρ) := by
  have h := congrArg ModuleCat.Hom.hom (cechAug_naturality (powProj M r ρ) d)
  simp only [ModuleCat.hom_comp] at h
  exact LinearMap.congr_fun h x

lemma bijective_cechAug_pow (M : GradedModule k n) (r : ℕ) (d : ℤ)
    (h : Function.Bijective ((M.cechAug d).hom)) :
    Function.Bijective (((M.pow r).cechAug d).hom) := by
  have hiso : Function.Bijective ((cechHgrPowIso M r 0 d).hom.hom) :=
    ⟨(ModuleCat.mono_iff_injective _).mp inferInstance,
      (ModuleCat.epi_iff_surjective _).mp inferInstance⟩
  constructor
  · intro x y hxy
    funext ρ
    refine h.1 ?_
    rw [← cechAug_pow_apply M r d x ρ, ← cechAug_pow_apply M r d y ρ, hxy]
  · intro z
    have hz := (cechHgrPowIso M r 0 d).hom.hom z
    choose x hx using fun ρ => h.2 (((cechHgrPowIso M r 0 d).hom.hom z) ρ)
    refine ⟨(x : (M.pow r).obj d), hiso.1 ?_⟩
    funext ρ
    rw [cechAug_pow_apply M r d x ρ, hx ρ]

lemma bijective_cechAug_structureModule (d : ℤ) (hd : 0 ≤ d) :
    Function.Bijective (((structureModule k n).cechAug d).hom) :=
  ⟨injective_cechAug _ (injective_structureModule_mulX n) d,
    surjective_cechAug_of_cocycles _ d (fun c hc => cocycle_structureModule d hd c hc)⟩

/-- **The augmentation is bijective on the free modules of the presentation** once the
twist is nonnegative. -/
theorem bijective_cechAug_free (a : ℤ) (r : ℕ) (d : ℤ) (hd : 0 ≤ d + a) :
    Function.Bijective ((((((structureModule k n).twist a)).pow r).cechAug d).hom) :=
  bijective_cechAug_pow _ r d
    (bijective_cechAug_twist (structureModule k n) a d
      (bijective_cechAug_structureModule (d + a) hd))

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
