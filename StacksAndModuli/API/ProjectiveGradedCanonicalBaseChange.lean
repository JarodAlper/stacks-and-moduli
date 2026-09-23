module

public import StacksAndModuli.API.ProjectiveGradedRelativeCBC
public import StacksAndModuli.API.ProjectiveGradedFreeAug
public import StacksAndModuli.API.ProjGammaStarQuotientFlat
public import StacksAndModuli.API.ProjGammaStarCechBaseChange

/-!
# Canonical arbitrary-ring base change for projective global sections

The relative Čech package constructs an arbitrary-ring base-change equivalence on
degree-zero Čech cohomology.  This file identifies that equivalence with the canonical
global-sections comparison for a flat finitely presented sheaf on polynomial projective
space.

The key point is compatibility of the Čech augmentation with extension of scalars.  Once
the original bounded Čech complex is exact in positive degrees, flatness of its cochains
makes its cocycles commute with every coefficient change.  Naturality of the augmentation
then transfers this statement through the already canonical comparison
`gammaStarBaseChangeHom`.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.GradedModule.bijective_cechAug_baseChange`;
* `AlgebraicGeometry.ProjectiveSpace.`
  `exists_bound_bijective_gammaStarBaseChangeApp_of_isFG_of_flatOver`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {k A : Type u} [CommRing k] [CommRing A] [Algebra k A]
  {n : ℕ} (M : GradedModule k n)

/-- Extension of scalars carries an equality transport to the corresponding equality
transport after base change, on pure tensors. -/
lemma baseChange_eqToHom_tmul {d e : ℤ} (h : d = e) (a : A) (x : M.obj d) :
    (eqToHom (congrArg (M.baseChange A).obj h)).hom (a ⊗ₜ[k] x) =
      LinearMap.baseChange A (eqToHom (congrArg M.obj h)).hom (a ⊗ₜ[k] x) := by
  subst h
  rfl

/-- Localization of a base-changed graded module agrees with base change of the
localization, on the image of a pure tensor. -/
lemma locOf_baseChange_tmul (l : List (Fin (n + 1))) (d : ℤ)
    (a : A) (x : M.obj d) :
    locBaseChangeEquiv A M l d
        ((((M.baseChange A).locOf l).app d).hom (a ⊗ₜ[k] x)) =
      a ⊗ₜ[k] (((M.locOf l).app d).hom x) := by
  rw [locOf_app, locOf_app]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  have h := congrArg ModuleCat.Hom.hom
    (locIncl_locBaseChangeToTensor A M l d 0)
  simp only [ModuleCat.hom_comp] at h
  let hd : d = locDeg l d 0 := by rw [locDeg_def]; push_cast; ring
  change (locBaseChangeToTensor A M l d).hom
      (((M.baseChange A).locIncl l d 0).hom
        ((eqToHom (congrArg (M.baseChange A).obj hd)).hom (a ⊗ₜ[k] x))) = _
  rw [← LinearMap.comp_apply, h, baseChange_eqToHom_tmul M hd]
  change (LinearMap.baseChange A (M.locIncl l d 0).hom)
      ((LinearMap.baseChange A (eqToHom (congrArg M.obj hd)).hom) (a ⊗ₜ[k] x)) = _
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
    LinearMap.baseChange_tmul]
  rfl

/-- The degree-zero Čech cochain augmentation commutes with extension of scalars, on
pure tensors. -/
lemma cechAug₀_baseChange_tmul (d : ℤ) (a : A) (x : M.obj d) :
    cechCochainBaseChangeEquiv A M 0 d
        (((M.baseChange A).cechAug₀ d).hom (a ⊗ₜ[k] x)) =
      a ⊗ₜ[k] ((M.cechAug₀ d).hom x) := by
  apply (cechCochainBaseChangeEquiv A M 0 d).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext τ
  rw [cechCochainBaseChangeEquiv_symm_tmul]
  change ((((M.baseChange A).locOf τ.toList).app d).hom (a ⊗ₜ[k] x)) = _
  apply (locBaseChangeEquiv A M τ.toList d).injective
  rw [LinearEquiv.apply_symm_apply, locOf_baseChange_tmul]
  rfl

/-- The Čech augmentation with codomain restricted to degree-zero cocycles. -/
noncomputable def cechAugCocycles (d : ℤ) :
    M.obj d →ₗ[k] CochainComplex.cocyclesSub (M.cechComplex d) 0 :=
  LinearMap.codRestrict _ (M.cechAug₀ d).hom (fun x => by
    rw [CochainComplex.cocyclesSub, LinearMap.mem_ker,
      M.cechComplex_d_zero_one d]
    have h := congrArg ModuleCat.Hom.hom (M.cechAug₀_comp_cechD d)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact LinearMap.congr_fun h x)

/-- The augmentation to degree-zero cocycles is natural in the graded module. -/
lemma cechAugCocycles_naturality {N : GradedModule k n} (φ : M ⟶ N) (d : ℤ) :
    (CochainComplex.cocyclesMap (cechComplexMap φ d) 0).comp
        (cechAugCocycles M d) =
      (cechAugCocycles N d).comp (φ.app d).hom := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have h := congrArg ModuleCat.Hom.hom (cechAug₀_naturality φ d)
  have hx := LinearMap.congr_fun h x
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hx
  change ((cechCochainMap φ 0 d).hom ((M.cechAug₀ d).hom x)) =
    (N.cechAug₀ d).hom ((φ.app d).hom x)
  exact hx

/-- An isomorphism on degree-zero Čech cohomology induces a bijection on the
degree-zero cocycles. -/
theorem bijective_cocyclesMap_of_isIso_cechHgrMap {N : GradedModule k n}
    (φ : M ⟶ N) (d : ℤ) [IsIso ((cechHgrMap φ 0).app d)] :
    Function.Bijective
      (CochainComplex.cocyclesMap (cechComplexMap φ d) 0) := by
  let e := (CochainComplex.homologyZeroEquiv (M.cechComplex d)).symm.trans
    ((asIso ((cechHgrMap φ 0).app d)).toLinearEquiv.trans
      (CochainComplex.homologyZeroEquiv (N.cechComplex d)))
  have he : e.toLinearMap =
      CochainComplex.cocyclesMap (cechComplexMap φ d) 0 := by
    apply LinearMap.ext
    intro z
    change CochainComplex.homologyZeroEquiv (N.cechComplex d)
        ((HomologicalComplex.homologyMap (cechComplexMap φ d) 0).hom
          ((CochainComplex.homologyZeroEquiv (M.cechComplex d)).symm z)) = _
    rw [CochainComplex.homologyZeroEquiv_naturality,
      LinearEquiv.apply_symm_apply]
  rw [← he]
  exact e.bijective

/-- Bijectivity of the augmentation to cocycles reflects across a morphism which is
bijective in the chosen degree and an isomorphism on degree-zero Čech cohomology. -/
theorem bijective_cechAugCocycles_of_morphism {N : GradedModule k n}
    (φ : M ⟶ N) (d : ℤ) [IsIso ((cechHgrMap φ 0).app d)]
    (hφ : Function.Bijective ((φ.app d).hom))
    (hN : Function.Bijective (cechAugCocycles N d)) :
    Function.Bijective (cechAugCocycles M d) := by
  have hcyc := bijective_cocyclesMap_of_isIso_cechHgrMap M φ d
  have hcomp : Function.Bijective
      ((CochainComplex.cocyclesMap (cechComplexMap φ d) 0).comp
        (cechAugCocycles M d)) := by
    rw [cechAugCocycles_naturality M φ d]
    exact hN.comp hφ
  exact (hcyc.of_comp_iff' (cechAugCocycles M d)).mp (by
    simpa only [LinearMap.coe_comp] using hcomp)

/-- An isomorphism of cochain complexes induces a linear equivalence on cocycles. -/
noncomputable def cocyclesLinearEquivOfIso
    {K L : CochainComplex (ModuleCat.{u} k) ℕ} (e : K ≅ L) (i : ℕ) :
    CochainComplex.cocyclesSub K i ≃ₗ[k] CochainComplex.cocyclesSub L i where
  toLinearMap := CochainComplex.cocyclesMap e.hom i
  invFun := CochainComplex.cocyclesMap e.inv i
  left_inv x := by
    apply Subtype.ext
    change (e.inv.f i).hom ((e.hom.f i).hom x) = x
    rw [← LinearMap.comp_apply]
    have h := congrArg (fun ψ => ψ.f i) e.hom_inv_id
    simpa only [HomologicalComplex.id_f, HomologicalComplex.comp_f,
      ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.id_apply] using
        LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x
  right_inv x := by
    apply Subtype.ext
    change (e.hom.f i).hom ((e.inv.f i).hom x) = x
    rw [← LinearMap.comp_apply]
    have h := congrArg (fun ψ => ψ.f i) e.inv_hom_id
    simpa only [HomologicalComplex.id_f, HomologicalComplex.comp_f,
      ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.id_apply] using
        LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x

/-- A bijective augmentation to degree-zero cocycles stays bijective after arbitrary
coefficient change, provided the original Čech complex is a bounded exact complex of flat
modules in positive cohomological degrees. -/
theorem bijective_cechAug_baseChange (d : ℤ)
    (hflat : ∀ p : ℕ, Module.Flat k ((M.cechComplex d).X p))
    {N : ℕ} (hvan : ∀ p : ℕ, N < p → Subsingleton ((M.cechComplex d).X p))
    (hex : ∀ i : ℕ, CochainComplex.ExactAtSucc (M.cechComplex d) i)
    (hbij : Function.Bijective (cechAugCocycles M d)) :
    Function.Bijective (((M.baseChange A).cechAug d).hom) := by
  let e₀ : M.obj d ≃ₗ[k] CochainComplex.cocyclesSub (M.cechComplex d) 0 :=
    LinearEquiv.ofBijective (cechAugCocycles M d) hbij
  let eA : A ⊗[k] (M.obj d) ≃ₗ[A]
      CochainComplex.cocyclesSub ((M.baseChange A).cechComplex d) 0 :=
    (e₀.baseChange k A).trans
      ((CochainComplex.cocyclesBaseChangeEquiv
        (M.cechComplex d) hflat hvan hex A 0).trans
        (cocyclesLinearEquivOfIso
          (cechComplexBaseChangeIso A M d).symm 0))
  let augA : A ⊗[k] (M.obj d) →ₗ[A]
      CochainComplex.cocyclesSub ((M.baseChange A).cechComplex d) 0 :=
    cechAugCocycles (M.baseChange A) d
  have heA : eA.toLinearMap = augA := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        rw [map_zero, map_zero]
    | add x y hx hy =>
        rw [map_add, map_add, hx, hy]
    | tmul a x =>
        dsimp only [augA]
        apply Subtype.ext
        change ((cechComplexBaseChangeIso A M d).inv.f 0).hom
            ((CochainComplex.cocyclesBaseChangeEquiv
              (M.cechComplex d) hflat hvan hex A 0)
              (a ⊗ₜ[k] (cechAugCocycles M d x)) : _) = _
        change (cechCochainBaseChangeEquiv A M 0 d).symm
            (a ⊗ₜ[k] ((M.cechAug₀ d).hom x)) =
          ((M.baseChange A).cechAug₀ d).hom (a ⊗ₜ[k] x)
        rw [← cechAug₀_baseChange_tmul M d a x,
          LinearEquiv.symm_apply_apply]
  have hcyc : Function.Bijective (cechAugCocycles (M.baseChange A) d) := by
    change Function.Bijective augA
    rw [← heA]
    exact eA.bijective
  constructor
  · apply (M.baseChange A).injective_cechAug_of_aug₀ d
    intro x y hxy
    apply hcyc.1
    exact Subtype.ext hxy
  · apply (M.baseChange A).surjective_cechAug_of_cocycles d
    intro c hc
    let z : CochainComplex.cocyclesSub ((M.baseChange A).cechComplex d) 0 :=
      ⟨c, by
        change ((M.baseChange A).cechD 0 d).hom c = 0
        exact hc⟩
    obtain ⟨x, hx⟩ := hcyc.2 z
    exact ⟨x, congrArg Subtype.val hx⟩

end AlgebraicGeometry.ProjectiveSpace.GradedModule

namespace AlgebraicGeometry.ProjectiveSpace

open ProjectiveSpectrum.Twist

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}

set_option synthInstance.maxHeartbeats 800000 in
-- Finitely presented polynomial-`Proj` sheaves carry expensive quantified twist instances.
set_option maxHeartbeats 1000000 in
/-- For a flat finitely presented sheaf on polynomial projective space whose `Γ_*` is
finitely generated, the literal canonical global-sections comparison is bijective after
every coefficient-ring change in all sufficiently large nonnegative twists. -/
theorem exists_bound_bijective_gammaStarBaseChangeApp_of_isFG_of_flatOver
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    [F.IsFinitePresentation]
    (hFG : GradedModule.IsFG
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (Proj.polynomialToSpec (Fin (n + 1)) R) F (stdVars n R)))
    (hflat : F.FlatOver (Proj.polynomialToSpec (Fin (n + 1)) R)) :
    ∃ d₀ : ℕ, ∀ (A : Type u) [CommRing A] (f : R →+* A) (d : ℕ), d₀ ≤ d →
      Function.Bijective (gammaStarBaseChangeApp n f F (d : ℤ)) := by
  letI hqc : ∀ e : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) F e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent F e
  let M := Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (Proj.polynomialToSpec (Fin (n + 1)) R) F (stdVars n R)
  change GradedModule.IsFG M at hFG
  have hflatC : ∀ (e : ℤ) (p : ℕ), Module.Flat R ((M.cechComplex e).X p) := by
    intro e p
    exact GradedModule.flat_cechCochain_of_flat_loc M
      (fun a ↦ Proj.isFlat_loc_gammaStar_of_flatOver F a hflat) p e
  obtain ⟨d₀, hd₀⟩ :=
    GradedModule.exists_uniform_subsingleton_cechHgr_baseChange' hFG hflatC
  refine ⟨d₀.toNat, ?_⟩
  intro A _ f d hd
  letI : Algebra R A := f.toAlgebra
  have hd' : d₀ ≤ (d : ℤ) := le_trans (Int.self_le_toNat d₀) (by exact_mod_cast hd)
  have hex : ∀ i : ℕ, CochainComplex.ExactAtSucc (M.cechComplex (d : ℤ)) i :=
    GradedModule.exactAtSucc_cechComplex_of_fibrewise' M (d : ℤ) hFG
      (hflatC (d : ℤ)) (fun κ _ _ i hi ↦ hd₀ κ i hi (d : ℤ) hd')
  have hcyc : Function.Bijective (GradedModule.cechAugCocycles M (d : ℤ)) := by
    constructor
    · intro x y hxy
      apply Proj.injective_gammaStar_cechAug₀
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (Proj.polynomialToSpec (Fin (n + 1)) R) F (stdVars n R)
        (top_le_iSup_basicOpen_stdVars n R) (d : ℤ)
      exact congrArg Subtype.val hxy
    · intro z
      obtain ⟨x, hx⟩ := Proj.exists_gammaStar_cechAug₀_eq
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (Proj.polynomialToSpec (Fin (n + 1)) R) F (stdVars n R)
        (top_le_iSup_basicOpen_stdVars n R) (d : ℤ) z.1 (by
          change (M.cechD 0 (d : ℤ)).hom z.1 = 0
          exact z.2)
      exact ⟨x, Subtype.ext hx⟩
  have haugBase : Function.Bijective (((M.baseChange A).cechAug (d : ℤ)).hom) :=
    GradedModule.bijective_cechAug_baseChange M (d : ℤ)
      (hflatC (d : ℤ)) (N := n)
      (fun p hp ↦ GradedModule.subsingleton_cechComplex_X M (d : ℤ) hp)
      hex hcyc
  let N := Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
    (Proj.polynomialToSpec (Fin (n + 1)) A)
    ((Scheme.Modules.pullback (coeffMap n f)).obj F) (stdVars n A)
  have haugTarget : Function.Bijective ((N.cechAug (d : ℤ)).hom) := by
    exact bijective_gammaStar_cechAug_of_isFinitePresentation
      (Proj.polynomialToSpec (Fin (n + 1)) A)
      ((Scheme.Modules.pullback (coeffMap n f)).obj F) (d : ℤ)
  let ψ := gammaStarBaseChangeHom n f F
  haveI : IsIso ((GradedModule.cechHgrMap ψ 0).app (d : ℤ)) :=
    isIso_cechHgrMap_gammaStarBaseChangeHom_app n f F d
  have hcech : Function.Bijective
      (((GradedModule.cechHgrMap ψ 0).app (d : ℤ)).hom) :=
    ConcreteCategory.bijective_of_isIso _
  have hnat := GradedModule.cechAug_naturality ψ (d : ℤ)
  have hcomp : Function.Bijective
      ((N.cechAug (d : ℤ)).hom.comp ((ψ.app (d : ℤ)).hom)) := by
    have hEq := congrArg ModuleCat.Hom.hom hnat
    simp only [ModuleCat.hom_comp] at hEq
    rw [← hEq]
    exact hcech.comp haugBase
  have happ : Function.Bijective ((ψ.app (d : ℤ)).hom) := by
    apply (haugTarget.of_comp_iff' ((ψ.app (d : ℤ)).hom)).mp
    simpa only [LinearMap.coe_comp] using hcomp
  change Function.Bijective ((gammaStarBaseChangeHomApp n f F (d : ℤ)).hom)
  simpa only [ψ, gammaStarBaseChangeHom] using happ

end AlgebraicGeometry.ProjectiveSpace

end

end
