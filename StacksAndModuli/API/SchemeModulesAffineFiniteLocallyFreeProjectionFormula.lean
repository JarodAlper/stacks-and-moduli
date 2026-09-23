module

public import StacksAndModuli.API.SchemeModulesProjectionFormula
public import StacksAndModuli.API.SchemeModulesPullbackKernelVectorBundle
public import StacksAndModuli.API.TwistMonomialSections

/-!
# Projection formula for finite locally free coefficients over an affine base

A finite locally free quasicoherent sheaf on an affine scheme is a retract of a finite
free sheaf: choose finitely many global generators and split the resulting epimorphism
using projectivity of global sections.  Naturality of the canonical projection-formula
map then reduces its invertibility to the finite-free calculation.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite locally free quasicoherent sheaf on an affine scheme is a retract of a
finite free sheaf. -/
theorem exists_retract_free_of_isFiniteLocallyFree_of_isAffine
    {X : Scheme.{u}} [IsAffine X] {K : X.Modules} [K.IsQuasicoherent]
    (hK : IsFiniteLocallyFree K) :
    ∃ (J : Type u) (_ : Finite J)
      (i : K ⟶ SheafOfModules.free (R := X.ringCatSheaf) J)
      (p : SheafOfModules.free (R := X.ringCatSheaf) J ⟶ K),
      i ≫ p = 𝟙 K := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  have hs := finiteLocallyFree_sections_finite_projective_affine hK U
  letI : Module.Finite Γ(X, ⊤) Γ(K, ⊤) := hs.1
  have hfg : ∃ (J : Type u) (_ : Finite J) (s : J → Γ(K, ⊤)),
      Submodule.span Γ(X, ⊤) (Set.range s) = ⊤ :=
    Submodule.fg_iff_exists_finite_generating_family.mp
      (Module.Finite.fg_top (R := Γ(X, ⊤)) (M := Γ(K, ⊤)))
  obtain ⟨J, hJ, s, hspan⟩ := hfg
  letI : Finite J := hJ
  let p : SheafOfModules.free (R := X.ringCatSheaf) J ⟶ K :=
    freeHomOfSections s
  have hpSurj : Function.Surjective (Hom.app p ⊤) := by
    let φ : Γ(SheafOfModules.free (R := X.ringCatSheaf) J, ⊤) →ₗ[Γ(X, ⊤)]
        Γ(K, ⊤) :=
      { toFun := Hom.app p ⊤
        map_add' := fun x y ↦ (Hom.app p ⊤).hom.map_add x y
        map_smul' := fun r x ↦ Hom.app_smul p r x }
    have hφ : Function.Surjective φ := by
      apply LinearMap.range_eq_top.mp
      apply top_unique
      rw [← hspan]
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      refine ⟨Scheme.freeGenSection X i, ?_⟩
      dsimp only [φ]
      simp only [p, Scheme.freeGenSection, freeHomOfSections]
      change ((SheafOfModules.freeHomEquiv K)
        (freeHomOfSections s) i).val (op ⊤) = s i
      simp only [freeHomOfSections, Equiv.apply_symm_apply]
      exact (sectionsTopEquiv K).apply_symm_apply (s i)
    exact hφ
  letI : Epi p := epi_of_appTop_surjective_of_isAffine p hpSurj
  letI : IsSplitEpi p :=
    isSplitEpi_of_epi_of_projective_sections_of_isAffine p hs.1 hs.2
  exact ⟨J, hJ, section_ p, p, IsSplitEpi.id p⟩

/-- For an arbitrary scheme morphism with affine target, the canonical projection
formula holds for every finite locally free quasicoherent coefficient sheaf. -/
theorem projectionFormulaHom_isIso_of_isFiniteLocallyFree_of_isAffine
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)
    {K : Y.Modules} [K.IsQuasicoherent] (hK : IsFiniteLocallyFree K)
    (F : X.Modules) : IsIso (projectionFormulaHom f K F) := by
  obtain ⟨J, hJ, i, p, h⟩ :=
    exists_retract_free_of_isFiniteLocallyFree_of_isAffine hK
  letI : Finite J := hJ
  letI : IsIso (projectionFormulaHom f
      (SheafOfModules.free (R := Y.ringCatSheaf) J) F) :=
    projectionFormulaHom_isIso_free f F
  exact projectionFormulaHom_isIso_of_retract f i p h F

/-- If a finite locally free coefficient starts on an affine scheme, then every one of
its pullbacks satisfies the canonical projection formula, without an affineness
assumption on the new base. -/
theorem projectionFormulaHom_isIso_pullback_of_isFiniteLocallyFree_of_isAffine
    {X Y Y' : Scheme.{u}} [IsAffine Y] (g : Y' ⟶ Y) (f : X ⟶ Y')
    {K : Y.Modules} [K.IsQuasicoherent] (hK : IsFiniteLocallyFree K)
    (F : X.Modules) :
    IsIso (projectionFormulaHom f ((pullback g).obj K) F) := by
  obtain ⟨J, hJ, i, p, h⟩ :=
    exists_retract_free_of_isFiniteLocallyFree_of_isAffine hK
  letI : Finite J := hJ
  let e := pullbackFreeIso g J
  let i' : (pullback g).obj K ⟶
      SheafOfModules.free (R := Y'.ringCatSheaf) J :=
    (pullback g).map i ≫ e.hom
  let p' : SheafOfModules.free (R := Y'.ringCatSheaf) J ⟶
      (pullback g).obj K :=
    e.inv ≫ (pullback g).map p
  have h' : i' ≫ p' = 𝟙 ((pullback g).obj K) := by
    dsimp only [i', p']
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp, h]
    exact (pullback g).map_id K
  letI : IsIso (projectionFormulaHom f
      (SheafOfModules.free (R := Y'.ringCatSheaf) J) F) :=
    projectionFormulaHom_isIso_free f F
  exact projectionFormulaHom_isIso_of_retract f i' p' h' F

end AlgebraicGeometry.Scheme.Modules

end

end
