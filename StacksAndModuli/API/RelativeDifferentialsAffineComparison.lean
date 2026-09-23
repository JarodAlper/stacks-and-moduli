module

public import StacksAndModuli.API.RelativeDifferentials
public import StacksAndModuli.API.RelativeDifferentialsAffine

/-!
# Comparing relative differentials on affine schemes

This file constructs the canonical comparison from the tilde sheaf associated
to `Ω[A/R]` to the sheafified relative differential module of the affine
scheme morphism `Spec A ⟶ Spec R`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {R A : CommRingCat.{u}}

/-- The global-sections derivation induced by the canonical derivation into
the relative differential sheaf of `Spec.map φ`. -/
noncomputable def affineGlobalRelativeDerivation (φ : R ⟶ A) :
    (moduleSpecΓFunctor.obj
      (Spec.map φ).relativeDifferentials).Derivation φ := by
  let f := Spec.map φ
  let d := f.relativeDifferentialsDerivation
  refine ModuleCat.Derivation.mk
    (fun a ↦ d.d ((ΓSpecIso A).inv a)) ?_ ?_ ?_
  · intro a b
    simp only [map_add]
  · intro a b
    have smul_eq (r : A)
        (x : Γ(f.relativeDifferentials, ⊤)) :
        r • x = (ΓSpecIso A).inv r • x := by
      rw [Scheme.Modules.smul_Spec_def]
      have htop : ((⊤ : (Spec A).Opens).leTop).op =
          𝟙 (Opposite.op (⊤ : (Spec A).Opens)) := Subsingleton.elim _ _
      rw [htop, (Spec A).presheaf.map_id]
      rfl
    rw [map_mul, d.d_mul, smul_eq, smul_eq]
  · intro r
    let adj := TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base
    let η := adj.unit.app (Spec R).presheaf
    let r' := (ΓSpecIso R).inv r
    have hmap : f.relativeStructureMap.app (Opposite.op ⊤)
        (η.app (Opposite.op ⊤) r') = f.appTop r' := by
      have h := NatTrans.congr_app f.pullbackUnit_comp_relativeStructureMap
        (Opposite.op (⊤ : (Spec R).Opens))
      exact ConcreteCategory.congr_hom h r'
    have hφ : (ΓSpecIso A).inv (φ r) = f.appTop r' :=
      ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) r
    rw [hφ, ← hmap]
    exact d.d_app _

/-- The canonical comparison from the affine Kähler model to the relative
differential sheaf constructed by sheafification. -/
noncomputable def affineToRelativeDifferentials (φ : R ⟶ A) :
    affineRelativeDifferentials φ ⟶
      (Spec.map φ).relativeDifferentials :=
  (AlgebraicGeometry.tilde.adjunction (R := A)).homEquiv _ _ |>.symm
    (affineGlobalRelativeDerivation φ).desc

/-- Under the tilde–global-sections adjunction, the affine comparison is the
map out of `Ω[A/R]` classified by the global relative derivation. -/
@[simp]
lemma tildeAdjunction_homEquiv_affineToRelativeDifferentials (φ : R ⟶ A) :
    (AlgebraicGeometry.tilde.adjunction (R := A)).homEquiv
        (CommRingCat.KaehlerDifferential φ)
        (Spec.map φ).relativeDifferentials
        (affineToRelativeDifferentials φ) =
      (affineGlobalRelativeDerivation φ).desc :=
  Equiv.apply_symm_apply _ _

/-- The affine comparison carries the universal ring differential to the
global relative differential. -/
@[simp]
lemma tildeAdjunction_affineToRelativeDifferentials_d (φ : R ⟶ A) (a : A) :
    ((AlgebraicGeometry.tilde.adjunction (R := A)).homEquiv
        (CommRingCat.KaehlerDifferential φ)
        (Spec.map φ).relativeDifferentials
        (affineToRelativeDifferentials φ))
          (CommRingCat.KaehlerDifferential.d a) =
      (affineGlobalRelativeDerivation φ).d a := by
  rw [tildeAdjunction_homEquiv_affineToRelativeDifferentials,
    ModuleCat.Derivation.desc_d]

/-- A concrete criterion for the affine comparison to be an isomorphism: it
is enough that its map on global sections be invertible and that the target
sheaf satisfy the expected localization property on principal opens. -/
lemma isIso_affineToRelativeDifferentials_of_isLocalizing (φ : R ⟶ A)
    (hTop : IsIso
      ((modulesSpecToSheaf.map (affineToRelativeDifferentials φ)).hom.app
        (Opposite.op (⊤ : (Spec A).Opens))))
    (hTarget : IsLocalizing
      (modulesSpecToSheaf.obj (Spec.map φ).relativeDifferentials)) :
    IsIso (affineToRelativeDifferentials φ) := by
  rw [← isIso_iff_of_reflects_iso _ modulesSpecToSheaf]
  exact isLocalizing_of_isIso_app_top hTop
    (by simpa only [affineRelativeDifferentials] using
      isLocalizing_tilde (CommRingCat.KaehlerDifferential φ))
    hTarget

/-- The same criterion phrased using the canonical map from the ring module
of differentials to the global sections of the sheafified construction. -/
lemma isIso_affineToRelativeDifferentials_of_globalSections_of_isLocalizing
    (φ : R ⟶ A)
    [IsIso (affineGlobalRelativeDerivation φ).desc]
    (hTarget : IsLocalizing
      (modulesSpecToSheaf.obj (Spec.map φ).relativeDifferentials)) :
    IsIso (affineToRelativeDifferentials φ) := by
  let adj := AlgebraicGeometry.tilde.adjunction (R := A)
  have hEq := adj.homEquiv_unit
    (X := CommRingCat.KaehlerDifferential φ)
    (Y := (Spec.map φ).relativeDifferentials)
    (f := affineToRelativeDifferentials φ)
  have hAdj : IsIso (adj.homEquiv
      (CommRingCat.KaehlerDifferential φ)
      (Spec.map φ).relativeDifferentials
      (affineToRelativeDifferentials φ)) := by
    exact (tildeAdjunction_homEquiv_affineToRelativeDifferentials φ).symm ▸
      (inferInstance : IsIso (affineGlobalRelativeDerivation φ).desc)
  let _ : IsIso
      (adj.unit.app (CommRingCat.KaehlerDifferential φ) ≫
        moduleSpecΓFunctor.map (affineToRelativeDifferentials φ)) :=
    hEq ▸ hAdj
  let _ : IsIso (moduleSpecΓFunctor.map
      (affineToRelativeDifferentials φ)) :=
    IsIso.of_isIso_comp_left
      (adj.unit.app (CommRingCat.KaehlerDifferential φ))
      (moduleSpecΓFunctor.map (affineToRelativeDifferentials φ))
  have hTop : IsIso
      ((modulesSpecToSheaf.map (affineToRelativeDifferentials φ)).hom.app
        (Opposite.op (⊤ : (Spec A).Opens))) := by
    change IsIso (moduleSpecΓFunctor.map
      (affineToRelativeDifferentials φ))
    infer_instance
  apply isIso_affineToRelativeDifferentials_of_isLocalizing φ
  · exact hTop
  · exact hTarget

/-- On a standard-smooth affine chart, the two affine comparison obligations
imply that the actual relative differential sheaf is finite locally free. -/
lemma relativeDifferentials_isFiniteLocallyFree_of_affineCompatibility
    (φ : R ⟶ A) (hφ : φ.hom.IsStandardSmooth)
    (hGlobal : IsIso (affineGlobalRelativeDerivation φ).desc)
    (hTarget : IsLocalizing
      (modulesSpecToSheaf.obj (Spec.map φ).relativeDifferentials)) :
    Modules.IsFiniteLocallyFree (Spec.map φ).relativeDifferentials := by
  let _ : IsIso (affineGlobalRelativeDerivation φ).desc := hGlobal
  let _ : IsIso (affineToRelativeDifferentials φ) :=
    isIso_affineToRelativeDifferentials_of_globalSections_of_isLocalizing
      φ hTarget
  exact Modules.IsFiniteLocallyFree.of_iso
    (asIso (affineToRelativeDifferentials φ))
    (affineRelativeDifferentials_isFiniteLocallyFree φ hφ)

/-- On a standard-smooth affine chart of relative dimension `n`, the two
affine comparison obligations imply that the actual relative differential
sheaf is finite locally free of rank `n`. -/
lemma relativeDifferentials_isProjectiveOfRank_of_affineCompatibility
    (n : ℕ) (φ : R ⟶ A) [Nontrivial A]
    (hφ : φ.hom.IsStandardSmoothOfRelativeDimension n)
    (hGlobal : IsIso (affineGlobalRelativeDerivation φ).desc)
    (hTarget : IsLocalizing
      (modulesSpecToSheaf.obj (Spec.map φ).relativeDifferentials)) :
    Modules.IsProjectiveOfRank n (Spec.map φ).relativeDifferentials := by
  let _ : IsIso (affineGlobalRelativeDerivation φ).desc := hGlobal
  let _ : IsIso (affineToRelativeDifferentials φ) :=
    isIso_affineToRelativeDifferentials_of_globalSections_of_isLocalizing
      φ hTarget
  exact Modules.IsProjectiveOfRank.of_iso
    (asIso (affineToRelativeDifferentials φ))
    (affineRelativeDifferentials_isProjectiveOfRank n φ hφ)

/-- Once the affine comparison has been proved invertible, this packages its
canonical isomorphism.  The instance is the precise geometric obligation: it
amounts to compatibility of sheafified differentials with affine
localization. -/
noncomputable def affineRelativeDifferentialsComparisonIso (φ : R ⟶ A)
    [IsIso (affineToRelativeDifferentials φ)] :
    affineRelativeDifferentials φ ≅
      (Spec.map φ).relativeDifferentials :=
  asIso (affineToRelativeDifferentials φ)

end AlgebraicGeometry.Scheme
