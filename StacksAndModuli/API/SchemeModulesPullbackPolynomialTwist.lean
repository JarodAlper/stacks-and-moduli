module

public import StacksAndModuli.API.SchemeModulesPullbackTensor
public import StacksAndModuli.API.ProjectiveTwistBaseChange
public import StacksAndModuli.API.ProjectiveTwistGlobalSections

/-!
# Pullback, tensor products, and nonnegative polynomial twists

This file proves that the canonical pullback--tensor comparison is an isomorphism when
the right factor is a nonnegative twisting sheaf pulled back from polynomial `Proj`.
The proof constructs the homogeneous coordinate section `X_i ^ d` of `O(d)`, identifies
it with the standard local basis on `D₊(X_i)`, and applies a general criterion for a
right tensor factor trivialized by sections on an open cover.

Main declarations:

* `Scheme.Modules.pullbackTensorComparison_isIso_of_section_cover`.
* `MvPolynomial.coordinateSectionHom_restrict_isIso`.
* `MvPolynomial.pullbackTensorComparison_pullback_polynomialTwist_nat_isIso`.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open ProjectiveSpectrum

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}}

/-- The natural isomorphism identifying restriction of a pullback to an inverse-image
open with pullback of the restricted module. -/
noncomputable def restrictPullbackNatIso (f : X ⟶ Y) (U : Y.Opens) :
    pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι ≅
      restrictFunctor U.ι ⋙ pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl) :=
  Functor.isoWhiskerLeft (pullback f)
      (restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι) ≪≫
    pullbackComp (f ⁻¹ᵁ U).ι f ≪≫
    pullbackCongr (by simp) ≪≫
    (pullbackComp (f.resLE U (f ⁻¹ᵁ U) le_rfl) U.ι).symm ≪≫
    Functor.isoWhiskerRight (restrictFunctorIsoPullback U.ι).symm
      (pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl))

/-- The component of `restrictPullbackNatIso` is the existing pointwise comparison
`restrictPullbackIsoPreimage`. -/
lemma restrictPullbackNatIso_app (f : X ⟶ Y) (U : Y.Opens) (M : Y.Modules) :
    (restrictPullbackNatIso f U).app M =
      restrictPullbackIsoPreimage f U M := by
  rfl

/-- The restriction--pullback comparison is natural in the module sheaf. -/
lemma restrictPullbackIsoPreimage_naturality
    (f : X ⟶ Y) (U : Y.Opens) {M N : Y.Modules} (φ : M ⟶ N) :
    (restrictFunctor (f ⁻¹ᵁ U).ι).map ((pullback f).map φ) ≫
        (restrictPullbackIsoPreimage f U N).hom =
      (restrictPullbackIsoPreimage f U M).hom ≫
        (pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl)).map
          ((restrictFunctor U.ι).map φ) := by
  rw [← restrictPullbackNatIso_app f U M,
    ← restrictPullbackNatIso_app f U N]
  change (pullback f ⋙ restrictFunctor (f ⁻¹ᵁ U).ι).map φ ≫
      (restrictPullbackNatIso f U).hom.app N =
    (restrictPullbackNatIso f U).hom.app M ≫
      (restrictFunctor U.ι ⋙
        pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl)).map φ
  exact (restrictPullbackNatIso f U).hom.naturality φ

/-- If a module morphism is an isomorphism on an open, then its pullback is an
isomorphism on the inverse-image open. -/
lemma restrict_pullback_map_isIso
    (f : X ⟶ Y) (U : Y.Opens) {M N : Y.Modules} (φ : M ⟶ N)
    [IsIso ((restrictFunctor U.ι).map φ)] :
    IsIso ((restrictFunctor (f ⁻¹ᵁ U).ι).map ((pullback f).map φ)) := by
  let a := (restrictFunctor (f ⁻¹ᵁ U).ι).map ((pullback f).map φ)
  let eM := restrictPullbackIsoPreimage f U M
  let eN := restrictPullbackIsoPreimage f U N
  let b := (pullback (f.resLE U (f ⁻¹ᵁ U) le_rfl)).map
    ((restrictFunctor U.ι).map φ)
  let _ : IsIso b := by
    dsimp only [b]
    infer_instance
  have h : a ≫ eN.hom = eM.hom ≫ b := by
    exact restrictPullbackIsoPreimage_naturality f U φ
  let _ : IsIso (a ≫ eN.hom) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_right a eN.hom

/-- Tensoring a morphism on the left preserves being an isomorphism after restriction
to an open. -/
lemma restrict_tensorMapRight_isIso
    (j : X ⟶ Y) [IsOpenImmersion j] (F : Y.Modules)
    {G G' : Y.Modules} (ψ : G ⟶ G')
    [IsIso ((restrictFunctor j).map ψ)] :
    IsIso ((restrictFunctor j).map (tensorMapRight F ψ)) := by
  let a := (restrictFunctor j).map (tensorMapRight F ψ)
  let e := restrictTensorIso j F G
  let e' := restrictTensorIso j F G'
  let b := tensorMapRight ((restrictFunctor j).obj F)
    ((restrictFunctor j).map ψ)
  let _ : IsIso b := by
    let ee := asIso ((restrictFunctor j).map ψ)
    change IsIso (tensorRightIso ((restrictFunctor j).obj F) ee).hom
    infer_instance
  have h0 := restrictTensorIso_naturality j (𝟙 F) ψ
  have hid : (restrictFunctor j).map (𝟙 F) =
      𝟙 ((restrictFunctor j).obj F) := (restrictFunctor j).map_id F
  have ht : tensorMapLeft (𝟙 ((restrictFunctor j).obj F))
      ((restrictFunctor j).obj G) = 𝟙 _ :=
    tensorMapLeft_id _ _
  have hs : tensorMapLeft (𝟙 F) G ≫ tensorMapRight F ψ =
      tensorMapRight F ψ := by
    rw [tensorMapLeft_id, Category.id_comp]
  have h : a ≫ e'.hom = e.hom ≫ b := by
    rw [hid, ht, Category.id_comp, hs] at h0
    exact h0
  let _ : IsIso (a ≫ e'.hom) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_right a e'.hom

/-- The canonical pullback--tensor comparison is an isomorphism when the right factor
admits local bases supplied by maps from the structure sheaf on an open cover. -/
theorem pullbackTensorComparison_isIso_of_section_cover
    {I : Type*} (f : X ⟶ Y) (F G : Y.Modules)
    (U : I → Y.Opens) (hU : ⨆ i, U i = ⊤)
    (s : I → (SheafOfModules.unit Y.ringCatSheaf ⟶ G))
    (hs : ∀ i, IsIso ((restrictFunctor (U i).ι).map (s i))) :
    IsIso (pullbackTensorComparison f F G) := by
  refine isIso_of_restrict_iSup_eq_top (pullbackTensorComparison f F G)
    (fun i ↦ f ⁻¹ᵁ U i) ?_ ?_
  · rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]
  · intro i
    let V : X.Opens := f ⁻¹ᵁ U i
    let t := (pullback f).map (tensorMapRight F (s i))
    let a := (restrictFunctor V.ι).map (pullbackTensorComparison f F G)
    let a0 := (restrictFunctor V.ι).map
      (pullbackTensorComparison f F (SheafOfModules.unit Y.ringCatSheaf))
    let b := (restrictFunctor V.ι).map
      (tensorMapRight ((pullback f).obj F) ((pullback f).map (s i)))
    let t' := (restrictFunctor V.ι).map t
    let _ : IsIso ((restrictFunctor (U i).ι).map (s i)) := hs i
    have htY : IsIso ((restrictFunctor (U i).ι).map
        (tensorMapRight F (s i))) :=
      restrict_tensorMapRight_isIso (U i).ι F (s i)
    let _ : IsIso ((restrictFunctor (U i).ι).map
        (tensorMapRight F (s i))) := htY
    have htX : IsIso t' := by
      dsimp only [t', t, V]
      exact restrict_pullback_map_isIso f (U i) (tensorMapRight F (s i))
    let _ : IsIso t' := htX
    have hsX : IsIso ((restrictFunctor V.ι).map ((pullback f).map (s i))) := by
      dsimp only [V]
      exact restrict_pullback_map_isIso f (U i) (s i)
    let _ : IsIso ((restrictFunctor V.ι).map ((pullback f).map (s i))) := hsX
    have hb : IsIso b := by
      dsimp only [b]
      exact restrict_tensorMapRight_isIso V.ι ((pullback f).obj F)
        ((pullback f).map (s i))
    let _ : IsIso b := hb
    let _ : IsIso (pullbackTensorComparison f F
        (SheafOfModules.unit Y.ringCatSheaf)) :=
      pullbackTensorComparison_isIso_unit f F
    let _ : IsIso a0 := by
      dsimp only [a0]
      infer_instance
    have hnat := pullbackTensorComparison_naturality_right f F (s i)
    have h : t' ≫ a = a0 ≫ b := by
      exact congrArg (restrictFunctor V.ι).map hnat
    let _ : IsIso (t' ≫ a) := h ▸ inferInstance
    exact IsIso.of_isIso_comp_left t' a

end AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency true

namespace ProjectiveSpectrum.Twist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (R : ℕ → σ) [GradedRing R]

/-- A homogeneous element defines the corresponding morphism from the structure sheaf
to its nonnegative twisting sheaf. -/
noncomputable def homogeneousSectionHom {d : ℕ} (p : R d) :
    SheafOfModules.unit (Proj R).ringCatSheaf ⟶ twist R (d : ℤ) :=
  (SheafOfModules.unitHomEquiv (twist R (d : ℤ))).symm
    (AlgebraicGeometry.Scheme.Modules.sectionsFromTop
      (twist R (d : ℤ)) (homogeneousSection R p ⊤))

/-- Applying `homogeneousSectionHom` to `1` on an open gives the pointwise homogeneous
section defined by the same form. -/
lemma homogeneousSectionHom_app_one {d : ℕ} (p : R d)
    (U : (Proj R).Opens) :
    (homogeneousSectionHom R p).val.app (.op U) (1 : Γ(Proj R, U)) =
      homogeneousSection R p U := by
  let s := AlgebraicGeometry.Scheme.Modules.sectionsFromTop
    (twist R (d : ℤ)) (homogeneousSection R p ⊤)
  have h := congrArg (fun t : (twist R (d : ℤ)).sections ↦ t.1 (.op U))
    (Equiv.apply_symm_apply (SheafOfModules.unitHomEquiv (twist R (d : ℤ))) s)
  change (homogeneousSectionHom R p).val.app (.op U)
    (1 : Γ(Proj R, U)) = _ at h
  change _ = (Scheme.Modules.presheaf (twist R (d : ℤ))).map
    (homOfLE le_top).op (homogeneousSection R p ⊤) at h
  exact h.trans (homogeneousSection_restrict R p le_top)

end ProjectiveSpectrum.Twist

namespace MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) (R : Type u) [CommRing R]

/-- The coordinate power `X_i ^ d`, bundled as a homogeneous polynomial of degree `d`. -/
noncomputable def coordinatePowerHomogeneous (i : Fin (n + 1)) (d : ℕ) :
    homogeneousSubmodule (Fin (n + 1)) R d :=
  ⟨X i ^ d, MvPolynomial.isHomogeneous_X_pow i d⟩

/-- The morphism `O → O(d)` on polynomial `Proj` defined by `X_i ^ d`. -/
noncomputable def coordinateSectionHom (i : Fin (n + 1)) (d : ℕ) :
    SheafOfModules.unit
        (Proj (homogeneousSubmodule (Fin (n + 1)) R)).ringCatSheaf ⟶
      ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ) :=
  ProjectiveSpectrum.Twist.homogeneousSectionHom
    (homogeneousSubmodule (Fin (n + 1)) R)
    (coordinatePowerHomogeneous n R i d)

/-- The standard open `D₊(X_i)`, with its type normalized as an open of the scheme
`Proj R[X_0, ..., X_n]`. -/
noncomputable def projectiveStandardSchemeOpen (i : Fin (n + 1)) :
    (Proj (homogeneousSubmodule (Fin (n + 1)) R)).Opens :=
  projectiveStandardOpen n R i

/-- On `D₊(X_i)`, the homogeneous section defined by `X_i ^ d` is the standard local
basis of `O(d)`. -/
theorem homogeneousSection_coordinatePower_eq_unitSection
    (i : Fin (n + 1)) (d : ℕ)
    (V : (Proj (homogeneousSubmodule (Fin (n + 1)) R)).Opens)
    (hV : V ≤ projectiveStandardSchemeOpen n R i) :
    ProjectiveSpectrum.Twist.homogeneousSection
        (homogeneousSubmodule (Fin (n + 1)) R)
        (coordinatePowerHomogeneous n R i d) V =
      ProjectiveSpectrum.Twist.unitSection
        (homogeneousSubmodule (Fin (n + 1)) R)
        (X_mem_homogeneousSubmodule_one n R i) (d : ℤ) (.op V) hV := by
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change Localization.mk (X i ^ d) 1 =
    (HomogeneousLocalization.unitPow
      (X_mem_homogeneousSubmodule_one n R i) (hV x.2) (d : ℤ)).embed
  simp only [HomogeneousLocalization.NumDenShift.embed_def,
    HomogeneousLocalization.unitPow, Int.toNat_natCast]
  simp only [show (-(d : ℤ)).toNat = 0 by omega, pow_zero]
  rw [Localization.mk_eq_mk_iff]
  exact Localization.r_of_eq (by simp)

/-- The section `1` of the structure sheaf, regarded as a section of its restriction to
the standard coordinate open. -/
noncomputable def coordinateRestrictedSourceOne
    (i : Fin (n + 1)) :
    Γ((Scheme.Modules.restrictFunctor (projectiveStandardSchemeOpen n R i).ι).obj
      (SheafOfModules.unit
        (Proj (homogeneousSubmodule (Fin (n + 1)) R)).ringCatSheaf), ⊤) :=
  (1 : Γ(Proj (homogeneousSubmodule (Fin (n + 1)) R),
    (projectiveStandardSchemeOpen n R i).ι ''ᵁ ⊤))

/-- The section `X_i ^ d` of `O(d)`, regarded as a section of the restricted sheaf on
the standard coordinate open. -/
noncomputable def coordinateRestrictedSection
    (i : Fin (n + 1)) (d : ℕ) :
    Γ((Scheme.Modules.restrictFunctor (projectiveStandardSchemeOpen n R i).ι).obj
      (ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ)), ⊤) :=
  ProjectiveSpectrum.Twist.homogeneousSection
    (homogeneousSubmodule (Fin (n + 1)) R)
    (coordinatePowerHomogeneous n R i d)
    ((projectiveStandardSchemeOpen n R i).ι ''ᵁ ⊤)

/-- The standard local trivialization of `O(d)` sends the restricted coordinate section
`X_i ^ d` to `1`. -/
theorem coordinateRestrictedSection_trivializes
    (i : Fin (n + 1)) (d : ℕ) :
    (ProjectiveSpectrum.Twist.restrictTwistIsoUnit
      (X_mem_homogeneousSubmodule_one n R i) (d : ℤ)).hom.app ⊤
        (coordinateRestrictedSection n R i d) =
      (1 : Γ((projectiveStandardSchemeOpen n R i).toScheme, ⊤)) := by
  let G := homogeneousSubmodule (Fin (n + 1)) R
  let U : (Proj G).Opens := projectiveStandardSchemeOpen n R i
  let hf : X i ∈ G 1 := X_mem_homogeneousSubmodule_one n R i
  change (U.ι.appIso ⊤).hom
      ((ProjectiveSpectrum.Twist.unitSectionEquiv G hf (d : ℤ)
        (.op (U.ι ''ᵁ ⊤)) (U.ι_image_le ⊤)).symm
        (ProjectiveSpectrum.Twist.homogeneousSection G
          (coordinatePowerHomogeneous n R i d) (U.ι ''ᵁ ⊤))) = 1
  rw [homogeneousSection_coordinatePower_eq_unitSection n R i d
    (U.ι ''ᵁ ⊤) (U.ι_image_le ⊤)]
  have hbasis :
      (ProjectiveSpectrum.Twist.unitSectionEquiv G hf (d : ℤ)
        (.op (U.ι ''ᵁ ⊤)) (U.ι_image_le ⊤)).symm
          (ProjectiveSpectrum.Twist.unitSection G hf (d : ℤ)
            (.op (U.ι ''ᵁ ⊤)) (U.ι_image_le ⊤)) = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    exact (ProjectiveSpectrum.Twist.unitSectionEquiv_one G hf
      (d : ℤ) _ _).symm
  rw [hbasis]
  exact map_one _

/-- The coordinate morphism `O → O(d)` is an isomorphism after restriction to
`D₊(X_i)`. -/
theorem coordinateSectionHom_restrict_isIso (i : Fin (n + 1)) (d : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor
      (show (Proj (homogeneousSubmodule (Fin (n + 1)) R)).Opens from
        projectiveStandardOpen n R i).ι).map
        (coordinateSectionHom n R i d)) := by
  let G := homogeneousSubmodule (Fin (n + 1)) R
  let U : (Proj G).Opens := projectiveStandardSchemeOpen n R i
  let j := U.ι
  let hf : X i ∈ G 1 := X_mem_homogeneousSubmodule_one n R i
  let e0 := Scheme.Modules.restrictUnitIso j
  let ed : (Scheme.Modules.restrictFunctor j).obj
        (ProjectiveSpectrum.Twist.twist G (d : ℤ)) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
    ProjectiveSpectrum.Twist.restrictTwistIsoUnit hf (d : ℤ)
  let s := coordinateSectionHom n R i d
  let a := e0.inv ≫ (Scheme.Modules.restrictFunctor j).map s ≫ ed.hom
  let _ : IsIso e0.inv := e0.isIso_inv
  let _ : IsIso ed.hom := ed.isIso_hom
  have ha : IsIso a := by
    apply Scheme.Modules.unit_endomorphism_isIso_of_exists_preimage_one
      a (1 : Γ(U.toScheme, ⊤))
    have he0 : Scheme.Modules.Hom.app e0.inv ⊤
        (1 : Γ(U.toScheme, ⊤)) =
        coordinateRestrictedSourceOne n R i := by
      change (j.appIso ⊤).inv 1 = 1
      exact map_one _
    have hs : Scheme.Modules.Hom.app
        ((Scheme.Modules.restrictFunctor j).map s) ⊤
          (coordinateRestrictedSourceOne n R i) =
        coordinateRestrictedSection n R i d := by
      change (coordinateSectionHom n R i d).val.app (.op (j ''ᵁ ⊤))
        (1 : Γ(Proj G, j ''ᵁ ⊤)) =
          ProjectiveSpectrum.Twist.homogeneousSection G
            (coordinatePowerHomogeneous n R i d) (j ''ᵁ ⊤)
      exact ProjectiveSpectrum.Twist.homogeneousSectionHom_app_one
        G (coordinatePowerHomogeneous n R i d) (j ''ᵁ ⊤)
    have hed : Scheme.Modules.Hom.app ed.hom ⊤
        (coordinateRestrictedSection n R i d) =
        (1 : Γ(U.toScheme, ⊤)) := by
      exact coordinateRestrictedSection_trivializes n R i d
    change ed.hom.app ⊤
      (((Scheme.Modules.restrictFunctor j).map s).app ⊤
        (e0.inv.app ⊤ (1 : Γ(U.toScheme, ⊤)))) =
          (1 : Γ(U.toScheme, ⊤))
    rw [he0, hs, hed]
  let _ : IsIso a := ha
  have hleft : IsIso (e0.inv ≫ (Scheme.Modules.restrictFunctor j).map s) :=
    IsIso.of_isIso_fac_right (f := ed.hom)
      (g := e0.inv ≫ (Scheme.Modules.restrictFunctor j).map s)
      (h := a) rfl
  let _ : IsIso (e0.inv ≫ (Scheme.Modules.restrictFunctor j).map s) := hleft
  exact IsIso.of_isIso_fac_left
    (f := e0.inv) (g := (Scheme.Modules.restrictFunctor j).map s)
    (h := e0.inv ≫ (Scheme.Modules.restrictFunctor j).map s) rfl

/-- Pullback along any morphism to polynomial `Proj` commutes with tensoring by `O(d)`
for a natural degree `d`. -/
theorem pullbackTensorComparison_polynomialTwist_nat_isIso
    {X : Scheme.{u}}
    (f : X ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) R))
    (F : (Proj (homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    (d : ℕ) :
    IsIso (Scheme.Modules.pullbackTensorComparison f F
      (ProjectiveSpectrum.Twist.twist
        (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ))) := by
  let G := homogeneousSubmodule (Fin (n + 1)) R
  let U (i : Fin (n + 1)) : (Proj G).Opens :=
    projectiveStandardSchemeOpen n R i
  refine Scheme.Modules.pullbackTensorComparison_isIso_of_section_cover
    f F (ProjectiveSpectrum.Twist.twist G (d : ℤ)) U ?_
      (fun i ↦ coordinateSectionHom n R i d) ?_
  · dsimp only [U]
    have hU : (⨆ i : Fin (n + 1), projectiveStandardSchemeOpen n R i) = ⊤ :=
      iSup_projectiveStandardOpen_eq_top n R
    exact hU
  · intro i
    exact coordinateSectionHom_restrict_isIso n R i d

/-- Pullback commutes with tensoring by a natural-degree polynomial twist after that
twist has already been pulled back along another scheme morphism. -/
theorem pullbackTensorComparison_pullback_polynomialTwist_nat_isIso
    {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    (h : Y ⟶ Proj (homogeneousSubmodule (Fin (n + 1)) R))
    (F : Y.Modules) (d : ℕ) :
    IsIso (Scheme.Modules.pullbackTensorComparison f F
      ((Scheme.Modules.pullback h).obj
        (ProjectiveSpectrum.Twist.twist
          (homogeneousSubmodule (Fin (n + 1)) R) (d : ℤ)))) := by
  let G := homogeneousSubmodule (Fin (n + 1)) R
  let U0 (i : Fin (n + 1)) : (Proj G).Opens :=
    projectiveStandardSchemeOpen n R i
  let U (i : Fin (n + 1)) : Y.Opens := h ⁻¹ᵁ U0 i
  let s0 (i : Fin (n + 1)) := coordinateSectionHom n R i d
  let e0 := asIso (SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)
  let s (i : Fin (n + 1)) := e0.inv ≫
    (Scheme.Modules.pullback h).map (s0 i)
  refine Scheme.Modules.pullbackTensorComparison_isIso_of_section_cover f F
    ((Scheme.Modules.pullback h).obj (ProjectiveSpectrum.Twist.twist G (d : ℤ))) U ?_ s ?_
  · dsimp only [U, U0]
    rw [← Scheme.Hom.preimage_iSup]
    have hU : (⨆ i : Fin (n + 1), projectiveStandardSchemeOpen n R i) = ⊤ :=
      iSup_projectiveStandardOpen_eq_top n R
    rw [hU, Scheme.Hom.preimage_top]
  · intro i
    let _ : IsIso ((Scheme.Modules.restrictFunctor
        (projectiveStandardSchemeOpen n R i).ι).map
          (coordinateSectionHom n R i d)) :=
      coordinateSectionHom_restrict_isIso n R i d
    have hp : IsIso ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ
        projectiveStandardSchemeOpen n R i).ι).map
          ((Scheme.Modules.pullback h).map (coordinateSectionHom n R i d))) :=
      Scheme.Modules.restrict_pullback_map_isIso h
        (projectiveStandardSchemeOpen n R i) (coordinateSectionHom n R i d)
    let _ : IsIso ((Scheme.Modules.restrictFunctor (h ⁻¹ᵁ
        projectiveStandardSchemeOpen n R i).ι).map
          ((Scheme.Modules.pullback h).map (coordinateSectionHom n R i d))) := hp
    dsimp only [U, s, s0, U0]
    let q := Scheme.Modules.restrictFunctor
      (h ⁻¹ᵁ projectiveStandardSchemeOpen n R i).ι
    have he := q.map_comp e0.inv
      ((Scheme.Modules.pullback h).map (coordinateSectionHom n R i d))
    let _ : IsIso e0.inv := e0.isIso_inv
    have he0q : IsIso (q.map e0.inv) := by
      change IsIso (q.mapIso e0.symm).hom
      infer_instance
    have hpq : IsIso (q.map ((Scheme.Modules.pullback h).map
        (coordinateSectionHom n R i d))) := by
      exact hp
    let hr : IsIso (q.map e0.inv ≫ q.map
        ((Scheme.Modules.pullback h).map (coordinateSectionHom n R i d))) := by
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ he0q hpq
    exact he.symm ▸ hr

end MvPolynomial

end
