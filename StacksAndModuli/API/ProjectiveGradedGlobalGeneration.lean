module

public import StacksAndModuli.API.ProjGammaStarChart
public import StacksAndModuli.API.TwistMonomialSections
public import StacksAndModuli.API.ProjTwistRestrictIso
public import StacksAndModuli.API.ProjectiveGradedCechAugmentationMultiplication
public import StacksAndModuli.API.PullbackPushforwardEvaluationEpi
public import StacksAndModuli.API.ProjGammaStarProjectiveSpace
public import StacksAndModuli.API.AffineQuasicoherentEpi

/-!
# From graded multiplication to relative global generation

Supporting API for the projectivity construction in Proposition 2.4.1.  A multiplication
span statement in graded Čech `H⁰` is converted into generation on each standard projective
chart.  The local generation statements are then glued to prove that the free sheaf on all
degree-`d` global sections, and hence the pullback--pushforward counit for the degree-`d`
twist, is epimorphic.

The chart calculation is the homogeneous identity `g = (g / xᵢᴺ) xᵢᴺ` on `D₊(xᵢ)`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace ProjectiveSpectrum.Twist

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A]
variable [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Multiplication by an arbitrary homogeneous `g` of degree `N` is, on
`D₊(f)`, multiplication by `f^N` followed by the regular function `g/f^N`. -/
theorem restrict_mulHom_eq_ratio_aux {f g : A} (_hf : f ∈ 𝒜 1)
    (_hg : g ∈ 𝒜 N) (e ec : ℤ) (hec : ec = e + (N : ℤ))
    (hfN : f ^ N ∈ 𝒜 N)
    (r : Γ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme, ⊤))
    (hr : ∀ (W : ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme.Opens)ᵒᵖ)
        (x : ↥((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι ''ᵁ W.unop))
        (z : Localization (x.1).asHomogeneousIdeal.toIdeal.primeCompl),
      (((((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι.appIso W.unop).inv
            (Scheme.Modules.resTop r W)).1 x).val) * (z * Localization.mk (f ^ N) 1)
        = z * Localization.mk g 1) :
    (Scheme.Modules.restrictFunctor
        (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
        (mulHom 𝒜 (⟨g, _hg⟩ : 𝒜 N) e ec hec)
      = (Scheme.Modules.restrictFunctor
          (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
          (mulHom 𝒜 (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)
        ≫ Scheme.Modules.smulHom r _ := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ ?_)
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  exact (hr W x (s.1 x).1).symm

/-- The preceding homogeneous bridge after tensoring with an arbitrary sheaf. -/
theorem restrict_twistModuleMulHom_eq_ratio_aux
    (F : (AlgebraicGeometry.Proj 𝒜).Modules) {f g : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 N)
    (e ec : ℤ) (hec : ec = e + (N : ℤ)) (hfN : f ^ N ∈ 𝒜 N)
    (r : Γ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme, ⊤))
    (hr : ∀ (W : ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme.Opens)ᵒᵖ)
        (x : ↥((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι ''ᵁ W.unop))
        (z : Localization (x.1).asHomogeneousIdeal.toIdeal.primeCompl),
      (((((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι.appIso W.unop).inv
            (Scheme.Modules.resTop r W)).1 x).val) * (z * Localization.mk (f ^ N) 1)
        = z * Localization.mk g 1) :
    (Scheme.Modules.restrictFunctor
        (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
        (twistModuleMulHom 𝒜 F (⟨g, hg⟩ : 𝒜 N) e ec hec)
      = (Scheme.Modules.restrictFunctor
          (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
          (twistModuleMulHom 𝒜 F (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)
        ≫ Scheme.Modules.smulHom r _ := by
  rw [← cancel_mono (Scheme.Modules.restrictTensorIso
    (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι F (twist 𝒜 ec)).hom]
  rw [twistModuleMulHom, twistModuleMulHom, restrict_tensorMapRight_naturality,
    restrict_mulHom_eq_ratio_aux 𝒜 hf hg e ec hec hfN r hr,
    Scheme.Modules.tensorMapRight_comp, Scheme.Modules.tensorMapRight_smulHom,
    ← Category.assoc, ← restrict_tensorMapRight_naturality, Category.assoc,
    Scheme.Modules.smulHom_naturality, ← Category.assoc]
  rfl

/-- The regular function `g/f^N` on `D₊(f)`, transported to the top open of
the open subscheme. -/
noncomputable def homogeneousRatioTop {f g : A} (hf : f ∈ 𝒜 1)
    (hg : g ∈ 𝒜 N) :
    Γ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme, ⊤) :=
  (AlgebraicGeometry.Proj.basicOpen 𝒜 f).topIso.inv
    (AlgebraicGeometry.Proj.ratioSection 𝒜 hf hg)

theorem homogeneousRatioTop_spec {f g : A} (hf : f ∈ 𝒜 1)
    (hg : g ∈ 𝒜 N)
    (W : ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme.Opens)ᵒᵖ)
    (x : ↥((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι ''ᵁ W.unop))
    (z : Localization (x.1).asHomogeneousIdeal.toIdeal.primeCompl) :
    (((((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι.appIso W.unop).inv
        (Scheme.Modules.resTop (homogeneousRatioTop 𝒜 hf hg) W)).1 x).val)
      * (z * Localization.mk (f ^ N) 1) = z * Localization.mk g 1 := by
  have hx : f ∈ (x.1).asHomogeneousIdeal.toIdeal.primeCompl :=
    Scheme.Opens.ι_image_le _ _ x.2
  have hval : (((((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι.appIso W.unop).inv
      (Scheme.Modules.resTop (homogeneousRatioTop 𝒜 hf hg) W)).1 x).val)
      = ((AlgebraicGeometry.Proj.ratioSection 𝒜 hf hg).1 ⟨x.1, hx⟩).val := by
    simp only [homogeneousRatioTop, Scheme.Opens.ι_appIso, Iso.refl_inv,
      Scheme.Modules.resTop, Scheme.Opens.topIso_inv]
    rfl
  rw [hval, AlgebraicGeometry.Proj.ratioSection_apply_val]
  simp only [pow_one]
  have hcancel :
      Localization.mk g ⟨f ^ N, (x.1).asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hx N⟩
        * Localization.mk (f ^ N) 1
        = Localization.mk g 1 := by
    rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    push_cast
    ring
  calc
    _ = z * (Localization.mk g ⟨f ^ N,
          (x.1).asHomogeneousIdeal.toIdeal.primeCompl.pow_mem hx N⟩
        * Localization.mk (f ^ N) 1) := by ac_rfl
    _ = z * Localization.mk g 1 := by rw [hcancel]

/-- Concrete homogeneous bridge on `D₊(f)`. -/
theorem restrict_twistModuleMulHom_eq_homogeneousRatio
    (F : (AlgebraicGeometry.Proj 𝒜).Modules) {f g : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 N)
    (e ec : ℤ) (hec : ec = e + (N : ℤ)) (hfN : f ^ N ∈ 𝒜 N) :
    (Scheme.Modules.restrictFunctor
        (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
        (twistModuleMulHom 𝒜 F (⟨g, hg⟩ : 𝒜 N) e ec hec)
      = (Scheme.Modules.restrictFunctor
          (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).map
          (twistModuleMulHom 𝒜 F (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)
        ≫ Scheme.Modules.smulHom (homogeneousRatioTop 𝒜 hf hg) _ :=
  restrict_twistModuleMulHom_eq_ratio_aux 𝒜 F hf hg e ec hec hfN _
    (homogeneousRatioTop_spec 𝒜 hf hg)

/-- Restriction of the transported homogeneous ratio to an arbitrary chart open. -/
theorem resTop_homogeneousRatioTop {f g : A} (hf : f ∈ 𝒜 1)
    (hg : g ∈ 𝒜 N)
    (W : ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme.Opens)ᵒᵖ) :
    Scheme.Modules.resTop (homogeneousRatioTop 𝒜 hf hg) W
      = ((AlgebraicGeometry.Proj 𝒜).presheaf.map
          (homOfLE (Scheme.Opens.ι_image_le
            (AlgebraicGeometry.Proj.basicOpen 𝒜 f) W.unop)).op).hom
        (AlgebraicGeometry.Proj.ratioSection 𝒜 hf hg) := by
  simp only [Scheme.Modules.resTop, homogeneousRatioTop,
    Scheme.Opens.topIso_inv]
  rfl

/-- The preceding restriction after the `appIso` transport inserted by restriction. -/
theorem appIso_inv_resTop_homogeneousRatioTop {f g : A} (hf : f ∈ 𝒜 1)
    (hg : g ∈ 𝒜 N)
    (W : ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme.Opens)ᵒᵖ) :
    ((((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι.appIso W.unop).inv)
        (Scheme.Modules.resTop (homogeneousRatioTop 𝒜 hf hg) W))
      = ((AlgebraicGeometry.Proj 𝒜).presheaf.map
          (homOfLE (Scheme.Opens.ι_image_le
            (AlgebraicGeometry.Proj.basicOpen 𝒜 f) W.unop)).op).hom
        (AlgebraicGeometry.Proj.ratioSection 𝒜 hf hg) := by
  rw [Scheme.Opens.ι_appIso]
  exact resTop_homogeneousRatioTop 𝒜 hf hg W

/-- Section-level form of the homogeneous-ratio bridge. -/
theorem app_twistModuleMulHom_eq_homogeneousRatio_smul
    (F : (AlgebraicGeometry.Proj 𝒜).Modules) {f g : A}
    (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 N)
    (e ec : ℤ) (hec : ec = e + (N : ℤ)) (hfN : f ^ N ∈ 𝒜 N)
    (W : ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme.Opens)ᵒᵖ)
    (s : Γ(twistModule 𝒜 F e,
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι ''ᵁ W.unop)) :
    Scheme.Modules.Hom.app
        (twistModuleMulHom 𝒜 F (⟨g, hg⟩ : 𝒜 N) e ec hec)
        ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι ''ᵁ W.unop) s
      = (((AlgebraicGeometry.Proj 𝒜).presheaf.map
          (homOfLE (Scheme.Opens.ι_image_le
            (AlgebraicGeometry.Proj.basicOpen 𝒜 f) W.unop)).op).hom
          (AlgebraicGeometry.Proj.ratioSection 𝒜 hf hg)) •
        Scheme.Modules.Hom.app
          (twistModuleMulHom 𝒜 F (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)
          ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι ''ᵁ W.unop) s := by
  have hb := restrict_twistModuleMulHom_eq_homogeneousRatio
    𝒜 F hf hg e ec hec hfN
  have happ := congrArg
    (fun ψ : (Scheme.Modules.restrictFunctor
        (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).obj (twistModule 𝒜 F e) ⟶
      (Scheme.Modules.restrictFunctor
        (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι).obj (twistModule 𝒜 F ec) ↦
      (PresheafOfModules.Hom.app ψ.val W).hom s) hb
  refine happ.trans ?_
  show ((((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι.appIso W.unop).inv)
      (Scheme.Modules.resTop (homogeneousRatioTop 𝒜 hf hg) W)) •
      Scheme.Modules.Hom.app
        (twistModuleMulHom 𝒜 F (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec)
        ((AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι ''ᵁ W.unop) s = _
  rw [appIso_inv_resTop_homogeneousRatioTop]

end ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.Proj

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A]
variable [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

set_option maxHeartbeats 1000000 in
-- Expanding the chart isomorphism and the homogeneous ratio carries a large sheaf term.
/-- The homogeneous-ratio bridge on an arbitrary open contained in the chart. -/
theorem app_twistModuleMulHom_eq_homogeneousRatio_smul_of_le
    {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 N)
    (F : (Proj 𝒜).Modules) (e ec : ℤ) (hec : ec = e + (N : ℤ))
    (hfN : f ^ N ∈ 𝒜 N) (V : (Proj 𝒜).Opens) (hV : V ≤ basicOpen 𝒜 f)
    (s : Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F e, V)) :
    Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
          (⟨g, hg⟩ : 𝒜 N) e ec hec) V s
      = (((Proj 𝒜).presheaf.map (homOfLE hV).op).hom
          (ratioSection 𝒜 hf hg)) •
        Scheme.Modules.Hom.app
          (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
            (⟨f ^ N, hfN⟩ : 𝒜 N) e ec hec) V s := by
  obtain ⟨W, hW⟩ : ∃ W : (basicOpen 𝒜 f).toScheme.Opens,
      V = (basicOpen 𝒜 f).ι ''ᵁ W :=
    ⟨_, eq_image_preimage_of_le hV⟩
  subst hW
  exact ProjectiveSpectrum.Twist.app_twistModuleMulHom_eq_homogeneousRatio_smul
    𝒜 F hf hg e ec hec hfN (op W) s

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Proj

variable {A σ : Type u} [CommRing A] [SetLike σ A]
variable [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

set_option maxHeartbeats 1000000 in
-- The calculation unfolds both the localization stage and tensor multiplication maps.
/-- Dividing a monomial multiple of a degree-`d` global section by the chart
variable gives a local scalar multiple of the original restricted section. -/
theorem chartStageMap_mulList_eq_ratio_smul_res
    {n : ℕ} {R : CommRingCat.{u}} (π : Proj 𝒜 ⟶ Spec R)
    (F : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1)
    (i : Fin (n + 1)) (d : ℤ) (l : List (Fin (n + 1)))
    (s : (gammaStar 𝒜 π F x).obj d) :
    chartStageMap 𝒜 π F x i d l.length
        (((gammaStar 𝒜 π F x).mulList l d
          (ProjectiveSpace.GradedModule.locDeg [i] d l.length)
          (locDeg_singleton i d l.length).symm).hom s)
      = (((Proj 𝒜).presheaf.map
          (homOfLE (le_refl (basicOpen 𝒜 (x i : A)))).op).hom
          (ratioSection 𝒜 (x i).2 (varProd_mem 𝒜 x l))) •
        (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 (x i : A) ≤ ⊤)).op s := by
  let U := basicOpen 𝒜 (x i : A)
  let E := chartTwistLinearEquiv 𝒜 π F x i d l.length
    (ProjectiveSpace.GradedModule.locDeg [i] d l.length)
    (locDeg_singleton i d l.length)
  refine E.injective ?_
  rw [chartStageMap_apply, LinearEquiv.apply_symm_apply]
  change (ProjectiveSpectrum.Twist.twistModule 𝒜 F
      (ProjectiveSpace.GradedModule.locDeg [i] d l.length)).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op
        (((gammaStar 𝒜 π F x).mulList l d
          (ProjectiveSpace.GradedModule.locDeg [i] d l.length)
          (locDeg_singleton i d l.length).symm).hom s) = _
  rw [gammaStar_mulList_apply 𝒜 π F x l d
      (ProjectiveSpace.GradedModule.locDeg [i] d l.length)
      (locDeg_singleton i d l.length).symm (varProd_mem 𝒜 x l)
      (locDeg_singleton i d l.length) s,
    ← Scheme.Modules.app_restrict]
  rw [show E (_ •
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op s) =
      Scheme.Modules.Hom.app
        (ProjectiveSpectrum.Twist.twistModuleMulHom 𝒜 F
          (⟨((x i : A)) ^ l.length, pow_var_mem 𝒜 x i l.length⟩ : 𝒜 l.length)
          d (ProjectiveSpace.GradedModule.locDeg [i] d l.length)
          (locDeg_singleton i d l.length)) U
        (_ • (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op s) from rfl,
    Scheme.Modules.Hom.app_smul]
  exact app_twistModuleMulHom_eq_homogeneousRatio_smul_of_le
    𝒜 (x i).2 (varProd_mem 𝒜 x l) F d
      (ProjectiveSpace.GradedModule.locDeg [i] d l.length)
      (locDeg_singleton i d l.length) (pow_var_mem 𝒜 x i l.length)
      U le_rfl
      ((ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op s)

set_option maxHeartbeats 1000000 in
-- Submodule supremum induction retains the full chart-stage comparison expression.
/-- Membership form of `chartStageMap_mulList_eq_ratio_smul_res`, extended
from the generators of `mulSpan` to its entire supremum. -/
theorem chartStageMap_mem_span_of_mem_mulSpan
    {n : ℕ} {R : CommRingCat.{u}} (π : Proj 𝒜 ⟶ Spec R)
    (F : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1)
    (i : Fin (n + 1)) (d : ℤ) (j : ℕ)
    (z : (gammaStar 𝒜 π F x).obj
      (ProjectiveSpace.GradedModule.locDeg [i] d j))
    (hz : z ∈ (gammaStar 𝒜 π F x).mulSpan d
      (ProjectiveSpace.GradedModule.locDeg [i] d j)) :
    letI := Scheme.Modules.openSectionsModuleOver π
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
      (basicOpen 𝒜 (x i : A))
    chartStageMap 𝒜 π F x i d j z ∈
      Submodule.span Γ(Proj 𝒜, basicOpen 𝒜 (x i : A))
        (Set.range (fun s : (gammaStar 𝒜 π F x).obj d ↦
          (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
            (homOfLE (le_top : basicOpen 𝒜 (x i : A) ≤ ⊤)).op s)) := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
    (basicOpen 𝒜 (x i : A))
  refine Submodule.iSup_induction
    (fun l : {l : List (Fin (n + 1)) //
        d + (l.length : ℤ) = ProjectiveSpace.GradedModule.locDeg [i] d j} ↦
      LinearMap.range (((gammaStar 𝒜 π F x).mulList l.1 d
        (ProjectiveSpace.GradedModule.locDeg [i] d j) l.2).hom))
    (motive := fun w ↦ chartStageMap 𝒜 π F x i d j w ∈
      Submodule.span Γ(Proj 𝒜, basicOpen 𝒜 (x i : A))
        (Set.range (fun s : (gammaStar 𝒜 π F x).obj d ↦
          (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
            (homOfLE (le_top : basicOpen 𝒜 (x i : A) ≤ ⊤)).op s)))
    hz ?_ ?_ ?_
  · rintro ⟨l, hl⟩ _ ⟨s, rfl⟩
    have hlen : l.length = j := by
      rw [locDeg_singleton] at hl
      omega
    subst j
    rw [chartStageMap_mulList_eq_ratio_smul_res]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨s, rfl⟩)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro z₁ z₂ hz₁ hz₂
    rw [map_add]
    exact Submodule.add_mem _ hz₁ hz₂

set_option maxHeartbeats 1000000 in
-- Direct-limit representatives and chart restriction spans elaborate simultaneously.
/-- If degree `d` generates every stage of the localization tower under monomial
multiplication, then the degree-`d` global sections generate on a standard chart. -/
theorem span_restrict_eq_top_of_mulSpan_chart
    {n : ℕ} {R : CommRingCat.{u}} (π : Proj 𝒜 ⟶ Spec R)
    (F : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1)
    (i : Fin (n + 1))
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤
      ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent]
    (d : ℤ)
    (hmul : ∀ j : ℕ, (gammaStar 𝒜 π F x).mulSpan d
      (ProjectiveSpace.GradedModule.locDeg [i] d j) = ⊤) :
    Submodule.span Γ(Proj 𝒜, basicOpen 𝒜 (x i : A))
      (Set.range (fun s : (gammaStar 𝒜 π F x).obj d ↦
        (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 (x i : A) ≤ ⊤)).op s)) = ⊤ := by
  letI := Scheme.Modules.openSectionsModuleOver π
    (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
    (basicOpen 𝒜 (x i : A))
  apply top_unique
  intro y _
  obtain ⟨w, hw⟩ := (bijective_chartColimitMap 𝒜 π F x i hcover d).2 y
  obtain ⟨j, z, rfl⟩ := Module.DirectLimit.exists_of w
  rw [chartColimitMap_of] at hw
  rw [← hw]
  exact chartStageMap_mem_span_of_mem_mulSpan 𝒜 π F x i d j z
    ((hmul j).symm ▸ Submodule.mem_top)

set_option maxHeartbeats 1000000 in
-- The Čech augmentation comparison expands at every localization-tower degree.
/-- A multiplication-span theorem in Čech `H⁰`, starting at degree `d`, makes
the degree-`d` global sections generate on every standard chart. -/
theorem span_restrict_eq_top_of_cechHgr_mulSpan_chart
    {n : ℕ} {R : CommRingCat.{u}} (π : Proj 𝒜 ⟶ Spec R)
    (F : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1)
    (i : Fin (n + 1))
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤
      ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent]
    (d : ℤ)
    (hmul : ∀ e : ℤ, d ≤ e →
      ((gammaStar 𝒜 π F x).cechHgr 0).mulSpan d e = ⊤) :
    Submodule.span Γ(Proj 𝒜, basicOpen 𝒜 (x i : A))
      (Set.range (fun s : (gammaStar 𝒜 π F x).obj d ↦
        (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
          (homOfLE (le_top : basicOpen 𝒜 (x i : A) ≤ ⊤)).op s)) = ⊤ := by
  apply span_restrict_eq_top_of_mulSpan_chart 𝒜 π F x i hcover d
  intro j
  apply ProjectiveSpace.GradedModule.mulSpan_eq_top_of_cechHgrZero_of_bijective_cechAug
  · exact bijective_gammaStar_cechAug 𝒜 π F x hcover d
  · exact bijective_gammaStar_cechAug 𝒜 π F x hcover
      (ProjectiveSpace.GradedModule.locDeg [i] d j)
  · apply hmul
    rw [locDeg_singleton]
    omega

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "π" => Proj.polynomialToSpec (Fin (n + 1)) R
local notation "x" => _root_.AlgebraicGeometry.ProjectiveSpace.stdVars n R

set_option maxHeartbeats 2000000 in
-- The standard affine cover proof retains every chart restriction and sheafification map.
set_option synthInstance.maxHeartbeats 1000000 in
-- Quasicoherence and restriction instances are synthesized for the whole finite cover.
/-- On polynomial projective space, a degree-`d` Čech multiplication-span
statement makes the map from the free sheaf on all degree-`d` global sections
epimorphic. -/
theorem epi_freeHomOfAllSections_of_cechHgr_mulSpan
    (F : (Proj 𝒜).Modules)
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent]
    (d : ℤ)
    (hmul : ∀ e : ℤ, d ≤ e →
      ((gammaStar 𝒜 π F x).cechHgr 0).mulSpan d e = ⊤) :
    Epi (Scheme.Modules.freeHomOfSections
      (M := ProjectiveSpectrum.Twist.twistModule 𝒜 F d)
      (fun s : (gammaStar 𝒜 π F x).obj d ↦ s)) := by
  classical
  let s : (gammaStar 𝒜 π F x).obj d →
      Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, ⊤) := fun a ↦ a
  let φ := Scheme.Modules.freeHomOfSections s
  have hcover : (⊤ : (Proj 𝒜).Opens) ≤
      ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : MvPolynomial (Fin (n + 1)) R)) :=
    ProjectiveSpace.top_le_iSup_basicOpen_stdVars n R
  have hspan (i : Fin (n + 1)) :
      Submodule.span
        Γ(Proj 𝒜, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
        (Set.range (fun a ↦
          (ProjectiveSpectrum.Twist.twistModule 𝒜 F d).presheaf.map
            (homOfLE (le_top : basicOpen 𝒜
              (x i : MvPolynomial (Fin (n + 1)) R) ≤ ⊤)).op (s a))) = ⊤ :=
    span_restrict_eq_top_of_cechHgr_mulSpan_chart
      𝒜 π F x i hcover d hmul
  change Epi φ
  apply Scheme.Modules.epi_of_openCover_restrict φ
    (Scheme.Cover.ulift
      (Proj.polynomialAffineOpenCover (Fin (n + 1)) R).openCover)
  intro z
  let 𝒰₀ := (Proj.polynomialAffineOpenCover (Fin (n + 1)) R).openCover
  let i : Fin (n + 1) := 𝒰₀.idx z
  change Epi ((Scheme.Modules.restrictFunctor (𝒰₀.f i)).map φ)
  apply Scheme.Modules.epi_restrictFunctor_map_of_app_image_top_surjective
  have hsurj := Scheme.Modules.surjective_app_freeHomOfSections_of_span s
    (basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)) (hspan i)
  have hf : 𝒰₀.f i =
      Proj.awayι 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)
        (MvPolynomial.isHomogeneous_X R i) Nat.one_pos := by
    change (Proj.polynomialAffineOpenCover (Fin (n + 1)) R).f i = _
    exact Proj.polynomialAffineOpenCover_f (Fin (n + 1)) R i
  have hopen : 𝒰₀.f i ''ᵁ (⊤ : (𝒰₀.X i).Opens) =
      basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) := by
    apply TopologicalSpace.Opens.ext
    simp only [Scheme.Hom.coe_image, TopologicalSpace.Opens.coe_top, Set.image_univ]
    change Set.range (𝒰₀.f i).base =
      (basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) : Set (Proj 𝒜))
    calc
      Set.range (𝒰₀.f i).base = Set.range
          (Proj.awayι 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)
            (MvPolynomial.isHomogeneous_X R i) Nat.one_pos).base :=
        congrArg (fun g ↦ Set.range g.base) hf
      _ = ((Proj.awayι 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)
          (MvPolynomial.isHomogeneous_X R i) Nat.one_pos).opensRange : Set (Proj 𝒜)) := rfl
      _ = (basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) : Set (Proj 𝒜)) :=
        congrArg (fun U : (Proj 𝒜).Opens ↦ (U : Set (Proj 𝒜)))
          (Proj.opensRange_awayι 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)
            (MvPolynomial.isHomogeneous_X R i) Nat.one_pos)
  exact Scheme.Modules.surjective_app_of_eq φ hopen hsurj

set_option maxHeartbeats 2000000 in
-- The evaluation counit factors through the preceding all-sections free presentation.
set_option synthInstance.maxHeartbeats 1000000 in
-- Its factorization carries nested pullback, pushforward, and free-sheaf instances.
/-- The same multiplication-span hypothesis makes the projective
pullback--pushforward evaluation epimorphic. -/
theorem pullbackPushforwardCounit_epi_of_cechHgr_mulSpan
    (F : (Proj 𝒜).Modules)
    [∀ e : ℤ, (ProjectiveSpectrum.Twist.twistModule 𝒜 F e).IsQuasicoherent]
    (d : ℤ)
    (hmul : ∀ e : ℤ, d ≤ e →
      ((gammaStar 𝒜 π F x).cechHgr 0).mulSpan d e = ⊤) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction π).counit.app
      (ProjectiveSpectrum.Twist.twistModule 𝒜 F d)) := by
  let s : (gammaStar 𝒜 π F x).obj d →
      Γ(ProjectiveSpectrum.Twist.twistModule 𝒜 F d, ⊤) := fun a ↦ a
  letI : Epi (Scheme.Modules.freeHomOfSections s) :=
    epi_freeHomOfAllSections_of_cechHgr_mulSpan F d hmul
  exact Scheme.Modules.pullbackPushforwardCounit_epi_of_freeHomOfSections
    π _ s

end AlgebraicGeometry.Proj

end

end
