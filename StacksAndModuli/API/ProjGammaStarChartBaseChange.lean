module

public import StacksAndModuli.API.ProjGammaStarBaseChange
public import StacksAndModuli.API.PolynomialProjectiveGlobalSectionsBaseChange
public import StacksAndModuli.API.ProjectiveGradedCechBaseChange
public import StacksAndModuli.API.ProjGammaStarChartComparison
public import StacksAndModuli.API.ProjTwistModuleQuasicoherent
public import StacksAndModuli.API.SchemeModulesTensorUnitNaturality

/-!
# The chart square for the base-change comparison of `Γ_*`

`AlgebraicGeometry.ProjectiveSpace.HasGammaStarBaseChangeCechHgrZero` is the single named
obligation of `RelativeCohomology.SchemeGlobalSectionsComparison`
(`API/ProjectiveSpaceTwistProjComparison.lean`).  By
`GradedModule.isIso_cechHgrMap_app_zero_of_injective` it reduces to bijectivity of the
comparison `gammaStarBaseChangeHom` after localizing at each coordinate, and by
`Proj.bijective_locMap_app_iff_bijective_comp` together with `Proj.chartColimitMap_locMap`
*that* reduces to a single identity at one stage of the localization tower.

This file proves that identity, `chartStageMap_gammaStarBaseChangeApp`:

```
chartStageMap_S i d j (Φ_{d+j}(1 ⊗ m))
  = ρ ( T_d ( bc ( 1 ⊗ chartStageMap_R i d j m ) ) )
```

where `Φ` is `gammaStarBaseChangeApp`, `bc` is the chart-level base-change map
(`pullbackOpenSectionsBaseChangeLinearMap`, bijective by
`Proj.ProjectiveCoverPullback.bijective_pullbackOpenSectionsBaseChange_chart`), `T` is the
twist-pullback comparison, and `ρ` is the restriction along the equality of opens
`gg⁻¹ D₊(xᵢ)_R = D₊(xᵢ)_S`.

Every input was already available; the work is the bookkeeping.  In order of use:

* `Proj.chartStageMap_apply` and `Proj.chartTwistLinearEquiv_apply` — the stage map is
  "restrict to the chart, then divide by `xᵢ^j`", and the division is `twistModuleMulHom`;
* naturality of `twistModuleMulHom` and of `twistModulePolynomialPullbackHom` with respect to
  restriction (`Scheme.Modules.Hom.mapPresheaf.naturality`);
* `ProjectiveSpectrum.Twist.pullback_map_twistModuleMulHom_comp_twistModulePolynomialPullbackHom`
  — the twist comparison intertwines multiplication by a form, with
  `gradedImage_stdVars_pow` identifying the image of `xᵢ^j`;
* naturality of the pullback-adjunction unit, both in the module and in the open;
* `gammaStarBaseChangeApp_tmul`.

**Two practical points.**  `Scheme.Modules.Hom.app ψ U` and
`(PresheafOfModules.Hom.app ψ.val (op U)).hom` are equal as functions but never syntactically,
so `rw` fails across them; restate the hypothesis in the form the goal uses and close the
restatement with `:= h` (defeq).  Some of those defeq checks are expensive, hence the raised
heartbeat budget.  The file also uses `local notation` (with `quotPrecheck` off, since the
abbreviations contain projections and anonymous constructors) — without it the statement alone
runs to eighty lines.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.coeffMap_preimage_basicOpen`;
* `AlgebraicGeometry.ProjectiveSpace.gradedImage_stdVars_pow`;
* `AlgebraicGeometry.ProjectiveSpace.chartStageMap_gammaStarBaseChangeApp`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false
-- The local notations below abbreviate projections and anonymous constructors.
set_option quotPrecheck false

open CategoryTheory TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry ProjectiveSpectrum.Twist

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
variable (i : Fin (n + 1)) (d : ℤ) (j : ℕ)

local notation "𝒜R" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "𝒜S" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S
local notation "gg" => coeffMap n φ
local notation "FS" => (Scheme.Modules.pullback (coeffMap n φ)).obj F
local notation "πR" => Proj.polynomialToSpec (Fin (n + 1)) R
local notation "πS" => Proj.polynomialToSpec (Fin (n + 1)) S
local notation "DR" => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  ((stdVars n R i : MvPolynomial (Fin (n + 1)) R))
local notation "DS" => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
  ((stdVars n S i : MvPolynomial (Fin (n + 1)) S))
local notation "VV" => coeffMap n φ ⁻¹ᵁ Proj.basicOpen
  (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  ((stdVars n R i : MvPolynomial (Fin (n + 1)) R))
local notation "ee" => ProjectiveSpace.GradedModule.locDeg [i] d j
local notation "xRj" => (⟨(stdVars n R i : MvPolynomial (Fin (n + 1)) R) ^ j,
  Proj.pow_var_mem _ (stdVars n R) i j⟩ :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R j)
local notation "xSj" => (⟨(stdVars n S i : MvPolynomial (Fin (n + 1)) S) ^ j,
  Proj.pow_var_mem _ (stdVars n S) i j⟩ :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S j)

/-- The chart of `ℙⁿ_S` is the preimage of the chart of `ℙⁿ_R`. -/
theorem coeffMap_preimage_basicOpen : VV = DS :=
  Proj.polynomialMap_preimage_polynomialStandardOpen n φ i

/-- Coefficient change fixes the powers of the standard coordinates. -/
theorem gradedImage_stdVars_pow :
    gradedImage (MvPolynomial.mapGradedRingHom (ι := Fin (n + 1)) φ) xRj = xSj := by
  refine Subtype.ext ?_
  show MvPolynomial.mapGradedRingHom φ ((MvPolynomial.X i) ^ j) = (MvPolynomial.X i) ^ j
  rw [map_pow, MvPolynomial.mapGradedRingHom_X]

set_option maxHeartbeats 2000000 in
/-- **The stage identity of the chart square.** -/
theorem chartStageMap_gammaStarBaseChangeApp (m : Γ(twistModule 𝒜R F ee, ⊤)) :
    letI : Algebra R S := φ.toAlgebra
    letI := Scheme.Modules.openSectionsModuleOver πS (twistModule 𝒜S FS d) DS
    letI := Scheme.Modules.openSectionsModuleOver πR (twistModule 𝒜R F d) DR
    letI := Scheme.Modules.globalSectionsModule πR (twistModule 𝒜R F ee)
    letI := Scheme.Modules.globalSectionsModule πS (twistModule 𝒜S FS ee)
    Proj.chartStageMap 𝒜S πS FS (stdVars n S) i d j
        (gammaStarBaseChangeApp n φ F ee (1 ⊗ₜ[R] m))
      = (twistModule 𝒜S FS d).presheaf.map
          (homOfLE (coeffMap_preimage_basicOpen n φ i).ge).op
          (Scheme.Modules.Hom.app
            (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) VV
            (pullbackOpenSectionsBaseChangeLinearMap (CommRingCat.ofHom φ) gg πR πS
              (coeffMap_w n φ) (twistModule 𝒜R F d) DR
              (1 ⊗ₜ[R] (Proj.chartStageMap 𝒜R πR F (stdVars n R) i d j m)))) := by
  letI : Algebra R S := φ.toAlgebra
  letI := Scheme.Modules.openSectionsModuleOver πS (twistModule 𝒜S FS d) DS
  letI := Scheme.Modules.openSectionsModuleOver πR (twistModule 𝒜R F d) DR
  letI := Scheme.Modules.globalSectionsModule πR (twistModule 𝒜R F ee)
  letI := Scheme.Modules.globalSectionsModule πS (twistModule 𝒜S FS ee)
  letI := Scheme.Modules.openSectionsModule πR (twistModule 𝒜R F d) DR
  have hge : DS ≤ VV := (coeffMap_preimage_basicOpen n φ i).ge
  refine (Proj.chartTwistLinearEquiv 𝒜S πS FS (stdVars n S) i d j ee
    (Proj.locDeg_singleton i d j)).injective ?_
  rw [Proj.chartStageMap_apply, LinearEquiv.apply_symm_apply,
    Proj.chartTwistLinearEquiv_apply]
  have hA : ∀ v, Scheme.Modules.Hom.app
        (twistModuleMulHom 𝒜S FS xSj d ee (Proj.locDeg_singleton i d j)) DS
        ((twistModule 𝒜S FS d).presheaf.map (homOfLE hge).op v)
      = (twistModule 𝒜S FS ee).presheaf.map (homOfLE hge).op
        (Scheme.Modules.Hom.app
          (twistModuleMulHom 𝒜S FS xSj d ee (Proj.locDeg_singleton i d j)) VV v) := by
    intro v
    have h := CategoryTheory.congr_fun
      ((twistModuleMulHom 𝒜S FS xSj d ee
        (Proj.locDeg_singleton i d j)).mapPresheaf.naturality (homOfLE hge).op) v
    simp only [CategoryTheory.comp_apply] at h
    exact h
  have hF2 := pullback_map_twistModuleMulHom_comp_twistModulePolynomialPullbackHom
    (Fin (n + 1)) φ F xRj d ee (Proj.locDeg_singleton i d j)
  rw [gradedImage_stdVars_pow] at hF2
  have hF2' : ∀ z, (PresheafOfModules.Hom.app
        (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F ee).val (op VV)).hom
        ((PresheafOfModules.Hom.app
          ((Scheme.Modules.pullback gg).map
            (twistModuleMulHom 𝒜R F xRj d ee (Proj.locDeg_singleton i d j))).val
          (op VV)).hom z)
      = (PresheafOfModules.Hom.app
          (twistModuleMulHom 𝒜S FS xSj d ee (Proj.locDeg_singleton i d j)).val (op VV)).hom
          ((PresheafOfModules.Hom.app
            (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d).val (op VV)).hom z) := fun z ↦
    congrArg (fun ψ : (Scheme.Modules.pullback gg).obj (twistModule 𝒜R F d) ⟶
        twistModule 𝒜S FS ee ↦ (PresheafOfModules.Hom.app ψ.val (op VV)).hom z) hF2
  have hUnitMod := fun w ↦ congrArg
    (fun ψ : twistModule 𝒜R F d ⟶ _ ↦ (PresheafOfModules.Hom.app ψ.val (op DR)).hom w)
    ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.naturality
      (twistModuleMulHom 𝒜R F xRj d ee (Proj.locDeg_singleton i d j)))
  have hcore : (PresheafOfModules.Hom.app
        (twistModuleMulHom 𝒜S FS xSj d ee (Proj.locDeg_singleton i d j)).val (op VV)).hom
        ((PresheafOfModules.Hom.app
          (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d).val (op VV)).hom
          (pullbackOpenSectionsBaseChangeLinearMap (CommRingCat.ofHom φ) gg πR πS
            (coeffMap_w n φ) (twistModule 𝒜R F d) DR
            (1 ⊗ₜ[R] (Proj.chartStageMap 𝒜R πR F (stdVars n R) i d j m))))
      = (twistModule 𝒜S FS ee).presheaf.map
          (homOfLE (show VV ≤ (⊤ : (Proj 𝒜S).Opens) from le_top)).op
          (gammaStarBaseChangeApp n φ F ee (1 ⊗ₜ[R] m)) := by
    rw [pullbackOpenSectionsBaseChangeLinearMap_tmul, one_smul, ← hF2']
    have hUnitMod' : ∀ w, (PresheafOfModules.Hom.app ((Scheme.Modules.pullback gg).map
          (twistModuleMulHom 𝒜R F xRj d ee (Proj.locDeg_singleton i d j))).val (op VV)).hom
          (Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
              (twistModule 𝒜R F d)) DR w)
        = Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
              (twistModule 𝒜R F ee)) DR
            (Scheme.Modules.Hom.app
              (twistModuleMulHom 𝒜R F xRj d ee (Proj.locDeg_singleton i d j)) DR w) :=
      fun w ↦ (hUnitMod w).symm
    rw [hUnitMod']
    have hBR : Scheme.Modules.Hom.app
        (twistModuleMulHom 𝒜R F xRj d ee (Proj.locDeg_singleton i d j)) DR
        (Proj.chartStageMap 𝒜R πR F (stdVars n R) i d j m)
      = (twistModule 𝒜R F ee).presheaf.map
          (homOfLE (show DR ≤ (⊤ : (Proj 𝒜R).Opens) from le_top)).op m := by
      rw [Proj.chartStageMap_apply, ← Proj.chartTwistLinearEquiv_apply 𝒜R πR F (stdVars n R)
        i d j ee (Proj.locDeg_singleton i d j), LinearEquiv.apply_symm_apply]
    rw [hBR]
    have hUnitOpen := CategoryTheory.congr_fun
      (((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
        (twistModule 𝒜R F ee)).mapPresheaf.naturality
          (homOfLE (show DR ≤ (⊤ : (Proj 𝒜R).Opens) from le_top)).op) m
    simp only [CategoryTheory.comp_apply] at hUnitOpen
    have hUnitOpen' : Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app (twistModule 𝒜R F ee)) DR
        ((twistModule 𝒜R F ee).presheaf.map
          (homOfLE (show DR ≤ (⊤ : (Proj 𝒜R).Opens) from le_top)).op m)
      = ((Scheme.Modules.pullback gg).obj (twistModule 𝒜R F ee)).presheaf.map
          (homOfLE (show VV ≤ (⊤ : (Proj 𝒜S).Opens) from le_top)).op
          (Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
              (twistModule 𝒜R F ee)) ⊤ m) := hUnitOpen
    rw [hUnitOpen']
    have hTe := CategoryTheory.congr_fun
      ((twistModulePolynomialPullbackHom (Fin (n + 1)) φ F ee).mapPresheaf.naturality
        (homOfLE (show VV ≤ (⊤ : (Proj 𝒜S).Opens) from le_top)).op)
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
          (twistModule 𝒜R F ee)) ⊤ m)
    simp only [CategoryTheory.comp_apply] at hTe
    have hTe' : (PresheafOfModules.Hom.app
        (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F ee).val (op VV)).hom
        (((Scheme.Modules.pullback gg).obj (twistModule 𝒜R F ee)).presheaf.map
          (homOfLE (show VV ≤ (⊤ : (Proj 𝒜S).Opens) from le_top)).op
          (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
            (twistModule 𝒜R F ee)) ⊤ m))
      = (twistModule 𝒜S FS ee).presheaf.map
          (homOfLE (show VV ≤ (⊤ : (Proj 𝒜S).Opens) from le_top)).op
          (Scheme.Modules.Hom.app
            (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F ee) ⊤
            (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
              (twistModule 𝒜R F ee)) ⊤ m)) := hTe
    rw [hTe']
    congr 1
    rw [gammaStarBaseChangeApp_tmul, one_smul]
    rfl
  refine Eq.symm (Eq.trans (hA _) ?_)
  refine Eq.trans (congrArg
    (fun y ↦ (twistModule 𝒜S FS ee).presheaf.map (homOfLE hge).op y) hcore) ?_
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

set_option maxHeartbeats 2000000 in
/-- **The stage identity on a general pure tensor.**  `chartStageMap_gammaStarBaseChangeApp`
with `1 ⊗ m` replaced by `a ⊗ m`, which is the form the localization tower hands you.

The scalar is pulled out by `S`-linearity of the four maps involved.  Two of them are already
`→ₗ[S]`; for `Scheme.Modules.Hom.app` and for the restriction it is
`Scheme.Modules.openSectionsLinearMap` and `Scheme.Modules.openRestrictionLinearMap` — note
these use `openSectionsModuleOver` and `openSectionsModule` respectively, two defeq but
syntactically different module instances, so the `map_smul` facts must be *stated* in the
flavour the goal uses and closed with `exact`. -/
theorem chartStageMap_gammaStarBaseChangeApp_tmul (a : S)
    (m : Γ(twistModule 𝒜R F ee, ⊤)) :
    letI : Algebra R S := φ.toAlgebra
    letI := Scheme.Modules.openSectionsModuleOver πS (twistModule 𝒜S FS d) DS
    letI := Scheme.Modules.openSectionsModuleOver πR (twistModule 𝒜R F d) DR
    letI := Scheme.Modules.globalSectionsModule πR (twistModule 𝒜R F ee)
    letI := Scheme.Modules.globalSectionsModule πS (twistModule 𝒜S FS ee)
    Proj.chartStageMap 𝒜S πS FS (stdVars n S) i d j
        (gammaStarBaseChangeApp n φ F ee (a ⊗ₜ[R] m))
      = (twistModule 𝒜S FS d).presheaf.map
          (homOfLE (coeffMap_preimage_basicOpen n φ i).ge).op
          (Scheme.Modules.Hom.app
            (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) VV
            (pullbackOpenSectionsBaseChangeLinearMap (CommRingCat.ofHom φ) gg πR πS
              (coeffMap_w n φ) (twistModule 𝒜R F d) DR
              (a ⊗ₜ[R] (Proj.chartStageMap 𝒜R πR F (stdVars n R) i d j m)))) := by
  letI : Algebra R S := φ.toAlgebra
  letI := Scheme.Modules.openSectionsModuleOver πS (twistModule 𝒜S FS d) DS
  letI := Scheme.Modules.openSectionsModuleOver πR (twistModule 𝒜R F d) DR
  letI := Scheme.Modules.globalSectionsModule πR (twistModule 𝒜R F ee)
  letI := Scheme.Modules.globalSectionsModule πS (twistModule 𝒜S FS ee)
  letI := Scheme.Modules.openSectionsModule πR (twistModule 𝒜R F d) DR
  letI := Scheme.Modules.openSectionsModule πS
    ((Scheme.Modules.pullback gg).obj (twistModule 𝒜R F d)) VV
  letI := Scheme.Modules.openSectionsModule πS (twistModule 𝒜S FS d) VV
  letI := Scheme.Modules.openSectionsModule πS (twistModule 𝒜S FS d) DS
  have hge : DS ≤ VV := (coeffMap_preimage_basicOpen n φ i).ge
  have hT : ∀ (b : S) (z : Γ((Scheme.Modules.pullback gg).obj (twistModule 𝒜R F d), VV)),
      Scheme.Modules.Hom.app
          (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) VV (b • z)
        = b • Scheme.Modules.Hom.app
          (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) VV z := by
    intro b z
    exact (Scheme.Modules.openSectionsLinearMap πS
      (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) VV).map_smul b z
  have hρ : ∀ (b : S) (z : Γ(twistModule 𝒜S FS d, VV)),
      (twistModule 𝒜S FS d).presheaf.map (homOfLE hge).op (b • z)
        = b • (twistModule 𝒜S FS d).presheaf.map (homOfLE hge).op z := by
    intro b z
    exact (Scheme.Modules.openRestrictionLinearMap πS (twistModule 𝒜S FS d) hge).map_smul b z
  have ha : (a ⊗ₜ[R] m : S ⊗[R] Γ(twistModule 𝒜R F ee, ⊤)) = a • (1 ⊗ₜ[R] m) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have ha' : (a ⊗ₜ[R] (Proj.chartStageMap 𝒜R πR F (stdVars n R) i d j m)
      : S ⊗[R] Γ(twistModule 𝒜R F d, DR))
      = a • (1 ⊗ₜ[R] (Proj.chartStageMap 𝒜R πR F (stdVars n R) i d j m)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [ha, ha', map_smul, map_smul, map_smul, hT, hρ,
    chartStageMap_gammaStarBaseChangeApp n φ F i d j m]

local notation "GR" => Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
  (Proj.polynomialToSpec (Fin (n + 1)) R) F (stdVars n R)

set_option maxHeartbeats 2000000 in
/-- **The chart square, in the colimit.**  Composing the localized base-change comparison with
the chart comparison is the same as: identify the localization of the base change with the base
change of the localization (`locBaseChangeToTensor`), apply the chart comparison over `R`, base
change the sections along the chart (`pullbackOpenSectionsBaseChangeLinearMap`), compare the
twists (`twistModulePolynomialPullbackHom`), and restrict to the chart of `ℙⁿ_S`.

Proved by `Module.DirectLimit.induction_on` and then `TensorProduct.induction_on`, with
`Proj.chartColimitMap_locMap` on the left, `GradedModule.locIncl_locBaseChangeToTensor` on the
right, and `chartStageMap_gammaStarBaseChangeApp_tmul` in the middle.

**Every map on the right-hand side is bijective**, which is what
`HasGammaStarBaseChangeCechHgrZero` needs: `GradedModule.bijective_locBaseChangeToTensor`,
`Proj.bijective_chartColimitMap`,
`Proj.ProjectiveCoverPullback.bijective_pullbackOpenSectionsBaseChange_chart`,
`ProjectiveSpectrum.Twist.twistModulePolynomialPullbackHom_isIso` (for `d : ℕ`), and the fact
that the last restriction is along an equality of opens. -/
theorem chartColimitMap_locMap_baseChange :
    letI : Algebra R S := φ.toAlgebra
    letI := Scheme.Modules.openSectionsModuleOver πS (twistModule 𝒜S FS d)
      (Proj.basicOpen 𝒜S ((stdVars n S i : MvPolynomial (Fin (n + 1)) S)))
    letI := Scheme.Modules.openSectionsModuleOver πR (twistModule 𝒜R F d) DR
    ∀ w : ((GradedModule.baseChange GR S).loc [i]).obj d,
      Proj.chartColimitMap 𝒜S πS FS (stdVars n S) i d
          (((GradedModule.locMap [i] (gammaStarBaseChangeHom n φ F)).app d).hom w)
        = (twistModule 𝒜S FS d).presheaf.map
            (homOfLE (coeffMap_preimage_basicOpen n φ i).ge).op
            (Scheme.Modules.Hom.app
              (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) VV
              (pullbackOpenSectionsBaseChangeLinearMap (CommRingCat.ofHom φ) gg πR πS
                (coeffMap_w n φ) (twistModule 𝒜R F d) DR
                (LinearMap.baseChange S
                  (Proj.chartColimitMap 𝒜R πR F (stdVars n R) i d)
                  ((GradedModule.locBaseChangeToTensor S GR [i] d).hom w)))) := by
  intro w
  letI : Algebra R S := φ.toAlgebra
  letI := Scheme.Modules.openSectionsModuleOver πS (twistModule 𝒜S FS d)
    (Proj.basicOpen 𝒜S ((stdVars n S i : MvPolynomial (Fin (n + 1)) S)))
  letI := Scheme.Modules.openSectionsModuleOver πR (twistModule 𝒜R F d) DR
  induction w using Module.DirectLimit.induction_on with
  | ih t z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
      have hL := Proj.chartColimitMap_locMap 𝒜S πS FS (stdVars n S) i
        (gammaStarBaseChangeHom n φ F) d t (a ⊗ₜ[R] m)
      have hR := congrArg (fun ψ : ((GradedModule.baseChange GR S).obj
          (GradedModule.locDeg [i] d t)) ⟶
          ModuleCat.of S (S ⊗[R] ((GradedModule.loc GR [i]).obj d)) ↦ ψ.hom (a ⊗ₜ[R] m))
        (GradedModule.locIncl_locBaseChangeToTensor S GR [i] d t)
      refine hL.trans (Eq.trans ?_ (congrArg
        (fun y : ModuleCat.of S (S ⊗[R] ((GradedModule.loc GR [i]).obj d)) ↦
          (twistModule 𝒜S FS d).presheaf.map
            (homOfLE (coeffMap_preimage_basicOpen n φ i).ge).op
            (Scheme.Modules.Hom.app
              (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) VV
              (pullbackOpenSectionsBaseChangeLinearMap (CommRingCat.ofHom φ) gg πR πS
                (coeffMap_w n φ) (twistModule 𝒜R F d) DR
                (LinearMap.baseChange S
                  (Proj.chartColimitMap 𝒜R πR F (stdVars n R) i d) y)))) hR).symm)
      refine (chartStageMap_gammaStarBaseChangeApp_tmul n φ F i d t a m).trans ?_
      congr 3
      exact congrArg (fun z ↦ a ⊗ₜ[R] z)
        (Proj.chartColimitMap_of 𝒜R πR F (stdVars n R) i d t m).symm

set_option maxHeartbeats 2000000 in
/-- **The localized base-change comparison is bijective on each chart.** -/
theorem bijective_locMap_gammaStarBaseChangeHom_app [F.IsFinitePresentation] (dN : ℕ) :
    letI : Algebra R S := φ.toAlgebra
    Function.Bijective
      (((GradedModule.locMap [i] (gammaStarBaseChangeHom n φ F)).app (dN : ℤ)).hom) := by
  letI : Algebra R S := φ.toAlgebra
  haveI : ((Scheme.Modules.pullback (coeffMap n φ)).obj F).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  letI hqS : ∀ e : ℤ, (twistModule 𝒜S FS e).IsQuasicoherent := fun e ↦
    twistModule_std_isQuasicoherent FS e
  letI hqR : ∀ e : ℤ, (twistModule 𝒜R F e).IsQuasicoherent := fun e ↦
    twistModule_std_isQuasicoherent F e
  letI := Scheme.Modules.openSectionsModuleOver πR (twistModule 𝒜R F (dN : ℤ)) DR
  letI := Scheme.Modules.openSectionsModuleOver πS (twistModule 𝒜S FS (dN : ℤ)) DS
  rw [Proj.bijective_locMap_app_iff_bijective_comp 𝒜S πS FS (stdVars n S) i
    (top_le_iSup_basicOpen_stdVars n S) (gammaStarBaseChangeHom n φ F) (dN : ℤ)]
  have hb1 := GradedModule.bijective_locBaseChangeToTensor S GR [i] (dN : ℤ)
  have hb2 : Function.Bijective (LinearMap.baseChange S
      (Proj.chartColimitMap 𝒜R πR F (stdVars n R) i (dN : ℤ))) := by
    have he := Proj.bijective_chartColimitMap 𝒜R πR F (stdVars n R) i
      (top_le_iSup_basicOpen_stdVars n R) (dN : ℤ)
    exact ((LinearEquiv.ofBijective _ he).baseChange _ S _ _).bijective
  have hb3 := Proj.ProjectiveCoverPullback.bijective_pullbackOpenSectionsBaseChange_chart
    n φ (twistModule 𝒜R F (dN : ℤ)) i
  have hb4 := Scheme.Modules.bijective_app_of_iso
    (asIso (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F (dN : ℤ))) (op VV)
  have hge : DS ≤ VV := (coeffMap_preimage_basicOpen n φ i).ge
  have hle : VV ≤ DS := (coeffMap_preimage_basicOpen n φ i).le
  have hb5 : Function.Bijective
      ((twistModule 𝒜S FS (dN : ℤ)).presheaf.map (homOfLE hge).op) := by
    constructor
    · intro x y hxy
      have h := congrArg
        ((twistModule 𝒜S FS (dN : ℤ)).presheaf.map (homOfLE hle).op) hxy
      rwa [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
        ← CategoryTheory.Functor.map_comp,
        Subsingleton.elim ((homOfLE hge).op ≫ (homOfLE hle).op) (𝟙 _),
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply,
        ConcreteCategory.id_apply] at h
    · intro y
      refine ⟨(twistModule 𝒜S FS (dN : ℤ)).presheaf.map (homOfLE hle).op y, ?_⟩
      rw [← ConcreteCategory.comp_apply, ← CategoryTheory.Functor.map_comp,
        Subsingleton.elim ((homOfLE hle).op ≫ (homOfLE hge).op) (𝟙 _),
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  have hfun : (fun w ↦ Proj.chartColimitMap 𝒜S πS FS (stdVars n S) i (dN : ℤ)
        (((GradedModule.locMap [i] (gammaStarBaseChangeHom n φ F)).app (dN : ℤ)).hom w))
      = (fun z ↦ (twistModule 𝒜S FS (dN : ℤ)).presheaf.map (homOfLE hge).op z) ∘
        (fun z ↦ Scheme.Modules.Hom.app
          (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F (dN : ℤ)) VV z) ∘
        (fun z ↦ pullbackOpenSectionsBaseChangeLinearMap (CommRingCat.ofHom φ) gg πR πS
          (coeffMap_w n φ) (twistModule 𝒜R F (dN : ℤ)) DR z) ∘
        (fun z ↦ LinearMap.baseChange S
          (Proj.chartColimitMap 𝒜R πR F (stdVars n R) i (dN : ℤ)) z) ∘
        (fun w ↦ (GradedModule.locBaseChangeToTensor S GR [i] (dN : ℤ)).hom w) :=
    funext (chartColimitMap_locMap_baseChange n φ F i (dN : ℤ))
  rw [hfun]
  exact hb5.comp (hb4.comp (hb3.comp (hb2.comp hb1)))

variable (k : Fin (n + 1))

local notation "ER" => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    ((stdVars n R i : MvPolynomial (Fin (n + 1)) R))
  ⊓ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    ((stdVars n R k : MvPolynomial (Fin (n + 1)) R))
local notation "ES" => Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
    ((stdVars n S i : MvPolynomial (Fin (n + 1)) S))
  ⊓ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
    ((stdVars n S k : MvPolynomial (Fin (n + 1)) S))
local notation "WW" => coeffMap n φ ⁻¹ᵁ (Proj.basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    ((stdVars n R i : MvPolynomial (Fin (n + 1)) R))
  ⊓ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    ((stdVars n R k : MvPolynomial (Fin (n + 1)) R)))
local notation "qq" => ProjectiveSpace.GradedModule.locDeg [i, k] d j
local notation "ff" => (⟨Proj.varProd (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (stdVars n R) (ProjectiveSpace.GradedModule.listPow [i, k] j),
  Proj.varProd_mem _ (stdVars n R) _⟩ :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
      (ProjectiveSpace.GradedModule.listPow [i, k] j).length)
local notation "ffS" => (⟨Proj.varProd (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
    (stdVars n S) (ProjectiveSpace.GradedModule.listPow [i, k] j),
  Proj.varProd_mem _ (stdVars n S) _⟩ :
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S
      (ProjectiveSpace.GradedModule.listPow [i, k] j).length)

/-- The overlap of two charts of `ℙⁿ_S` is the preimage of the overlap on `ℙⁿ_R`. -/
theorem coeffMap_preimage_basicOpen_inf : WW = ES :=
  Proj.polynomialMap_preimage_polynomialStandardOpen_inf n φ i k

/-- Coefficient change fixes the monomial attached to a list of coordinates. -/
theorem gradedImage_varProd (l : List (Fin (n + 1))) :
    gradedImage (MvPolynomial.mapGradedRingHom (ι := Fin (n + 1)) φ)
        (⟨Proj.varProd (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (stdVars n R) l,
          Proj.varProd_mem _ (stdVars n R) l⟩ :
          MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R l.length)
      = ⟨Proj.varProd (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S) (stdVars n S) l,
          Proj.varProd_mem _ (stdVars n S) l⟩ := by
  refine Subtype.ext ?_
  show MvPolynomial.mapGradedRingHom φ
      (Proj.varProd (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (stdVars n R) l)
    = Proj.varProd (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S) (stdVars n S) l
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [Proj.varProd_cons, Proj.varProd_cons, map_mul, ih]
      exact congrArg (· * _) (MvPolynomial.mapGradedRingHom_X φ a)

set_option maxHeartbeats 2000000 in
/-- **The stage identity of the chart square, on a pairwise overlap.**  The two-variable
analogue of `chartStageMap_gammaStarBaseChangeApp`; the proof is the same, with
`Proj.pairTwistLinearEquiv` — multiplication by `(xᵢ x_k)^j` — in place of
`Proj.chartTwistLinearEquiv`. -/
theorem pairStageMap_gammaStarBaseChangeApp (m : Γ(twistModule 𝒜R F qq, ⊤)) :
    letI : Algebra R S := φ.toAlgebra
    letI := Scheme.Modules.openSectionsModuleOver πS (twistModule 𝒜S FS d) ES
    letI := Scheme.Modules.openSectionsModuleOver πR (twistModule 𝒜R F d) ER
    letI := Scheme.Modules.globalSectionsModule πR (twistModule 𝒜R F qq)
    letI := Scheme.Modules.globalSectionsModule πS (twistModule 𝒜S FS qq)
    Proj.pairStageMap 𝒜S πS FS (stdVars n S) i k d j
        (gammaStarBaseChangeApp n φ F qq (1 ⊗ₜ[R] m))
      = (twistModule 𝒜S FS d).presheaf.map
          (homOfLE (coeffMap_preimage_basicOpen_inf n φ i k).ge).op
          (Scheme.Modules.Hom.app
            (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) WW
            (pullbackOpenSectionsBaseChangeLinearMap (CommRingCat.ofHom φ) gg πR πS
              (coeffMap_w n φ) (twistModule 𝒜R F d) ER
              (1 ⊗ₜ[R] (Proj.pairStageMap 𝒜R πR F (stdVars n R) i k d j m)))) := by
  letI : Algebra R S := φ.toAlgebra
  letI := Scheme.Modules.openSectionsModuleOver πS (twistModule 𝒜S FS d) ES
  letI := Scheme.Modules.openSectionsModuleOver πR (twistModule 𝒜R F d) ER
  letI := Scheme.Modules.globalSectionsModule πR (twistModule 𝒜R F qq)
  letI := Scheme.Modules.globalSectionsModule πS (twistModule 𝒜S FS qq)
  letI := Scheme.Modules.openSectionsModule πR (twistModule 𝒜R F d) ER
  have hge : ES ≤ WW := (coeffMap_preimage_basicOpen_inf n φ i k).ge
  refine (Proj.pairTwistLinearEquiv 𝒜S πS FS (stdVars n S) i k d j qq
    (Proj.locDeg_eq_length [i, k] d j)).injective ?_
  rw [Proj.pairStageMap_apply, LinearEquiv.apply_symm_apply,
    Proj.pairTwistLinearEquiv_apply]
  have hA : ∀ v, Scheme.Modules.Hom.app
        (twistModuleMulHom 𝒜S FS ffS d qq (Proj.locDeg_eq_length [i, k] d j)) ES
        ((twistModule 𝒜S FS d).presheaf.map (homOfLE hge).op v)
      = (twistModule 𝒜S FS qq).presheaf.map (homOfLE hge).op
        (Scheme.Modules.Hom.app
          (twistModuleMulHom 𝒜S FS ffS d qq (Proj.locDeg_eq_length [i, k] d j)) WW v) := by
    intro v
    have h := CategoryTheory.congr_fun
      ((twistModuleMulHom 𝒜S FS ffS d qq
        (Proj.locDeg_eq_length [i, k] d j)).mapPresheaf.naturality (homOfLE hge).op) v
    simp only [CategoryTheory.comp_apply] at h
    exact h
  have hF2 := pullback_map_twistModuleMulHom_comp_twistModulePolynomialPullbackHom
    (Fin (n + 1)) φ F ff d qq (Proj.locDeg_eq_length [i, k] d j)
  rw [gradedImage_varProd] at hF2
  have hF2' : ∀ z, (PresheafOfModules.Hom.app
        (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F qq).val (op WW)).hom
        ((PresheafOfModules.Hom.app
          ((Scheme.Modules.pullback gg).map
            (twistModuleMulHom 𝒜R F ff d qq (Proj.locDeg_eq_length [i, k] d j))).val
          (op WW)).hom z)
      = (PresheafOfModules.Hom.app
          (twistModuleMulHom 𝒜S FS ffS d qq (Proj.locDeg_eq_length [i, k] d j)).val (op WW)).hom
          ((PresheafOfModules.Hom.app
            (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d).val (op WW)).hom z) := fun z ↦
    congrArg (fun ψ : (Scheme.Modules.pullback gg).obj (twistModule 𝒜R F d) ⟶
        twistModule 𝒜S FS qq ↦ (PresheafOfModules.Hom.app ψ.val (op WW)).hom z) hF2
  have hUnitMod := fun w ↦ congrArg
    (fun ψ : twistModule 𝒜R F d ⟶ _ ↦ (PresheafOfModules.Hom.app ψ.val (op ER)).hom w)
    ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.naturality
      (twistModuleMulHom 𝒜R F ff d qq (Proj.locDeg_eq_length [i, k] d j)))
  have hcore : (PresheafOfModules.Hom.app
        (twistModuleMulHom 𝒜S FS ffS d qq (Proj.locDeg_eq_length [i, k] d j)).val (op WW)).hom
        ((PresheafOfModules.Hom.app
          (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d).val (op WW)).hom
          (pullbackOpenSectionsBaseChangeLinearMap (CommRingCat.ofHom φ) gg πR πS
            (coeffMap_w n φ) (twistModule 𝒜R F d) ER
            (1 ⊗ₜ[R] (Proj.pairStageMap 𝒜R πR F (stdVars n R) i k d j m))))
      = (twistModule 𝒜S FS qq).presheaf.map
          (homOfLE (show WW ≤ (⊤ : (Proj 𝒜S).Opens) from le_top)).op
          (gammaStarBaseChangeApp n φ F qq (1 ⊗ₜ[R] m)) := by
    rw [pullbackOpenSectionsBaseChangeLinearMap_tmul, one_smul, ← hF2']
    have hUnitMod' : ∀ w, (PresheafOfModules.Hom.app ((Scheme.Modules.pullback gg).map
          (twistModuleMulHom 𝒜R F ff d qq (Proj.locDeg_eq_length [i, k] d j))).val (op WW)).hom
          (Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
              (twistModule 𝒜R F d)) ER w)
        = Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
              (twistModule 𝒜R F qq)) ER
            (Scheme.Modules.Hom.app
              (twistModuleMulHom 𝒜R F ff d qq (Proj.locDeg_eq_length [i, k] d j)) ER w) :=
      fun w ↦ (hUnitMod w).symm
    rw [hUnitMod']
    have hBR : Scheme.Modules.Hom.app
        (twistModuleMulHom 𝒜R F ff d qq (Proj.locDeg_eq_length [i, k] d j)) ER
        (Proj.pairStageMap 𝒜R πR F (stdVars n R) i k d j m)
      = (twistModule 𝒜R F qq).presheaf.map
          (homOfLE (show ER ≤ (⊤ : (Proj 𝒜R).Opens) from le_top)).op m := by
      rw [Proj.pairStageMap_apply, ← Proj.pairTwistLinearEquiv_apply 𝒜R πR F (stdVars n R)
        i k d j qq (Proj.locDeg_eq_length [i, k] d j), LinearEquiv.apply_symm_apply]
    rw [hBR]
    have hUnitOpen := CategoryTheory.congr_fun
      (((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
        (twistModule 𝒜R F qq)).mapPresheaf.naturality
          (homOfLE (show ER ≤ (⊤ : (Proj 𝒜R).Opens) from le_top)).op) m
    simp only [CategoryTheory.comp_apply] at hUnitOpen
    have hUnitOpen' : Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app (twistModule 𝒜R F qq)) ER
        ((twistModule 𝒜R F qq).presheaf.map
          (homOfLE (show ER ≤ (⊤ : (Proj 𝒜R).Opens) from le_top)).op m)
      = ((Scheme.Modules.pullback gg).obj (twistModule 𝒜R F qq)).presheaf.map
          (homOfLE (show WW ≤ (⊤ : (Proj 𝒜S).Opens) from le_top)).op
          (Scheme.Modules.Hom.app
            ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
              (twistModule 𝒜R F qq)) ⊤ m) := hUnitOpen
    rw [hUnitOpen']
    have hTe := CategoryTheory.congr_fun
      ((twistModulePolynomialPullbackHom (Fin (n + 1)) φ F qq).mapPresheaf.naturality
        (homOfLE (show WW ≤ (⊤ : (Proj 𝒜S).Opens) from le_top)).op)
      (Scheme.Modules.Hom.app
        ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
          (twistModule 𝒜R F qq)) ⊤ m)
    simp only [CategoryTheory.comp_apply] at hTe
    have hTe' : (PresheafOfModules.Hom.app
        (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F qq).val (op WW)).hom
        (((Scheme.Modules.pullback gg).obj (twistModule 𝒜R F qq)).presheaf.map
          (homOfLE (show WW ≤ (⊤ : (Proj 𝒜S).Opens) from le_top)).op
          (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
            (twistModule 𝒜R F qq)) ⊤ m))
      = (twistModule 𝒜S FS qq).presheaf.map
          (homOfLE (show WW ≤ (⊤ : (Proj 𝒜S).Opens) from le_top)).op
          (Scheme.Modules.Hom.app
            (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F qq) ⊤
            (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction gg).unit.app
              (twistModule 𝒜R F qq)) ⊤ m)) := hTe
    rw [hTe']
    congr 1
    rw [gammaStarBaseChangeApp_tmul, one_smul]
    rfl
  refine Eq.symm (Eq.trans (hA _) ?_)
  refine Eq.trans (congrArg
    (fun y ↦ (twistModule 𝒜S FS qq).presheaf.map (homOfLE hge).op y) hcore) ?_
  rw [← CategoryTheory.comp_apply, ← CategoryTheory.Functor.map_comp]
  rfl

set_option maxHeartbeats 2000000 in
/-- **The overlap stage identity on a general pure tensor.**  The two-variable analogue of
`chartStageMap_gammaStarBaseChangeApp_tmul`. -/
theorem pairStageMap_gammaStarBaseChangeApp_tmul (a : S)
    (m : Γ(twistModule 𝒜R F qq, ⊤)) :
    letI : Algebra R S := φ.toAlgebra
    letI := Scheme.Modules.openSectionsModuleOver πS (twistModule 𝒜S FS d) ES
    letI := Scheme.Modules.openSectionsModuleOver πR (twistModule 𝒜R F d) ER
    letI := Scheme.Modules.globalSectionsModule πR (twistModule 𝒜R F qq)
    letI := Scheme.Modules.globalSectionsModule πS (twistModule 𝒜S FS qq)
    Proj.pairStageMap 𝒜S πS FS (stdVars n S) i k d j
        (gammaStarBaseChangeApp n φ F qq (a ⊗ₜ[R] m))
      = (twistModule 𝒜S FS d).presheaf.map
          (homOfLE (coeffMap_preimage_basicOpen_inf n φ i k).ge).op
          (Scheme.Modules.Hom.app
            (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) WW
            (pullbackOpenSectionsBaseChangeLinearMap (CommRingCat.ofHom φ) gg πR πS
              (coeffMap_w n φ) (twistModule 𝒜R F d) ER
              (a ⊗ₜ[R] (Proj.pairStageMap 𝒜R πR F (stdVars n R) i k d j m)))) := by
  letI : Algebra R S := φ.toAlgebra
  letI := Scheme.Modules.openSectionsModuleOver πS (twistModule 𝒜S FS d) ES
  letI := Scheme.Modules.openSectionsModuleOver πR (twistModule 𝒜R F d) ER
  letI := Scheme.Modules.globalSectionsModule πR (twistModule 𝒜R F qq)
  letI := Scheme.Modules.globalSectionsModule πS (twistModule 𝒜S FS qq)
  letI := Scheme.Modules.openSectionsModule πR (twistModule 𝒜R F d) ER
  letI := Scheme.Modules.openSectionsModule πS
    ((Scheme.Modules.pullback gg).obj (twistModule 𝒜R F d)) WW
  letI := Scheme.Modules.openSectionsModule πS (twistModule 𝒜S FS d) WW
  letI := Scheme.Modules.openSectionsModule πS (twistModule 𝒜S FS d) ES
  have hge : ES ≤ WW := (coeffMap_preimage_basicOpen_inf n φ i k).ge
  have hT : ∀ (b : S) (z : Γ((Scheme.Modules.pullback gg).obj (twistModule 𝒜R F d), WW)),
      Scheme.Modules.Hom.app
          (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) WW (b • z)
        = b • Scheme.Modules.Hom.app
          (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) WW z := by
    intro b z
    exact (Scheme.Modules.openSectionsLinearMap πS
      (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) WW).map_smul b z
  have hρ : ∀ (b : S) (z : Γ(twistModule 𝒜S FS d, WW)),
      (twistModule 𝒜S FS d).presheaf.map (homOfLE hge).op (b • z)
        = b • (twistModule 𝒜S FS d).presheaf.map (homOfLE hge).op z := by
    intro b z
    exact (Scheme.Modules.openRestrictionLinearMap πS (twistModule 𝒜S FS d) hge).map_smul b z
  have ha : (a ⊗ₜ[R] m : S ⊗[R] Γ(twistModule 𝒜R F qq, ⊤)) = a • (1 ⊗ₜ[R] m) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have ha' : (a ⊗ₜ[R] (Proj.pairStageMap 𝒜R πR F (stdVars n R) i k d j m)
      : S ⊗[R] Γ(twistModule 𝒜R F d, ER))
      = a • (1 ⊗ₜ[R] (Proj.pairStageMap 𝒜R πR F (stdVars n R) i k d j m)) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [ha, ha', map_smul, map_smul, map_smul, hT, hρ,
    pairStageMap_gammaStarBaseChangeApp n φ F i d j k m]

set_option maxHeartbeats 2000000 in
/-- **The overlap square, in the colimit.**  Composing the localized base-change comparison with
the chart comparison is the same as: identify the localization of the base change with the base
change of the localization (`locBaseChangeToTensor`), apply the chart comparison over `R`, base
change the sections along the chart (`pullbackOpenSectionsBaseChangeLinearMap`), compare the
twists (`twistModulePolynomialPullbackHom`), and restrict to the chart of `ℙⁿ_S`.

Proved by `Module.DirectLimit.induction_on` and then `TensorProduct.induction_on`, with
`Proj.chartColimitMap_locMap` on the left, `GradedModule.locIncl_locBaseChangeToTensor` on the
right, and `chartStageMap_gammaStarBaseChangeApp_tmul` in the middle.

**Every map on the right-hand side is bijective**, which is what
`HasGammaStarBaseChangeCechHgrZero` needs: `GradedModule.bijective_locBaseChangeToTensor`,
`Proj.bijective_chartColimitMap`,
`Proj.ProjectiveCoverPullback.bijective_pullbackOpenSectionsBaseChange_chart`,
`ProjectiveSpectrum.Twist.twistModulePolynomialPullbackHom_isIso` (for `d : ℕ`), and the fact
that the last restriction is along an equality of opens. -/
theorem pairColimitMap_locMap_baseChange :
    letI : Algebra R S := φ.toAlgebra
    letI := Scheme.Modules.openSectionsModuleOver πS (twistModule 𝒜S FS d)
      (Proj.basicOpen 𝒜S ((stdVars n S i : MvPolynomial (Fin (n + 1)) S)))
    letI := Scheme.Modules.openSectionsModuleOver πR (twistModule 𝒜R F d) ER
    ∀ w : ((GradedModule.baseChange GR S).loc [i, k]).obj d,
      Proj.pairColimitMap 𝒜S πS FS (stdVars n S) i k d
          (((GradedModule.locMap [i, k] (gammaStarBaseChangeHom n φ F)).app d).hom w)
        = (twistModule 𝒜S FS d).presheaf.map
            (homOfLE (coeffMap_preimage_basicOpen_inf n φ i k).ge).op
            (Scheme.Modules.Hom.app
              (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) WW
              (pullbackOpenSectionsBaseChangeLinearMap (CommRingCat.ofHom φ) gg πR πS
                (coeffMap_w n φ) (twistModule 𝒜R F d) ER
                (LinearMap.baseChange S
                  (Proj.pairColimitMap 𝒜R πR F (stdVars n R) i k d)
                  ((GradedModule.locBaseChangeToTensor S GR [i, k] d).hom w)))) := by
  intro w
  letI : Algebra R S := φ.toAlgebra
  letI := Scheme.Modules.openSectionsModuleOver πS (twistModule 𝒜S FS d)
    (Proj.basicOpen 𝒜S ((stdVars n S i : MvPolynomial (Fin (n + 1)) S)))
  letI := Scheme.Modules.openSectionsModuleOver πR (twistModule 𝒜R F d) ER
  induction w using Module.DirectLimit.induction_on with
  | ih t z =>
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
      have hL := Proj.pairColimitMap_locMap 𝒜S πS FS (stdVars n S) i k
        (gammaStarBaseChangeHom n φ F) d t (a ⊗ₜ[R] m)
      have hR := congrArg (fun ψ : ((GradedModule.baseChange GR S).obj
          (GradedModule.locDeg [i, k] d t)) ⟶
          ModuleCat.of S (S ⊗[R] ((GradedModule.loc GR [i, k]).obj d)) ↦ ψ.hom (a ⊗ₜ[R] m))
        (GradedModule.locIncl_locBaseChangeToTensor S GR [i, k] d t)
      refine hL.trans (Eq.trans ?_ (congrArg
        (fun y : ModuleCat.of S (S ⊗[R] ((GradedModule.loc GR [i, k]).obj d)) ↦
          (twistModule 𝒜S FS d).presheaf.map
            (homOfLE (coeffMap_preimage_basicOpen_inf n φ i k).ge).op
            (Scheme.Modules.Hom.app
              (twistModulePolynomialPullbackHom (Fin (n + 1)) φ F d) WW
              (pullbackOpenSectionsBaseChangeLinearMap (CommRingCat.ofHom φ) gg πR πS
                (coeffMap_w n φ) (twistModule 𝒜R F d) ER
                (LinearMap.baseChange S
                  (Proj.pairColimitMap 𝒜R πR F (stdVars n R) i k d) y)))) hR).symm)
      refine (pairStageMap_gammaStarBaseChangeApp_tmul n φ F i d t k a m).trans ?_
      congr 3
      exact congrArg (fun z ↦ a ⊗ₜ[R] z)
        (Proj.pairColimitMap_of 𝒜R πR F (stdVars n R) i k d t m).symm

end AlgebraicGeometry.ProjectiveSpace
end

end
