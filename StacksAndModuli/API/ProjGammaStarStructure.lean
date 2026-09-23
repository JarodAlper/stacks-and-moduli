module

public import StacksAndModuli.API.ProjGammaStar
public import StacksAndModuli.API.ProjGammaStarProjectiveSpace
public import StacksAndModuli.API.ProjectiveTwistHomogeneousSection
public import StacksAndModuli.API.ProjectiveSpaceOverSpecComparison
public import StacksAndModuli.API.SchemeModulesTensorUnitNaturality
public import StacksAndModuli.API.ProjectiveTwistNegativeGlobalSections

/-!
# The comparison `S ⟶ Γ_*(𝒪)` on `ℙⁿ_k`

Hartshorne II.5.13 identifies the polynomial ring `S = k[x₀, …, xₙ]`, as a graded module,
with `Γ_*(𝒪_{ℙⁿ})`.  This file builds the comparison morphism; that it is an isomorphism is
a separate statement, reduced by `AlgebraicGeometry.Proj.bijective_locMap_app_iff_bijective_comp`
and `AlgebraicGeometry.Proj.chartColimitMap_locMap` to a computation at one stage of the
localization tower.

Two mismatches have to be absorbed, and each is isolated in its own lemma so that no
`eqToHom` transport of a section is ever formed (see the root INSIGHTS on
`motive is not type correct`):

* the source `GradedModule.polySubmodule k n d` is `homogeneousSubmodule … d.toNat` only
  after a case split on `0 ≤ d`, and the natural degree index produced by multiplying by a
  variable is `d.toNat + 1` rather than `(d + 1).toNat`.  The first is handled by
  `polySubmoduleEquivNonneg`, the second by
  `ProjectiveSpectrum.Twist.homogeneousSection'_congr`, which says the section depends only
  on the underlying form;
* the target is `Γ(𝒪 ⊗ 𝒪(d), ⊤)`, not `Γ(𝒪(d), ⊤)`, since `twistModule 𝒜 F d` tensors.  The
  identification and its compatibility with the degree-raising maps is
  `Scheme.Modules.tensorLeftUnitIso_inv_naturality`.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.polySubmoduleEquivNonneg`;
* `AlgebraicGeometry.ProjectiveSpace.coeff_smul_homogeneousSection'`, `k`-linearity of
  `p ↦ p / 1` for the intrinsic action coming from the structure morphism;
* `AlgebraicGeometry.ProjectiveSpace.polyToTwistSections`, the degreewise comparison into
  `Γ(𝒪(d), ⊤)`;
* `AlgebraicGeometry.ProjectiveSpace.mulSectionHom_polyToTwistSections`, its compatibility
  with multiplication by `xᵢ`;
* `AlgebraicGeometry.ProjectiveSpace.structureToGammaStar`, the morphism of graded modules.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [CommRing k] (n : ℕ)

/-- The structure morphism of `ℙⁿ_k = Proj k[x₀, …, xₙ]`. -/
noncomputable abbrev projπ : Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) ⟶
    Spec (CommRingCat.of k) := Proj.polynomialToSpec (Fin (n + 1)) k

section PolySubmoduleComparison

variable {k n}

/-- In nonnegative degrees the graded piece of `S` used by `GradedModule.structureModule` is
the space of homogeneous forms. -/
noncomputable def polySubmoduleEquivNonneg {d : ℤ} (h : 0 ≤ d) :
    GradedModule.polySubmodule k n d ≃ₗ[k]
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k d.toNat :=
  LinearEquiv.ofEq _ _ (GradedModule.polySubmodule_of_nonneg k n h)

@[simp] theorem polySubmoduleEquivNonneg_coe {d : ℤ} (h : 0 ≤ d)
    (p : GradedModule.polySubmodule k n d) :
    ((polySubmoduleEquivNonneg h p : MvPolynomial (Fin (n + 1)) k)) = (p : _) := rfl

end PolySubmoduleComparison

open ProjectiveSpectrum.Twist in
/-- **The coefficient action on `p / 1` is the action on `p`.**  The `k`-module structure on
global sections is restriction of scalars along the structure morphism, which by
`projectiveSpaceScalarRingHom_eq_baseRingHom` is multiplication by the constant form `C c`. -/
theorem coeff_smul_homogeneousSection' {d : ℤ} {m : ℕ} (he : d = (m : ℤ)) (c : k)
    (q : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k m) :
    letI := Scheme.Modules.globalSectionsModule (projπ k n)
      (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) d)
    homogeneousSection' (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (c • q) d he ⊤
      = c • homogeneousSection' (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) q d he ⊤ := by
  letI := Scheme.Modules.globalSectionsModule (projπ k n)
    (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) d)
  change _ = (Scheme.Modules.baseRingHom (projπ k n)).hom c •
    (homogeneousSection' (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) q d he ⊤ :
      Γ(twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) d, ⊤))
  rw [← projectiveSpaceScalarRingHom_eq_baseRingHom n k]
  rw [MvPolynomial.projectiveSpaceScalarRingHom_apply]
  rw [degreeZeroSection_smul_homogeneousSection']
  congr 1
  exact Subtype.ext (MvPolynomial.smul_eq_C_mul _ c)

open ProjectiveSpectrum.Twist in
/-- **The degree-`e` component of `S ⟶ Γ_*(𝒪)`, before the unit-tensor identification.**  A
form of degree `e ≥ 0` becomes the global section `p / 1` of `𝒪(e')`; in negative degrees the
source is `⊥` and the map is zero.

The *target* degree `e'` is a separate parameter, supplied with an equation `e' = e`, so that
a section is never transported across a degree equality; this is what lets the same
construction serve the twisted comparison, where the source index is `d + a` and the target
index is `a + d`.

The case split is made *at the level of linear maps*, not inside the function, so that
linearity is proved once. -/
noncomputable def polyToTwistSections (e e' : ℤ) (he : e' = e) :
    letI := Scheme.Modules.globalSectionsModule (projπ k n)
      (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) e')
    GradedModule.polySubmodule k n e →ₗ[k]
      Γ(twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) e', ⊤) := by
  letI := Scheme.Modules.globalSectionsModule (projπ k n)
    (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) e')
  classical
  exact if h : 0 ≤ e then
    { toFun := fun p ↦ homogeneousSection' (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
        (polySubmoduleEquivNonneg h p) e' (by omega) ⊤
      map_add' := fun p q ↦ by
        rw [map_add]
        exact homogeneousSection'_add _ _ _ _ _ _
      map_smul' := fun c p ↦ by
        rw [map_smul]
        exact coeff_smul_homogeneousSection' k n _ c _ }
  else 0

open ProjectiveSpectrum.Twist in
@[simp] theorem polyToTwistSections_of_nonneg {e e' : ℤ} (he : e' = e) (h : 0 ≤ e)
    (p : GradedModule.polySubmodule k n e) :
    polyToTwistSections k n e e' he p =
      homogeneousSection' (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
        (polySubmoduleEquivNonneg h p) e' (by omega) ⊤ := by
  simp only [polyToTwistSections, h, ↓reduceDIte]
  rfl

theorem polyToTwistSections_of_neg {e e' : ℤ} (he : e' = e) (h : e < 0)
    (p : GradedModule.polySubmodule k n e) :
    polyToTwistSections k n e e' he p = 0 := by
  simp only [polyToTwistSections, Int.not_le.mpr h, ↓reduceDIte]
  rfl

open ProjectiveSpectrum.Twist in
/-- **The degreewise comparison commutes with multiplication by `xᵢ`.**  In nonnegative
degrees this is `mulSectionHom_homogeneousSection'` together with
`homogeneousSection'_congr`, which absorbs the mismatch between the degree indices
`e.toNat + 1` and `(e + 1).toNat`; in negative degrees the source is `⊥`.

The degree-`(e+1)` form is taken as a *parameter* `q` constrained only by its underlying
polynomial, so that an `eqToHom` coming from a twist (`GradedModule.mulX'`) never has to be
computed. -/
theorem mulSectionHom_polyToTwistSections (i : Fin (n + 1)) (e e' g g' : ℤ) (he : e' = e)
    (hg : g = e + 1) (hg' : g' = e' + 1) (p : GradedModule.polySubmodule k n e)
    (q : GradedModule.polySubmodule k n g)
    (hq : (q : MvPolynomial (Fin (n + 1)) k)
      = MvPolynomial.X i * (p : MvPolynomial (Fin (n + 1)) k)) :
    mulSectionHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (stdVars n k i) e' g'
        (by push_cast; omega) (op ⊤) (polyToTwistSections k n e e' he p)
      = polyToTwistSections k n g g' (by omega) q := by
  rcases lt_or_ge e 0 with h | h
  · have hp : p = 0 :=
      Subtype.ext ((Submodule.eq_bot_iff _).mp (GradedModule.polySubmodule_of_neg k n h) _ p.2)
    have hq0 : q = 0 := Subtype.ext (by rw [hq, hp]; simp)
    rw [hp, hq0, map_zero, map_zero]
    rw [← mulHom_val_app_apply]
    exact map_zero _
  · rw [polyToTwistSections_of_nonneg k n he h, polyToTwistSections_of_nonneg k n _ (by omega)]
    rw [mulSectionHom_homogeneousSection' (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
      (polySubmoduleEquivNonneg h p) (stdVars n k i) e' g' (by omega) (by push_cast; omega)
      (by push_cast; omega) (op ⊤)]
    refine homogeneousSection'_congr _ _ _ ?_ _ _ _ _
    change (p : MvPolynomial (Fin (n + 1)) k) * MvPolynomial.X i
      = (q : MvPolynomial (Fin (n + 1)) k)
    rw [hq, mul_comm]

open ProjectiveSpectrum.Twist in
/-- **The comparison morphism of Hartshorne II.5.13.**  The polynomial ring, as a graded
module, maps to `Γ_*(𝒪_{ℙⁿ_k})`: a homogeneous form `p` of degree `d ≥ 0` goes to the global
section `p / 1` of `𝒪(d)`, and negative degrees go to zero.

That this is an isomorphism is not proved here; by
`Proj.bijective_locMap_app_iff_bijective_comp` it reduces to a computation of
`Proj.chartStageMap` on `homogeneousSection'`. -/
noncomputable def structureToGammaStar :
    GradedModule.structureModule k n ⟶
      Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (projπ k n)
        (SheafOfModules.unit (Proj (MvPolynomial.homogeneousSubmodule
          (Fin (n + 1)) k)).ringCatSheaf) (stdVars n k) :=
  letI (d : ℤ) : Module (CommRingCat.of k)
      Γ(twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
        (SheafOfModules.unit _) d, ⊤) :=
    Scheme.Modules.globalSectionsModule (projπ k n)
      (twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
        (SheafOfModules.unit _) d)
  letI (d : ℤ) : Module (CommRingCat.of k)
      Γ(twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) d, ⊤) :=
    Scheme.Modules.globalSectionsModule (projπ k n)
      (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) d)
  { app := fun d ↦ ModuleCat.ofHom
      ((Scheme.Modules.globalSectionsLinearMap (projπ k n)
        (Scheme.Modules.tensorLeftUnitIso
          (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) d)).inv).comp
        (polyToTwistSections k n d d rfl))
    comm := fun i d ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun p ↦ ?_)
      have hnat := Scheme.Modules.tensorLeftUnitIso_inv_naturality
        (mulHom (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (stdVars n k i) d (d + 1)
          (by norm_num))
      have happ := congrArg
        (fun ψ : twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) d ⟶
            twistModule (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
              (SheafOfModules.unit _) (d + 1) ↦
          (PresheafOfModules.Hom.app ψ.val (op ⊤)).hom (polyToTwistSections k n d d rfl p)) hnat
      refine happ.trans ?_
      exact congrArg (fun s : Γ(twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)
          (d + 1), ⊤) ↦
        (PresheafOfModules.Hom.app (Scheme.Modules.tensorLeftUnitIso
          (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (d + 1))).inv.val
            (op ⊤)).hom s) (mulSectionHom_polyToTwistSections k n i d d (d + 1) (d + 1) rfl rfl rfl p
          (GradedModule.polyMulX k n i d p) rfl) }

open ProjectiveSpectrum.Twist in
/-- The value of the comparison: the section `p / 1`, pushed across `𝒪(d) ≅ 𝒪 ⊗ 𝒪(d)`. -/
theorem structureToGammaStar_app_apply (d : ℤ)
    (p : (GradedModule.structureModule k n).obj d) :
    ((structureToGammaStar k n).app d).hom p
      = (PresheafOfModules.Hom.app (Scheme.Modules.tensorLeftUnitIso
          (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) d)).inv.val (op ⊤)).hom
        (polyToTwistSections k n d d rfl p) := rfl

open ProjectiveSpectrum.Twist in
/-- **The degreewise comparison is bijective**, for `0 < n`.  In nonnegative degrees this is
`Γ(ℙⁿ, 𝒪(d)) = S_d` (`bijective_homogeneousSection'`); in negative degrees both sides vanish,
the source because `polySubmodule` is `⊥` and the target by
`globalSection_twist_eq_zero_of_neg` — which is where `0 < n` is used. -/
theorem bijective_polyToTwistSections (hn : 0 < n) (e e' : ℤ) (he : e' = e) :
    letI := Scheme.Modules.globalSectionsModule (projπ k n)
      (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) e')
    Function.Bijective (polyToTwistSections k n e e' he) := by
  letI := Scheme.Modules.globalSectionsModule (projπ k n)
    (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) e')
  rcases lt_or_ge e 0 with h | h
  · have hbot := GradedModule.polySubmodule_of_neg k n h
    refine ⟨fun p q _ ↦ Subtype.ext (((Submodule.eq_bot_iff _).mp hbot _ p.2).trans
        ((Submodule.eq_bot_iff _).mp hbot _ q.2).symm), fun t ↦ ⟨0, ?_⟩⟩
    exact (polyToTwistSections k n e e' he).map_zero.trans
      (globalSection_twist_eq_zero_of_neg n k hn (by omega) t).symm
  · have heq : (polyToTwistSections k n e e' he : _ → _) =
        (fun q : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k e.toNat ↦
          homogeneousSection' (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) q e'
            (by omega) ⊤) ∘ (polySubmoduleEquivNonneg h) :=
      funext fun p ↦ polyToTwistSections_of_nonneg k n he h p
    rw [heq]
    exact (bijective_homogeneousSection' n k e.toNat e' (by omega)).comp
      (polySubmoduleEquivNonneg h).bijective

open ProjectiveSpectrum.Twist in
/-- The comparison of Hartshorne II.5.13 is bijective in every degree, for `0 < n`. -/
theorem bijective_structureToGammaStar_app (hn : 0 < n) (d : ℤ) :
    Function.Bijective (((structureToGammaStar k n).app d).hom) := by
  have hu := Scheme.Modules.bijective_app_of_iso
    (Scheme.Modules.tensorLeftUnitIso
      (twist (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) d)).symm (op ⊤)
  exact hu.comp (bijective_polyToTwistSections k n hn d d rfl)

/-- **Hartshorne II.5.13.**  On `ℙⁿ_k` with `n ≥ 1`, the polynomial ring is `Γ_*(𝒪)`:

`S = k[x₀, …, xₙ] ≅ Γ_*(𝒪_{ℙⁿ_k})`

as graded modules.  The hypothesis `0 < n` is necessary: on `ℙ⁰` all twists of the structure
sheaf are trivial, so `Γ_*(𝒪)` is `k` in every degree while `S` vanishes in negative ones. -/
noncomputable def structureIsoGammaStar (hn : 0 < n) :
    GradedModule.structureModule k n ≅
      Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (projπ k n)
        (SheafOfModules.unit (Proj (MvPolynomial.homogeneousSubmodule
          (Fin (n + 1)) k)).ringCatSheaf) (stdVars n k) :=
  GradedModule.isoOfBijective (structureToGammaStar k n)
    (bijective_structureToGammaStar_app k n hn)

end AlgebraicGeometry.ProjectiveSpace

end

end
