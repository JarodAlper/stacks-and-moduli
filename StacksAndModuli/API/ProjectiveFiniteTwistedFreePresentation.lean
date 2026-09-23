module

public import StacksAndModuli.API.ProjGammaStarChartComparison
public import StacksAndModuli.API.ProjGammaStarProjectiveSpace
public import StacksAndModuli.API.ProjTwistModuleQuasicoherentOfQuasicoherent
public import StacksAndModuli.API.HilbertQuotientBridge
public import StacksAndModuli.API.AffineQuasicoherentEpi
public import StacksAndModuli.API.TwistMonomialSections
public import StacksAndModuli.«Section2.2-Grassmannian».«part2.2.2-projectivity-of-the-grassmannian»

/-!
# Finite twisted-free presentations on projective space

The first step in a finite twisted-free resolution is a relative global-generation
statement.  A finitely presented quasicoherent module on polynomial projective space has
finitely many homogeneous global sections, all in one nonnegative degree, whose normalized
restrictions generate on every standard affine chart.

The proof is elementary.  Choose finitely many generators on each of the finitely many
standard charts, lift them through the Hartshorne II.5.14 comparison
`Proj.chartColimitEquiv`, and move the finitely many representatives to a common stage of
the localization towers.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {n : ℕ}

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
local notation "X" => Proj 𝒜
local notation "π" => Proj.polynomialToSpec (Fin (n + 1)) R
local notation "x" => _root_.AlgebraicGeometry.ProjectiveSpace.stdVars n R

/-- The standard affine chart, packaged as an affine open. -/
noncomputable def polynomialStandardAffineOpen (i : Fin (n + 1)) : (Proj 𝒜).affineOpens :=
  ⟨basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R),
    isAffineOpen_basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)
      (x i).2 Nat.one_pos⟩

/-- Multiplication by `xᵢ^k` on a standard chart, as a linear equivalence over the full
coordinate ring of that chart. -/
noncomputable def polynomialChartTwistLinearEquiv
    (F : (Proj 𝒜).Modules) (i : Fin (n + 1)) (d : ℤ) (k : ℕ)
    (ec : ℤ) (hec : ec = d + (k : ℤ)) :
    Γ(twistModule 𝒜 F d,
        basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)) ≃ₗ[
      Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))]
      Γ(twistModule 𝒜 F ec,
        basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)) :=
  LinearEquiv.ofBijective
    ((twistModuleMulHom 𝒜 F
      (⟨(x i : MvPolynomial (Fin (n + 1)) R) ^ k,
        pow_var_mem 𝒜 x i k⟩ : 𝒜 k) d ec hec).val.app
      (op (basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)))).hom
    (bijective_app_twistModuleMulHom_natPow 𝒜 (x i).2 F d k
      (pow_var_mem 𝒜 x i k) ec hec _ le_rfl)

@[simp]
theorem polynomialChartTwistLinearEquiv_apply
    (F : (Proj 𝒜).Modules) (i : Fin (n + 1)) (d : ℤ) (k : ℕ)
    (ec : ℤ) (hec : ec = d + (k : ℤ))
    (v : Γ(twistModule 𝒜 F d,
      basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))) :
    polynomialChartTwistLinearEquiv F i d k ec hec v =
      Scheme.Modules.Hom.app
        (twistModuleMulHom 𝒜 F
          (⟨(x i : MvPolynomial (Fin (n + 1)) R) ^ k,
            pow_var_mem 𝒜 x i k⟩ : 𝒜 k) d ec hec)
        (basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)) v := rfl

/-- A degree-`D` global section, divided by `xᵢ^D`, as a section of the untwisted
module on the standard chart `D₊(xᵢ)`. -/
noncomputable def normalizedChartSection
    (F : (Proj 𝒜).Modules) (i : Fin (n + 1)) (D : ℕ)
    (s : (gammaStar 𝒜 π F x).obj (D : ℤ)) :
    Γ(twistModule 𝒜 F 0,
      basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)) :=
  (chartTwistLinearEquiv 𝒜 π F x i 0 D (D : ℤ) (by simp)).symm
    ((twistModule 𝒜 F (D : ℤ)).presheaf.map
      (homOfLE (le_top :
        basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) ≤ ⊤)).op s)

/-- Multiplying a normalized section back by `xᵢ^D` recovers the restriction of the
original degree-`D` global section. -/
@[simp]
theorem polynomialChartTwistLinearEquiv_normalizedChartSection
    (F : (Proj 𝒜).Modules) (i : Fin (n + 1)) (D : ℕ)
    (s : (gammaStar 𝒜 π F x).obj (D : ℤ)) :
    polynomialChartTwistLinearEquiv F i 0 D (D : ℤ) (by simp)
        (normalizedChartSection F i D s) =
      (twistModule 𝒜 F (D : ℤ)).presheaf.map
        (homOfLE (le_top :
          basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) ≤ ⊤)).op s := by
  rw [polynomialChartTwistLinearEquiv_apply, normalizedChartSection,
    ← chartTwistLinearEquiv_apply]
  exact (chartTwistLinearEquiv 𝒜 π F x i 0 D (D : ℤ) (by simp)).apply_symm_apply _

/-- If the normalized degree-`D` sections generate the untwisted module on a standard
chart, then the original sections generate the degree-`D` twist there. -/
theorem span_restrict_eq_top_of_span_normalizedChartSection_eq_top
    {I : Type v} (F : (Proj 𝒜).Modules) (i : Fin (n + 1)) (D : ℕ)
    (s : I → (gammaStar 𝒜 π F x).obj (D : ℤ))
    (h : Submodule.span
      Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
      (Set.range (fun a ↦ normalizedChartSection F i D (s a))) = ⊤) :
    Submodule.span
      Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
      (Set.range (fun a ↦
        (twistModule 𝒜 F (D : ℤ)).presheaf.map
          (homOfLE (le_top :
            basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) ≤ ⊤)).op (s a))) = ⊤ := by
  let e := polynomialChartTwistLinearEquiv F i 0 D (D : ℤ) (by simp)
  have heTop : Submodule.map e.toLinearMap ⊤ = ⊤ := by
    rw [Submodule.map_top]
    exact e.range
  have hmap := congrArg (Submodule.map e.toLinearMap) h
  rw [Submodule.map_span, heTop] at hmap
  have hrange : ⇑e.toLinearMap ''
      Set.range (fun a ↦ normalizedChartSection F i D (s a)) =
      Set.range (fun a ↦
        (twistModule 𝒜 F (D : ℤ)).presheaf.map
          (homOfLE (le_top :
            basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) ≤ ⊤)).op (s a)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a,
        (polynomialChartTwistLinearEquiv_normalizedChartSection F i D (s a)).symm⟩
    · rintro ⟨a, rfl⟩
      refine ⟨normalizedChartSection F i D (s a), ⟨a, rfl⟩, ?_⟩
      exact polynomialChartTwistLinearEquiv_normalizedChartSection F i D (s a)
  rw [hrange] at hmap
  exact hmap

set_option synthInstance.maxHeartbeats 1000000 in
-- The nested polynomial grading, twist, and open-section module structures make instance
-- synthesis for the statement substantially more expensive than the default budget.
/-- If the degree-zero twist of a quasicoherent module has finite sections on every
standard chart, then finitely many homogeneous global sections in one common degree,
beyond any prescribed bound, have normalized restrictions generating on every chart. -/
theorem exists_commonDegree_normalizedChart_generators_ge_of_finite_chart_sections
    (F : (Proj 𝒜).Modules) [F.IsQuasicoherent] (B : ℕ)
    (hfinite : ∀ i : Fin (n + 1),
      Module.Finite
        Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
        Γ(twistModule 𝒜 F 0,
          basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))) :
    ∃ (m : Fin (n + 1) → ℕ) (D : ℕ)
      (s : (Σ i, Fin (m i)) → (gammaStar 𝒜 π F x).obj (D : ℤ)),
      B ≤ D ∧ ∀ i : Fin (n + 1),
        Submodule.span
          Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
          (Set.range (fun a ↦ normalizedChartSection F i D (s a))) = ⊤ := by
  classical
  haveI htwistqc : ∀ e : ℤ, (twistModule 𝒜 F e).IsQuasicoherent :=
    fun e ↦ twistModule_std_isQuasicoherent_of_isQuasicoherent n F e
  choose m g hg using fun i : Fin (n + 1) ↦
    @Module.Finite.exists_fin
      Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
      Γ(twistModule 𝒜 F 0,
        basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
      _ _ _ (hfinite i)
  let G := gammaStar 𝒜 π F x
  have hcover : (⊤ : (Proj 𝒜).Opens) ≤
      ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : MvPolynomial (Fin (n + 1)) R)) :=
    ProjectiveSpace.top_le_iSup_basicOpen_stdVars n R
  let J := Σ i, Fin (m i)
  have hlift : ∀ a : J,
      ∃ (j : ℕ) (z : G.obj (ProjectiveSpace.GradedModule.locDeg [a.1] 0 j)),
        chartStageMap 𝒜 π F x a.1 0 j z = g a.1 a.2 := by
    intro a
    let e := chartColimitEquiv 𝒜 π F x a.1 hcover 0
    let w : (G.loc [a.1]).obj 0 := e.symm (g a.1 a.2)
    obtain ⟨j, z, hz⟩ := ProjectiveSpace.GradedModule.locIncl_exists
      (M := G) (l := [a.1]) 0 w
    refine ⟨j, z, ?_⟩
    have hw : chartColimitMap 𝒜 π F x a.1 0 w = g a.1 a.2 :=
      e.apply_symm_apply (g a.1 a.2)
    rw [← hz] at hw
    have hof : chartColimitMap 𝒜 π F x a.1 0
        ((G.locIncl [a.1] 0 j).hom z) =
        chartStageMap 𝒜 π F x a.1 0 j z :=
      chartColimitMap_of 𝒜 π F x a.1 0 j z
    rw [hof] at hw
    exact hw
  choose stage z hz using hlift
  let D : ℕ := max B (Finset.univ.sup stage)
  have hB : B ≤ D := le_max_left _ _
  have hstage (a : J) : stage a ≤ D := by
    exact (Finset.le_sup (f := stage) (Finset.mem_univ a)).trans (le_max_right _ _)
  let zD (a : J) : G.obj (ProjectiveSpace.GradedModule.locDeg [a.1] 0 D) :=
    (G.locTr [a.1] 0 (stage a) D (hstage a)).hom (z a)
  have hzD (a : J) :
      chartStageMap 𝒜 π F x a.1 0 D (zD a) = g a.1 a.2 := by
    exact (chartStageMap_locTr 𝒜 π F x a.1 0
      (stage a) D (hstage a) (z a)).trans (hz a)
  have hdeg (i : Fin (n + 1)) :
      ProjectiveSpace.GradedModule.locDeg [i] 0 D = (D : ℤ) := by
    rw [locDeg_singleton]
    simp
  let s (a : J) : G.obj (D : ℤ) :=
    (eqToHom (congrArg G.obj (hdeg a.1))).hom (zD a)
  refine ⟨m, D, s, hB, fun i ↦ ?_⟩
  apply top_unique
  rw [← hg i]
  apply Submodule.span_mono
  rintro _ ⟨j, rfl⟩
  refine ⟨⟨i, j⟩, ?_⟩
  have h := hzD ⟨i, j⟩
  rw [chartStageMap_apply] at h
  change normalizedChartSection F i D
      ((eqToHom (congrArg G.obj (hdeg i))).hom (zD ⟨i, j⟩)) = g i j
  have htransport (e : ℤ) (he : e = (D : ℤ))
      (hec : e = 0 + (D : ℤ)) (v : G.obj e) :
      normalizedChartSection F i D
          ((eqToHom (congrArg G.obj he)).hom v) =
        (chartTwistLinearEquiv 𝒜 π F x i 0 D e hec).symm
          ((twistModule 𝒜 F e).presheaf.map
            (homOfLE (le_top :
              basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) ≤ ⊤)).op v) := by
    subst e
    rfl
  exact (htransport
    (ProjectiveSpace.GradedModule.locDeg [i] 0 D) (hdeg i)
    (locDeg_singleton i 0 D) (zD ⟨i, j⟩)).trans h

set_option synthInstance.maxHeartbeats 1000000 in
-- The nested polynomial grading, twist, and open-section module structures make instance
-- synthesis for the statement substantially more expensive than the default budget.
/-- A finitely presented module on polynomial projective space has finitely many
homogeneous global sections in one common degree, beyond any prescribed bound, whose
normalized restrictions generate on every standard affine chart. -/
theorem exists_commonDegree_normalizedChart_generators_ge
    (F : (Proj 𝒜).Modules) [F.IsFinitePresentation] (B : ℕ) :
    ∃ (m : Fin (n + 1) → ℕ) (D : ℕ)
      (s : (Σ i, Fin (m i)) → (gammaStar 𝒜 π F x).obj (D : ℤ)),
      B ≤ D ∧ ∀ i : Fin (n + 1),
        Submodule.span
          Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
          (Set.range (fun a ↦ normalizedChartSection F i D (s a))) = ⊤ := by
  classical
  haveI hFqc : F.IsQuasicoherent := inferInstance
  have hcoordinateCover :
      (⨆ k : ULift.{u} (Fin (n + 1)),
        basicOpen 𝒜 (MvPolynomial.X k.down)) = ⊤ := by
    rw [iSup_ulift]
    exact iSup_basicOpen_X_eq_top R n
  haveI htwistfp0 : (twistModule 𝒜 F 0).IsFinitePresentation :=
    twistModule_isFinitePresentation 𝒜
      (fun k : ULift.{u} (Fin (n + 1)) ↦ MvPolynomial.X k.down)
      (fun k ↦ X_mem_homogeneousSubmodule R n k.down)
      hcoordinateCover F 0
  have hfinite : ∀ i : Fin (n + 1),
      Module.Finite
        Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
        Γ(twistModule 𝒜 F 0,
          basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)) := by
    intro i
    have hfp : Module.FinitePresentation
        Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
        Γ(twistModule 𝒜 F 0,
          basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)) := by
      exact (Scheme.Modules.isFinitePresentation_iff_sections_affineOpens
        (twistModule 𝒜 F 0)).mp inferInstance
        (polynomialStandardAffineOpen (R := R) (n := n) i)
    letI := hfp
    infer_instance
  exact exists_commonDegree_normalizedChart_generators_ge_of_finite_chart_sections
    F B hfinite

set_option synthInstance.maxHeartbeats 1000000 in
-- The nested polynomial grading, twist, and open-section module structures make instance
-- synthesis for the statement substantially more expensive than the default budget.
/-- A finitely presented module on polynomial projective space has finitely many
homogeneous global sections in one common nonnegative degree whose normalized restrictions
generate on every standard affine chart. -/
theorem exists_commonDegree_normalizedChart_generators
    (F : (Proj 𝒜).Modules) [F.IsFinitePresentation] :
    ∃ (m : Fin (n + 1) → ℕ) (D : ℕ)
      (s : (Σ i, Fin (m i)) → (gammaStar 𝒜 π F x).obj (D : ℤ)),
      ∀ i : Fin (n + 1),
        Submodule.span
          Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
          (Set.range (fun a ↦ normalizedChartSection F i D (s a))) = ⊤ := by
  obtain ⟨m, D, s, _, hs⟩ := exists_commonDegree_normalizedChart_generators_ge F 0
  exact ⟨m, D, s, hs⟩

set_option synthInstance.maxHeartbeats 1000000 in
-- The explicit polynomial twist instances make typeclass synthesis for the statement slow.
/-- A finitely presented module on polynomial projective space has finitely many global
sections in a twist beyond any prescribed bound which generate on every standard chart. -/
theorem exists_commonDegree_chart_generators_ge
    (F : (Proj 𝒜).Modules) [F.IsFinitePresentation] (B : ℕ) :
    ∃ (m : Fin (n + 1) → ℕ) (D : ℕ)
      (s : (Σ i, Fin (m i)) → (gammaStar 𝒜 π F x).obj (D : ℤ)),
      B ≤ D ∧ ∀ i : Fin (n + 1),
        Submodule.span
          Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
          (Set.range (fun a ↦
            (twistModule 𝒜 F (D : ℤ)).presheaf.map
              (homOfLE (le_top :
                basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) ≤ ⊤)).op (s a))) = ⊤ := by
  obtain ⟨m, D, s, hD, hs⟩ := exists_commonDegree_normalizedChart_generators_ge F B
  refine ⟨m, D, s, hD, fun i ↦ ?_⟩
  exact span_restrict_eq_top_of_span_normalizedChartSection_eq_top F i D s (hs i)

set_option synthInstance.maxHeartbeats 1000000 in
-- The explicit polynomial twist instances make typeclass synthesis for the statement slow.
/-- A finitely presented module on polynomial projective space has finitely many global
sections of one twist which generate on every standard chart. -/
theorem exists_commonDegree_chart_generators
    (F : (Proj 𝒜).Modules) [F.IsFinitePresentation] :
    ∃ (m : Fin (n + 1) → ℕ) (D : ℕ)
      (s : (Σ i, Fin (m i)) → (gammaStar 𝒜 π F x).obj (D : ℤ)),
      ∀ i : Fin (n + 1),
        Submodule.span
          Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
          (Set.range (fun a ↦
            (twistModule 𝒜 F (D : ℤ)).presheaf.map
              (homOfLE (le_top :
                basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) ≤ ⊤)).op (s a))) = ⊤ := by
  obtain ⟨m, D, s, _, hs⟩ := exists_commonDegree_chart_generators_ge F 0
  exact ⟨m, D, s, hs⟩

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
-- Constructing the dependent free map over explicit polynomial `Proj` is elaboration- and
-- instance-heavy.
/-- Beyond any prescribed degree, a finitely presented module on polynomial projective
space becomes a quotient of a finite free sheaf after twisting. -/
theorem exists_epi_freeHomOfSections_to_twistModule_ge
    (F : (Proj 𝒜).Modules) [F.IsFinitePresentation] (B : ℕ) :
    ∃ (m : Fin (n + 1) → ℕ) (D : ℕ)
      (s : (Σ i, Fin (m i)) → (gammaStar 𝒜 π F x).obj (D : ℤ)),
      B ≤ D ∧ Epi (Scheme.Modules.freeHomOfSections
        (I := ULift.{u} (Σ i, Fin (m i))) (M := twistModule 𝒜 F (D : ℤ))
        (fun a ↦ s a.down)) := by
  classical
  haveI hFqc : F.IsQuasicoherent := inferInstance
  obtain ⟨m, D, s, hD, hs⟩ := exists_commonDegree_chart_generators_ge F B
  haveI htwistqc : (twistModule 𝒜 F (D : ℤ)).IsQuasicoherent :=
    twistModule_std_isQuasicoherent_of_isQuasicoherent n F (D : ℤ)
  let J := Σ i, Fin (m i)
  let sU : ULift.{u} J → (gammaStar 𝒜 π F x).obj (D : ℤ) := fun a ↦ s a.down
  have hsU (i : Fin (n + 1)) :
      Submodule.span
        Γ(X, basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R))
        (Set.range (fun a ↦
          (twistModule 𝒜 F (D : ℤ)).presheaf.map
            (homOfLE (le_top :
              basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) ≤ ⊤)).op (sU a))) = ⊤ := by
    have hrange : Set.range (fun a : ULift.{u} J ↦
        (twistModule 𝒜 F (D : ℤ)).presheaf.map
          (homOfLE (le_top :
            basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) ≤ ⊤)).op (sU a)) =
      Set.range (fun a : J ↦
        (twistModule 𝒜 F (D : ℤ)).presheaf.map
          (homOfLE (le_top :
            basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) ≤ ⊤)).op (s a)) := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a.down, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨ULift.up a, rfl⟩
    rw [hrange]
    exact hs i
  refine ⟨m, D, s, hD, ?_⟩
  change Epi (Scheme.Modules.freeHomOfSections
    (I := ULift.{u} J) (M := twistModule 𝒜 F (D : ℤ)) sU)
  apply Scheme.Modules.epi_of_openCover_restrict
    (Scheme.Modules.freeHomOfSections
      (I := ULift.{u} J) (M := twistModule 𝒜 F (D : ℤ)) sU)
    (Scheme.Cover.ulift
      (Proj.polynomialAffineOpenCover (Fin (n + 1)) R).openCover)
  intro z
  let 𝒰₀ := (Proj.polynomialAffineOpenCover (Fin (n + 1)) R).openCover
  let i : Fin (n + 1) := 𝒰₀.idx z
  change Epi ((Scheme.Modules.restrictFunctor (𝒰₀.f i)).map
    (Scheme.Modules.freeHomOfSections
      (I := ULift.{u} J) (M := twistModule 𝒜 F (D : ℤ)) sU))
  apply Scheme.Modules.epi_restrictFunctor_map_of_app_image_top_surjective
  have hsurj := Scheme.Modules.surjective_app_freeHomOfSections_of_span sU
    (basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)) (hsU i)
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
      (basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) : Set X)
    calc
      Set.range (𝒰₀.f i).base = Set.range
          (Proj.awayι 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)
            (MvPolynomial.isHomogeneous_X R i) Nat.one_pos).base :=
        congrArg (fun g ↦ Set.range g.base) hf
      _ = ((Proj.awayι 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)
          (MvPolynomial.isHomogeneous_X R i) Nat.one_pos).opensRange : Set X) := rfl
      _ = (basicOpen 𝒜 (x i : MvPolynomial (Fin (n + 1)) R) : Set X) :=
        congrArg (fun U : (Proj 𝒜).Opens ↦ (U : Set X))
          (Proj.opensRange_awayι 𝒜 (x i : MvPolynomial (Fin (n + 1)) R)
            (MvPolynomial.isHomogeneous_X R i) Nat.one_pos)
  exact Scheme.Modules.surjective_app_of_eq
    (Scheme.Modules.freeHomOfSections
      (I := ULift.{u} J) (M := twistModule 𝒜 F (D : ℤ)) sU)
    hopen hsurj

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 1000000 in
-- Constructing the dependent free map over explicit polynomial `Proj` is elaboration- and
-- instance-heavy.
/-- A finitely presented module on polynomial projective space becomes a quotient of a
finite free sheaf after one nonnegative twist. -/
theorem exists_epi_freeHomOfSections_to_twistModule
    (F : (Proj 𝒜).Modules) [F.IsFinitePresentation] :
    ∃ (m : Fin (n + 1) → ℕ) (D : ℕ)
      (s : (Σ i, Fin (m i)) → (gammaStar 𝒜 π F x).obj (D : ℤ)),
      Epi (Scheme.Modules.freeHomOfSections
        (I := ULift.{u} (Σ i, Fin (m i))) (M := twistModule 𝒜 F (D : ℤ))
        (fun a ↦ s a.down)) := by
  obtain ⟨m, D, s, _, hs⟩ := exists_epi_freeHomOfSections_to_twistModule_ge F 0
  exact ⟨m, D, s, hs⟩

end AlgebraicGeometry.Proj

end

end
