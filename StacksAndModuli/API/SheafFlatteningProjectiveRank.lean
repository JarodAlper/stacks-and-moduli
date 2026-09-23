module

public import StacksAndModuli.API.SheafFlattening
public import StacksAndModuli.API.HilbertQuotientBridge
public import StacksAndModuli.API.ProjectiveTwistBaseChange

/-!
# The sheaf flattening functor as a vector-bundle condition

The general-base flattening functor in `API/SheafFlattening.lean` is defined by local
factorization through affine module-theoretic strata.  For a finitely presented
quasicoherent sheaf this file identifies that chartwise definition with the intrinsic
condition that the pulled-back sheaf be finite locally free of the prescribed rank.

This comparison is useful when a geometric condition (such as projective flattening in
relative dimension zero) is naturally expressed in terms of vector bundles, while the
finite-intersection representability API is phrased using `flatRankFunctorOver`.

Main declaration:

* `AlgebraicGeometry.Scheme.Modules.locallyFactors_affineStratum_iff_isProjectiveOfRank`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]

/-- The module of global sections of an affine pullback satisfying the chartwise
flat-rank condition is finite projective of the prescribed rank.  Finite presentation
is used exactly once, to turn flatness into projectivity. -/
theorem sections_top_finite_projective_rank_of_affineFlatRank
    (hfp : E.IsFinitePresentation) (r : ℕ) (U : X.affineOpens)
    {Z : Scheme.{u}} [IsAffine Z] (psi : Z ⟶ U.1.toScheme)
    (h : AffineFlatRank E r U psi) :
    let M := (pullback (psi ≫ U.1.ι)).obj E
    Module.Finite Γ(Z, ⊤) Γ(M, ⊤) ∧
      Module.Projective Γ(Z, ⊤) Γ(M, ⊤) ∧
      ∀ p : PrimeSpectrum Γ(Z, ⊤), Module.rankAtStalk Γ(M, ⊤) p = r := by
  haveI : IsAffine U.1.toScheme := U.2
  let M := (pullback (psi ≫ U.1.ι)).obj E
  have hfpM : M.IsFinitePresentation :=
    isFinitePresentation_pullback_of_isFinitePresentation _ hfp
  letI : M.IsFinitePresentation := hfpM
  have hfpTop : Module.FinitePresentation Γ(Z, ⊤) Γ(M, ⊤) :=
    (Scheme.Modules.isFinitePresentation_iff_sections_affineOpens M).mp hfpM
      ⟨⊤, isAffineOpen_top Z⟩
  letI : Module.FinitePresentation Γ(Z, ⊤) Γ(M, ⊤) := hfpTop
  letI : Algebra Γ(U.1.toScheme, ⊤) Γ(Z, ⊤) := psi.appTop.hom.toAlgebra
  let e := affineOpenTensorEquiv E U psi
  letI : Module.Flat Γ(Z, ⊤)
      (Γ(Z, ⊤) ⊗[Γ(U.1.toScheme, ⊤)] Γ((pullback U.1.ι).obj E, ⊤)) := h.1
  have hflat : Module.Flat Γ(Z, ⊤) Γ(M, ⊤) :=
    Module.Flat.of_linearEquiv e.symm
  letI : Module.Flat Γ(Z, ⊤) Γ(M, ⊤) := hflat
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation,
    fun p ↦ (congrFun (Module.rankAtStalk_eq_of_equiv e) p).symm.trans (h.2 p)⟩

/-- An affine flat-rank condition gives a vector bundle of the same rank on the affine
test scheme. -/
theorem isProjectiveOfRank_pullback_of_affineFlatRank
    (hfp : E.IsFinitePresentation) (r : ℕ) (U : X.affineOpens)
    {Z : Scheme.{u}} [IsAffine Z] (psi : Z ⟶ U.1.toScheme)
    (h : AffineFlatRank E r U psi) :
    IsProjectiveOfRank r ((pullback (psi ≫ U.1.ι)).obj E) := by
  obtain ⟨hfin, hproj, hrank⟩ :=
    sections_top_finite_projective_rank_of_affineFlatRank E hfp r U psi h
  exact isProjectiveOfRank_of_top hfin hproj hrank

/-- Local factorization through the general-base flattening strata makes the pulled-back
finitely presented sheaf a vector bundle of the prescribed rank. -/
theorem isProjectiveOfRank_pullback_of_locallyFactors
    (hfp : E.IsFinitePresentation) (r : ℕ) (T : Over X)
    (hT : Scheme.LocallyFactors (affineStratum E r) T) :
    IsProjectiveOfRank r ((pullback T.hom).obj E) := by
  let N := (pullback T.hom).obj E
  intro t
  obtain ⟨V, k, hk, ht, U, a, ha⟩ := hT t
  obtain ⟨v, hv⟩ := ht
  letI : IsOpenImmersion k.left := hk
  obtain ⟨R₁, c, hc, hvc, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset
      (X := V.left) (x := v) (U := ⊤) trivial
  letI : IsOpenImmersion c := hc
  obtain ⟨v₁, hv₁⟩ := hvc
  obtain ⟨R, b, hb, hvb, hafr⟩ :=
    exists_affineFlatRank_of_toAffineStratum E r U (c ≫ a) v₁
  letI : IsOpenImmersion b := hb
  haveI : IsAffine U.1.toScheme := U.2
  let psi : Spec R ⟶ U.1.toScheme :=
    b ≫ (c ≫ a) ≫
      (Module.flatRankRepresentative Γ(U.1.toScheme, ⊤)
        Γ((pullback U.1.ι).obj E, ⊤) r).hom ≫ U.1.toScheme.isoSpec.inv
  let j : Spec R ⟶ T.left := (b ≫ c) ≫ k.left
  haveI : IsOpenImmersion j := inferInstance
  have hpsi : j ≫ T.hom = psi ≫ U.1.ι := by
    change ((b ≫ c) ≫ k.left) ≫ T.hom =
      (b ≫ (c ≫ a) ≫
        (Module.flatRankRepresentative Γ(U.1.toScheme, ⊤)
          Γ((pullback U.1.ι).obj E, ⊤) r).hom ≫ U.1.toScheme.isoSpec.inv) ≫ U.1.ι
    rw [Category.assoc, Over.w k, ← ha]
    rfl
  let e : (pullback j).obj N ≅ (pullback (psi ≫ U.1.ι)).obj E :=
    (pullbackComp j T.hom).app E ≪≫ (pullbackCongr hpsi).app E
  obtain ⟨hfin, hproj, hrank⟩ :=
    sections_top_finite_projective_rank_of_affineFlatRank E hfp r U psi hafr
  obtain ⟨hfin', hproj', hrank'⟩ :=
    sections_finite_projective_rank_of_iso e.symm ⊤ hfin hproj hrank
  obtain ⟨hfin'', hproj'', hrank''⟩ :=
    sections_finite_projective_rank_of_pullback_openImmersion
      j N ⊤ hfin' hproj' hrank'
  let W : T.left.affineOpens :=
    ⟨j ''ᵁ (⊤ : (Spec R).Opens),
      (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion j).mpr (isAffineOpen_top _)⟩
  have htW : t ∈ W.1 := by
    obtain ⟨w, hw⟩ := hvb
    exact ⟨w, trivial, by
      change j.base w = t
      change k.left.base (c.base (b.base w)) = t
      rw [hw, hv₁, hv]⟩
  exact ⟨W, htW, hfin'', hproj'', hrank''⟩

/-- Conversely, if the pulled-back sheaf is a vector bundle of rank `r`, the test
object locally factors through the affine flattening strata. -/
theorem locallyFactors_of_isProjectiveOfRank_pullback
    (hfp : E.IsFinitePresentation) (r : ℕ) (T : Over X)
    (hT : IsProjectiveOfRank r ((pullback T.hom).obj E)) :
    Scheme.LocallyFactors (affineStratum E r) T := by
  let N := (pullback T.hom).obj E
  haveI : N.IsQuasicoherent := inferInstance
  intro t
  obtain ⟨_, ⟨U₀, hU₀, rfl⟩, htU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (T.hom.base t)) isOpen_univ
  let U : X.affineOpens := ⟨U₀, hU₀⟩
  obtain ⟨_, ⟨W₀, hW₀, rfl⟩, htW, hWU⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open
      htU (T.hom ⁻¹ᵁ U.1).2
  let W : T.left.affineOpens := ⟨W₀, hW₀⟩
  have hNW : IsProjectiveOfRank r ((pullback W.1.ι).obj N) :=
    hT.pullback W.1.ι
  obtain ⟨A, htA, hfinA, hprojA, hrankA⟩ := hNW ⟨t, htW⟩
  let Z := A.1.toScheme
  let j : Z ⟶ T.left := A.1.ι ≫ W.1.ι
  haveI : IsOpenImmersion j := inferInstance
  let rho : W.1.toScheme ⟶ U.1.toScheme := T.hom.resLE U.1 W.1 hWU
  let psi : Z ⟶ U.1.toScheme := A.1.ι ≫ rho
  have hpsi : psi ≫ U.1.ι = j ≫ T.hom := by
    change (A.1.ι ≫ T.hom.resLE U.1 W.1 hWU) ≫ U.1.ι =
      (A.1.ι ≫ W.1.ι) ≫ T.hom
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
  let NW := (pullback W.1.ι).obj N
  have himageA : A.1.ι ''ᵁ (⊤ : Z.Opens) = A.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  obtain ⟨hfinPull, hprojPull, hrankPull⟩ :=
    pullback_openImmersion_sections_finite_projective_rank
      A.1.ι NW ⊤ (by rw [himageA]; exact hfinA)
        (by rw [himageA]; exact hprojA) (by rw [himageA]; exact hrankA)
  let e : (pullback A.1.ι).obj NW ≅ (pullback (psi ≫ U.1.ι)).obj E :=
    (pullback A.1.ι).mapIso ((pullbackComp W.1.ι T.hom).app E) ≪≫
      (pullbackComp A.1.ι (W.1.ι ≫ T.hom)).app E ≪≫
      (pullbackCongr hpsi.symm).app E
  obtain ⟨hfinM, hprojM, hrankM⟩ :=
    sections_finite_projective_rank_of_iso e ⊤
      hfinPull hprojPull hrankPull
  haveI : IsAffine U.1.toScheme := U.2
  letI : Algebra Γ(U.1.toScheme, ⊤) Γ(Z, ⊤) := psi.appTop.hom.toAlgebra
  let eTensor := affineOpenTensorEquiv E U psi
  letI : Module.Projective Γ(Z, ⊤) Γ((pullback (psi ≫ U.1.ι)).obj E, ⊤) := hprojM
  letI : Module.Flat Γ(Z, ⊤) Γ((pullback (psi ≫ U.1.ι)).obj E, ⊤) := inferInstance
  have hafr : AffineFlatRank E r U psi := ⟨
    Module.Flat.of_linearEquiv eTensor,
    fun p ↦ (congrFun (Module.rankAtStalk_eq_of_equiv eTensor) p).trans (hrankM p)⟩
  have hfpU : ((pullback U.1.ι).obj E).IsFinitePresentation :=
    isFinitePresentation_pullback_of_isFinitePresentation U.1.ι hfp
  have hfpSec : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
      Γ((pullback U.1.ι).obj E, ⊤) :=
    (Scheme.Modules.isFinitePresentation_iff_sections_affineOpens
      ((pullback U.1.ι).obj E)).mp hfpU ⟨⊤, isAffineOpen_top _⟩
  letI : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
      Γ((pullback U.1.ι).obj E, ⊤) := hfpSec
  letI : Module.Finite Γ(U.1.toScheme, ⊤)
      Γ((pullback U.1.ι).obj E, ⊤) := inferInstance
  have hloc := locallyFlatRank_of_affineFlatRank E r U psi hafr
  let c := (Module.flatRankRepresentableBy Γ(U.1.toScheme, ⊤)
    Γ((pullback U.1.ι).obj E, ⊤) r).homEquiv.symm ⟨⟨hloc⟩⟩
  have hc : c.left ≫
      (Module.flatRankRepresentative Γ(U.1.toScheme, ⊤)
        Γ((pullback U.1.ι).obj E, ⊤) r).hom =
      psi ≫ U.1.toScheme.isoSpec.hom := Over.w c
  have hfac : c.left ≫ (affineStratum E r U).hom = j ≫ T.hom := by
    change c.left ≫
      (Module.flatRankRepresentative Γ(U.1.toScheme, ⊤)
        Γ((pullback U.1.ι).obj E, ⊤) r).hom ≫
          U.1.toScheme.isoSpec.inv ≫ U.1.ι = j ≫ T.hom
    calc
      _ = (psi ≫ U.1.toScheme.isoSpec.hom) ≫
          U.1.toScheme.isoSpec.inv ≫ U.1.ι := by rw [← Category.assoc, hc]
      _ = psi ≫ U.1.ι := by simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = j ≫ T.hom := hpsi
  let k : Over.mk (j ≫ T.hom) ⟶ T := Over.homMk j rfl
  have hk : IsOpenImmersion k.left := by
    change IsOpenImmersion j
    infer_instance
  refine ⟨Over.mk (j ≫ T.hom), k, hk, ?_, U, c.left, hfac⟩
  exact ⟨⟨⟨t, htW⟩, htA⟩, rfl⟩

/-- For a finitely presented quasicoherent sheaf, the chartwise general-base
flattening condition is exactly finite local freeness of fixed rank after pullback. -/
theorem locallyFactors_affineStratum_iff_isProjectiveOfRank
    (hfp : E.IsFinitePresentation) (r : ℕ) (T : Over X) :
    Scheme.LocallyFactors (affineStratum E r) T ↔
      IsProjectiveOfRank r ((pullback T.hom).obj E) :=
  ⟨isProjectiveOfRank_pullback_of_locallyFactors E hfp r T,
    locallyFactors_of_isProjectiveOfRank_pullback E hfp r T⟩

end AlgebraicGeometry.Scheme.Modules

end
