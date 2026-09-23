module

public import StacksAndModuli.API.QuasicoherentObjectProperties
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»

/-!
# Fpqc locality of quasicoherent vector bundles

This file proves that finite local freeness is fpqc-local for quasicoherent sheaves.
The affine core identifies a finite locally free quasicoherent sheaf on `Spec R` with
a finite projective coordinate module. It then applies faithfully flat descent of
finite projective modules and passes from finite affine refinements to arbitrary fpqc
covering sieves.

The resulting locality instance applies to
`Scheme.Modules.vectorBundlePseudofunctor`, the full subpseudofunctor of
quasicoherent sheaves cut out by finite local freeness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 3000000 in
/-- On an affine spectrum, the coordinate module of a quasicoherent finite locally
free sheaf is flat. -/
lemma moduleSpecΓFunctor_flat_of_isFiniteLocallyFree
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (hM : IsFiniteLocallyFree M) :
    Module.Flat R (moduleSpecΓFunctor.obj M) := by
  have hpoint : ∀ x : Spec R, ∃ r : R,
      x ∈ PrimeSpectrum.basicOpen r ∧
        Module.Flat R Γ(M, PrimeSpectrum.basicOpen r) := by
    intro x
    obtain ⟨U, hxU, hfinU, hprojU⟩ := hM x
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter
      (isAffineOpen_top (Spec R)) U.2 x ⟨trivial, hxU⟩
    let r : R := (Scheme.ΓSpecIso R).hom f
    refine ⟨r, ?_, ?_⟩
    · rw [← basicOpen_eq_of_affine' f]
      exact hxf
    · let j := U.2.fromSpec
      let N := (pullback j).obj M
      have himTop : j ''ᵁ (⊤ : (Spec (.of Γ(Spec R, U.1))).Opens) = U.1 := by
        rw [Scheme.Hom.image_top_eq_opensRange, U.2.opensRange_fromSpec]
      have hfinImage : Module.Finite Γ(Spec R, j ''ᵁ ⊤) Γ(M, j ''ᵁ ⊤) := by
        rw [himTop]
        exact hfinU
      have hprojImage : Module.Projective Γ(Spec R, j ''ᵁ ⊤) Γ(M, j ''ᵁ ⊤) := by
        rw [himTop]
        exact hprojU
      have hNtop := pullback_openImmersion_sections_finite_projective
        j M ⊤ hfinImage hprojImage
      let b : R →+* Γ(Spec R, U.1) :=
        (Spec R).presheaf.map (homOfLE le_top).op |>.hom |>.comp
          (Scheme.ΓSpecIso R).inv.hom
      have hb : b.Flat := by
        let i := U.1.ι
        have hi : i ''ᵁ (⊤ : U.1.toScheme.Opens) = U.1 := by
          rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
        let e : Γ(Spec R, U.1) ≅ Γ(U.1, ⊤) :=
          (Spec R).presheaf.mapIso (eqToIso hi).op ≪≫ i.appIso ⊤
        apply (RingHom.Flat.comp_iff_of_bijective_left (f := b)
          (g := e.hom.hom) (ConcreteCategory.bijective_of_isIso e.hom)).mp
        let d : R →+* Γ(U.1, ⊤) :=
          (i.appLE ⊤ ⊤ le_top).hom.comp (Scheme.ΓSpecIso R).inv.hom
        have hd : d.Flat := RingHom.Flat.comp
          (RingHom.Flat.of_bijective
            (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv))
          (i.flat_appLE (isAffineOpen_top _) (isAffineOpen_top _) le_top)
        have hbd : e.hom.hom.comp b = d := by
          ext z
          simp [e, b, d, i, Scheme.Hom.appLE]
          rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
          rfl
        rwa [hbd]
      have hNcoord :
          Module.Finite Γ(Spec R, U.1)
              ((moduleSpecΓFunctor (R := Γ(Spec R, U.1))).obj N) ∧
            Module.Projective Γ(Spec R, U.1)
              ((moduleSpecΓFunctor (R := Γ(Spec R, U.1))).obj N) :=
        @moduleSpecΓFunctor_finite_projective_of_top
          Γ(Spec R, U.1) N hNtop.1 hNtop.2
      letI : Algebra R Γ(Spec R, U.1) := b.toAlgebra
      letI : Module.Flat R Γ(Spec R, U.1) := hb
      letI : Module.Projective Γ(Spec R, U.1)
          ((moduleSpecΓFunctor (R := Γ(Spec R, U.1))).obj N) :=
        hNcoord.2
      letI : Module.Flat Γ(Spec R, U.1)
          ((moduleSpecΓFunctor (R := Γ(Spec R, U.1))).obj N) :=
        inferInstance
      letI : Module R ((moduleSpecΓFunctor (R := Γ(Spec R, U.1))).obj N) :=
        Module.compHom ((moduleSpecΓFunctor (R := Γ(Spec R, U.1))).obj N) b
      letI : IsScalarTower R Γ(Spec R, U.1)
          ((moduleSpecΓFunctor (R := Γ(Spec R, U.1))).obj N) :=
        IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      have hNcoordFlat : Module.Flat R
          ((moduleSpecΓFunctor (R := Γ(Spec R, U.1))).obj N) :=
        Module.Flat.trans R Γ(Spec R, U.1)
          ((moduleSpecΓFunctor (R := Γ(Spec R, U.1))).obj N)
      letI : Module.Flat R
          ((moduleSpecΓFunctor (R := Γ(Spec R, U.1))).obj N) := hNcoordFlat
      have hNflat :
          letI := Module.compHom Γ(N, ⊤) b
          Module.Flat R Γ(N, ⊤) := by
        exact moduleSpecΓFunctor_flat_to_top_restrictScalars N b
          (fun _ _ ↦ rfl)
      let s : Γ(Spec R, U.1) := g
      have hbasic :
          letI := Module.compHom Γ(N, PrimeSpectrum.basicOpen s) b
          Module.Flat R Γ(N, PrimeSpectrum.basicOpen s) := by
        exact flat_sections_basicOpen_of_top N s hNflat
      let D := PrimeSpectrum.basicOpen s
      let bD : R →+* Γ(Spec Γ(Spec R, U.1), D) :=
        (algebraMap Γ(Spec R, U.1) _).comp b
      have hbasicD :
          letI := Module.compHom Γ(N, D) bD
          Module.Flat R Γ(N, D) := by
        exact hbasic
      let a : R →+* Γ(Spec R, j ''ᵁ D) := (j.appIso D).inv.hom.comp bD
      have hpush :
          letI := Module.compHom Γ(M, j ''ᵁ D) a
          Module.Flat R Γ(M, j ''ᵁ D) :=
        sections_flat_of_pullback_openImmersion j M D bD hbasicD
      have hopen : j ''ᵁ D = PrimeSpectrum.basicOpen r := by
        dsimp [D, s, j]
        rw [U.2.fromSpec_image_basicOpen, ← hfg, basicOpen_eq_of_affine' f]
      have htransport :
          let a' : R →+* Γ(Spec R, PrimeSpectrum.basicOpen r) := hopen ▸ a
          letI := Module.compHom Γ(M, PrimeSpectrum.basicOpen r) a'
          Module.Flat R Γ(M, PrimeSpectrum.basicOpen r) :=
        sections_flat_of_eq M (j ''ᵁ D) (PrimeSpectrum.basicOpen r)
          hopen a hpush
      let dImg : Γ(Spec R, ⊤) →+* Γ(Spec R, j ''ᵁ D) :=
        ((𝟙 (Spec R) : Spec R ⟶ Spec R).appLE ⊤ (j ''ᵁ D) le_top).hom
      have ha : a = dImg.comp (Scheme.ΓSpecIso R).inv.hom := by
        let c0 : Γ(Spec R, ⊤) →+* Γ(Spec R, U.1) :=
          ((𝟙 (Spec R) : Spec R ⟶ Spec R).appLE ⊤ U.1 (by simp)).hom
        let b0 : Γ(Spec R, ⊤) →+* Γ(Spec Γ(Spec R, U.1), D) :=
          (algebraMap Γ(Spec R, U.1) _).comp c0
        let a0 : Γ(Spec R, ⊤) →+* Γ(Spec R, j ''ᵁ D) :=
          (j.appIso D).inv.hom.comp b0
        let d0 : Γ(Spec R, ⊤) →+* Γ(Spec R, j ''ᵁ D) :=
          ((𝟙 (Spec R) : Spec R ⟶ Spec R).appLE ⊤ (j ''ᵁ D) le_top).hom
        have hcore := affineOpen_fromSpec_coefficient
          (𝟙 (Spec R)) U (⊤ : (Spec R).Opens) (by simp) D
        have hcore' : a0 = d0 := by
          simpa only [a0, b0, c0, d0, j] using hcore
        calc
          a = a0.comp (Scheme.ΓSpecIso R).inv.hom := by
            ext z
            rfl
          _ = d0.comp (Scheme.ΓSpecIso R).inv.hom := by rw [hcore']
          _ = dImg.comp (Scheme.ΓSpecIso R).inv.hom := by rfl
      let dTarget : Γ(Spec R, ⊤) →+* Γ(Spec R, PrimeSpectrum.basicOpen r) :=
        ((𝟙 (Spec R) : Spec R ⟶ Spec R).appLE ⊤
          (PrimeSpectrum.basicOpen r) le_top).hom
      have hdTransport : hopen ▸ dImg = dTarget := by
        dsimp only [dImg, dTarget]
        exact Scheme.Hom.appLE_hom_transport (𝟙 (Spec R)) ⊤
          (j ''ᵁ D) (PrimeSpectrum.basicOpen r) hopen le_top le_top
      have hcoef : hopen ▸ a = algebraMap R Γ(Spec R, PrimeSpectrum.basicOpen r) := by
        ext z
        rw [Scheme.ringHom_transport_apply]
        rw [RingHom.congr_fun ha z]
        have hz := RingHom.congr_fun hdTransport
          ((Scheme.ΓSpecIso R).inv.hom z)
        rw [Scheme.ringHom_transport_apply] at hz
        change hopen ▸ dImg ((Scheme.ΓSpecIso R).inv.hom z) =
          (algebraMap R Γ(Spec R, PrimeSpectrum.basicOpen r)) z
        rw [hz]
        have hto := congrArg
          (fun q : R ⟶ Γ(Spec R, PrimeSpectrum.basicOpen r) ↦ q.hom z)
          (Scheme.toOpen_eq (R := R) (PrimeSpectrum.basicOpen r))
        simpa [dTarget, Scheme.Hom.appLE] using hto.symm
      exact Module.Flat.compHom_congr (hopen ▸ a)
        (algebraMap R Γ(Spec R, PrimeSpectrum.basicOpen r)) hcoef htransport

  have htop :
      letI := Module.compHom Γ(M, ⊤) (RingHom.id R)
      Module.Flat R Γ(M, ⊤) :=
    flat_sections_top_of_pointwise_basicOpen M hpoint
  exact moduleSpecΓFunctor_flat_of_top_restrictScalars M (RingHom.id R)
    (fun r m ↦ algebra_compatible_smul Γ(Spec R, ⊤) r m)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 3000000 in
/-- On an affine spectrum, a quasicoherent finite locally free sheaf has a finite
projective coordinate module. -/
lemma moduleSpecΓFunctor_finite_projective_of_isFiniteLocallyFree
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]
    (hM : IsFiniteLocallyFree M) :
    Module.Finite R (moduleSpecΓFunctor.obj M) ∧
      Module.Projective R (moduleSpecΓFunctor.obj M) := by
  have hfpSheaf : M.IsFinitePresentation := hM.isFinitePresentation
  letI : M.IsFinitePresentation := hfpSheaf
  have hfp : Module.FinitePresentation R (moduleSpecΓFunctor.obj M) :=
    AlgebraicGeometry.moduleSpecΓFunctor_finitePresentation_of_isFinitePresentation M
  letI : Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := hfp
  have hflat : Module.Flat R (moduleSpecΓFunctor.obj M) :=
    moduleSpecΓFunctor_flat_of_isFiniteLocallyFree M hM
  letI : Module.Flat R (moduleSpecΓFunctor.obj M) := hflat
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 3000000 in
/-- Finite local freeness of a quasicoherent sheaf descends along a flat surjective
morphism between affine schemes. -/
lemma isFiniteLocallyFree_of_pullback_of_flat_surjective_affine
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)
    [Flat f] [Surjective f] (M : Y.Modules) [M.IsQuasicoherent]
    (hM : IsFiniteLocallyFree ((pullback f).obj M)) : IsFiniteLocallyFree M := by
  let N := (pullback Y.isoSpec.inv).obj M
  let N' := (pullback X.isoSpec.inv).obj ((pullback f).obj M)
  have hN' : IsFiniteLocallyFree N' :=
    hM.pullback_of_isIso X.isoSpec.inv
  let e := AlgebraicGeometry.pullbackAffineIsoSpecIso f M
  have hPull : IsFiniteLocallyFree ((pullback (Spec.map f.appTop)).obj N) :=
    IsFiniteLocallyFree.of_iso e.symm hN'
  have hB := moduleSpecΓFunctor_finite_projective_of_isFiniteLocallyFree
    ((pullback (Spec.map f.appTop)).obj N) hPull
  letI : Module.Projective Γ(X, ⊤)
      (moduleSpecΓFunctor.obj ((pullback (Spec.map f.appTop)).obj N)) := hB.2
  let eSec := AlgebraicGeometry.pullbackQuasicoherentSectionsLinearEquiv f.appTop N
  have hTensorProj : Module.Projective Γ(X, ⊤)
      ((ModuleCat.extendScalars f.appTop.hom).obj
        (moduleSpecΓFunctor.obj N)) :=
    Module.Projective.of_equiv eSec
  have hMfp : M.IsFinitePresentation :=
    isFinitePresentation_of_pullback_of_flat_surjective_affine f M
      hM.isFinitePresentation
  letI : M.IsFinitePresentation := hMfp
  have hNfp : N.IsFinitePresentation := by
    dsimp [N]
    infer_instance
  letI : N.IsFinitePresentation := hNfp
  have hNmodFp : Module.FinitePresentation Γ(Y, ⊤)
      (moduleSpecΓFunctor.obj N) :=
    AlgebraicGeometry.moduleSpecΓFunctor_finitePresentation_of_isFinitePresentation N
  letI : Module.FinitePresentation Γ(Y, ⊤) (moduleSpecΓFunctor.obj N) := hNmodFp
  letI : Module.Finite Γ(Y, ⊤) (moduleSpecΓFunctor.obj N) := inferInstance
  have hff : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp
      ⟨inferInstance, inferInstance⟩
  algebraize [f.appTop.hom]
  letI : Module.FaithfullyFlat Γ(Y, ⊤) Γ(X, ⊤) := hff
  letI : Module.Projective Γ(X, ⊤)
      (TensorProduct Γ(Y, ⊤) Γ(X, ⊤) (moduleSpecΓFunctor.obj N)) := by
    change Module.Projective Γ(X, ⊤)
      ((ModuleCat.extendScalars f.appTop.hom).obj (moduleSpecΓFunctor.obj N))
    exact hTensorProj
  have hNproj : Module.Projective Γ(Y, ⊤) (moduleSpecΓFunctor.obj N) :=
    Module.Projective.of_baseChange_faithfullyFlat
      Γ(Y, ⊤) (moduleSpecΓFunctor.obj N) Γ(X, ⊤)
  have hNtop := AlgebraicGeometry.moduleSpecΓFunctor_finite_projective_top N
    (inferInstance : Module.Finite Γ(Y, ⊤) (moduleSpecΓFunctor.obj N)) hNproj
  have hN : IsFiniteLocallyFree N :=
    isFiniteLocallyFree_of_top hNtop.1 hNtop.2
  have hBack : IsFiniteLocallyFree ((pullback Y.isoSpec.hom).obj N) :=
    hN.pullback_of_isIso Y.isoSpec.hom
  let eBack : (pullback Y.isoSpec.hom).obj N ≅ M :=
    (pullbackComp Y.isoSpec.hom Y.isoSpec.inv).app M ≪≫
      (pullbackCongr Y.isoSpec.hom_inv_id).app M ≪≫
      (pullbackId _).app M
  exact IsFiniteLocallyFree.of_iso eBack hBack

/-- Finite local freeness can be checked after pullback to every affine open
subscheme. -/
lemma IsFiniteLocallyFree.of_affineOpen_pullbacks {X : Scheme.{u}} {M : X.Modules}
    (h : ∀ U : X.affineOpens,
      IsFiniteLocallyFree ((Modules.pullback U.1.ι).obj M)) :
    IsFiniteLocallyFree M := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  let A : X.affineOpens := ⟨U, hU⟩
  obtain ⟨V, hxV, hfin, hproj⟩ := h A ⟨x, hxU⟩
  let W : X.affineOpens :=
    ⟨A.1.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion A.1.ι⟩
  refine ⟨W, ?_, ?_⟩
  · exact ⟨⟨x, hxU⟩, hxV, rfl⟩
  · exact sections_finite_projective_of_pullback_openImmersion
      A.1.ι M V.1 hfin hproj

/-- Finite local freeness descends from the members of an arbitrary
scheme-theoretic open cover. -/
lemma IsFiniteLocallyFree.of_openCover_restrict {X : Scheme.{u}} {M : X.Modules}
    (𝒰 : X.OpenCover) (h : ∀ i,
      IsFiniteLocallyFree ((Modules.restrictFunctor (𝒰.f i)).obj M)) :
    IsFiniteLocallyFree M := by
  intro x
  obtain ⟨y, hy⟩ := 𝒰.covers x
  let i := 𝒰.idx x
  have hPull : IsFiniteLocallyFree ((Modules.pullback (𝒰.f i)).obj M) :=
    (h i).of_iso ((Modules.restrictFunctorIsoPullback (𝒰.f i)).app M)
  obtain ⟨U, hyU, hfin, hproj⟩ := hPull y
  let W : X.affineOpens :=
    ⟨𝒰.f i ''ᵁ U.1, U.2.image_of_isOpenImmersion (𝒰.f i)⟩
  refine ⟨W, ?_, ?_⟩
  · exact ⟨y, hyU, hy⟩
  · exact sections_finite_projective_of_pullback_openImmersion
      (𝒰.f i) M U.1 hfin hproj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 3000000 in
/-- Finite local freeness on a finite disjoint union is detected on its
components. -/
lemma isFiniteLocallyFree_of_sigma_pullbacks {n : ℕ} (X : Fin n → Scheme.{u})
    [∀ i, IsAffine (X i)] (M : (∐ X).Modules) [M.IsQuasicoherent]
    (hM : ∀ i, IsFiniteLocallyFree ((pullback (Sigma.ι X i)).obj M)) :
    IsFiniteLocallyFree M := by
  let 𝒰 := AlgebraicGeometry.sigmaOpenCover X
  apply IsFiniteLocallyFree.of_openCover_restrict 𝒰
  intro i
  have hi : IsFiniteLocallyFree ((pullback (𝒰.f i)).obj M) := hM i
  exact hi.of_iso ((restrictFunctorIsoPullback (𝒰.f i)).app M).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 3000000 in
/-- Finite local freeness descends from an fpqc covering sieve on an affine
scheme. -/
lemma isFiniteLocallyFree_of_fpqc_sieve_affine {S : Scheme.{u}} [IsAffine S]
    (R : Sieve S) (hR : R ∈ Scheme.fpqcTopology S)
    (M : S.Modules) [M.IsQuasicoherent]
    (hM : ∀ {X : Scheme.{u}} (f : X ⟶ S), R.arrows f →
      IsFiniteLocallyFree ((pullback f).obj M)) :
    IsFiniteLocallyFree M := by
  obtain ⟨Q, hQ, hQR⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hR
  obtain ⟨n, X, p, hX, hp, hpQ, hcover⟩ :=
    Scheme.exists_finite_affine_refinement_of_mem_fpqcPrecoverage hQ
  letI (i : Fin n) : IsAffine (X i) := hX i
  have hcoverFlat : Presieve.ofArrows X p ∈ Scheme.precoverage (@Flat) S :=
    (Scheme.propQCPrecoverage_le_precoverage (P := @Flat)) S hcover
  let C : Scheme.Cover.{0, u} (Scheme.precoverage (@Flat)) S :=
    { I₀ := Fin n
      X := X
      f := p
      mem₀ := hcoverFlat }
  let T : Scheme.{u} := ∐ X
  let q : T ⟶ S := Sigma.desc p
  letI : IsAffine T := by
    dsimp [T]
    infer_instance
  letI : Flat q := IsZariskiLocalAtSource.sigmaDesc hp
  letI : Surjective q :=
    Surjective.sigmaDesc_of_union_range_eq_univ (by
      simpa [C, q] using C.iUnion_range)
  have hqM : IsFiniteLocallyFree ((pullback q).obj M) := by
    apply isFiniteLocallyFree_of_sigma_pullbacks X
    intro i
    have hpR : R.arrows (p i) :=
      ((Sieve.generate_le_iff Q R).mpr hQR) _ (hpQ i)
    have hpi : IsFiniteLocallyFree ((pullback (p i)).obj M) := hM (p i) hpR
    let e : (pullback (Sigma.ι X i)).obj ((pullback q).obj M) ≅
        (pullback (p i)).obj M :=
      (pullbackComp (Sigma.ι X i) q).app M ≪≫
        (pullbackCongr (Sigma.ι_desc p i)).app M
    exact hpi.of_iso e.symm
  exact isFiniteLocallyFree_of_pullback_of_flat_surjective_affine q M hqM

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 3000000 in
/-- Finite local freeness of a quasicoherent sheaf descends from an fpqc
covering sieve. -/
lemma isFiniteLocallyFree_of_fpqc_sieve {S : Scheme.{u}}
    (R : Sieve S) (hR : R ∈ Scheme.fpqcTopology S)
    (M : S.Modules) [M.IsQuasicoherent]
    (hM : ∀ {X : Scheme.{u}} (f : X ⟶ S), R.arrows f →
      IsFiniteLocallyFree ((pullback f).obj M)) :
    IsFiniteLocallyFree M := by
  apply IsFiniteLocallyFree.of_affineOpen_pullbacks
  intro U
  let f := U.1.ι
  let N := (pullback f).obj M
  apply isFiniteLocallyFree_of_fpqc_sieve_affine
    (R.pullback f) (Scheme.fpqcTopology.pullback_stable f hR) N
  intro X g hg
  have hcomp : IsFiniteLocallyFree ((pullback (g ≫ f)).obj M) :=
    hM (g ≫ f) hg
  exact hcomp.of_iso ((pullbackComp g f).app M).symm

instance : finiteLocallyFreeProperty.{u}.IsLocal Scheme.fpqcTopology where
  of_sieve {S} R hR M hM := by
    change IsFiniteLocallyFree M.obj
    letI : M.obj.IsQuasicoherent := M.property
    apply isFiniteLocallyFree_of_fpqc_sieve R hR M.obj
    intro X f hf
    let q := Presieve.categoryMk R.arrows f hf
    have hq := hM q
    change IsFiniteLocallyFree ((pullback f).obj M.obj) at hq
    exact hq

end AlgebraicGeometry.Scheme.Modules
