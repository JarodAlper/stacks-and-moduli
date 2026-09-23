module

public import StacksAndModuli.API.ProjectiveGradedEventuallyFlat
public import StacksAndModuli.API.ProjChartFlatSections
public import StacksAndModuli.API.ProjGammaStarChart
public import StacksAndModuli.API.ProjGammaStarProjectiveSpace
public import StacksAndModuli.API.ProjTwistModuleQuasicoherentOfQuasicoherent
public import StacksAndModuli.API.ProjectiveTwistedFreeGlobalSectionsFinite
public import StacksAndModuli.API.PushforwardProjectiveRank
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»

/-!
# Eventual flatness of `Γ_*` and relative flatness on projective space

Supporting API with no Stacks Project counterpart.

If the graded pieces of `Γ_*(F)` are flat in all sufficiently large degrees, then every
degree of each single-coordinate localization is flat.  The chart comparison identifies
the degree-zero piece of that localization with the sections of `F(0)` on the corresponding
standard chart, and the zero-twist comparison then identifies those sections with the
sections of `F` itself.  Quasicoherent affine gluing gives flat sections on every affine
open of polynomial `Proj`.  The affine polynomial-`Proj` comparison and the canonical
identification
`ℙⁿ_{Spec Γ(T,V)} ≅ (π⁻¹(V)).toScheme` then assemble these affine-base statements into
`Scheme.Modules.FlatOver` on relative projective space over an arbitrary base.

Main declarations:

* `AlgebraicGeometry.Proj.flat_openSections_basicOpen_of_isFlatAbove_gammaStar`;
* `AlgebraicGeometry.Proj.flat_openSections_affine_of_isFlatAbove_gammaStar`;
* `AlgebraicGeometry.ProjectiveSpace.flat_openSections_affine_of_isFlatAbove_gammaStarPull`;
* `AlgebraicGeometry.ProjectiveSpace.flatOver_of_isFlatAbove_gammaStarPull_on_affineOpens`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Proj

open ProjectiveSpectrum.Twist AlgebraicGeometry.ProjectiveSpace

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {n : ℕ} {R : CommRingCat.{u}} (π : Proj 𝒜 ⟶ Spec R)
variable (G : (Proj 𝒜).Modules) (x : Fin (n + 1) → 𝒜 1)

/-- Flatness over the coordinate ring of an affine base open passes from an affine open
to every ambient basic open cut out inside it. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.flat_basicOpen_of_flat_affineOpen
    {X : Scheme.{u}} {R : CommRingCat.{u}} (p : X ⟶ Spec R)
    (M : X.Modules) [M.IsQuasicoherent] (W : X.affineOpens)
    (hflat :
      letI := Module.compHom Γ(M, W.1) (p.appLE ⊤ W.1 le_top).hom
      Module.Flat Γ(Spec R, ⊤) Γ(M, W.1))
    (s : Γ(X, W.1)) :
    letI := Module.compHom Γ(M, X.basicOpen s)
      (p.appLE ⊤ (X.basicOpen s) le_top).hom
    Module.Flat Γ(Spec R, ⊤) Γ(M, X.basicOpen s) := by
  let j := W.2.fromSpec
  let N := (Scheme.Modules.pullback j).obj M
  letI : N.IsQuasicoherent := by
    dsimp only [N]
    infer_instance
  let D := PrimeSpectrum.basicOpen s
  have himageTop : j ''ᵁ (⊤ : (Spec (.of Γ(X, W.1))).Opens) = W.1 := by
    rw [Scheme.Hom.image_top_eq_opensRange, W.2.opensRange_fromSpec]
  let c : Γ(Spec R, ⊤) →+* Γ(X, W.1) := (p.appLE ⊤ W.1 le_top).hom
  let aTop : Γ(Spec R, ⊤) →+* Γ(X, j ''ᵁ ⊤) := himageTop.symm ▸ c
  have hflatImage :
      letI := Module.compHom Γ(M, j ''ᵁ ⊤) aTop
      Module.Flat Γ(Spec R, ⊤) Γ(M, j ''ᵁ ⊤) :=
    Scheme.Modules.sections_flat_of_eq M W.1 (j ''ᵁ ⊤)
      himageTop.symm c hflat
  have hNtopRaw :
      letI := Module.compHom Γ(N, ⊤) ((j.appIso ⊤).hom.hom.comp aTop)
      Module.Flat Γ(Spec R, ⊤) Γ(N, ⊤) :=
    Scheme.Modules.pullback_openImmersion_sections_flat_restrictScalars
      j M ⊤ aTop hflatImage
  letI : Algebra Γ(Spec R, ⊤) Γ(X, W.1) := c.toAlgebra
  have hNtop :
      letI := Module.compHom Γ(N, ⊤)
        ((Scheme.ΓSpecIso (.of Γ(X, W.1))).inv.hom.comp c)
      Module.Flat Γ(Spec R, ⊤) Γ(N, ⊤) := by
    let bTop : Γ(Spec R, ⊤) →+* Γ(Spec Γ(X, W.1), ⊤) :=
      (algebraMap Γ(X, W.1) _).comp c
    let hJD : j ''ᵁ (⊤ : (Spec (.of Γ(X, W.1))).Opens) ≤
        p ⁻¹ᵁ (⊤ : (Spec R).Opens) := le_top
    have htransport : aTop = (p.appLE ⊤ (j ''ᵁ ⊤) hJD).hom :=
      Scheme.Hom.appLE_hom_transport p ⊤ W.1 (j ''ᵁ ⊤)
        himageTop.symm le_top hJD
    have hcoef := Scheme.Modules.affineOpen_fromSpec_coefficient p W ⊤
      (show W.1 ≤ p ⁻¹ᵁ (⊤ : (Spec R).Opens) from le_top)
      (⊤ : (Spec (.of Γ(X, W.1))).Opens)
    have hmap : (j.appIso ⊤).hom.hom.comp aTop = bTop := by
      have ha : aTop = (j.appIso ⊤).inv.hom.comp bTop := by
        exact htransport.trans (by simpa only [j, c, bTop, hJD] using hcoef.symm)
      exact (congrArg (fun q ↦ (j.appIso ⊤).hom.hom.comp q) ha).trans (by
        ext z
        simp)
    apply Module.Flat.compHom_congr
      ((j.appIso ⊤).hom.hom.comp aTop)
      ((Scheme.ΓSpecIso (.of Γ(X, W.1))).inv.hom.comp c)
    · exact hmap
    · exact hNtopRaw
  let b : Γ(Spec R, ⊤) →+* Γ(Spec Γ(X, W.1), D) :=
    (algebraMap Γ(X, W.1) _).comp c
  have hND :
      letI := Module.compHom Γ(N, D) b
      Module.Flat Γ(Spec R, ⊤) Γ(N, D) := by
    exact Scheme.Modules.flat_sections_basicOpen_of_top N s hNtop
  have hND' :
      letI := Module.compHom Γ(N, D) b
      Module.Flat Γ(Spec R, ⊤) Γ(N, D) := by
    exact hND
  have hpush := Scheme.Modules.sections_flat_of_pullback_openImmersion
    j M D b hND'
  have himage : j ''ᵁ D = X.basicOpen s := by
    dsimp only [D, j]
    exact W.2.fromSpec_image_basicOpen s
  have htransport :
      let a' : Γ(Spec R, ⊤) →+* Γ(X, X.basicOpen s) :=
        himage ▸ ((j.appIso D).inv.hom.comp b)
      letI := Module.compHom Γ(M, X.basicOpen s) a'
      Module.Flat Γ(Spec R, ⊤) Γ(M, X.basicOpen s) :=
    Scheme.Modules.sections_flat_of_eq M (j ''ᵁ D) (X.basicOpen s)
      himage ((j.appIso D).inv.hom.comp b) hpush
  apply Module.Flat.compHom_congr
    (himage ▸ ((j.appIso D).inv.hom.comp b))
    (p.appLE ⊤ (X.basicOpen s) le_top).hom
  · let hJD : j ''ᵁ D ≤ p ⁻¹ᵁ (⊤ : (Spec R).Opens) := le_top
    have hcoef := Scheme.Modules.affineOpen_fromSpec_coefficient p W ⊤
      (show W.1 ≤ p ⁻¹ᵁ (⊤ : (Spec R).Opens) from le_top) D
    have hraw : (j.appIso D).inv.hom.comp b =
        (p.appLE ⊤ (j ''ᵁ D) hJD).hom := by
      simpa only [j, c, b, hJD] using hcoef
    exact (congrArg
      (fun q : Γ(Spec R, ⊤) →+* Γ(X, j ''ᵁ D) ↦ himage ▸ q) hraw).trans
      (Scheme.Hom.appLE_hom_transport p ⊤ (j ''ᵁ D)
        (X.basicOpen s) himage hJD le_top)
  · exact htransport

/-- Flatness of affine sections descends through an isomorphism of source schemes.  The
coefficient morphism on the source is written as the composite with the isomorphism, so the
only content is transport of sections across the corresponding image open. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.flat_sections_affine_of_pullback_isIso
    {X Y : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Y) [IsIso f]
    (M : Y.Modules) (p : Y ⟶ Spec R) (V : Y.affineOpens)
    (hflat :
      let U : X.affineOpens := ⟨f ⁻¹ᵁ V.1, V.2.preimage f⟩
      letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, U.1)
        ((f ≫ p).appLE ⊤ U.1 le_top).hom
      Module.Flat Γ(Spec R, ⊤) Γ((Scheme.Modules.pullback f).obj M, U.1)) :
    letI := Module.compHom Γ(M, V.1) (p.appLE ⊤ V.1 le_top).hom
    Module.Flat Γ(Spec R, ⊤) Γ(M, V.1) := by
  let U : X.affineOpens := ⟨f ⁻¹ᵁ V.1, V.2.preimage f⟩
  let b : Γ(Spec R, ⊤) →+* Γ(X, U.1) :=
    ((f ≫ p).appLE ⊤ U.1 le_top).hom
  have hflat' :
      letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, U.1) b
      Module.Flat Γ(Spec R, ⊤) Γ((Scheme.Modules.pullback f).obj M, U.1) := hflat
  have hpush := Scheme.Modules.sections_flat_of_pullback_openImmersion
    f M U.1 b hflat'
  have himage : f ''ᵁ U.1 = V.1 := by
    dsimp only [U]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  have htransport :
      let a' : Γ(Spec R, ⊤) →+* Γ(Y, V.1) :=
        himage ▸ ((f.appIso U.1).inv.hom.comp b)
      letI := Module.compHom Γ(M, V.1) a'
      Module.Flat Γ(Spec R, ⊤) Γ(M, V.1) :=
    Scheme.Modules.sections_flat_of_eq M (f ''ᵁ U.1) V.1 himage
      ((f.appIso U.1).inv.hom.comp b) hpush
  apply Module.Flat.compHom_congr
    (himage ▸ ((f.appIso U.1).inv.hom.comp b))
    (p.appLE ⊤ V.1 le_top).hom
  · have hpre : U.1 ≤ f ⁻¹ᵁ (f ''ᵁ U.1) := f.preimage_image_eq U.1 |>.ge
    have hinj : Function.Injective
        (fun q : Γ(Spec R, ⊤) →+* Γ(Y, f ''ᵁ U.1) ↦
          (f.appIso U.1).hom.hom.comp q) := by
      intro q₁ q₂ hq
      ext r
      apply (ConcreteCategory.bijective_of_isIso (f.appIso U.1).hom).injective
      exact RingHom.congr_fun hq r
    have hmap : (f.appIso U.1).inv.hom.comp b =
        (p.appLE ⊤ (f ''ᵁ U.1) le_top).hom := by
      apply hinj
      have hleft : (f.appIso U.1).hom.hom.comp
          ((f.appIso U.1).inv.hom.comp b) = b := by
        ext r
        simp
      exact hleft.trans (by
        rw [Scheme.Hom.appIso_hom']
        change b = (((p.appLE ⊤ (f ''ᵁ U.1) le_top) ≫
          f.appLE (f ''ᵁ U.1) U.1 hpre).hom)
        rw [Scheme.Hom.appLE_comp_appLE])
    exact (congrArg
      (fun q : Γ(Spec R, ⊤) →+* Γ(Y, f ''ᵁ U.1) ↦ himage ▸ q) hmap).trans
      (Scheme.Hom.appLE_hom_transport p ⊤ (f ''ᵁ U.1) V.1
        himage le_top le_top)
  · exact htransport

/-- Flatness of affine sections descends from the pullback along an open immersion when
the affine open lies in its range. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.flat_sections_affine_of_pullback_openImmersion
    {X Y : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (p : Y ⟶ Spec R) (V : Y.affineOpens)
    (hV : V.1 ≤ f.opensRange)
    (hflat :
      let U : X.affineOpens :=
        ⟨f ⁻¹ᵁ V.1, V.2.preimage_of_isOpenImmersion f hV⟩
      letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, U.1)
        ((f ≫ p).appLE ⊤ U.1 le_top).hom
      Module.Flat Γ(Spec R, ⊤) Γ((Scheme.Modules.pullback f).obj M, U.1)) :
    letI := Module.compHom Γ(M, V.1) (p.appLE ⊤ V.1 le_top).hom
    Module.Flat Γ(Spec R, ⊤) Γ(M, V.1) := by
  let U : X.affineOpens :=
    ⟨f ⁻¹ᵁ V.1, V.2.preimage_of_isOpenImmersion f hV⟩
  let b : Γ(Spec R, ⊤) →+* Γ(X, U.1) :=
    ((f ≫ p).appLE ⊤ U.1 le_top).hom
  have hflat' :
      letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, U.1) b
      Module.Flat Γ(Spec R, ⊤) Γ((Scheme.Modules.pullback f).obj M, U.1) := hflat
  have hpush := Scheme.Modules.sections_flat_of_pullback_openImmersion
    f M U.1 b hflat'
  have himage : f ''ᵁ U.1 = V.1 := by
    dsimp only [U]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]
  have htransport :
      let a' : Γ(Spec R, ⊤) →+* Γ(Y, V.1) :=
        himage ▸ ((f.appIso U.1).inv.hom.comp b)
      letI := Module.compHom Γ(M, V.1) a'
      Module.Flat Γ(Spec R, ⊤) Γ(M, V.1) :=
    Scheme.Modules.sections_flat_of_eq M (f ''ᵁ U.1) V.1 himage
      ((f.appIso U.1).inv.hom.comp b) hpush
  apply Module.Flat.compHom_congr
    (himage ▸ ((f.appIso U.1).inv.hom.comp b))
    (p.appLE ⊤ V.1 le_top).hom
  · have hpre : U.1 ≤ f ⁻¹ᵁ (f ''ᵁ U.1) := f.preimage_image_eq U.1 |>.ge
    have hinj : Function.Injective
        (fun q : Γ(Spec R, ⊤) →+* Γ(Y, f ''ᵁ U.1) ↦
          (f.appIso U.1).hom.hom.comp q) := by
      intro q₁ q₂ hq
      ext r
      apply (ConcreteCategory.bijective_of_isIso (f.appIso U.1).hom).injective
      exact RingHom.congr_fun hq r
    have hmap : (f.appIso U.1).inv.hom.comp b =
        (p.appLE ⊤ (f ''ᵁ U.1) le_top).hom := by
      apply hinj
      have hleft : (f.appIso U.1).hom.hom.comp
          ((f.appIso U.1).inv.hom.comp b) = b := by
        ext r
        simp
      exact hleft.trans (by
        rw [Scheme.Hom.appIso_hom']
        change b = (((p.appLE ⊤ (f ''ᵁ U.1) le_top) ≫
          f.appLE (f ''ᵁ U.1) U.1 hpre).hom)
        rw [Scheme.Hom.appLE_comp_appLE])
    exact (congrArg
      (fun q : Γ(Spec R, ⊤) →+* Γ(Y, f ''ᵁ U.1) ↦ himage ▸ q) hmap).trans
      (Scheme.Hom.appLE_hom_transport p ⊤ (f ''ᵁ U.1) V.1
        himage le_top le_top)
  · exact htransport

/-- The arbitrary-base-open form of
`flat_sections_affine_of_pullback_openImmersion`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.flat_sections_affine_of_pullback_openImmersion_appLE
    {X Y T : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (p : Y ⟶ T) (V : Y.affineOpens) (W : T.affineOpens)
    (hVW : V.1 ≤ p ⁻¹ᵁ W.1) (hV : V.1 ≤ f.opensRange)
    (hflat :
      let U : X.affineOpens :=
        ⟨f ⁻¹ᵁ V.1, V.2.preimage_of_isOpenImmersion f hV⟩
      let hUW : U.1 ≤ (f ≫ p) ⁻¹ᵁ W.1 := by
        intro x hx
        exact hVW hx
      letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, U.1)
        ((f ≫ p).appLE W.1 U.1 hUW).hom
      Module.Flat Γ(T, W.1) Γ((Scheme.Modules.pullback f).obj M, U.1)) :
    letI := Module.compHom Γ(M, V.1) (p.appLE W.1 V.1 hVW).hom
    Module.Flat Γ(T, W.1) Γ(M, V.1) := by
  let U : X.affineOpens :=
    ⟨f ⁻¹ᵁ V.1, V.2.preimage_of_isOpenImmersion f hV⟩
  let hUW : U.1 ≤ (f ≫ p) ⁻¹ᵁ W.1 := by
    intro x hx
    exact hVW hx
  let b : Γ(T, W.1) →+* Γ(X, U.1) :=
    ((f ≫ p).appLE W.1 U.1 hUW).hom
  have hflat' :
      letI := Module.compHom Γ((Scheme.Modules.pullback f).obj M, U.1) b
      Module.Flat Γ(T, W.1) Γ((Scheme.Modules.pullback f).obj M, U.1) := hflat
  have hpush := Scheme.Modules.sections_flat_of_pullback_openImmersion
    f M U.1 b hflat'
  have himage : f ''ᵁ U.1 = V.1 := by
    dsimp only [U]
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]
  let hImage : f ''ᵁ U.1 ≤ p ⁻¹ᵁ W.1 := by
    rintro y ⟨x, hx, rfl⟩
    exact hVW hx
  have htransport :
      let a' : Γ(T, W.1) →+* Γ(Y, V.1) :=
        himage ▸ ((f.appIso U.1).inv.hom.comp b)
      letI := Module.compHom Γ(M, V.1) a'
      Module.Flat Γ(T, W.1) Γ(M, V.1) :=
    Scheme.Modules.sections_flat_of_eq M (f ''ᵁ U.1) V.1 himage
      ((f.appIso U.1).inv.hom.comp b) hpush
  apply Module.Flat.compHom_congr
    (himage ▸ ((f.appIso U.1).inv.hom.comp b))
    (p.appLE W.1 V.1 hVW).hom
  · have hpre : U.1 ≤ f ⁻¹ᵁ (f ''ᵁ U.1) := f.preimage_image_eq U.1 |>.ge
    have hinj : Function.Injective
        (fun q : Γ(T, W.1) →+* Γ(Y, f ''ᵁ U.1) ↦
          (f.appIso U.1).hom.hom.comp q) := by
      intro q₁ q₂ hq
      ext r
      apply (ConcreteCategory.bijective_of_isIso (f.appIso U.1).hom).injective
      exact RingHom.congr_fun hq r
    have hmap : (f.appIso U.1).inv.hom.comp b =
        (p.appLE W.1 (f ''ᵁ U.1) hImage).hom := by
      apply hinj
      have hleft : (f.appIso U.1).hom.hom.comp
          ((f.appIso U.1).inv.hom.comp b) = b := by
        ext r
        simp
      exact hleft.trans (by
        rw [Scheme.Hom.appIso_hom']
        change b = (((p.appLE W.1 (f ''ᵁ U.1) hImage) ≫
          f.appLE (f ''ᵁ U.1) U.1 hpre).hom)
        rw [Scheme.Hom.appLE_comp_appLE])
    exact (congrArg
      (fun q : Γ(T, W.1) →+* Γ(Y, f ''ᵁ U.1) ↦ himage ▸ q) hmap).trans
      (Scheme.Hom.appLE_hom_transport p W.1 (f ''ᵁ U.1) V.1
        himage hImage hVW)
  · exact htransport

/-- Eventual flatness of the pieces of `Γ_*(F)` makes the sections of `F` flat on each
standard projective chart. -/
theorem flat_openSections_basicOpen_of_isFlatAbove_gammaStar
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    [∀ e : ℤ, (twistModule 𝒜 G e).IsQuasicoherent]
    {D : ℤ} (hG : GradedModule.IsFlatAbove (gammaStar 𝒜 π G x) D)
    (i : Fin (n + 1)) :
    letI := Scheme.Modules.openSectionsModuleOver π G (basicOpen 𝒜 ((x i : A)))
    Module.Flat R Γ(G, basicOpen 𝒜 ((x i : A))) := by
  letI := Scheme.Modules.openSectionsModuleOver π (twistModule 𝒜 G 0)
    (basicOpen 𝒜 ((x i : A)))
  letI := Scheme.Modules.openSectionsModuleOver π G (basicOpen 𝒜 ((x i : A)))
  haveI hloc : Module.Flat R (((gammaStar 𝒜 π G x).loc [i]).obj 0) :=
    hG.flat_loc_singleton_degree i 0
  haveI htwist : Module.Flat R
      Γ(twistModule 𝒜 G 0, basicOpen 𝒜 ((x i : A))) :=
    Module.Flat.of_linearEquiv (chartColimitEquiv 𝒜 π G x i hcover 0).symm
  exact Module.Flat.of_linearEquiv (chartTwistZeroLinearEquiv 𝒜 π G x i).symm

/-- Eventual flatness of `Γ_*(F)` makes the sections of `F` flat over the coefficient ring
of the affine base on every affine open of `Proj`.  This is the `V = ⊤` local statement
needed to prove relative flatness after restricting the base to an affine open. -/
theorem flat_sections_affine_top_of_isFlatAbove_gammaStar
    [G.IsQuasicoherent]
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    [∀ e : ℤ, (twistModule 𝒜 G e).IsQuasicoherent]
    {D : ℤ} (hG : GradedModule.IsFlatAbove (gammaStar 𝒜 π G x) D)
    (U : (Proj 𝒜).affineOpens) :
    letI := Module.compHom Γ(G, U.1) (π.appLE ⊤ U.1 le_top).hom
    Module.Flat Γ(Spec R, ⊤) Γ(G, U.1) := by
  apply Scheme.Modules.FlatOver.flat_sections_affine_of_pointwise_basicOpen
    π G U ⟨⊤, isAffineOpen_top _⟩ le_top
  intro p hpU
  have hpcover : p ∈ ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)) :=
    hcover (show p ∈ (⊤ : (Proj 𝒜).Opens) by trivial)
  rw [Opens.mem_iSup] at hpcover
  obtain ⟨i, hpi⟩ := hpcover
  let W : (Proj 𝒜).affineOpens :=
    ⟨basicOpen 𝒜 ((x i : A)), isAffineOpen_basicOpen 𝒜 _ (x i).2 Nat.one_pos⟩
  obtain ⟨r, s, hrs, hpr⟩ :=
    exists_basicOpen_le_affine_inter U.2 W.2 p ⟨hpU, hpi⟩
  refine ⟨r, hpr, ?_⟩
  have hchartR :
      letI := Scheme.Modules.openSectionsModuleOver π G W.1
      Module.Flat R Γ(G, W.1) := by
    exact flat_openSections_basicOpen_of_isFlatAbove_gammaStar
      𝒜 π G x hcover hG i
  let eR := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  let aR : R →+* Γ(Proj 𝒜, W.1) := (Scheme.Modules.openRingHom π W.1).hom
  let bW : Γ(Spec R, ⊤) →+* Γ(Proj 𝒜, W.1) :=
    (π.appLE ⊤ W.1 le_top).hom
  have hcoeff : bW.comp eR.toRingHom = aR := by
    rfl
  have hchart :
      letI := Module.compHom Γ(G, W.1) bW
      Module.Flat Γ(Spec R, ⊤) Γ(G, W.1) :=
    (Module.Flat.compHom_ringEquiv_iff eR aR bW hcoeff).mp hchartR
  have hsflat := Scheme.Modules.flat_basicOpen_of_flat_affineOpen
    π G W hchart s
  have htransport :
      let a' : Γ(Spec R, ⊤) →+* Γ(Proj 𝒜, (Proj 𝒜).basicOpen r) :=
        hrs.symm ▸ (π.appLE ⊤ ((Proj 𝒜).basicOpen s) le_top).hom
      letI := Module.compHom Γ(G, (Proj 𝒜).basicOpen r) a'
      Module.Flat Γ(Spec R, ⊤) Γ(G, (Proj 𝒜).basicOpen r) :=
    Scheme.Modules.sections_flat_of_eq G ((Proj 𝒜).basicOpen s)
      ((Proj 𝒜).basicOpen r) hrs.symm
      (π.appLE ⊤ ((Proj 𝒜).basicOpen s) le_top).hom hsflat
  apply Module.Flat.compHom_congr
    (hrs.symm ▸ (π.appLE ⊤ ((Proj 𝒜).basicOpen s) le_top).hom)
    (π.appLE ⊤ ((Proj 𝒜).basicOpen r) le_top).hom
  · exact Scheme.Hom.appLE_hom_transport π ⊤
      ((Proj 𝒜).basicOpen s) ((Proj 𝒜).basicOpen r)
      hrs.symm le_top le_top
  · exact htransport

/-- The coefficient-ring form of
`flat_sections_affine_top_of_isFlatAbove_gammaStar`. -/
theorem flat_openSections_affine_of_isFlatAbove_gammaStar
    [G.IsQuasicoherent]
    (hcover : (⊤ : (Proj 𝒜).Opens) ≤ ⨆ k : Fin (n + 1), basicOpen 𝒜 ((x k : A)))
    [∀ e : ℤ, (twistModule 𝒜 G e).IsQuasicoherent]
    {D : ℤ} (hG : GradedModule.IsFlatAbove (gammaStar 𝒜 π G x) D)
    (U : (Proj 𝒜).affineOpens) :
    letI := Scheme.Modules.openSectionsModuleOver π G U.1
    Module.Flat R Γ(G, U.1) := by
  let eR := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  let aR : R →+* Γ(Proj 𝒜, U.1) := (Scheme.Modules.openRingHom π U.1).hom
  let b : Γ(Spec R, ⊤) →+* Γ(Proj 𝒜, U.1) :=
    (π.appLE ⊤ U.1 le_top).hom
  have hcoeff : b.comp eR.toRingHom = aR := by
    rfl
  apply (Module.Flat.compHom_ringEquiv_iff eR aR b hcoeff).mpr
  exact flat_sections_affine_top_of_isFlatAbove_gammaStar
    𝒜 π G x hcover hG U

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- For the canonical affine chart `Spec Γ(T,V) ⟶ T`, the coefficient map from
`Γ(T,V)` to sections over a scheme above that chart is the usual coefficient map over
`Spec Γ(T,V)`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.openRingHom_eq_appLE_fromSpec
    {T X : Scheme.{u}} (V : T.affineOpens)
    (p : X ⟶ Spec (.of Γ(T, V.1))) (U : X.Opens)
    (hU : U ≤ (p ≫ V.2.fromSpec) ⁻¹ᵁ V.1) :
    (Scheme.Modules.openRingHom p U).hom =
      ((p ≫ V.2.fromSpec).appLE V.1 U hU).hom := by
  let g := V.2.fromSpec
  have hg : (⊤ : (Spec (.of Γ(T, V.1))).Opens) ≤ g ⁻¹ᵁ V.1 := by
    intro x _
    change V.1.ι (V.2.isoSpec.inv x) ∈ V.1
    exact (V.2.isoSpec.inv x).2
  have hcoeff : (g.appLE V.1 ⊤ hg).hom =
      algebraMap Γ(T, V.1) Γ(Spec (.of Γ(T, V.1)), ⊤) := by
    exact V.2.fromSpec_appLE_eq_algebraMap ⊤
  have hleft : (Scheme.Modules.openRingHom p U).hom =
      ((g.appLE V.1 ⊤ hg ≫ p.appLE ⊤ U le_top).hom) := by
    apply RingHom.ext
    intro r
    change (Scheme.Modules.openRingHom p U).hom r =
      ((p.appLE ⊤ U le_top).hom.comp (g.appLE V.1 ⊤ hg).hom) r
    rw [hcoeff]
    rfl
  have hcomp : ((g.appLE V.1 ⊤ hg ≫ p.appLE ⊤ U le_top).hom) =
      ((p ≫ g).appLE V.1 U hU).hom := by
    exact congrArg CommRingCat.Hom.hom
      (Scheme.Hom.appLE_comp_appLE p g V.1 ⊤ U hg le_top)
  exact hleft.trans hcomp

/-- Eventual flatness of the intrinsic polynomial `Γ_*` of a quasicoherent sheaf on
relative projective space over `Spec R` makes its sections on every affine open flat over
the global sections of `Spec R`. -/
theorem flat_sections_affine_top_of_isFlatAbove_gammaStarPull
    (n : ℕ) (R : Type u) [CommRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
    [Q.IsQuasicoherent] {D : ℤ}
    (hG : GradedModule.IsFlatAbove
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (Proj.polynomialToSpec (Fin (n + 1)) R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
        (stdVars n R)) D)
    (U : (Scheme.projectiveSpaceOver n (Spec (.of R))).affineOpens) :
    letI := Module.compHom Γ(Q, U.1)
      ((Scheme.projectiveSpaceOverπ n (Spec (.of R))).appLE ⊤ U.1 le_top).hom
    Module.Flat Γ(Spec (.of R), ⊤) Γ(Q, U.1) := by
  let e := projectiveSpaceOverSpecIso n R
  let p := Scheme.projectiveSpaceOverπ n (Spec (.of R))
  let G := (Scheme.Modules.pullback e.inv).obj Q
  let U' : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).affineOpens :=
    ⟨e.inv ⁻¹ᵁ U.1, U.2.preimage e.inv⟩
  letI : G.IsQuasicoherent := by
    dsimp only [G]
    infer_instance
  letI (d : ℤ) :
      (ProjectiveSpectrum.Twist.twistModule
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) G d).IsQuasicoherent :=
    twistModule_std_isQuasicoherent_of_isQuasicoherent n G d
  have hraw :
      letI := Module.compHom Γ(G, U'.1)
        ((Proj.polynomialToSpec (Fin (n + 1)) R).appLE ⊤ U'.1 le_top).hom
      Module.Flat Γ(Spec (.of R), ⊤) Γ(G, U'.1) :=
    Proj.flat_sections_affine_top_of_isFlatAbove_gammaStar
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (Proj.polynomialToSpec (Fin (n + 1)) R) G (stdVars n R)
        (top_le_iSup_basicOpen_stdVars n R) hG U'
  have hsource :
      letI := Module.compHom Γ(G, U'.1)
        ((e.inv ≫ p).appLE ⊤ U'.1 le_top).hom
      Module.Flat Γ(Spec (.of R), ⊤) Γ(G, U'.1) := by
    apply Module.Flat.compHom_congr
      ((Proj.polynomialToSpec (Fin (n + 1)) R).appLE ⊤ U'.1 le_top).hom
      ((e.inv ≫ p).appLE ⊤ U'.1 le_top).hom
    · rw [projectiveSpaceOverSpecIso_inv_comp_projectiveSpaceOverπ]
    · exact hraw
  exact Scheme.Modules.flat_sections_affine_of_pullback_isIso
    e.inv Q p U hsource

/-- The coefficient-ring form of
`flat_sections_affine_top_of_isFlatAbove_gammaStarPull`. -/
theorem flat_openSections_affine_of_isFlatAbove_gammaStarPull
    (n : ℕ) (R : Type u) [CommRing R]
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules)
    [Q.IsQuasicoherent] {D : ℤ}
    (hG : GradedModule.IsFlatAbove
      (Proj.gammaStar (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (Proj.polynomialToSpec (Fin (n + 1)) R)
        ((Scheme.Modules.pullback (projectiveSpaceOverSpecIso n R).inv).obj Q)
        (stdVars n R)) D)
    (U : (Scheme.projectiveSpaceOver n (Spec (.of R))).affineOpens) :
    letI := Scheme.Modules.openSectionsModuleOver
      (Scheme.projectiveSpaceOverπ n (Spec (.of R))) Q U.1
    Module.Flat R Γ(Q, U.1) := by
  let p := Scheme.projectiveSpaceOverπ n (Spec (.of R))
  let eR := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  let aR : R →+* Γ(Scheme.projectiveSpaceOver n (Spec (.of R)), U.1) :=
    (Scheme.Modules.openRingHom p U.1).hom
  let b : Γ(Spec (.of R), ⊤) →+*
      Γ(Scheme.projectiveSpaceOver n (Spec (.of R)), U.1) :=
    (p.appLE ⊤ U.1 le_top).hom
  have hcoeff : b.comp eR.toRingHom = aR := by
    rfl
  apply (Module.Flat.compHom_ringEquiv_iff eR aR b hcoeff).mpr
  exact flat_sections_affine_top_of_isFlatAbove_gammaStarPull n R Q hG U

/-- A quasicoherent sheaf on relative projective space is flat over the base if, after
restriction to the projective space over every affine base chart and transport to
polynomial `Proj`, its `Γ_*` is degreewise flat in all sufficiently large degrees. -/
theorem flatOver_of_isFlatAbove_gammaStarPull_on_affineOpens
    (n : ℕ) (T : Scheme.{u})
    (Q : (Scheme.projectiveSpaceOver n T).Modules) [Q.IsQuasicoherent]
    (hflat : ∀ V : T.affineOpens,
      ∃ D : ℤ, GradedModule.IsFlatAbove
        (Proj.gammaStar
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) Γ(T, V.1))
          (Proj.polynomialToSpec (Fin (n + 1)) Γ(T, V.1))
          ((Scheme.Modules.pullback
            (projectiveSpaceOverSpecIso n Γ(T, V.1)).inv).obj
              ((Scheme.Modules.pullback
                (Scheme.projectiveSpaceOverMap n V.2.fromSpec)).obj Q))
          (stdVars n Γ(T, V.1))) D) :
    Q.FlatOver (Scheme.projectiveSpaceOverπ n T) := by
  intro U V hUV
  let R : Type u := Γ(T, V.1)
  let g : Spec (.of R) ⟶ T := V.2.fromSpec
  let m := Scheme.projectiveSpaceOverMap n g
  let pR := Scheme.projectiveSpaceOverπ n (Spec (.of R))
  let π := Scheme.projectiveSpaceOverπ n T
  let QV := (Scheme.Modules.pullback m).obj Q
  haveI : IsOpenImmersion g := by
    dsimp only [g]
    infer_instance
  haveI : IsOpenImmersion m := by
    dsimp only [m]
    infer_instance
  haveI : QV.IsQuasicoherent := by
    dsimp only [QV]
    infer_instance
  have hmrange : m.opensRange = π ⁻¹ᵁ V.1 := by
    let e := Scheme.projectiveSpaceOverAffineOpenIso n V
    let j := (π ⁻¹ᵁ V.1).ι
    have hfac : e.hom ≫ j = m := by
      simpa only [e, j, m, π, g, IsAffineOpen.fromSpec] using
        Scheme.projectiveSpaceOverAffineOpenIso_hom_ι n V
    apply TopologicalSpace.Opens.ext
    change Set.range m.base = (π ⁻¹ᵁ V.1 : Set _)
    rw [← hfac, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    have hsurj : Set.range e.hom.base = Set.univ := by
      refine Set.range_eq_univ.mpr (fun y ↦ ⟨e.inv.base y, ?_⟩)
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    change j.base '' Set.range e.hom.base = (π ⁻¹ᵁ V.1 : Set _)
    have hjrange : Set.range j.base = (π ⁻¹ᵁ V.1 : Set _) := by
      dsimp only [j]
      exact Scheme.Opens.range_ι (π ⁻¹ᵁ V.1)
    exact (congrArg (fun Z ↦ j.base '' Z) hsurj).trans
      (Set.image_univ.trans hjrange)
  have hUrange : U.1 ≤ m.opensRange := by
    rw [hmrange]
    exact hUV
  let U' : (Scheme.projectiveSpaceOver n (Spec (.of R))).affineOpens :=
    ⟨m ⁻¹ᵁ U.1, U.2.preimage_of_isOpenImmersion m hUrange⟩
  let hU'V : U'.1 ≤ (m ≫ π) ⁻¹ᵁ V.1 := by
    intro x hx
    exact hUV hx
  obtain ⟨D, hD⟩ := hflat V
  have hlocal :
      letI := Scheme.Modules.openSectionsModuleOver pR QV U'.1
      Module.Flat R Γ(QV, U'.1) := by
    exact flat_openSections_affine_of_isFlatAbove_gammaStarPull
      n R QV hD U'
  have hpV : U'.1 ≤ (pR ≫ g) ⁻¹ᵁ V.1 := by
    rw [← Scheme.projectiveSpaceOverMap_π n g]
    exact hU'V
  have hcoeff : (Scheme.Modules.openRingHom pR U'.1).hom =
      ((m ≫ π).appLE V.1 U'.1 hU'V).hom := by
    have hcoeff' := Scheme.Modules.openRingHom_eq_appLE_fromSpec V pR U'.1 hpV
    simpa only [m, π, pR, g, Scheme.projectiveSpaceOverMap_π] using hcoeff'
  have hlocal' :
      letI := Module.compHom Γ(QV, U'.1)
        ((m ≫ π).appLE V.1 U'.1 hU'V).hom
      Module.Flat R Γ(QV, U'.1) := by
    exact Module.Flat.compHom_congr
      (Scheme.Modules.openRingHom pR U'.1).hom
      ((m ≫ π).appLE V.1 U'.1 hU'V).hom hcoeff hlocal
  exact Scheme.Modules.flat_sections_affine_of_pullback_openImmersion_appLE
    m Q π U V hUV hUrange hlocal'

end AlgebraicGeometry.ProjectiveSpace

end

end
