module

public import StacksAndModuli.API.FinitePresentationSmoothDescent
public import StacksAndModuli.API.FormallyUnramifiedSourceLocal
public import StacksAndModuli.«Section3.1-Descent».«part3.1.5-descending-properties»

/-!
# Source locality along surjective smooth and étale morphisms

This file packages source-locality for locally finite presentation and smoothness along
a surjective smooth morphism, and hence also along a surjective étale morphism.  The
finite-presentation step uses the
specialized, axiom-free smooth faithfully flat cancellation theorem from
`StacksAndModuli/API/FinitePresentationSmoothDescent.lean`; in particular, none of the results
below depends on the unresolved general finite-presentation permanence theorem 02KK.

The two final equivalences are the forms used when comparing scheme charts of algebraic
spaces.  The covering morphism is always surjective and étale; the property being
descended is either surjective-étale or surjective-smooth.

## Main results

* `AlgebraicGeometry.LocallyOfFinitePresentation.of_surjective_etale_precomp`
* `AlgebraicGeometry.LocallyOfFinitePresentation.of_surjective_smooth_precomp`
* `AlgebraicGeometry.Smooth.of_surjective_etale_precomp`
* `AlgebraicGeometry.Smooth.of_surjective_smooth_precomp`
* `AlgebraicGeometry.Etale.of_surjective_etale_precomp`
* `AlgebraicGeometry.surjectiveEtale_iff_comp_of_surjectiveEtale`
* `AlgebraicGeometry.surjectiveSmooth_iff_comp_of_surjectiveEtale`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- Local finite presentation descends through precomposition by a surjective smooth
morphism.  The proof refines the pulled-back cover over each affine chart to a finite
affine coproduct, then applies smooth faithfully flat finite-presentation cancellation
on coordinate rings. -/
theorem LocallyOfFinitePresentation.of_surjective_smooth_precomp
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Surjective g] [Smooth g] [LocallyOfFinitePresentation (g ≫ f)] :
    LocallyOfFinitePresentation f := by
  constructor
  intro U hU V hV e
  let fVU := f.resLE U V e
  letI : IsAffine V := hV
  letI : IsAffine U := hU
  let gV := pullback.fst V.ι g
  haveI : Surjective gV := inferInstance
  haveI : Smooth gV := inferInstance
  let 𝒰 : Scheme.Cover (Scheme.precoverage (⊤ : MorphismProperty Scheme.{u})) V :=
    Scheme.Cover.mkOfCovers PUnit (fun _ ↦ pullback V.ι g) (fun _ ↦ gV)
      (fun x ↦ ⟨PUnit.unit, (gV.surjective x).choose,
        (gV.surjective x).choose_spec⟩)
      (fun _ ↦ trivial)
  letI : QuasiCompactCover 𝒰.toPreZeroHypercover :=
    QuasiCompactCover.of_isOpenMap fun _ ↦ gV.isOpenMap
  letI : IsZariskiLocalAtSource
      (@Smooth : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  letI : MorphismProperty.IsStableUnderBaseChange
      (@Smooth : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.isStableUnderBaseChange RingHom.Smooth.isStableUnderBaseChange
  letI : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.isStableUnderBaseChange
      RingHom.finitePresentation_isStableUnderBaseChange
  letI : MorphismProperty.HasOfPostcompProperty
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      (MorphismProperty.monomorphisms Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
  letI : MorphismProperty.HasOfPostcompProperty
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
    MorphismProperty.HasOfPostcompProperty.of_le
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
      (.monomorphisms Scheme.{u}) (fun _ _ i hi ↦ by
        letI : IsOpenImmersion i := hi
        infer_instance)
  letI : MorphismProperty.RespectsLeft (⊤ : MorphismProperty Scheme.{u})
      (@IsOpenImmersion : MorphismProperty Scheme.{u}) :=
    { precomp := fun _ _ _ _ ↦ trivial }
  obtain ⟨𝒱, r, hfin, hr⟩ := QuasiCompactCover.exists_hom 𝒰
  letI : Finite 𝒱.I₀ := hfin
  let p : (∐ fun j ↦ Spec (𝒱.X j)) ⟶ V := Sigma.desc 𝒱.f
  haveI : Surjective p := by
    change Surjective (Sigma.desc fun i ↦ 𝒱.cover.f i)
    infer_instance
  haveI : Smooth p := by
    apply IsZariskiLocalAtSource.sigmaDesc (P := (@Smooth : MorphismProperty Scheme.{u}))
    intro j
    let j' : 𝒱.cover.I₀ := j
    change Smooth (𝒱.cover.f j')
    rw [← r.w₀ j']
    change Smooth (r.h₀ j' ≫ gV)
    letI : IsOpenImmersion (r.h₀ j') := hr j'
    exact MorphismProperty.comp_mem (@Smooth : MorphismProperty Scheme.{u})
      (r.h₀ j') gV
      (HasRingHomProperty.of_isOpenImmersion
        RingHom.Smooth.holdsForLocalizationAway.containsIdentities)
      (show Smooth gV from inferInstance)
  have hpcomp : LocallyOfFinitePresentation (p ≫ fVU) := by
    change LocallyOfFinitePresentation (Sigma.desc 𝒱.f ≫ fVU)
    have hpieces : ∀ j, LocallyOfFinitePresentation (𝒱.f j ≫ fVU) := by
      intro j
      let j' : 𝒱.cover.I₀ := j
      apply MorphismProperty.of_postcomp
        (W := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
        (W' := (@IsOpenImmersion : MorphismProperty Scheme.{u}))
        (𝒱.f j ≫ fVU) U.ι inferInstance
      rw [Category.assoc]
      change LocallyOfFinitePresentation (𝒱.cover.f j' ≫ fVU ≫ U.ι)
      rw [← r.w₀ j']
      rw [Scheme.Hom.resLE_comp_ι]
      let q : 𝒰.X (r.s₀ j') ⟶ X' := by
        change pullback V.ι g ⟶ X'
        exact pullback.snd V.ι g
      have hq : 𝒰.f (r.s₀ j') ≫ V.ι = q ≫ g := by
        change pullback.fst V.ι g ≫ V.ι = pullback.snd V.ι g ≫ g
        exact pullback.condition
      change LocallyOfFinitePresentation
        (r.h₀ j' ≫ 𝒰.f (r.s₀ j') ≫ V.ι ≫ f)
      rw [show r.h₀ j' ≫ 𝒰.f (r.s₀ j') ≫ V.ι ≫ f =
        r.h₀ j' ≫ q ≫ g ≫ f by
          calc
            _ = (r.h₀ j' ≫ (𝒰.f (r.s₀ j') ≫ V.ι)) ≫ f :=
              congrArg (fun k ↦ k ≫ f)
                (Category.assoc (r.h₀ j') (𝒰.f (r.s₀ j')) V.ι)
            _ = (r.h₀ j' ≫ (q ≫ g)) ≫ f := by rw [hq]
            _ = _ := congrArg (fun k ↦ k ≫ f)
              (Category.assoc (r.h₀ j') q g).symm]
      letI : IsOpenImmersion (r.h₀ j') := hr j'
      letI : IsOpenImmersion q := by
        change IsOpenImmersion (pullback.snd V.ι g)
        infer_instance
      have hqfp : LocallyOfFinitePresentation q :=
        HasRingHomProperty.of_isOpenImmersion
          RingHom.finitePresentation_holdsForLocalizationAway.containsIdentities
      exact MorphismProperty.comp_mem
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
        (r.h₀ j' ≫ q) (g ≫ f)
        (MorphismProperty.comp_mem
          (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
          (r.h₀ j') q inferInstance hqfp) inferInstance
    have hall : LocallyOfFinitePresentation (Sigma.desc fun j ↦ 𝒱.f j ≫ fVU) :=
      IsZariskiLocalAtSource.sigmaDesc
        (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})) hpieces
    rw [← show Sigma.desc (fun j ↦ 𝒱.f j ≫ fVU) = Sigma.desc 𝒱.f ≫ fVU by
      ext j
      simp]
    exact hall
  letI := hpcomp
  have hfVU : LocallyOfFinitePresentation fVU := by
    apply HasRingHomProperty.iff_of_isAffine.mpr
    apply RingHom.FinitePresentation.of_comp_of_smooth_of_faithfullyFlat
      fVU.appTop.hom p.appTop.hom
    · rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop]
      exact HasRingHomProperty.appTop @LocallyOfFinitePresentation (p ≫ fVU)
        inferInstance
    · exact HasRingHomProperty.appTop @Smooth p inferInstance
    · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine p).mp
        ⟨inferInstance, inferInstance⟩
  exact RingHom.finitePresentation_respectsIso.arrow_mk_iso_iff
    (arrowResLEAppIso f U V e) |>.mp
      (HasRingHomProperty.appTop
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) fVU hfVU)

/-- Local finite presentation descends through precomposition by a surjective étale
morphism. -/
theorem LocallyOfFinitePresentation.of_surjective_etale_precomp
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Surjective g] [Etale g] [LocallyOfFinitePresentation (g ≫ f)] :
    LocallyOfFinitePresentation f := by
  haveI : Smooth g := inferInstance
  exact LocallyOfFinitePresentation.of_surjective_smooth_precomp g f

/-- Smoothness descends through precomposition by a surjective smooth morphism. -/
theorem Smooth.of_surjective_smooth_precomp
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Surjective g] [Smooth g] [Smooth (g ≫ f)] : Smooth f := by
  letI : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.of_surjective_smooth_precomp g f
  letI : Flat f := (flat_comp_iff_of_surjective_flat g f).mp inferInstance
  apply Smooth.of_smooth_fiberToSpecResidueField
  intro y
  let K := Y.residueField y
  let Ω : Type u := AlgebraicClosure K
  let t : Spec (.of Ω) ⟶ Spec (.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let q : f.fiber y ⟶ Spec (.of (Y.residueField y)) := f.fiberToSpecResidueField y
  letI : LocallyOfFinitePresentation q :=
    MorphismProperty.pullback_snd f (Y.fromSpecResidueField y) inferInstance
  letI : LocallyOfFinitePresentation (pullback.snd q t) := inferInstance
  have hs : Smooth (pullback.snd q t) := by
    apply Scheme.smooth_toSpec_of_isAlgClosed_of_forall_isRegularLocalRing
    intro x
    exact g.isRegularLocalRing_stalk_geometricFiber_of_smooth_fpqc_precomp f y Ω x
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := q) (g := t) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hs

/-- Smoothness descends through precomposition by a surjective étale morphism. -/
theorem Smooth.of_surjective_etale_precomp
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Surjective g] [Etale g] [Smooth (g ≫ f)] : Smooth f := by
  haveI : Smooth g := inferInstance
  exact Smooth.of_surjective_smooth_precomp g f

/-- Étaleness descends through precomposition by a surjective étale morphism. -/
theorem Etale.of_surjective_etale_precomp
    {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)
    [Surjective g] [Etale g] [Etale (g ≫ f)] : Etale f := by
  haveI : Flat f := (flat_comp_iff_of_surjective_flat g f).mp inferInstance
  haveI : LocallyOfFinitePresentation f :=
    LocallyOfFinitePresentation.of_surjective_etale_precomp g f
  haveI : FormallyUnramified f :=
    formallyUnramified_of_comp_of_smooth_surjective g f inferInstance
  exact Etale.of_formallyUnramified_of_flat f

/-- The property of being surjective and étale is local on the source along a
surjective étale morphism. -/
theorem surjectiveEtale_iff_comp_of_surjectiveEtale
    {X' X Y : Scheme.{u}} (p : X' ⟶ X) (f : X ⟶ Y)
    (hp : (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p) :
    (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) f ↔
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) (p ≫ f) := by
  letI : Surjective p := hp.1
  letI : Etale p := hp.2
  constructor
  · rintro ⟨hfSurjective, hfEtale⟩
    letI : Surjective f := hfSurjective
    letI : Etale f := hfEtale
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hpfSurjective, hpfEtale⟩
    letI : Surjective (p ≫ f) := hpfSurjective
    letI : Etale (p ≫ f) := hpfEtale
    exact ⟨Surjective.of_comp p f, Etale.of_surjective_etale_precomp p f⟩

/-- The property of being surjective and smooth is local on the source along a
surjective étale morphism. -/
theorem surjectiveSmooth_iff_comp_of_surjectiveEtale
    {X' X Y : Scheme.{u}} (p : X' ⟶ X) (f : X ⟶ Y)
    (hp : (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p) :
    (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) f ↔
      (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) (p ≫ f) := by
  letI : Surjective p := hp.1
  letI : Etale p := hp.2
  constructor
  · rintro ⟨hfSurjective, hfSmooth⟩
    letI : Surjective f := hfSurjective
    letI : Smooth f := hfSmooth
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hpfSurjective, hpfSmooth⟩
    letI : Surjective (p ≫ f) := hpfSurjective
    letI : Smooth (p ≫ f) := hpfSmooth
    exact ⟨Surjective.of_comp p f, Smooth.of_surjective_etale_precomp p f⟩

end AlgebraicGeometry
