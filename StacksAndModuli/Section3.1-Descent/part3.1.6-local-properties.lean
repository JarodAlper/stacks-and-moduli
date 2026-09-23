module

public import StacksAndModuli.«Section3.1-Descent».«part3.1.4-descending-schemes»
public import StacksAndModuli.«Section3.1-Descent».«part3.1.4b-effective-descent-schemes»
public import StacksProject.Descent.FiniteAndSmoothnessProperties.«lemma-flat-finitely-presented-permanence-algebra»
public import StacksProject.Descent.FpqcLocalSource.«lemma-flat-fpqc-local-source»
public import StacksProject.Descent.FpqcLocalTarget.«lemma-universally-submersive-local»
public import StacksAndModuli.API.SchemeTheoreticImageFlatBaseChange
public import StacksAndModuli.Util.FpqcCover
public import StacksAndModuli.«Section3.1-Descent».«part3.1.5-descending-properties»
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-!
# Properties of morphisms that are fpqc local on the target

This module formalizes Proposition 3.1.26 (`prop:fpqc-local-properties-on-the-target`) and
Proposition 3.1.27 (`prop:properties-local-on-source`) of §3.1 (Descent theory,
`sec:descent-theory`) of *Stacks and Moduli*.

A morphism `f : S' ⟶ S` is treated as an fpqc covering through the property
`AlgebraicGeometry.Scheme.IsFpqcCover` (the singleton `{f}` belongs to the fpqc precoverage),
defined in `part3.1.3-descending-morphisms`.
The proposition states that for each property `P` in a long list, `X ⟶ S` has `P` if and
only if its base change `X ×_S S' ⟶ S'` does. The "only if" direction is stability under
base change; the "if" direction is descent, expressed through Mathlib's
`MorphismProperty.DescendsAlong`.

Main results:
- the instances of `prop:fpqc-local-properties-on-the-target` for the properties of the
  book's list, as `P (pullback.snd g f) ↔ P g`;
- `AlgebraicGeometry.LocallyOfFinitePresentation.comp_iff_of_fppf`,
  `LocallyOfFiniteType.comp_iff_of_fppf`, `Surjective.comp_iff_of_fppf`,
  `Flat.comp_iff_of_fppf`, `fppf_comp_iff_of_fppf`,
  `Smooth.comp_iff_of_smooth_surjective`, `Etale.comp_iff_of_etale_surjective`,
  `unramified_comp_iff_of_etale_surjective`, and
  `quasiFinite_comp_iff_of_etale_surjective`: the parts of
  `prop:properties-local-on-source`.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section PropFpqcLocalPropertiesOnTheTarget

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.MorphismProperty

open AlgebraicGeometry.Scheme

/-- API lemma used in the proof of Proposition 3.1.26 (general descent
principle): let `P` be a property of morphisms of schemes which is Zariski local on the target,
stable under base change, and descends along surjective flat quasi-compact morphisms. Then
`P` descends along arbitrary fpqc coverings. (Over an affine open of the base, the
quasi-compactness condition of an fpqc covering provides a quasi-compact open of the source
covering it, which is a surjective flat quasi-compact cover.) -/
theorem descendsAlong_fpqcCover (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] :
    P.DescendsAlong Scheme.IsFpqcCover.{u} := by
  apply IsZariskiLocalAtTarget.descendsAlong
  intro R X Y f g hf H
  obtain ⟨V, hV, e⟩ := hf.exists_compact_opens_image_eq (isAffineOpen_top (Spec R))
  haveI : Flat f := by
    have hflat : Presieve.singleton f ∈ Scheme.precoverage @Flat (Spec R) := hf.2
    exact (Scheme.singleton_mem_precoverage_iff (P := @Flat) f).mp hflat |>.2
  refine MorphismProperty.of_isPullback_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (.paste_vert (.of_hasPullback V.ι _) (.of_hasPullback f g)) ⟨⟨?_, inferInstance⟩,
      (quasiCompact_iff_compactSpace _).mpr (isCompact_iff_compactSpace.mp hV)⟩ ?_
  · exact ⟨fun x ↦ by
      obtain ⟨y, hy, ey⟩ := Set.ext_iff.mp e x |>.mpr (Set.mem_univ x)
      exact ⟨⟨y, hy⟩, ey⟩⟩
  · exact IsZariskiLocalAtTarget.of_isPullback (.flip <| .of_hasPullback _ _) H

/-- API lemma used in the proof of Proposition 3.1.26 (general iff
form): for `P` satisfying the hypotheses of `descendsAlong_fpqcCover`, a morphism `g : X ⟶ S`
has `P` if and only if its base change along an fpqc covering `f : S' ⟶ S` does. -/
theorem iff_of_fpqcCover {P : MorphismProperty Scheme.{u}} {S' S : Scheme.{u}} {f : S' ⟶ S}
    (hf : Scheme.IsFpqcCover f) {X : Scheme.{u}} (g : X ⟶ S) [IsZariskiLocalAtTarget P]
    [P.IsStableUnderBaseChange]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] :
    P g ↔ P (pullback.snd g f) := by
  have := descendsAlong_fpqcCover P
  exact (MorphismProperty.iff_of_isPullback (IsPullback.of_hasPullback g f).flip hf).symm

end AlgebraicGeometry.MorphismProperty

namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.MorphismProperty

variable {S' S : Scheme.{u}} {f : S' ⟶ S} (hf : Scheme.IsFpqcCover f)
  {X : Scheme.{u}} (g : X ⟶ S)

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (surjective):
the individual properties of the book's list for which Mathlib provides the descent
along surjective flat quasi-compact morphisms. Each is an instance of `iff_of_fpqcCover`. -/
example : Surjective g ↔ Surjective (pullback.snd g f) :=
  iff_of_fpqcCover (P := @Surjective) hf g

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (isomorphism). -/
example : IsIso g ↔ IsIso (pullback.snd g f) := by
  simpa using iff_of_fpqcCover (P := MorphismProperty.isomorphisms Scheme.{u}) hf g

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (open immersion). -/
example : IsOpenImmersion g ↔ IsOpenImmersion (pullback.snd g f) :=
  iff_of_fpqcCover (P := @IsOpenImmersion) hf g

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (locally of finite type). -/
example : LocallyOfFiniteType g ↔ LocallyOfFiniteType (pullback.snd g f) :=
  iff_of_fpqcCover (P := @LocallyOfFiniteType) hf g

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (locally of finite presentation). -/
example : LocallyOfFinitePresentation g ↔ LocallyOfFinitePresentation (pullback.snd g f) :=
  iff_of_fpqcCover (P := @LocallyOfFinitePresentation) hf g

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (universally closed). -/
example : UniversallyClosed g ↔ UniversallyClosed (pullback.snd g f) :=
  iff_of_fpqcCover (P := @UniversallyClosed) hf g

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (universally open). -/
example : UniversallyOpen g ↔ UniversallyOpen (pullback.snd g f) :=
  iff_of_fpqcCover (P := @UniversallyOpen) hf g

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (universally submersive). -/
example : UniversallySubmersive g ↔ UniversallySubmersive (pullback.snd g f) :=
  iff_of_fpqcCover (P := @UniversallySubmersive) hf g

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (smooth). -/
example : Smooth g ↔ Smooth (pullback.snd g f) :=
  iff_of_fpqcCover (P := @Smooth) hf g

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (étale). -/
example : Etale g ↔ Etale (pullback.snd g f) :=
  iff_of_fpqcCover (P := @Etale) hf g

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (unramified:
formally unramified together with locally of finite type). -/
example :
    (FormallyUnramified g ∧ LocallyOfFiniteType g) ↔
      (FormallyUnramified (pullback.snd g f) ∧
        LocallyOfFiniteType (pullback.snd g f)) := by
  exact and_congr (iff_of_fpqcCover (P := @FormallyUnramified) hf g)
    (iff_of_fpqcCover (P := @LocallyOfFiniteType) hf g)

/-- API lemma used in the proof of Proposition 3.1.26 (quasi-compact):
quasi-compactness descends along surjective flat quasi-compact morphisms. -/
theorem quasiCompact_descendsAlong :
    MorphismProperty.DescendsAlong (@QuasiCompact)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  constructor
  intro A X Y Z fst snd f g h hf hfst
  have hsnd : Surjective snd :=
    MorphismProperty.of_isPullback (P := @Surjective) h hf.1.1
  letI : Surjective snd := hsnd
  constructor
  intro U hU hUc
  have hfpre : IsCompact (f ⁻¹' U) := hf.2.isCompact_preimage U hU hUc
  have hfstpre : IsCompact (fst ⁻¹' (f ⁻¹' U)) :=
    hfst.isCompact_preimage _ (f.continuous.isOpen_preimage _ hU) hfpre
  have himage : IsCompact (snd '' (fst ⁻¹' (f ⁻¹' U))) :=
    hfstpre.image snd.continuous
  suffices snd '' (fst ⁻¹' (f ⁻¹' U)) = g ⁻¹' U by simpa [← this]
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    change g (snd a) ∈ U
    have hw : f (fst a) = g (snd a) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w]
    exact hw ▸ ha
  · intro hy
    obtain ⟨a, ha⟩ := snd.surjective y
    refine ⟨a, ?_, ha⟩
    change f (fst a) ∈ U
    have hw : f (fst a) = g (snd a) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w]
    rw [hw, ha]
    exact hy

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (quasi-compact). -/
example : QuasiCompact g ↔ QuasiCompact (pullback.snd g f) := by
  have := quasiCompact_descendsAlong.{u}
  exact iff_of_fpqcCover (P := @QuasiCompact) hf g

/-- API lemma used in the proof of Proposition 3.1.26 (quasi-separated):
quasi-separatedness descends along surjective flat quasi-compact morphisms. -/
theorem quasiSeparated_descendsAlong :
    MorphismProperty.DescendsAlong (@QuasiSeparated)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  haveI := quasiCompact_descendsAlong.{u}
  rw [quasiSeparated_eq_diagonal_is_quasiCompact]
  infer_instance

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (quasi-separated). -/
example : QuasiSeparated g ↔ QuasiSeparated (pullback.snd g f) := by
  have := quasiSeparated_descendsAlong.{u}
  exact iff_of_fpqcCover (P := @QuasiSeparated) hf g

/-- API lemma used in the proof of Proposition 3.1.26 (closed immersion):
closed immersions descend along surjective flat quasi-compact morphisms. -/
theorem isClosedImmersion_descendsAlong :
    MorphismProperty.DescendsAlong (@IsClosedImmersion)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  let Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
  haveI : MorphismProperty.DescendsAlong (MorphismProperty.monomorphisms Scheme.{u}) Q := by
    rw [← MorphismProperty.diagonal_isomorphisms]
    infer_instance
  constructor
  intro A X Y Z fst snd f g h hf hfst
  have hgmono : Mono g := MorphismProperty.DescendsAlong.of_isPullback h hf
    (inferInstanceAs (Mono fst))
  letI : Mono g := hgmono
  have hguc : UniversallyClosed g := MorphismProperty.DescendsAlong.of_isPullback h hf
    (inferInstanceAs (UniversallyClosed fst))
  have hglft : LocallyOfFiniteType g := MorphismProperty.DescendsAlong.of_isPullback h hf
    (inferInstanceAs (LocallyOfFiniteType fst))
  have hgproper : IsProper g :=
    { toIsSeparated := inferInstance
      toUniversallyClosed := hguc
      toLocallyOfFiniteType := hglft }
  exact (IsClosedImmersion.iff_isProper_and_mono (f := g)).mpr ⟨hgproper, hgmono⟩

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (closed immersion). -/
example : IsClosedImmersion g ↔ IsClosedImmersion (pullback.snd g f) := by
  have := isClosedImmersion_descendsAlong.{u}
  exact iff_of_fpqcCover (P := @IsClosedImmersion) hf g

/-- API lemma used in the proof of Proposition 3.1.26 (monomorphism):
monomorphisms descend along surjective flat quasi-compact morphisms. -/
theorem monomorphisms_descendsAlong :
    MorphismProperty.DescendsAlong (MorphismProperty.monomorphisms Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  rw [← MorphismProperty.diagonal_isomorphisms]
  infer_instance

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (monomorphism). -/
example : Mono g ↔ Mono (pullback.snd g f) := by
  have := monomorphisms_descendsAlong.{u}
  exact iff_of_fpqcCover
    (P := MorphismProperty.monomorphisms Scheme.{u}) hf g

/-- API lemma used in the proof of Proposition 3.1.26 (affine):
affine morphisms descend along surjective flat quasi-compact morphisms. -/
theorem isAffineHom_descendsAlong :
    MorphismProperty.DescendsAlong (@IsAffineHom)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  letI : Pseudofunctor.ObjectProperty.IsLocal
      (fpqcTopology.representableByProperty
        (@IsAffineHom : MorphismProperty Scheme.{u})) fpqcTopology :=
    isLocal_representableByProperty_isAffineHom fpqcTopology le_rfl
  apply CategoryTheory.GrothendieckTopology.representableByProperty_descendsAlong
    (J := fpqcTopology)
  intro X S f hf
  letI : Surjective f := hf.1.1
  letI : Flat f := hf.1.2
  letI : QuasiCompact f := hf.2
  exact Precoverage.generate_mem_toGrothendieck f.singleton_mem_fpqcPrecoverage

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (affine). -/
example : IsAffineHom g ↔ IsAffineHom (pullback.snd g f) := by
  have := isAffineHom_descendsAlong.{u}
  exact iff_of_fpqcCover (P := @IsAffineHom) hf g

/-- API lemma used in the proof of Proposition 3.1.26 (quasi-affine):
quasi-affine morphisms descend along arbitrary singleton fpqc covers.  This direct
`IsFpqcCover` formulation also covers the non-quasi-compact singleton presentations of
an fpqc covering allowed by the book. -/
theorem isQuasiAffineHom_descendsAlong_fpqcCover :
    MorphismProperty.DescendsAlong
      (IsQuasiAffineHom : MorphismProperty Scheme.{u})
      Scheme.IsFpqcCover.{u} := by
  letI : Pseudofunctor.ObjectProperty.IsLocal
      (fpqcTopology.representableByProperty
        (IsQuasiAffineHom : MorphismProperty Scheme.{u})) fpqcTopology :=
    isLocal_representableByProperty_isQuasiAffineHom fpqcTopology le_rfl
  apply CategoryTheory.GrothendieckTopology.representableByProperty_descendsAlong
    (J := fpqcTopology)
  intro X S f hf
  exact Precoverage.generate_mem_toGrothendieck hf

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (quasi-affine). -/
example : IsQuasiAffineHom g ↔ IsQuasiAffineHom (pullback.snd g f) := by
  have := isQuasiAffineHom_descendsAlong_fpqcCover.{u}
  exact (MorphismProperty.pullback_snd_iff
    (P := IsQuasiAffineHom) hf).symm

/-- API lemma used in the proof of Proposition 3.1.26
(quasi-compact locally closed immersion): the conjunction of quasi-compactness
and being an immersion descends along surjective flat quasi-compact morphisms. -/
theorem quasiCompact_isImmersion_descendsAlong :
    MorphismProperty.DescendsAlong
      (@QuasiCompact ⊓ @IsImmersion : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  apply MorphismProperty.DescendsAlong.mk'
  intro X Y Z f g _ hf hfg
  have := quasiCompact_descendsAlong.{u}
  have hgqc : QuasiCompact g :=
    MorphismProperty.of_pullback_fst_of_descendsAlong
      (P := @QuasiCompact) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (f := f) hf hfg.1
  letI : QuasiCompact g := hgqc
  letI : Flat f := hf.1.2
  letI : IsImmersion (pullback.fst f g) := hfg.2
  let a : pullback f g ⟶ pullback f g.imageι :=
    pullback.map f g f g.imageι (𝟙 _) g.toImage (𝟙 _)
      (by simp) (by simp)
  have haopen : IsOpenImmersion a := by
    dsimp [a]
    rw [← Scheme.Hom.toImage_imagePullbackIsoOfFlat_hom f g]
    infer_instance
  have ha : IsPullback a (pullback.snd f g)
      (pullback.snd f g.imageι) g.toImage := by
    exact .of_right (t := .of_hasPullback f g.imageι)
      (by simpa [a] using (.of_hasPullback f g)) (by simp [a])
  have hcover :
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
        (pullback.snd f g.imageι) :=
    MorphismProperty.pullback_snd f g.imageι hf
  have hgo : IsOpenImmersion g.toImage :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := @IsOpenImmersion)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) ha hcover haopen
  letI : IsOpenImmersion g.toImage := hgo
  refine ⟨hgqc, ?_⟩
  rw [← g.toImage_imageι]
  infer_instance

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`)
(quasi-compact locally closed immersion). -/
example :
    (QuasiCompact g ∧ IsImmersion g) ↔
      (QuasiCompact (pullback.snd g f) ∧
        IsImmersion (pullback.snd g f)) := by
  have := quasiCompact_isImmersion_descendsAlong.{u}
  exact iff_of_fpqcCover
    (P := @QuasiCompact ⊓ @IsImmersion) hf g

/-- API lemma used in the proof of Proposition 3.1.26 (separated):
separatedness descends along surjective flat quasi-compact morphisms. -/
theorem isSeparated_descendsAlong :
    MorphismProperty.DescendsAlong (@IsSeparated)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  letI : MorphismProperty.DescendsAlong (@IsClosedImmersion)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
    isClosedImmersion_descendsAlong
  rw [IsSeparated.isSeparated_eq_diagonal_isClosedImmersion]
  infer_instance

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (separated). -/
example : IsSeparated g ↔ IsSeparated (pullback.snd g f) := by
  have := isSeparated_descendsAlong.{u}
  exact iff_of_fpqcCover (P := @IsSeparated) hf g

/-- API lemma used in the proof of Proposition 3.1.26 (proper):
properness descends along surjective flat quasi-compact morphisms. -/
theorem isProper_descendsAlong :
    MorphismProperty.DescendsAlong (@IsProper)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  letI : MorphismProperty.DescendsAlong (@IsSeparated)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
    isSeparated_descendsAlong
  rw [AlgebraicGeometry.isProper_eq]
  infer_instance

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (proper). -/
example : IsProper g ↔ IsProper (pullback.snd g f) := by
  have := isProper_descendsAlong.{u}
  exact iff_of_fpqcCover (P := @IsProper) hf g

/-- API lemma used in the proof of Proposition 3.1.26 (finite):
finiteness descends along surjective flat quasi-compact morphisms. -/
theorem isFinite_descendsAlong :
    MorphismProperty.DescendsAlong (@IsFinite)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  letI : MorphismProperty.DescendsAlong (@IsProper)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
    isProper_descendsAlong
  letI : MorphismProperty.DescendsAlong (@IsAffineHom)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
    isAffineHom_descendsAlong
  rw [IsFinite.eq_isProper_inf_isAffineHom]
  infer_instance

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (finite). -/
example : IsFinite g ↔ IsFinite (pullback.snd g f) := by
  have := isFinite_descendsAlong.{u}
  exact iff_of_fpqcCover (P := @IsFinite) hf g

/-- API lemma used in the proof of Proposition 3.1.26
(locally quasi-finite): local quasi-finiteness descends along surjective flat
quasi-compact morphisms. -/
theorem locallyQuasiFinite_descendsAlong :
    MorphismProperty.DescendsAlong (@LocallyQuasiFinite)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  exact HasRingHomProperty.descendsAlong_flat
    RingHom.QuasiFinite.codescendsAlong_faithfullyFlat_of_ringHom

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`)
(locally quasi-finite; the finite-type factor supplies the clause omitted by
Mathlib's fibrewise `LocallyQuasiFinite`) -/
example :
    (LocallyOfFiniteType g ∧ LocallyQuasiFinite g) ↔
      (LocallyOfFiniteType (pullback.snd g f) ∧
        LocallyQuasiFinite (pullback.snd g f)) := by
  have := locallyQuasiFinite_descendsAlong.{u}
  exact and_congr (iff_of_fpqcCover (P := @LocallyOfFiniteType) hf g)
    (iff_of_fpqcCover (P := @LocallyQuasiFinite) hf g)

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`)
(quasi-finite: quasi-compact and locally quasi-finite). -/
example :
    (QuasiCompact g ∧ LocallyOfFiniteType g ∧ LocallyQuasiFinite g) ↔
      (QuasiCompact (pullback.snd g f) ∧
        LocallyOfFiniteType (pullback.snd g f) ∧
        LocallyQuasiFinite (pullback.snd g f)) := by
  have := quasiCompact_descendsAlong.{u}
  have := locallyQuasiFinite_descendsAlong.{u}
  exact and_congr (iff_of_fpqcCover (P := @QuasiCompact) hf g)
    (and_congr (iff_of_fpqcCover (P := @LocallyOfFiniteType) hf g)
      (iff_of_fpqcCover (P := @LocallyQuasiFinite) hf g))

/-- API lemma used in the proof of Proposition 3.1.26 (flat):
flatness descends along surjective flat quasi-compact morphisms. -/
theorem flat_descendsAlong :
    MorphismProperty.DescendsAlong (@Flat)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  apply HasRingHomProperty.descendsAlong_flat (Q := RingHom.Flat)
  apply RingHom.CodescendsAlong.mk (P := RingHom.Flat)
    (Q := RingHom.FaithfullyFlat) RingHom.Flat.respectsIso
  intro R S T _ _ _ _ _ hff hflat
  rw [RingHom.faithfullyFlat_algebraMap_iff] at hff
  letI := hff
  rw [RingHom.flat_algebraMap_iff] at hflat ⊢
  exact (Module.Flat.iff_flat_tensorProduct R T S).mp hflat

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`) (flat). -/
example : Flat g ↔ Flat (pullback.snd g f) := by
  have := flat_descendsAlong.{u}
  exact iff_of_fpqcCover (P := @Flat) hf g

/- **Proposition 3.1.26** (`prop:fpqc-local-properties-on-the-target`)
(fppf: flat and locally of finite presentation). -/
example :
    (Flat g ∧ LocallyOfFinitePresentation g) ↔
      (Flat (pullback.snd g f) ∧
        LocallyOfFinitePresentation (pullback.snd g f)) := by
  have := flat_descendsAlong.{u}
  exact and_congr (iff_of_fpqcCover (P := @Flat) hf g)
    (iff_of_fpqcCover (P := @LocallyOfFinitePresentation) hf g)

end AlgebraicGeometry.Scheme

end PropFpqcLocalPropertiesOnTheTarget

section PropPropertiesLocalOnSource

open CategoryTheory Limits AlgebraicGeometry

universe u

variable {X' X Y : Scheme.{u}} (g : X' ⟶ X) (f : X ⟶ Y)

/-- Affine reduction used in the proof of Proposition 3.1.27 (part (1), locally of
finite type, affine case): affine case of fppf locality on the source for locally finite
type. Its algebraic input is [Stacks Project, Tag 0367]. -/
theorem AlgebraicGeometry.LocallyOfFiniteType.of_comp_of_fppf_of_isAffine
    [IsAffine X'] [IsAffine X] [IsAffine Y] [Surjective g] [Flat g]
    [LocallyOfFinitePresentation g] [LocallyOfFiniteType (g ≫ f)] :
    LocallyOfFiniteType f := by
  apply HasRingHomProperty.iff_of_isAffine.mpr
  apply RingHom.FiniteType.of_comp_of_faithfullyFlat_finitePresentation_permanence
    f.appTop.hom g.appTop.hom
  · rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop]
    exact HasRingHomProperty.appTop @LocallyOfFiniteType (g ≫ f) inferInstance
  · exact HasRingHomProperty.appTop @LocallyOfFinitePresentation g inferInstance
  · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
      ⟨inferInstance, inferInstance⟩

/-- **Proposition 3.1.27** (`prop:properties-local-on-source`) (part (1), locally of finite
presentation): properties fppf local on the source: for an fppf morphism `g : X' ⟶ X`,
the composite `X' ⟶ X ⟶ Y` is locally of finite presentation if and only if `X ⟶ Y`
is. -/
@[stacks 036N]
theorem AlgebraicGeometry.LocallyOfFinitePresentation.comp_iff_of_fppf [Surjective g]
    [Flat g] [LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation (g ≫ f) ↔ LocallyOfFinitePresentation f := by
  constructor
  · intro hgf
    letI : LocallyOfFinitePresentation (g ≫ f) := hgf
    constructor
    intro U hU V hV e
    let fVU := f.resLE U V e
    letI : IsAffine V := hV
    letI : IsAffine U := hU
    let gV := pullback.fst V.ι g
    haveI : Surjective gV := inferInstance
    haveI : Flat gV := inferInstance
    haveI : LocallyOfFinitePresentation gV := inferInstance
    let 𝒰 : Scheme.Cover (Scheme.precoverage (⊤ : MorphismProperty Scheme.{u})) V :=
      Scheme.Cover.mkOfCovers PUnit (fun _ ↦ pullback V.ι g) (fun _ ↦ gV)
        (fun x ↦ ⟨PUnit.unit, (gV.surjective x).choose,
          (gV.surjective x).choose_spec⟩)
        (fun _ ↦ trivial)
    letI : QuasiCompactCover 𝒰.toPreZeroHypercover :=
      QuasiCompactCover.of_isOpenMap fun _ ↦ gV.isOpenMap
    letI : IsZariskiLocalAtSource
        (@Flat : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
    letI : IsZariskiLocalAtSource
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
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
    haveI : Flat p := by
      change Flat (Sigma.desc 𝒱.f)
      exact IsZariskiLocalAtSource.sigmaDesc
        (P := (@Flat : MorphismProperty Scheme.{u})) fun j ↦ by
          let j' : 𝒱.cover.I₀ := j
          change Flat (𝒱.cover.f j')
          rw [← r.w₀ j']
          change Flat (r.h₀ j' ≫ gV)
          letI : IsOpenImmersion (r.h₀ j') := hr j'
          exact MorphismProperty.comp_mem (@Flat : MorphismProperty Scheme.{u})
            (r.h₀ j') gV
            (HasRingHomProperty.of_isOpenImmersion RingHom.Flat.containsIdentities)
            (show Flat gV from inferInstance)
    haveI : LocallyOfFinitePresentation p := by
      apply IsZariskiLocalAtSource.sigmaDesc
        (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
      intro j
      let j' : 𝒱.cover.I₀ := j
      change LocallyOfFinitePresentation (𝒱.cover.f j')
      rw [← r.w₀ j']
      change LocallyOfFinitePresentation (r.h₀ j' ≫ gV)
      letI : IsOpenImmersion (r.h₀ j') := hr j'
      exact MorphismProperty.comp_mem
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) (r.h₀ j') gV
        (HasRingHomProperty.of_isOpenImmersion
          RingHom.finitePresentation_holdsForLocalizationAway.containsIdentities)
        (show LocallyOfFinitePresentation gV from inferInstance)
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
            (r.h₀ j') q inferInstance hqfp) hgf
      have hall : LocallyOfFinitePresentation (Sigma.desc fun j ↦ 𝒱.f j ≫ fVU) :=
        IsZariskiLocalAtSource.sigmaDesc
          (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})) hpieces
      rw [← show Sigma.desc (fun j ↦ 𝒱.f j ≫ fVU) = Sigma.desc 𝒱.f ≫ fVU by
        ext j
        simp]
      exact hall
    letI := hpcomp
    have hfVU := LocallyOfFinitePresentation.of_comp_of_fppf_of_isAffine p fVU
    exact RingHom.finitePresentation_respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U V e) |>.mp
        (HasRingHomProperty.appTop
          (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) fVU hfVU)
  · intro hf
    letI := hf
    infer_instance

/-- **Proposition 3.1.27** (`prop:properties-local-on-source`) (part (1), locally of finite
type): for an fppf morphism `g : X' ⟶ X`, the composite `X' ⟶ X ⟶ Y` is locally of
finite type if and only if `X ⟶ Y` is. -/
@[stacks 036O]
theorem AlgebraicGeometry.LocallyOfFiniteType.comp_iff_of_fppf [Surjective g] [Flat g]
    [LocallyOfFinitePresentation g] :
    LocallyOfFiniteType (g ≫ f) ↔ LocallyOfFiniteType f := by
  constructor
  · intro hgf
    letI : LocallyOfFiniteType (g ≫ f) := hgf
    constructor
    intro U hU V hV e
    let fVU := f.resLE U V e
    letI : IsAffine V := hV
    letI : IsAffine U := hU
    let gV := pullback.fst V.ι g
    haveI : Surjective gV := inferInstance
    haveI : Flat gV := inferInstance
    haveI : LocallyOfFinitePresentation gV := inferInstance
    let 𝒰 : Scheme.Cover (Scheme.precoverage (⊤ : MorphismProperty Scheme.{u})) V :=
      Scheme.Cover.mkOfCovers PUnit (fun _ ↦ pullback V.ι g) (fun _ ↦ gV)
        (fun x ↦ ⟨PUnit.unit, (gV.surjective x).choose,
          (gV.surjective x).choose_spec⟩)
        (fun _ ↦ trivial)
    letI : QuasiCompactCover 𝒰.toPreZeroHypercover :=
      QuasiCompactCover.of_isOpenMap fun _ ↦ gV.isOpenMap
    letI : IsZariskiLocalAtSource
        (@Flat : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
    letI : IsZariskiLocalAtSource
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
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
    haveI : Flat p := by
      change Flat (Sigma.desc 𝒱.f)
      exact IsZariskiLocalAtSource.sigmaDesc
        (P := (@Flat : MorphismProperty Scheme.{u})) fun j ↦ by
          let j' : 𝒱.cover.I₀ := j
          change Flat (𝒱.cover.f j')
          rw [← r.w₀ j']
          change Flat (r.h₀ j' ≫ gV)
          letI : IsOpenImmersion (r.h₀ j') := hr j'
          exact MorphismProperty.comp_mem (@Flat : MorphismProperty Scheme.{u})
            (r.h₀ j') gV
            (HasRingHomProperty.of_isOpenImmersion RingHom.Flat.containsIdentities)
            (show Flat gV from inferInstance)
    haveI : LocallyOfFinitePresentation p := by
      apply IsZariskiLocalAtSource.sigmaDesc
        (P := (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}))
      intro j
      let j' : 𝒱.cover.I₀ := j
      change LocallyOfFinitePresentation (𝒱.cover.f j')
      rw [← r.w₀ j']
      change LocallyOfFinitePresentation (r.h₀ j' ≫ gV)
      letI : IsOpenImmersion (r.h₀ j') := hr j'
      exact MorphismProperty.comp_mem
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) (r.h₀ j') gV
        (HasRingHomProperty.of_isOpenImmersion
          RingHom.finitePresentation_holdsForLocalizationAway.containsIdentities)
        (show LocallyOfFinitePresentation gV from inferInstance)
    have hpcomp : LocallyOfFiniteType (p ≫ fVU) := by
      change LocallyOfFiniteType (Sigma.desc 𝒱.f ≫ fVU)
      have hpieces : ∀ j, LocallyOfFiniteType (𝒱.f j ≫ fVU) := by
        intro j
        let j' : 𝒱.cover.I₀ := j
        apply MorphismProperty.of_postcomp
          (W := (@LocallyOfFiniteType : MorphismProperty Scheme.{u}))
          (W' := (@IsOpenImmersion : MorphismProperty Scheme.{u}))
          (𝒱.f j ≫ fVU) U.ι inferInstance
        rw [Category.assoc]
        change LocallyOfFiniteType (𝒱.cover.f j' ≫ fVU ≫ U.ι)
        rw [← r.w₀ j']
        rw [Scheme.Hom.resLE_comp_ι]
        let q : 𝒰.X (r.s₀ j') ⟶ X' := by
          change pullback V.ι g ⟶ X'
          exact pullback.snd V.ι g
        have hq : 𝒰.f (r.s₀ j') ≫ V.ι = q ≫ g := by
          change pullback.fst V.ι g ≫ V.ι = pullback.snd V.ι g ≫ g
          exact pullback.condition
        change LocallyOfFiniteType
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
        have hqfp : LocallyOfFiniteType q :=
          HasRingHomProperty.of_isOpenImmersion
            RingHom.finiteType_holdsForLocalizationAway.containsIdentities
        exact MorphismProperty.comp_mem
          (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
          (r.h₀ j' ≫ q) (g ≫ f)
          (MorphismProperty.comp_mem
            (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
            (r.h₀ j') q inferInstance hqfp) hgf
      have hall : LocallyOfFiniteType (Sigma.desc fun j ↦ 𝒱.f j ≫ fVU) :=
        IsZariskiLocalAtSource.sigmaDesc
          (P := (@LocallyOfFiniteType : MorphismProperty Scheme.{u})) hpieces
      rw [← show Sigma.desc (fun j ↦ 𝒱.f j ≫ fVU) = Sigma.desc 𝒱.f ≫ fVU by
        ext j
        simp]
      exact hall
    letI := hpcomp
    have hfVU := LocallyOfFiniteType.of_comp_of_fppf_of_isAffine p fVU
    exact RingHom.finiteType_respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U V e) |>.mp
        (HasRingHomProperty.appTop
          (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) fVU hfVU)
  · intro hf
    letI := hf
    infer_instance

/-- **Proposition 3.1.27** (`prop:properties-local-on-source`) (part (1), surjective):
for an fppf morphism `g : X' ⟶ X`, the composite `X' ⟶ X ⟶ Y` is surjective if and
only if `X ⟶ Y` is. -/
theorem AlgebraicGeometry.Surjective.comp_iff_of_fppf [Surjective g] :
    Surjective (g ≫ f) ↔ Surjective f := by
  refine ⟨fun h ↦ ⟨fun y ↦ ?_⟩, fun _ ↦ inferInstance⟩
  obtain ⟨x, hx⟩ := h.1 y
  exact ⟨g x, by rw [← Scheme.Hom.comp_apply]; exact hx⟩

/-- **Proposition 3.1.27** (`prop:properties-local-on-source`) (part (1), flat):
for an fppf morphism `g : X' ⟶ X`, the composite `X' ⟶ X ⟶ Y` is flat if and only if
`X ⟶ Y` is. -/
theorem AlgebraicGeometry.Flat.comp_iff_of_fppf [Surjective g] [Flat g] :
    Flat (g ≫ f) ↔ Flat f := by
  exact flat_comp_iff_of_surjective_flat g f

/-- **Proposition 3.1.27** (`prop:properties-local-on-source`) (part (1), fppf):
for an fppf morphism `g : X' ⟶ X`, the composite `X' ⟶ X ⟶ Y` is fppf if and
only if `X ⟶ Y` is.  Here the standard fppf property is stated exactly as flatness
together with local finite presentation. -/
theorem AlgebraicGeometry.fppf_comp_iff_of_fppf [Surjective g] [Flat g]
    [LocallyOfFinitePresentation g] :
    (Flat (g ≫ f) ∧ LocallyOfFinitePresentation (g ≫ f)) ↔
      (Flat f ∧ LocallyOfFinitePresentation f) := by
  exact and_congr (Flat.comp_iff_of_fppf g f)
    (LocallyOfFinitePresentation.comp_iff_of_fppf g f)

/-- **Proposition 3.1.27** (`prop:properties-local-on-source`) (part (2), smooth): for a
surjective smooth morphism `g : X' ⟶ X`, the composite `X' ⟶ X ⟶ Y` is smooth if and
only if `X ⟶ Y` is. -/
@[stacks 02KM "smooth case", stacks 036U]
theorem AlgebraicGeometry.Smooth.comp_iff_of_smooth_surjective [Surjective g] [Smooth g] :
    Smooth (g ≫ f) ↔ Smooth f := by
  constructor
  · intro hgf
    letI : Smooth (g ≫ f) := hgf
    exact Smooth.of_fppf_precomp g f
  · intro hf
    letI : Smooth f := hf
    infer_instance

/-- Affine case of étale locality on the source for formal unramifiedness. -/
theorem AlgebraicGeometry.FormallyUnramified.of_comp_of_etale_surjective_of_isAffine
    [IsAffine X'] [IsAffine X] [IsAffine Y] [Surjective g] [Etale g]
    [FormallyUnramified (g ≫ f)] : FormallyUnramified f := by
  apply HasRingHomProperty.iff_of_isAffine.mpr
  apply RingHom.FormallyUnramified.of_comp_of_etale_faithfullyFlat_permanence
    f.appTop.hom g.appTop.hom
  · rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop]
    exact HasRingHomProperty.appTop @FormallyUnramified (g ≫ f) inferInstance
  · exact HasRingHomProperty.appTop @Etale g inferInstance
  · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
      ⟨inferInstance, inferInstance⟩

/-- Helper lemma used in the proof of Proposition 3.1.27 (part (3), formal
unramifiedness):
for a surjective étale morphism `g : X' ⟶ X`, the composite `X' ⟶ X ⟶ Y` is (formally)
unramified if and only if `X ⟶ Y` is. -/
theorem AlgebraicGeometry.FormallyUnramified.comp_iff_of_etale_surjective [Surjective g]
    [Etale g] :
    FormallyUnramified (g ≫ f) ↔ FormallyUnramified f := by
  constructor
  · intro hgf
    letI : FormallyUnramified (g ≫ f) := hgf
    constructor
    intro U hU V hV e
    let fVU := f.resLE U V e
    letI : IsAffine V := hV
    letI : IsAffine U := hU
    let gV := pullback.fst V.ι g
    haveI : Surjective gV := inferInstance
    haveI : Etale gV := inferInstance
    let 𝒰 : Scheme.Cover (Scheme.precoverage (⊤ : MorphismProperty Scheme.{u})) V :=
      Scheme.Cover.mkOfCovers PUnit (fun _ ↦ pullback V.ι g) (fun _ ↦ gV)
        (fun x ↦ ⟨PUnit.unit, (gV.surjective x).choose,
          (gV.surjective x).choose_spec⟩)
        (fun _ ↦ trivial)
    letI : QuasiCompactCover 𝒰.toPreZeroHypercover :=
      QuasiCompactCover.of_isOpenMap fun _ ↦ gV.isOpenMap
    letI : IsZariskiLocalAtSource
        (@Etale : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
    letI : MorphismProperty.IsStableUnderBaseChange
        (@Etale : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.isStableUnderBaseChange
        RingHom.Etale.isStableUnderBaseChange
    letI : MorphismProperty.HasOfPostcompProperty
        (@Etale : MorphismProperty Scheme.{u})
        (MorphismProperty.monomorphisms Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
    letI : MorphismProperty.HasOfPostcompProperty
        (@Etale : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
      MorphismProperty.HasOfPostcompProperty.of_le
        (@Etale : MorphismProperty Scheme.{u})
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
    haveI : Etale p := by
      apply IsZariskiLocalAtSource.sigmaDesc
        (P := (@Etale : MorphismProperty Scheme.{u}))
      intro j
      let j' : 𝒱.cover.I₀ := j
      change Etale (𝒱.cover.f j')
      rw [← r.w₀ j']
      change Etale (r.h₀ j' ≫ gV)
      letI : IsOpenImmersion (r.h₀ j') := hr j'
      exact MorphismProperty.comp_mem
        (@Etale : MorphismProperty Scheme.{u}) (r.h₀ j') gV
        (HasRingHomProperty.of_isOpenImmersion
          RingHom.Etale.containsIdentities)
        (show Etale gV from inferInstance)
    have hpcomp : FormallyUnramified (p ≫ fVU) := by
      change FormallyUnramified (Sigma.desc 𝒱.f ≫ fVU)
      have hpieces : ∀ j, FormallyUnramified (𝒱.f j ≫ fVU) := by
        intro j
        let j' : 𝒱.cover.I₀ := j
        apply MorphismProperty.of_postcomp
          (W := (@FormallyUnramified : MorphismProperty Scheme.{u}))
          (W' := (@IsOpenImmersion : MorphismProperty Scheme.{u}))
          (𝒱.f j ≫ fVU) U.ι inferInstance
        rw [Category.assoc]
        change FormallyUnramified (𝒱.cover.f j' ≫ fVU ≫ U.ι)
        rw [← r.w₀ j']
        rw [Scheme.Hom.resLE_comp_ι]
        let q : 𝒰.X (r.s₀ j') ⟶ X' := by
          change pullback V.ι g ⟶ X'
          exact pullback.snd V.ι g
        have hq : 𝒰.f (r.s₀ j') ≫ V.ι = q ≫ g := by
          change pullback.fst V.ι g ≫ V.ι = pullback.snd V.ι g ≫ g
          exact pullback.condition
        change FormallyUnramified
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
        have hqfp : FormallyUnramified q :=
          HasRingHomProperty.of_isOpenImmersion
            RingHom.FormallyUnramified.holdsForLocalizationAway.containsIdentities
        exact MorphismProperty.comp_mem
          (@FormallyUnramified : MorphismProperty Scheme.{u})
          (r.h₀ j' ≫ q) (g ≫ f)
          (MorphismProperty.comp_mem
            (@FormallyUnramified : MorphismProperty Scheme.{u})
            (r.h₀ j') q inferInstance hqfp) hgf
      have hall : FormallyUnramified (Sigma.desc fun j ↦ 𝒱.f j ≫ fVU) :=
        IsZariskiLocalAtSource.sigmaDesc
          (P := (@FormallyUnramified : MorphismProperty Scheme.{u})) hpieces
      rw [← show Sigma.desc (fun j ↦ 𝒱.f j ≫ fVU) = Sigma.desc 𝒱.f ≫ fVU by
        ext j
        simp]
      exact hall
    letI := hpcomp
    have hfVU := FormallyUnramified.of_comp_of_etale_surjective_of_isAffine p fVU
    exact RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U V e) |>.mp
        (HasRingHomProperty.appTop
          (@FormallyUnramified : MorphismProperty Scheme.{u}) fVU hfVU)
  · intro hf
    letI := hf
    exact MorphismProperty.comp_mem (@FormallyUnramified : MorphismProperty Scheme.{u})
      g f inferInstance hf

/-- **Proposition 3.1.27** (`prop:properties-local-on-source`) (part (3), étale):
for a surjective étale morphism `g : X' ⟶ X`, the composite `X' ⟶ X ⟶ Y` is étale if
and only if `X ⟶ Y` is. -/
@[stacks 036W]
theorem AlgebraicGeometry.Etale.comp_iff_of_etale_surjective [Surjective g] [Etale g] :
    Etale (g ≫ f) ↔ Etale f := by
  constructor
  · intro hgf
    letI : Etale (g ≫ f) := hgf
    haveI : Flat f :=
      (Flat.comp_iff_of_fppf g f).mp (inferInstanceAs (Flat (g ≫ f)))
    haveI : LocallyOfFinitePresentation f :=
      (LocallyOfFinitePresentation.comp_iff_of_fppf g f).mp
        (inferInstanceAs (LocallyOfFinitePresentation (g ≫ f)))
    haveI : FormallyUnramified f :=
      (FormallyUnramified.comp_iff_of_etale_surjective g f).mp
        (inferInstanceAs (FormallyUnramified (g ≫ f)))
    exact Etale.of_formallyUnramified_of_flat f
  · intro hf
    letI : Etale f := hf
    infer_instance

/-- **Proposition 3.1.27** (`prop:properties-local-on-source`) (part (3),
unramified in the standard finite-type sense): for a surjective étale morphism
`g : X' ⟶ X`, the composite `X' ⟶ X ⟶ Y` is unramified if and only if
`X ⟶ Y` is. -/
theorem AlgebraicGeometry.unramified_comp_iff_of_etale_surjective
    [Surjective g] [Etale g] :
    (LocallyOfFiniteType (g ≫ f) ∧ FormallyUnramified (g ≫ f)) ↔
      (LocallyOfFiniteType f ∧ FormallyUnramified f) := by
  exact and_congr (LocallyOfFiniteType.comp_iff_of_fppf g f)
    (FormallyUnramified.comp_iff_of_etale_surjective g f)

/-- Affine case of étale locality on the source for local quasi-finiteness. -/
theorem AlgebraicGeometry.LocallyQuasiFinite.of_comp_of_etale_surjective_of_isAffine
    [IsAffine X'] [IsAffine X] [IsAffine Y] [Surjective g] [Etale g]
    [LocallyQuasiFinite (g ≫ f)] : LocallyQuasiFinite f := by
  apply HasRingHomProperty.iff_of_isAffine.mpr
  apply RingHom.QuasiFinite.of_comp_of_faithfullyFlat_permanence f.appTop.hom g.appTop.hom
  · rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop]
    exact HasRingHomProperty.appTop @LocallyQuasiFinite (g ≫ f) inferInstance
  · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
      ⟨inferInstance, inferInstance⟩

/-- Helper lemma used in the proof of Proposition 3.1.27 (part (3), locally
quasi-finite): for a surjective étale morphism `g : X' ⟶ X`, the composite `X' ⟶ X ⟶ Y`
is locally quasi-finite if and only if `X ⟶ Y` is. -/
@[stacks 03X4]
theorem AlgebraicGeometry.LocallyQuasiFinite.comp_iff_of_etale_surjective [Surjective g]
    [Etale g] :
    LocallyQuasiFinite (g ≫ f) ↔ LocallyQuasiFinite f := by
  constructor
  · intro hgf
    letI : LocallyQuasiFinite (g ≫ f) := hgf
    constructor
    intro U hU V hV e
    let fVU := f.resLE U V e
    letI : IsAffine V := hV
    letI : IsAffine U := hU
    let gV := pullback.fst V.ι g
    haveI : Surjective gV := inferInstance
    haveI : Etale gV := inferInstance
    let 𝒰 : Scheme.Cover (Scheme.precoverage (⊤ : MorphismProperty Scheme.{u})) V :=
      Scheme.Cover.mkOfCovers PUnit (fun _ ↦ pullback V.ι g) (fun _ ↦ gV)
        (fun x ↦ ⟨PUnit.unit, (gV.surjective x).choose,
          (gV.surjective x).choose_spec⟩)
        (fun _ ↦ trivial)
    letI : QuasiCompactCover 𝒰.toPreZeroHypercover :=
      QuasiCompactCover.of_isOpenMap fun _ ↦ gV.isOpenMap
    letI : IsZariskiLocalAtSource
        (@Etale : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
    letI : MorphismProperty.IsStableUnderBaseChange
        (@Etale : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.isStableUnderBaseChange
        RingHom.Etale.isStableUnderBaseChange
    letI : MorphismProperty.HasOfPostcompProperty
        (@Etale : MorphismProperty Scheme.{u})
        (MorphismProperty.monomorphisms Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
    letI : MorphismProperty.HasOfPostcompProperty
        (@Etale : MorphismProperty Scheme.{u}) @IsOpenImmersion :=
      MorphismProperty.HasOfPostcompProperty.of_le
        (@Etale : MorphismProperty Scheme.{u})
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
    haveI : Etale p := by
      apply IsZariskiLocalAtSource.sigmaDesc
        (P := (@Etale : MorphismProperty Scheme.{u}))
      intro j
      let j' : 𝒱.cover.I₀ := j
      change Etale (𝒱.cover.f j')
      rw [← r.w₀ j']
      change Etale (r.h₀ j' ≫ gV)
      letI : IsOpenImmersion (r.h₀ j') := hr j'
      exact MorphismProperty.comp_mem
        (@Etale : MorphismProperty Scheme.{u}) (r.h₀ j') gV
        (HasRingHomProperty.of_isOpenImmersion
          RingHom.Etale.containsIdentities)
        (show Etale gV from inferInstance)
    have hpcomp : LocallyQuasiFinite (p ≫ fVU) := by
      change LocallyQuasiFinite (Sigma.desc 𝒱.f ≫ fVU)
      have hpieces : ∀ j, LocallyQuasiFinite (𝒱.f j ≫ fVU) := by
        intro j
        let j' : 𝒱.cover.I₀ := j
        apply MorphismProperty.of_postcomp
          (W := (@LocallyQuasiFinite : MorphismProperty Scheme.{u}))
          (W' := (@IsOpenImmersion : MorphismProperty Scheme.{u}))
          (𝒱.f j ≫ fVU) U.ι inferInstance
        rw [Category.assoc]
        change LocallyQuasiFinite (𝒱.cover.f j' ≫ fVU ≫ U.ι)
        rw [← r.w₀ j']
        rw [Scheme.Hom.resLE_comp_ι]
        let q : 𝒰.X (r.s₀ j') ⟶ X' := by
          change pullback V.ι g ⟶ X'
          exact pullback.snd V.ι g
        have hq : 𝒰.f (r.s₀ j') ≫ V.ι = q ≫ g := by
          change pullback.fst V.ι g ≫ V.ι = pullback.snd V.ι g ≫ g
          exact pullback.condition
        change LocallyQuasiFinite
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
        have hqfp : LocallyQuasiFinite q :=
          HasRingHomProperty.of_isOpenImmersion
            RingHom.QuasiFinite.holdsForLocalizationAway.containsIdentities
        exact MorphismProperty.comp_mem
          (@LocallyQuasiFinite : MorphismProperty Scheme.{u})
          (r.h₀ j' ≫ q) (g ≫ f)
          (MorphismProperty.comp_mem
            (@LocallyQuasiFinite : MorphismProperty Scheme.{u})
            (r.h₀ j') q inferInstance hqfp) hgf
      have hall : LocallyQuasiFinite (Sigma.desc fun j ↦ 𝒱.f j ≫ fVU) :=
        IsZariskiLocalAtSource.sigmaDesc
          (P := (@LocallyQuasiFinite : MorphismProperty Scheme.{u})) hpieces
      rw [← show Sigma.desc (fun j ↦ 𝒱.f j ≫ fVU) = Sigma.desc 𝒱.f ≫ fVU by
        ext j
        simp]
      exact hall
    letI := hpcomp
    have hfVU := LocallyQuasiFinite.of_comp_of_etale_surjective_of_isAffine p fVU
    exact RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso f U V e) |>.mp
        (HasRingHomProperty.appTop
          (@LocallyQuasiFinite : MorphismProperty Scheme.{u}) fVU hfVU)
  · intro hf
    letI := hf
    letI : LocallyQuasiFinite g :=
      ⟨fun {_} hU {_} hV e ↦ RingHom.QuasiFinite.of_etale_of_ringHom _ (g.etale_appLE hU hV e)⟩
    exact MorphismProperty.comp_mem (@LocallyQuasiFinite : MorphismProperty Scheme.{u})
      g f inferInstance hf

/-- **Proposition 3.1.27** (`prop:properties-local-on-source`) (part (3), locally
quasi-finite in the standard finite-type sense): for a surjective étale morphism
`g : X' ⟶ X`, the composite `X' ⟶ X ⟶ Y` is locally quasi-finite if and only if
`X ⟶ Y` is.  The explicit finite-type factor restores the convention used in the
book, since Mathlib's `LocallyQuasiFinite` class records only the fibrewise clause. -/
theorem AlgebraicGeometry.quasiFinite_comp_iff_of_etale_surjective
    [Surjective g] [Etale g] :
    (LocallyOfFiniteType (g ≫ f) ∧ LocallyQuasiFinite (g ≫ f)) ↔
      (LocallyOfFiniteType f ∧ LocallyQuasiFinite f) := by
  exact and_congr (LocallyOfFiniteType.comp_iff_of_fppf g f)
    (LocallyQuasiFinite.comp_iff_of_etale_surjective g f)

end PropPropertiesLocalOnSource
