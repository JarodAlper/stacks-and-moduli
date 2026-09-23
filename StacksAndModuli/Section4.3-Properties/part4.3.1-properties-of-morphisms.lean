module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.3-fiber-products»
public import StacksAndModuli.API.CommonCover
public import StacksProject.Descent.FpqcLocalSource.«lemma-flat-fpqc-local-source»
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksAndModuli.API.QuasiAffineMorphism
public import StacksAndModuli.API.PrestackProducts
public import StacksAndModuli.API.RepresentableSourceAlgebraicSpace
public import StacksAndModuli.API.PresentationBaseChange
public import StacksAndModuli.API.SmoothRelativeDimensionDescent
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import StacksAndModuli.API.FiniteTypeSourceLocal
public import StacksAndModuli.API.FormallyUnramifiedSourceLocal
public import StacksAndModuli.API.SurjectiveEtaleSourceLocal
public import StacksAndModuli.API.StackPresentationLocalLift
public import StacksAndModuli.API.PresheafFiberProductYoneda
public import StacksAndModuli.API.RelativePresheafOver
public import StacksAndModuli.API.RepresentedSecondFiberBaseChange
public import StacksAndModuli.API.EtaleLocalRepresentability
public import StacksAndModuli.API.SchemeFiberPresentationComparison
public import StacksAndModuli.API.SmoothEtaleRefinement
public import StacksAndModuli.API.AlgebraicStackDiagonalFiniteType
public import StacksAndModuli.API.RelativeDiagonalFaithfulTarget
public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.6-criterion-for-sheaf-to-be-scheme»

/-!
# Properties of morphisms of algebraic stacks

This module formalizes `lem:composition`, `def:properties-of-morphisms-of-stacks`,
`ex:locally-of-finite-type`, `exer:diagonal-locally-of-finite-type` and
`prop:smooth-descent-for-representable-morphisms` of §4.3 (First properties) of *Stacks
and Moduli* (the section carries no
`sec:` label). It corresponds to the subsection "Properties of morphisms", the first
subsection of §4.3.

Main declarations:
- `AlgebraicGeometry.BasedCategory.exists_isAlgebraicSpace_of_representable` and
  `AlgebraicGeometry.BasedFunctor.Representable.comp`: a representable morphism into an
  algebraic space has algebraic-space source, and representable morphisms are closed under
  composition;
- `AlgebraicGeometry.IsLocalOnSourceAlong` and `AlgebraicGeometry.IsLocalOnTargetAlong`:
  a property of morphisms of schemes being local on the source (resp. target) along a
  class of covers (étale, smooth, fppf, fpqc surjections);
- `AlgebraicGeometry.BasedFunctor.HasProperty` (smooth presentations) and
  `HasEtaleProperty` (étale presentations): a
  morphism of algebraic (resp. Deligne–Mumford) stacks having a property `P` of morphisms
  of schemes, tested on presentations;
- smooth descent for representable morphisms
  (`prop:smooth-descent-for-representable-morphisms`), stated per property.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section LemComposition

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ v₄ u₄ u

namespace AlgebraicGeometry

/-- **Lemma 4.3.1** (`lem:composition`) (part (1)): if $\cX \to Y$ is a representable
morphism of prestacks over $\Sch_{\ét}$ and $Y$ is an algebraic space, then $\cX$ is an
algebraic space: $\cX$ is represented by a presheaf on $\Sch$ which is an algebraic
space. -/
theorem BasedCategory.exists_isAlgebraicSpace_of_representable
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} [𝒳.p.IsFiberedInGroupoids]
    {Y : Scheme.{u}ᵒᵖ ⥤ Type u} [IsAlgebraicSpace Y]
    (F : 𝒳 ⥤ᵇ BasedCategory.ofPresheaf Y) (hF : BasedFunctor.Representable F) :
    ∃ X : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace X ∧ 𝒳.IsRepresentedByPresheaf X := by
  exact hF.exists_source_isAlgebraicSpace

/-- **Lemma 4.3.1** (`lem:composition`) (part (2)): the composition of representable
morphisms of prestacks over $\Sch_{\ét}$ is representable. -/
theorem BasedFunctor.Representable.comp {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}
    {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}} {𝒵 : BasedCategory.{v₄, u₄} Scheme.{u}}
    [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids] [𝒵.p.IsFiberedInGroupoids]
    {F : 𝒳 ⥤ᵇ 𝒴} {G : 𝒴 ⥤ᵇ 𝒵} (hF : BasedFunctor.Representable F)
    (hG : BasedFunctor.Representable G) : BasedFunctor.Representable (F.comp G) := by
  intro T g
  obtain ⟨Y, hY, E, hE⟩ := hG T g
  let _ : IsAlgebraicSpace Y := hY
  let _ : E.toFunctor.IsEquivalence := hE
  let a := E.comp (fiberProductFst G g)
  have hπ : BasedFunctor.Representable (BasedCategory.fiberProductSnd F a) :=
    hF.fiberProductSnd a
  obtain ⟨X, hX, H, hH⟩ := hπ.exists_source_isAlgebraicSpace
  let _ : H.toFunctor.IsEquivalence := hH
  let R := fiberProductRightMap F (fiberProductFst G g) E
  let _ : R.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductRightMap F (fiberProductFst G g) E
  let K := (H.comp R).comp (pasteFwd F G g)
  refine ⟨X, hX, K, ?_⟩
  let _ : (H.comp R).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans H.toFunctor R.toFunctor
  exact Functor.isEquivalence_trans (H.comp R).toFunctor
    (pasteFwd F G g).toFunctor

end AlgebraicGeometry

end LemComposition

section DefPropertiesOfMorphismsOfStacks

open CategoryTheory Functor Limits AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry

/-- **Definition 4.3.2** (`def:properties-of-morphisms-of-stacks`) (part (1), local on
the source): let $\cP$ and $\cQ$ be
properties of morphisms of schemes. Then $\cP$ is *local on the source along $\cQ$* if
for every morphism $g \colon X' \to X$ satisfying $\cQ$ and every morphism
$f \colon X \to Y$, the morphism $f$ satisfies $\cP$ if and only if the composition
$g \circ f \colon X' \to Y$ does. For $\cQ$ the class of étale (resp. smooth, fppf,
fpqc) surjections this is the book's "étale (resp. smooth, fppf, fpqc) local on the
source". -/
def IsLocalOnSourceAlong (P Q : MorphismProperty Scheme.{u}) : Prop :=
  ∀ ⦃X' X Y : Scheme.{u}⦄ (g : X' ⟶ X) (f : X ⟶ Y), Q g → (P f ↔ P (g ≫ f))

/-- **Definition 4.3.2** (`def:properties-of-morphisms-of-stacks`) (part (1), local on
the target): let $\cP$ and $\cQ$ be
properties of morphisms of schemes. Then $\cP$ is *local on the target along $\cQ$* if
for every morphism $f \colon X \to Y$ and every morphism $g \colon Y' \to Y$ satisfying
$\cQ$, the morphism $f$ satisfies $\cP$ if and only if the base change
$X \times_Y Y' \to Y'$ does. For $\cQ$ the class of étale (resp. smooth, fppf, fpqc)
surjections this is the book's "étale (resp. smooth, fppf, fpqc) local on the
target". -/
def IsLocalOnTargetAlong (P Q : MorphismProperty Scheme.{u}) : Prop :=
  ∀ ⦃X Y Y' : Scheme.{u}⦄ (f : X ⟶ Y) (g : Y' ⟶ Y), Q g → (P f ↔ P (pullback.snd f g))

/-- A property of morphisms of schemes that is stable under base change and descends
along a class `Q` of morphisms (in the sense of `MorphismProperty.DescendsAlong`) is
local on the target along `Q`. -/
lemma isLocalOnTargetAlong_of_descendsAlong (P Q : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.DescendsAlong Q] : IsLocalOnTargetAlong P Q :=
  fun _ _ _ _ _ hg => (MorphismProperty.pullback_snd_iff hg).symm

/-- Smooth surjections of schemes are surjective, flat and locally of finite
presentation (i.e. fppf). -/
lemma surjective_inf_smooth_le_surjective_inf_flat_inf_locallyOfFinitePresentation :
    (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) ≤
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := by
  rintro X Y f ⟨h₁, h₂⟩
  haveI := h₂
  exact ⟨⟨h₁, inferInstance⟩, inferInstance⟩

/-- Étale surjections of schemes are surjective, flat and locally of finite presentation
(i.e. fppf). -/
lemma surjective_inf_etale_le_surjective_inf_flat_inf_locallyOfFinitePresentation :
    (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) ≤
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) := by
  rintro X Y f ⟨h₁, h₂⟩
  haveI := h₂
  exact ⟨⟨h₁, inferInstance⟩, inferInstance⟩

/-- A property of morphisms of schemes that is stable under base change and satisfies
fppf descent (in the sense of `MorphismProperty.DescendsAlong`) is local on the target
along smooth surjections. -/
lemma isLocalOnTargetAlong_surjective_inf_smooth_of_descendsAlong
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})] :
    IsLocalOnTargetAlong P (@Surjective ⊓ @Smooth) := by
  haveI := MorphismProperty.DescendsAlong.of_le
    (P := P) (W := (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}))
    surjective_inf_smooth_le_surjective_inf_flat_inf_locallyOfFinitePresentation
  exact isLocalOnTargetAlong_of_descendsAlong P _

/-- A property of morphisms of schemes that is stable under base change and satisfies
fppf descent (in the sense of `MorphismProperty.DescendsAlong`) is local on the target
along étale surjections. -/
lemma isLocalOnTargetAlong_surjective_inf_etale_of_descendsAlong
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.DescendsAlong
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u})] :
    IsLocalOnTargetAlong P (@Surjective ⊓ @Etale) := by
  haveI := MorphismProperty.DescendsAlong.of_le
    (P := P) (W := (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}))
    surjective_inf_etale_le_surjective_inf_flat_inf_locallyOfFinitePresentation
  exact isLocalOnTargetAlong_of_descendsAlong P _

/-- Background hypothesis bundle for Definition 4.3.2, part (2), in the smooth case:
a property of morphisms of schemes respects isomorphisms, is stable under composition
and base change, and is smooth local on the source and target. -/
structure IsSmoothLocal (P : MorphismProperty Scheme.{u}) : Prop where
  /-- `P` respects isomorphisms. -/
  respectsIso : P.RespectsIso
  /-- `P` is stable under composition. -/
  isStableUnderComposition : P.IsStableUnderComposition
  /-- `P` is stable under base change. -/
  isStableUnderBaseChange : P.IsStableUnderBaseChange
  /-- `P` is smooth local on the source. -/
  isLocalOnSourceAlong : IsLocalOnSourceAlong P (@Surjective ⊓ @Smooth)
  /-- `P` is smooth local on the target. -/
  isLocalOnTargetAlong : IsLocalOnTargetAlong P (@Surjective ⊓ @Smooth)

/-- Background hypothesis bundle for Definition 4.3.2, part (2), in the étale case:
a property of morphisms of schemes respects isomorphisms, is stable under composition
and base change, and is étale local on the source and target. -/
structure IsEtaleLocal (P : MorphismProperty Scheme.{u}) : Prop where
  /-- `P` respects isomorphisms. -/
  respectsIso : P.RespectsIso
  /-- `P` is stable under composition. -/
  isStableUnderComposition : P.IsStableUnderComposition
  /-- `P` is stable under base change. -/
  isStableUnderBaseChange : P.IsStableUnderBaseChange
  /-- `P` is étale local on the source. -/
  isLocalOnSourceAlong : IsLocalOnSourceAlong P (@Surjective ⊓ @Etale)
  /-- `P` is étale local on the target. -/
  isLocalOnTargetAlong : IsLocalOnTargetAlong P (@Surjective ⊓ @Etale)

/-- API lemma used after Definition 4.3.2 (flatness is smooth
local, from the unlabeled paragraph after the definition): flatness of morphisms of
schemes is smooth local (on the source and the target).

Neither half needs fpqc descent of flatness (which Mathlib does not have). Source-locality
is the two-out-of-three lemma `flat_comp_iff_of_surjective_flat` for a flat surjection, and
target-locality reduces to it: `pullback.fst f g` is a flat surjection, being the base
change of the smooth surjection `g`, and `pullback.fst f g ≫ f = pullback.snd f g ≫ g` is
flat as soon as `pullback.snd f g` is. -/
theorem isSmoothLocal_flat : IsSmoothLocal (@Flat : MorphismProperty Scheme.{u}) where
  respectsIso := inferInstance
  isStableUnderComposition := inferInstance
  isStableUnderBaseChange := inferInstance
  isLocalOnSourceAlong := fun {X'} {X} {Y} g f hg ↦ by
    haveI : Surjective g := hg.1
    haveI : Smooth g := hg.2
    exact (flat_comp_iff_of_surjective_flat g f).symm
  isLocalOnTargetAlong := by
    intro X Y Y' f g hg
    obtain ⟨hg1, hg2⟩ := hg
    have : Surjective g := hg1
    have : Smooth g := hg2
    have hfs : Surjective (pullback.fst f g) :=
      MorphismProperty.pullback_fst _ _ ‹Surjective g›
    have hff : Flat (pullback.fst f g) := MorphismProperty.pullback_fst _ _ inferInstance
    refine ⟨fun hf => MorphismProperty.pullback_snd _ _ hf, fun hsnd => ?_⟩
    have := hsnd
    have h1 : Flat (pullback.snd f g ≫ g) := inferInstance
    rw [← pullback.condition] at h1
    exact (flat_comp_iff_of_surjective_flat (pullback.fst f g) f).mp h1

/-- API lemma used after Definition 4.3.2 (smoothness is
smooth local, from the unlabeled paragraph after the definition): smoothness of
morphisms of schemes is smooth local (on the source and the target). -/
theorem isSmoothLocal_smooth : IsSmoothLocal (@Smooth : MorphismProperty Scheme.{u}) where
  respectsIso := inferInstance
  isStableUnderComposition := inferInstance
  isStableUnderBaseChange := inferInstance
  isLocalOnSourceAlong := fun {X'} {X} {Y} g f hg ↦ by
    haveI : Surjective g := hg.1
    haveI : Smooth g := hg.2
    constructor
    · intro hf
      haveI : Smooth f := hf
      infer_instance
    · intro hgf
      haveI : Smooth (g ≫ f) := hgf
      exact Smooth.of_surjective_smooth_precomp g f
  isLocalOnTargetAlong := isLocalOnTargetAlong_surjective_inf_smooth_of_descendsAlong _

/-- API lemma used after Definition 4.3.2 (surjectivity is
smooth local, from the unlabeled paragraph after the definition): surjectivity of
morphisms of schemes is smooth local (on the source and the target).

Source-locality is elementary and does not need smoothness of `g`, only surjectivity:
a composition of surjections is surjective, and if `g ≫ f` is surjective then so is `f`,
its range being larger. -/
theorem isSmoothLocal_surjective :
    IsSmoothLocal (@Surjective : MorphismProperty Scheme.{u}) where
  respectsIso := inferInstance
  isStableUnderComposition := inferInstance
  isStableUnderBaseChange := inferInstance
  isLocalOnSourceAlong := fun {X'} {X} {Y} g f hg ↦ by
    have hgs : Surjective g := hg.1
    refine ⟨fun hf => inferInstance, fun hgf => ⟨fun y => ?_⟩⟩
    obtain ⟨x', hx'⟩ := hgf.surj y
    exact ⟨g.base x', hx'⟩
  isLocalOnTargetAlong := isLocalOnTargetAlong_surjective_inf_smooth_of_descendsAlong _

/-- API lemma used after Definition 4.3.2 (locally of finite
type is smooth local, from the unlabeled paragraph after the definition): being locally
of finite type is smooth local (on the source and the target).

Source-locality is the nontrivial half and is absent from Mathlib; it is supplied by
`locallyOfFiniteType_of_comp_of_smooth_surjective`, which descends the finite-type
property along a smooth surjection (Stacks 0367 in the smooth case, together with a
Zariski reduction to affines). The forward direction is just stability under composition,
a smooth morphism being locally of finite type. -/
theorem isSmoothLocal_locallyOfFiniteType :
    IsSmoothLocal (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) where
  respectsIso := inferInstance
  isStableUnderComposition := inferInstance
  isStableUnderBaseChange := inferInstance
  isLocalOnSourceAlong := fun {X'} {X} {Y} g f hg ↦ by
    haveI : Surjective g := hg.1
    haveI : Smooth g := hg.2
    refine ⟨fun hf => ?_, fun hgf => ?_⟩
    · have := hf
      infer_instance
    · exact locallyOfFiniteType_of_comp_of_smooth_surjective g f hgf
  isLocalOnTargetAlong := isLocalOnTargetAlong_surjective_inf_smooth_of_descendsAlong _

/-- API lemma used after Definition 4.3.2 (locally of finite
presentation is smooth local, from the unlabeled paragraph after the definition): being
locally of finite presentation is smooth local (on the source and the target). -/
theorem isSmoothLocal_locallyOfFinitePresentation :
    IsSmoothLocal (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) where
  respectsIso := inferInstance
  isStableUnderComposition := inferInstance
  isStableUnderBaseChange := inferInstance
  isLocalOnSourceAlong := fun {X'} {X} {Y} g f hg ↦ by
    haveI : Surjective g := hg.1
    haveI : Smooth g := hg.2
    constructor
    · intro hf
      haveI : LocallyOfFinitePresentation f := hf
      infer_instance
    · intro hgf
      haveI : LocallyOfFinitePresentation (g ≫ f) := hgf
      exact LocallyOfFinitePresentation.of_surjective_smooth_precomp g f
  isLocalOnTargetAlong := isLocalOnTargetAlong_surjective_inf_smooth_of_descendsAlong _

/-- Diagnostic theorem associated with Definition 4.3.2 (smoothness of relative
dimension `n`, from the unlabeled paragraph after the definition; **erratum**): being smooth
of relative dimension `n` is *not* smooth local on the source, for any `n`.

Counterexample over any nonzero base ring `A` (here `ULift ℤ`): the projection
`𝔸ᵏ_A → Spec A` is a smooth surjection, and precomposing with it shifts the relative
dimension by `k`. With `f = 𝟙` and `k = 1` the ⇒ direction fails for `n = 0` (the identity
has relative dimension `0`, `𝔸¹_A → Spec A` has relative dimension `1`); with `f = 𝟙` and
`k = n ≥ 1` the ⇐ direction fails. The correct statement is that the property is *étale*
local on the source. See COMMENTARY.md. -/
theorem not_isLocalOnSourceAlong_smoothOfRelativeDimension (n : ℕ) :
    ¬ IsLocalOnSourceAlong (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Smooth) := by
  intro h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have key := h (specMvPolynomialHom (ULift.{u} ℤ) 1) (𝟙 _) ⟨inferInstance, inferInstance⟩
    have h1 : SmoothOfRelativeDimension 0 (𝟙 (Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
      inferInstance
    have h2 := key.mp h1
    rw [Category.comp_id] at h2
    have := eq_of_smoothOfRelativeDimension_specMvPolynomialHom (ULift.{u} ℤ) h2
    omega
  · have key := h (specMvPolynomialHom (ULift.{u} ℤ) n) (𝟙 _) ⟨inferInstance, inferInstance⟩
    have h2 : SmoothOfRelativeDimension n (specMvPolynomialHom (ULift.{u} ℤ) n ≫ 𝟙 _) := by
      rw [Category.comp_id]; infer_instance
    have := eq_zero_of_smoothOfRelativeDimension_id (ULift.{u} ℤ) (key.mpr h2)
    omega

/-- Diagnostic theorem associated with Definition 4.3.2 (smoothness of relative
dimension `n`, from the unlabeled paragraph after the definition; **erratum**): for `n ≠ 0`,
being smooth of relative dimension `n` is *not* stable under composition — relative
dimensions add, so `𝔸ⁿ_{𝔸ⁿ_A} → 𝔸ⁿ_A → Spec A` has relative dimension `2n`. The correct
statement is Mathlib's graded `smoothOfRelativeDimension_comp`. See COMMENTARY.md. -/
theorem not_isStableUnderComposition_smoothOfRelativeDimension {n : ℕ} (hn : n ≠ 0) :
    ¬ MorphismProperty.IsStableUnderComposition
      (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u}) := by
  intro h
  set A := ULift.{u} ℤ
  set B := MvPolynomial (Fin n) A
  set C := MvPolynomial (Fin n) B
  have hcomp : specMvPolynomialHom B n ≫ specMvPolynomialHom A n =
      Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
    rw [specMvPolynomialHom, specMvPolynomialHom, ← Spec.map_comp]
    congr 1
  have : Algebra.IsStandardSmoothOfRelativeDimension (n + n) A C :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans (n := n) (m := n) A B C
  have hmem := h.comp_mem (specMvPolynomialHom B n) (specMvPolynomialHom A n)
    inferInstance inferInstance
  rw [hcomp] at hmem
  have := eq_of_smoothOfRelativeDimension_SpecMap (A := A) (C := C) (m := n + n) hmem
  omega

/-- Diagnostic theorem associated with Definition 4.3.2 (smoothness of relative
dimension `n`, from the unlabeled paragraph after the definition; **erratum**): the book's
assertion that smoothness of relative dimension `n` is smooth local on the source and the
target, and stable under composition, is false for every `n`; so `SmoothOfRelativeDimension n`
is not a legitimate input to part (2) of the definition.

What *is* true: `SmoothOfRelativeDimension n` respects isomorphisms (a Mathlib instance), is
stable under base change (`smoothOfRelativeDimension_isStableUnderBaseChange`), composes in
the graded sense (`smoothOfRelativeDimension_comp`, of relative dimension `n + m`), is
*étale* local on the source, and is smooth — indeed fppf — local on the target
(`isLocalOnTargetAlong_smoothOfRelativeDimension`). See COMMENTARY.md. -/
theorem not_isSmoothLocal_smoothOfRelativeDimension (n : ℕ) :
    ¬ IsSmoothLocal (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u}) :=
  fun h => not_isLocalOnSourceAlong_smoothOfRelativeDimension n h.isLocalOnSourceAlong

/-- API lemma for the corrected discussion following Definition 4.3.2 (source-locality
claim, ⇒ direction): precomposing a morphism of relative dimension `n` with an étale morphism
does not change the relative dimension. -/
theorem smoothOfRelativeDimension_comp_of_etale {X' X Y : Scheme.{u}} (n : ℕ)
    (g : X' ⟶ X) (f : X ⟶ Y) [Etale g] [SmoothOfRelativeDimension n f] :
    SmoothOfRelativeDimension n (g ≫ f) := by
  have h : SmoothOfRelativeDimension (0 + n) (g ≫ f) := inferInstance
  simpa using h

/-- API lemma for the corrected discussion following Definition 4.3.2 (target-locality
claim, relative dimension `0`): being étale — equivalently, smooth of relative dimension `0`
(`Etale.eq_smoothOfRelativeDimension_zero`) — is smooth local on the target. -/
theorem isLocalOnTargetAlong_smoothOfRelativeDimension_zero :
    IsLocalOnTargetAlong (@SmoothOfRelativeDimension 0 : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Smooth) := by
  rw [← Etale.eq_smoothOfRelativeDimension_zero]
  exact isLocalOnTargetAlong_surjective_inf_smooth_of_descendsAlong _

/-- API lemma for the corrected discussion following Definition 4.3.2 (target-locality
claim): being smooth of relative dimension `n` *is* smooth local on the target, for every `n`.

The ⇒ direction is stability under base change.  For the ⇐ direction,
`RingHom.locally_isStandardSmoothOfRelativeDimension_codescendsAlong_faithfullyFlat`
descends the ring-level fixed-dimension condition; `HasRingHomProperty.descendsAlong_flat`
and Zariski locality then give fppf descent for the corresponding scheme property. -/
theorem isLocalOnTargetAlong_smoothOfRelativeDimension (n : ℕ) :
    IsLocalOnTargetAlong (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Smooth) := by
  letI : MorphismProperty.IsStableUnderBaseChange
      (@SmoothOfRelativeDimension n : MorphismProperty Scheme.{u}) :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  letI := HasRingHomProperty.descendsAlong_flat
    (P := @SmoothOfRelativeDimension n)
    (RingHom.locally_isStandardSmoothOfRelativeDimension_codescendsAlong_faithfullyFlat n)
  exact isLocalOnTargetAlong_surjective_inf_smooth_of_descendsAlong _

/-- API lemma used after Definition 4.3.2 (étaleness is étale
local, from the unlabeled paragraph after the definition): étaleness of morphisms of
schemes is étale local (on the source and the target). Source-locality follows from
`Etale.of_surjective_etale_precomp`, while target-locality is fppf descent. -/
theorem isEtaleLocal_etale : IsEtaleLocal (@Etale : MorphismProperty Scheme.{u}) where
  respectsIso := inferInstance
  isStableUnderComposition := inferInstance
  isStableUnderBaseChange := inferInstance
  isLocalOnSourceAlong := fun {X'} {X} {Y} g f hg ↦ by
    haveI : Surjective g := hg.1
    haveI : Etale g := hg.2
    constructor
    · intro hf
      haveI : Etale f := hf
      infer_instance
    · intro hgf
      haveI : Etale (g ≫ f) := hgf
      exact Etale.of_surjective_etale_precomp g f
  isLocalOnTargetAlong := isLocalOnTargetAlong_surjective_inf_etale_of_descendsAlong _

/-- API lemma used after Definition 4.3.2 (unramifiedness is
étale local, from the unlabeled paragraph after the definition): unramifiedness of
morphisms of schemes—being locally of finite type and formally unramified—is étale
local (on the source and the target). (Mathlib has no bundled `Unramified` class, so
unramifiedness is spelled `@LocallyOfFiniteType ⊓ @FormallyUnramified`.)

Source-locality is proved componentwise, and holds along smooth surjections already: for
"locally of finite type" it is `locallyOfFiniteType_of_comp_of_smooth_surjective`
(Stacks 0367 in the smooth case), and for formal unramifiedness it is
`formallyUnramified_of_comp_of_smooth_surjective` (the Jacobi–Zariski sequence). An étale
surjection is a smooth surjection, and is itself locally of finite type and formally
unramified, which gives the forward direction. -/
theorem isEtaleLocal_locallyOfFiniteType_inf_formallyUnramified :
    IsEtaleLocal
      (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u}) where
  respectsIso := inferInstance
  isStableUnderComposition := inferInstance
  isStableUnderBaseChange := inferInstance
  isLocalOnSourceAlong := fun {X'} {X} {Y} g f hg ↦ by
    haveI : Surjective g := hg.1
    haveI : Etale g := hg.2
    haveI : Smooth g := inferInstance
    refine ⟨fun hf => ⟨?_, ?_⟩, fun hgf => ⟨?_, ?_⟩⟩
    · have := hf.1
      infer_instance
    · exact MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hf.2
    · exact locallyOfFiniteType_of_comp_of_smooth_surjective g f hgf.1
    · exact formallyUnramified_of_comp_of_smooth_surjective g f hgf.2
  isLocalOnTargetAlong := isLocalOnTargetAlong_surjective_inf_etale_of_descendsAlong _

/-- Independence of a source-local property from the chosen presentation: if `P` is local
on the source along `Q`, then for any two `Q`-presentations `q₁`, `q₂` of a prestack `𝒵`
and any morphism `H : 𝒵 ⥤ᵇ Sch/V`, the induced morphisms of schemes `U₁ ⟶ V` and
`U₂ ⟶ V` satisfy `P` together or not at all.

This is the "vertical" half of the independence statements of Definition 4.3.2 and
Definition 4.3.7 — the half that varies the presentation of the source while keeping the
base fixed. -/
theorem hasProperty_chart_indep {P Q : MorphismProperty Scheme.{u}}
    (hsrc : IsLocalOnSourceAlong P Q)
    {𝒵 : BasedCategory.{v₂, u₂} Scheme.{u}} {V : Scheme.{u}} (H : 𝒵 ⥤ᵇ overBased V)
    {U₁ U₂ : Scheme.{u}} {q₁ : overBased U₁ ⥤ᵇ 𝒵} {q₂ : overBased U₂ ⥤ᵇ 𝒵}
    (h₁ : BasedFunctor.RepresentableWith Q q₁)
    (h₂ : BasedFunctor.RepresentableWith Q q₂) :
    P (q₁.comp H).overHom ↔ P (q₂.comp H).overHom := by
  obtain ⟨W, a₁, a₂, ha₁, ha₂, ⟨e⟩⟩ := exists_common_cover_iso h₁ h₂
  have e' : (overBased.map a₁).comp (q₁.comp H) ≅ (overBased.map a₂).comp (q₂.comp H) :=
    CategoryTheory.BasedCategory.isoWhiskerRight e H
  have key : a₁ ≫ (q₁.comp H).overHom = a₂ ≫ (q₂.comp H).overHom := by
    have h := CategoryTheory.BasedFunctor.overHom_eq_of_iso e'
    rwa [CategoryTheory.BasedFunctor.overHom_comp,
      CategoryTheory.BasedFunctor.overHom_comp,
      CategoryTheory.BasedFunctor.overHom_map,
      CategoryTheory.BasedFunctor.overHom_map] at h
  rw [hsrc a₁ _ ha₁, hsrc a₂ _ ha₂, key]

end AlgebraicGeometry

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- Background definition for Definition 4.3.2 (part (2), the general
presentation-tested form): let
$F \colon \cX \to \cY$ be a morphism of prestacks over $\Sch_{\ét}$ and let $\cQ_1$,
$\cQ_2$, $\cP$ be properties of morphisms of schemes. Then $F$ *has property $\cP$
tested on $(\cQ_1, \cQ_2)$-presentations* if for every presentation
$g \colon V \to \cY$ (a representable morphism from a scheme with property $\cQ_1$) and
every presentation $q \colon U \to \cX \times_{\cY} V$ with property $\cQ_2$, the induced
morphism of schemes $U \to V$ has property $\cP$. The cases $\cQ_1 = \cQ_2$ smooth
surjective (resp. étale surjective) give the notion of a morphism of algebraic (resp.
Deligne–Mumford) stacks having a property; the mixed case is used for étale and
unramified morphisms (Definition 4.3.37). -/
def HasPropertyOfPresentations (Q₁ Q₂ P : MorphismProperty Scheme.{u}) (F : 𝒳 ⥤ᵇ 𝒴) :
    Prop :=
  ∀ (V : Scheme.{u}) (g : overBased V ⥤ᵇ 𝒴), RepresentableWith Q₁ g →
    ∀ (U : Scheme.{u}) (q : overBased U ⥤ᵇ BasedCategory.fiberProduct F g),
      RepresentableWith Q₂ q →
      P (q.comp (BasedCategory.fiberProductSnd F g)).overHom

/-- **Definition 4.3.2** (`def:properties-of-morphisms-of-stacks`) (part (2), algebraic
stacks): let $\cP$ be a property of
morphisms of schemes which is smooth local and stable under composition and base change
(`AlgebraicGeometry.IsSmoothLocal`). A morphism $F \colon \cX \to \cY$ of algebraic
stacks *has property $\cP$* if for all smooth presentations $V \to \cY$ and
$U \to \cX \times_{\cY} V$, the induced morphism of schemes $U \to V$ has property
$\cP$. -/
abbrev HasProperty (P : MorphismProperty Scheme.{u}) (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  HasPropertyOfPresentations
    (@Surjective ⊓ @Smooth) (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) P F

/-- **Definition 4.3.2** (`def:properties-of-morphisms-of-stacks`) (part (2),
Deligne–Mumford stacks): let $\cP$ be a
property of morphisms of schemes which is étale local and stable under composition and
base change (`AlgebraicGeometry.IsEtaleLocal`). A morphism $F \colon \cX \to \cY$ of
Deligne–Mumford stacks *has property $\cP$* if for all étale presentations $V \to \cY$
and $U \to \cX \times_{\cY} V$, the induced morphism of schemes $U \to V$ has property
$\cP$. -/
abbrev HasEtaleProperty (P : MorphismProperty Scheme.{u}) (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  HasPropertyOfPresentations
    (@Surjective ⊓ @Etale) (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) P F

/-- If a morphism property is local on both the source and target along a class of
scheme presentations, then one pair of presentations suffices to test it. -/
theorem hasPropertyOfPresentations_of_exists
    {Q P : MorphismProperty Scheme.{u}}
    (hsrc : IsLocalOnSourceAlong P Q) (htgt : IsLocalOnTargetAlong P Q)
    [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]
    {F : 𝒳 ⥤ᵇ 𝒴}
    (h : ∃ (V : Scheme.{u}) (g : overBased V ⥤ᵇ 𝒴),
      RepresentableWith Q g ∧
      ∃ (U : Scheme.{u}) (q : overBased U ⥤ᵇ BasedCategory.fiberProduct F g),
        RepresentableWith Q q ∧
        P (q.comp (BasedCategory.fiberProductSnd F g)).overHom) :
    HasPropertyOfPresentations Q Q P F := by
  obtain ⟨V₀, g₀, hg₀, U₀, q₀, hq₀, hP₀⟩ := h
  intro V g hg U q hq
  obtain ⟨W, a₀, a, ha₀, ha, ⟨e⟩⟩ :=
    AlgebraicGeometry.exists_common_cover_iso hg₀ hg
  obtain ⟨q₀W, hq₀W, hproj₀⟩ := hq₀.exists_baseChange_presentation a₀
  obtain ⟨qW, hqW, hproj⟩ := hq.exists_baseChange_presentation a
  let K := BasedCategory.fiberProductMapRightIso F e
  let _ : K.toFunctor.IsEquivalence :=
    BasedCategory.isEquivalence_fiberProductMapRightIso F e
  let q₀W' := q₀W.comp K
  have hq₀W' : RepresentableWith Q q₀W' :=
    hq₀W.comp_target_isEquivalence K
  have hK_snd : K.comp (BasedCategory.fiberProductSnd F
      ((overBased.map a).comp g)) =
      BasedCategory.fiberProductSnd F ((overBased.map a₀).comp g₀) := by
    apply CategoryTheory.BasedFunctor.ext_of_toFunctor_eq
    rfl
  have hP₀pb : P (pullback.snd
      (q₀.comp (BasedCategory.fiberProductSnd F g₀)).overHom a₀) :=
    (htgt _ _ ha₀).mp hP₀
  have hPq₀W : P (q₀W.comp (BasedCategory.fiberProductSnd F
      ((overBased.map a₀).comp g₀))).overHom := by
    rw [hproj₀]
    exact hP₀pb
  have hPq₀W' : P (q₀W'.comp (BasedCategory.fiberProductSnd F
      ((overBased.map a).comp g))).overHom := by
    rw [show q₀W'.comp (BasedCategory.fiberProductSnd F
        ((overBased.map a).comp g)) =
        q₀W.comp (BasedCategory.fiberProductSnd F
          ((overBased.map a₀).comp g₀)) by
      simp only [q₀W', CategoryTheory.BasedFunctor.comp_assoc, hK_snd]]
    exact hPq₀W
  have hindep := AlgebraicGeometry.hasProperty_chart_indep hsrc
    (BasedCategory.fiberProductSnd F ((overBased.map a).comp g)) hq₀W' hqW
  have hPqW : P (qW.comp (BasedCategory.fiberProductSnd F
      ((overBased.map a).comp g))).overHom := hindep.mp hPq₀W'
  rw [hproj] at hPqW
  exact (htgt _ _ ha).mpr hPqW

/-- API theorem supporting Definition 4.3.2 (part (2);
independence of the presentation): for a smooth local property $\cP$ of morphisms of
schemes and a morphism of algebraic stacks, it is enough to check property $\cP$ on a
single pair of smooth presentations: if some smooth presentations $V \to \cY$ and
$U \to \cX \times_{\cY} V$ induce a morphism $U \to V$ with $\cP$, then all such
presentations do. -/
theorem hasProperty_of_exists {P : MorphismProperty Scheme.{u}} (hP : IsSmoothLocal P)
    [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴] {F : 𝒳 ⥤ᵇ 𝒴}
    (h : ∃ (V : Scheme.{u}) (g : overBased V ⥤ᵇ 𝒴),
      RepresentableWith (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) g ∧
      ∃ (U : Scheme.{u}) (q : overBased U ⥤ᵇ BasedCategory.fiberProduct F g),
        RepresentableWith (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) q ∧
        P (q.comp (BasedCategory.fiberProductSnd F g)).overHom) :
    HasProperty P F := by
  exact hasPropertyOfPresentations_of_exists
    hP.isLocalOnSourceAlong hP.isLocalOnTargetAlong h

/-- API theorem supporting Definition 4.3.2 (part (2);
independence of the presentation, étale case): for an étale local property $\cP$ of
morphisms of schemes and a morphism of Deligne–Mumford stacks, it is enough to check
property $\cP$ on a single pair of étale presentations. -/
theorem hasEtaleProperty_of_exists {P : MorphismProperty Scheme.{u}} (hP : IsEtaleLocal P)
    [IsDeligneMumfordStack 𝒳] [IsDeligneMumfordStack 𝒴] {F : 𝒳 ⥤ᵇ 𝒴}
    (h : ∃ (V : Scheme.{u}) (g : overBased V ⥤ᵇ 𝒴),
      RepresentableWith (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) g ∧
      ∃ (U : Scheme.{u}) (q : overBased U ⥤ᵇ BasedCategory.fiberProduct F g),
        RepresentableWith (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) q ∧
        P (q.comp (BasedCategory.fiberProductSnd F g)).overHom) :
    HasEtaleProperty P F := by
  exact hasPropertyOfPresentations_of_exists
    hP.isLocalOnSourceAlong hP.isLocalOnTargetAlong h

/-- Named API specialization of Definition 4.3.2, part (2), from the unlabeled paragraph
after it: a morphism of algebraic stacks is *flat* if it has the smooth-local property
of flatness of morphisms of schemes. -/
abbrev Flat (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  HasProperty (@_root_.AlgebraicGeometry.Flat : MorphismProperty Scheme.{u}) F

/-- Named API specialization of Definition 4.3.2, part (2), from the unlabeled paragraph
after it: a morphism of algebraic stacks is *smooth* if it has the smooth-local property
of smoothness of morphisms of schemes. -/
abbrev Smooth (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  HasProperty (@_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) F

/-- Named API specialization of Definition 4.3.2, part (2), from the unlabeled paragraph
after it: a morphism of algebraic stacks is *surjective* if it has the smooth-local
property of surjectivity of morphisms of schemes. -/
abbrev Surjective (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  HasProperty (@_root_.AlgebraicGeometry.Surjective : MorphismProperty Scheme.{u}) F

/-- Named API specialization of Definition 4.3.2, part (2), from the unlabeled paragraph
after it: a morphism of algebraic stacks is *locally of finite type* if it has the
smooth-local property of being locally of finite type for morphisms of schemes. -/
abbrev LocallyOfFiniteType (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  HasProperty (@_root_.AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u}) F

/-- Named API specialization of Definition 4.3.2, part (2), from the unlabeled paragraph
after it: a morphism of algebraic stacks is *locally of finite presentation* if it has
the smooth-local property of being locally of finite presentation for morphisms of
schemes. -/
abbrev LocallyOfFinitePresentation (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  HasProperty
    (@_root_.AlgebraicGeometry.LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) F

/- **Definition 4.3.2** (`def:properties-of-morphisms-of-stacks`) (part (3)): a morphism
$\cX \to \cY$ of algebraic stacks
representable by schemes *has property $\cP$* if for every morphism $T \to \cY$ from a
scheme, the base change $\cX \times_{\cY} T \to T$ has $\cP$. This is exactly §4.1's
`CategoryTheory.BasedFunctor.RelativelyRepresentableWith P`. -/
example (P : MorphismProperty Scheme.{u}) (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  F.RelativelyRepresentableWith P

end AlgebraicGeometry.BasedFunctor

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- Named API specialization of Definition 4.3.2, part (3): a morphism of algebraic
stacks is an *isomorphism* when it is representable by schemes and every scheme base
change is an isomorphism. -/
abbrev IsIso (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  F.RelativelyRepresentableWith (MorphismProperty.isomorphisms Scheme.{u})

/-- Named API specialization of Definition 4.3.2, part (3): a morphism of algebraic
stacks is an *open immersion* when it is representable by schemes and every scheme base
change is an open immersion. -/
abbrev IsOpenImmersion (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  F.RelativelyRepresentableWith
    (@_root_.AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})

/-- Named API specialization of Definition 4.3.2, part (3): a morphism of algebraic
stacks is a *closed immersion* when it is representable by schemes and every scheme base
change is a closed immersion. -/
abbrev IsClosedImmersion (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  F.RelativelyRepresentableWith
    (@_root_.AlgebraicGeometry.IsClosedImmersion : MorphismProperty Scheme.{u})

/-- Named API specialization of Definition 4.3.2, part (3): a morphism of algebraic
stacks is a *locally closed immersion* when it is representable by schemes and every
scheme base change is an immersion (Mathlib's `AlgebraicGeometry.IsImmersion`). -/
abbrev IsLocallyClosedImmersion (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  F.RelativelyRepresentableWith
    (@_root_.AlgebraicGeometry.IsImmersion : MorphismProperty Scheme.{u})

/-- Named API specialization of Definition 4.3.2, part (3): a morphism of algebraic
stacks is *affine* when it is representable by schemes and every scheme base change is
affine. -/
abbrev IsAffine (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  F.RelativelyRepresentableWith
    (@_root_.AlgebraicGeometry.IsAffineHom : MorphismProperty Scheme.{u})

/-- Named API specialization of Definition 4.3.2, part (3): a morphism of algebraic
stacks is *quasi-affine* when it is representable by schemes and every scheme base
change is quasi-affine. -/
abbrev IsQuasiAffine (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  F.RelativelyRepresentableWith IsQuasiAffineHom

end AlgebraicGeometry.BasedFunctor

end DefPropertiesOfMorphismsOfStacks

section ExLocallyOfFiniteType

/- LEDGER — **Example 4.3.3** (`ex:locally-of-finite-type`): for a smooth affine group
scheme `G → S` acting
on an algebraic space `U → S`, the quotient `[U/G] → S` is flat (resp. smooth,
surjective, locally of finite presentation, locally of finite type) if and only if
`U → S` is; consequently `𝓜_g` is locally of finite type over `ℤ` and `Coh_{r,d}(C)` and
`Bun_{r,d}(C)` are locally of finite type over the base field. The main statement is
blocked on the quotient stacks `[U/G]`. Of the consequences, the `𝓜_g` one is available:
`AlgebraicGeometry.BasedFunctor.locallyOfFiniteType_moduliOfCurves` in
`StacksAndModuli/Section4.6-Characterization/part4.6.2-equivalent-characterizations.lean` derives
it from `ℳ_g` being of finite type (Corollary 4.6.10); `Coh` and `Bun` remain blocked on
`thm:bunC-is-algebraic`.

LEDGER (unlabeled exercise after `ex:locally-of-finite-type`): for `G = ℤ/2` acting on
`𝔸²` by `(-1)·(x,y) = (-x,-y)`, the quotient stack `[𝔸²/G]` is smooth while the scheme
quotient `Spec k[x,y]^G` is singular. Blocked on quotient stacks as above. -/

end ExLocallyOfFiniteType

section ExerDiagonalLocallyOfFiniteType

open CategoryTheory Limits AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- The scheme-chart output needed to prove that the relative diagonal of a morphism
of algebraic stacks is locally of finite type.

The pending geometric construction starts with the relative-Isom fiber of `F` over a
smooth chart of `𝒳 ×_𝒴 𝒳`, represents that fiber by an algebraic space, and then chooses
the displayed smooth presentation by a scheme.  Its structural morphism is the map to
the chosen target chart. -/
structure RelativeDiagonalIsomFiberChart (F : 𝒳 ⥤ᵇ 𝒴) where
  /-- A smooth scheme presentation of the target of the relative diagonal. -/
  targetBase : Scheme.{u}
  targetPresentation : overBased targetBase ⥤ᵇ BasedCategory.fiberProduct F F
  targetPresentation_smooth : BasedFunctor.RepresentableWith
    (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
      MorphismProperty Scheme.{u}) targetPresentation
  /-- A smooth scheme presentation of the resulting relative-diagonal fiber. -/
  sourceBase : Scheme.{u}
  sourcePresentation : overBased sourceBase ⥤ᵇ
    BasedCategory.fiberProduct F.diag targetPresentation
  sourcePresentation_smooth : BasedFunctor.RepresentableWith
    (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
      MorphismProperty Scheme.{u}) sourcePresentation
  /-- The structural map of the relative-Isom chart is locally of finite type. -/
  structural_locallyOfFiniteType : _root_.AlgebraicGeometry.LocallyOfFiniteType
    (sourcePresentation.comp
      (BasedCategory.fiberProductSnd F.diag targetPresentation)).overHom

/-- A relative-Isom fiber chart proves that the relative diagonal is locally of finite
type.  This is the formal reduction of Exercise 4.3.5; the remaining construction of
`RelativeDiagonalIsomFiberChart` is isolated in `locallyOfFiniteType_diag`. -/
theorem locallyOfFiniteType_diag_of_isomFiberChart
    (F : 𝒳 ⥤ᵇ 𝒴) [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴]
    (h : RelativeDiagonalIsomFiberChart F) :
    LocallyOfFiniteType F.diag := by
  let _ : IsAlgebraicStack (BasedCategory.fiberProduct F F) :=
    IsAlgebraicStack.fiberProduct F F
  apply hasProperty_of_exists isSmoothLocal_locallyOfFiniteType
  exact ⟨h.targetBase, h.targetPresentation, h.targetPresentation_smooth,
    h.sourceBase, h.sourcePresentation, h.sourcePresentation_smooth,
    h.structural_locallyOfFiniteType⟩

/-- **Exercise 4.3.5** (`exer:diagonal-locally-of-finite-type`): the diagonal
$\Delta_F \colon \cX \to \cX \times_{\cY} \cX$ of a morphism of algebraic stacks is
locally of finite type.

The smooth-chart argument for the absolute diagonal is formalized in
`IsAlgebraicStack.representableWith_locallyOfFiniteType_diag_of_presentation`.  For a
relative diagonal, every test point lifts to the square of a scheme-valued base change
(`RepresentableWith.diag_of_scheme_base_changes`), whose target prestack has faithful
projection, so its relative diagonal fibers agree with the absolute diagonal fibers of
the base-changed algebraic stack
(`RepresentableWith.diag_of_target_projection_faithful`). -/
theorem locallyOfFiniteType_diag (F : 𝒳 ⥤ᵇ 𝒴) [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴] :
    LocallyOfFiniteType F.diag := by
  refine locallyOfFiniteType_diag_of_isomFiberChart F (Nonempty.some ?_)
  have hrw : RepresentableWith
      (@_root_.AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u})
      F.diag := by
    apply RepresentableWith.diag_of_scheme_base_changes
    intro T g
    let _ : IsAlgebraicStack
        (BasedCategory.fiberProduct F ((relativeDiagonalPointFst F g).comp F)) :=
      IsAlgebraicStack.fiberProduct F ((relativeDiagonalPointFst F g).comp F)
    let _ : (overBased T).p.Faithful :=
      inferInstanceAs (Over.forget T).Faithful
    exact RepresentableWith.diag_of_target_projection_faithful
      (relativeDiagonalBaseChangeSnd F g)
      (IsAlgebraicStack.representableWith_locallyOfFiniteType_diag_of_presentation _)
  let _ : IsAlgebraicStack (BasedCategory.fiberProduct F F) :=
    IsAlgebraicStack.fiberProduct F F
  obtain ⟨T₀, tp, htp⟩ :=
    IsAlgebraicStack.exists_presentation (𝒳 := BasedCategory.fiberProduct F F)
  obtain ⟨P, hP, E, hE⟩ := hrw.1 T₀ tp
  let _ : IsAlgebraicSpace P := hP
  let _ : E.toFunctor.IsEquivalence := hE
  obtain ⟨U, q, hq⟩ := IsAlgebraicSpace.exists_presentation (X := P)
  let sp : overBased U ⥤ᵇ BasedCategory.fiberProduct F.diag tp :=
    (overBasedToOfPresheafYoneda U).comp ((ofPresheaf.map q).comp E)
  have hsprel : sp.RelativelyRepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale :
        MorphismProperty Scheme.{u}) :=
    ((relativelyRepresentableWith_ofPresheaf_map hq).comp_of_isEquivalence
      (overBasedToOfPresheafYoneda U)).comp_target_isEquivalence E
  have hsp : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale :
        MorphismProperty Scheme.{u}) sp :=
    RelativelyRepresentableWith.representableWith le_rfl hsprel
  refine ⟨⟨T₀, tp, htp, U, sp, ?_, ?_⟩⟩
  · exact hsp.mono (inf_le_inf le_rfl etale_le_smooth)
  · have h := hrw.2 T₀ tp P hP E hE U q hq
    exact h

end AlgebraicGeometry.BasedFunctor

end ExerDiagonalLocallyOfFiniteType

section PropSmoothDescentForRepresentableMorphisms

open CategoryTheory Functor Limits Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ v₄ u₄ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
  {𝒴' : BasedCategory.{v₄, u₄} Scheme.{u}} [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴]
  [IsAlgebraicStack 𝒴'] (F : 𝒳 ⥤ᵇ 𝒴) (G : 𝒴' ⥤ᵇ 𝒴)

/-- The conjunction of two smooth-local morphism properties is smooth-local. -/
theorem IsSmoothLocal.inf {P Q : MorphismProperty Scheme.{u}}
    (hP : IsSmoothLocal P) (hQ : IsSmoothLocal Q) :
    IsSmoothLocal (P ⊓ Q) where
  respectsIso := by
    letI : P.RespectsIso := hP.respectsIso
    letI : Q.RespectsIso := hQ.respectsIso
    infer_instance
  isStableUnderComposition := by
    letI : P.IsStableUnderComposition := hP.isStableUnderComposition
    letI : Q.IsStableUnderComposition := hQ.isStableUnderComposition
    exact MorphismProperty.IsStableUnderComposition.inf
  isStableUnderBaseChange := by
    letI : P.IsStableUnderBaseChange := hP.isStableUnderBaseChange
    letI : Q.IsStableUnderBaseChange := hQ.isStableUnderBaseChange
    infer_instance
  isLocalOnSourceAlong := by
    intro X' X Y p f hp
    exact and_congr (hP.isLocalOnSourceAlong p f hp)
      (hQ.isLocalOnSourceAlong p f hp)
  isLocalOnTargetAlong := by
    intro X Y Y' f p hp
    exact and_congr (hP.isLocalOnTargetAlong f p hp)
      (hQ.isLocalOnTargetAlong f p hp)

/-- A smooth-local property of a morphism of algebraic stacks can be read on a
scheme presentation after an arbitrary scheme-valued base change, even though
`HasProperty` is defined using presentations of the target stack.

The proof lifts the arbitrary test map étale-locally to a fixed presentation of
the target and then compares the two resulting presentations of the fiber. -/
theorem HasProperty.arbitraryBaseChart
    {P : MorphismProperty Scheme.{u}} (hP : IsSmoothLocal P)
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}}
    {Ycat : BasedCategory.{v₃, u₃} Scheme.{u}}
    {H : Xcat ⥤ᵇ Ycat} [IsAlgebraicStack Xcat] [IsAlgebraicStack Ycat]
    (hH : HasProperty P H) {T U : Scheme.{u}}
    (g : overBased T ⥤ᵇ Ycat)
    (q : overBased U ⥤ᵇ fiberProduct H g)
    (hq : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q) :
    P (q.comp (fiberProductSnd H g)).overHom := by
  letI : P.RespectsIso := hP.respectsIso
  letI : P.IsStableUnderComposition := hP.isStableUnderComposition
  letI : P.IsStableUnderBaseChange := hP.isStableUnderBaseChange
  obtain ⟨V, a, ha⟩ := IsAlgebraicStack.exists_presentation (𝒳 := Ycat)
  obtain ⟨T', p, hpEtale, hpSurjective, l, ⟨e⟩⟩ :=
    ha.exists_etale_surjective_lift g
  letI : @_root_.AlgebraicGeometry.Etale _ _ p := hpEtale
  letI : @_root_.AlgebraicGeometry.Surjective _ _ p := hpSurjective
  have hpQ :
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) p :=
    ⟨hpSurjective, inferInstance⟩
  obtain ⟨q', hq', hq'proj⟩ := hq.exists_baseChange_presentation p
  let _ : IsAlgebraicStack (fiberProduct H a) :=
    IsAlgebraicStack.fiberProduct H a
  obtain ⟨W, q₀, hq₀⟩ :=
    IsAlgebraicStack.exists_presentation (𝒳 := fiberProduct H a)
  have hP₀ : P (q₀.comp (fiberProductSnd H a)).overHom :=
    hH V a ha W q₀ hq₀
  obtain ⟨q₀', hq₀', hq₀'proj⟩ :=
    hq₀.exists_baseChange_presentation l.overHom
  have hP₀' : P (q₀'.comp
      (fiberProductSnd H ((overBased.map l.overHom).comp a))).overHom := by
    rw [hq₀'proj]
    exact MorphismProperty.pullback_snd _ _ hP₀
  obtain ⟨el⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map l
  let ec : (overBased.map l.overHom).comp a ≅ (overBased.map p).comp g :=
    (isoWhiskerRight el.symm a).trans e
  let M := fiberProductMapRightIso H ec
  let _ : M.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso H ec
  let q₀'' := q₀'.comp M
  have hq₀'' : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) q₀'' :=
    hq₀'.comp_target_isEquivalence M
  have hM_snd : M.comp
      (fiberProductSnd H ((overBased.map p).comp g)) =
      fiberProductSnd H ((overBased.map l.overHom).comp a) := by
    apply CategoryTheory.BasedFunctor.ext_of_toFunctor_eq
    rfl
  have hP₀'' : P (q₀''.comp
      (fiberProductSnd H ((overBased.map p).comp g))).overHom := by
    rw [show q₀''.comp (fiberProductSnd H ((overBased.map p).comp g)) =
        q₀'.comp (fiberProductSnd H ((overBased.map l.overHom).comp a)) by
      simp only [q₀'', CategoryTheory.BasedFunctor.comp_assoc, hM_snd]]
    exact hP₀'
  have hindep := AlgebraicGeometry.hasProperty_chart_indep
    hP.isLocalOnSourceAlong
    (fiberProductSnd H ((overBased.map p).comp g)) hq₀'' hq'
  have hPq' : P (q'.comp
      (fiberProductSnd H ((overBased.map p).comp g))).overHom :=
    hindep.mp hP₀''
  rw [hq'proj] at hPq'
  exact (hP.isLocalOnTargetAlong
    (q.comp (fiberProductSnd H g)).overHom p hpQ).mpr hPq'

omit [IsAlgebraicStack 𝒳] in
/-- A smooth-surjective cover of the target on which a morphism is representable
supplies an algebraic-space representation of every scheme-valued fiber after one
smooth-surjective base change. -/
theorem exists_smoothCover_algebraicSpace_representation
    (hG : HasProperty
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) G)
    (hFG : Representable (fiberProductSnd F G))
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒴) :
    ∃ (U : Scheme.{u}) (p : U ⟶ T),
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) p ∧
      ∃ (A : Scheme.{u}ᵒᵖ ⥤ Type u), IsAlgebraicSpace A ∧
        ∃ K : ofPresheaf A ⥤ᵇ fiberProduct F ((overBased.map p).comp g),
          K.toFunctor.IsEquivalence := by
  let _ : IsAlgebraicStack (fiberProduct G g) :=
    IsAlgebraicStack.fiberProduct G g
  obtain ⟨U, k, hk⟩ :=
    IsAlgebraicStack.exists_presentation (𝒳 := fiberProduct G g)
  let hQ : IsSmoothLocal
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) :=
    IsSmoothLocal.inf isSmoothLocal_surjective isSmoothLocal_smooth
  have hp :
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u})
        (k.comp (fiberProductSnd G g)).overHom :=
    HasProperty.arbitraryBaseChart hQ hG g k hk
  let p : U ⟶ T := (k.comp (fiberProductSnd G g)).overHom
  let l := k.comp (fiberProductFst G g)
  obtain ⟨A, hA, K₀, hK₀⟩ := hFG U l
  let _ : K₀.toFunctor.IsEquivalence := hK₀
  let K₁ := K₀.comp (fiberProductAssoc F G l)
  let _ : (fiberProductAssoc F G l).toFunctor.IsEquivalence :=
    isEquivalence_fiberProductAssoc F G l
  let _ : K₁.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans K₀.toFunctor
      (fiberProductAssoc F G l).toFunctor
  let b := k.comp (fiberProductSnd G g)
  obtain ⟨eb⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map b
  let ecomm : l.comp G ≅ b.comp g :=
    isoWhiskerLeft k (fiberProductIsoComm G g)
  let e : l.comp G ≅ (overBased.map p).comp g :=
    ecomm.trans (isoWhiskerRight eb g)
  let M := fiberProductMapRightIso F e
  let _ : M.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso F e
  let K := K₁.comp M
  have hK : K.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans K₁.toFunctor M.toFunctor
  exact ⟨U, p, hp, A, hA, K, hK⟩

omit [IsAlgebraicStack 𝒳] in
/-- A smooth-surjective cover of the target on which a morphism is
representable with property `P` supplies a smooth-local scheme representation
of every scheme-valued fiber. -/
theorem exists_smoothCover_scheme_representation
    {P : MorphismProperty Scheme.{u}}
    (hG : HasProperty
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) G)
    (hFG : CategoryTheory.BasedFunctor.RelativelyRepresentableWith P
      (fiberProductSnd F G))
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒴) :
    ∃ (U : Scheme.{u}) (p : U ⟶ T),
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) p ∧
      ∃ (W : Scheme.{u})
        (K : overBased W ⥤ᵇ fiberProduct F ((overBased.map p).comp g)),
        K.toFunctor.IsEquivalence ∧
          P (K.comp (fiberProductSnd F
            ((overBased.map p).comp g))).overHom := by
  let _ : IsAlgebraicStack (fiberProduct G g) :=
    IsAlgebraicStack.fiberProduct G g
  obtain ⟨U, k, hk⟩ :=
    IsAlgebraicStack.exists_presentation (𝒳 := fiberProduct G g)
  let hQ : IsSmoothLocal
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) :=
    IsSmoothLocal.inf isSmoothLocal_surjective isSmoothLocal_smooth
  have hp :
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u})
        (k.comp (fiberProductSnd G g)).overHom :=
    HasProperty.arbitraryBaseChart hQ hG g k hk
  let p : U ⟶ T := (k.comp (fiberProductSnd G g)).overHom
  let l := k.comp (fiberProductFst G g)
  obtain ⟨W, K₀, hK₀⟩ := hFG.1 U l
  let _ : K₀.toFunctor.IsEquivalence := hK₀
  have hPK₀ : P (K₀.comp
      (fiberProductSnd (fiberProductSnd F G) l)).overHom :=
    hFG.2 U l W K₀ hK₀
  let K₁ := K₀.comp (fiberProductAssoc F G l)
  let _ : (fiberProductAssoc F G l).toFunctor.IsEquivalence :=
    isEquivalence_fiberProductAssoc F G l
  let _ : K₁.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans K₀.toFunctor
      (fiberProductAssoc F G l).toFunctor
  let b := k.comp (fiberProductSnd G g)
  obtain ⟨eb⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map b
  let ecomm : l.comp G ≅ b.comp g :=
    isoWhiskerLeft k (fiberProductIsoComm G g)
  let e : l.comp G ≅ (overBased.map p).comp g :=
    ecomm.trans (isoWhiskerRight eb g)
  let M := fiberProductMapRightIso F e
  let _ : M.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductMapRightIso F e
  let K := K₁.comp M
  have hK : K.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans K₁.toFunctor M.toFunctor
  refine ⟨U, p, hp, W, K, hK, ?_⟩
  have hM_snd : M.comp
      (fiberProductSnd F ((overBased.map p).comp g)) =
      fiberProductSnd F (l.comp G) := by
    apply CategoryTheory.BasedFunctor.ext_of_toFunctor_eq
    rfl
  rw [show K.comp (fiberProductSnd F ((overBased.map p).comp g)) =
      K₀.comp (fiberProductSnd (fiberProductSnd F G) l) by
    simp only [K, K₁, CategoryTheory.BasedFunctor.comp_assoc, hM_snd,
      fiberProductAssoc_comp_snd]]
  exact hPK₀

/-- If a scheme property is local on the target along smooth-surjective
morphisms, then it holds for every scheme representation of a fiber once it
holds after the given smooth cover. -/
theorem property_of_smoothCover
    {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    [P.IsStableUnderBaseChange]
    (hlocal : IsLocalOnTargetAlong P
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}))
    (hG : HasProperty
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) G)
    (hFG : CategoryTheory.BasedFunctor.RelativelyRepresentableWith P
      (fiberProductSnd F G))
    (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒴)
    (U : Scheme.{u}) (R : overBased U ⥤ᵇ fiberProduct F g)
    (hR : R.toFunctor.IsEquivalence) :
    P (R.comp (fiberProductSnd F g)).overHom := by
  obtain ⟨S, p, hp, W, K, hK, hPK⟩ :=
    exists_smoothCover_scheme_representation F G hG hFG T g
  obtain ⟨R', hR', hR'proj⟩ :=
    exists_baseChange_scheme_representation R hR p
  obtain ⟨a, ha, hstruct⟩ :=
    exists_isIso_overHom_comp_eq_of_scheme_representations
      R' hR' K hK (fiberProductSnd F ((overBased.map p).comp g))
  let f := (R.comp (fiberProductSnd F g)).overHom
  have hPaR' : P (a ≫ (R'.comp
      (fiberProductSnd F ((overBased.map p).comp g))).overHom) :=
    hstruct ▸ hPK
  let _ : CategoryTheory.IsIso a := ha
  have hPR' : P (R'.comp
      (fiberProductSnd F ((overBased.map p).comp g))).overHom :=
    (P.cancel_left_of_respectsIso a _).mp hPaR'
  have hPpullback : P (pullback.snd f p) := by
    rw [← hR'proj]
    exact hPR'
  exact (hlocal f p hp).mpr hPpullback

/-- Descent of `representableByProperty P` along smooth-surjective maps implies
that `P` itself is local on the target along such maps. -/
theorem isLocalOnTargetAlong_of_representableByProperty_smoothDescent
    {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    [P.IsStableUnderBaseChange]
    (hdescent : ∀ {T S : Scheme.{u}} (p : S ⟶ T)
      [@_root_.AlgebraicGeometry.Surjective _ _ p]
      [@_root_.AlgebraicGeometry.Smooth _ _ p]
      (A : Sheaf (Scheme.etaleTopology.over T) (Type u)),
      (Scheme.etaleTopology.representableByProperty P).prop (.mk (op S))
          ((Scheme.etaleTopology.overMapPullback (Type u) p).obj A) →
        (Scheme.etaleTopology.representableByProperty P).prop (.mk (op T)) A) :
    IsLocalOnTargetAlong P
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) := by
  intro X T S f p hp
  constructor
  · intro hf
    exact P.pullback_snd f p hf
  · intro hfp
    let η := yoneda.map f
    let ePull : Over.mk (yoneda.map (pullback.snd f p)) ≅
        Over.mk (pullback.snd η (yoneda.map p)) :=
      Over.isoMk (Presheaf.isPullback_yoneda_map f p).isoPullback
        (Presheaf.isPullback_yoneda_map f p).isoPullback_hom_snd
    let eLocal : yoneda.obj (Over.mk (pullback.snd f p)) ≅
        (Over.map p).op ⋙ Presheaf.relativeOver η :=
      Presheaf.relativeOverYonedaIso (Over.mk (pullback.snd f p)) ≪≫
        Presheaf.relativeOverMapIso ePull ≪≫
          Presheaf.relativeOverPullbackIso p η
    have hXSheaf : Presieve.IsSheaf Scheme.etaleTopology
        (yoneda.obj X) :=
      GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
    let Frel : Sheaf (Scheme.etaleTopology.over T) (Type u) :=
      ⟨Presheaf.relativeOver η,
        (isSheaf_iff_isSheaf_of_type _ _).2
          (Presheaf.relativeOver_isSheaf Scheme.etaleTopology η
            hXSheaf)⟩
    let _ : @_root_.AlgebraicGeometry.Surjective _ _ p := hp.1
    let _ : @_root_.AlgebraicGeometry.Smooth _ _ p := hp.2
    have hLocal :
        (Scheme.etaleTopology.representableByProperty P).prop (.mk (op S))
          ((Scheme.etaleTopology.overMapPullback (Type u) p).obj Frel) :=
      ⟨Over.mk (pullback.snd f p), hfp, ⟨eLocal⟩⟩
    obtain ⟨Z, hZ, ⟨eZ⟩⟩ := hdescent p Frel hLocal
    let eYoneda : yoneda.obj Z ≅ yoneda.obj (Over.mk f) :=
      eZ ≪≫ (Presheaf.relativeOverYonedaIso (Over.mk f)).symm
    let eOver : Z ≅ Over.mk f :=
      Yoneda.fullyFaithful.preimageIso eYoneda
    let _ : CategoryTheory.IsIso eOver.hom.left := inferInstance
    have hcomp : P (eOver.hom.left ≫ f) := by
      change P (eOver.hom.left ≫ (Over.mk f).hom)
      rw [eOver.hom.w]
      exact hZ
    exact (P.cancel_left_of_respectsIso eOver.hom.left f).mp hcomp

/-- A sheaf on an étale over-site which becomes represented by an
isomorphism after smooth-surjective pullback is itself represented by an
isomorphism. -/
theorem presheaf_isomorphism_of_smooth_pullback
    {T S : Scheme.{u}} (p : S ⟶ T)
    [@_root_.AlgebraicGeometry.Surjective _ _ p]
    [@_root_.AlgebraicGeometry.Smooth _ _ p]
    (A : Sheaf (Scheme.etaleTopology.over T) (Type u))
    (hA : (Scheme.etaleTopology.representableByProperty
      (MorphismProperty.isomorphisms Scheme.{u})).prop (.mk (op S))
        ((Scheme.etaleTopology.overMapPullback (Type u) p).obj A)) :
    (Scheme.etaleTopology.representableByProperty
      (MorphismProperty.isomorphisms Scheme.{u})).prop (.mk (op T)) A := by
  obtain ⟨W, hW, ⟨eW⟩⟩ := hA
  have hW' : CategoryTheory.IsIso W.hom :=
    (MorphismProperty.isomorphisms.iff W.hom).mp hW
  let _ : CategoryTheory.IsIso W.hom := hW'
  have hWopen : @_root_.AlgebraicGeometry.IsOpenImmersion _ _ W.hom :=
    inferInstance
  have hAopen : (Scheme.etaleTopology.representableByProperty
      (@_root_.AlgebraicGeometry.IsOpenImmersion :
        MorphismProperty Scheme.{u})).prop (.mk (op S))
        ((Scheme.etaleTopology.overMapPullback (Type u) p).obj A) :=
    ⟨W, hWopen, ⟨eW⟩⟩
  obtain ⟨Z, hZopen, ⟨eZ⟩⟩ :=
    MorphismProperty.presheaf_isOpenImmersion_of_pullback p A hAopen
  let Zpull := (Over.pullback p).obj Z
  let ePull : yoneda.obj Zpull ≅
      ((Scheme.etaleTopology.overMapPullback (Type u) p).obj A).obj :=
    (Over.mapPullbackAdj p).compYonedaIso.app Z ≪≫
      Functor.isoWhiskerLeft (Over.map p).op eZ
  let eOver : W ≅ Zpull :=
    Yoneda.fullyFaithful.preimageIso (eW ≪≫ ePull.symm)
  let _ : CategoryTheory.IsIso eOver.hom.left := inferInstance
  have hWsurj : @_root_.AlgebraicGeometry.Surjective _ _ W.hom :=
    inferInstance
  have hcomp : @_root_.AlgebraicGeometry.Surjective _ _
      (eOver.hom.left ≫ Zpull.hom) := by
    rw [eOver.hom.w]
    exact hWsurj
  have hZpull : @_root_.AlgebraicGeometry.Surjective _ _ Zpull.hom :=
    (MorphismProperty.cancel_left_of_respectsIso
      (P := @_root_.AlgebraicGeometry.Surjective)
      eOver.hom.left Zpull.hom).mp hcomp
  have hZsurj : @_root_.AlgebraicGeometry.Surjective _ _ Z.hom := by
    apply (isSmoothLocal_surjective.isLocalOnTargetAlong Z.hom p
      ⟨inferInstance, inferInstance⟩).mpr
    exact hZpull
  have hZiso : CategoryTheory.IsIso Z.hom :=
    (isIso_iff_isOpenImmersion_and_surjective Z.hom).mpr
      ⟨hZopen, hZsurj⟩
  exact ⟨Z, (MorphismProperty.isomorphisms.iff Z.hom).mpr hZiso, ⟨eZ⟩⟩

/-- **Proposition 4.3.6** (`prop:smooth-descent-for-representable-morphisms`)
(representable): let $\cY' \to \cY$ be a smooth surjective morphism of algebraic stacks
and let $\cX \to \cY$ be a morphism of algebraic stacks with base change
$\cX' = \cX \times_{\cY} \cY' \to \cY'$. Then $\cX \to \cY$ is representable if and only
if $\cX' \to \cY'$ is. -/
theorem representable_iff_representable_fiberProductSnd
    (hG : HasProperty
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) G) :
    Representable F ↔ Representable (fiberProductSnd F G) := by
  constructor
  · intro hF
    exact hF.fiberProductSnd G
  · intro hFG T g
    obtain ⟨U, p, hp, A, hA, K, hK⟩ :=
      exists_smoothCover_algebraicSpace_representation F G hG hFG T g
    let _ : @_root_.AlgebraicGeometry.Surjective _ _ p := hp.1
    let _ : @_root_.AlgebraicGeometry.Smooth _ _ p := hp.2
    obtain ⟨S, q, hqEtale, hqSurjective, s, hs⟩ :=
      Scheme.Hom.exists_etale_surjective_refinement_of_smooth p
    let _ : IsAlgebraicSpace A := hA
    let _ : K.toFunctor.IsEquivalence := hK
    let B := pullback
      (representedFiberSecondBaseMap F ((overBased.map p).comp g) K)
      (yoneda.map s)
    let hB : IsAlgebraicSpace B := IsAlgebraicSpace.pullback _ _
    let _ : IsAlgebraicSpace B := hB
    let L := representedFiberSecondBaseChangeRepresentation F
      ((overBased.map p).comp g) K s
    let _ : L.toFunctor.IsEquivalence :=
      isEquivalence_representedFiberSecondBaseChangeRepresentation F
        ((overBased.map p).comp g) K s
    have hleg :
        (overBased.map s).comp ((overBased.map p).comp g) =
          (overBased.map q).comp g := by
      rw [← CategoryTheory.BasedFunctor.comp_assoc,
        ← overBased.map_comp, hs]
    let e :
        (overBased.map s).comp ((overBased.map p).comp g) ≅
          (overBased.map q).comp g := eqToIso hleg
    let M := fiberProductMapRightIso F e
    let _ : M.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductMapRightIso F e
    let Kq := L.comp M
    have hKq : Kq.toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans L.toFunctor M.toFunctor
    let _ : IsAlgebraicStack (fiberProduct F g) :=
      IsAlgebraicStack.fiberProduct F g
    exact exists_isAlgebraicSpace_of_etale_presheaf_baseChange
      F g q hqEtale hqSurjective Kq hKq

/-- Descent of scheme-valued sheaves with a morphism property upgrades smooth
descent of representability to smooth descent of relative representability with
that property. -/
theorem relativelyRepresentableWith_of_smoothCover
    {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    [P.IsStableUnderBaseChange]
    (hlocal : IsLocalOnTargetAlong P
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}))
    (hdescent : ∀ {T S : Scheme.{u}} (p : S ⟶ T)
      [@_root_.AlgebraicGeometry.Surjective _ _ p]
      [@_root_.AlgebraicGeometry.Smooth _ _ p]
      (A : Sheaf (Scheme.etaleTopology.over T) (Type u)),
      (Scheme.etaleTopology.representableByProperty P).prop (.mk (op S))
          ((Scheme.etaleTopology.overMapPullback (Type u) p).obj A) →
        (Scheme.etaleTopology.representableByProperty P).prop (.mk (op T)) A)
    (hG : HasProperty
      (@_root_.AlgebraicGeometry.Surjective ⊓
        @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) G)
    (hFG : CategoryTheory.BasedFunctor.RelativelyRepresentableWith P
      (fiberProductSnd F G)) :
    CategoryTheory.BasedFunctor.RelativelyRepresentableWith P F := by
  have hFrep : Representable F :=
    (representable_iff_representable_fiberProductSnd F G hG).mpr
      (representable_of_relativelyRepresentable hFG.1)
  have hFrel : F.RelativelyRepresentable := by
    intro T g
    obtain ⟨X, hX, E, hE⟩ := hFrep T g
    let _ : IsAlgebraicSpace X := hX
    let _ : E.toFunctor.IsEquivalence := hE
    let η := representedFiberSecondBaseMap F g E
    obtain ⟨S, p, hp, W, K, hK, hPK⟩ :=
      exists_smoothCover_scheme_representation F G hG hFG T g
    let _ : @_root_.AlgebraicGeometry.Surjective _ _ p := hp.1
    let _ : @_root_.AlgebraicGeometry.Smooth _ _ p := hp.2
    let L := representedFiberSecondBaseChangeRepresentation F g E p
    let _ : L.toFunctor.IsEquivalence :=
      isEquivalence_representedFiberSecondBaseChangeRepresentation F g E p
    let _ : K.toFunctor.IsEquivalence := hK
    let K' := (ofPresheafYonedaToOverBased W).comp K
    let _ : K'.toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans
        (ofPresheafYonedaToOverBased W).toFunctor K.toFunctor
    let e := ofPresheaf.comparisonIso L K'
    let kstruct :=
      (K.comp (fiberProductSnd F ((overBased.map p).comp g))).overHom
    have he : e.hom ≫ pullback.snd η (yoneda.map p) =
        yoneda.map kstruct := by
      have he' := comparisonIso_hom_comp_representedFiberSecondBaseMap
        F ((overBased.map p).comp g) L K
      rw [representedFiberSecondBaseMap_baseChangeRepresentation] at he'
      simpa only [η, kstruct] using he'
    let eOver : Over.mk (yoneda.map kstruct) ≅
        Over.mk (pullback.snd η (yoneda.map p)) :=
      Over.isoMk e he
    let eLocal : yoneda.obj (Over.mk kstruct) ≅
        (Over.map p).op ⋙ Presheaf.relativeOver η :=
      Presheaf.relativeOverYonedaIso (Over.mk kstruct) ≪≫
        Presheaf.relativeOverMapIso eOver ≪≫
          Presheaf.relativeOverPullbackIso p η
    let Frel : Sheaf (Scheme.etaleTopology.over T) (Type u) :=
      ⟨Presheaf.relativeOver η,
        (isSheaf_iff_isSheaf_of_type _ _).2
          (Presheaf.relativeOver_isSheaf Scheme.etaleTopology η
            hX.isSheaf)⟩
    have hLocal :
        (Scheme.etaleTopology.representableByProperty P).prop (.mk (op S))
          ((Scheme.etaleTopology.overMapPullback (Type u) p).obj Frel) := by
      refine ⟨Over.mk kstruct, hPK, ⟨?_⟩⟩
      exact eLocal
    obtain ⟨Z, -, ⟨eZ⟩⟩ := hdescent p Frel hLocal
    let eArrow :=
      Presheaf.relativeOverRepresentationArrowIso η Z eZ
    let eSource : yoneda.obj Z.left ≅ X :=
      Arrow.leftFunc.mapIso eArrow
    let R := (overBasedToOfPresheafYoneda Z.left).comp
      ((ofPresheaf.map eSource.hom).comp E)
    refine ⟨Z.left, R, ?_⟩
    let _ : (ofPresheaf.map eSource.hom).toFunctor.IsEquivalence :=
      ofPresheaf.isEquivalence_map eSource.hom
    let _ : ((ofPresheaf.map eSource.hom).comp E).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans
        (ofPresheaf.map eSource.hom).toFunctor E.toFunctor
    exact Functor.isEquivalence_trans
      (overBasedToOfPresheafYoneda Z.left).toFunctor
      ((ofPresheaf.map eSource.hom).comp E).toFunctor
  refine ⟨hFrel, ?_⟩
  intro T g U R hR
  exact property_of_smoothCover F G hlocal hG hFG T g U R hR

/-- **Proposition 4.3.6** (`prop:smooth-descent-for-representable-morphisms`)
(isomorphisms): let $\cY' \to \cY$ be a smooth surjective morphism of algebraic stacks
and let $\cX \to \cY$ be a morphism of algebraic stacks with base change
$\cX' = \cX \times_{\cY} \cY' \to \cY'$. Then $\cX \to \cY$ is an isomorphism if and
only if $\cX' \to \cY'$ is. -/
theorem isIso_iff_isIso_fiberProductSnd
    (hG : HasProperty
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) G) :
    IsIso F ↔ IsIso (fiberProductSnd F G) := by
  constructor
  · intro hF
    exact hF.fiberProductSnd G
  · intro hFG
    let hdescent := @presheaf_isomorphism_of_smooth_pullback
    exact relativelyRepresentableWith_of_smoothCover F G
      (isLocalOnTargetAlong_of_representableByProperty_smoothDescent hdescent)
      hdescent hG hFG

/-- **Proposition 4.3.6** (`prop:smooth-descent-for-representable-morphisms`) (open
immersions): let $\cY' \to \cY$ be a smooth surjective morphism of algebraic stacks and
let $\cX \to \cY$ be a morphism of algebraic stacks with base change
$\cX' = \cX \times_{\cY} \cY' \to \cY'$. Then $\cX \to \cY$ is an open immersion if and
only if $\cX' \to \cY'$ is. -/
theorem isOpenImmersion_iff_isOpenImmersion_fiberProductSnd
    (hG : HasProperty
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) G) :
    IsOpenImmersion F ↔ IsOpenImmersion (fiberProductSnd F G) := by
  constructor
  · intro hF
    exact hF.fiberProductSnd G
  · intro hFG
    let hdescent := @MorphismProperty.presheaf_isOpenImmersion_of_pullback
    exact relativelyRepresentableWith_of_smoothCover F G
      (isLocalOnTargetAlong_of_representableByProperty_smoothDescent hdescent)
      hdescent hG hFG

/-- **Proposition 4.3.6** (`prop:smooth-descent-for-representable-morphisms`) (closed
immersions): let $\cY' \to \cY$ be a smooth surjective morphism of algebraic stacks and
let $\cX \to \cY$ be a morphism of algebraic stacks with base change
$\cX' = \cX \times_{\cY} \cY' \to \cY'$. Then $\cX \to \cY$ is a closed immersion if and
only if $\cX' \to \cY'$ is. -/
theorem isClosedImmersion_iff_isClosedImmersion_fiberProductSnd
    (hG : HasProperty
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) G) :
    IsClosedImmersion F ↔ IsClosedImmersion (fiberProductSnd F G) := by
  constructor
  · intro hF
    exact hF.fiberProductSnd G
  · intro hFG
    let hdescent := @MorphismProperty.presheaf_isClosedImmersion_of_pullback
    exact relativelyRepresentableWith_of_smoothCover F G
      (isLocalOnTargetAlong_of_representableByProperty_smoothDescent hdescent)
      hdescent hG hFG

/-- **Proposition 4.3.6** (`prop:smooth-descent-for-representable-morphisms`) (affine
morphisms): let $\cY' \to \cY$ be a smooth surjective morphism of algebraic stacks and
let $\cX \to \cY$ be a morphism of algebraic stacks with base change
$\cX' = \cX \times_{\cY} \cY' \to \cY'$. Then $\cX \to \cY$ is affine if and only if
$\cX' \to \cY'$ is. -/
theorem isAffine_iff_isAffine_fiberProductSnd
    (hG : HasProperty
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) G) :
    IsAffine F ↔ IsAffine (fiberProductSnd F G) := by
  constructor
  · intro hF
    exact hF.fiberProductSnd G
  · intro hFG
    let hdescent := @MorphismProperty.presheaf_isAffineHom_of_pullback
    exact relativelyRepresentableWith_of_smoothCover F G
      (isLocalOnTargetAlong_of_representableByProperty_smoothDescent hdescent)
      hdescent hG hFG

/-- **Proposition 4.3.6** (`prop:smooth-descent-for-representable-morphisms`)
(quasi-affine morphisms): let $\cY' \to \cY$ be a smooth surjective morphism of
algebraic stacks and let $\cX \to \cY$ be a morphism of algebraic stacks with base
change $\cX' = \cX \times_{\cY} \cY' \to \cY'$. Then $\cX \to \cY$ is quasi-affine if
and only if $\cX' \to \cY'$ is. -/
theorem isQuasiAffine_iff_isQuasiAffine_fiberProductSnd
    (hG : HasProperty
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) G) :
    IsQuasiAffine F ↔ IsQuasiAffine (fiberProductSnd F G) := by
  constructor
  · intro hF
    exact hF.fiberProductSnd G
  · intro hFG
    let hdescent := @MorphismProperty.presheaf_isQuasiAffineHom_of_pullback
    exact relativelyRepresentableWith_of_smoothCover F G
      (isLocalOnTargetAlong_of_representableByProperty_smoothDescent hdescent)
      hdescent hG hFG

end AlgebraicGeometry.BasedFunctor

end PropSmoothDescentForRepresentableMorphisms
