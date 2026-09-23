module

public import StacksAndModuli.«Section4.2-Representability».«part4.2.1-representability»
public import StacksAndModuli.«Section4.3-Properties».«part4.3.6-etale-and-unramified»
public import StacksAndModuli.«Section4.4-Equivalence-Relations».«part4.4.4-algebraicity»
public import StacksAndModuli.«Section4.2-Representability».«part4.2.3-inertia»
public import StacksAndModuli.API.ClosedMapQuotientDescent
public import StacksAndModuli.API.RepresentableHasProperty
public import StacksAndModuli.API.RelativeDiagonalBaseChange
public import StacksAndModuli.API.RepresentedFiberClosedMap
public import StacksAndModuli.API.SchemeFiberDiagonalComparison
public import StacksAndModuli.API.SchemeFiberPresentationComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Properness and the valuative criterion: definitions

This module formalizes `def:separated-proper` and covers `exer:proper-actions` of §4.8
(Properness and the Valuative Criterion) of *Stacks and Moduli*,
label `sec:valuative-criteria`.

It also carries two §4.3 items whose statements need §4.8 vocabulary:
**Exercise 4.3.38** (`exer:diagonal-characterizations`) — the three characterizations of an
unramified / separated / quasi-separated diagonal through the relative inertia and the
double diagonal — and **Definition 4.3.11** (`def:separated-for-representable-morphism`)
in full, each in its own section block. For the definition: all four items are stated in
terms of the diagonal, and
§4.3 defers them because the notions they are built from — quasi-compactness of a morphism
of stacks (§4.3.4) and properness of a representable morphism (§4.8) — are only available
here. §4.3's part4.3.3 records a pointer.

Main declarations:
- `AlgebraicGeometry.BasedFunctor.UniversallyClosed`: universally closed morphisms of
  algebraic stacks, via closedness of the maps `|𝒳 ×_𝒴 𝒴'| → |𝒴'|` of topological spaces
  for all base changes by algebraic stacks;
- `AlgebraicGeometry.BasedFunctor.IsSeparatedRepresentable` and
  `AlgebraicGeometry.BasedFunctor.IsProperRepresentable`: separatedness and properness for
  representable morphisms of algebraic stacks, through the diagonal (representable by
  schemes) and the scheme property `AlgebraicGeometry.IsProper`;
- `AlgebraicGeometry.BasedFunctor.IsSeparated` and `AlgebraicGeometry.BasedFunctor.IsProper`:
  separated and proper morphisms of algebraic stacks;
- `AlgebraicGeometry.BasedFunctor.QuasiSeparated`: quasi-separated morphisms (diagonal and
  double diagonal quasi-compact) — **Definition 4.3.11** part (2);
- `AlgebraicGeometry.BasedFunctor.HasAffineDiagonal`, `…HasQuasiAffineDiagonal`,
  `…HasSeparatedDiagonal`: **Definition 4.3.11** part (1);
- `AlgebraicGeometry.BasedFunctor.FinitePresentation`: **Definition 4.3.11** part (3),
  with `…FinitePresentation.finiteType`;
- the theorem that universal closedness can be tested on base changes by schemes.

Two §4.3 labels are also carried here, because they need both the quotient stack `[U/G]`
of §4.4 and the diagonal predicates defined above, and §4.3 can import neither:
- `AlgebraicGeometry.PresheafGroupoid.isProper_actionMap_iff_isSeparated_quotientPrestack_ofAction`:
  part (a) of `exer:proper-actions` — an action is proper if and only if `[U/G]` is
  separated;
- `AlgebraicGeometry.PresheafGroupoid.hasAffineDiagonal_toBase_quotientPrestack_ofAction`
  and `…hasQuasiAffineDiagonal_toBase_quotientPrestack_ofAction`: **Lemma 4.3.14**
  (`lem:quotient-stack-diagonal`, §4.3).

The examples (`BG`, `Bun_{r,d}(C)`, `𝓜_{(g,n)}`) are ledgered: they are blocked on
classifying stacks and the moduli stacks of curves and bundles.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefSeparatedForRepresentableMorphism

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ v₃ u₂ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

variable [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]
/-- **Definition 4.3.11** (`def:separated-for-representable-morphism`) (part (4)): a
*representable* morphism $f \colon \cX \to \cY$ of algebraic stacks is *separated* if its
diagonal $\Delta_f \colon \cX \to \cX \times_{\cY} \cX$, which is representable by
schemes (Exercise 4.2.4), is proper, i.e. every base change
of $\Delta_f$ by a morphism from a scheme is a proper morphism of schemes. (The predicate
is stated for every morphism of prestacks over $\Sch$; it carries its intended meaning
for representable morphisms of algebraic stacks. It realizes the definition of
separatedness for representable morphisms of §4.3, recorded there as a ledger pending the
§4.2 diagonal.) -/
abbrev IsSeparatedRepresentable (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  F.diag.RelativelyRepresentableWith
    (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u})

/-- **Definition 4.3.11** (`def:separated-for-representable-morphism`) (part (1)): a
morphism $f \colon \cX \to \cY$ of algebraic stacks has *affine diagonal* if the diagonal
$\Delta_f \colon \cX \to \cX \times_{\cY} \cX$ is affine, in the sense of Definition 4.3.2
part (3). -/
abbrev HasAffineDiagonal (F : 𝒳 ⥤ᵇ 𝒴) : Prop := IsAffine F.diag

/-- **Definition 4.3.11** (`def:separated-for-representable-morphism`) (part (1)): a
morphism of algebraic stacks has *quasi-affine diagonal* if its diagonal is
quasi-affine. -/
abbrev HasQuasiAffineDiagonal (F : 𝒳 ⥤ᵇ 𝒴) : Prop := IsQuasiAffine F.diag

/-- **Definition 4.3.11** (`def:separated-for-representable-morphism`) (part (1)): a
morphism of algebraic stacks has *separated diagonal* if its diagonal is separated. The
diagonal is representable by schemes (Exercise 4.2.4), so "separated" here is
separatedness for a representable morphism, part (4) of this same definition. -/
abbrev HasSeparatedDiagonal (F : 𝒳 ⥤ᵇ 𝒴) : Prop := IsSeparatedRepresentable F.diag

/-- **Definition 4.3.11** (`def:separated-for-representable-morphism`) (part (2)):
a morphism
$f \colon \cX \to \cY$ of algebraic stacks is *quasi-separated* if the diagonal
$\Delta_f \colon \cX \to \cX \times_{\cY} \cX$ and the second diagonal
$\Delta_{\Delta_f} \colon \cX \to \cX \times_{\cX \times_{\cY} \cX} \cX$ are
quasi-compact. (This realizes the definition of quasi-separatedness of §4.3, recorded
there as a ledger pending the §4.2 diagonal; it enters the hypotheses of the valuative
criteria of §4.8.) -/
def QuasiSeparated (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  QuasiCompact F.diag ∧ QuasiCompact F.diag.diag

/-- **Definition 4.3.11** (`def:separated-for-representable-morphism`) (part (3)):
a morphism
$f \colon \cX \to \cY$ of algebraic stacks is of *finite presentation* if it is locally of
finite presentation, quasi-compact, and quasi-separated. -/
def FinitePresentation (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  LocallyOfFinitePresentation F ∧ QuasiCompact F ∧ QuasiSeparated F

/-- A morphism of finite presentation is of finite type: it is locally of finite
presentation, hence locally of finite type, and quasi-compact. -/
lemma FinitePresentation.finiteType {F : 𝒳 ⥤ᵇ 𝒴} (h : FinitePresentation F) :
    FiniteType F :=
  ⟨fun V g hg U q hq => by
      have := h.1 V g hg U q hq
      infer_instance, h.2.1⟩

end AlgebraicGeometry.BasedFunctor

/- Supporting note for Definition 4.3.11, part (1), absolute form: the book adds that an
algebraic stack `𝒳` has affine (resp. quasi-affine, separated)
diagonal if `𝒳 → Spec ℤ` does. That is `HasAffineDiagonal 𝒳.toBase` and its variants, so no
separate name is introduced here.

A word of warning about one name: `AlgebraicGeometry.BasedCategory.HasAffineDiagonal` in
`StacksAndModuli/Section4.5-Dimension/part4.5.2-tangent-spaces.lean` is the *same notion* stated
without the diagonal — for all `Spec A → 𝒳` and `Spec B → 𝒳`, the fibre product
`Spec A ×_𝒳 Spec B` is affine — introduced there as the hypothesis of Proposition 4.5.10.
The comparison of the two formulations is still open; it needs the identification of the
base change of `Δ_𝒳` along `(f, g)` with `fiberProduct f g`
(`exer:magic-square`/`exer:isom-presheaf`). See this folder's COMMENTARY.md. -/

end DefSeparatedForRepresentableMorphism

section ExerDiagonalCharacterizations

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ v₃ u₂ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}
  (F : 𝒳 ⥤ᵇ 𝒴)
variable [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]

/-- **Exercise 4.3.38** (`exer:diagonal-characterizations`, §4.3) (unramified case): for a
morphism `F : 𝒳 ⟶ 𝒴` of algebraic stacks the following are equivalent — the diagonal
`Δ_F : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` is unramified; the relative inertia `I_{𝒳/𝒴} ⟶ 𝒳` is unramified; and
the double diagonal `𝒳 ⟶ I_{𝒳/𝒴} = 𝒳 ×_{𝒳 ×_𝒴 𝒳} 𝒳` is an open immersion.

The exercise is stated in §4.3 but formalized here, with Definition 4.3.11, because its
three variants speak about separatedness and quasi-separatedness, which are §4.8
vocabulary. Compare Stacks 0CL0. -/
theorem tfae_unramified_diag [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴] :
    List.TFAE
      [Unramified F.diag,
        Unramified (fiberProductFst F.diag F.diag),
        IsOpenImmersion F.inertiaUnit] := by
  sorry

/-- **Exercise 4.3.38** (`exer:diagonal-characterizations`, §4.3) (separated case): the
diagonal is separated iff the relative inertia `I_{𝒳/𝒴} ⟶ 𝒳` is separated iff the double
diagonal is a closed immersion. -/
theorem tfae_isSeparatedRepresentable_diag [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴] :
    List.TFAE
      [IsSeparatedRepresentable F.diag,
        IsSeparatedRepresentable (fiberProductFst F.diag F.diag),
        IsClosedImmersion F.inertiaUnit] := by
  sorry

/-- **Exercise 4.3.38** (`exer:diagonal-characterizations`, §4.3) (quasi-separated case):
the diagonal is quasi-separated iff the relative inertia `I_{𝒳/𝒴} ⟶ 𝒳` is quasi-separated
iff the double diagonal is quasi-compact. -/
theorem tfae_quasiSeparated_diag [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴] :
    List.TFAE
      [QuasiSeparated F.diag,
        QuasiSeparated (fiberProductFst F.diag F.diag),
        QuasiCompact F.inertiaUnit] := by
  sorry

end AlgebraicGeometry.BasedFunctor

end ExerDiagonalCharacterizations

section DefSeparatedProper

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ v₃ u₂ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

variable [𝒳.p.IsFiberedInGroupoids] [𝒴.p.IsFiberedInGroupoids]
/-- **Definition 4.8.1** (`def:separated-proper`) (part (1)): a morphism
$f \colon \cX \to \cY$ of algebraic stacks is *universally closed* if for every morphism
$\cY' \to \cY$ of algebraic stacks, the base change $\cX \times_{\cY} \cY' \to \cY'$
induces a closed map $|\cX \times_{\cY} \cY'| \to |\cY'|$ of topological spaces. (The
test stacks $\cY'$ cannot be quantified over all universes inside a single proposition;
they are quantified in the universes `{u, u + 1}` of the standard prestacks over
`Scheme.{u}` — those of `CategoryTheory.BasedCategory.ofPresheaf` and of quotient
prestacks. Testing against these is equivalent to testing against schemes, and hence
against algebraic stacks in arbitrary universes, since universal closedness is smooth
local on the target; see
`universallyClosed_iff_isClosedMap_mapPoints_fiberProductSnd` below.) -/
def UniversallyClosed (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  ∀ (𝒴' : BasedCategory.{u, u + 1} Scheme.{u}) [IsAlgebraicStack 𝒴'] (G : 𝒴' ⥤ᵇ 𝒴),
    IsClosedMap (mapPoints (BasedCategory.fiberProductSnd F G))

/-- **Definition 4.8.1** (`def:separated-proper`) (part (2)): a *representable* morphism
$f \colon \cX \to \cY$ of algebraic stacks is *proper* if it is universally closed,
separated (`AlgebraicGeometry.BasedFunctor.IsSeparatedRepresentable`), and of finite
type. (The predicate is stated for every morphism of prestacks over $\Sch$; it carries
its intended meaning for representable morphisms of algebraic stacks.) -/
def IsProperRepresentable (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  UniversallyClosed F ∧ IsSeparatedRepresentable F ∧ FiniteType F

/-- **Definition 4.8.1** (`def:separated-proper`) (part (3)): a morphism
$f \colon \cX \to \cY$ of algebraic stacks is *separated* if the representable morphism
$\Delta_f \colon \cX \to \cX \times_{\cY} \cX$ is proper, i.e. universally closed,
separated as a representable morphism, and of finite type. -/
abbrev IsSeparated (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  IsProperRepresentable F.diag

/-- **Definition 4.8.1** (`def:separated-proper`) (part (4)): a morphism
$f \colon \cX \to \cY$ of algebraic stacks is *proper* if it is universally closed,
separated, and of finite type. Unlike for schemes and algebraic spaces, properness of a
morphism of algebraic stacks is *not* equivalent to the diagonal being a closed
immersion: the diagonal of an algebraic stack need not be a monomorphism. -/
def IsProper (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  UniversallyClosed F ∧ IsSeparated F ∧ FiniteType F

/-- Supporting implication for the scheme-test criterion in §4.8: a universally closed
morphism remains closed after
base change by every scheme. This is a direct specialization of `UniversallyClosed`,
since a representable prestack `Sch/T` is an algebraic stack. -/
theorem isClosedMap_mapPoints_fiberProductSnd_of_universallyClosed
    [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴] {F : 𝒳 ⥤ᵇ 𝒴}
    (hF : UniversallyClosed F) (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒴) :
    IsClosedMap (mapPoints (BasedCategory.fiberProductSnd F g)) := by
  exact hF (overBased T) g

/-- The unnumbered scheme-test criterion in §4.8, between Definition 4.8.1 and the
proper-actions exercise:
universal closedness can be tested on base changes by schemes — a morphism
$\cX \to \cY$ of algebraic stacks is universally closed if and only if for every morphism
$T \to \cY$ from a scheme, the induced map $|\cX \times_{\cY} T| \to |\Sch/T|$ is closed.
(This is the first equivalence of the remark: universal closedness is smooth local on the
target. The further reduction to a single smooth presentation $V \to \cY$, and — for
noetherian $\cY$ — to finite type base changes $T \to \cY$, is part of the proof of
Theorem 4.8.7.) -/
theorem universallyClosed_iff_isClosedMap_mapPoints_fiberProductSnd
    [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴] (F : 𝒳 ⥤ᵇ 𝒴) :
    UniversallyClosed F ↔
      ∀ (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒴),
        IsClosedMap (mapPoints (BasedCategory.fiberProductSnd F g)) := by
  constructor
  · exact fun hF T g ↦
      isClosedMap_mapPoints_fiberProductSnd_of_universallyClosed hF T g
  · intro hF Y' hY' G
    let _ : IsAlgebraicStack (BasedCategory.fiberProduct F G) :=
      IsAlgebraicStack.fiberProduct F G
    let H := BasedCategory.fiberProductSnd F G
    obtain ⟨T, g, hg⟩ := IsAlgebraicStack.exists_presentation (𝒳 := Y')
    let _ : IsAlgebraicStack (BasedCategory.fiberProduct H g) :=
      IsAlgebraicStack.fiberProduct H g
    let A := BasedCategory.fiberProductAssoc F G g
    have hA : A.toFunctor.IsEquivalence :=
      BasedCategory.isEquivalence_fiberProductAssoc F G g
    let _ : A.toFunctor.IsEquivalence := hA
    have hAclosed : IsClosedMap (mapPoints A) :=
      isClosedMap_mapPoints_of_isEquivalence A hA
    have hKclosed : IsClosedMap
        (mapPoints (BasedCategory.fiberProductSnd F (g.comp G))) :=
      hF T (g.comp G)
    have hstruct : A.comp (BasedCategory.fiberProductSnd F (g.comp G)) =
        BasedCategory.fiberProductSnd H g := by
      exact BasedCategory.fiberProductAssoc_comp_snd F G g
    have hbaseClosed : IsClosedMap
        (mapPoints (BasedCategory.fiberProductSnd H g)) := by
      rw [← hstruct]
      have hmap : mapPoints
          (A.comp (BasedCategory.fiberProductSnd F (g.comp G))) =
          mapPoints (BasedCategory.fiberProductSnd F (g.comp G)) ∘ mapPoints A := by
        funext z
        exact BasedCategory.quotientMapOfPresentation.mapPoints_comp
          A (BasedCategory.fiberProductSnd F (g.comp G)) z
      rw [hmap]
      exact hKclosed.comp hAclosed
    apply IsClosedMap.of_isQuotientMap_baseChange
      (BasedCategory.isQuotientMap_mapPoints_of_presentation g hg)
      (continuous_mapPoints' (BasedCategory.fiberProductFst H g)) hbaseClosed
    · intro z
      rw [← BasedCategory.quotientMapOfPresentation.mapPoints_comp,
        ← BasedCategory.quotientMapOfPresentation.mapPoints_comp,
        BasedCategory.quotientMapOfPresentation.mapPoints_eq_of_iso
          (BasedCategory.fiberProductIsoComm H g)]
    · intro x y hxy
      obtain ⟨z, hz₁, hz₂⟩ :=
        exists_mapPoints_fiberProduct_eq' H g x y hxy
      exact ⟨z, hz₁, hz₂⟩

/-- Supporting schematic comparison for Definition 4.8.1, part (1): for a morphism
representable by schemes, universal closedness on stack point spaces is
equivalent to every scheme-valued fiber being universally closed as a morphism of
schemes. -/
theorem universallyClosed_iff_relativelyRepresentableWith_universallyClosed
    [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴] {F : 𝒳 ⥤ᵇ 𝒴}
    (hF : F.RelativelyRepresentable) :
    UniversallyClosed F ↔ F.RelativelyRepresentableWith
      (@_root_.AlgebraicGeometry.UniversallyClosed : MorphismProperty Scheme.{u}) := by
  constructor
  · intro hclosed
    refine ⟨hF, ?_⟩
    intro T g U E hE
    let f := (E.comp (BasedCategory.fiberProductSnd F g)).overHom
    refine ⟨CategoryTheory.MorphismProperty.universally_mk'
      (_root_.AlgebraicGeometry.topologically @IsClosedMap) f ?_⟩
    intro S p _
    obtain ⟨E', hE', hstruct⟩ :=
      exists_baseChange_scheme_representation E hE p
    let H' := BasedCategory.fiberProductSnd F ((overBased.map p).comp g)
    have hstack : IsClosedMap (mapPoints H') :=
      (universallyClosed_iff_isClosedMap_mapPoints_fiberProductSnd F).mp
        hclosed S ((overBased.map p).comp g)
    have hscheme : IsClosedMap (E'.comp H').overHom :=
      (isClosedMap_mapPoints_iff_of_scheme_representation E' hE' H').mp hstack
    have hsnd : IsClosedMap (Limits.pullback.snd f p) := by
      rw [← hstruct]
      exact hscheme
    change IsClosedMap (Limits.pullback.fst p f)
    rw [← Limits.pullbackSymmetry_hom_comp_snd p f]
    exact hsnd.comp (Limits.pullbackSymmetry p f).hom.homeomorph.isClosedMap
  · intro hclosed
    apply (universallyClosed_iff_isClosedMap_mapPoints_fiberProductSnd F).mpr
    intro T g
    obtain ⟨U, E, hE⟩ := hclosed.1 T g
    let f := (E.comp (BasedCategory.fiberProductSnd F g)).overHom
    have hf : _root_.AlgebraicGeometry.UniversallyClosed f :=
      hclosed.2 T g U E hE
    let _ : _root_.AlgebraicGeometry.UniversallyClosed f := hf
    exact (isClosedMap_mapPoints_iff_of_scheme_representation E hE
      (BasedCategory.fiberProductSnd F g)).mpr f.isClosedMap

/-- A universally closed morphism of algebraic stacks which is representable by schemes
is quasi-compact.  On an affine base its representing scheme is quasi-compact over a
compact scheme, hence has compact point space. -/
theorem quasiCompact_of_universallyClosed_of_relativelyRepresentable
    [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴] {F : 𝒳 ⥤ᵇ 𝒴}
    (hF : F.RelativelyRepresentable) (hclosed : UniversallyClosed F) :
    QuasiCompact F := by
  intro B g
  obtain ⟨U, E, hE⟩ := hF (Spec B) g
  let f := (E.comp (BasedCategory.fiberProductSnd F g)).overHom
  have hf : _root_.AlgebraicGeometry.UniversallyClosed f :=
    ((universallyClosed_iff_relativelyRepresentableWith_universallyClosed hF).mp
      hclosed).2 (Spec B) g U E hE
  let _ : _root_.AlgebraicGeometry.UniversallyClosed f := hf
  let _ : CompactSpace U :=
    _root_.AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace f
  have hU : BasedCategory.IsQuasiCompact (overBased U) := by
    obtain ⟨e⟩ := Scheme.nonempty_homeomorph_pointSpace U
    exact e.symm.compactSpace
  exact isQuasiCompact_of_equivalence E hE hU

/-- Supporting schematic comparison for Definition 4.8.1, part (2): a representable
morphism is separated in the stack sense exactly
when every scheme-valued fiber is a separated morphism of schemes.

The comparison identifies the relative diagonal of a scheme-valued base change with the
ordinary diagonal of its representing scheme.  For an arbitrary test point of `F.diag`,
`relativeDiagonalTargetLiftIso` factors it through such a base-changed diagonal. -/
theorem isSeparatedRepresentable_iff_relativelyRepresentableWith_isSeparated
    [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴] {F : 𝒳 ⥤ᵇ 𝒴}
    (hF : F.RelativelyRepresentable) :
    IsSeparatedRepresentable F ↔ F.RelativelyRepresentableWith
      (@_root_.AlgebraicGeometry.IsSeparated : MorphismProperty Scheme.{u}) := by
  constructor
  · intro hdiag
    refine ⟨hF, ?_⟩
    intro T g U E hE
    let H := E.comp (fiberProductSnd F g)
    let _ : E.toFunctor.IsEquivalence := hE
    have hdiagBase := hdiag.diag_fiberProductSnd g
    have hdiagH := hdiagBase.diag_comp_of_isEquivalence E
    obtain ⟨e⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map H
    have hdiagMap := hdiagH.diag_of_iso e
    exact (relativelyRepresentableWith_proper_diag_iff_isSeparated H.overHom).mp hdiagMap
  · intro hsep
    refine ⟨(representable_of_relativelyRepresentable hF).relativelyRepresentable_diag, ?_⟩
    intro T g U E hE
    let q := (relativeDiagonalPointFst F g).comp F
    let H := fiberProductSnd F q
    obtain ⟨V, R, hR⟩ := hF T q
    let _ : R.toFunctor.IsEquivalence := hR
    let f := (R.comp H).overHom
    have hfsep : _root_.AlgebraicGeometry.IsSeparated f :=
      hsep.2 T q V R hR
    have hmapDiag : (overBased.map f).diag.RelativelyRepresentableWith
        (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) :=
      (relativelyRepresentableWith_proper_diag_iff_isSeparated f).mpr hfsep
    obtain ⟨eR⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map (R.comp H)
    have hRdiag : (R.comp H).diag.RelativelyRepresentableWith
        (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) :=
      hmapDiag.diag_of_iso eR.symm
    obtain ⟨J, ⟨α⟩, ⟨β⟩⟩ :=
      CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor R
    have hJ : J.toFunctor.IsEquivalence :=
      Functor.IsEquivalence.mk' R.toFunctor
        ((BasedNatTrans.forgetful _ _).mapIso β).symm
        ((BasedNatTrans.forgetful _ _).mapIso α)
    let _ : J.toFunctor.IsEquivalence := hJ
    have hJdiag := hRdiag.diag_comp_of_isEquivalence J
    let eH : (J.comp (R.comp H)) ≅ H :=
      (eqToIso (CategoryTheory.BasedFunctor.comp_assoc J R H).symm).trans
        ((isoWhiskerRight β H).trans
          (eqToIso (CategoryTheory.BasedFunctor.id_comp H)))
    have hHdiag : H.diag.RelativelyRepresentableWith
        (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) :=
      hJdiag.diag_of_iso eH
    let K := baseChangeDiagonalTarget F q
    let C := baseChangeDiagonalComparison F q
    let _ : C.toFunctor.IsEquivalence :=
      isEquivalence_baseChangeDiagonalComparison F q
    have hCK : (C.comp (fiberProductSnd F.diag K)).RelativelyRepresentableWith
        (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) := by
      rw [baseChangeDiagonalComparison_comp_snd]
      exact hHdiag
    have hK : (fiberProductSnd F.diag K).RelativelyRepresentableWith
        (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) :=
      hCK.of_comp_isEquivalence C
    let L := relativeDiagonalTargetLift F g
    have hNested := hK.fiberProductSnd L
    let A := fiberProductAssoc F.diag K L
    let _ : A.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductAssoc F.diag K L
    have hAcomp : (A.comp (fiberProductSnd F.diag (L.comp K))).RelativelyRepresentableWith
        (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) := by
      rw [fiberProductAssoc_comp_snd]
      exact hNested
    have hDirect : (fiberProductSnd F.diag (L.comp K)).RelativelyRepresentableWith
        (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) :=
      hAcomp.of_comp_isEquivalence A
    let M := fiberProductMapRightIso F.diag (relativeDiagonalTargetLiftIso F g)
    let _ : M.toFunctor.IsEquivalence :=
      isEquivalence_fiberProductMapRightIso F.diag (relativeDiagonalTargetLiftIso F g)
    have hDirect' : (M.comp (fiberProductSnd F.diag g)).RelativelyRepresentableWith
        (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) := by
      rw [show M.comp (fiberProductSnd F.diag g) =
          fiberProductSnd F.diag (L.comp K) by
        apply CategoryTheory.BasedFunctor.ext_of_toFunctor_eq
        rfl]
      exact hDirect
    have hg : (fiberProductSnd F.diag g).RelativelyRepresentableWith
        (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) :=
      hDirect'.of_comp_isEquivalence M
    let _ : E.toFunctor.IsEquivalence := hE
    have hEprop := hg.comp_of_isEquivalence E
    exact (relativelyRepresentableWith_iff_overHom
      (E.comp (fiberProductSnd F.diag g))).mp hEprop

/-- Supporting scheme-level comparison for Definition 4.8.1, part (2): for a morphism of
algebraic stacks representable by schemes,
properness in the sense of part (2) — universally closed, separated, and of finite
type — coincides with the transfer of the scheme property `AlgebraicGeometry.IsProper`
along the representability, i.e. with every base change by a morphism from a scheme
being a proper morphism of schemes (Definition 4.3.2, part (3)). -/
theorem isProperRepresentable_iff_relativelyRepresentableWith_isProper
    [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴] {F : 𝒳 ⥤ᵇ 𝒴}
    (hF : F.RelativelyRepresentable) :
    IsProperRepresentable F ↔
      F.RelativelyRepresentableWith
        (@_root_.AlgebraicGeometry.IsProper : MorphismProperty Scheme.{u}) := by
  have hUC :=
    universallyClosed_iff_relativelyRepresentableWith_universallyClosed hF
  have hSep :=
    isSeparatedRepresentable_iff_relativelyRepresentableWith_isSeparated hF
  have hLFT := hasProperty_iff_relativelyRepresentableWith
    isSmoothLocal_locallyOfFiniteType hF
  constructor
  · rintro ⟨hclosed, hseparated, hlft, _⟩
    refine ⟨hF, ?_⟩
    intro T g U E hE
    exact
      { toIsSeparated := (hSep.mp hseparated).2 T g U E hE
        toUniversallyClosed := (hUC.mp hclosed).2 T g U E hE
        toLocallyOfFiniteType := (hLFT.mp hlft).2 T g U E hE }
  · intro hproper
    have hclosedRel : F.RelativelyRepresentableWith
        (@_root_.AlgebraicGeometry.UniversallyClosed : MorphismProperty Scheme.{u}) :=
      hproper.mono fun X Y f hf ↦ by
        let _ : _root_.AlgebraicGeometry.IsProper f := hf
        infer_instance
    have hseparatedRel : F.RelativelyRepresentableWith
        (@_root_.AlgebraicGeometry.IsSeparated : MorphismProperty Scheme.{u}) :=
      hproper.mono fun X Y f hf ↦ by
        let _ : _root_.AlgebraicGeometry.IsProper f := hf
        infer_instance
    have hlftRel : F.RelativelyRepresentableWith
        (@_root_.AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
      hproper.mono fun X Y f hf ↦ by
        let _ : _root_.AlgebraicGeometry.IsProper f := hf
        infer_instance
    have hclosed : UniversallyClosed F := hUC.mpr hclosedRel
    exact ⟨hclosed, hSep.mpr hseparatedRel, hLFT.mpr hlftRel,
      quasiCompact_of_universallyClosed_of_relativelyRepresentable hF hclosed⟩

/- LEDGER (discussion after `def:separated-proper`): for a separated algebraic stack `𝒳`
over a scheme `S` and a field-valued point `x : Spec k → 𝒳`, the stabilizer `G_x` — the
base change of the diagonal along `(x, x) : Spec k → 𝒳 × 𝒳` — is a proper group algebraic
space over `k`, and even a group scheme by `thm:group-algebraic-spaces-are-schemes`
(§5.5, not yet formalized); if moreover `𝒳` has affine diagonal, then `G_x` is proper and
affine, hence finite. Blocked on the stabilizer comparison lemmas of §4.2
(`part4.2.2-stabilizers`) together with §5.5.

LEDGER (unlabeled example after the stabilizer discussion): for an abstract finite group
`G`, the classifying stack `BG → Spec ℤ` is proper; for a proper group scheme `G → S`
(e.g. an abelian scheme), `BG → S` is proper; for a non-finite affine group scheme
(e.g. `𝔾ₘ → Spec ℤ`), `BG → S` is universally closed but not separated. Blocked on
classifying stacks `BG` (§3.4/§3.5 ledgers, `def:classifying-prestack`).

LEDGER (unlabeled easy exercise): the moduli stacks `𝓜_{(0,0)}`, `𝓜_{(0,1)}`,
`𝓜_{(0,2)}`, and `𝓜_{(1,0)}` are not separated. Blocked on the moduli stacks of curves
(§3.4/§3.5 ledgers, `thm:mg-is-algebraic`).

LEDGER (unlabeled example: `Bun_{r,d}(C)` is not separated): since `Bun_{r,d}(C)` has
affine diagonal (`ex:moduli-affine-diagonal`, §4.3, itself ledgered) and infinite
automorphism groups, it is not separated over the base field. Blocked on the moduli stack
of bundles (§4.1 ledger, `thm:bunC-is-algebraic`). -/

end AlgebraicGeometry.BasedFunctor

end DefSeparatedProper

section ExerProperActions

open CategoryTheory Limits Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.PresheafGroupoid

variable {k : Type u} [Field k] {G U₀ : Scheme.{u}}
  (πG : G ⟶ Spec (CommRingCat.of k)) (πU : U₀ ⟶ Spec (CommRingCat.of k))
  (m : pullback πG πG ⟶ G)
  (eG : (Spec (CommRingCat.of k)) ⟶ G) (ι : G ⟶ G) (σ : pullback πG πU ⟶ U₀)

variable (hm : m ≫ πG = pullback.fst πG πG ≫ πG) (heG : eG ≫ πG = 𝟙 (Spec (CommRingCat.of k)))
  (hι : ι ≫ πG = πG) (hσ : σ ≫ πU = pullback.snd πG πU ≫ πU)

variable (hm_assoc : ∀ {T : Scheme.{u}} (g₁ g₂ g₃ : T ⟶ G) (h₁₂ : g₁ ≫ πG = g₂ ≫ πG)
    (h₂₃ : g₂ ≫ πG = g₃ ≫ πG) (h₁ : (pullback.lift g₁ g₂ h₁₂ ≫ m) ≫ πG = g₃ ≫ πG)
    (h₂ : g₁ ≫ πG = (pullback.lift g₂ g₃ h₂₃ ≫ m) ≫ πG),
    pullback.lift (pullback.lift g₁ g₂ h₁₂ ≫ m) g₃ h₁ ≫ m =
      pullback.lift g₁ (pullback.lift g₂ g₃ h₂₃ ≫ m) h₂ ≫ m)

variable (hm_one_mul : ∀ {T : Scheme.{u}} (g : T ⟶ G)
    (h : (g ≫ πG ≫ eG) ≫ πG = g ≫ πG), pullback.lift (g ≫ πG ≫ eG) g h ≫ m = g)

variable (hm_mul_one : ∀ {T : Scheme.{u}} (g : T ⟶ G)
    (h : g ≫ πG = (g ≫ πG ≫ eG) ≫ πG), pullback.lift g (g ≫ πG ≫ eG) h ≫ m = g)

variable (hm_inv_mul : ∀ {T : Scheme.{u}} (g : T ⟶ G) (h : (g ≫ ι) ≫ πG = g ≫ πG),
    pullback.lift (g ≫ ι) g h ≫ m = g ≫ πG ≫ eG)

variable (hm_mul_inv : ∀ {T : Scheme.{u}} (g : T ⟶ G) (h : g ≫ πG = (g ≫ ι) ≫ πG),
    pullback.lift g (g ≫ ι) h ≫ m = g ≫ πG ≫ eG)

variable (hσ_mul : ∀ {T : Scheme.{u}} (g' g : T ⟶ G) (u : T ⟶ U₀)
    (hg : g' ≫ πG = g ≫ πG) (hu : g ≫ πG = u ≫ πU)
    (h₁ : (pullback.lift g' g hg ≫ m) ≫ πG = u ≫ πU)
    (h₂ : g' ≫ πG = (pullback.lift g u hu ≫ σ) ≫ πU),
    pullback.lift (pullback.lift g' g hg ≫ m) u h₁ ≫ σ =
      pullback.lift g' (pullback.lift g u hu ≫ σ) h₂ ≫ σ)

variable (hσ_one : ∀ {T : Scheme.{u}} (u : T ⟶ U₀)
    (h : (u ≫ πU ≫ eG) ≫ πG = u ≫ πU), pullback.lift (u ≫ πU ≫ eG) u h ≫ σ = u)

/-- **Exercise 4.8.6** (`exer:proper-actions`) (part (a)): for an action of an algebraic
group `G` over a field `k` on a `k`-scheme `U`, call the action *proper* if the action map
`Ψ : G × U → U × U`, `(g, u) ↦ (g·u, u)` (`PresheafGroupoid.actionMap`) is a proper
morphism of schemes. Then the action is proper if and only if the quotient stack `[U/G]` —
here a stackification `𝒳` of the quotient prestack of the action groupoid — is separated.

Part (b) of the exercise (for `u ∈ U(k)` with orbit map `Ψ_u : G → U`, `g ↦ g·u`: `Ψ_u`
proper ⟺ `u : Spec k → [U/G]` proper ⟺ the orbit `G·u ⊆ U` is closed and the stabilizer
`G_u` is proper) is not stated: it needs the orbit and stabilizer *group schemes* of a
point (§4.2.2 ledger; §4.5's `groupoidOrbit` is only a set of points), and its hint needs
Generic Flatness for algebraic stacks (Exercise 4.3.8, ledgered) and fppf descent.

"Algebraic group over `k`" is rendered as a smooth affine group scheme of finite type over
`Spec k` — the standing hypotheses of Theorem 4.1.10 plus finite type. See COMMENTARY.md. -/
theorem isProper_actionMap_iff_isSeparated_quotientPrestack_ofAction
    [Smooth πG] [IsAffineHom πG] [LocallyOfFiniteType πG] [QuasiCompact πG]
    {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}} [𝒳st.p.IsFiberedInGroupoids]
    {i : (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
      hm_inv_mul hm_mul_inv hσ_mul hσ_one).quotientPrestack ⥤ᵇ 𝒳st}
    (hi : i.IsStackification Scheme.etaleTopology) :
    _root_.AlgebraicGeometry.IsProper (actionMap πG πU σ hσ) ↔
      BasedFunctor.IsSeparated 𝒳st.toBase := by
  sorry

end AlgebraicGeometry.PresheafGroupoid

end ExerProperActions

section LemQuotientStackDiagonal

open CategoryTheory Limits Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.PresheafGroupoid

variable {S G U₀ : Scheme.{u}} (πG : G ⟶ S) (πU : U₀ ⟶ S) (m : pullback πG πG ⟶ G)
  (eG : S ⟶ G) (ι : G ⟶ G) (σ : pullback πG πU ⟶ U₀)

variable (hm : m ≫ πG = pullback.fst πG πG ≫ πG) (heG : eG ≫ πG = 𝟙 S)
  (hι : ι ≫ πG = πG) (hσ : σ ≫ πU = pullback.snd πG πU ≫ πU)

variable (hm_assoc : ∀ {T : Scheme.{u}} (g₁ g₂ g₃ : T ⟶ G) (h₁₂ : g₁ ≫ πG = g₂ ≫ πG)
    (h₂₃ : g₂ ≫ πG = g₃ ≫ πG) (h₁ : (pullback.lift g₁ g₂ h₁₂ ≫ m) ≫ πG = g₃ ≫ πG)
    (h₂ : g₁ ≫ πG = (pullback.lift g₂ g₃ h₂₃ ≫ m) ≫ πG),
    pullback.lift (pullback.lift g₁ g₂ h₁₂ ≫ m) g₃ h₁ ≫ m =
      pullback.lift g₁ (pullback.lift g₂ g₃ h₂₃ ≫ m) h₂ ≫ m)

variable (hm_one_mul : ∀ {T : Scheme.{u}} (g : T ⟶ G)
    (h : (g ≫ πG ≫ eG) ≫ πG = g ≫ πG), pullback.lift (g ≫ πG ≫ eG) g h ≫ m = g)

variable (hm_mul_one : ∀ {T : Scheme.{u}} (g : T ⟶ G)
    (h : g ≫ πG = (g ≫ πG ≫ eG) ≫ πG), pullback.lift g (g ≫ πG ≫ eG) h ≫ m = g)

variable (hm_inv_mul : ∀ {T : Scheme.{u}} (g : T ⟶ G) (h : (g ≫ ι) ≫ πG = g ≫ πG),
    pullback.lift (g ≫ ι) g h ≫ m = g ≫ πG ≫ eG)

variable (hm_mul_inv : ∀ {T : Scheme.{u}} (g : T ⟶ G) (h : g ≫ πG = (g ≫ ι) ≫ πG),
    pullback.lift g (g ≫ ι) h ≫ m = g ≫ πG ≫ eG)

variable (hσ_mul : ∀ {T : Scheme.{u}} (g' g : T ⟶ G) (u : T ⟶ U₀)
    (hg : g' ≫ πG = g ≫ πG) (hu : g ≫ πG = u ≫ πU)
    (h₁ : (pullback.lift g' g hg ≫ m) ≫ πG = u ≫ πU)
    (h₂ : g' ≫ πG = (pullback.lift g u hu ≫ σ) ≫ πU),
    pullback.lift (pullback.lift g' g hg ≫ m) u h₁ ≫ σ =
      pullback.lift g' (pullback.lift g u hu ≫ σ) h₂ ≫ σ)

variable (hσ_one : ∀ {T : Scheme.{u}} (u : T ⟶ U₀)
    (h : (u ≫ πU ≫ eG) ≫ πG = u ≫ πU), pullback.lift (u ≫ πU ≫ eG) u h ≫ σ = u)

/-- **Lemma 4.3.14** (`lem:quotient-stack-diagonal`, §4.3): let `S` be an affine scheme and
`G → S` a smooth affine group scheme acting on an `S`-scheme `U`. If `U` has affine
diagonal, then so does the quotient stack `[U/G]` — here a stackification `𝒳` of the
quotient prestack of the action groupoid (Example 4.4.3), the rendering Theorem 4.1.10 is
stated for in
`StacksAndModuli/Section4.4-Equivalence-Relations/part4.4.4-algebraicity.lean`.

The proof (deferred) is the book's: `[U/G]` is algebraic
(`isAlgebraicStack_quotientPrestack_ofAction`), so Representability of the Diagonal
(Theorem 4.2.2 (2)) makes `Δ_{[U/G]}` representable;
smooth descent for representable morphisms (Proposition 4.3.9) then reduces affineness of `Δ_{[U/G]}` to
affineness of its base change along the smooth surjection `U × U → [U/G]  × [U/G]`, which is
`U ×_{[U/G]} U = G ×_S U → U ×_S U` — the action map, affine because `G → S` is affine and
`U` has affine diagonal.  The scheme-level input — the pair `(σ, pr₂) : G ×_S U → U ⨯ U`
has any multiplicative base-change-stable property containing closed immersions once
`πG` and `Δ_{U/S}` do and `S` is affine — is proved as
`AlgebraicGeometry.MorphismProperty.prodLift_actionPair`
(`StacksAndModuli/API/ActionGroupoidRelationAffine.lean`, via the graph-factorization
cancellation `CategoryTheory.MorphismProperty.of_comp_of_diagonal`); the remaining
obligation is the stack-level identification of the base-changed diagonal with the
base changes of that pair.

This block lives in §4.8 because it needs both `ofAction` (§4.4) and
`BasedFunctor.HasAffineDiagonal` (defined above in this file), and §4.3 can import
neither. -/
theorem hasAffineDiagonal_toBase_quotientPrestack_ofAction [IsAffine S] [Smooth πG]
    [IsAffineHom πG]
    (hU : _root_.AlgebraicGeometry.IsAffineHom (pullback.diagonal πU))
    {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}}
    {i : (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
      hm_inv_mul hm_mul_inv hσ_mul hσ_one).quotientPrestack ⥤ᵇ 𝒳st}
    (hi : i.IsStackification Scheme.etaleTopology) :
    BasedFunctor.HasAffineDiagonal 𝒳st.toBase := by
  sorry

/-- **Lemma 4.3.14** (`lem:quotient-stack-diagonal`, §4.3) (quasi-affine case): with the
same hypotheses except that `U` is assumed only to have *quasi-affine* diagonal, the
quotient stack `[U/G]` has quasi-affine diagonal. The proof is the same descent argument,
run with `IsQuasiAffineHom` in place of `IsAffineHom`. -/
theorem hasQuasiAffineDiagonal_toBase_quotientPrestack_ofAction [IsAffine S] [Smooth πG]
    [IsAffineHom πG]
    (hU : _root_.AlgebraicGeometry.IsQuasiAffineHom (pullback.diagonal πU))
    {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}}
    {i : (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
      hm_inv_mul hm_mul_inv hσ_mul hσ_one).quotientPrestack ⥤ᵇ 𝒳st}
    (hi : i.IsStackification Scheme.etaleTopology) :
    BasedFunctor.HasQuasiAffineDiagonal 𝒳st.toBase := by
  sorry

end AlgebraicGeometry.PresheafGroupoid

end LemQuotientStackDiagonal
