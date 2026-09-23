module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Sites.Small
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.Over

/-!
# The lisse-étale site, restricted sites, and sites of affine schemes

This module formalizes the second half of §3.2 (Grothendieck topologies and sites) of
*Stacks and Moduli*, section label
`sec:sites` (the material still lies in Subsection 3.2.2, `subsec:big-sites`): the unlabelled
lisse-étale example, restricted (localized) categories and sites
(`ex:restricted-categories-and-sites`), and the unlabelled example on Grothendieck topologies
on the category of affine schemes, in the book's order.

Main results:
- `AlgebraicGeometry.etale_le_smooth`: étale morphisms of schemes are smooth;
- `AlgebraicGeometry.Scheme.LisseEtale`: the category of schemes smooth over a scheme `X`;
- `AlgebraicGeometry.Scheme.lisseEtaleTopology`: the lisse-étale topology, whose coverings
  are the jointly surjective families of étale morphisms, with membership criterion
  `AlgebraicGeometry.Scheme.mem_lisseEtaleTopology`;
- recalls of `CategoryTheory.Over` and `CategoryTheory.GrothendieckTopology.over` for the
  restricted category and site, and of `AlgebraicGeometry.Scheme.overGrothendieckTopology`
  for the relative big Zariski/étale/fppf/fpqc sites;
- `AlgebraicGeometry.AffineScheme.forgetToScheme_isCoverDense_of_le`: affine schemes are
  cover-dense in any topology refining the Zariski topology;
- `AlgebraicGeometry.AffineScheme.zariskiTopology`/`etaleTopology`/`fppfTopology`: the big
  sites on the category of affine schemes, which define the same categories of sheaves as the
  corresponding big sites on all schemes.

-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExRestrictedCategoriesAndSitesLisseEtale

open CategoryTheory AlgebraicGeometry

universe u

/-- Étale morphisms of schemes are smooth, as an inequality of morphism properties. -/
lemma AlgebraicGeometry.etale_le_smooth : @Etale ≤ @Smooth := fun _ _ f hf ↦
  have : Etale f := hf
  inferInstance

namespace AlgebraicGeometry.Scheme

/-- Background construction from Subsection 3.2.2 (the unlabelled example "Lisse-étale site",
underlying category): the underlying category of the lisse-étale site of a scheme `X`: the
category of schemes smooth over `X`, in which a morphism is an arbitrary (not necessarily
smooth) morphism of schemes over `X`. -/
protected abbrev LisseEtale (X : Scheme.{u}) : Type _ :=
  MorphismProperty.Over @Smooth ⊤ X

/-- Constructor for objects of the lisse-étale site of a scheme `X`: it takes a smooth
morphism `f : Y ⟶ X` as an input. -/
abbrev LisseEtale.mk {X Y : Scheme.{u}} (f : Y ⟶ X) [Smooth f] : X.LisseEtale :=
  MorphismProperty.Over.mk _ f inferInstance

/-- Background construction from Subsection 3.2.2 (the unlabelled example "Lisse-étale site"):
the lisse-étale topology on the category `X.LisseEtale` of schemes smooth over `X`: a sieve
on a smooth `X`-scheme `U` is a covering if and only if it contains a jointly surjective
family of étale `X`-morphisms `{Uᵢ ⟶ U}`; see
`AlgebraicGeometry.Scheme.mem_lisseEtaleTopology`. -/
abbrev lisseEtaleTopology (X : Scheme.{u}) : GrothendieckTopology X.LisseEtale :=
  X.smallGrothendieckTopology (P := @Etale)

/-- Background construction from Subsection 3.2.2 (the unlabelled example "Lisse-étale site",
description of the coverings): a sieve on a smooth `X`-scheme `U` is a covering for the
lisse-étale topology if and only if its pushforward to the category of `X`-schemes contains
an étale cover of `U` by `X`-schemes. -/
lemma mem_lisseEtaleTopology {X : Scheme.{u}} {U : X.LisseEtale} (R : Sieve U) :
    R ∈ X.lisseEtaleTopology U ↔
      ∃ (𝒰 : Cover.{u} (Scheme.precoverage @Etale)
          ((MorphismProperty.Over.forget @Smooth ⊤ X).obj U).left) (_ : 𝒰.Over X),
        𝒰.toPresieveOver ≤
          (R.functorPushforward (MorphismProperty.Over.forget @Smooth ⊤ X)).arrows := by
  have : (MorphismProperty.Over.forget @Smooth ⊤ X).LocallyCoverDense
      (X.overGrothendieckTopology @Etale) :=
    locallyCoverDense_of_le X etale_le_smooth
  rw [lisseEtaleTopology, smallGrothendieckTopology, Functor.mem_restrictedTopology_iff,
    mem_overGrothendieckTopology]

end AlgebraicGeometry.Scheme

end ExRestrictedCategoriesAndSitesLisseEtale

section ExRestrictedCategoriesAndSites

open CategoryTheory AlgebraicGeometry

universe u

/- **Example 3.2.12** (`ex:restricted-categories-and-sites`) (the restricted category): the
restricted category $\cS/S$ of an object $S$ of a category $\cS$: objects are maps $T \to S$
in $\cS$, and a morphism $(T' \to S) \to (T \to S)$ is a map $T' \to T$ over $S$. In Mathlib
this is the over category `Over S`. -/
example {𝒮 : Type*} [Category 𝒮] (S : 𝒮) := Over S

/- A map `T ⟶ S` determines an object of the restricted category. -/
example {𝒮 : Type*} [Category 𝒮] {S T : 𝒮} (f : T ⟶ S) : Over S :=
  Over.mk f

/- **Example 3.2.12** (`ex:restricted-categories-and-sites`) (the restricted site): if $\cS$
is a site, the restricted category $\cS/S$ is a site: a covering of $(T \to S)$ is a covering
$\{T_i \to T\}$ in $\cS$. -/
example {𝒮 : Type*} [Category 𝒮] (J : GrothendieckTopology 𝒮) (S : 𝒮) :
    GrothendieckTopology (Over S) :=
  J.over S

/- **Example 3.2.12** (`ex:restricted-categories-and-sites`) (description of the coverings):
a sieve on `(T ⟶ S)` is a covering for the restricted site exactly when the corresponding
sieve on `T` is a covering in `𝒮`. -/
example {𝒮 : Type*} [Category 𝒮] (J : GrothendieckTopology 𝒮) {S : 𝒮} {Y : Over S}
    (R : Sieve Y) :
    R ∈ J.over S Y ↔ Sieve.overEquiv Y R ∈ J Y.left :=
  J.mem_over_iff R

/- **Example 3.2.12** (`ex:restricted-categories-and-sites`) (the relative big sites):
applying this construction to a scheme $S$ yields the relative big Zariski, étale, fppf, and
fpqc sites $(\SchS)_{\Zar}$, $(\SchS)_{\et}$, $(\SchS)_{\fppf}$, $(\SchS)_{\fpqc}$. -/
example (S : Scheme.{u}) : GrothendieckTopology (Over S) :=
  Scheme.zariskiTopology.over S

example (S : Scheme.{u}) : GrothendieckTopology (Over S) :=
  Scheme.etaleTopology.over S

example (S : Scheme.{u}) : GrothendieckTopology (Over S) :=
  Scheme.fppfTopology.over S

example (S : Scheme.{u}) : GrothendieckTopology (Over S) :=
  Scheme.fpqcTopology.over S

/- The relative big étale site coincides with Mathlib's `overGrothendieckTopology` for the
étale morphism property, whose coverings are described by covers of the underlying scheme. -/
example (S : Scheme.{u}) : S.overGrothendieckTopology @Etale = Scheme.etaleTopology.over S :=
  rfl

end ExRestrictedCategoriesAndSites

section ExRestrictedCategoriesAndSitesAffine

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AffineScheme

/-- Let `K` be a Grothendieck topology on the category of schemes refining the Zariski
topology. Then the category of affine schemes is cover-dense in `(Sch, K)`: every scheme
admits a `K`-covering by affine schemes. -/
lemma forgetToScheme_isCoverDense_of_le {K : GrothendieckTopology Scheme.{u}}
    (hK : Scheme.zariskiTopology ≤ K) :
    forgetToScheme.IsCoverDense K where
  is_cover X := by
    refine K.superset_covering ?_ (hK _ X.affineCover.mem_grothendieckTopology)
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro Y f ⟨i⟩
    exact ⟨⟨.of (X.affineCover.X i), 𝟙 _, X.affineCover.f i, Category.id_comp _⟩⟩

instance : forgetToScheme.IsCoverDense Scheme.zariskiTopology.{u} :=
  forgetToScheme_isCoverDense_of_le le_rfl

instance : forgetToScheme.IsCoverDense Scheme.etaleTopology.{u} :=
  forgetToScheme_isCoverDense_of_le Scheme.zariskiTopology_le_etaleTopology

instance : forgetToScheme.IsCoverDense Scheme.fppfTopology.{u} :=
  forgetToScheme_isCoverDense_of_le <| Scheme.grothendieckTopology_monotone fun _ _ f hf ↦
    have : IsOpenImmersion f := hf
    ⟨inferInstance, inferInstance⟩

instance : forgetToScheme.IsCoverDense Scheme.fpqcTopology.{u} :=
  forgetToScheme_isCoverDense_of_le Scheme.zariskiTopology_le_fpqcTopology

/-- Background construction from Subsection 3.2.2 (the unlabelled example "Grothendieck
topologies on the category of affine schemes"): the big Zariski topology on the category of
affine schemes, induced from the big Zariski topology on all schemes. -/
noncomputable abbrev zariskiTopology : GrothendieckTopology AffineScheme.{u} :=
  forgetToScheme.inducedTopology Scheme.zariskiTopology

/-- Background construction from Subsection 3.2.2 (the unlabelled example "Grothendieck
topologies on the category of affine schemes"): the big étale topology on the category of
affine schemes, induced from the big étale topology on all schemes. -/
noncomputable abbrev etaleTopology : GrothendieckTopology AffineScheme.{u} :=
  forgetToScheme.inducedTopology Scheme.etaleTopology

/-- Background construction from Subsection 3.2.2 (the unlabelled example "Grothendieck
topologies on the category of affine schemes"): the big fppf topology on the category of
affine schemes, induced from the big fppf topology on all schemes. -/
noncomputable abbrev fppfTopology : GrothendieckTopology AffineScheme.{u} :=
  forgetToScheme.inducedTopology Scheme.fppfTopology

end AlgebraicGeometry.AffineScheme

/- Background construction from Subsection 3.2.2 (the unlabelled example "Grothendieck
topologies on the category of affine schemes", main claim): the big sites on the category of
affine schemes define the same categories of sheaves as the corresponding big sites on the
category of all schemes; here for the étale topology, and verbatim the same for the Zariski
and fppf topologies below. -/
noncomputable example (A : Type*) [Category A]
    [∀ X : Scheme.{u}ᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow X AffineScheme.forgetToScheme.op) A] :
    Sheaf Scheme.etaleTopology.{u} A ≌ Sheaf AffineScheme.etaleTopology.{u} A :=
  (AffineScheme.forgetToScheme.sheafPushforwardContinuous A
    AffineScheme.etaleTopology Scheme.etaleTopology).asEquivalence

noncomputable example (A : Type*) [Category A]
    [∀ X : Scheme.{u}ᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow X AffineScheme.forgetToScheme.op) A] :
    Sheaf Scheme.zariskiTopology.{u} A ≌ Sheaf AffineScheme.zariskiTopology.{u} A :=
  (AffineScheme.forgetToScheme.sheafPushforwardContinuous A
    AffineScheme.zariskiTopology Scheme.zariskiTopology).asEquivalence

noncomputable example (A : Type*) [Category A]
    [∀ X : Scheme.{u}ᵒᵖ,
      Limits.HasLimitsOfShape (StructuredArrow X AffineScheme.forgetToScheme.op) A] :
    Sheaf Scheme.fppfTopology.{u} A ≌ Sheaf AffineScheme.fppfTopology.{u} A :=
  (AffineScheme.forgetToScheme.sheafPushforwardContinuous A
    AffineScheme.fppfTopology Scheme.fppfTopology).asEquivalence

end ExRestrictedCategoriesAndSitesAffine
