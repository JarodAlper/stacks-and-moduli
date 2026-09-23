module

public import StacksAndModuli.«Section4.3-Properties».«part4.3.1-properties-of-morphisms»
public import StacksAndModuli.API.CommonCover
public import StacksAndModuli.«Section3.1-Descent».«part3.1.5-descending-properties»
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Properties of algebraic spaces and stacks

This module formalizes `def:properties-of-algebraic-spaces-and-stacks` of §4.3 (First
properties) of *Stacks and Moduli*, together with the subsequent unlabeled definition of
substacks (the section carries no `sec:`
label). It corresponds to the subsection "Properties of algebraic spaces and stacks".

Main declarations:
- `AlgebraicGeometry.Scheme.IsLocalAlong`: a property of schemes being local along a
  class of morphisms (e.g. smooth or étale surjections);
- `AlgebraicGeometry.BasedCategory.HasSchemePropertyAlong` and the specialization
  `HasSchemeProperty`: an algebraic stack having a property of schemes, tested on
  presentations, with the abbreviations `IsReduced` and `IsLocallyNoetherian`;
- `AlgebraicGeometry.BasedCategory.IsReduced` and `.IsLocallyNoetherian`: the named
  properties immediately following Definition 4.3.7.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section DefPropertiesOfAlgebraicSpacesAndStacks

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry

/-- **Definition 4.3.7** (`def:properties-of-algebraic-spaces-and-stacks`) (the
hypothesis on the property): let $\cP$ be a property of schemes and $\cQ$ a property of
morphisms of schemes. Then $\cP$ is *local along $\cQ$* if for every morphism
$f \colon X \to Y$ satisfying $\cQ$, the scheme $X$ has $\cP$ if and only if $Y$ does.
For $\cQ$ the étale (resp. smooth) surjections this is the book's "étale (resp. smooth)
local" property of schemes. -/
def Scheme.IsLocalAlong (P : Scheme.{u} → Prop) (Q : MorphismProperty Scheme.{u}) :
    Prop :=
  ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), Q f → (P X ↔ P Y)

/-- **Definition 4.3.7** (`def:properties-of-algebraic-spaces-and-stacks`) (the general
presentation-tested form): let $\cP$ be a property of schemes which is local along a
class $\cQ$ of morphisms and let $\cX$ be a prestack over $\Sch_{\ét}$. Then $\cX$ *has
property $\cP$ tested on $\cQ$-presentations* if for every presentation $U \to \cX$ (a
representable morphism from a scheme with property $\cQ$), the scheme $U$ has $\cP$.
For $\cQ$ the smooth (resp. étale) surjections and $\cX$ an algebraic (resp.
Deligne–Mumford) stack this is the book's "$\cX$ has property $\cP$". -/
def BasedCategory.HasSchemePropertyAlong (Q : MorphismProperty Scheme.{u})
    (P : Scheme.{u} → Prop) (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) : Prop :=
  ∀ (U : Scheme.{u}) (p : overBased U ⥤ᵇ 𝒳), BasedFunctor.RepresentableWith Q p → P U

/-- **Definition 4.3.7** (`def:properties-of-algebraic-spaces-and-stacks`) (algebraic
stacks): let $\cP$ be a smooth local property of schemes. An algebraic stack $\cX$ *has
property $\cP$* if for all smooth presentations $U \to \cX$, the scheme $U$ has $\cP$.
(For Deligne–Mumford stacks and étale local properties, use
`AlgebraicGeometry.BasedCategory.HasSchemePropertyAlong` with étale surjections.) -/
abbrev BasedCategory.HasSchemeProperty (P : Scheme.{u} → Prop)
    (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) : Prop :=
  BasedCategory.HasSchemePropertyAlong
    (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) P 𝒳

/-- **Definition 4.3.7** (`def:properties-of-algebraic-spaces-and-stacks`)
(independence of the presentation, the parenthetical "equivalently for all
presentations"): for a smooth local property $\cP$ of schemes and an algebraic stack
$\cX$, it is enough to check property $\cP$ on a single smooth presentation: if
$U \to \cX$ is a smooth presentation and $U$ has $\cP$, then the presentation scheme of
every smooth presentation has $\cP$. -/
theorem BasedCategory.hasSchemeProperty_of_exists {P : Scheme.{u} → Prop}
    (hP : Scheme.IsLocalAlong P (@Surjective ⊓ @Smooth))
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack 𝒳]
    (h : ∃ (U : Scheme.{u}) (p : overBased U ⥤ᵇ 𝒳),
      BasedFunctor.RepresentableWith (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u})
        p ∧ P U) :
    BasedCategory.HasSchemeProperty P 𝒳 := by
  obtain ⟨U, p, hp, hPU⟩ := h
  intro U' p' hp'
  obtain ⟨W, a, b, ha, hb⟩ := exists_common_cover_of_representableWith hp hp'
  exact (hP b hb).mp ((hP a ha).mpr hPU)

/-- API lemma used after Definition 4.3.7 (reducedness
is smooth local, from the unlabeled paragraph after the definition): reducedness of
schemes is smooth local: if `X ⟶ Y` is a smooth surjection of schemes, then `X` is
reduced if and only if `Y` is. (Derived from Proposition 3.1.30.) -/
theorem Scheme.isLocalAlong_isReduced :
    Scheme.IsLocalAlong (fun X : Scheme.{u} => IsReduced X) (@Surjective ⊓ @Smooth) := by
  rintro X Y f ⟨h₁, h₂⟩
  haveI := h₁
  haveI := h₂
  exact Scheme.isReduced_iff_of_smooth_of_surjective f

/-- API lemma used after Definition 4.3.7 (local
noetherianity is smooth local, from the unlabeled paragraph after the definition):
local noetherianity of schemes is smooth local: if `X ⟶ Y` is a smooth surjection of
schemes, then `X` is locally noetherian if and only if `Y` is. (Derived from
Proposition 3.1.30.) -/
theorem Scheme.isLocalAlong_isLocallyNoetherian :
    Scheme.IsLocalAlong (fun X : Scheme.{u} => IsLocallyNoetherian X)
      (@Surjective ⊓ @Smooth) := by
  rintro X Y f ⟨h₁, h₂⟩
  haveI := h₁
  haveI := h₂
  exact Scheme.isLocallyNoetherian_iff_of_fppf f

/-- **Definition 4.3.7** (`def:properties-of-algebraic-spaces-and-stacks`) (reduced
stacks): an algebraic stack is *reduced* if it has the smooth local property of
reducedness of schemes, i.e. the source of every smooth presentation is a reduced
scheme. -/
abbrev BasedCategory.IsReduced (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) : Prop :=
  BasedCategory.HasSchemeProperty (fun U => _root_.AlgebraicGeometry.IsReduced U) 𝒳

/-- **Definition 4.3.7** (`def:properties-of-algebraic-spaces-and-stacks`) (locally
noetherian stacks): an algebraic stack is *locally noetherian* if it has the smooth
local property of local noetherianity of schemes, i.e. the source of every smooth
presentation is a locally noetherian scheme. -/
abbrev BasedCategory.IsLocallyNoetherian (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) :
    Prop :=
  BasedCategory.HasSchemeProperty
    (fun U => _root_.AlgebraicGeometry.IsLocallyNoetherian U) 𝒳

/- LEDGER (regularity): the book also records that regularity of schemes is smooth local
(`prop:fpqc-descent-for-properties-of-schemes`) and hence defines regular algebraic
stacks. Mathlib has no class of regular schemes yet (only `IsRegularLocalRing` at the
level of stalks), so regular stacks are deferred until such a class is available.

LEDGER (unlabeled example): for a smooth affine group scheme `G → S` acting on a scheme
`U` over `S`, the quotient `[U/G]` is locally noetherian, reduced, or regular if and only
if `U` is. Blocked on quotient stacks `[U/G]` (§3.4/§3.5 ledgers). -/

end AlgebraicGeometry

namespace AlgebraicGeometry.BasedFunctor

variable {𝒯 : BasedCategory.{v₃, u₃} Scheme.{u}} {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}

/-- Background definition from the unnumbered "Substacks" definition following
Definition 4.3.7: let $\cZ \to \cX$ be a morphism of
stacks over $\Sch_{\ét}$. It exhibits $\cZ$ as a *locally closed substack* of $\cX$ if
it is fully faithful and representable by schemes by immersions (locally closed
immersions). Together with `AlgebraicGeometry.BasedFunctor.IsOpenSubstackInclusion` and
`AlgebraicGeometry.BasedFunctor.IsClosedSubstackInclusion` from §4.1, this realizes the
book's definition of closed, open, and locally closed substacks. -/
class IsLocallyClosedSubstackInclusion (F : 𝒯 ⥤ᵇ 𝒳) : Prop where
  /-- The underlying functor is full. -/
  full : F.toFunctor.Full
  /-- The underlying functor is faithful. -/
  faithful : F.toFunctor.Faithful
  /-- The inclusion is representable by schemes by immersions. -/
  relativelyRepresentableWith :
    F.RelativelyRepresentableWith (@IsImmersion : MorphismProperty Scheme.{u})

/- LEDGER (unlabeled exercise after the Substacks definition): for an action of a smooth
affine group scheme `G → S` on a scheme `U` over `S`, closed (resp. open) substacks of
`[U/G]` correspond to `G`-invariant closed (resp. open) subschemes of `U`. Blocked on
quotient stacks `[U/G]` (§3.4/§3.5 ledgers). -/

end AlgebraicGeometry.BasedFunctor

end DefPropertiesOfAlgebraicSpacesAndStacks
