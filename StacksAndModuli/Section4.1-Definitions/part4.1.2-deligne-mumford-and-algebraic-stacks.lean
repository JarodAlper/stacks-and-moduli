module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»
public import StacksAndModuli.API.FiberProductIdentity
public import StacksAndModuli.API.PresheafPrestackComparison
public import StacksAndModuli.API.PresheafFiberProduct
public import StacksAndModuli.API.RelativelyRepresentableSourceEquivalence
public import StacksAndModuli.«Section3.2-Sites».«part3.2.3-restricted-and-affine-sites»
public import StacksAndModuli.«Section3.5-Stacks».«part3.5.1-the-definition»
public import StacksAndModuli.«Section3.5-Stacks».«part3.5.2-first-examples»
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Deligne–Mumford stacks and algebraic stacks

This module formalizes **Definition 4.1.3** (`def:representable-morphisms`),
**Definition 4.1.4** (`def:deligne-mumford-stack`), and **Definition 4.1.6**
(`def:algebraic-stack`), together with the unlabeled
definition of open and closed substacks and the unlabeled fiber-products exercise, of §4.1
(Definitions of algebraic spaces and stacks) of *Stacks and Moduli*,
label `sec:algebraic-spaces-and-stacks`.
**Remark 4.1.5** (`rmk:representability-difference`) is recorded as prose in its section
block together with its formalizable half, the comparison statement
`AlgebraicGeometry.BasedFunctor.RelativelyRepresentableWith.representableWith`.

Main results:
- `AlgebraicGeometry.BasedFunctor.Representable` and
  `AlgebraicGeometry.BasedFunctor.RepresentableWith`: **Definition 4.1.3**
  (`def:representable-morphisms`), a morphism of prestacks over `Sch`
  being representable (all base changes by schemes are algebraic spaces), and having a
  property `P` of morphisms of schemes that is stable under base change and étale-local on
  the source;
- `AlgebraicGeometry.IsDeligneMumfordStack`: **Definition 4.1.4**
  (`def:deligne-mumford-stack`), étale stacks over `Sch` with a surjective
  étale representable presentation by a scheme;
- `AlgebraicGeometry.IsAlgebraicStack`: **Definition 4.1.6** (`def:algebraic-stack`),
  étale stacks over `Sch` with a surjective smooth
  representable presentation by a scheme;
- `AlgebraicGeometry.BasedFunctor.IsOpenSubstackInclusion` and
  `AlgebraicGeometry.BasedFunctor.IsClosedSubstackInclusion`: the unlabeled definition of
  open and closed substacks;
- the theorem that fiber products of algebraic spaces are algebraic spaces. The
  Deligne–Mumford-stack and algebraic-stack cases of the same unlabeled exercise are
  continued in the following part, after the reusable presentation API they require.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefRepresentableMorphisms

open CategoryTheory Functor Limits Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- **Definition 4.1.3** (`def:representable-morphisms`): let $F \colon \cX \to \cY$ be a
morphism of prestacks over $\Sch$. Then $F$ is
*representable* if for every scheme $T$ and every morphism $\Sch/T \to \cY$ of prestacks,
the fiber product $\cX \times_{\cY} \Sch/T$ is an algebraic space. -/
def Representable (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  ∀ (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒴), ∃ X : Scheme.{u}ᵒᵖ ⥤ Type u,
    IsAlgebraicSpace X ∧ (fiberProduct F g).IsRepresentedByPresheaf X

/-- A morphism of prestacks over `Sch` that is representable by schemes is representable:
schemes are algebraic spaces. -/
lemma representable_of_relativelyRepresentable {F : 𝒳 ⥤ᵇ 𝒴}
    (h : F.RelativelyRepresentable) : Representable F := by
  intro T g
  obtain ⟨T', hT'⟩ := h T g
  exact ⟨yoneda.obj T', inferInstance, hT'.isRepresentedByPresheaf⟩

/-- **Definition 4.1.3** (`def:representable-morphisms`) (the "has property $\cP$"
refinement): let $\cP$ be a property of morphisms of schemes stable under base change and
étale-local on the source, and let $F \colon \cX \to \cY$ be a morphism of prestacks over
$\Sch$. Then $F$ is representable *with property $\cP$* if it is representable and for
every morphism $T \to \cY$ from a scheme, every realization of the fiber product
$\cX \times_{\cY} \Sch/T$ as an algebraic space $X$, and every étale presentation
$U \to X$ by a scheme, the composition $U \to X \to T$ has property $\cP$. -/
def RepresentableWith (P : MorphismProperty Scheme.{u}) (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  Representable F ∧
    ∀ (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒴) (X : Scheme.{u}ᵒᵖ ⥤ Type u),
      IsAlgebraicSpace X → ∀ (E : ofPresheaf X ⥤ᵇ fiberProduct F g),
        E.toFunctor.IsEquivalence → ∀ (U : Scheme.{u}) (q : yoneda.obj U ⟶ X),
          MorphismProperty.presheaf (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u})
            q →
          P ((overBasedToOfPresheafYoneda U).comp ((ofPresheaf.map q).comp
            (E.comp (fiberProductSnd F g)))).overHom

/-- A morphism of prestacks that is representable with a property is representable. -/
lemma RepresentableWith.representable {P : MorphismProperty Scheme.{u}} {F : 𝒳 ⥤ᵇ 𝒴}
    (h : RepresentableWith P F) : Representable F :=
  h.1

/-- Representability with a property is monotone in the property. -/
lemma RepresentableWith.mono {P Q : MorphismProperty Scheme.{u}} (hPQ : P ≤ Q)
    {F : 𝒳 ⥤ᵇ 𝒴} (h : RepresentableWith P F) : RepresentableWith Q F :=
  ⟨h.1, fun T g X hX E hE U q hq => hPQ _ (h.2 T g X hX E hE U q hq)⟩

/-- API lemma for Definition 4.1.3 (compatibility of the
presheaf-level and prestack-level notions): let $\varphi \colon X \to Y$ be a morphism of
presheaves on $\Sch$ that is
representable by schemes with a property $\cP$ stable under base change. Then the induced
morphism of associated prestacks is relatively representable with property $\cP$: the
fiber product of prestacks over a map from $\Sch/T$ is represented by the scheme
representing the fiber product of presheaves over $T$. -/
theorem relativelyRepresentableWith_ofPresheaf_map {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] {X Y : Scheme.{u}ᵒᵖ ⥤ Type u} {φ : X ⟶ Y}
    (hφ : MorphismProperty.presheaf P φ) :
    (ofPresheaf.map φ).RelativelyRepresentableWith P := by
  refine ⟨fun S g => ⟨hφ.rep.pullback g.ofPresheafHom,
    isRepresentedBy_fiberProduct_ofPresheafMap g hφ.rep⟩, ?_⟩
  intro S g S' E hE
  rw [overHom_comp_ofPresheafFiberProductProj g hφ.rep E]
  have h1 := hE
  have h2 := isEquivalence_ofPresheafFiberProductProj g hφ.rep
  have h3 : (E.comp (ofPresheafFiberProductProj g hφ.rep)).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans E.toFunctor (ofPresheafFiberProductProj g hφ.rep).toFunctor
  have h4 := CategoryTheory.BasedFunctor.isIso_overHom_of_isEquivalence _ h3
  exact MorphismProperty.RespectsIso.precomp P _ _ (hφ.property_snd _)

end AlgebraicGeometry.BasedFunctor

end DefRepresentableMorphisms

section DefDeligneMumfordStack

open CategoryTheory Functor Limits Opposite CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry

/-- **Definition 4.1.4** (`def:deligne-mumford-stack`): let $\cX$ be a stack over
$\Sch_{\ét}$. Then $\cX$ is a *Deligne–Mumford stack* if
there exist a scheme $U$ and a surjective, étale, and representable morphism
$U \to \cX$ (an *étale presentation*). -/
class IsDeligneMumfordStack (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) : Prop where
  isStack : BasedCategory.IsStack Scheme.etaleTopology 𝒳
  exists_presentation : ∃ (U : Scheme.{u}) (F : overBased U ⥤ᵇ 𝒳),
    BasedFunctor.RepresentableWith (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) F

/- The stack structure of a Deligne–Mumford stack is registered as an instance: it is a
property (a `Prop`-valued class), so no diamond issues can arise. -/
attribute [instance] IsDeligneMumfordStack.isStack

/-- A Deligne–Mumford stack is fibered in groupoids. -/
instance IsDeligneMumfordStack.isFiberedInGroupoids (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u})
    [IsDeligneMumfordStack 𝒳] : 𝒳.p.IsFiberedInGroupoids :=
  (IsDeligneMumfordStack.isStack (𝒳 := 𝒳)).isFiberedInGroupoids

/-- API lemma for Definition 4.1.4 (the following prose: algebraic
spaces are Deligne–Mumford stacks): the associated prestack of an étale
sheaf is a stack, and an étale presentation of the algebraic space induces an étale
presentation of the associated stack. -/
theorem IsDeligneMumfordStack.ofPresheaf (X : Scheme.{u}ᵒᵖ ⥤ Type u)
    [IsAlgebraicSpace X] : IsDeligneMumfordStack (BasedCategory.ofPresheaf X) where
  isStack :=
    { isFiberedInGroupoids := inferInstance
      isStack := (Functor.isStack_proj_yoneda_iff _ _).mpr IsAlgebraicSpace.isSheaf }
  exists_presentation := by
    refine ⟨IsAlgebraicSpace.presentationScheme X,
      (overBasedToOfPresheafYoneda _).comp
        (ofPresheaf.map (IsAlgebraicSpace.presentation X)), ?_⟩
    let h :=
      (BasedFunctor.relativelyRepresentableWith_ofPresheaf_map
          (IsAlgebraicSpace.presheaf_surjective_etale_presentation X)).comp_of_isEquivalence
        (overBasedToOfPresheafYoneda (IsAlgebraicSpace.presentationScheme X))
    refine ⟨BasedFunctor.representable_of_relativelyRepresentable h.1, ?_⟩
    intro T g Y hY E hE U q hq
    obtain ⟨S', E', hE'⟩ := h.1 T g
    have hE'' : ((ofPresheafYonedaToOverBased S').comp E').toFunctor.IsEquivalence :=
      inferInstanceAs
        ((ofPresheafYonedaToOverBased S').toFunctor ⋙ E'.toFunctor).IsEquivalence
    set e : yoneda.obj S' ≅ Y :=
      ofPresheaf.comparisonIso E ((ofPresheafYonedaToOverBased S').comp E') with he
    set Ξ : BasedFunctor (overBased S') (BasedCategory.fiberProduct
        ((overBasedToOfPresheafYoneda (IsAlgebraicSpace.presentationScheme X)).comp
          (ofPresheaf.map (IsAlgebraicSpace.presentation X))) g) :=
      (overBasedToOfPresheafYoneda S').comp ((ofPresheaf.map e.hom).comp E) with hΞ
    have hΞeq : Ξ.toFunctor.IsEquivalence := by
      rw [hΞ]
      exact inferInstanceAs ((overBasedToOfPresheafYoneda S').toFunctor ⋙
        ((ofPresheaf.map e.hom).toFunctor ⋙ E.toFunctor)).IsEquivalence
    have hΞP := h.2 T g S' Ξ hΞeq
    set u : U ⟶ S' := Yoneda.fullyFaithful.preimage (q ≫ e.inv) with hu
    have hyu : yoneda.map u = q ≫ e.inv := Yoneda.fullyFaithful.map_preimage _
    have hq' : MorphismProperty.presheaf
        (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) (yoneda.map u) := by
      rw [hyu]
      exact MorphismProperty.RespectsIso.postcomp _ e.inv q hq
    have hu' : (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) u :=
      MorphismProperty.of_relative_map hq'
    have hqeq : q = yoneda.map u ≫ e.hom := by
      rw [hyu, Category.assoc, e.inv_hom_id, Category.comp_id]
    have hfact : (overBasedToOfPresheafYoneda U).comp ((ofPresheaf.map q).comp E) =
        (overBased.map u).comp Ξ := by
      rw [hqeq, hΞ, show ofPresheaf.map (yoneda.map u ≫ e.hom) =
        (ofPresheaf.map (yoneda.map u)).comp (ofPresheaf.map e.hom) from rfl]
      rw [← BasedFunctor.comp_assoc, ← BasedFunctor.comp_assoc,
        overBasedToOfPresheafYoneda_comp_map]
      rfl
    have hcomp : (overBasedToOfPresheafYoneda U).comp ((ofPresheaf.map q).comp
        (E.comp (BasedCategory.fiberProductSnd _ g))) =
        (overBased.map u).comp (Ξ.comp (BasedCategory.fiberProductSnd _ g)) := by
      change ((overBasedToOfPresheafYoneda U).comp ((ofPresheaf.map q).comp E)).comp
        (BasedCategory.fiberProductSnd _ g) = _
      rw [hfact]
      rfl
    rw [hcomp, BasedFunctor.overHom_comp, BasedFunctor.overHom_map]
    exact MorphismProperty.comp_mem _ _ _ hu' hΞP

end AlgebraicGeometry

end DefDeligneMumfordStack

section RmkRepresentabilityDifference

/- Prose record of Remark 4.1.5: the essential difference between
an algebraic space
and a Deligne–Mumford stack is that one is a sheaf and the other a stack, but there is
also the technical difference that an étale presentation of an algebraic space is
required to be representable *by schemes*, while an étale presentation of a
Deligne–Mumford stack is only required to be representable (by algebraic spaces). If the
diagonal of a Deligne–Mumford stack is separated and quasi-compact, the two notions
agree: the diagonal is then representable by schemes and every presentation is
representable by schemes (Corollary 5.5.8, `cor:diagonal-of-a-DM-stack-is-quasi-affine`).
There are
Deligne–Mumford stacks whose diagonal is not quasi-compact, not separated, or not
representable by schemes (see the examples of §4.9). The unconditional comparison
direction — representable by schemes with $\cP$ implies representable with $\cP$ — is
`RelativelyRepresentableWith.representableWith` below. -/

open CategoryTheory Functor Limits Opposite CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- **Remark 4.1.5** (`rmk:representability-difference`) (comparison of the two
representability notions): let $F \colon \cX \to \cY$ be a morphism of prestacks over $\Sch$
that is representable by schemes with a property $\cP$. If $\cP$ is stable under
composition and contains the surjective étale morphisms, then $F$ is representable with
property $\cP$.

The proof: a fiber product $\cX \times_{\cY} \Sch/T$ is represented by a scheme $S'$, and
any algebraic space $X$ realizing it is then isomorphic to $\Mor(-, S')$ — the prestack of a
presheaf remembers the presheaf
(`CategoryTheory.BasedCategory.ofPresheaf.comparisonIso`). Under that isomorphism an étale
presentation $U \to X$ becomes a surjective étale morphism $U \to S'$ of schemes, and the
composition $U \to S' \to T$ has $\cP$ because $\cP$ contains the surjective étale morphisms
and is stable under composition. -/
theorem RelativelyRepresentableWith.representableWith {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderComposition]
    (hle : (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale :
      MorphismProperty Scheme.{u}) ≤ P) {F : 𝒳 ⥤ᵇ 𝒴}
    (h : F.RelativelyRepresentableWith P) : RepresentableWith P F := by
  refine ⟨representable_of_relativelyRepresentable h.1, ?_⟩
  intro T g X hX E hE U q hq
  have := hE
  -- a scheme `S'` representing the fiber product, and the presentation it induces
  obtain ⟨S', E', hE'⟩ := h.1 T g
  have := hE'
  have : ((ofPresheafYonedaToOverBased S').comp E').toFunctor.IsEquivalence :=
    inferInstanceAs ((ofPresheafYonedaToOverBased S').toFunctor ⋙ E'.toFunctor).IsEquivalence
  -- the algebraic space `X` realizing the fiber product is the scheme `S'`
  set e : yoneda.obj S' ≅ X :=
    ofPresheaf.comparisonIso E ((ofPresheafYonedaToOverBased S').comp E') with he
  set Ξ : overBased S' ⥤ᵇ BasedCategory.fiberProduct F g :=
    (overBasedToOfPresheafYoneda S').comp ((ofPresheaf.map e.hom).comp E) with hΞ
  have : Ξ.toFunctor.IsEquivalence := by
    rw [hΞ]
    exact inferInstanceAs ((overBasedToOfPresheafYoneda S').toFunctor ⋙
      ((ofPresheaf.map e.hom).toFunctor ⋙ E.toFunctor)).IsEquivalence
  have hΞP := h.2 T g S' Ξ inferInstance
  -- the étale presentation `q : U → X` is a surjective étale morphism of schemes `u : U → S'`
  set u : U ⟶ S' := Yoneda.fullyFaithful.preimage (q ≫ e.inv) with hu
  have hyu : yoneda.map u = q ≫ e.inv := Yoneda.fullyFaithful.map_preimage _
  have hq' : MorphismProperty.presheaf
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale :
        MorphismProperty Scheme.{u}) (yoneda.map u) := by
    rw [hyu]
    exact MorphismProperty.RespectsIso.postcomp _ e.inv q hq
  have hu' : (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale :
      MorphismProperty Scheme.{u}) u := MorphismProperty.of_relative_map hq'
  -- the projection to `T` factors as `U → S' → T`
  have hqeq : q = yoneda.map u ≫ e.hom := by
    rw [hyu, Category.assoc, e.inv_hom_id, Category.comp_id]
  have hfact : (overBasedToOfPresheafYoneda U).comp ((ofPresheaf.map q).comp E) =
      (overBased.map u).comp Ξ := by
    rw [hqeq, hΞ, show ofPresheaf.map (yoneda.map u ≫ e.hom) =
      (ofPresheaf.map (yoneda.map u)).comp (ofPresheaf.map e.hom) from rfl]
    rw [← CategoryTheory.BasedFunctor.comp_assoc, ← CategoryTheory.BasedFunctor.comp_assoc,
      overBasedToOfPresheafYoneda_comp_map]
    rfl
  have h4 : (overBasedToOfPresheafYoneda U).comp ((ofPresheaf.map q).comp
      (E.comp (BasedCategory.fiberProductSnd F g))) =
      (overBased.map u).comp (Ξ.comp (BasedCategory.fiberProductSnd F g)) := by
    show ((overBasedToOfPresheafYoneda U).comp ((ofPresheaf.map q).comp E)).comp
      (BasedCategory.fiberProductSnd F g) = _
    rw [hfact]
    rfl
  rw [h4, CategoryTheory.BasedFunctor.overHom_comp, CategoryTheory.BasedFunctor.overHom_map]
  exact P.comp_mem _ _ (hle _ hu') hΞP
end AlgebraicGeometry.BasedFunctor

end RmkRepresentabilityDifference

section DefRepresentableMorphisms

open CategoryTheory Functor Limits Opposite CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ v₄ u₄ uu

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{uu}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{uu}}
  {𝒴' : BasedCategory.{v₄, u₄} Scheme.{uu}}

/-- API lemma for Definition 4.1.3 (stability under base change):
if `F : 𝒳 → 𝒴` is representable and `G : 𝒴' → 𝒴` is any morphism of prestacks over
`Sch`, then the projection `𝒳 ×_𝒴 𝒴' → 𝒴'` is representable. -/
lemma Representable.fiberProductSnd {F : 𝒳 ⥤ᵇ 𝒴} (hF : Representable F) (G : 𝒴' ⥤ᵇ 𝒴) :
    Representable (BasedCategory.fiberProductSnd F G) := by
  intro T g
  obtain ⟨X, hX, hrep⟩ := hF T (g.comp G)
  exact ⟨X, hX, IsRepresentedByPresheaf.of_fiberProductAssoc F G g hrep⟩

/-- API lemma for Definition 4.1.3 (stability under base change,
with a property): if `F : 𝒳 → 𝒴` is representable with property `P`, so is the
projection `𝒳 ×_𝒴 𝒴' → 𝒴'`. -/
lemma RepresentableWith.fiberProductSnd {P : MorphismProperty Scheme.{uu}} {F : 𝒳 ⥤ᵇ 𝒴}
    (hF : RepresentableWith P F) (G : 𝒴' ⥤ᵇ 𝒴) :
    RepresentableWith P (BasedCategory.fiberProductSnd F G) := by
  refine ⟨hF.1.fiberProductSnd G, ?_⟩
  intro T g X hX E hE U q hq
  have h1 := hE
  have h2 := isEquivalence_fiberProductAssoc F G g
  exact hF.2 T (g.comp G) X hX (E.comp (fiberProductAssoc F G g))
    (Functor.isEquivalence_trans E.toFunctor (fiberProductAssoc F G g).toFunctor) U q hq

end AlgebraicGeometry.BasedFunctor

end DefRepresentableMorphisms

section DefAlgebraicStack

open CategoryTheory Functor Limits Opposite CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ v₄ u₄ u

namespace AlgebraicGeometry

/-- **Definition 4.1.6** (`def:algebraic-stack`): let $\cX$ be a stack over $\Sch_{\ét}$.
Then $\cX$ is an *algebraic stack* if there
exist a scheme $U$ and a surjective, smooth, and representable morphism $U \to \cX$ (a
*smooth presentation*).

In the literature most authors add a representability condition on the diagonal; as shown
in Theorem 4.2.1 , the existence of a smooth
presentation
already implies the representability of the diagonal, so no condition is imposed here. -/
class IsAlgebraicStack (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) : Prop where
  isStack : BasedCategory.IsStack Scheme.etaleTopology 𝒳
  exists_presentation : ∃ (U : Scheme.{u}) (F : overBased U ⥤ᵇ 𝒳),
    BasedFunctor.RepresentableWith (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) F

/- The stack structure of an algebraic stack is registered as an instance: it is a
property (a `Prop`-valued class), so no diamond issues can arise. -/
attribute [instance] IsAlgebraicStack.isStack

/-- An algebraic stack is fibered in groupoids. (Stated separately from
`CategoryTheory.BasedCategory.IsStack.isFiberedInGroupoids` because that instance leaves the
Grothendieck topology a metavariable, so instance search does not chain through it.) -/
instance IsAlgebraicStack.isFiberedInGroupoids (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u})
    [IsAlgebraicStack 𝒳] : 𝒳.p.IsFiberedInGroupoids :=
  (IsAlgebraicStack.isStack (𝒳 := 𝒳)).isFiberedInGroupoids

/-- Supporting instance for Definition 4.1.6 (the following prose: Deligne–Mumford
stacks are algebraic): an étale presentation is a smooth
presentation, since étale morphisms of schemes are smooth. -/
instance (priority := 900) IsAlgebraicStack.of_isDeligneMumfordStack
    (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) [IsDeligneMumfordStack 𝒳] :
    IsAlgebraicStack 𝒳 where
  isStack := IsDeligneMumfordStack.isStack
  exists_presentation := by
    obtain ⟨U, F, hF⟩ := IsDeligneMumfordStack.exists_presentation (𝒳 := 𝒳)
    exact ⟨U, F, hF.mono (inf_le_inf le_rfl etale_le_smooth)⟩

namespace BasedFunctor

variable {𝒯 : BasedCategory.{v₃, u₃} Scheme.{u}} {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}

/-- Background definition for Section 4.1 (the unlabeled definition of open
and closed substacks): let $\cT \to \cX$ be a morphism of stacks over $\Sch_{\ét}$. It
exhibits $\cT$ as an
*open substack* of $\cX$ if it is fully faithful (an inclusion of a full subcategory up to
equivalence) and representable by schemes by open immersions. The book states the
condition for an inclusion of a substack $\cT \subseteq \cX$; the fully-faithfulness
clause renders "substack inclusion" (see this folder's COMMENTARY.md). -/
class IsOpenSubstackInclusion (F : 𝒯 ⥤ᵇ 𝒳) : Prop where
  full : F.toFunctor.Full
  faithful : F.toFunctor.Faithful
  relativelyRepresentableWith :
    F.RelativelyRepresentableWith (@IsOpenImmersion : MorphismProperty Scheme.{u})

/-- Supporting instance for Section 4.1 (the unlabeled definition of open
and closed substacks): every prestack is an open substack of itself.

The identity is fully faithful, and it is representable by schemes by open immersions
because the fiber product `𝒳 ×_𝒳 (Sch/S)` is equivalent to `Sch/S`
(`CategoryTheory.BasedCategory.fiberProductIdInv`), so the induced morphism of schemes is
an isomorphism (`CategoryTheory.BasedFunctor.isIso_overHom_of_isEquivalence`) and in
particular an open immersion. -/
instance IsOpenSubstackInclusion.id (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) :
    IsOpenSubstackInclusion (BasedFunctor.id 𝒳) where
  full := inferInstanceAs (𝟭 𝒳.obj).Full
  faithful := inferInstanceAs (𝟭 𝒳.obj).Faithful
  relativelyRepresentableWith := by
    refine ⟨fun S g => ⟨S, fiberProductIdInv g, isEquivalence_fiberProductIdInv g⟩, ?_⟩
    intro S g S' E hE
    have h0 := hE
    have h1 := isEquivalence_fiberProductSnd_id g
    have h2 : (E.comp (fiberProductSnd (BasedFunctor.id 𝒳) g)).toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans E.toFunctor
        (fiberProductSnd (BasedFunctor.id 𝒳) g).toFunctor
    have h3 := CategoryTheory.BasedFunctor.isIso_overHom_of_isEquivalence _ h2
    infer_instance

/-- Background definition for Section 4.1 (the unlabeled definition of open
and closed substacks): let $\cT \to \cX$ be a morphism of stacks over $\Sch_{\ét}$. It
exhibits $\cT$ as a
*closed substack* of $\cX$ if it is fully faithful and representable by schemes by closed
immersions. The fully-faithfulness clause renders "substack inclusion" (see this folder's
COMMENTARY.md). -/
class IsClosedSubstackInclusion (F : 𝒯 ⥤ᵇ 𝒳) : Prop where
  full : F.toFunctor.Full
  faithful : F.toFunctor.Faithful
  relativelyRepresentableWith :
    F.RelativelyRepresentableWith (@IsClosedImmersion : MorphismProperty Scheme.{u})

end BasedFunctor

/-- Sheaves for a Grothendieck topology are stable under fiber products: the fiber
product of two morphisms of sheaves of types, formed in the category of presheaves, is
again a sheaf.

This is the general fact that the sheaf condition is closed under limits
(`CategoryTheory.Presheaf.IsSheaf` is `IsClosedUnderLimitsOfShape`), specialised to
cospans and transported to the `Presieve.IsSheaf` formulation. -/
theorem isSheaf_pullback {C : Type u} [Category.{v₂} C] (J : GrothendieckTopology C)
    {X Y Z : Cᵒᵖ ⥤ Type v₂} (f : X ⟶ Z) (g : Y ⟶ Z)
    (hX : Presieve.IsSheaf J X) (hY : Presieve.IsSheaf J Y) (hZ : Presieve.IsSheaf J Z) :
    Presieve.IsSheaf J (Limits.pullback f g) := by
  rw [← CategoryTheory.isSheaf_iff_isSheaf_of_type]
  refine ObjectProperty.prop_of_isLimit (P := Presheaf.IsSheaf J)
    (limit.isLimit (cospan f g)) ?_
  rintro (_ | _ | _) <;>
    simp only [cospan_one, cospan_left, cospan_right] <;>
    rw [CategoryTheory.isSheaf_iff_isSheaf_of_type]
  · exact hZ
  · exact hX
  · exact hY

/-- API lemma for Section 4.1 (the unlabeled fiber-products
exercise): fiber products exist for algebraic spaces — the fiber product of presheaves of
two morphisms of algebraic spaces is an algebraic space. -/
theorem IsAlgebraicSpace.pullback {X Y Z : Scheme.{u}ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X]
    [IsAlgebraicSpace Y] [IsAlgebraicSpace Z] (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsAlgebraicSpace (Limits.pullback f g) := by
  refine ⟨isSheaf_pullback _ f g IsAlgebraicSpace.isSheaf IsAlgebraicSpace.isSheaf
    IsAlgebraicSpace.isSheaf, ?_⟩
  -- Write `𝒫` for `(Surjective ⊓ Etale).presheaf`. It is stable under base change
  -- (`MorphismProperty.relative_isStableUnderBaseChange`) and under composition.
  have hbc : MorphismProperty.IsStableUnderBaseChange
      ((@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}).presheaf) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  -- Étale presentations `U → X`, `V → Y`, `W → Z`.
  obtain ⟨U, u, hu⟩ := IsAlgebraicSpace.exists_presentation (X := X)
  obtain ⟨V, v, hv⟩ := IsAlgebraicSpace.exists_presentation (X := Y)
  obtain ⟨W, w, hw⟩ := IsAlgebraicSpace.exists_presentation (X := Z)
  have hwrep := MorphismProperty.relative.rep hw
  -- `W → Z` is representable by schemes and `U`, `V` are schemes, so the fiber products
  -- `UW = U ×_Z W` and `VW = V ×_Z W` are schemes.
  set UW : Scheme.{u} := hwrep.pullback (u ≫ f) with hUWdef
  set VW : Scheme.{u} := hwrep.pullback (v ≫ g) with hVWdef
  set sU : UW ⟶ U := hwrep.snd (u ≫ f) with hsU
  set sV : VW ⟶ V := hwrep.snd (v ≫ g) with hsV
  set ωU : UW ⟶ W := hwrep.fst' (u ≫ f) with hωU
  set ωV : VW ⟶ W := hwrep.fst' (v ≫ g) with hωV
  have SqU : IsPullback (yoneda.map ωU) (yoneda.map sU) w (u ≫ f) := by
    rw [hωU, Functor.relativelyRepresentable.map_fst']
    exact hwrep.isPullback (u ≫ f)
  have SqV : IsPullback (yoneda.map ωV) (yoneda.map sV) w (v ≫ g) := by
    rw [hωV, Functor.relativelyRepresentable.map_fst']
    exact hwrep.isPullback (v ≫ g)
  -- The presentation scheme is `T = UW ×_W VW`, a fiber product of schemes; as a
  -- presheaf it is `U ×_Z V ×_Z W`.
  set T : Scheme.{u} := Limits.pullback ωU ωV with hT
  set t₁ : T ⟶ UW := Limits.pullback.fst ωU ωV with ht₁
  set t₂ : T ⟶ VW := Limits.pullback.snd ωU ωV with ht₂
  have SqT : IsPullback (yoneda.map t₁) (yoneda.map t₂) (yoneda.map ωU) (yoneda.map ωV) :=
    (IsPullback.of_hasPullback ωU ωV).map yoneda
  -- `Q = U ×_Z V`, which maps to `X ×_Z Y` by a composition of two base changes of the
  -- presentations `u` and `v`.
  set Q := Limits.pullback (u ≫ f) (v ≫ g) with hQ
  set prU : Q ⟶ yoneda.obj U := Limits.pullback.fst (u ≫ f) (v ≫ g) with hprU
  set prV : Q ⟶ yoneda.obj V := Limits.pullback.snd (u ≫ f) (v ≫ g) with hprV
  have SqQ : IsPullback prU prV (u ≫ f) (v ≫ g) := IsPullback.of_hasPullback _ _
  have hq := MorphismProperty.pullbackMap
    (P := (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}).presheaf) hu hv
    (rfl : u ≫ f = u ≫ f) (rfl : v ≫ g = v ≫ g)
  -- The comparison morphism `μ : T → Q`.
  have hcomm : (yoneda.map t₁ ≫ yoneda.map sU) ≫ (u ≫ f) =
      (yoneda.map t₂ ≫ yoneda.map sV) ≫ (v ≫ g) := by
    calc (yoneda.map t₁ ≫ yoneda.map sU) ≫ (u ≫ f)
        = yoneda.map t₁ ≫ (yoneda.map sU ≫ (u ≫ f)) := Category.assoc _ _ _
      _ = yoneda.map t₁ ≫ (yoneda.map ωU ≫ w) := by rw [SqU.w]
      _ = (yoneda.map t₁ ≫ yoneda.map ωU) ≫ w := (Category.assoc _ _ _).symm
      _ = (yoneda.map t₂ ≫ yoneda.map ωV) ≫ w := by rw [SqT.w]
      _ = yoneda.map t₂ ≫ (yoneda.map ωV ≫ w) := Category.assoc _ _ _
      _ = yoneda.map t₂ ≫ (yoneda.map sV ≫ (v ≫ g)) := by rw [SqV.w]
      _ = (yoneda.map t₂ ≫ yoneda.map sV) ≫ (v ≫ g) := (Category.assoc _ _ _).symm
  set μ : yoneda.obj T ⟶ Q :=
    Limits.pullback.lift (yoneda.map t₁ ≫ yoneda.map sU)
      (yoneda.map t₂ ≫ yoneda.map sV) hcomm with hμdef
  have hlift_fst : μ ≫ prU = yoneda.map t₁ ≫ yoneda.map sU := by
    rw [hμdef, hprU]; exact Limits.pullback.lift_fst _ _ _
  have hlift_snd : μ ≫ prV = yoneda.map t₂ ≫ yoneda.map sV := by
    rw [hμdef, hprV]; exact Limits.pullback.lift_snd _ _ _
  -- `T = UW ×_Z V` (paste the square defining `T` onto the square defining `VW`) …
  have SqA : IsPullback (yoneda.map t₁) (yoneda.map t₂ ≫ yoneda.map sV)
      (yoneda.map ωU ≫ w) (v ≫ g) := SqT.paste_vert SqV
  have SqA' : IsPullback (yoneda.map t₁) (μ ≫ prV) (yoneda.map sU ≫ (u ≫ f)) (v ≫ g) := by
    rw [hlift_snd, ← SqU.w]
    exact SqA
  -- … hence `T = Q ×_U UW`, by cancelling the square defining `Q` …
  have SqS : IsPullback (yoneda.map t₁) μ (yoneda.map sU) prU :=
    (IsPullback.paste_vert_iff SqQ hlift_fst.symm).mp SqA'
  -- … hence `T = Q ×_Z W`, so `μ` is a base change of `w`.
  have SqFinal : IsPullback (yoneda.map t₁ ≫ yoneda.map ωU) μ w (prU ≫ (u ≫ f)) :=
    SqS.paste_horiz SqU
  have hμ : (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}).presheaf μ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback SqFinal hw
  exact ⟨T, μ ≫ _, MorphismProperty.comp_mem _ _ _ hμ hq⟩

end AlgebraicGeometry

end DefAlgebraicStack

section DefAlgebraicStack

open CategoryTheory Functor Limits Opposite CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.BasedFunctor

/-- API lemma for Definition 4.1.3 (the identity): the identity of
a prestack is representable by schemes by surjective smooth morphisms — the fiber product
`𝒳 ×_𝒳 (Sch/S)` is equivalent to `Sch/S` (`fiberProductIdInv`), so the induced morphism
of schemes is an isomorphism (`isIso_overHom_of_isEquivalence`). Same proof as
`BasedFunctor.IsOpenSubstackInclusion.id`. -/
lemma relativelyRepresentableWith_id (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) :
    (CategoryTheory.BasedFunctor.id 𝒳).RelativelyRepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) := by
  refine ⟨fun S g => ⟨S, fiberProductIdInv g, isEquivalence_fiberProductIdInv g⟩, ?_⟩
  intro S g S' E hE
  have h0 := hE
  have h1 := isEquivalence_fiberProductSnd_id g
  have h2 : Functor.IsEquivalence
      (E.comp (fiberProductSnd (CategoryTheory.BasedFunctor.id 𝒳) g)).toFunctor :=
    Functor.isEquivalence_trans E.toFunctor
      (fiberProductSnd (CategoryTheory.BasedFunctor.id 𝒳) g).toFunctor
  have h3 := CategoryTheory.BasedFunctor.isIso_overHom_of_isEquivalence _ h2
  exact ⟨inferInstance, inferInstance⟩

/-- API lemma for Definition 4.1.3 (the identity): the identity of
a prestack is representable with surjective smooth morphisms.

Deduced from `relativelyRepresentableWith_id` through Remark 4.1.5
(`RelativelyRepresentableWith.representableWith`). -/
lemma representableWith_id (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) :
    RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) (CategoryTheory.BasedFunctor.id 𝒳) :=
  RelativelyRepresentableWith.representableWith (inf_le_inf le_rfl etale_le_smooth)
    (relativelyRepresentableWith_id 𝒳)

end AlgebraicGeometry.BasedFunctor

namespace AlgebraicGeometry

/-- Supporting instance for Definition 4.1.6 (the following prose: "every scheme,
algebraic space, or Deligne–Mumford stack is also an algebraic stack" — the scheme case):
the representable prestack `Sch/V` of a scheme is an algebraic stack. It is an étale
stack because `Mor(-, V)` is an étale sheaf (`isStack_overBased`), and the identity is a
smooth presentation (`BasedFunctor.representableWith_id`).

Registered as an `instance`, so that every `[IsAlgebraicStack 𝒳]` lemma applies at a
scheme chart `𝒳 = Sch/V`. That was the point of the "`IsAlgebraicStack (overBased X)`
spine" recorded in this folder's COMMENTARY.md, and it became available once
`RelativelyRepresentableWith.representableWith` (Remark 4.1.5) was proved. -/
instance isAlgebraicStack_overBased (V : Scheme.{u}) : IsAlgebraicStack (overBased V) where
  isStack := CategoryTheory.BasedCategory.isStack_overBased Scheme.etaleTopology V
    (IsAlgebraicSpace.isSheaf (X := yoneda.obj V))
  exists_presentation :=
    ⟨V, CategoryTheory.BasedFunctor.id _, BasedFunctor.representableWith_id _⟩

end AlgebraicGeometry

end DefAlgebraicStack
