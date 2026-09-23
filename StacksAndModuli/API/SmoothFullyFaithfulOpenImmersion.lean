module

public import StacksAndModuli.API.OpenSubstackIntersection
public import StacksAndModuli.API.RepresentableHasProperty
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# Smooth fully faithful schematic morphisms are open immersions

This file records the formal part of the standard argument that a smooth fully faithful
morphism of algebraic stacks is an open immersion.  Once the morphism is known to be
representable by schemes, full faithfulness makes every representing morphism a
monomorphism; smooth monomorphisms of schemes are open immersions.

It also isolates the remaining algebraic-space input needed to upgrade a representable
fully faithful morphism to a schematic one: monomorphisms from algebraic spaces to schemes
must be representable by schemes.

## Main results

* `BasedFunctor.relativelyRepresentableWith_monomorphisms_of_full_faithful`
* `BasedFunctor.relativelyRepresentableWith_isOpenImmersion_of_smooth_full_faithful`
* `BasedFunctor.relativelyRepresentable_of_representable_full_faithful`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}}
  {Ycat : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- A relatively representable fully faithful morphism is relatively representable by
monomorphisms. -/
theorem relativelyRepresentableWith_monomorphisms_of_full_faithful
    {F : Xcat ⥤ᵇ Ycat} [F.toFunctor.Full] [F.toFunctor.Faithful]
    (hF : F.RelativelyRepresentable) :
    F.RelativelyRepresentableWith (MorphismProperty.monomorphisms Scheme.{u}) := by
  refine ⟨hF, ?_⟩
  intro T g W E hE
  haveI : E.toFunctor.IsEquivalence := hE
  haveI hsndFull : (fiberProductSnd F g).toFunctor.Full :=
    fiberProductSnd_full (F := F) (G := g)
  haveI hcompFull :
      (E.comp (fiberProductSnd F g)).toFunctor.Full :=
    Functor.Full.comp _ _
  obtain ⟨α⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map
    (E.comp (fiberProductSnd F g))
  have β : (E.comp (fiberProductSnd F g)).toFunctor ≅
      (overBased.map (E.comp (fiberProductSnd F g)).overHom).toFunctor :=
    (BasedNatTrans.forgetful (overBased W) (overBased T)).mapIso α
  haveI :
      (overBased.map (E.comp (fiberProductSnd F g)).overHom).toFunctor.Full :=
    Functor.Full.of_iso β
  exact mono_of_overBased_map_full _

/-- A smooth, schematic, fully faithful morphism of algebraic stacks is an open
immersion. -/
theorem relativelyRepresentableWith_isOpenImmersion_of_smooth_full_faithful
    [IsAlgebraicStack Xcat] [IsAlgebraicStack Ycat]
    {F : Xcat ⥤ᵇ Ycat} [F.toFunctor.Full] [F.toFunctor.Faithful]
    (hFrel : F.RelativelyRepresentable) (hFsmooth : Smooth F) :
    F.RelativelyRepresentableWith
      (@_root_.AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u}) := by
  have hsmooth : F.RelativelyRepresentableWith
      (@_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) :=
    (hasProperty_iff_relativelyRepresentableWith isSmoothLocal_smooth hFrel).mp hFsmooth
  have hmono :=
    relativelyRepresentableWith_monomorphisms_of_full_faithful hFrel
  refine ⟨hFrel, ?_⟩
  intro T g W E hE
  haveI : @_root_.AlgebraicGeometry.Smooth _ _
      (E.comp (fiberProductSnd F g)).overHom := hsmooth.2 T g W E hE
  haveI : Mono (E.comp (fiberProductSnd F g)).overHom :=
    hmono.2 T g W E hE
  exact IsOpenImmersion.of_flat_of_mono _

/-- Conditional on the standard fact that a monomorphism from an algebraic space to a
scheme is representable by schemes, a representable fully faithful morphism is
representable by schemes. -/
theorem relativelyRepresentable_of_representable_full_faithful
    (hmono : ∀ {X : Scheme.{u}ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X]
      {T : Scheme.{u}} (f : X ⟶ yoneda.obj T), [Mono f] →
        yoneda.relativelyRepresentable f)
    {F : Xcat ⥤ᵇ Ycat} [F.toFunctor.Full] [F.toFunctor.Faithful]
    (hF : Representable F) : F.RelativelyRepresentable := by
  intro T g
  obtain ⟨X, hX, E, hE⟩ := hF T g
  letI : IsAlgebraicSpace X := hX
  letI : E.toFunctor.IsEquivalence := hE
  let L := fiberProductSymm F g
  letI : L.toFunctor.IsEquivalence := inferInstance
  let H := (E.comp L).comp (fiberProductFst g F)
  let η := representedFiberSecondBaseMap F g E
  have hH : H = E.comp (fiberProductSnd F g) := by
    rw [show H = E.comp (L.comp (fiberProductFst g F)) by
      exact BasedFunctor.comp_assoc E L (fiberProductFst g F)]
    change E.comp ((fiberProductSymm F g).comp (fiberProductFst g F)) = _
    rw [fiberProductSymm_comp_fst]
  haveI hsndFull : (fiberProductSnd F g).toFunctor.Full :=
    fiberProductSnd_full (F := F) (G := g)
  haveI hHfull : H.toFunctor.Full := by
    rw [hH]
    exact Functor.Full.comp _ _
  let Q := ofPresheafYonedaToOverBased T
  letI : Q.toFunctor.IsEquivalence := inferInstance
  let eH : (ofPresheaf.map η).comp Q ≅ H := by
    exact ofPresheaf.comparisonOverMapIso Q H
  let eH' : ((ofPresheaf.map η).comp Q).toFunctor ≅ H.toFunctor :=
    (BasedNatTrans.forgetful _ _).mapIso eH
  haveI hcompFull : ((ofPresheaf.map η).comp Q).toFunctor.Full :=
    Functor.Full.of_iso eH'.symm
  haveI hcompFull' :
      ((ofPresheaf.map η).toFunctor ⋙ Q.toFunctor).Full := hcompFull
  haveI hηfull : (ofPresheaf.map η).toFunctor.Full :=
    Functor.Full.of_comp_faithful _ Q.toFunctor
  haveI hηmono : Mono η := by
    rw [NatTrans.mono_iff_mono_app]
    intro Z
    rw [mono_iff_injective]
    induction Z with
    | op S => exact injective_app_of_full η S
  let hη := hmono η
  let S := hη.pullback (𝟙 (yoneda.obj T))
  let hpb : IsPullback (hη.fst (𝟙 (yoneda.obj T)))
      (yoneda.map (hη.snd (𝟙 (yoneda.obj T)))) η (𝟙 (yoneda.obj T)) :=
    hη.isPullback (𝟙 (yoneda.obj T))
  let eX : yoneda.obj S ≅ X :=
    hpb.isoIsPullback X (yoneda.obj T) (IsPullback.id_horiz η)
  letI : (ofPresheaf.map eX.hom).toFunctor.IsEquivalence :=
    ofPresheaf.isEquivalence_map eX.hom
  letI : ((ofPresheaf.map eX.hom).comp E).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans (ofPresheaf.map eX.hom).toFunctor E.toFunctor
  let K := (overBasedToOfPresheafYoneda S).comp
    ((ofPresheaf.map eX.hom).comp E)
  refine ⟨S, K, ?_⟩
  exact Functor.isEquivalence_trans
    (overBasedToOfPresheafYoneda S).toFunctor
    ((ofPresheaf.map eX.hom).comp E).toFunctor

end AlgebraicGeometry.BasedFunctor
