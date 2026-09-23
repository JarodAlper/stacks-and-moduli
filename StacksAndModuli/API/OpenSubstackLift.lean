module

public import StacksAndModuli.API.OpenSubstackIntersection
public import StacksAndModuli.API.BasedFunctorWhiskering

/-!
# Lifting a morphism from a scheme through an open substack

If `i : 𝒰 ⥤ᵇ 𝒳` is an open substack inclusion and `g : Sch/S ⥤ᵇ 𝒳` has its value at `𝟙 S`
in the fiber-essential image of `i`, then `g` factors through `i` up to 2-isomorphism.

This is the step that lets the point-set description of `def:topology-of-stacks` be proved
*without* the 2-Yoneda lemma, and hence without a `IsFiberedInGroupoids` hypothesis on `𝒳`
or on the open substacks: 2-Yoneda would turn the *object* `u` of `𝒰` provided by the
fiber-essential image into a *morphism* `Sch/Spec K ⥤ᵇ 𝒰`, but it needs `𝒰` fibered in
groupoids. The representability datum carried by `IsOpenSubstackInclusion` produces the
morphism directly instead: the fiber product `𝒰 ×_𝒳 (Sch/S)` is represented by some `T'`
whose classified morphism `T' ⟶ S` is an open immersion, the hypothesis makes `𝟙 S` factor
through it, so it is a split epimorphism and — being a monomorphism — an isomorphism, and
composing the first projection with its inverse gives the lift.

## Main results

* `AlgebraicGeometry.exists_lift_of_fiberEssImage`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry

open CategoryTheory Limits CategoryTheory.BasedCategory CategoryTheory.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒰 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- **Lifting a morphism from a scheme through an open substack.** If `i : 𝒰 ⥤ᵇ 𝒳` is an
open substack inclusion and `g : Sch/S ⥤ᵇ 𝒳` has its value at `𝟙 S` in the fiber-essential
image of `i`, then `g` factors through `i` up to 2-isomorphism.

The representability datum of `i` supplies the factorization: the fiber product
`𝒰 ×_𝒳 (Sch/S)` is represented by some `T'` whose classified morphism `T' ⟶ S` is an open
immersion, and the hypothesis makes `𝟙 S` factor through it, so that morphism is a split
epimorphism and hence — being a monomorphism — an isomorphism. Composing the first
projection with the inverse gives the lift. -/
lemma exists_lift_of_fiberEssImage (i : 𝒰 ⥤ᵇ 𝒳)
    [hi : BasedFunctor.IsOpenSubstackInclusion i] (S : Scheme.{u})
    (g : overBased S ⥤ᵇ 𝒳) (h : i.fiberEssImage (g.obj (Over.mk (𝟙 S)))) :
    ∃ H : overBased S ⥤ᵇ 𝒰, Nonempty (H.comp i ≅ g) := by
  obtain ⟨T', E, hE⟩ := hi.relativelyRepresentableWith.1 S g
  haveI hoi : IsOpenImmersion ((E.comp (fiberProductSnd i g)).overHom) :=
    hi.relativelyRepresentableWith.2 S g T' E hE
  obtain ⟨k, hk⟩ := (fiberEssImage_obj_iff_factors i g E hE (Over.mk (𝟙 S))).mp h
  haveI hse : IsSplitEpi ((E.comp (fiberProductSnd i g)).overHom) := ⟨⟨k, hk⟩⟩
  haveI hiso : IsIso ((E.comp (fiberProductSnd i g)).overHom) :=
    isIso_of_mono_of_isSplitEpi _
  obtain ⟨α⟩ := BasedFunctor.nonempty_iso_overBased_map (E.comp (fiberProductSnd i g))
  refine ⟨(overBased.map (inv (E.comp (fiberProductSnd i g)).overHom)).comp
    (E.comp (fiberProductFst i g)), ⟨?_⟩⟩
  have β : (E.comp (fiberProductFst i g)).comp i
      ≅ (E.comp (fiberProductSnd i g)).comp g := by
    rw [BasedFunctor.comp_assoc, BasedFunctor.comp_assoc]
    exact BasedCategory.isoWhiskerLeft E (fiberProductIsoComm i g)
  have γ : (E.comp (fiberProductSnd i g)).comp g
      ≅ (overBased.map (E.comp (fiberProductSnd i g)).overHom).comp g :=
    BasedCategory.isoWhiskerRight α g
  have δ : (overBased.map (inv (E.comp (fiberProductSnd i g)).overHom)).comp
      ((overBased.map (E.comp (fiberProductSnd i g)).overHom).comp g) ≅ g := by
    rw [← BasedFunctor.comp_assoc, ← overBased.map_comp, IsIso.inv_hom_id,
      show overBased.map (𝟙 S) = CategoryTheory.BasedFunctor.id _ from
        CategoryTheory.BasedFunctor.ext_of_toFunctor_eq (Over.mapId_eq _),
      BasedFunctor.id_comp]
  rw [BasedFunctor.comp_assoc]
  exact (BasedCategory.isoWhiskerLeft _ (β.trans γ)).trans δ

end AlgebraicGeometry
