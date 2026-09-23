module

public import StacksAndModuli.API.SmoothEtaleRefinement
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»

/-!
# Étale-local lifts to a smooth stack presentation

This file turns the defining smooth presentation of an algebraic stack into its basic
local lifting property: a map from a scheme lifts to the presentation after a single
surjective étale base change.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor
open CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.BasedFunctor

/-- A morphism represented by algebraic spaces with surjective smooth fibres admits
étale-local lifts from every scheme-valued point.

More precisely, if `P : Sch/U → 𝒳` has surjective smooth algebraic-space fibres and
`g : Sch/S → 𝒳`, then some surjective étale `p : S' → S` admits a lift
`Sch/S' → Sch/U`, compatible with `g` up to a based natural isomorphism. -/
theorem RepresentableWith.exists_etale_surjective_lift
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {U S : Scheme.{u}}
    {P : overBased U ⥤ᵇ 𝒳}
    (hP : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) P)
    (g : overBased S ⥤ᵇ 𝒳) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S), Etale p ∧ Surjective p ∧
      ∃ lift : overBased S' ⥤ᵇ overBased U,
        Nonempty (lift.comp P ≅ (overBased.map p).comp g) := by
  classical
  obtain ⟨X, hX, E, hE⟩ := hP.1 S g
  let _ : IsAlgebraicSpace X := hX
  obtain ⟨V, q, hq⟩ := IsAlgebraicSpace.exists_presentation (X := X)
  let H : overBased V ⥤ᵇ BasedCategory.fiberProduct P g :=
    (overBasedToOfPresheafYoneda V).comp ((ofPresheaf.map q).comp E)
  let f : V ⟶ S :=
    (H.comp (CategoryTheory.BasedCategory.fiberProductSnd P g)).overHom
  have hf : (@_root_.AlgebraicGeometry.Surjective ⊓
      @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) f :=
    hP.2 S g X hX E hE V q hq
  let _ : Surjective f := hf.1
  let _ : Smooth f := hf.2
  obtain ⟨S', p, hpEtale, hpSurjective, s, hs⟩ :=
    Scheme.Hom.exists_etale_surjective_refinement_of_smooth f
  let K : overBased S' ⥤ᵇ BasedCategory.fiberProduct P g :=
    (overBased.map s).comp H
  let lift : overBased S' ⥤ᵇ overBased U :=
    K.comp (CategoryTheory.BasedCategory.fiberProductFst P g)
  let base : overBased S' ⥤ᵇ overBased S :=
    K.comp (CategoryTheory.BasedCategory.fiberProductSnd P g)
  have hbase : base.overHom = p := by
    rw [show base = (overBased.map s).comp
      (H.comp (CategoryTheory.BasedCategory.fiberProductSnd P g)) from rfl]
    rw [CategoryTheory.BasedFunctor.overHom_comp,
      CategoryTheory.BasedFunctor.overHom_map]
    exact hs
  obtain ⟨ebase⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map base
  have ebase' : base ≅ overBased.map p := by
    rw [← hbase]
    exact ebase
  let ecomm : lift.comp P ≅ base.comp g :=
    isoWhiskerLeft K (fiberProductIsoComm P g)
  exact ⟨S', p, hpEtale, hpSurjective, lift,
    ⟨ecomm ≪≫ isoWhiskerRight ebase' g⟩⟩

/-- Two scheme-valued points of the target lift simultaneously to a smooth presentation
after one surjective étale base change. -/
theorem RepresentableWith.exists_etale_surjective_pair_lift
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {U S : Scheme.{u}}
    {P : overBased U ⥤ᵇ 𝒳}
    (hP : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) P)
    (a b : overBased S ⥤ᵇ 𝒳) :
    ∃ (S' : Scheme.{u}) (p : S' ⟶ S), Etale p ∧ Surjective p ∧
      ∃ (liftA liftB : overBased S' ⥤ᵇ overBased U),
        Nonempty (liftA.comp P ≅ (overBased.map p).comp a) ∧
          Nonempty (liftB.comp P ≅ (overBased.map p).comp b) := by
  obtain ⟨S₁, p₁, hp₁Etale, hp₁Surjective, liftA₁, ⟨eA₁⟩⟩ :=
    hP.exists_etale_surjective_lift a
  let _ : Etale p₁ := hp₁Etale
  let _ : Surjective p₁ := hp₁Surjective
  obtain ⟨S₂, p₂, hp₂Etale, hp₂Surjective, liftB, ⟨eB⟩⟩ :=
    hP.exists_etale_surjective_lift ((overBased.map p₁).comp b)
  let _ : Etale p₂ := hp₂Etale
  let _ : Surjective p₂ := hp₂Surjective
  let p : S₂ ⟶ S := p₂ ≫ p₁
  let liftA : overBased S₂ ⥤ᵇ overBased U := (overBased.map p₂).comp liftA₁
  have eA : liftA.comp P ≅ (overBased.map p).comp a := by
    simpa only [liftA, p, CategoryTheory.BasedFunctor.comp_assoc,
      overBased.map_comp] using isoWhiskerLeft (overBased.map p₂) eA₁
  have eB' : liftB.comp P ≅ (overBased.map p).comp b := by
    simpa only [p, CategoryTheory.BasedFunctor.comp_assoc,
      overBased.map_comp] using eB
  exact ⟨S₂, p, inferInstance, inferInstance, liftA, liftB, ⟨eA⟩, ⟨eB'⟩⟩

end AlgebraicGeometry.BasedFunctor
