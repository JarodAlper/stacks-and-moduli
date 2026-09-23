module

public import StacksAndModuli.API.EtaleLocalFiberRepresentationSmall
public import StacksAndModuli.API.EtaleLocalGoodChart
public import StacksAndModuli.API.QuotientCoproductPoint
public import StacksAndModuli.API.StackCoproductMorphismGlue

/-!
# Geometric presentations of quotient stacks

This file assembles the representability ingredients for the canonical map from
the object presheaf of a groupoid to a stackification of its quotient prestack.
Once quotient-local lifts can be combined over a coproduct, every scheme-valued
fiber has a small étale sheaf representation and an étale-local scheme chart.
The resulting chart criterion proves that the quotient presentation has any
morphism property inherited from the groupoid source and local on the source for
surjective étale maps.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits Opposite
open CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.PresheafGroupoid

variable {G : PresheafGroupoid.{u}}
  {Xst : BasedCategory.{v₂, u₂} Scheme.{u}}
  {i : BasedFunctor G.quotientPrestack Xst}

/-- A representable groupoid source map is relatively surjective.  The section
of every represented base change is induced by the identity relation. -/
theorem presheaf_surjective_s
    (hs : yoneda.relativelyRepresentable G.s) :
    MorphismProperty.presheaf (@Surjective : MorphismProperty Scheme.{u}) G.s := by
  apply MorphismProperty.relative_of_snd hs
  intro T g
  let sec : T ⟶ hs.pullback g :=
    hs.lift (g ≫ G.e) (𝟙 T) (by simp [Category.assoc, G.e_s])
  have hsec : sec ≫ hs.snd g = 𝟙 T := hs.lift_snd _ _ _
  have hcomp : Surjective (sec ≫ hs.snd g) := by
    rw [hsec]
    infer_instance
  exact @Surjective.of_comp _ _ _ sec (hs.snd g) hcomp

/-- A morphism property of the groupoid source can be combined with relative
surjectivity, supplied by the identity relation. -/
theorem presheaf_surjective_inf_s
    {P : MorphismProperty Scheme.{u}}
    (hs : MorphismProperty.presheaf P G.s) :
    MorphismProperty.presheaf
      (@Surjective ⊓ P : MorphismProperty Scheme.{u}) G.s := by
  let hsurj := presheaf_surjective_s (G := G) hs.rep
  exact ⟨hs.rep, fun {a b} g fst snd hpb ↦
    ⟨hsurj.property g fst snd hpb, hs.property g fst snd hpb⟩⟩

/-- A stack target and a sheaf object presheaf supply the coproduct gluing
needed to turn quotient-local density into one surjective étale lift. -/
theorem coproductLiftsGlue_of_isStack
    (hstack : BasedCategory.IsStack Scheme.etaleTopology Xst)
    (hU : Presieve.IsSheaf Scheme.zariskiTopology G.U) :
    CoproductLiftsGlue (i := i) := by
  intro y cover hlocal
  let x : ∀ j, G.quotientPrestack.obj := fun j ↦ (hlocal j).choose
  let q : ∀ j, i.obj (x j) ⟶ y := fun j ↦
    (hlocal j).choose_spec.choose
  have hq : ∀ j, IsHomLift Xst.p (cover.f j) (q j) := fun j ↦
    (hlocal j).choose_spec.choose_spec
  have hx : ∀ j, (x j).base = cover.X j := fun j ↦
    (i.w_obj (x j)).symm.trans
      (IsHomLift.domain_eq Xst.p (cover.f j) (q j))
  obtain ⟨a, ha, r⟩ := exists_quotientCoproductCocone hU cover.X x hx
  let eta : ∀ j, i.obj (x j) ⟶ i.obj a := fun j ↦
    i.map (r j).choose
  have heta : ∀ j, IsHomLift Xst.p (Sigma.ι cover.X j) (eta j) := by
    intro j
    let _ : IsHomLift G.quotientProj (Sigma.ι cover.X j) (r j).choose :=
      (r j).choose_spec
    exact i.preserves_isHomLift (Sigma.ι cover.X j) (r j).choose
  let _ : BasedCategory.IsStack Scheme.etaleTopology Xst := hstack
  let _ : ∀ j, IsHomLift Xst.p (Sigma.ι cover.X j) (eta j) := heta
  let _ : ∀ j, IsHomLift Xst.p (cover.f j) (q j) := hq
  obtain ⟨Q, hQ⟩ := BasedCategory.exists_homLift_sigmaDesc
    cover.X cover.f (i.w_obj a |>.trans ha) rfl eta q
  exact ⟨a, Q, hQ⟩

/-- An étale-local fiber representation together with the scheme chart from
the represented relation that produced its local algebraic-space structure. -/
structure EtaleLocalFiberChart
    (P : MorphismProperty Scheme.{u})
    (i : BasedFunctor G.quotientPrestack Xst)
    (T : Scheme.{u}) (g : BasedFunctor (overBased T) Xst) where
  /-- The small global sheaf representation and chosen local base change. -/
  fiber : BasedFunctor.EtaleLocalFiberRepresentation
    (G.quotientPresentation.comp i) T g
  /-- The scheme representing the local fiber. -/
  W : Scheme.{u}
  /-- The chosen local scheme representation. -/
  chart : BasedFunctor (overBased W)
    (fiberProduct (G.quotientPresentation.comp i)
      ((overBased.map fiber.localMap).comp g))
  /-- The local chart represents that fiber. -/
  chart_isEquivalence : chart.toFunctor.IsEquivalence
  /-- Its structural map has the groupoid projection's property. -/
  chart_property : P (chart.comp (fiberProductSnd
    (G.quotientPresentation.comp i)
      ((overBased.map fiber.localMap).comp g))).overHom

/-- Compatible small-sheaf and local-chart data exist for a quotient presentation
when quotient-local lifts can be combined over coproducts. -/
theorem nonempty_etaleLocalFiberChart_of_coproductLiftsGlue
    {P : MorphismProperty Scheme.{u}}
    (hi : BasedFunctor.IsLocalStackification
      (J := Scheme.etaleTopology) i)
    (hglue : CoproductLiftsGlue (i := i))
    (hU : Presieve.IsSheaf Scheme.etaleTopology G.U)
    (hs : MorphismProperty.presheaf P G.s)
    (T : Scheme.{u}) (g : BasedFunctor (overBased T) Xst) :
    Nonempty (EtaleLocalFiberChart P i T g) := by
  let _ : Xst.p.IsFiberedInGroupoids := hi.isStack.isFiberedInGroupoids
  let _ : BasedCategory.IsStack Scheme.etaleTopology Xst := hi.isStack
  let _ : i.toFunctor.Full := hi.full
  let _ : i.toFunctor.Faithful := hi.faithful
  let A := G.quotientPresentation.comp i
  have hFiberStack : BasedCategory.IsStack Scheme.etaleTopology
      (fiberProduct A g) :=
    BasedFunctor.isStack_fiberProduct_ofPresheaf_overBased A g hU
  let _ : BasedCategory.IsStack Scheme.etaleTopology (fiberProduct A g) :=
    hFiberStack
  let y := ((twoYonedaEval (𝒳 := Xst) T).obj g).1
  obtain ⟨S, p, hpEtale, hpSurjective, x, q, hq⟩ :=
    exists_etale_surjective_lift_of_coproductLiftsGlue
      hi.locallyEssentiallySurjective hglue y
  let p' : S ⟶ T :=
    p ≫ eqToHom ((twoYonedaEval (𝒳 := Xst) T).obj g).2
  have hp'Etale : Etale p' := by
    let _ : Etale p := hpEtale
    dsimp only [p']
    infer_instance
  have hp'Surjective : Surjective p' := by
    let _ : Surjective p := hpSurjective
    dsimp only [p']
    infer_instance
  let _ : IsHomLift Xst.p p q := hq
  let _ : IsHomLift Xst.p p' q := by
    apply IsHomLift.of_fac Xst.p p' q
      (IsHomLift.domain_eq Xst.p p q)
      ((twoYonedaEval (𝒳 := Xst) T).obj g).2
    rw [IsHomLift.fac' Xst.p p q]
    simp [p']
  let f := quotientLiftBaseMap g x q
  obtain ⟨hfEtale, hfSurjective⟩ :=
    quotientLiftBaseMap_surjective_etale p' g x q hp'Etale hp'Surjective
  obtain ⟨W, K, hK, hPK⟩ :=
    exists_scheme_representation_localFiber i hs g x q
  let hR := isRepresentedByPresheaf_fiberProduct_of_isLocalStackification hi
  let D := BasedFunctor.EtaleLocalFiberRepresentation.of_smallSelfIntersection
    g hR f hfEtale hfSurjective K hK
  exact ⟨
    { fiber := D
      W := W
      chart := K
      chart_isEquivalence := hK
      chart_property := hPK }⟩

/-- A chosen compatible local fiber representation and scheme chart for a
quotient presentation. -/
noncomputable def etaleLocalFiberChart_of_coproductLiftsGlue
    {P : MorphismProperty Scheme.{u}}
    (hi : BasedFunctor.IsLocalStackification
      (J := Scheme.etaleTopology) i)
    (hglue : CoproductLiftsGlue (i := i))
    (hU : Presieve.IsSheaf Scheme.etaleTopology G.U)
    (hs : MorphismProperty.presheaf P G.s)
    (T : Scheme.{u}) (g : BasedFunctor (overBased T) Xst) :
    EtaleLocalFiberChart P i T g :=
  Classical.choice
    (nonempty_etaleLocalFiberChart_of_coproductLiftsGlue
      hi hglue hU hs T g)

/-- A local stackification of a quotient prestack has a geometric quotient
presentation when local lifts glue over coproducts and the groupoid source has
a property local on the source for surjective étale maps. -/
theorem representableWith_quotientPresentation_of_coproductLiftsGlue
    {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderComposition]
    (hle : (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) ≤ P)
    (hlocal : ∀ ⦃S' S T : Scheme.{u}⦄ (p : S' ⟶ S) (f : S ⟶ T),
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p →
        (P f ↔ P (p ≫ f)))
    (hi : BasedFunctor.IsLocalStackification
      (J := Scheme.etaleTopology) i)
    (hglue : CoproductLiftsGlue (i := i))
    (hU : Presieve.IsSheaf Scheme.etaleTopology G.U)
    (hs : MorphismProperty.presheaf P G.s) :
    BasedFunctor.RepresentableWith P
      (G.quotientPresentation.comp i) := by
  let _ : Xst.p.IsFiberedInGroupoids := hi.isStack.isFiberedInGroupoids
  let A := G.quotientPresentation.comp i
  let D := fun (T : Scheme.{u}) (g : BasedFunctor (overBased T) Xst) ↦
    etaleLocalFiberChart_of_coproductLiftsGlue hi hglue hU hs T g
  apply BasedFunctor.RepresentableWith.of_etaleLocalFiberRepresentations_and_goodLocalCharts A
      (fun T g ↦ (D T g).fiber) hle hlocal
  intro T g
  let d := D T g
  let _ : d.chart.toFunctor.IsEquivalence := d.chart_isEquivalence
  exact ⟨d.W, d.chart,
    BasedFunctor.RepresentableWith.surjectiveEtale_of_isEquivalence d.chart,
    d.chart_property⟩

/-- A local stackification of a quotient prestack has a geometric quotient
presentation when the groupoid source has a property local on the source for
surjective étale maps. -/
theorem representableWith_quotientPresentation_of_isLocalStackification
    {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderComposition]
    (hle : (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) ≤ P)
    (hlocal : ∀ ⦃S' S T : Scheme.{u}⦄ (p : S' ⟶ S) (f : S ⟶ T),
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p →
        (P f ↔ P (p ≫ f)))
    (hi : BasedFunctor.IsLocalStackification
      (J := Scheme.etaleTopology) i)
    (hU : Presieve.IsSheaf Scheme.etaleTopology G.U)
    (hs : MorphismProperty.presheaf P G.s) :
    BasedFunctor.RepresentableWith P
      (G.quotientPresentation.comp i) := by
  let hUz : Presieve.IsSheaf Scheme.zariskiTopology G.U :=
    Presieve.isSheaf_of_le G.U
      Scheme.zariskiTopology_le_etaleTopology hU
  exact representableWith_quotientPresentation_of_coproductLiftsGlue
    hle hlocal hi (coproductLiftsGlue_of_isStack hi.isStack hUz) hU hs

end AlgebraicGeometry.PresheafGroupoid
