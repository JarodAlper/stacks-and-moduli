module

public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»
public import StacksAndModuli.API.PrestackProducts

/-!
# Common refinements of two presentations

Two presentations of the same prestack, both representable with a property `Q`, are
dominated by a common presentation — and, crucially, the two legs are *compatible*: the
two composites `Sch/W ⥤ᵇ 𝒵` are 2-isomorphic. Combined with
`CategoryTheory.BasedFunctor.overHom_eq_of_iso`, that 2-isomorphism turns the two legs
into a commuting square of morphisms of schemes, which is what every
"independence of the chosen presentation" argument runs on (Definition 4.3.2 and
Definition 4.3.7 of *Stacks and Moduli*).

Main results:
- `AlgebraicGeometry.exists_common_cover_iso`: the common refinement, with the
  2-isomorphism;
- `AlgebraicGeometry.exists_common_cover_of_representableWith`: the weaker form without
  it, which is what `AlgebraicGeometry.BasedCategory.hasSchemeProperty_of_exists` uses.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section CommonCover

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry

/-- Two presentations of a prestack are dominated by a common presentation, with
*compatible* legs: if `p₁ : Sch/U₁ ⥤ᵇ 𝒵` and `p₂ : Sch/U₂ ⥤ᵇ 𝒵` are both representable
with a property `Q`, there are a scheme `W` and morphisms `a₁ : W ⟶ U₁`, `a₂ : W ⟶ U₂`
with `Q a₁` and `Q a₂` such that the two composites `Sch/W ⥤ᵇ 𝒵` are 2-isomorphic.

The 2-isomorphism is the point: it is what turns the two legs into a commuting square of
morphisms of schemes after composing with any morphism `𝒵 ⥤ᵇ Sch/V` (via
`CategoryTheory.BasedFunctor.overHom_eq_of_iso`), which is how the independence of a
property from the chosen presentation is proved.

The construction: `p₂` is representable, so `Sch/U₂ ×_𝒵 Sch/U₁` is an algebraic space `X`;
take an étale presentation `W` of `X` and let `Φ : Sch/W ⥤ᵇ Sch/U₂ ×_𝒵 Sch/U₁` be the
resulting morphism. The two legs are `Φ` composed with the two projections, and the
2-isomorphism is the fiber product's own 2-commutativity isomorphism
`fiberProductIsoComm`, whiskered by `Φ` and corrected on each side by
`CategoryTheory.BasedFunctor.nonempty_iso_overBased_map`. That `Q` holds for the second
leg uses `CategoryTheory.BasedCategory.fiberProductSymm` to feed the *same* presentation
`W` of the *same* algebraic space into the representability hypothesis for `p₁`. -/
theorem exists_common_cover_iso {Q : MorphismProperty Scheme.{u}}
    {𝒵 : BasedCategory.{v₂, u₂} Scheme.{u}} {U₁ U₂ : Scheme.{u}}
    {p₁ : overBased U₁ ⥤ᵇ 𝒵} {p₂ : overBased U₂ ⥤ᵇ 𝒵}
    (hp₁ : BasedFunctor.RepresentableWith Q p₁)
    (hp₂ : BasedFunctor.RepresentableWith Q p₂) :
    ∃ (W : Scheme.{u}) (a₁ : W ⟶ U₁) (a₂ : W ⟶ U₂), Q a₁ ∧ Q a₂ ∧
      Nonempty ((overBased.map a₁).comp p₁ ≅ (overBased.map a₂).comp p₂) := by
  obtain ⟨X, hX, E, hE⟩ := hp₂.1 U₁ p₁
  have := hX
  have := hE
  obtain ⟨W, q, hq⟩ := IsAlgebraicSpace.exists_presentation (X := X)
  set Φ : overBased W ⥤ᵇ BasedCategory.fiberProduct p₂ p₁ :=
    (overBasedToOfPresheafYoneda W).comp ((ofPresheaf.map q).comp E) with hΦ
  have ha := hp₂.2 U₁ p₁ X hX E hE W q hq
  have hb := hp₁.2 U₂ p₂ X hX (E.comp (fiberProductSymm p₂ p₁))
    (inferInstanceAs (E.toFunctor ⋙ (fiberProductSymm p₂ p₁).toFunctor).IsEquivalence) W q hq
  rw [CategoryTheory.BasedFunctor.comp_assoc, fiberProductSymm_comp_snd] at hb
  refine ⟨W, (Φ.comp (fiberProductSnd p₂ p₁)).overHom,
    (Φ.comp (fiberProductFst p₂ p₁)).overHom, ha, hb, ?_⟩
  obtain ⟨e₁⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map
    (Φ.comp (fiberProductSnd p₂ p₁))
  obtain ⟨e₂⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map
    (Φ.comp (fiberProductFst p₂ p₁))
  exact ⟨(CategoryTheory.BasedCategory.isoWhiskerRight e₁.symm p₁).trans
    (((CategoryTheory.BasedCategory.isoWhiskerLeft Φ (fiberProductIsoComm p₂ p₁)).symm).trans
      (CategoryTheory.BasedCategory.isoWhiskerRight e₂ p₂))⟩

/-- Two presentations of a prestack are dominated by a common presentation. This is the
form used by `AlgebraicGeometry.BasedCategory.hasSchemeProperty_of_exists`; the refinement
carrying the 2-isomorphism is `exists_common_cover_iso`. -/
theorem exists_common_cover_of_representableWith {Q : MorphismProperty Scheme.{u}}
    {𝒵 : BasedCategory.{v₂, u₂} Scheme.{u}} {U₁ U₂ : Scheme.{u}}
    {p₁ : overBased U₁ ⥤ᵇ 𝒵} {p₂ : overBased U₂ ⥤ᵇ 𝒵}
    (hp₁ : BasedFunctor.RepresentableWith Q p₁)
    (hp₂ : BasedFunctor.RepresentableWith Q p₂) :
    ∃ (W : Scheme.{u}) (a₁ : W ⟶ U₁) (a₂ : W ⟶ U₂), Q a₁ ∧ Q a₂ := by
  obtain ⟨W, a₁, a₂, h₁, h₂, -⟩ := exists_common_cover_iso hp₁ hp₂
  exact ⟨W, a₁, a₂, h₁, h₂⟩

end AlgebraicGeometry

end CommonCover
