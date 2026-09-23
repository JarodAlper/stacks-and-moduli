module

public import StacksAndModuli.«Section4.4-Equivalence-Relations».«part4.4.1-groupoids-and-equivalence-relations»

/-!
# Groupoids of schemes from relation data

For a scheme-theoretic relation whose arrows are uniquely determined by their source
and target, the endpoint identities for composition, identity, and inverse imply all
five higher groupoid laws. This file packages that uniqueness argument and the resulting
étale-groupoid and equivalence-relation interfaces.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.PresheafGroupoid

/-- Construct a presheaf groupoid from scheme-theoretic source, target, composition,
identity, and inverse maps when arrows are uniquely determined by their source and
target. Uniqueness supplies associativity, the two unit laws, and the two inverse laws. -/
noncomputable def ofSchemesOfRelation {U₀ R₀ : Scheme.{u}}
    (s t : R₀ ⟶ U₀) (c : pullback s t ⟶ R₀) (e : U₀ ⟶ R₀) (i : R₀ ⟶ R₀)
    (hcs : c ≫ s = pullback.snd s t ≫ s)
    (hct : c ≫ t = pullback.fst s t ≫ t)
    (hes : e ≫ s = 𝟙 U₀) (het : e ≫ t = 𝟙 U₀)
    (his : i ≫ s = t) (hit : i ≫ t = s)
    (hunique : ∀ {T : Scheme.{u}} (x y : T ⟶ R₀),
      x ≫ s = y ≫ s → x ≫ t = y ≫ t → x = y) : PresheafGroupoid.{u} :=
  ofSchemes s t c e i hcs hct hes het his hit
    (by
      intro T x y z hxy hyz h₁ h₂
      apply hunique
      · simp only [Category.assoc, hcs, pullback.lift_snd_assoc]
      · simp only [Category.assoc, hct, pullback.lift_fst_assoc])
    (by
      intro T x h
      apply hunique
      · simp only [Category.assoc, hcs, pullback.lift_snd_assoc, hes,
          Category.comp_id]
      · simp only [Category.assoc, hct, pullback.lift_fst_assoc])
    (by
      intro T x h
      apply hunique
      · simp only [Category.assoc, hcs, pullback.lift_snd_assoc]
      · simp only [Category.assoc, hct, pullback.lift_fst_assoc, het,
          Category.comp_id])
    (by
      intro T x h
      apply hunique
      · simp only [Category.assoc, hcs, pullback.lift_snd_assoc, hes,
          Category.comp_id]
      · simp only [Category.assoc, hct, pullback.lift_fst_assoc, hit, het,
          Category.comp_id])
    (by
      intro T x h
      apply hunique
      · simp only [Category.assoc, hcs, pullback.lift_snd_assoc, his, hes,
          Category.comp_id]
      · simp only [Category.assoc, hct, pullback.lift_fst_assoc, het,
          Category.comp_id])

/-- A groupoid constructed from a relation with unique arrows is an equivalence
relation. -/
lemma ofSchemesOfRelation_isEquivalenceRelation {U₀ R₀ : Scheme.{u}}
    (s t : R₀ ⟶ U₀) (c : pullback s t ⟶ R₀) (e : U₀ ⟶ R₀) (i : R₀ ⟶ R₀)
    (hcs : c ≫ s = pullback.snd s t ≫ s)
    (hct : c ≫ t = pullback.fst s t ≫ t)
    (hes : e ≫ s = 𝟙 U₀) (het : e ≫ t = 𝟙 U₀)
    (his : i ≫ s = t) (hit : i ≫ t = s)
    (hunique : ∀ {T : Scheme.{u}} (x y : T ⟶ R₀),
      x ≫ s = y ≫ s → x ≫ t = y ≫ t → x = y) :
    (ofSchemesOfRelation s t c e i hcs hct hes het his hit
      hunique).IsEquivalenceRelation := by
  intro T x y hs ht
  exact hunique x y hs ht

/-- If the source and target maps are étale, the groupoid constructed from relation
data is an étale groupoid. -/
lemma ofSchemesOfRelation_isEtale {U₀ R₀ : Scheme.{u}}
    (s t : R₀ ⟶ U₀) (c : pullback s t ⟶ R₀) (e : U₀ ⟶ R₀) (i : R₀ ⟶ R₀)
    (hcs : c ≫ s = pullback.snd s t ≫ s)
    (hct : c ≫ t = pullback.fst s t ≫ t)
    (hes : e ≫ s = 𝟙 U₀) (het : e ≫ t = 𝟙 U₀)
    (his : i ≫ s = t) (hit : i ≫ t = s)
    (hunique : ∀ {T : Scheme.{u}} (x y : T ⟶ R₀),
      x ≫ s = y ≫ s → x ≫ t = y ≫ t → x = y)
    [Etale s] [Etale t] :
    (ofSchemesOfRelation s t c e i hcs hct hes het his hit hunique).IsEtale where
  presheaf_s := MorphismProperty.presheaf_yoneda_map (inferInstance : Etale s)
  presheaf_t := MorphismProperty.presheaf_yoneda_map (inferInstance : Etale t)

end AlgebraicGeometry.PresheafGroupoid
