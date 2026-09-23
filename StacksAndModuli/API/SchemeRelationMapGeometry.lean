module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Geometry of a scheme relation map

This module records the scheme-theoretic input used when an étale presentation
`U ⟶ X` of an algebraic space is replaced by its relation
`R = U ×_X U`.  If the first projection `R ⟶ U` is étale and the pair of
projections `R ⟶ U × U` is a monomorphism, then the latter map is locally of
finite type, locally quasi-finite, and separated.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

/-- The graph of a morphism is the pullback of the diagonal along the product
of that morphism with the identity. -/
lemma isPullback_graph {A B : C} (f : A ⟶ B) :
    IsPullback f (prod.lift (𝟙 A) f)
      (prod.lift (𝟙 B) (𝟙 B)) (prod.map f (𝟙 B)) := by
  apply IsPullback.mk'
  · apply prod.hom_ext <;> simp
  · intro Q a b hab hbase
    have h := congrArg (fun q ↦ q ≫ prod.fst) hbase
    simpa only [Category.assoc, prod.lift_fst, Category.comp_id] using h
  · intro Q a b hab
    refine ⟨b ≫ prod.fst, ?_, ?_⟩
    · have h := congrArg (fun q ↦ q ≫ prod.fst) hab
      simpa only [Category.assoc, prod.lift_fst, Category.comp_id,
        prod.map_fst] using h.symm
    · apply prod.hom_ext
      · simp only [Category.assoc, prod.lift_fst, Category.comp_id]
      · have h₁ := congrArg (fun q ↦ q ≫ prod.fst) hab
        have h₂ := congrArg (fun q ↦ q ≫ prod.snd) hab
        have h₁' : a = b ≫ prod.fst ≫ f := by
          simpa only [Category.assoc, prod.lift_fst, Category.comp_id,
            prod.map_fst] using h₁
        have h₂' : a = b ≫ prod.snd := by
          simpa only [Category.assoc, prod.lift_snd, Category.comp_id,
            prod.map_snd] using h₂
        simpa only [Category.assoc, prod.lift_snd] using h₁'.symm.trans h₂'

/-- A pullback of a morphism with itself is the pullback of its diagonal along
the product of the morphism with itself. -/
lemma IsPullback.relation_diagonal
    {R U X : C} {s t : R ⟶ U} {p : U ⟶ X}
    (h : IsPullback s t p p) :
    IsPullback (s ≫ p) (prod.lift s t)
      (Limits.diag X) (prod.map p p) := by
  apply IsPullback.mk'
  · calc
      (s ≫ p) ≫ Limits.diag X = prod.lift (s ≫ p) (s ≫ p) := by
        ext <;> simp
      _ = prod.lift (s ≫ p) (t ≫ p) := by rw [h.w]
      _ = prod.lift s t ≫ prod.map p p := by ext <;> simp
  · intro Q a b _ hbase
    apply h.hom_ext
    · have hfst := congrArg (fun q ↦ q ≫ prod.fst) hbase
      simpa only [Category.assoc, prod.lift_fst] using hfst
    · have hsnd := congrArg (fun q ↦ q ≫ prod.snd) hbase
      simpa only [Category.assoc, prod.lift_snd] using hsnd
  · intro Q a b hab
    have hfst := congrArg (fun q ↦ q ≫ prod.fst) hab
    have hsnd := congrArg (fun q ↦ q ≫ prod.snd) hab
    have hfst' : a = (b ≫ prod.fst) ≫ p := by
      simpa only [Category.assoc, Limits.diag, prod.lift_fst,
        prod.map_fst, Category.comp_id] using hfst
    have hsnd' : a = (b ≫ prod.snd) ≫ p := by
      simpa only [Category.assoc, Limits.diag, prod.lift_snd,
        prod.map_snd, Category.comp_id] using hsnd
    have hpairs : (b ≫ prod.fst) ≫ p = (b ≫ prod.snd) ≫ p :=
      hfst'.symm.trans hsnd'
    let l := h.lift (b ≫ prod.fst) (b ≫ prod.snd) hpairs
    refine ⟨l, ?_, ?_⟩
    · dsimp only [l]
      rw [h.lift_fst_assoc]
      exact hfst'.symm
    · apply prod.hom_ext
      · simpa only [Category.assoc, prod.lift_fst] using
          h.lift_fst (b ≫ prod.fst) (b ≫ prod.snd) hpairs
      · simpa only [Category.assoc, prod.lift_snd] using
          h.lift_snd (b ≫ prod.fst) (b ≫ prod.snd) hpairs

end CategoryTheory

namespace AlgebraicGeometry

variable {R U : Scheme.{u}}

/-- If one projection of a scheme relation is étale and the relation map is a
monomorphism, then the relation map is locally of finite type, locally
quasi-finite, and separated. -/
theorem relationMap_locallyOfFiniteType_locallyQuasiFinite_isSeparated
    (s t : R ⟶ U) [Etale s] [Mono (prod.lift s t : R ⟶ U ⨯ U)] :
    (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated :
      MorphismProperty Scheme.{u}) (prod.lift s t) := by
  let graph : R ⟶ R ⨯ U := prod.lift (𝟙 R) t
  let base : R ⨯ U ⟶ U ⨯ U := prod.map s (𝟙 U)
  have hgraph : IsImmersion graph := by
    exact MorphismProperty.of_isPullback
      (CategoryTheory.isPullback_graph t) inferInstance
  let _ : IsImmersion graph := hgraph
  have hbase : Etale base := by
    dsimp only [base]
    exact MorphismProperty.of_isPullback
      (IsPullback.of_prod_fst_with_id s U) inferInstance
  let _ : Etale base := hbase
  have hfac : graph ≫ base = prod.lift s t := by
    apply prod.hom_ext <;> simp [graph, base]
  have hLFTcomp : LocallyOfFiniteType (graph ≫ base) := by infer_instance
  have hLFT : LocallyOfFiniteType (prod.lift s t) := hfac ▸ hLFTcomp
  have hLQF : LocallyQuasiFinite (prod.lift s t) := by
    rw [locallyQuasiFinite_iff_isDiscrete_preimage_singleton]
    intro x
    apply Set.Subsingleton.isDiscrete
    intro a ha b hb
    apply (prod.lift s t).injective
    simpa using ha.trans hb.symm
  have hsep : IsSeparated (prod.lift s t) := by infer_instance
  exact ⟨⟨hLFT, hLQF⟩, hsep⟩

end AlgebraicGeometry
