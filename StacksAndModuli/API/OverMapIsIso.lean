module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Equivalence

/-!
# `Over.map f` is an equivalence only if `f` is an isomorphism

Mathlib records that `CategoryTheory.Over.map f` is an equivalence when `f` is an
isomorphism (`Over.mapId`, and the instance following `Over.mapIso`). The converse is not
there, and it is what identifies the morphism classified by an equivalence of representable
prestacks as an isomorphism.

The proof is elementary. Essential surjectivity at the terminal object `𝟙 V` of `Over V`
produces `X → S` with `X.hom ≫ f` invertible, hence a section `s` of `f`. Fullness applied
to the unique morphism `Over.mk f ⟶ Over.mk (𝟙 V)` in the image then forces `f ≫ s = 𝟙 S`.

## Main results

* `CategoryTheory.Over.isIso_of_isEquivalence_map`: if `Over.map f` is an equivalence then
  `f` is an isomorphism.
-/

@[expose] public section

namespace CategoryTheory.Over

open CategoryTheory

universe v₁ u₁

variable {T : Type u₁} [Category.{v₁} T]

/-- **If `Over.map f` is an equivalence then `f` is an isomorphism.** -/
lemma isIso_of_isEquivalence_map {S V : T} (f : S ⟶ V)
    (h : (Over.map f).IsEquivalence) : IsIso f := by
  have := h
  obtain ⟨X, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := Over.map f) (Over.mk (𝟙 V))
  have hw : e.hom.left ≫ 𝟙 V = X.hom ≫ f := Over.w e.hom
  have hiso : IsIso e.hom.left :=
    ⟨e.inv.left, congrArg CommaMorphism.left e.hom_inv_id,
      congrArg CommaMorphism.left e.inv_hom_id⟩
  have hXf : X.hom ≫ f = e.hom.left := by rw [← hw]; simp
  have hsf : (inv e.hom.left ≫ X.hom) ≫ f = 𝟙 V := by
    rw [Category.assoc, hXf, IsIso.inv_hom_id]
    rfl
  refine ⟨inv e.hom.left ≫ X.hom, ?_, hsf⟩
  obtain ⟨u, hu⟩ := (Over.map f).map_surjective
    (X := Over.mk (𝟙 S)) (Y := Over.mk (inv e.hom.left ≫ X.hom))
    (Over.homMk f (show f ≫ (inv e.hom.left ≫ X.hom) ≫ f = 𝟙 S ≫ f by
      rw [hsf, Category.comp_id, Category.id_comp]))
  have hul : u.left = f := by simpa using congrArg CommaMorphism.left hu
  have hu' : u.left ≫ (inv e.hom.left ≫ X.hom) = 𝟙 S := by simpa using Over.w u
  rw [hul] at hu'
  exact hu'

end CategoryTheory.Over
