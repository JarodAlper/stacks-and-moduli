module

public import StacksAndModuli.API.BasedFunctorEquivalence
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.1-representable-morphisms-and-algebraic-spaces»
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affine morphisms from chosen scheme representations

To prove that a morphism of prestacks is representable by affine morphisms, it is
enough to choose one affine scheme representation of every scheme-valued fiber.
Any other scheme representation differs from the chosen one by an equivalence of
representable prestacks, whose classified scheme morphism is an isomorphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits
open CategoryTheory.BasedCategory

universe v₁ v₂ u₁ u₂ u

namespace AlgebraicGeometry.BasedFunctor

variable {Xcat : BasedCategory.{v₁, u₁} Scheme.{u}}
  {Ycat : BasedCategory.{v₂, u₂} Scheme.{u}}

/-- A chosen affine scheme representation of every scheme-valued fiber proves
relative representability by affine morphisms. -/
theorem relativelyRepresentableWith_isAffineHom_of_goodRepresentations
    (F : Xcat ⥤ᵇ Ycat)
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    (hgood : ∀ (T : Scheme.{u}) (g : overBased T ⥤ᵇ Ycat),
      ∃ (W : Scheme.{u})
        (K : overBased W ⥤ᵇ fiberProduct F g),
        K.toFunctor.IsEquivalence ∧
          IsAffineHom (K.comp (fiberProductSnd F g)).overHom) :
    F.RelativelyRepresentableWith
      (@IsAffineHom : MorphismProperty Scheme.{u}) := by
  constructor
  · intro T g
    obtain ⟨W, K, hK, -⟩ := hgood T g
    exact ⟨W, K, hK⟩
  · intro T g V E hE
    obtain ⟨W, K, hK, hAffine⟩ := hgood T g
    let _ : K.toFunctor.IsEquivalence := hK
    obtain ⟨J, ⟨α⟩, ⟨β⟩⟩ :=
      CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor K
    have hJ : J.toFunctor.IsEquivalence :=
      Functor.IsEquivalence.mk' K.toFunctor
        ((BasedNatTrans.forgetful _ _).mapIso β).symm
        ((BasedNatTrans.forgetful _ _).mapIso α)
    let M := E.comp J
    have hM : M.toFunctor.IsEquivalence :=
      Functor.isEquivalence_trans E.toFunctor J.toFunctor
    let H := fiberProductSnd F g
    let e : M.comp (K.comp H) ≅ E.comp H := by
      simpa only [M, H, CategoryTheory.BasedFunctor.comp_assoc,
        CategoryTheory.BasedFunctor.id_comp] using
        CategoryTheory.BasedCategory.isoWhiskerLeft E
          (CategoryTheory.BasedCategory.isoWhiskerRight β H)
    have heq := CategoryTheory.BasedFunctor.overHom_eq_of_iso e
    rw [CategoryTheory.BasedFunctor.overHom_comp] at heq
    let _ : _root_.CategoryTheory.IsIso M.overHom :=
      CategoryTheory.BasedFunctor.isIso_overHom_of_isEquivalence M hM
    let _ : IsAffineHom (K.comp H).overHom := hAffine
    have hcomp : IsAffineHom (M.overHom ≫ (K.comp H).overHom) := inferInstance
    exact heq ▸ hcomp

end AlgebraicGeometry.BasedFunctor
