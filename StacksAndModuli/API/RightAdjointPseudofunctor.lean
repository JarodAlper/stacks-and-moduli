module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# The pseudofunctor of right adjoints

A pseudofunctor from a locally discrete bicategory to the bicategory of
adjunctions in `Cat` determines a contravariant pseudofunctor by taking right
adjoints.  This file supplies that construction, which is not yet present in
Mathlib's `Bicategory.Adj` API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Bicategory Opposite

universe u v w

namespace CategoryTheory.Bicategory.Adj

noncomputable section

/-- Two 2-morphisms between morphisms of adjunctions in `Cat` agree when their
right-adjoint components agree.  This is useful for proving coherence of
adjunction-valued pseudofunctors: the left component is the mate of the right
component and therefore carries no additional data. -/
lemma hom₂_ext_r
    {a b : Bicategory.Adj Cat.{u, u + 1}} {f g : a ⟶ b}
    {x y : f ⟶ g} (h : x.τr = y.τr) : x = y := by
  apply Bicategory.Adj.hom₂_ext
  apply (conjugateEquiv g.adj f.adj).injective
  rw [x.conjugateEquiv_τl, y.conjugateEquiv_τl, h]

/-- The right-adjoint component of an equality between adjunctions is the
oppositely oriented equality between their right adjoints. -/
@[simp]
lemma eqToHom_τr
    {B : Type v} [Bicategory B] {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (h : f = g) :
    (eqToHom h : f ⟶ g).τr =
      eqToHom (congrArg (fun k ↦ k.r) h).symm := by
  subst h
  rfl

/-- Taking the right adjoint of every map in an adjunction-valued
pseudofunctor reverses the variance and gives a `Cat`-valued pseudofunctor. -/
noncomputable def rightPseudofunctor
    {C : Type w} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete C) (Bicategory.Adj Cat.{u, u + 1})) :
    Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{u, u + 1} := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun X ↦ (F.obj ⟨X.unop⟩).obj)
    (fun f ↦ (F.map f.unop.toLoc).r)
    (fun X ↦ Bicategory.Adj.rIso (F.mapId ⟨X.unop⟩))
    (fun f g ↦ Bicategory.Adj.rIso
      (F.mapComp g.unop.toLoc f.unop.toLoc)) ?_ ?_ ?_
  · intro W X Y Z f g h
    apply Cat.Hom₂.ext
    have H := congrArg Bicategory.Adj.Hom₂.τr
      (F.map₂_associator h.unop.toLoc g.unop.toLoc f.unop.toLoc)
    rw [show (α_ h.unop.toLoc g.unop.toLoc f.unop.toLoc).hom =
      eqToHom (by simp) from Subsingleton.elim _ _,
      PrelaxFunctor.map₂_eqToHom] at H
    dsimp at H
    have H' := congrArg (fun k ↦ k.toNatTrans) H.symm
    rw [Cat.Hom₂.eqToHom_toNatTrans]
    simpa [eqToHom_τr, Cat.Hom₂.eqToHom_toNatTrans,
      CategoryTheory.eqToHom_app] using H'
  · intro X Y f
    let e := Bicategory.Adj.rIso
        (F.mapComp f.unop.toLoc (𝟙 X).unop.toLoc) ≪≫
      whiskerRightIso (Bicategory.Adj.rIso
        (F.mapId ⟨X.unop⟩)) (F.map f.unop.toLoc).r ≪≫
      (λ_ (F.map f.unop.toLoc).r)
    change e.hom = (eqToIso (by simp)).hom
    rw [← Iso.inv_eq_inv]
    rw [eqToIso.inv]
    have H := congrArg Bicategory.Adj.Hom₂.τr
      (F.map₂_right_unitor f.unop.toLoc)
    rw [show (ρ_ f.unop.toLoc).hom = eqToHom (by simp) from
      Subsingleton.elim _ _, PrelaxFunctor.map₂_eqToHom] at H
    dsimp at H
    simpa [e, eqToHom_τr, eqToIso.inv] using H.symm
  · intro X Y f
    let e := Bicategory.Adj.rIso
        (F.mapComp (𝟙 Y).unop.toLoc f.unop.toLoc) ≪≫
      whiskerLeftIso (F.map f.unop.toLoc).r
        (Bicategory.Adj.rIso (F.mapId ⟨Y.unop⟩)) ≪≫
      (ρ_ (F.map f.unop.toLoc).r)
    change e.hom = (eqToIso (by simp)).hom
    rw [← Iso.inv_eq_inv]
    rw [eqToIso.inv]
    have H := congrArg Bicategory.Adj.Hom₂.τr
      (F.map₂_left_unitor f.unop.toLoc)
    rw [show (λ_ f.unop.toLoc).hom = eqToHom (by simp) from
      Subsingleton.elim _ _, PrelaxFunctor.map₂_eqToHom] at H
    dsimp at H
    simpa [e, eqToHom_τr, eqToIso.inv] using H.symm

end

end CategoryTheory.Bicategory.Adj
