module

public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-!
# Left projection of adjunction-valued pseudofunctors and transformations

An adjunction-valued pseudofunctor on a locally discrete bicategory determines
a `Cat`-valued pseudofunctor by taking left adjoints, with the compositors
taken componentwise; unlike composition with `Bicategory.Adj.forget₁`, this
projection introduces no residual identity 2-cells in the compositors.  A
strong transformation of adjunction-valued pseudofunctors likewise projects to
a strong transformation of the left-adjoint pseudofunctors.  Coherence is
inherited: each axiom is the left component of the corresponding axiom
upstairs, because equality of 2-morphisms of adjunctions is detected on left
components.

This is the `τl`-mirror of `CategoryTheory.Bicategory.Adj.rightPseudofunctor`
in `StacksAndModuli/API/RightAdjointPseudofunctor.lean`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Bicategory

universe u w v

namespace CategoryTheory.Bicategory.Adj

/-- The left-adjoint component of an equality between adjunctions is the
underlying equality of left adjoints. -/
@[simp]
lemma eqToHom_τl
    {B : Type w} [Bicategory B] {a b : Bicategory.Adj B}
    {f g : a ⟶ b} (h : f = g) :
    (eqToHom h : f ⟶ g).τl =
      eqToHom (congrArg (fun k ↦ k.l) h) := by
  subst h
  rfl

/-- Constructor for isomorphisms between 1-morphisms in `Adj B` from an
isomorphism of the left adjoints alone: the right component is the conjugate,
so the mate condition holds by construction. -/
noncomputable def iso₂MkOfLeft {B : Type w} [Bicategory B] {a b : Bicategory.Adj B}
    {α β : a ⟶ b} (el : α.l ≅ β.l) : α ≅ β :=
  iso₂Mk el
    { hom := Bicategory.conjugateEquiv β.adj α.adj el.hom
      inv := Bicategory.conjugateEquiv α.adj β.adj el.inv
      hom_inv_id := by
        rw [Bicategory.conjugateEquiv_comp, el.inv_hom_id,
          Bicategory.conjugateEquiv_id]
      inv_hom_id := by
        rw [Bicategory.conjugateEquiv_comp, el.hom_inv_id,
          Bicategory.conjugateEquiv_id] }
    rfl

@[simp]
lemma lIso_iso₂MkOfLeft {B : Type w} [Bicategory B] {a b : Bicategory.Adj B}
    {α β : a ⟶ b} (el : α.l ≅ β.l) :
    lIso (iso₂MkOfLeft el) = el := rfl

@[simp]
lemma iso₂MkOfLeft_hom_τl {B : Type w} [Bicategory B] {a b : Bicategory.Adj B}
    {α β : a ⟶ b} (el : α.l ≅ β.l) :
    (iso₂MkOfLeft el).hom.τl = el.hom := rfl

@[simp]
lemma iso₂MkOfLeft_inv_τl {B : Type w} [Bicategory B] {a b : Bicategory.Adj B}
    {α β : a ⟶ b} (el : α.l ≅ β.l) :
    (iso₂MkOfLeft el).inv.τl = el.inv := rfl

noncomputable section

/-- Taking the left adjoint of every map in an adjunction-valued pseudofunctor
on a locally discrete bicategory gives a `Cat`-valued pseudofunctor with
componentwise compositors. -/
def leftPseudofunctor {C : Type w} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete C) (Bicategory.Adj Cat.{u, u + 1})) :
    Pseudofunctor (LocallyDiscrete C) Cat.{u, u + 1} := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun X ↦ (F.obj ⟨X⟩).obj)
    (fun f ↦ (F.map f.toLoc).l)
    (fun X ↦ Bicategory.Adj.lIso (F.mapId ⟨X⟩))
    (fun f g ↦ Bicategory.Adj.lIso (F.mapComp f.toLoc g.toLoc)) ?_ ?_ ?_
  · intro W X Y Z f g h
    apply Cat.Hom₂.ext
    have H := congrArg Bicategory.Adj.Hom₂.τl
      (F.map₂_associator f.toLoc g.toLoc h.toLoc)
    rw [show (α_ f.toLoc g.toLoc h.toLoc).hom =
      eqToHom (by simp) from Subsingleton.elim _ _,
      PrelaxFunctor.map₂_eqToHom] at H
    dsimp at H
    have H' := congrArg (fun k ↦ k.toNatTrans) H.symm
    rw [Cat.Hom₂.eqToHom_toNatTrans]
    simpa [eqToHom_τl, Cat.Hom₂.eqToHom_toNatTrans,
      CategoryTheory.eqToHom_app] using H'
  · intro X Y f
    let e := Bicategory.Adj.lIso (F.mapComp (𝟙 X).toLoc f.toLoc) ≪≫
      whiskerRightIso (Bicategory.Adj.lIso (F.mapId ⟨X⟩)) (F.map f.toLoc).l ≪≫
      (λ_ (F.map f.toLoc).l)
    change e.hom = (eqToIso (by simp)).hom
    rw [eqToIso.hom]
    have H := congrArg Bicategory.Adj.Hom₂.τl
      (F.map₂_left_unitor f.toLoc)
    rw [show (λ_ f.toLoc).hom = eqToHom (by simp) from
      Subsingleton.elim _ _, PrelaxFunctor.map₂_eqToHom] at H
    dsimp at H
    simpa [e, eqToHom_τl] using H.symm
  · intro X Y f
    let e := Bicategory.Adj.lIso (F.mapComp f.toLoc (𝟙 Y).toLoc) ≪≫
      whiskerLeftIso (F.map f.toLoc).l
        (Bicategory.Adj.lIso (F.mapId ⟨Y⟩)) ≪≫
      (ρ_ (F.map f.toLoc).l)
    change e.hom = (eqToIso (by simp)).hom
    rw [eqToIso.hom]
    have H := congrArg Bicategory.Adj.Hom₂.τl
      (F.map₂_right_unitor f.toLoc)
    rw [show (ρ_ f.toLoc).hom = eqToHom (by simp) from
      Subsingleton.elim _ _, PrelaxFunctor.map₂_eqToHom] at H
    dsimp at H
    simpa [e, eqToHom_τl] using H.symm

variable {C : Type w} [Category.{v} C]
  {F G : Pseudofunctor (LocallyDiscrete C) (Bicategory.Adj Cat.{u, u + 1})}

/-- The left components of a strong transformation of adjunction-valued
pseudofunctors form a strong transformation of the left-adjoint
pseudofunctors. -/
def leftStrongTrans (η : Pseudofunctor.StrongTrans F G) :
    Pseudofunctor.StrongTrans (leftPseudofunctor F) (leftPseudofunctor G) where
  app a := (η.app ⟨a.as⟩).l
  naturality {a b} f := Adj.lIso (η.naturality f)
  naturality_naturality {a b f g} θ := by
    obtain rfl : f = g := LocallyDiscrete.eq_of_hom θ
    obtain rfl : θ = 𝟙 f := Subsingleton.elim _ _
    simp
  naturality_id a := by
    have h := congrArg Adj.Hom₂.τl (η.naturality_id ⟨a.as⟩)
    simp only [Adj.comp_τl, Adj.whiskerLeft_τl, Adj.whiskerRight_τl,
      Adj.leftUnitor_hom_τl, Adj.rightUnitor_inv_τl] at h
    exact h
  naturality_comp {a b c} f g := by
    have h := congrArg Adj.Hom₂.τl (η.naturality_comp f g)
    simp only [Adj.comp_τl, Adj.whiskerLeft_τl, Adj.whiskerRight_τl,
      Adj.associator_hom_τl, Adj.associator_inv_τl] at h
    exact h

@[simp]
lemma leftStrongTrans_app (η : Pseudofunctor.StrongTrans F G)
    (a : LocallyDiscrete C) :
    ((leftStrongTrans η).app a) = (η.app ⟨a.as⟩).l := rfl

@[simp]
lemma leftStrongTrans_naturality_hom (η : Pseudofunctor.StrongTrans F G)
    {a b : LocallyDiscrete C} (f : a ⟶ b) :
    ((leftStrongTrans η).naturality f).hom = (η.naturality f).hom.τl := rfl

variable (F₀ : Pseudofunctor (LocallyDiscrete C) Cat.{u, u + 1})

/-- Enhance a `Cat`-valued pseudofunctor on a locally discrete bicategory to an
adjunction-valued pseudofunctor, given a right adjoint for each of its maps.
The compositors are transported by `iso₂MkOfLeft`, so the left projection
recovers the original compositors on the nose
(`Adj.leftPseudofunctor_adjPseudofunctorOfLeft_mapComp`). -/
def adjPseudofunctorOfLeft
    (right : ∀ {a b : C}, (a ⟶ b) → (F₀.obj ⟨b⟩ ⟶ F₀.obj ⟨a⟩))
    (adj : ∀ {a b : C} (f : a ⟶ b),
      Bicategory.Adjunction (F₀.map f.toLoc) (right f)) :
    Pseudofunctor (LocallyDiscrete C) (Bicategory.Adj Cat.{u, u + 1}) := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Bicategory.Adj.mk (F₀.obj ⟨X⟩))
    (fun f ↦ .mk (adj f))
    (fun X ↦ iso₂MkOfLeft (F₀.mapId ⟨X⟩))
    (fun f g ↦ iso₂MkOfLeft (F₀.mapComp f.toLoc g.toLoc)) ?_ ?_ ?_
  · intro W X Y Z f g h
    apply hom₂_ext
    simp only [Adj.comp_τl, Adj.whiskerLeft_τl, Adj.whiskerRight_τl,
      Adj.associator_hom_τl, iso₂MkOfLeft_hom_τl, iso₂MkOfLeft_inv_τl,
      eqToHom_τl]
    have H := F₀.map₂_associator f.toLoc g.toLoc h.toLoc
    rw [show (α_ f.toLoc g.toLoc h.toLoc).hom =
      eqToHom (by simp) from Subsingleton.elim _ _,
      PrelaxFunctor.map₂_eqToHom] at H
    exact H.symm
  · intro X Y f
    apply hom₂_ext
    simp only [Adj.comp_τl, Adj.whiskerRight_τl,
      Adj.leftUnitor_hom_τl, iso₂MkOfLeft_hom_τl,
      eqToHom_τl]
    have H := F₀.map₂_left_unitor f.toLoc
    rw [show (λ_ f.toLoc).hom = eqToHom (by simp) from
      Subsingleton.elim _ _, PrelaxFunctor.map₂_eqToHom] at H
    exact H.symm
  · intro X Y f
    apply hom₂_ext
    simp only [Adj.comp_τl, Adj.whiskerLeft_τl,
      Adj.rightUnitor_hom_τl, iso₂MkOfLeft_hom_τl,
      eqToHom_τl]
    have H := F₀.map₂_right_unitor f.toLoc
    rw [show (ρ_ f.toLoc).hom = eqToHom (by simp) from
      Subsingleton.elim _ _, PrelaxFunctor.map₂_eqToHom] at H
    exact H.symm

@[simp]
lemma leftPseudofunctor_adjPseudofunctorOfLeft_map
    (right : ∀ {a b : C}, (a ⟶ b) → (F₀.obj ⟨b⟩ ⟶ F₀.obj ⟨a⟩))
    (adj : ∀ {a b : C} (f : a ⟶ b),
      Bicategory.Adjunction (F₀.map f.toLoc) (right f))
    {a b : LocallyDiscrete C} (f : a ⟶ b) :
    (leftPseudofunctor (adjPseudofunctorOfLeft F₀ right adj)).map f =
      F₀.map f := rfl

@[simp]
lemma leftPseudofunctor_adjPseudofunctorOfLeft_mapComp
    (right : ∀ {a b : C}, (a ⟶ b) → (F₀.obj ⟨b⟩ ⟶ F₀.obj ⟨a⟩))
    (adj : ∀ {a b : C} (f : a ⟶ b),
      Bicategory.Adjunction (F₀.map f.toLoc) (right f))
    {a b c : LocallyDiscrete C} (f : a ⟶ b) (g : b ⟶ c) :
    (leftPseudofunctor (adjPseudofunctorOfLeft F₀ right adj)).mapComp f g =
      F₀.mapComp f g := rfl

@[simp]
lemma leftPseudofunctor_adjPseudofunctorOfLeft_mapId
    (right : ∀ {a b : C}, (a ⟶ b) → (F₀.obj ⟨b⟩ ⟶ F₀.obj ⟨a⟩))
    (adj : ∀ {a b : C} (f : a ⟶ b),
      Bicategory.Adjunction (F₀.map f.toLoc) (right f))
    (a : LocallyDiscrete C) :
    (leftPseudofunctor (adjPseudofunctorOfLeft F₀ right adj)).mapId a =
      F₀.mapId a := rfl

/-- The left projection of `adjPseudofunctorOfLeft` compares to the original
pseudofunctor by an identity-components strong transformation. -/
def adjPseudofunctorOfLeftComparison
    (right : ∀ {a b : C}, (a ⟶ b) → (F₀.obj ⟨b⟩ ⟶ F₀.obj ⟨a⟩))
    (adj : ∀ {a b : C} (f : a ⟶ b),
      Bicategory.Adjunction (F₀.map f.toLoc) (right f)) :
    Pseudofunctor.StrongTrans
      (leftPseudofunctor (adjPseudofunctorOfLeft F₀ right adj)) F₀ where
  app a := 𝟙 (F₀.obj a)
  naturality {a b} f := ρ_ (F₀.map f) ≪≫ (λ_ (F₀.map f)).symm
  naturality_naturality {a b f g} θ := by
    obtain rfl : f = g := LocallyDiscrete.eq_of_hom θ
    obtain rfl : θ = 𝟙 f := Subsingleton.elim _ _
    simp

end

end CategoryTheory.Bicategory.Adj
