module

public import StacksAndModuli.API.CommAlgebraPushoutPseudofunctor

/-!
# Pointwise opposite of commutative-algebra base change

Relative spectrum identifies affine schemes over `Spec R` with the opposite of the
category `Under R` of commutative `R`-algebras.  This file packages pointwise opposite
extension of scalars as a pseudofunctor.  Its coherence is obtained by reversing the
coherence isomorphisms of `underPushoutPseudofunctorOpOp`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory Opposite

universe u

namespace CommRingCat

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

/-- The identity comparison for pointwise opposite extension of scalars. -/
def underPushoutPointwiseOpMapId
    (R : (CommRingCat.{u}ᵒᵖ)ᵒᵖ) :
    (Under.pushout (𝟙 R).unop.unop).op ≅
      Functor.id ((Under R.unop.unop)ᵒᵖ) :=
  (NatIso.op (Cat.Hom.toNatIso
    (underPushoutPseudofunctorOpOp.mapId ⟨R⟩))).symm.trans
      (Functor.opId (Under R.unop.unop))

/-- The composition comparison for pointwise opposite extension of scalars. -/
def underPushoutPointwiseOpMapComp
    {R S T : (CommRingCat.{u}ᵒᵖ)ᵒᵖ}
    (f : R ⟶ S) (g : S ⟶ T) :
    (Under.pushout (f ≫ g).unop.unop).op ≅
      (Under.pushout f.unop.unop).op ⋙
        (Under.pushout g.unop.unop).op :=
  (NatIso.op (Cat.Hom.toNatIso
    (underPushoutPseudofunctorOpOp.mapComp f.toLoc g.toLoc))).symm.trans
      (Functor.opComp (Under.pushout f.unop.unop)
        (Under.pushout g.unop.unop))

/-- Pointwise opposite extension of scalars for commutative algebras. -/
def underPushoutPointwiseOpPseudofunctor :
    Pseudofunctor (LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ)
      Cat.{u, u + 1} := by
  let G := underPushoutPseudofunctorOpOp.{u}
  refine LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Cat.of ((Under R.unop.unop)ᵒᵖ))
    (fun f ↦ (Under.pushout f.unop.unop).op.toCatHom)
    (fun R ↦ Cat.Hom.isoMk (underPushoutPointwiseOpMapId R))
    (fun f g ↦ Cat.Hom.isoMk (underPushoutPointwiseOpMapComp f g)) ?_ ?_ ?_
  · intro R S T U f g h
    apply Cat.Hom₂.ext
    ext A
    apply Quiver.Hom.unop_inj
    have hcoh := G.map₂_associator f.toLoc g.toLoc h.toLoc
    rw [show (α_ f.toLoc g.toLoc h.toLoc).hom = eqToHom (by simp) from
      Subsingleton.elim _ _, PrelaxFunctor.map₂_eqToHom] at hcoh
    have hcomp :
        (G.mapComp (f.toLoc ≫ g.toLoc) h.toLoc).hom ≫
          (G.mapComp f.toLoc g.toLoc).hom ▷ G.map h.toLoc ≫
          (α_ (G.map f.toLoc) (G.map g.toLoc) (G.map h.toLoc)).hom ≫
          G.map f.toLoc ◁ (G.mapComp g.toLoc h.toLoc).inv ≫
          (G.mapComp f.toLoc (g.toLoc ≫ h.toLoc)).inv = 𝟙 _ := by
      simpa using hcoh.symm
    have hcompInv :
        (G.mapComp f.toLoc (g.toLoc ≫ h.toLoc)).hom ≫
          G.map f.toLoc ◁ (G.mapComp g.toLoc h.toLoc).hom ≫
          (α_ (G.map f.toLoc) (G.map g.toLoc) (G.map h.toLoc)).inv ≫
          (G.mapComp f.toLoc g.toLoc).inv ▷ G.map h.toLoc ≫
          (G.mapComp (f.toLoc ≫ g.toLoc) h.toLoc).inv = 𝟙 _ := by
      rw [← cancel_mono
        ((G.mapComp (f.toLoc ≫ g.toLoc) h.toLoc).hom ≫
          (G.mapComp f.toLoc g.toLoc).hom ▷ G.map h.toLoc ≫
          (α_ (G.map f.toLoc) (G.map g.toLoc) (G.map h.toLoc)).hom ≫
          G.map f.toLoc ◁ (G.mapComp g.toLoc h.toLoc).inv ≫
          (G.mapComp f.toLoc (g.toLoc ≫ h.toLoc)).inv)]
      simp only [Category.assoc]
      simp
      exact hcomp.symm
    exact congrArg (fun k ↦ k.toNatTrans.app A.unop) hcompInv
  · intro R S f
    apply Cat.Hom₂.ext
    ext A
    apply Quiver.Hom.unop_inj
    have hcoh := G.map₂_left_unitor f.toLoc
    rw [show (λ_ f.toLoc).hom = eqToHom (by simp) from
      Subsingleton.elim _ _, PrelaxFunctor.map₂_eqToHom] at hcoh
    have hcomp :
        (G.mapComp (𝟙 _) f.toLoc).hom ≫
          (G.mapId ⟨R⟩).hom ▷ G.map f.toLoc ≫
          (λ_ (G.map f.toLoc)).hom = 𝟙 _ := by
      simpa using hcoh.symm
    have hcompInv :
        (λ_ (G.map f.toLoc)).inv ≫
          (G.mapId ⟨R⟩).inv ▷ G.map f.toLoc ≫
          (G.mapComp (𝟙 _) f.toLoc).inv = 𝟙 _ := by
      rw [← cancel_mono
        ((G.mapComp (𝟙 _) f.toLoc).hom ≫
          (G.mapId ⟨R⟩).hom ▷ G.map f.toLoc ≫
          (λ_ (G.map f.toLoc)).hom)]
      simp only [Category.assoc]
      simp
      exact hcomp.symm
    exact congrArg (fun k ↦ k.toNatTrans.app A.unop) hcompInv
  · intro R S f
    apply Cat.Hom₂.ext
    ext A
    apply Quiver.Hom.unop_inj
    have hcoh := G.map₂_right_unitor f.toLoc
    rw [show (ρ_ f.toLoc).hom = eqToHom (by simp) from
      Subsingleton.elim _ _, PrelaxFunctor.map₂_eqToHom] at hcoh
    have hcomp :
        (G.mapComp f.toLoc (𝟙 _)).hom ≫
          G.map f.toLoc ◁ (G.mapId ⟨S⟩).hom ≫
          (ρ_ (G.map f.toLoc)).hom = 𝟙 _ := by
      simpa using hcoh.symm
    have hcompInv :
        (ρ_ (G.map f.toLoc)).inv ≫
          G.map f.toLoc ◁ (G.mapId ⟨S⟩).inv ≫
          (G.mapComp f.toLoc (𝟙 _)).inv = 𝟙 _ := by
      rw [← cancel_mono
        ((G.mapComp f.toLoc (𝟙 _)).hom ≫
          G.map f.toLoc ◁ (G.mapId ⟨S⟩).hom ≫
          (ρ_ (G.map f.toLoc)).hom)]
      simp only [Category.assoc]
      simp
      exact hcomp.symm
    exact congrArg (fun k ↦ k.toNatTrans.app A.unop) hcompInv

@[simp]
lemma underPushoutPointwiseOpPseudofunctor_obj
    (R : (CommRingCat.{u}ᵒᵖ)ᵒᵖ) :
    underPushoutPointwiseOpPseudofunctor.obj ⟨R⟩ =
      Cat.of ((Under R.unop.unop)ᵒᵖ) := rfl

@[simp]
lemma underPushoutPointwiseOpPseudofunctor_map
    {R S : (CommRingCat.{u}ᵒᵖ)ᵒᵖ} (f : R ⟶ S) :
    underPushoutPointwiseOpPseudofunctor.map f.toLoc =
      (Under.pushout f.unop.unop).op.toCatHom := rfl

@[simp]
lemma underPushoutPointwiseOpPseudofunctor_mapId
    (R : (CommRingCat.{u}ᵒᵖ)ᵒᵖ) :
    underPushoutPointwiseOpPseudofunctor.mapId ⟨R⟩ =
      Cat.Hom.isoMk (underPushoutPointwiseOpMapId R) := rfl

@[simp]
lemma underPushoutPointwiseOpPseudofunctor_mapComp
    {R S T : (CommRingCat.{u}ᵒᵖ)ᵒᵖ} (f : R ⟶ S) (g : S ⟶ T) :
    underPushoutPointwiseOpPseudofunctor.mapComp f.toLoc g.toLoc =
      Cat.Hom.isoMk (underPushoutPointwiseOpMapComp f g) := rfl

end

end CommRingCat
