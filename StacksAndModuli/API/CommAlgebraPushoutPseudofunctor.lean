module

public import StacksAndModuli.API.CommAlgebraPushoutDescent
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Sites.Descent.DescentDataAsCoalgebra

/-!
# Base change of commutative algebras as a pseudofunctor of adjunctions

For a commutative ring `R`, commutative `R`-algebras form the under-category
`Under R`.  A ring map `R ⟶ S` induces the adjunction whose left adjoint is
pushout (extension of scalars) and whose right adjoint is restriction of
scalars.  This file packages these adjunctions into a pseudofunctor.  Keeping
both adjoints makes its coherence reducible to the strict coherence of the
restriction functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Bicategory

universe u

noncomputable section

namespace CommRingCat

namespace UnderPushoutAdj

/-- The identity comparison for extension of scalars in under-categories. -/
noncomputable def mapId (R : CommRingCat.{u}) :
    Under.pushout (𝟙 R) ≅ 𝟭 (Under R) :=
  Under.pushoutId

/-- The composition comparison for extension of scalars in under-categories. -/
noncomputable def mapComp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    Under.pushout (f ≫ g) ≅ Under.pushout f ⋙ Under.pushout g :=
  Under.pushoutComp f g

/-- The extension/restriction adjunction attached to a ring map, viewed as a
one-morphism in the bicategory of adjunctions in `Cat`. -/
noncomputable def adjMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Bicategory.Adj.mk (Cat.of (Under R)) ⟶
      Bicategory.Adj.mk (Cat.of (Under S)) :=
  Bicategory.Adj.Hom.mk (CategoryTheory.Adjunction.toCat (Under.mapPushoutAdj f))

/-- The identity comparison for the extension/restriction adjunctions. -/
noncomputable def adjMapId (R : CommRingCat.{u}) :
    adjMap (𝟙 R) ≅
      𝟙 (Bicategory.Adj.mk (Cat.of (Under R))) := by
  refine Bicategory.Adj.iso₂Mk
    (Cat.Hom.isoMk (mapId R)) (Cat.Hom.isoMk (Under.mapId R).symm) ?_
  apply Cat.Hom₂.ext
  rw [Bicategory.toNatTrans_conjugateEquiv]
  change CategoryTheory.conjugateEquiv
      (CategoryTheory.Adjunction.id (C := Under R))
      (Under.mapPushoutAdj (𝟙 R)) (mapId R).hom =
    (Under.mapId R).inv
  exact Adjunction.conjugateEquiv_leftAdjointIdIso_hom
    (Under.mapPushoutAdj (𝟙 R)) (Under.mapId R)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The composition comparison for the extension/restriction adjunctions. -/
noncomputable def adjMapComp {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    adjMap (f ≫ g) ≅ adjMap f ≫ adjMap g := by
  refine Bicategory.Adj.iso₂Mk
    (Cat.Hom.isoMk (mapComp f g)) (Cat.Hom.isoMk (Under.mapComp f g).symm) ?_
  dsimp only [adjMap, Bicategory.Adj.comp_adj]
  rw [CategoryTheory.Adjunction.toCat_comp_toCat]
  apply Cat.Hom₂.ext
  rw [Bicategory.toNatTrans_conjugateEquiv]
  change CategoryTheory.conjugateEquiv
      ((Under.mapPushoutAdj f).comp (Under.mapPushoutAdj g))
      (Under.mapPushoutAdj (f ≫ g)) (mapComp f g).hom =
    (Under.mapComp f g).inv
  simp [mapComp, Under.pushoutComp]

/-- Two maps of adjunctions in `Cat` agree if their right-adjoint components
agree. -/
lemma hom₂_ext_r
    {a b : Bicategory.Adj Cat.{u, u + 1}} {α β : a ⟶ b}
    {x y : α ⟶ β} (h : x.τr = y.τr) : x = y := by
  apply Bicategory.Adj.hom₂_ext
  apply (conjugateEquiv β.adj α.adj).injective
  rw [x.conjugateEquiv_τl, y.conjugateEquiv_τl, h]

end UnderPushoutAdj

/-- Extension and restriction of scalars for commutative algebras, as a
pseudofunctor valued in adjunctions of categories. -/
noncomputable def underPushoutAdjPseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u})
      (Bicategory.Adj Cat.{u, u + 1}) := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Bicategory.Adj.mk (Cat.of (Under R)))
    (fun f ↦ UnderPushoutAdj.adjMap f)
    (fun R ↦ UnderPushoutAdj.adjMapId R)
    (fun f g ↦ UnderPushoutAdj.adjMapComp f g) ?_ ?_ ?_
  · intro R S T U f g h
    apply UnderPushoutAdj.hom₂_ext_r
    ext X
    rfl
  · intro R S f
    apply UnderPushoutAdj.hom₂_ext_r
    ext X
    rfl
  · intro R S f
    apply UnderPushoutAdj.hom₂_ext_r
    ext X
    rfl

/-- The underlying pseudofunctor of extension-of-scalars functors. -/
noncomputable def underPushoutPseudofunctor :
    Pseudofunctor (LocallyDiscrete CommRingCat.{u}) Cat.{u, u + 1} :=
  Pseudofunctor.comp underPushoutAdjPseudofunctor Bicategory.Adj.forget₁

/-- The double-opposite presentation of
`underPushoutAdjPseudofunctor`, in the domain shape used by the descent API. -/
noncomputable def underPushoutAdjPseudofunctorOpOp :
    Pseudofunctor (LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ)
      (Bicategory.Adj Cat.{u, u + 1}) := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Bicategory.Adj.mk (Cat.of (Under R.unop.unop)))
    (fun f ↦ UnderPushoutAdj.adjMap f.unop.unop)
    (fun R ↦ UnderPushoutAdj.adjMapId R.unop.unop)
    (fun f g ↦ UnderPushoutAdj.adjMapComp f.unop.unop g.unop.unop) ?_ ?_ ?_
  · intro R S T U f g h
    apply UnderPushoutAdj.hom₂_ext_r
    ext X
    rfl
  · intro R S f
    apply UnderPushoutAdj.hom₂_ext_r
    ext X
    rfl
  · intro R S f
    apply UnderPushoutAdj.hom₂_ext_r
    ext X
    rfl

/-- The underlying double-opposite pseudofunctor of commutative-algebra base
change. -/
noncomputable def underPushoutPseudofunctorOpOp :
    Pseudofunctor (LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ) Cat.{u, u + 1} :=
  Pseudofunctor.comp underPushoutAdjPseudofunctorOpOp Bicategory.Adj.forget₁

/-- Coalgebra-form descent data for commutative algebras are effective along a
faithfully flat ring map. -/
theorem isEquivalence_toDescentDataAsCoalgebra_of_faithfullyFlat
    {A B : CommRingCat.{u}} (f : A ⟶ B) (hf : f.hom.FaithfullyFlat) :
    (underPushoutAdjPseudofunctorOpOp.toDescentDataAsCoalgebra
      (fun (_ : Unit) ↦ f.op)).IsEquivalence := by
  apply (Pseudofunctor.isEquivalence_toDescentDataAsCoalgebra_iff_isEquivalence_comonadComparison
      (F := underPushoutAdjPseudofunctorOpOp) (ι := Unit) f.op).2
  change (Comonad.comparison (Under.mapPushoutAdj f)).IsEquivalence
  exact (comonadicPushoutOfFaithfullyFlat f hf).eqv

end CommRingCat
