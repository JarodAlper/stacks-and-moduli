module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete

/-!
# Compositors of the scheme module pseudofunctor

This file identifies the abstract compositors of
`Scheme.Modules.pseudofunctorToCat` with the concrete pullback compositors.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The left-adjoint part of the adjunction-valued pseudofunctor of module
sheaves on schemes. -/
noncomputable def pseudofunctorToCat :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Modules.pseudofunctor.comp Bicategory.Adj.forget₁

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Hom

/-- Reversing a compositional equality of scheme maps gives the corresponding
equality in the locally discrete opposite category. -/
lemma schemeOpCompEq {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (q : X ⟶ Z) (hgf : g ≫ f = q) :
    f.op.toLoc ≫ g.op.toLoc = q.op.toLoc := by
  subst q
  rfl

set_option maxHeartbeats 400000 in
-- Unfolding the adjunction-valued pseudofunctor compositor is
-- elaboration-intensive.
/-- The inverse compositor of the module pseudofunctor is the concrete pullback
compositor followed by transport along the supplied equality. -/
lemma pseudofunctorToCat_mapComp'_inv_app
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (q : X ⟶ Z) (hgf : g ≫ f = q) (M : Z.Modules) :
    (Scheme.Modules.pseudofunctorToCat.mapComp'
      f.op.toLoc g.op.toLoc q.op.toLoc
        (schemeOpCompEq g f q hgf)).inv.toNatTrans.app M =
      (Modules.pullbackComp g f).hom.app M ≫
        (Modules.pullbackCongr hgf.symm).inv.app M := by
  change (Scheme.Modules.pseudofunctorToCat.mapComp
      f.op.toLoc g.op.toLoc).inv.toNatTrans.app M ≫
    (Scheme.Modules.pseudofunctorToCat.map₂Iso
      (eqToIso (congrArg (fun k : X ⟶ Z ↦ k.op.toLoc)
        hgf.symm))).inv.toNatTrans.app M = _
  rw [show (Scheme.Modules.pseudofunctorToCat.mapComp
      f.op.toLoc g.op.toLoc).inv.toNatTrans.app M =
        (Modules.pullbackComp g f).hom.app M by rfl]
  rw [show (Scheme.Modules.pseudofunctorToCat.map₂Iso
      (eqToIso (congrArg (fun k : X ⟶ Z ↦ k.op.toLoc)
        hgf.symm))).inv.toNatTrans.app M =
        (Modules.pullbackCongr hgf.symm).inv.app M by
      subst hgf
      rfl]

set_option maxHeartbeats 400000 in
-- Unfolding the adjunction-valued pseudofunctor compositor is
-- elaboration-intensive.
/-- The forward compositor of the module pseudofunctor is transport along the
supplied equality followed by the inverse concrete pullback compositor. -/
lemma pseudofunctorToCat_mapComp'_hom_app
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z)
    (q : X ⟶ Z) (hgf : g ≫ f = q) (M : Z.Modules) :
    (Scheme.Modules.pseudofunctorToCat.mapComp'
      f.op.toLoc g.op.toLoc q.op.toLoc
        (schemeOpCompEq g f q hgf)).hom.toNatTrans.app M =
      (Modules.pullbackCongr hgf.symm).hom.app M ≫
        (Modules.pullbackComp g f).inv.app M := by
  change (Scheme.Modules.pseudofunctorToCat.map₂Iso
      (eqToIso (congrArg (fun k : X ⟶ Z ↦ k.op.toLoc)
        hgf.symm))).hom.toNatTrans.app M ≫
    (Scheme.Modules.pseudofunctorToCat.mapComp
      f.op.toLoc g.op.toLoc).hom.toNatTrans.app M = _
  rw [show (Scheme.Modules.pseudofunctorToCat.map₂Iso
      (eqToIso (congrArg (fun k : X ⟶ Z ↦ k.op.toLoc)
        hgf.symm))).hom.toNatTrans.app M =
        (Modules.pullbackCongr hgf.symm).hom.app M by
      subst hgf
      rfl]
  rw [show (Scheme.Modules.pseudofunctorToCat.mapComp
      f.op.toLoc g.op.toLoc).hom.toNatTrans.app M =
        (Modules.pullbackComp g f).inv.app M by rfl]

/-- The pseudofunctor attached to `Spec.op` sends a ring map, viewed as a 1-cell of the
locally discrete bicategory, to the locally discrete image of `Spec` of it.

This is the bridge between the two spellings of the same 1-cell that occur on either side of
a `Pseudofunctor.comp`: `Scheme.Spec.op.toPseudofunctor.map ⟨f⟩` and `(Spec.map φ).op.toLoc`. -/
lemma toPseudofunctor_map_specOp {a b : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ}
    (f : a.as ⟶ b.as) :
    Scheme.Spec.op.toPseudofunctor.map (⟨f⟩ : a ⟶ b) =
      (Spec.map f.unop.unop).op.toLoc := rfl

set_option maxHeartbeats 1000000 in
-- Unfolding the adjunction-valued pseudofunctor compositor is elaboration-intensive; see
-- `pseudofunctorToCat_mapComp'_hom_app` above.
/-- The compositor of the `Spec`-precomposed module pseudofunctor is the pullback
compositor, in the spelling produced by `Pseudofunctor.comp_mapComp`.

This is `pseudofunctorToCat_mapComp'_hom_app`'s inner `rfl` restated with
`Scheme.Spec.op.toPseudofunctor.map` in place of `_.op.toLoc`, which is the shape a goal
coming from `Pseudofunctor.comp` actually has.  Note the transposition: the *first*
compositor argument matches the *second* `pullbackComp` argument. -/
lemma pseudofunctorToCat_mapComp_specOp_hom_app
    {a b c : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ} (f : a.as ⟶ b.as) (g : b.as ⟶ c.as)
    (M : (Spec a.as.unop.unop).Modules) :
    (Scheme.Modules.pseudofunctorToCat.mapComp
        (Scheme.Spec.op.toPseudofunctor.map (⟨f⟩ : a ⟶ b))
        (Scheme.Spec.op.toPseudofunctor.map (⟨g⟩ : b ⟶ c))).hom.toNatTrans.app M =
      (Modules.pullbackComp (Spec.map g.unop.unop) (Spec.map f.unop.unop)).inv.app M := rfl

set_option maxHeartbeats 2000000 in
/-- The compositor identity again, with the object in the **bundled** `Cat` spelling
`↥(pseudofunctorToCat.obj ⟨op (Spec R)⟩)` rather than `(Spec R).Modules`.

This is the spelling a goal coming from a full subcategory of `pseudofunctorToCat` actually
has, and stating it this way is what makes the lemma usable there: `exact` against the
unbundled version has to unify the two types, which forces the adjunction-valued
pseudofunctor to unfold and does not terminate in any reasonable time inside a file that
imports `part3.1.2`.  Paying that unification once, here, costs seconds. -/
lemma pseudofunctorToCat_mapComp_specOp_hom_app_bundled
    {a b c : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ} (f : a.as ⟶ b.as) (g : b.as ⟶ c.as)
    (M : Scheme.Modules.pseudofunctorToCat.obj
      (⟨op (Spec a.as.unop.unop)⟩ : LocallyDiscrete Scheme.{u}ᵒᵖ)) :
    (Scheme.Modules.pseudofunctorToCat.mapComp
        (Scheme.Spec.op.toPseudofunctor.map (⟨f⟩ : a ⟶ b))
        (Scheme.Spec.op.toPseudofunctor.map (⟨g⟩ : b ⟶ c))).hom.toNatTrans.app M =
      (Modules.pullbackComp (Spec.map g.unop.unop) (Spec.map f.unop.unop)).inv.app M := rfl

set_option maxHeartbeats 2000000 in
/-- The compositor identity for an object of a full subcategory cut out by an **arbitrary**
object property of `pseudofunctorToCat`.

This is the form to use against a goal in a file importing `part3.1.2`.  Applying the two
variants above there requires unifying `X.obj`'s type
`↥(pseudofunctorToCat.obj ⟨op (Spec R)⟩)` with `(Spec R).Modules`, which unfolds the
adjunction-valued pseudofunctor and does not terminate; quantifying over the property `P`
instead makes the use site a pure instantiation `P := isQuasicoherentProperty`, with no
cross-spelling unification at all. -/
lemma pseudofunctorToCat_mapComp_specOp_hom_app_fullSub
    (P : Scheme.Modules.pseudofunctorToCat.{u}.ObjectProperty)
    {a b c : LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ} (f : a.as ⟶ b.as) (g : b.as ⟶ c.as)
    (X : (P.prop (⟨op (Spec a.as.unop.unop)⟩ :
      LocallyDiscrete Scheme.{u}ᵒᵖ)).FullSubcategory) :
    (Scheme.Modules.pseudofunctorToCat.mapComp
        (Scheme.Spec.op.toPseudofunctor.map (⟨f⟩ : a ⟶ b))
        (Scheme.Spec.op.toPseudofunctor.map (⟨g⟩ : b ⟶ c))).hom.toNatTrans.app X.obj =
      (Modules.pullbackComp (Spec.map g.unop.unop) (Spec.map f.unop.unop)).inv.app X.obj :=
  rfl

end AlgebraicGeometry.Scheme.Modules.Hom
