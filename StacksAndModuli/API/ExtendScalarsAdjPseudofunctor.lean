module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Pseudofunctor
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import StacksAndModuli.API.AdjointStrongTransProjection
public import StacksAndModuli.API.ModuleDescentData.Standard

/-!
# The adjunction-valued extension-of-scalars pseudofunctor

The extension/restriction-of-scalars adjunctions assemble into a pseudofunctor
from commutative rings (indexed as for
`ModuleCat.extendScalarsPseudofunctorOpOp`) to the bicategory of adjunctions in
`Cat`.  The compositor mate conditions hold by construction, because Mathlib
defines `ModuleCat.extendScalarsId` and `ModuleCat.extendScalarsComp` as
conjugates of the restriction-of-scalars compositors.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Bicategory Opposite

universe u

namespace ModuleCat

/-- The conjugate of the extension-of-scalars unitor is the inverse
restriction-of-scalars unitor; this holds by definition of
`ModuleCat.extendScalarsId`. -/
lemma conjugateEquiv_extendScalarsId_hom (R : Type u) [CommRing R] :
    conjugateEquiv Adjunction.id (extendRestrictScalarsAdj (RingHom.id R))
      (extendScalarsId R).hom = (restrictScalarsId R).inv :=
  congrArg Iso.inv (Equiv.apply_symm_apply
    (conjugateIsoEquiv (extendRestrictScalarsAdj (RingHom.id R)) Adjunction.id)
    (restrictScalarsId R))

/-- The conjugate of the extension-of-scalars compositor is the inverse
restriction-of-scalars compositor; this holds by definition of
`ModuleCat.extendScalarsComp`. -/
lemma conjugateEquiv_extendScalarsComp_hom
    {R₁ R₂ R₃ : Type u} [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (f : R₁ →+* R₂) (g : R₂ →+* R₃) :
    conjugateEquiv
      ((extendRestrictScalarsAdj f).comp (extendRestrictScalarsAdj g))
      (extendRestrictScalarsAdj (g.comp f)) (extendScalarsComp f g).hom =
      (restrictScalarsComp f g).inv :=
  congrArg Iso.hom (Equiv.apply_symm_apply
    (conjugateIsoEquiv
      ((extendRestrictScalarsAdj f).comp (extendRestrictScalarsAdj g))
      (extendRestrictScalarsAdj (g.comp f)))
    (restrictScalarsComp f g).symm)

/-- The pseudofunctor valued in adjunctions in `Cat` which sends a commutative
ring to its module category, a ring morphism to the extension/restriction of
scalars adjunction, indexed as for
`ModuleCat.extendScalarsPseudofunctorOpOp`. -/
noncomputable def extendRestrictScalarsAdjPseudofunctor :
    Pseudofunctor (LocallyDiscrete (CommRingCat.{u}ᵒᵖ)ᵒᵖ)
      (Bicategory.Adj Cat.{u, u + 1}) := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R ↦ Bicategory.Adj.mk (Cat.of (ModuleCat.{u} R.unop.unop)))
    (fun g ↦ .mk (extendRestrictScalarsAdj g.unop.unop.hom).toCat)
    (fun R ↦ Bicategory.Adj.iso₂Mk
      (Cat.Hom.isoMk (extendScalarsId R.unop.unop))
      (Cat.Hom.isoMk (restrictScalarsId R.unop.unop).symm) ?_)
    (fun g h ↦ Bicategory.Adj.iso₂Mk
      (Cat.Hom.isoMk (extendScalarsComp g.unop.unop.hom h.unop.unop.hom))
      (Cat.Hom.isoMk
        (restrictScalarsComp g.unop.unop.hom h.unop.unop.hom).symm) ?_)
    ?_ ?_ ?_
  · apply Cat.Hom₂.ext
    rw [Bicategory.toNatTrans_conjugateEquiv]
    simpa using conjugateEquiv_extendScalarsId_hom _
  · apply Cat.Hom₂.ext
    rw [Bicategory.toNatTrans_conjugateEquiv]
    simpa [Adjunction.ofCat_comp] using
      conjugateEquiv_extendScalarsComp_hom _ _
  · intros
    apply Bicategory.Adj.hom₂_ext
    simp only [Bicategory.Adj.comp_τl, Bicategory.Adj.whiskerLeft_τl,
      Bicategory.Adj.whiskerRight_τl, Bicategory.Adj.associator_hom_τl,
      Bicategory.Adj.iso₂Mk_hom_τl, Bicategory.Adj.iso₂Mk_inv_τl,
      Bicategory.Adj.eqToHom_τl]
    ext1
    apply extendScalars_assoc'
  · intros
    apply Bicategory.Adj.hom₂_ext
    simp only [Bicategory.Adj.comp_τl, Bicategory.Adj.whiskerRight_τl,
      Bicategory.Adj.leftUnitor_hom_τl, Bicategory.Adj.iso₂Mk_hom_τl,
      Bicategory.Adj.eqToHom_τl]
    ext1
    apply extendScalars_id_comp
  · intros
    apply Bicategory.Adj.hom₂_ext
    simp only [Bicategory.Adj.comp_τl, Bicategory.Adj.whiskerLeft_τl,
      Bicategory.Adj.rightUnitor_hom_τl, Bicategory.Adj.iso₂Mk_hom_τl,
      Bicategory.Adj.eqToHom_τl]
    ext1
    apply extendScalars_comp_id

/-- The left-adjoint projection of the adjunction-valued extension-of-scalars
pseudofunctor is the extension-of-scalars pseudofunctor. -/
lemma leftPseudofunctor_extendRestrictScalarsAdjPseudofunctor :
    Bicategory.Adj.leftPseudofunctor extendRestrictScalarsAdjPseudofunctor.{u} =
      extendScalarsPseudofunctorOpOp.{u} :=
  rfl

end ModuleCat
