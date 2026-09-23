module

public import Mathlib.CategoryTheory.Sites.SheafHom

/-!
# Internal Homs of representable presheaves on a slice category

For objects `X`, `Y`, and `T` over a fixed base, this file identifies the value at `T` of
the internal-Hom presheaf between the representables of `X` and `Y` with morphisms between
their pullbacks to `T`.

The only categorical bookkeeping is the standard equivalence between the iterated slice
`(C/S)/T` and `C/T`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Over

set_option backward.defeqAttrib.useBackward true in
/-- The two descriptions of the forgetful functor from the iterated slice `(C/S)/T` to
`C/S` agree up to a natural isomorphism: either pass through `C/T` and compose with
`T.hom`, or forget the final arrow directly. -/
def iteratedSliceForwardMapOpIso {C : Type u} [Category.{v} C] {S : C}
    (T : Over S) :
    T.iteratedSliceForward.op ⋙ (Over.map T.hom).op ≅ (Over.forget T).op :=
  NatIso.ofComponents
    (fun U ↦
      (Over.isoMk
        (f := (Over.forget T).obj U.unop)
        (g := (Over.map T.hom).obj (T.iteratedSliceForward.obj U.unop))
        (Iso.refl _) (by simp)).op)
    (by
      rintro ⟨U⟩ ⟨V⟩ ⟨f⟩
      apply Quiver.Hom.unop_inj
      ext
      simp)

/-- Restriction of a presheaf on `C/S` to the iterated slice `(C/S)/T` agrees, through
the standard iterated-slice equivalence, with restriction to `C/T`. -/
def iteratedSliceRestrictionIso
    {C : Type u} [Category.{v} C] {A : Type w} [Category A] {S : C}
    (T : Over S) (F : (Over S)ᵒᵖ ⥤ A) :
    T.iteratedSliceForward.op ⋙ ((Over.map T.hom).op ⋙ F) ≅ (Over.forget T).op ⋙ F :=
  (Functor.associator _ _ F).symm.trans
    (Functor.isoWhiskerRight (iteratedSliceForwardMapOpIso T) F)

end CategoryTheory.Over

namespace CategoryTheory

/-- The value at `T` of the internal-Hom presheaf between two representables on `C/S`
is canonically the type of morphisms over `T` between their pullbacks to `T`. -/
noncomputable def representablePresheafHomObjEquiv
    {C : Type u} [Category.{v} C] [HasPullbacks C] {S : C}
    (X Y T : Over S) :
    (presheafHom (yoneda.obj X) (yoneda.obj Y)).obj (op T) ≃
      ((Over.pullback T.hom).obj X ⟶ (Over.pullback T.hom).obj Y) := by
  let _ : T.iteratedSliceForward.op.IsEquivalence :=
    Equivalence.isEquivalence_functor T.iteratedSliceEquiv.op
  refine ((Iso.homCongr
    (Over.iteratedSliceRestrictionIso T (yoneda.obj X))
    (Over.iteratedSliceRestrictionIso T (yoneda.obj Y))).symm.trans ?_)
  refine (((Functor.FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft (Over T)ᵒᵖ (Over T.left)ᵒᵖ (Type v)).obj
      T.iteratedSliceForward.op)).homEquiv
        (X := (Over.map T.hom).op ⋙ yoneda.obj X)
        (Y := (Over.map T.hom).op ⋙ yoneda.obj Y)).symm.trans ?_)
  refine (Iso.homCongr
    ((Over.mapPullbackAdj T.hom).compYonedaIso.app X).symm
    ((Over.mapPullbackAdj T.hom).compYonedaIso.app Y).symm).trans ?_
  exact Yoneda.fullyFaithful.homEquiv.symm

end CategoryTheory
