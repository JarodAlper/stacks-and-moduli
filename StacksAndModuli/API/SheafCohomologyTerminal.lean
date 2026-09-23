module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Sheaf cohomology at a terminal object

For a terminal object `T` of a site, the sheafification of the free abelian
presheaf on `yoneda.obj T` is canonically isomorphic to the constant sheaf on
`ULift ℤ`.  Applying the contravariant argument of `Ext` identifies the value
at `T` of Mathlib's cohomology presheaf with global sheaf cohomology in every
degree.  This supplies the terminal-object comparison left as a TODO in
`Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Abelian

universe w' v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{v}]

/-- Sheafification composed with the pointwise free-abelian-group functor is
left adjoint to forgetting an abelian-group-valued sheaf to a presheaf of
types. -/
noncomputable def freeAbelianSheafAdjunction :
    ((Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj
        AddCommGrpCat.free ⋙ presheafToSheaf J AddCommGrpCat.{v}) ⊣
      (sheafToPresheaf J AddCommGrpCat.{v} ⋙
        (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{v} (Type v)).obj
          (forget AddCommGrpCat.{v})) :=
  (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).comp
    (sheafificationAdjunction J AddCommGrpCat.{v})

/-- The underlying type of the sections of an abelian sheaf at `T`. -/
abbrev sectionsUnderlyingFunctor (T : C) :
    Sheaf J AddCommGrpCat.{v} ⥤ Type v :=
  (sheafSections J AddCommGrpCat.{v}).obj (Opposite.op T) ⋙
    forget AddCommGrpCat.{v}

/-- The sheafification of the free abelian presheaf on `yoneda.obj T`
corepresents the underlying set of sections at `T`. -/
noncomputable def freeAbelianYonedaCorepresentableBy (T : C) :
    (sectionsUnderlyingFunctor J T).CorepresentableBy
      ((presheafToSheaf J AddCommGrpCat.{v}).obj
        (yoneda.obj T ⋙ AddCommGrpCat.free)) where
  homEquiv :=
    ((freeAbelianSheafAdjunction J).homEquiv _ _).trans yonedaEquiv
  homEquiv_comp g f := by
    rw [Equiv.trans_apply, Equiv.trans_apply,
      Adjunction.homEquiv_naturality_right, yonedaEquiv_comp]
    rfl

/-- At a terminal object, the constant sheaf on `ULift ℤ` corepresents the
underlying set of sections. -/
noncomputable def constantSheafCorepresentableBy {T : C}
    (hT : IsTerminal T) :
    (sectionsUnderlyingFunctor J T).CorepresentableBy
      ((constantSheaf J AddCommGrpCat.{v}).obj
        (AddCommGrpCat.of (ULift ℤ))) where
  homEquiv :=
    ((constantSheafAdj J AddCommGrpCat.{v} hT).homEquiv _ _).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _).toEquiv
  homEquiv_comp g f := by
    rw [Equiv.trans_apply, Equiv.trans_apply,
      Adjunction.homEquiv_naturality_right]
    rfl

/-- At a terminal object, the sheafification of the free abelian presheaf on
the representable presheaf is canonically the constant sheaf on `ULift ℤ`. -/
noncomputable def freeAbelianYonedaIsoConstantSheaf {T : C}
    (hT : IsTerminal T) :
    (presheafToSheaf J AddCommGrpCat.{v}).obj
        (yoneda.obj T ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat.{v}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  (freeAbelianYonedaCorepresentableBy J T).uniqueUpToIso
    (constantSheafCorepresentableBy J hT)

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{v})]

/-- The natural isomorphism in the coefficient sheaf underlying the
terminal-object comparison between the cohomology presheaf and global sheaf
cohomology. -/
noncomputable def HPrimeTerminalNatIsoH (n : ℕ) {T : C}
    (hT : IsTerminal T) :
    (Abelian.extFunctor n).obj
        (Opposite.op ((presheafToSheaf J AddCommGrpCat.{v}).obj
          (yoneda.obj T ⋙ AddCommGrpCat.free))) ≅
      (Abelian.extFunctor n).obj
        (Opposite.op ((constantSheaf J AddCommGrpCat.{v}).obj
          (AddCommGrpCat.of (ULift ℤ)))) :=
  (Abelian.extFunctor n).mapIso
    (freeAbelianYonedaIsoConstantSheaf J hT).symm.op

/-- The value at a terminal object of the degree-`n` cohomology presheaf is
isomorphic, as an abelian group, to global degree-`n` sheaf cohomology. -/
noncomputable def HPrimeTerminalIsoH
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {T : C}
    (hT : IsTerminal T) :
    F.H' n T ≅ AddCommGrpCat.of (F.H n) :=
  (HPrimeTerminalNatIsoH J n hT).app F

/-- The additive equivalence between the value at a terminal object of the
cohomology presheaf and global sheaf cohomology. -/
noncomputable def HPrimeTerminalEquivH
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {T : C}
    (hT : IsTerminal T) :
    F.H' n T ≃+ F.H n :=
  (HPrimeTerminalIsoH J F n hT).addCommGroupIsoToAddEquiv

/-- Vanishing of the cohomology presheaf at a terminal object is equivalent
to vanishing of global sheaf cohomology. -/
theorem subsingleton_HPrime_terminal_iff
    (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {T : C}
    (hT : IsTerminal T) :
    Subsingleton (F.H' n T) ↔ Subsingleton (F.H n) :=
  (HPrimeTerminalEquivH J F n hT).toEquiv.subsingleton_congr

end CategoryTheory.Sheaf
