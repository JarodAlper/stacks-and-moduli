module

public import StacksAndModuli.API.SheafCohomologyOpenExact
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

/-!
# Mayer--Vietoris cohomology on slice sites

This file rewrites every local-cohomology term in Mathlib's six-term
Mayer--Vietoris sequence as global sheaf cohomology on the corresponding slice
site.  The maps are obtained by conjugating Mathlib's maps with the canonical
open-object cohomology equivalences.
-/

@[expose] public noncomputable section

universe u

namespace CategoryTheory.GrothendieckTopology.MayerVietorisSquare

open Category Opposite Limits Abelian ComposableArrows

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type u)] [HasSheafify J AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{u})
  (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)

/-- The canonical isomorphism from local cohomology at an object of the site
to global cohomology of the restricted sheaf on its slice site. -/
noncomputable abbrev openCohomologyIso (X : C) (n : ℕ) :
    F.H' n X ≅ AddCommGrpCat.of ((F.over X).H n) :=
  (Sheaf.HPrimeOpenEquivH J F X n).toAddCommGrpIso

/-- The six-term Mayer--Vietoris sequence with every local-cohomology term
written as global cohomology on the corresponding slice site. -/
noncomputable abbrev openSequence :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  mk₅
    ((openCohomologyIso F S.X₄ n₀).inv ≫ S.toBiprod F n₀ ≫
      (biprod.mapIso (openCohomologyIso F S.X₂ n₀)
        (openCohomologyIso F S.X₃ n₀)).hom)
    ((biprod.mapIso (openCohomologyIso F S.X₂ n₀)
        (openCohomologyIso F S.X₃ n₀)).inv ≫ S.fromBiprod F n₀ ≫
      (openCohomologyIso F S.X₁ n₀).hom)
    ((openCohomologyIso F S.X₁ n₀).inv ≫ S.δ F n₀ n₁ h ≫
      (openCohomologyIso F S.X₄ n₁).hom)
    ((openCohomologyIso F S.X₄ n₁).inv ≫ S.toBiprod F n₁ ≫
      (biprod.mapIso (openCohomologyIso F S.X₂ n₁)
        (openCohomologyIso F S.X₃ n₁)).hom)
    ((biprod.mapIso (openCohomologyIso F S.X₂ n₁)
        (openCohomologyIso F S.X₃ n₁)).inv ≫ S.fromBiprod F n₁ ≫
      (openCohomologyIso F S.X₁ n₁).hom)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Mathlib's Mayer--Vietoris sequence is isomorphic to the version whose six
objects are global cohomology groups on slice sites. -/
noncomputable def sequenceIsoOpen :
    S.sequence F n₀ n₁ h ≅ S.openSequence F n₀ n₁ h :=
  isoMk₅ (openCohomologyIso F S.X₄ n₀)
    (biprod.mapIso (openCohomologyIso F S.X₂ n₀)
      (openCohomologyIso F S.X₃ n₀))
    (openCohomologyIso F S.X₁ n₀)
    (openCohomologyIso F S.X₄ n₁)
    (biprod.mapIso (openCohomologyIso F S.X₂ n₁)
      (openCohomologyIso F S.X₃ n₁))
    (openCohomologyIso F S.X₁ n₁)
    (by
      change S.toBiprod F n₀ ≫
          (biprod.mapIso (openCohomologyIso F S.X₂ n₀)
            (openCohomologyIso F S.X₃ n₀)).hom =
        (openCohomologyIso F S.X₄ n₀).hom ≫
          ((openCohomologyIso F S.X₄ n₀).inv ≫
            S.toBiprod F n₀ ≫
            (biprod.mapIso (openCohomologyIso F S.X₂ n₀)
              (openCohomologyIso F S.X₃ n₀)).hom)
      simp only [Iso.hom_inv_id_assoc])
    (by
      change S.fromBiprod F n₀ ≫ (openCohomologyIso F S.X₁ n₀).hom =
        (biprod.mapIso (openCohomologyIso F S.X₂ n₀)
            (openCohomologyIso F S.X₃ n₀)).hom ≫
          ((biprod.mapIso (openCohomologyIso F S.X₂ n₀)
              (openCohomologyIso F S.X₃ n₀)).inv ≫
            S.fromBiprod F n₀ ≫ (openCohomologyIso F S.X₁ n₀).hom)
      simp only [Iso.hom_inv_id_assoc])
    (by
      change S.δ F n₀ n₁ h ≫ (openCohomologyIso F S.X₄ n₁).hom =
        (openCohomologyIso F S.X₁ n₀).hom ≫
          ((openCohomologyIso F S.X₁ n₀).inv ≫ S.δ F n₀ n₁ h ≫
            (openCohomologyIso F S.X₄ n₁).hom)
      simp only [Iso.hom_inv_id_assoc])
    (by
      change S.toBiprod F n₁ ≫
          (biprod.mapIso (openCohomologyIso F S.X₂ n₁)
            (openCohomologyIso F S.X₃ n₁)).hom =
        (openCohomologyIso F S.X₄ n₁).hom ≫
          ((openCohomologyIso F S.X₄ n₁).inv ≫
            S.toBiprod F n₁ ≫
            (biprod.mapIso (openCohomologyIso F S.X₂ n₁)
              (openCohomologyIso F S.X₃ n₁)).hom)
      simp only [Iso.hom_inv_id_assoc])
    (by
      change S.fromBiprod F n₁ ≫ (openCohomologyIso F S.X₁ n₁).hom =
        (biprod.mapIso (openCohomologyIso F S.X₂ n₁)
            (openCohomologyIso F S.X₃ n₁)).hom ≫
          ((biprod.mapIso (openCohomologyIso F S.X₂ n₁)
              (openCohomologyIso F S.X₃ n₁)).inv ≫
            S.fromBiprod F n₁ ≫ (openCohomologyIso F S.X₁ n₁).hom)
      simp only [Iso.hom_inv_id_assoc])

/-- The Mayer--Vietoris sequence written entirely in terms of global
cohomology on slice sites is exact. -/
lemma openSequence_exact :
    (S.openSequence F n₀ n₁ h).Exact :=
  exact_of_iso (S.sequenceIsoOpen F n₀ n₁ h)
    (S.sequence_exact F n₀ n₁ h)

end CategoryTheory.GrothendieckTopology.MayerVietorisSquare
