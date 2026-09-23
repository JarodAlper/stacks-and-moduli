module

public import StacksAndModuli.API.SheafCohomologyTerminal
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

/-!
# Mayer--Vietoris cohomology over a terminal object

When the fourth object of a Mayer--Vietoris square is terminal, this file
replaces the two occurrences of the cohomology-presheaf value on that object
in Mathlib's six-term exact sequence by global sheaf cohomology.
-/

@[expose] public noncomputable section

universe w v u

namespace CategoryTheory.GrothendieckTopology.MayerVietorisSquare

open Category Opposite Limits Abelian ComposableArrows

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type v)] [HasSheafify J AddCommGrpCat.{v}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

variable (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{v})
  (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (hT : IsTerminal S.X₄)

/-- The six-term Mayer--Vietoris sequence in which the two terms belonging
to the terminal object `S.X₄` are written as global sheaf cohomology. -/
noncomputable abbrev terminalSequence :
    ComposableArrows AddCommGrpCat.{w} 5 :=
  mk₅
    ((Sheaf.HPrimeTerminalIsoH J F n₀ hT).inv ≫ S.toBiprod F n₀)
    (S.fromBiprod F n₀)
    (S.δ F n₀ n₁ h ≫ (Sheaf.HPrimeTerminalIsoH J F n₁ hT).hom)
    ((Sheaf.HPrimeTerminalIsoH J F n₁ hT).inv ≫ S.toBiprod F n₁)
    (S.fromBiprod F n₁)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Mathlib's Mayer--Vietoris sequence is isomorphic to the version whose
terms over the terminal object are global cohomology groups. -/
noncomputable def sequenceIsoTerminal :
    S.sequence F n₀ n₁ h ≅ S.terminalSequence F n₀ n₁ h hT :=
  isoMk₅ (Sheaf.HPrimeTerminalIsoH J F n₀ hT)
    (Iso.refl _) (Iso.refl _) (Sheaf.HPrimeTerminalIsoH J F n₁ hT)
    (Iso.refl _) (Iso.refl _)
    (by dsimp; simp)
    (by
      change S.fromBiprod F n₀ ≫ 𝟙 _ = 𝟙 _ ≫ S.fromBiprod F n₀
      simp)
    (by
      change S.δ F n₀ n₁ h ≫ (Sheaf.HPrimeTerminalIsoH J F n₁ hT).hom =
        𝟙 _ ≫ (S.δ F n₀ n₁ h ≫
          (Sheaf.HPrimeTerminalIsoH J F n₁ hT).hom)
      simp)
    (by
      change S.toBiprod F n₁ ≫ 𝟙 _ =
        (Sheaf.HPrimeTerminalIsoH J F n₁ hT).hom ≫
          ((Sheaf.HPrimeTerminalIsoH J F n₁ hT).inv ≫ S.toBiprod F n₁)
      simp)
    (by
      change S.fromBiprod F n₁ ≫ 𝟙 _ = 𝟙 _ ≫ S.fromBiprod F n₁
      simp)

/-- The Mayer--Vietoris sequence with global cohomology at its terminal
object is exact. -/
lemma terminalSequence_exact :
    (S.terminalSequence F n₀ n₁ h hT).Exact :=
  exact_of_iso (S.sequenceIsoTerminal F n₀ n₁ h hT)
    (S.sequence_exact F n₀ n₁ h)

end CategoryTheory.GrothendieckTopology.MayerVietorisSquare
