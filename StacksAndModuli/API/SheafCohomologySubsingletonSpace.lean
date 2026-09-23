module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# Sheaf cohomology on a subsingleton space

On a nonempty subsingleton topological space, evaluation on the top open preserves
epimorphisms: a local lift at the unique point is already a global lift.  Consequently,
the constant sheaf on `ULift ℤ` is projective and every sheaf of abelian groups has
vanishing positive cohomology.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace TopCat.Sheaf

/-- Evaluation on the top open of a nonempty subsingleton space preserves epimorphisms. -/
noncomputable instance sheafSectionsTop_preservesEpimorphisms_of_subsingleton
    {X : TopCat.{u}} [Nonempty X] [Subsingleton X] :
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : Opens X))).PreservesEpimorphisms where
  preserves := by
    intro F G f hf
    rw [AddCommGrpCat.epi_iff_surjective]
    intro t
    have hloc : TopCat.Presheaf.IsLocallySurjective f.hom :=
      (TopCat.Sheaf.isLocallySurjective_iff_epi f).2 hf
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨V, _, ⟨s, hs⟩, hxV⟩ :=
      (TopCat.Presheaf.isLocallySurjective_iff f.hom).1 hloc ⊤ t x (by simp)
    have hV : V = ⊤ := by
      apply le_antisymm le_top
      intro y hy
      simpa only [Subsingleton.elim y x] using hxV
    subst V
    exact ⟨s, by simpa using hs⟩

end TopCat.Sheaf

namespace CategoryTheory.Sheaf

/-- Every positive sheaf-cohomology group on a nonempty subsingleton space is zero. -/
theorem subsingleton_H_succ_of_nonempty_subsingleton
    {X : TopCat.{u}} [Nonempty X] [Subsingleton X]
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Subsingleton (F.H (n + 1)) := by
  let P := AddCommGrpCat.of (ULift.{u} ℤ)
  letI : Projective P := by
    let M := ModuleCat.of ℤ (ULift.{u} ℤ)
    letI : Projective M := inferInstance
    change Projective ((forget₂ (ModuleCat ℤ) AddCommGrpCat).obj M)
    infer_instance
  let J := Opens.grothendieckTopology X
  let adj := constantSheafAdj J AddCommGrpCat Limits.isTerminalTop
  letI : Projective ((constantSheaf J AddCommGrpCat).obj P) :=
    adj.map_projective P (by infer_instance)
  change Subsingleton
    (Abelian.Ext ((constantSheaf J AddCommGrpCat).obj P) F (n + 1))
  exact Abelian.Ext.subsingleton_of_projective _ F n

end CategoryTheory.Sheaf
