module

public import StacksAndModuli.API.ProjGammaStarChart

/-!
# Torsion-freeness of global sections is local

Two small facts about sections of a sheaf of modules on a scheme over an affine base:

* a section vanishing on every open of a cover vanishes (the sheaf axiom, in the form
  `TopCat.Sheaf.eq_of_locally_eq'`);
* consequently, if the sections over each open of a cover are torsion-free over the base ring,
  so are the global sections.

The second is what turns flatness of a sheaf over its base — a condition stated on *affine*
opens (`Scheme.Modules.FlatOver`) — into degreewise flatness of `Γ_*`, whose pieces are
sections over the non-affine `⊤`.  Degreewise flatness is
`AlgebraicGeometry.ProjectiveSpace.RelativeCohomology.cech`'s `IsFlat`, one of the two
hypotheses of
`SchemeGlobalSectionsComparison.toHasEventualFiniteProjectiveGlobalSectionsBaseChange`.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.eq_zero_of_res_eq_zero`;
* `AlgebraicGeometry.Scheme.Modules.isTorsionFree_globalSections_of_cover`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- **A section vanishing on an open cover vanishes.** -/
theorem eq_zero_of_res_eq_zero {X : Scheme.{u}} (M : X.Modules)
    {ι : Type*} (U : ι → X.Opens) (hcover : (⊤ : X.Opens) ≤ iSup U)
    (s : Γ(M, ⊤))
    (h : ∀ i, M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op s = 0) :
    s = 0 := by
  refine TopCat.Sheaf.eq_of_locally_eq'
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) U ⊤
    (fun i => homOfLE (le_top : U i ≤ ⊤)) hcover s 0 fun i => ?_
  rw [map_zero]
  exact h i

/-- **Torsion-freeness of global sections is local.**  If the sections of `M` on each open of a
cover are torsion-free over the base ring, so are the global sections. -/
theorem isTorsionFree_globalSections_of_cover {X : Scheme.{u}} {R : CommRingCat.{u}}
    (π : X ⟶ Spec R) (M : X.Modules) {ι : Type*} (U : ι → X.Opens)
    (hcover : (⊤ : X.Opens) ≤ iSup U)
    (h : ∀ i, letI := openSectionsModuleOver π M (U i);
      Module.IsTorsionFree R Γ(M, U i)) :
    letI := globalSectionsModule π M
    Module.IsTorsionFree R Γ(M, ⊤) := by
  letI := globalSectionsModule π M
  refine ⟨fun r hr => ?_⟩
  have hzero : ∀ s : Γ(M, ⊤), r • s = 0 → s = 0 := by
    intro s hs
    refine eq_zero_of_res_eq_zero M U hcover s fun i => ?_
    letI := openSectionsModuleOver π M (U i)
    refine (h i).isSMulRegular hr
      (a₁ := M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op s) (a₂ := 0) ?_
    change r • (M.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op s) = r • (0 : Γ(M, U i))
    rw [smul_zero]
    have hlin := (resFromTopLinearMap π M (U i)).map_smul r s
    rw [hs, map_zero] at hlin
    exact hlin.symm
  intro a b hab
  have hab' : r • a = r • b := hab
  have h1 : r • (a - b) = 0 := by rw [smul_sub, hab', sub_self]
  exact sub_eq_zero.mp (hzero _ h1)

end AlgebraicGeometry.Scheme.Modules

end

end
