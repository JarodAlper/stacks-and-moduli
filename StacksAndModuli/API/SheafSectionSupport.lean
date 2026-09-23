module

public import StacksAndModuli.API.FiniteClosedComplement
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Support of a sheaf section

The support of a global section of a presheaf of abelian groups is the set of points
where its germ is nonzero.  This support is closed.  On a Noetherian one-dimensional
`T₀` space it is finite whenever the section vanishes at a point whose singleton is
dense, such as the generic point of an integral curve.

## Main results

* `TopCat.Presheaf.isClosed_topSectionSupport`: the germ support of a global section is
  closed.
* `TopCat.Presheaf.finite_topSectionSupport_of_dense_singleton`: vanishing at a dense
  point makes that support finite in dimension at most one.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Presheaf

variable {X : TopCat.{u}}

/-- The support of a global section, defined by nonvanishing of its germs. -/
def topSectionSupport (F : X.Presheaf AddCommGrpCat.{u})
    (s : F.obj (op (⊤ : Opens X))) : Set X :=
  {x | F.germ ⊤ x (Set.mem_univ x) s ≠ 0}

/-- The germ support of a global section of a presheaf of abelian groups is closed. -/
theorem isClosed_topSectionSupport (F : X.Presheaf AddCommGrpCat.{u})
    (s : F.obj (op (⊤ : Opens X))) :
    IsClosed (topSectionSupport F s) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  simp only [Set.mem_compl_iff, topSectionSupport, Set.mem_ofPred_eq,
    not_ne_iff] at hx
  have hx' : F.germ ⊤ x (Set.mem_univ x) s =
      F.germ ⊤ x (Set.mem_univ x) 0 := by simpa using hx
  obtain ⟨W, hxW, iU, iV, hW⟩ :=
    F.germ_eq x (Set.mem_univ x) (Set.mem_univ x) s 0 hx'
  refine ⟨W, ?_, W.2, hxW⟩
  intro y hy
  simp only [Set.mem_compl_iff, topSectionSupport, Set.mem_ofPred_eq,
    not_ne_iff]
  calc
    F.germ ⊤ y (Set.mem_univ y) s =
        F.germ W y hy (F.map iU.op s) := by
      symm
      exact F.germ_res_apply iU y hy s
    _ = F.germ W y hy (F.map iV.op 0) := congrArg _ hW
    _ = F.germ ⊤ y (Set.mem_univ y) 0 :=
      F.germ_res_apply iV y hy 0
    _ = 0 := map_zero _

/-- On a Noetherian one-dimensional `T₀` space, a global section vanishing at a
point with dense singleton has finite support. -/
theorem finite_topSectionSupport_of_dense_singleton
    [T0Space X] [NoetherianSpace X]
    (F : X.Presheaf AddCommGrpCat.{u})
    (s : F.obj (op (⊤ : Opens X))) (x : X)
    (hx : Dense ({x} : Set X))
    (hdim : topologicalKrullDim X ≤ 1)
    (hzero : F.germ ⊤ x (Set.mem_univ x) s = 0) :
    (topSectionSupport F s).Finite := by
  apply Set.Finite.of_isClosed_disjoint_dense_of_topologicalKrullDim_le_one
    (isClosed_topSectionSupport F s) hx
  · rw [Set.disjoint_left]
    intro y hy hyx
    rw [Set.mem_singleton_iff] at hyx
    subst y
    exact hy hzero
  · exact hdim

end TopCat.Presheaf
