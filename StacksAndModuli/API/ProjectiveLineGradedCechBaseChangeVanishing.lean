module

public import StacksAndModuli.API.ProjectiveGradedCechH0CanonicalBaseChange

/-!
# Projective-line Čech vanishing after coefficient change

For a graded module on projective one-space, vanishing of first Čech
cohomology survives arbitrary coefficient change.  Indeed, the first Čech
differential is then surjective, tensor product preserves surjections, and
the Čech complex has no nonzero term above degree one.

Main declaration:

* `GradedModule.subsingleton_cechHgr_one_baseChange_of_subsingleton`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory TensorProduct

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- On projective one-space, vanishing of first Čech cohomology is preserved
by arbitrary coefficient change; no flatness hypothesis is needed. -/
theorem subsingleton_cechHgr_one_baseChange_of_subsingleton
    (M : GradedModule R 1) (d : ℤ)
    [Subsingleton ((M.cechHgr 1).obj d)] :
    Subsingleton (((M.baseChange A).cechHgr 1).obj d) := by
  have hsurj := cechD_zero_surjective_of_subsingleton_cechHgr_one M d
  have hsurjBC : Function.Surjective
      ((cochainBaseChange A (M.cechComplex d)).d 0 1).hom := by
    rw [CochainComplex.cochainBaseChange_d_hom]
    exact LinearMap.baseChange_surjective A hsurj
  have hexBC : CochainComplex.ExactAtSucc
      (cochainBaseChange A (M.cechComplex d)) 0 := by
    rw [CochainComplex.ExactAtSucc,
      LinearMap.range_eq_top.mpr hsurjBC]
    apply le_antisymm
    · intro x _
      rw [CochainComplex.cocyclesSub, LinearMap.mem_ker]
      haveI : Subsingleton
          ((cochainBaseChange A (M.cechComplex d)).X 2) := by
        haveI : Subsingleton ((M.cechComplex d).X 2) := by
          have h := isZero_cechCochain M (show 1 < 2 by omega) d
          rw [ModuleCat.isZero_iff_subsingleton] at h
          exact h
        change Subsingleton (A ⊗[R] ((M.cechComplex d).X 2))
        exact subsingleton_baseChange A
      exact Subsingleton.elim _ _
    · exact le_top
  have hhom : Subsingleton
      ((cochainBaseChange A (M.cechComplex d)).homology 1) :=
    (CochainComplex.subsingleton_homology_succ_iff
      (cochainBaseChange A (M.cechComplex d)) 0).2 hexBC
  let e := (HomologicalComplex.homologyFunctor
    (ModuleCat.{u} A) (ComplexShape.up ℕ) 1).mapIso
      (cechComplexBaseChangeIso A M d)
  exact ⟨fun x y ↦ e.toLinearEquiv.injective (hhom.elim _ _)⟩

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
