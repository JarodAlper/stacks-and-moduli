module

public import StacksAndModuli.API.ProjectiveLineGradedKoszulBaseChange
public import StacksAndModuli.API.ProjectiveLineGradedCechBaseChangeVanishing
public import StacksAndModuli.API.ProjectiveLineGradedKoszulSurjectivity

/-!
# Finite-projective tails for zeroth projective-line Cech cohomology

The two-step Koszul recurrence propagates finite projectivity of zeroth graded Cech
cohomology from two adjacent degrees.  Vanishing of first Cech cohomology supplies the
surjectivity needed both before and after passage to every maximal residue field, while the
canonical Cech base-change maps supply the fibre comparisons.

Main declaration:

* `GradedModule.finite_projective_and_canonicalBaseChange_cechHgr_zero_tail`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {R : Type u} [CommRing R]

/-- Vanishing of first graded Cech cohomology along a projective-line tail propagates
finite projectivity of zeroth Cech cohomology and bijectivity of its canonical comparison
with every maximal residue field from the first two degrees to the whole tail. -/
theorem finite_projective_and_canonicalBaseChange_cechHgr_zero_tail
    (M : GradedModule R 1) (d : ℤ)
    (hvan : ∀ t, Subsingleton
      ((M.cechHgr 1).obj (lineKoszulDegree d t)))
    (hfin0 : Module.Finite R ((M.cechHgr 0).obj d))
    (hproj0 : Module.Projective R ((M.cechHgr 0).obj d))
    (hfin1 : Module.Finite R ((M.cechHgr 0).obj (d + 1)))
    (hproj1 : Module.Projective R ((M.cechHgr 0).obj (d + 1)))
    (hβ0 : ∀ (I : Ideal R) [I.IsMaximal], Function.Bijective
      (cechHgrZeroCanonicalBaseChangeHom (A := I.ResidueField) M d))
    (hβ1 : ∀ (I : Ideal R) [I.IsMaximal], Function.Bijective
      (cechHgrZeroCanonicalBaseChangeHom (A := I.ResidueField) M (d + 1))) :
    ∀ t,
      (Module.Finite R
          ((M.cechHgr 0).obj (lineKoszulDegree d t)) ∧
        Module.Projective R
          ((M.cechHgr 0).obj (lineKoszulDegree d t))) ∧
      ∀ (I : Ideal R) [I.IsMaximal], Function.Bijective
        (cechHgrZeroCanonicalBaseChangeHom
          (A := I.ResidueField) M (lineKoszulDegree d t)) := by
  apply finite_projective_and_fibreComparison_of_lineKoszul_baseChange
    (M.cechHgr 0) d
    (fun t ↦ exact_lineKoszulF_lineKoszulG_cechHgr
      M 0 (lineKoszulDegree d t))
    (fun t ↦ by
      letI := hvan t
      exact lineKoszulG_cechHgr_zero_surjective_of_subsingleton_one
        M (lineKoszulDegree d t))
    (fun I _ ↦ (M.baseChange I.ResidueField).cechHgr 0)
    (fun I _ ↦ cechHgrZeroCanonicalBaseChangeMap
      (A := I.ResidueField) M)
    (fun I _ t ↦ exact_lineKoszulF_lineKoszulG_cechHgr
      (M.baseChange I.ResidueField) 0 (lineKoszulDegree d t))
    (fun I _ t ↦ by
      letI := hvan t
      letI := subsingleton_cechHgr_one_baseChange_of_subsingleton
        (A := I.ResidueField) M (lineKoszulDegree d t)
      exact lineKoszulG_cechHgr_zero_surjective_of_subsingleton_one
        (M.baseChange I.ResidueField) (lineKoszulDegree d t))
    (fun I _ t ↦ injective_lineKoszulF_cechHgr_zero
      (M.baseChange I.ResidueField) (lineKoszulDegree d t))
    hfin0 hproj0 hfin1 hproj1
    (fun I _ ↦ hβ0 I)
    (fun I _ ↦ hβ1 I)

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
