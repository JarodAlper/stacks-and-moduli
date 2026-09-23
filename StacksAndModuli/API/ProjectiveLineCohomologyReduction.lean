module

public import StacksAndModuli.API.ProjectiveGradedCohomology
public import StacksAndModuli.API.ProjectiveLineStandardCoverCohomology
public import StacksAndModuli.API.SheafCohomologyModule
public import StacksAndModuli.API.ProjectiveSpaceOverSpecComparison
public import StacksAndModuli.API.SheafCohomologySchemeIso

/-!
# Reducing structure-sheaf cohomology of the projective line

The packaged graded cohomology theory of `ProjectiveGradedCohomology` already contains the
standard computation `Hⁱ(ℙⁿ, O(d))`. This file isolates the remaining comparison with
Mathlib's derived sheaf cohomology and records the consequences of that comparison.

There are two independent routes. A comparison in degree zero of the twist transfers the
packaged computation. Alternatively, the standard two-chart Mayer--Vietoris calculation
proves `H¹(ℙ¹, O) = 0` from exactly the two local `H¹`-vanishing instances. The latter
route leaves only affine quasicoherent acyclicity, rather than a global
Čech-to-derived-cohomology comparison.

Main declarations:

* `AlgebraicGeometry.ProjectiveSpace.Cohomology.SchemeStructureComparison`;
* `AlgebraicGeometry.ProjectiveSpace.Cohomology.PolynomialProjStructureComparison`;
* `AlgebraicGeometry.ProjectiveSpace.Cohomology.
    projectiveLine_H_one_subsingleton_of_chart_H_one`;
* `AlgebraicGeometry.ProjectiveSpace.Cohomology.SchemeStructureComparison.subsingleton_H`;
* `AlgebraicGeometry.ProjectiveSpace.Cohomology.SchemeStructureComparison.
    projectiveLine_h_one_eq_zero_canonical`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

variable {k : Type u} [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The packaged graded cohomology of the structure sheaf on projective space vanishes in
every positive degree. This is the degree-zero-twist specialization of the standard
`Hⁱ(ℙⁿ, O(d))` computation stored in `Cohomology`. -/
theorem subsingleton_H_structureModule_zero (C : Cohomology k) (n i : ℕ) (hi : 1 ≤ i) :
    Subsingleton ((C.Hgr (GradedModule.structureModule k n) i).obj 0) :=
  C.subsingleton_Hgr_structureModule i 0 hi (Or.inr (by omega))

/-- In the packaged graded model, the first cohomology of the projective-line structure
sheaf has dimension zero. -/
theorem h_one_structureModule_projectiveLine_eq_zero (C : Cohomology k) :
    C.h (GradedModule.structureModule k 1) 1 0 = 0 :=
  C.h_eq_zero_of_subsingleton (C.subsingleton_H_structureModule_zero 1 1 (by omega))

/-- A comparison in cohomological degree `i` between the packaged graded cohomology of `O`
and Mathlib's derived sheaf cohomology of the actual relative projective space over
`Spec k`.

Only one degree of the structure sheaf and its zero twist is included. This is enough for
the genus of the projective line, while avoiding the substantially stronger comparison for
arbitrary cohomological degrees, quasicoherent sheaves, and twists. -/
abbrev SchemeStructureComparison (C : Cohomology k) (n i : ℕ) :=
    Scheme.Modules.H
        (Scheme.structureModule
          (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of k)))) i ≃+
      (C.Hgr (GradedModule.structureModule k n) i).obj 0

/-- The corresponding comparison stated directly on the intrinsic polynomial `Proj`.
This is the natural target of a future Čech-to-derived-cohomology theorem; the canonical
scheme isomorphism transfers it to relative projective space. -/
abbrev PolynomialProjStructureComparison (C : Cohomology k) (n i : ℕ) :=
  Scheme.Modules.H
      (Scheme.structureModule
        (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k))) i ≃+
    (C.Hgr (GradedModule.structureModule k n) i).obj 0

/-- Structure-sheaf `H¹` of the relative projective line vanishes as soon as it vanishes
on the two standard affine charts. Surjectivity of the overlap difference map is proved
by the polynomial/Laurent-polynomial calculation. -/
theorem projectiveLine_H_one_subsingleton_of_chart_H_one
    [Subsingleton (Scheme.Modules.H
      (Scheme.structureModule (Proj.projectiveLineChartZero k).toScheme) 1)]
    [Subsingleton (Scheme.Modules.H
      (Scheme.structureModule (Proj.projectiveLineChartOne k).toScheme) 1)] :
    Subsingleton
      (Scheme.Modules.H
        (Scheme.structureModule
          (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))) 1) := by
  let _ : Subsingleton
      (Scheme.Modules.H
        (Scheme.structureModule (Proj.projectiveLine k)) 1) :=
    Proj.projectiveLine_H_one_subsingleton_of_chart_H_one k
  exact (Scheme.structureCohomologyAddEquivOfIso
    (ProjectiveSpace.projectiveSpaceOverSpecIso 1 k) 1).toEquiv.subsingleton

/-- With its canonical structure morphism, the two standard-chart local vanishings imply
`h¹(ℙ¹_k, O) = 0`. -/
theorem projectiveLine_h_one_eq_zero_canonical_of_chart_H_one
    [Subsingleton (Scheme.Modules.H
      (Scheme.structureModule (Proj.projectiveLineChartZero k).toScheme) 1)]
    [Subsingleton (Scheme.Modules.H
      (Scheme.structureModule (Proj.projectiveLineChartOne k).toScheme) 1)] :
    letI : Scheme.Over
      (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))
      (Spec (CommRingCat.of k)) :=
        ⟨Scheme.projectiveSpaceOverπ 1 (Spec (CommRingCat.of k))⟩
    Scheme.Modules.h k
      (Scheme.structureModule
        (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))) 1 = 0 := by
  let _ : Scheme.Over
      (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))
      (Spec (CommRingCat.of k)) :=
    ⟨Scheme.projectiveSpaceOverπ 1 (Spec (CommRingCat.of k))⟩
  exact Scheme.Modules.h_eq_zero_of_subsingleton k _ 1
    projectiveLine_H_one_subsingleton_of_chart_H_one

namespace SchemeStructureComparison

variable {C : Cohomology k} {n i : ℕ}

/-- Transfer a structure-sheaf comparison on polynomial `Proj` across the canonical
isomorphism from relative projective space over `Spec k`. -/
noncomputable def ofPolynomialProj
    (E : PolynomialProjStructureComparison C n i) :
    SchemeStructureComparison C n i :=
  (Scheme.structureCohomologyAddEquivOfIso
    (ProjectiveSpace.projectiveSpaceOverSpecIso n k) i).trans E

/-- A graded-to-derived comparison transfers the standard vanishing of
`Hⁱ(ℙⁿ_k, O)` to the actual scheme for every positive `i`. -/
theorem subsingleton_H (E : SchemeStructureComparison C n i) (hi : 1 ≤ i) :
    Subsingleton
      (Scheme.Modules.H
        (Scheme.structureModule
          (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of k)))) i) := by
  let _ : Subsingleton ((C.Hgr (GradedModule.structureModule k n) i).obj 0) :=
    C.subsingleton_H_structureModule_zero n i hi
  exact E.toEquiv.subsingleton

/-- A graded-to-derived comparison makes the scheme-theoretic structure-sheaf `hⁱ`
vanish in every positive degree, for any chosen `k`-scheme structure on projective space. -/
theorem h_structureModule_eq_zero
    (E : SchemeStructureComparison C n i) (hi : 1 ≤ i)
    [Scheme.Over
      (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of k)))
      (Spec (CommRingCat.of k))] :
    Scheme.Modules.h k
      (Scheme.structureModule
        (Scheme.projectiveSpaceOver n (Spec (CommRingCat.of k)))) i = 0 :=
  Scheme.Modules.h_eq_zero_of_subsingleton k _ i (E.subsingleton_H hi)

/-- A graded-to-derived comparison proves `H¹(ℙ¹_k, O) = 0`. -/
theorem projectiveLine_H_one_subsingleton
    (E : SchemeStructureComparison C 1 1) :
    Subsingleton
      (Scheme.Modules.H
        (Scheme.structureModule
          (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))) 1) :=
  E.subsingleton_H (by omega)

/-- A graded-to-derived comparison proves that the structure-sheaf `h¹` of `ℙ¹_k` is
zero, for any chosen `k`-scheme structure on the displayed projective line. -/
theorem projectiveLine_h_one_eq_zero
    (E : SchemeStructureComparison C 1 1)
    [Scheme.Over
      (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))
      (Spec (CommRingCat.of k))] :
    Scheme.Modules.h k
      (Scheme.structureModule
        (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))) 1 = 0 :=
  E.h_structureModule_eq_zero (by omega)

/-- With its canonical structure morphism, a graded-to-derived comparison proves that
`h¹(ℙ¹_k, O) = 0`. -/
theorem projectiveLine_h_one_eq_zero_canonical
    (E : SchemeStructureComparison C 1 1) :
    letI : Scheme.Over
      (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))
      (Spec (CommRingCat.of k)) :=
        ⟨Scheme.projectiveSpaceOverπ 1 (Spec (CommRingCat.of k))⟩
    Scheme.Modules.h k
      (Scheme.structureModule
        (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))) 1 = 0 := by
  let _ : Scheme.Over
      (Scheme.projectiveSpaceOver 1 (Spec (CommRingCat.of k)))
      (Spec (CommRingCat.of k)) :=
    ⟨Scheme.projectiveSpaceOverπ 1 (Spec (CommRingCat.of k))⟩
  exact E.projectiveLine_h_one_eq_zero

end SchemeStructureComparison

end AlgebraicGeometry.ProjectiveSpace.Cohomology

end
