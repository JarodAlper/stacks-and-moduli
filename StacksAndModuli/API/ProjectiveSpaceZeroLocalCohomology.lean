module

public import StacksAndModuli.API.SheafCohomologyGlobalPoint
public import StacksAndModuli.API.ProjectiveSpaceZeroCohomology

/-!
# Cohomology of zero-dimensional projective space over a local ring

The closed point of the spectrum of a local ring belongs to no proper open.
The same is therefore true of its inverse image under the homeomorphism
`P⁰_R ≃ Spec R`.  The global-point cohomology API then gives vanishing of
all positive cohomology groups of all abelian sheaves on `P⁰_R`, and hence
scheme-level Serre vanishing over every commutative local ring.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry ProjectiveSpectrum HomogeneousLocalization

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The canonical homeomorphism between relative `P⁰` over a ring and its prime
spectrum. -/
noncomputable def projectiveSpaceOverZeroHomeomorphPrimeSpectrum
    (R : Type u) [CommRing R] :
    Scheme.projectiveSpaceOver 0 (Spec (.of R)) ≃ₜ PrimeSpectrum R := by
  let G := MvPolynomial.homogeneousSubmodule (Fin 1) R
  let i : Fin 1 := 0
  let U := Proj.polynomialStandardOpen 0 R i
  have hU : U = ⊤ := by
    apply top_unique
    rw [← Proj.iSup_polynomialStandardOpen_eq_top 0 R]
    refine iSup_le fun j ↦ ?_
    have hji : j = i := by
      apply Fin.ext
      omega
    rw [hji]
  let eTop : U.toScheme ≅ Proj G :=
    (Proj G).isoOfEq hU ≪≫ Scheme.topIso (Proj G)
  let eBasic : U.toScheme ≅ Spec (.of (Away G (MvPolynomial.X i))) :=
    Proj.basicOpenIsoSpec G (MvPolynomial.X i)
      (MvPolynomial.X_mem_homogeneousSubmodule_one 0 R i) Nat.one_pos
  letI : IsEmpty {j : Fin 1 // j ≠ i} :=
    ⟨fun j ↦ j.2 (Subsingleton.elim j.1 i)⟩
  let eRing : Away G (MvPolynomial.X i) ≃+* R :=
    (Proj.projectiveChartPolynomialEquivAway (Fin 1) i R).symm.trans
      (MvPolynomial.isEmptyRingEquiv R {j : Fin 1 // j ≠ i})
  exact (Proj.polynomialProjOverSpecIso (Fin 1) R).hom.homeomorph |>.trans
    (eTop.inv.homeomorph.trans
      (eBasic.hom.homeomorph.trans
        (PrimeSpectrum.homeomorphOfRingEquiv eRing)))

/-- The point of relative `P⁰` corresponding to the closed point of the
spectrum of a local ring. -/
noncomputable def projectiveSpaceOverZeroClosedPoint
    (R : Type u) [CommRing R] [IsLocalRing R] :
    Scheme.projectiveSpaceOver 0 (Spec (.of R)) :=
  (projectiveSpaceOverZeroHomeomorphPrimeSpectrum R).symm
    (IsLocalRing.closedPoint R)

/-- The closed point of relative `P⁰` over a local ring is a global point: its
only open neighbourhood is the whole projective space. -/
theorem projectiveSpaceOverZeroClosedPoint_isGlobalPoint
    (R : Type u) [CommRing R] [IsLocalRing R] :
    TopologicalSpace.IsGlobalPoint (projectiveSpaceOverZeroClosedPoint R) := by
  let e := projectiveSpaceOverZeroHomeomorphPrimeSpectrum R
  have hclosed : TopologicalSpace.IsGlobalPoint
      (IsLocalRing.closedPoint R : PrimeSpectrum R) :=
    fun (y : PrimeSpectrum R) ↦
      IsLocalRing.specializes_closedPoint (R := R) y
  exact hclosed.homeomorph e.symm

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

/-- Every positive cohomology group of every abelian sheaf on the spectrum of
a local ring vanishes. -/
theorem spec_H_succ_subsingleton_of_isLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R]
    (F : TopCat.Sheaf AddCommGrpCat.{u} (Spec (.of R))) (n : ℕ) :
    Subsingleton (F.H (n + 1)) := by
  let x : Spec (.of R) := IsLocalRing.closedPoint R
  have hx : TopologicalSpace.IsGlobalPoint x :=
    fun (y : Spec (.of R)) ↦
      IsLocalRing.specializes_closedPoint (R := R) y
  exact CategoryTheory.Sheaf.subsingleton_H_succ_of_isGlobalPoint x hx F n

/-- Every positive cohomology group of every abelian sheaf on relative `P⁰`
over a local ring vanishes. -/
theorem projectiveSpaceOverZero_H_succ_subsingleton_of_isLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R]
    (F : TopCat.Sheaf AddCommGrpCat.{u}
      (projectiveSpaceOver 0 (Spec (.of R)))) (n : ℕ) :
    Subsingleton (F.H (n + 1)) :=
  CategoryTheory.Sheaf.subsingleton_H_succ_of_isGlobalPoint
    (ProjectiveSpace.projectiveSpaceOverZeroClosedPoint R)
    (ProjectiveSpace.projectiveSpaceOverZeroClosedPoint_isGlobalPoint R) F n

/-- Every positive cohomology group of every abelian sheaf on relative `P⁰`
over a local ring vanishes, with the degree supplied as an inequality. -/
theorem projectiveSpaceOverZero_H_subsingleton_of_isLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R]
    (F : TopCat.Sheaf AddCommGrpCat.{u}
      (projectiveSpaceOver 0 (Spec (.of R))))
    (i : ℕ) (hi : 1 ≤ i) : Subsingleton (F.H i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hi
  simpa [Nat.add_comm] using
    projectiveSpaceOverZero_H_succ_subsingleton_of_isLocalRing R F n

/-- Scheme-level Serre vanishing holds on relative `P⁰` over every
commutative local ring.  In fact, every positive cohomology group vanishes in
every twist degree, without finiteness hypotheses on the sheaf. -/
theorem projectiveSpaceHasSerreVanishing_zero_spec_of_isLocalRing
    (R : Type u) [CommRing R] [IsLocalRing R] :
    ProjectiveSpaceHasSerreVanishing 0 (Spec (.of R)) := by
  intro M _ _ i hi
  filter_upwards [] with d
  exact projectiveSpaceOverZero_H_subsingleton_of_isLocalRing R _ i hi

end AlgebraicGeometry.Scheme
