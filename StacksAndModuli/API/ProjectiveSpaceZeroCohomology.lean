module

public import StacksAndModuli.API.SheafCohomologySubsingletonSpace
public import StacksAndModuli.API.ProjectiveStandardCoverBaseChange
public import StacksAndModuli.API.ProjectiveSpaceSerreVanishing

/-!
# Cohomology of zero-dimensional projective space

The sole standard chart of `ℙ⁰_R` is the whole space and has coordinate ring `R`, so
its underlying space is the prime spectrum of `R`.  When that spectrum is nonempty and
subsingleton—in particular, when `R` is a field—the general subsingleton-space
cohomology theorem proves pointwise vanishing of every positive cohomology group, for
every sheaf of abelian groups on `ℙ⁰_R`.  In particular, the scheme-level
Serre-vanishing predicate holds for `ℙ⁰_K` over a field.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry ProjectiveSpectrum HomogeneousLocalization

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The underlying set of relative `ℙ⁰` over a ring is equivalent to the ring's prime
spectrum. -/
noncomputable def projectiveSpaceOverZeroEquivPrimeSpectrum
    (R : Type u) [CommRing R] :
    Scheme.projectiveSpaceOver 0 (Spec (.of R)) ≃ PrimeSpectrum R := by
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
  exact (Proj.polynomialProjOverSpecIso (Fin 1) R).hom.homeomorph.toEquiv |>.trans
    (eTop.inv.homeomorph.toEquiv.trans
      (eBasic.hom.homeomorph.toEquiv.trans
        (PrimeSpectrum.homeomorphOfRingEquiv eRing).toEquiv))

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

/-- Every positive cohomology group of every abelian sheaf on relative `ℙ⁰` over a
ring with nonempty subsingleton prime spectrum vanishes. -/
theorem projectiveSpaceOverZero_H_succ_subsingleton_of_primeSpectrum
    (R : Type u) [CommRing R] [Nonempty (PrimeSpectrum R)]
    [Subsingleton (PrimeSpectrum R)]
    (F : TopCat.Sheaf AddCommGrpCat.{u}
      (projectiveSpaceOver 0 (Spec (.of R)))) (n : ℕ) :
    Subsingleton (F.H (n + 1)) := by
  let e := ProjectiveSpace.projectiveSpaceOverZeroEquivPrimeSpectrum R
  let _ : Nonempty (projectiveSpaceOver 0 (Spec (.of R))) := e.nonempty
  let _ : Subsingleton (projectiveSpaceOver 0 (Spec (.of R))) := e.subsingleton
  exact CategoryTheory.Sheaf.subsingleton_H_succ_of_nonempty_subsingleton F n

/-- Every positive cohomology group of every abelian sheaf on relative `ℙ⁰` over a
field vanishes. -/
theorem projectiveSpaceOverZero_H_succ_subsingleton
    (K : Type u) [Field K] (F : TopCat.Sheaf AddCommGrpCat.{u}
      (projectiveSpaceOver 0 (Spec (.of K)))) (n : ℕ) :
    Subsingleton (F.H (n + 1)) :=
  projectiveSpaceOverZero_H_succ_subsingleton_of_primeSpectrum K F n

/-- Every positive cohomology group of every abelian sheaf on relative `ℙ⁰` over a
ring with nonempty subsingleton prime spectrum vanishes, with the positive degree
supplied as an inequality. -/
theorem projectiveSpaceOverZero_H_subsingleton_of_primeSpectrum
    (R : Type u) [CommRing R] [Nonempty (PrimeSpectrum R)]
    [Subsingleton (PrimeSpectrum R)]
    (F : TopCat.Sheaf AddCommGrpCat.{u}
      (projectiveSpaceOver 0 (Spec (.of R))))
    (i : ℕ) (hi : 1 ≤ i) : Subsingleton (F.H i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hi
  simpa [Nat.add_comm] using
    projectiveSpaceOverZero_H_succ_subsingleton_of_primeSpectrum R F n

/-- Every positive cohomology group of every abelian sheaf on relative `ℙ⁰` over a
field vanishes, with the positive degree supplied as an inequality. -/
theorem projectiveSpaceOverZero_H_subsingleton
    (K : Type u) [Field K] (F : TopCat.Sheaf AddCommGrpCat.{u}
      (projectiveSpaceOver 0 (Spec (.of K))))
    (i : ℕ) (hi : 1 ≤ i) : Subsingleton (F.H i) :=
  projectiveSpaceOverZero_H_subsingleton_of_primeSpectrum K F i hi

/-- For every integral twist degree, `H¹(ℙ⁰_K, O(d))` vanishes. -/
theorem projectiveSpaceOverTwist_zero_H_one_subsingleton
    (K : Type u) [Field K] (d : ℤ) :
    Subsingleton
      (((SheafOfModules.toSheaf _).obj
        (projectiveSpaceOverTwist 0 (Spec (.of K)) d)).H 1) :=
  projectiveSpaceOverZero_H_subsingleton K _ 1 (by omega)

/-- Scheme-level Serre vanishing holds on relative `ℙ⁰` over every ring whose
prime spectrum is nonempty and subsingleton. -/
theorem projectiveSpaceHasSerreVanishing_zero_spec_of_primeSpectrum
    (R : Type u) [CommRing R] [Nonempty (PrimeSpectrum R)]
    [Subsingleton (PrimeSpectrum R)] :
    ProjectiveSpaceHasSerreVanishing 0 (Spec (.of R)) := by
  intro M _ _ i hi
  filter_upwards [] with d
  exact projectiveSpaceOverZero_H_subsingleton_of_primeSpectrum R _ i hi

/-- Scheme-level Serre vanishing holds on relative `ℙ⁰` over a field.  In fact, the
proof gives pointwise vanishing in every twist degree, without finiteness hypotheses on
the sheaf. -/
theorem projectiveSpaceHasSerreVanishing_zero_spec
    (K : Type u) [Field K] :
    ProjectiveSpaceHasSerreVanishing 0 (Spec (.of K)) :=
  projectiveSpaceHasSerreVanishing_zero_spec_of_primeSpectrum K

end AlgebraicGeometry.Scheme
