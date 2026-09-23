module

public import StacksAndModuli.API.FlatCoefficientModelHomogeneousMatrixDescent
public import StacksAndModuli.API.FlatCoefficientModelNoetherianPolynomial

/-!
# Noetherian Cech models from coefficient-flat homogeneous matrices

A uniformly homogeneous polynomial matrix has a canonical polynomial model whose module
is the total module of its graded cokernel.  If that total module is flat over the
coefficient ring, unconditional polynomial coefficient spreading supplies a flat model
which retains the matrix.  Homogeneous matrix descent then gives noetherian Cech models
for the graded cokernel in every sufficiently large twist.

Main declaration:

* `GradedModule.Total.exists_eventual_noetherianCechModel_of_flat_homogeneousMatrix`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

open MvPolynomial

/-- The graded cokernel of a uniformly homogeneous polynomial matrix admits noetherian
Cech models in every sufficiently large twist if its total module is coefficient-flat. -/
theorem exists_eventual_noetherianCechModel_of_flat_homogeneousMatrix
    {A : Type u} [CommRing A] {n m r degree : ℕ}
    (G : Matrix (Fin r) (Fin m) (MvPolynomial (Fin (n + 1)) A))
    (hG : ∀ i j, G i j ∈ polySubmodule A n degree)
    (hflat : @Module.Flat A
      (GradedModule.coker (homogeneousMatrixHom G hG)).Total _ _
      (Module.compHom (GradedModule.coker (homogeneousMatrixHom G hG)).Total
        (algebraMap A (MvPolynomial (Fin (n + 1)) A)))) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      Nonempty (GradedModule.NoetherianCechModel
        (GradedModule.coker (homogeneousMatrixHom G hG)) d) := by
  let D := homogeneousMatrixPolynomialModel G hG
  obtain ⟨E⟩ :=
    Module.FinitePresentation.PolynomialModel.exists_flatCoefficientModel_of_flat
      (A := A) (M := (GradedModule.coker (homogeneousMatrixHom G hG)).Total)
      D hflat
  exact
    E.exists_eventual_noetherianCechModel_of_homogeneousMatrixPolynomialModel
      G hG

end AlgebraicGeometry.ProjectiveSpace.GradedModule.Total

end

end
