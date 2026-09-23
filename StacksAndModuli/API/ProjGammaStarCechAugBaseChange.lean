module

public import StacksAndModuli.API.ProjGammaStarCechBaseChange

/-!
# Reflecting `Γ_*` base change through the Čech augmentation

For a finitely presented sheaf on polynomial `Proj`, the Čech augmentation of
`Γ_*(F)` and of the pulled-back sheaf is bijective.  Moreover, the graded
base-change comparison is an isomorphism after applying Čech `H⁰`.  The
naturality square for the augmentation therefore reflects degreewise
bijectivity of `Γ_*` base change into bijectivity of the augmentation after
coefficient change.

Main declaration:

* `AlgebraicGeometry.ProjectiveSpace.
    bijective_cechAug_baseChange_of_bijective_gammaStarBaseChangeApp`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory TensorProduct
open AlgebraicGeometry ProjectiveSpectrum.Twist

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

set_option synthInstance.maxHeartbeats 1000000 in
-- Finitely presented pullbacks on explicit polynomial `Proj` synthesize slowly.
/-- If the degreewise `Γ_*` base-change comparison is bijective, then the
Čech augmentation of the scalar-extended graded module is bijective in that
degree. -/
theorem bijective_cechAug_baseChange_of_bijective_gammaStarBaseChangeApp
    (n : ℕ) {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    [F.IsFinitePresentation] (dN : ℕ)
    (hψ : Function.Bijective (gammaStarBaseChangeApp n f F (dN : ℤ))) :
    letI : Algebra R S := f.toAlgebra
    Function.Bijective
      (((Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (Proj.polynomialToSpec (Fin (n + 1)) R) F
        (stdVars n R)).baseChange S).cechAug (dN : ℤ)).hom := by
  letI : Algebra R S := f.toAlgebra
  let M := Proj.gammaStar
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
    (Proj.polynomialToSpec (Fin (n + 1)) R) F (stdVars n R)
  let N := Proj.gammaStar
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S)
    (Proj.polynomialToSpec (Fin (n + 1)) S)
    ((Scheme.Modules.pullback (coeffMap n f)).obj F) (stdVars n S)
  have haugTarget : Function.Bijective ((N.cechAug (dN : ℤ)).hom) :=
    bijective_gammaStar_cechAug_of_isFinitePresentation
      (Proj.polynomialToSpec (Fin (n + 1)) S)
      ((Scheme.Modules.pullback (coeffMap n f)).obj F) (dN : ℤ)
  let ψ := gammaStarBaseChangeHom n f F
  haveI : IsIso ((GradedModule.cechHgrMap ψ 0).app (dN : ℤ)) :=
    isIso_cechHgrMap_gammaStarBaseChangeHom_app n f F dN
  have hcech : Function.Bijective
      (((GradedModule.cechHgrMap ψ 0).app (dN : ℤ)).hom) :=
    ConcreteCategory.bijective_of_isIso _
  have hnat := GradedModule.cechAug_naturality ψ (dN : ℤ)
  have hEq := congrArg ModuleCat.Hom.hom hnat
  simp only [ModuleCat.hom_comp] at hEq
  have hψ' : Function.Bijective ((ψ.app (dN : ℤ)).hom) := by
    change Function.Bijective (gammaStarBaseChangeApp n f F (dN : ℤ))
    exact hψ
  have hcomp : Function.Bijective
      (((GradedModule.cechHgrMap ψ 0).app (dN : ℤ)).hom.comp
        (((M.baseChange S).cechAug (dN : ℤ)).hom)) := by
    rw [hEq]
    exact haugTarget.comp hψ'
  exact (hcech.of_comp_iff'
    (((M.baseChange S).cechAug (dN : ℤ)).hom)).mp
      (by simpa only [LinearMap.coe_comp] using hcomp)

end AlgebraicGeometry.ProjectiveSpace

end

end
