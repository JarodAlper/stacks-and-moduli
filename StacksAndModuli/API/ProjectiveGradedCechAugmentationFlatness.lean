module

public import StacksAndModuli.API.ProjectiveGradedEventuallyFlat
public import StacksAndModuli.API.ProjectiveGradedCech

/-!
# Eventual flatness reflected by the Čech augmentation

A degreewise bijective Čech augmentation transfers eventual flatness from
Čech `H⁰` back to the original graded module.  This is the final algebraic
step when a recurrence is most naturally proved on Čech cohomology but the
geometric flatness criterion is stated for `Γ_*`.

Main declaration:

* `GradedModule.isFlatAbove_of_cechAug_bijective`.
-/

@[expose] public section

noncomputable section

set_option linter.style.haveILetI false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {R : Type u} [CommRing R] {n : ℕ}

/-- Eventual flatness of Čech `H⁰` reflects through a degreewise bijective
Čech augmentation. -/
theorem isFlatAbove_of_cechAug_bijective
    (M : GradedModule R n) (D : ℤ)
    (hH0 : IsFlatAbove (M.cechHgr 0) D)
    (haug : ∀ d, D ≤ d → Function.Bijective ((M.cechAug d).hom)) :
    IsFlatAbove M D := by
  intro d hd
  letI : Module.Flat R ((M.cechHgr 0).obj d) := hH0 d hd
  let e := LinearEquiv.ofBijective ((M.cechAug d).hom) (haug d hd)
  exact Module.Flat.of_linearEquiv e

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
