module

public import StacksAndModuli.API.ProjectiveGradedCechH0CanonicalBaseChange

/-!
# Finite-dimensional canonical base change on projective-line Cech H-zero

Supporting API with no Stacks Project counterpart.  On the projective line,
vanishing of first graded Cech cohomology makes the canonical coefficient-change
map on zeroth graded Cech cohomology surjective.  Over a field, equality of the
finite dimensions of its source and target upgrades that map to a bijection.

Main declaration:
- `GradedModule.cechHgrZeroCanonicalBaseChangeHom_bijective_of_subsingleton_one_of_finrank_eq`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open TensorProduct

variable {R A : Type u} [CommRing R] [Field A] [Algebra R A]

/-- On the projective line, vanishing first Cech cohomology and equality of the
finite dimensions on the two sides make the canonical `H⁰` coefficient-change
map bijective. -/
theorem cechHgrZeroCanonicalBaseChangeHom_bijective_of_subsingleton_one_of_finrank_eq
    (M : GradedModule R 1) (d : ℤ)
    [Subsingleton ((M.cechHgr 1).obj d)]
    [FiniteDimensional A (A ⊗[R] ((M.cechHgr 0).obj d))]
    [FiniteDimensional A (((M.baseChange A).cechHgr 0).obj d)]
    (hfinrank :
      Module.finrank A (A ⊗[R] ((M.cechHgr 0).obj d)) =
        Module.finrank A (((M.baseChange A).cechHgr 0).obj d)) :
    Function.Bijective
      (cechHgrZeroCanonicalBaseChangeHom (A := A) M d) := by
  have hsurjective :=
    cechHgrZeroCanonicalBaseChangeHom_surjective_of_subsingleton_one
      (A := A) M d
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    hfinrank).mpr hsurjective, hsurjective⟩

end AlgebraicGeometry.ProjectiveSpace.GradedModule
