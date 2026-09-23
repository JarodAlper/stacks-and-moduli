module

public import StacksAndModuli.API.ProjectiveGradedFreeAug

/-!
# The graded `H⁰` of a twisted-free module as homogeneous forms

The graded half of the `H⁰` bridge of `PLAN-hilbert-quot.md` for the twisted-free ambient
sheaf.  For `M = ⨁_r S(-l)` and a degree `d` with `d - l = e ≥ 0`,

`(H⁰(M~(d)))_d ≃ₗ[R] (Fin r → R[x₀, …, xₙ]_e)`.

This is `GradedModule.bijective_cechAug_free` — the augmentation `M_d → H⁰(M~(d))` is
bijective once the twist is nonnegative — composed with the description of `M_d` itself as a
finite product of spaces of homogeneous forms.

Together with
`AlgebraicGeometry.ProjectiveSpace.twistedFreeTwistGlobalSectionsHomogeneousEquiv` (the scheme
half) both sides of `RelativeCohomology.SchemeGlobalSectionsComparison.globalSectionsIso` are
now identified with `Fin r → R[x]_e`, in the range `d ≥ l` allowed by the `bound` field of
that structure.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

open CategoryTheory MvPolynomial

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The degree-`d` part of `⨁_r S(-l)` is a finite product of spaces of homogeneous forms of
degree `e = d - l`, provided `e ≥ 0`. -/
noncomputable def freeObjHomogeneousEquiv (l : ℤ) (r : ℕ) (d : ℤ) (e : ℕ)
    (he : (e : ℤ) = d - l) :
    ((((structureModule R n).twist (-l)).pow r).obj d) ≃ₗ[R]
      (Fin r → MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R e) := by
  have hpoly : polySubmodule R n (d + -l)
      = MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R e := by
    have hnn : (0 : ℤ) ≤ d + -l := by omega
    rw [polySubmodule_of_nonneg (k := R) (n := n) hnn]
    congr 1
    omega
  exact LinearEquiv.piCongrRight fun _ : Fin r => LinearEquiv.ofEq _ _ hpoly

/-- **The graded half of the twisted-free `H⁰` comparison.** -/
noncomputable def cechHgrFreeHomogeneousEquiv (l : ℤ) (r : ℕ) (d : ℤ) (e : ℕ)
    (he : (e : ℤ) = d - l) :
    ((((((structureModule R n).twist (-l)).pow r).cechHgr 0).obj d)) ≃ₗ[R]
      (Fin r → MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R e) := by
  have hnn : (0 : ℤ) ≤ d + -l := by omega
  exact (LinearEquiv.ofBijective
      (((((structureModule R n).twist (-l)).pow r).cechAug d).hom)
      (bijective_cechAug_free (-l) r d hnn)).symm.trans
    (freeObjHomogeneousEquiv R n l r d e he)

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
