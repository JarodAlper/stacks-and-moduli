module

public import StacksAndModuli.API.FiniteProjectiveCokernelFiberCriterion
public import StacksAndModuli.API.ProjectiveGradedEventuallyFlat

/-!
# Eventual graded flatness from a projective-line recurrence

The standard two-variable Koszul recurrence on projective one-space has the shape
`0 → M_t → M_(t+1)² → M_(t+2) → 0`.  This file records the formal persistence
consequence of such a recurrence.  If its first map remains injective over every
maximal-local residue field and the first two pieces are finite projective, then all pieces
in the tail are finite projective.  In particular the graded module is flat above the
initial degree, so `GradedModule.IsFlatAbove.flat_loc_singleton` makes every standard-chart
localization degreewise flat.

Constructing the recurrence for a particular projective sheaf, and proving its exactness and
base-change compatibility, are deliberately separate geometric inputs.

Main declaration:

* `GradedModule.isFlatAbove_of_projectiveLine_recurrence`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace.GradedModule

variable {R : Type u} [CommRing R] {n : ℕ}

/-- A projective-line two-step recurrence propagates flatness to every graded piece above
its two finite-projective initial pieces. -/
theorem isFlatAbove_of_projectiveLine_recurrence
    (M : GradedModule R n) (D : ℤ)
    (f : ∀ t : ℕ,
      M.obj (D + (t : ℤ)) →ₗ[R]
        (Fin 2 → M.obj (D + ((t + 1 : ℕ) : ℤ))))
    (g : ∀ t : ℕ,
      (Fin 2 → M.obj (D + ((t + 1 : ℕ) : ℤ))) →ₗ[R]
        M.obj (D + ((t + 2 : ℕ) : ℤ)))
    (hex : ∀ t, Function.Exact (f t) (g t))
    (hg : ∀ t, Function.Surjective (g t))
    (hf : ∀ t (I : Ideal R) (_ : I.IsMaximal),
      Function.Injective
        ((LocalizedModule.map I.primeCompl (f t)).lTensor
          (IsLocalRing.ResidueField (Localization.AtPrime I))))
    (hfin0 : Module.Finite R (M.obj D))
    (hproj0 : Module.Projective R (M.obj D))
    (hfin1 : Module.Finite R (M.obj (D + 1)))
    (hproj1 : Module.Projective R (M.obj (D + 1))) :
    IsFlatAbove M D := by
  let X : ℕ → Type u := fun t ↦ M.obj (D + (t : ℤ))
  have hpersist : ∀ t, Module.Finite R (X t) ∧ Module.Projective R (X t) := by
    apply LinearMap.finite_projective_of_twoStep_exact_of_forall_maximal_lTensor_injective
      X f g hex hg hf
    · letI : Module.Finite R (M.obj D) := hfin0
      exact Module.Finite.equiv
        (CategoryTheory.eqToIso (congrArg M.obj
          (show D = D + ((0 : ℕ) : ℤ) by omega))).toLinearEquiv
    · letI : Module.Projective R (M.obj D) := hproj0
      exact Module.Projective.of_equiv
        (CategoryTheory.eqToIso (congrArg M.obj
          (show D = D + ((0 : ℕ) : ℤ) by omega))).toLinearEquiv
    · simpa [X]
    · simpa [X]
  intro d hd
  let t : ℕ := (d - D).toNat
  have hDt : D + (t : ℤ) = d := by
    dsimp [t]
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr hd)]
    omega
  have hproj : Module.Projective R (M.obj (D + (t : ℤ))) := (hpersist t).2
  rw [← hDt]
  letI : Module.Projective R (M.obj (D + (t : ℤ))) := hproj
  exact Module.Flat.of_projective

end AlgebraicGeometry.ProjectiveSpace.GradedModule

end

end
