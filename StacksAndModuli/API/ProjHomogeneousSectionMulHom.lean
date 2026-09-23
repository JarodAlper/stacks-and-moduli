module

public import StacksAndModuli.API.ProjGammaStarTwist
public import StacksAndModuli.API.SchemeModulesPullbackPolynomialTwist

/-!
# Homogeneous sections as multiplication morphisms

For a nonnegative degree, the morphism from the structure sheaf represented by a
homogeneous section is multiplication by that form, after identifying the zero twist
with the structure sheaf.  This is the one-factor input in comparisons between the
multiplication and tensor-cancellation models of projective twisting.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace ProjectiveSpectrum.Twist

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (R : ℕ → σ) [GradedRing R]

/-- The morphism represented by a homogeneous form is multiplication by that form
from the zero twist, transported from the structure sheaf. -/
lemma homogeneousSectionHom_eq_zeroIso_inv_comp_mulHom
    {d : ℕ} (p : R d) :
    homogeneousSectionHom R p =
      (zeroIso R).inv ≫ mulHom R p 0 (d : ℤ) (by omega) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U ↦ ?_)
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  change (homogeneousSectionHom R p).val.app U
      (1 : Γ(Proj R, U.unop)) = _
  rw [homogeneousSectionHom_app_one]
  change homogeneousSection R p U.unop =
    mulSectionHom R p 0 (d : ℤ) (by omega) U
      ((sectionsZeroLinearEquiv R U) 1)
  refine Subtype.ext (funext fun x ↦ Subtype.ext ?_)
  change Localization.mk (p : A) 1 =
    Localization.mk (1 : A) 1 * Localization.mk (p : A) 1
  rw [Localization.mk_one, one_mul]

end ProjectiveSpectrum.Twist

end

end
