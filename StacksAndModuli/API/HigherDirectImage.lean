module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-!
# Higher direct images

Mathlib has no higher direct images `R^i f_* F`. The usual construction as the right
derived functor of `f_*` is out of reach: it needs `EnoughInjectives` for
`SheafOfModules`, and neither that nor `IsGrothendieckAbelian` is registered for sheaves of
modules on a scheme.

This file builds them instead by the other standard route, as the sheafification of the
presheaf `U ↦ H^i(f⁻¹ U, F)`. That presheaf is available: Mathlib's
`CategoryTheory.Sheaf.cohomologyPresheaf` is exactly `U ↦ H^i(U, F)` on the site, and for
the site of opens of a space it only has to be restricted along `f`.

The result is a sheaf of abelian groups rather than of `𝒪_Y`-modules. That is enough for the
vanishing statements (`R^i π_* Q(d) = 0`), and it sidesteps the module-structure plumbing
entirely.

**Upgrading to sheaves of modules is what §A.6 needs and does not have.** Grauert's Theorem
(A.6.7), Cohomology and Base Change II (A.6.8) and Exercise A.6.9 all assert that
`R^i f_* F` is a vector bundle, which is meaningless for an abelian sheaf. The obstruction is
that a section `r ∈ Γ(Y, U)` acts on `F` only after restriction to `f⁻¹ U`, so the action is
*not* induced by an endomorphism of the global sheaf `F`, and therefore not by the
functoriality of `cohomologyPresheafFunctor` in `F`. The natural route — identify
`(F.cohomologyPresheaf n).obj (op U)` with the cohomology of `F.over U` on the over-site and
put the module structure there by the `smulEnd` construction of
`StacksAndModuli/API/SheafCohomologyModule.lean` — is **not** available off the shelf: that
identification is listed as a TODO in Mathlib's
`CategoryTheory/Sites/SheafCohomology/Basic.lean` and would have to be built first, followed
by semilinearity of the restriction maps. See the §A.6 COMMENTARY.

## Main definitions

* `AlgebraicGeometry.Scheme.higherDirectImagePresheaf`: the presheaf `U ↦ H^i(f⁻¹ U, F)`.
* `AlgebraicGeometry.Scheme.higherDirectImage`: `R^i f_* F`, its sheafification.
* `AlgebraicGeometry.Scheme.higherDirectImageOfModules`: `R^i f_* F` for `F` a sheaf of
  modules, via the forgetful functor to abelian sheaves.

## Main results

* `AlgebraicGeometry.Scheme.higherDirectImage_zero_of_isZero_cohomologyPresheaf`: if every
  `H^i(f⁻¹ U, F)` vanishes then so does `R^i f_* F`.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory TopologicalSpace Opposite Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The presheaf `U ↦ H^i(f⁻¹ U, F)` on `Y`, whose sheafification is the higher direct
image `R^i f_* F`. -/
noncomputable def higherDirectImagePresheaf (F : TopCat.Sheaf AddCommGrpCat.{u} X) (i : ℕ) :
    (Y.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (TopologicalSpace.Opens.map f.base).op ⋙ F.cohomologyPresheaf i

/-- The **higher direct image** `R^i f_* F` of a sheaf of abelian groups, the sheafification
of `U ↦ H^i(f⁻¹ U, F)`. -/
noncomputable def higherDirectImage (F : TopCat.Sheaf AddCommGrpCat.{u} X) (i : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} Y :=
  (presheafToSheaf _ _).obj (higherDirectImagePresheaf f F i)

/-- The **higher direct image** `R^i f_* F` of a sheaf of modules, taken after forgetting to
abelian sheaves. -/
noncomputable def higherDirectImageOfModules (F : X.Modules) (i : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} Y :=
  higherDirectImage f ((SheafOfModules.toSheaf _).obj F) i

variable {f}

/-- If all the cohomology groups `H^i(f⁻¹ U, F)` vanish, then `R^i f_* F = 0`: the
sheafification of a zero presheaf is zero. -/
theorem higherDirectImage_isZero_of_isZero_presheaf
    {F : TopCat.Sheaf AddCommGrpCat.{u} X} {i : ℕ}
    (h : IsZero (higherDirectImagePresheaf f F i)) :
    IsZero (higherDirectImage f F i) := by
  rw [IsZero.iff_id_eq_zero] at h ⊢
  rw [show 𝟙 (higherDirectImage f F i) =
    (presheafToSheaf _ AddCommGrpCat.{u}).map (𝟙 (higherDirectImagePresheaf f F i)) from
      (CategoryTheory.Functor.map_id _ _).symm, h, Functor.map_zero]

end AlgebraicGeometry.Scheme
