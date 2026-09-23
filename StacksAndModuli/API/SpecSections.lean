module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# `A`-module structure on sections over an open of `Spec A`

Supporting API with no Stacks Project counterpart.

Mathlib gives the sections of a sheaf of modules `M` on a scheme `X` the module structure
`Module Γ(X, U) Γ(M, U)` (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:94`), and on an affine
scheme it gives the coefficient ring the algebra structure
`Algebra R Γ(Spec R, U)` (`Mathlib/AlgebraicGeometry/AffineScheme.lean:644`). It does not
compose the two: `Module R Γ(M, U)` is not derivable by instance search, because restricting
scalars along an algebra map is not automatic.

§2.1 needs exactly that composite, uniformly in `U` — for example to say that `Γ(M, D(r))` is
flat over a coefficient ring mapping into `R`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Sections of a sheaf of modules on `Spec R` over any open form an `R`-module, by restricting
scalars along Mathlib's `Algebra R Γ(Spec R, U)`. -/
noncomputable instance specSectionsModule {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (U : (Spec R).Opens) : Module R Γ(M, U) :=
  Module.compHom Γ(M, U) (algebraMap R Γ(Spec R, U))

/-- The same instance in the shape it is used in §2.1: over a basic open. Instance search keys
on the syntactic form of the open, and `PrimeSpectrum.basicOpen r` does not match the general
`U : (Spec R).Opens` pattern, so this specialization is needed even though the underlying term
is identical. -/
noncomputable instance specSectionsModuleBasicOpen {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (r : R) : Module R Γ(M, PrimeSpectrum.basicOpen r) :=
  specSectionsModule M _

instance specSectionsIsScalarTower {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (U : (Spec R).Opens) : IsScalarTower R Γ(Spec R, U) Γ(M, U) :=
  ⟨fun r b n ↦ by rw [Algebra.smul_def]; exact mul_smul _ _ _⟩

/-- Mathlib states the module structure on sections in the `Γ(M, U)` spelling, which unfolds to
`(Scheme.Modules.presheaf M).obj (op U)` — an `Ab`-valued presheaf. Parts of §2.1 instead write
the sections as `M.val.obj (op U)`, a `ModuleCat`. The two are definitionally equal but are
different discrimination-tree keys, so instance search does not see through. -/
instance sectionsValModule {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) :
    Module Γ(X, U) (M.val.obj (Opposite.op U)) :=
  (M.val.obj (.op U)).isModule

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Hom

/-- Global sections of an isomorphism of schemes is an isomorphism of rings.

Mathlib has `AlgebraicGeometry.Scheme.Hom.inv_appTop`, which *presupposes* this, but does not
register it as an instance. -/
instance isIso_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : IsIso f.appTop :=
  ⟨(inv f).appTop, by
    rw [← Scheme.Hom.comp_appTop, IsIso.inv_hom_id, Scheme.Hom.id_appTop], by
    rw [← Scheme.Hom.comp_appTop, IsIso.hom_inv_id, Scheme.Hom.id_appTop]⟩

end AlgebraicGeometry.Scheme.Hom
