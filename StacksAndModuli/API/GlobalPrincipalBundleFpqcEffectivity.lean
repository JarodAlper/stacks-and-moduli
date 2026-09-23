module

public import StacksAndModuli.API.GlobalPrincipalBundleAffine
public import StacksAndModuli.API.GlobalPrincipalBundleFpqcProperties
public import StacksAndModuli.API.GlobalPrincipalBundleUnderlyingArrowGluing

/-!
# Effective FPQC descent of principal bundles

This file combines effective descent of affine scheme arrows with the
structured descent API for principal bundles.  It first packages any
cartesian gluing of the underlying arrows as an `UnderlyingGluing`; the final
fpqc theorem is supplied once the affine-arrow effectivity bridge is imported.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor

universe u

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {G : Over S} [GrpObj G]
variable {T : Over S} {R : Sieve T}
variable (D : R.arrows.category ⥤ ClassifyingObj G)
variable (hDobj : ∀ q : R.arrows.category,
  (classifyingPrestack G).p.obj (D.obj q) = q.obj.left)
variable (hDmap : ∀ {q r : R.arrows.category} (k : q ⟶ r),
  IsHomLift (classifyingPrestack G).p k.hom.left (D.map k))

namespace ClassifyingObj

/-- A cartesian gluing of the underlying scheme arrows gives the underlying
total-space gluing required for descent of principal-bundle structure. -/
theorem nonempty_underlyingGluing_of_arrowGluing
    (A : Arrow Scheme.{u})
    (hA : (arrowCartesian Scheme.{u}).p.obj A = T.left)
    (ε : ∀ q : R.arrows.category, (underlyingArrowFunctor D).obj q ⟶ A)
    (hε : ∀ q : R.arrows.category,
      IsHomLift (arrowCartesian Scheme.{u}).p q.obj.hom.left (ε q))
    (hnat : ∀ {q r : R.arrows.category} (k : q ⟶ r),
      (underlyingArrowFunctor D).map k ≫ ε r = ε q) :
    Nonempty (UnderlyingGluing D hDobj hDmap) :=
  ⟨underlyingGluingOfArrowGluing D hDobj hDmap A hA ε hε hnat⟩

end ClassifyingObj

end AlgebraicGeometry.Scheme
