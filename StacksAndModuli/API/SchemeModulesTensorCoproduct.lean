module

public import StacksAndModuli.API.SchemeModulesTensorExact

/-!
# Tensor products and arbitrary coproducts of scheme modules

Tensoring on the right by an arbitrary module sheaf preserves all small colimits.
This file records the resulting canonical isomorphism for coproducts whose index type
lives in the scheme's universe.  Unlike the finite-biproduct construction, it therefore
applies directly to the `ULift`-indexed finite coproducts used in the book.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Tensoring in the right factor distributes over every small coproduct. -/
noncomputable def tensorCoproductIso {J : Type u}
    (F : J → X.Modules) (G : X.Modules) :
    ((∐ F) ⊗ₘ G) ≅ ∐ fun j ↦ F j ⊗ₘ G :=
  PreservesCoproduct.iso (tensorRightFunctor G) F

end AlgebraicGeometry.Scheme.Modules

end
