module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.5-fiber-products-of-prestacks»

/-!
# Faithful projections of fiber products

If both factors of a prestack fiber product are fibered in sets, then so is the
fiber product.  Equality of base maps first determines the morphism in the first
factor; the cartesian-lift equations then determine the base map in the second
factor, where faithfulness determines that morphism as well.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.BasedCategory

variable {S : Type u₁} [Category.{v₁} S]
  {X : BasedCategory.{v₂, u₂} S}
  {Y : BasedCategory.{v₃, u₃} S}
  {Z : BasedCategory.{v₄, u₄} S}
  (F : X ⥤ᵇ Y) (G : Z ⥤ᵇ Y)

/-- The projection of a fiber product is faithful when both factor projections
are faithful. -/
instance fiberProduct_projection_faithful [X.p.Faithful] [Z.p.Faithful] :
    (fiberProduct F G).p.Faithful where
  map_injective {a b} φ ψ h := by
    rcases φ with ⟨φ₁, φ₂, hφ, wφ⟩
    rcases ψ with ⟨ψ₁, ψ₂, hψ, wψ⟩
    change X.p.map φ₁ = X.p.map ψ₁ at h
    have h₁ : φ₁ = ψ₁ := X.p.map_injective h
    subst ψ₁
    have h₂ : φ₂ = ψ₂ := by
      apply Z.p.map_injective
      rw [IsHomLift.fac' Z.p (X.p.map φ₁) φ₂]
      rw [IsHomLift.fac' Z.p (X.p.map φ₁) ψ₂]
    subst ψ₂
    rfl

end CategoryTheory.BasedCategory
