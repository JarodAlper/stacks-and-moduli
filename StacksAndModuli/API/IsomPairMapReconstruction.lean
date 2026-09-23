module

public import StacksAndModuli.API.ProductReassembly
public import StacksAndModuli.API.TwoYonedaReconstruction
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.6-isom-presheaves»

/-!
# Reconstructing maps to a product from two fiber objects

An arbitrary morphism from a representable prestack to a product is 2-isomorphic to
the canonical pair map obtained by evaluating its two projections and taking chosen
cartesian pullbacks.  This packages the change-of-leg step used for diagonal fibers.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.BasedCategory

variable {C : Type u₁} [Category.{v₁} C]
  {X : BasedCategory.{v₂, u₂} C} [X.p.IsFiberedInGroupoids]
  {S : C}

/-- The first fiber object classified by a map from a representable prestack to
`X × X`. -/
noncomputable abbrev isomPairMapFstObj (g : overBased S ⥤ᵇ prod X X) :
    X.p.Fiber S :=
  (twoYonedaEval (𝒳 := X) S).obj
    (g.comp (fiberProductFst X.toBase X.toBase))

/-- The second fiber object classified by a map from a representable prestack to
`X × X`. -/
noncomputable abbrev isomPairMapSndObj (g : overBased S ⥤ᵇ prod X X) :
    X.p.Fiber S :=
  (twoYonedaEval (𝒳 := X) S).obj
    (g.comp (fiberProductSnd X.toBase X.toBase))

/-- Any map from a representable prestack to `X × X` is 2-isomorphic to the
canonical pair map attached to its two fiber objects. -/
noncomputable def isomPairMapReconstructionIso (g : overBased S ⥤ᵇ prod X X) :
    isomPairMap (isomPairMapFstObj g) (isomPairMapSndObj g) ≅ g :=
  prodLiftIso
      (twoYonedaPullbackEvalIso
        (g.comp (fiberProductFst X.toBase X.toBase)))
      (twoYonedaPullbackEvalIso
        (g.comp (fiberProductSnd X.toBase X.toBase))) ≪≫
    prodLiftProjectionsIso g

end CategoryTheory.BasedCategory
