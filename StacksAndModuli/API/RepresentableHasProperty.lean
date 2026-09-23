module

public import StacksAndModuli.API.RepresentableWithEtaleEquivalence
public import StacksAndModuli.«Section4.3-Properties».«part4.3.1-properties-of-morphisms»

/-!
# Smooth-local properties of schematic morphisms

For a morphism of algebraic stacks known to be representable by schemes, testing a
smooth-local scheme property on smooth presentations is equivalent to requiring the
property on every representing scheme of every scheme-valued fiber.

## Main result

* `BasedFunctor.hasProperty_iff_relativelyRepresentableWith`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ v₃ u₂ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}}
  {Ycat : BasedCategory.{v₃, u₃} Scheme.{u}}
  [IsAlgebraicStack Xcat] [IsAlgebraicStack Ycat]

/-- On a morphism representable by schemes, a smooth-local property tested on stack
presentations is equivalent to relative representability with that property. -/
theorem hasProperty_iff_relativelyRepresentableWith
    {P : MorphismProperty Scheme.{u}} (hP : IsSmoothLocal P)
    {F : Xcat ⥤ᵇ Ycat} (hF : F.RelativelyRepresentable) :
    HasProperty P F ↔ F.RelativelyRepresentableWith P := by
  constructor
  · intro h
    refine ⟨hF, ?_⟩
    intro T g U E hE
    let _ : IsAlgebraicStack (fiberProduct F g) :=
      IsAlgebraicStack.fiberProduct F g
    let _ : E.toFunctor.IsEquivalence := hE
    have hE' : RepresentableWith
        (@_root_.AlgebraicGeometry.Surjective ⊓
          @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) E :=
      (RepresentableWith.surjectiveEtale_of_isEquivalence E).mono
        (inf_le_inf le_rfl etale_le_smooth)
    exact HasProperty.arbitraryBaseChart hP h g E hE'
  · intro h V g _ U q hq
    obtain ⟨W, E, hE⟩ := h.1 V g
    let _ : E.toFunctor.IsEquivalence := hE
    have hE' : RepresentableWith
        (@_root_.AlgebraicGeometry.Surjective ⊓
          @_root_.AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}) E :=
      (RepresentableWith.surjectiveEtale_of_isEquivalence E).mono
        (inf_le_inf le_rfl etale_le_smooth)
    exact (AlgebraicGeometry.hasProperty_chart_indep
      hP.isLocalOnSourceAlong (BasedCategory.fiberProductSnd F g) hE' hq).mp
        (h.2 V g W E hE)

end AlgebraicGeometry.BasedFunctor
