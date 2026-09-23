module

public import StacksAndModuli.API.AlgebraicStackDiagonal
public import StacksAndModuli.API.FaithfulStackComponents
public import StacksAndModuli.API.FiberProductComponentsSmall
public import StacksAndModuli.API.FiberProductProjectionFaithful

/-!
# Small sheaf representations of scheme-valued fibers

If a map from a small presheaf has a self-intersection represented by a small
presheaf, then every scheme-valued base change has universe-small connected
components.  When that base change is a faithful stack, shrinking its component
presheaf therefore gives a small étale sheaf whose associated prestack is equivalent
to the base change.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Opposite
open CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry

/-- A representation of a prestack over schemes by a universe-small étale sheaf. -/
structure BasedFunctor.SmallEtaleSheafRepresentation
    (Xcat : BasedCategory.{v₂, u₂} Scheme.{u}) where
  /-- The small representing presheaf. -/
  X : Scheme.{u}ᵒᵖ ⥤ Type u
  /-- The representing presheaf is an étale sheaf. -/
  isSheaf : Presieve.IsSheaf Scheme.etaleTopology X
  /-- The comparison from the associated prestack. -/
  representation : ofPresheaf X ⥤ᵇ Xcat
  /-- The comparison is an equivalence. -/
  representation_isEquivalence : representation.toFunctor.IsEquivalence

namespace BasedFunctor

/-- A faithful stack over schemes with universe-small fiberwise components has
a representation by a universe-small étale sheaf. -/
noncomputable def smallEtaleSheafRepresentation_of_smallFiberComponents
    (Zcat : BasedCategory.{v₂, u₂} Scheme.{u})
    [Zcat.p.IsFiberedInGroupoids] [Zcat.p.Faithful]
    [BasedCategory.IsStack Scheme.etaleTopology Zcat]
    (hsmall : ∀ R : Scheme.{u}, Small.{u}
      (CategoryTheory.ConnectedComponents (Zcat.p.Fiber R))) :
    SmallEtaleSheafRepresentation Zcat := by
  let C := fiberComponents (𝒳 := Zcat)
  have hsmall' : FunctorToTypes.Small.{u} C := by
    intro R
    exact hsmall R.unop
  let _ : FunctorToTypes.Small.{u} C := hsmall'
  let X := FunctorToTypes.shrink.{u} C
  let E : ofPresheaf X ⥤ᵇ Zcat :=
    { toFunctor :=
        (CategoryOfElements.costructuredArrowYonedaEquivalence X).inverse ⋙
          (shrinkElementsComparison C).toFunctor ⋙
          (componentPrestackComparison (𝒳 := Zcat)).toFunctor
      w := by
        rw [Functor.assoc, Functor.assoc,
          (componentPrestackComparison (𝒳 := Zcat)).w,
          (shrinkElementsComparison C).w]
        rfl }
  have hE : E.toFunctor.IsEquivalence := by
    have h₁ :=
      (CategoryOfElements.costructuredArrowYonedaEquivalence X).isEquivalence_inverse
    have h₂ := isEquivalence_shrinkElementsComparison C
    have h₃ := isEquivalence_componentPrestackComparison (𝒳 := Zcat)
    have h₁₂ :
        ((CategoryOfElements.costructuredArrowYonedaEquivalence X).inverse ⋙
          (shrinkElementsComparison C).toFunctor).IsEquivalence :=
      Functor.isEquivalence_trans _ _
    exact Functor.isEquivalence_trans _ _
  exact
    { X := X
      isSheaf := FunctorToTypes.isSheaf_shrink C
        (fiberComponents_isSheaf (X := Zcat))
      representation := E
      representation_isEquivalence := hE }

variable {Ycat : BasedCategory.{v₂, u₂} Scheme.{u}}
  {U R : Scheme.{u}ᵒᵖ ⥤ Type u}
  (F : ofPresheaf U ⥤ᵇ Ycat)
  {T : Scheme.{u}} (g : overBased T ⥤ᵇ Ycat)

/-- A scheme-valued fiber of a map from an étale sheaf to an étale stack is
again an étale stack. -/
theorem isStack_fiberProduct_ofPresheaf_overBased
    [BasedCategory.IsStack Scheme.etaleTopology Ycat]
    (hU : Presieve.IsSheaf Scheme.etaleTopology U) :
    BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g) := by
  let hSource : BasedCategory.IsStack Scheme.etaleTopology (ofPresheaf U) :=
    { isFiberedInGroupoids := inferInstance
      isStack := (Functor.isStack_proj_yoneda_iff
        Scheme.etaleTopology U).2 hU }
  let _ : BasedCategory.IsStack Scheme.etaleTopology (ofPresheaf U) := hSource
  let hPoint : BasedCategory.IsStack Scheme.etaleTopology (overBased T) :=
    isStack_overBased Scheme.etaleTopology T
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  let _ : BasedCategory.IsStack Scheme.etaleTopology (overBased T) := hPoint
  exact isStack_fiberProduct Scheme.etaleTopology F g

/-- A small represented self-intersection makes a faithful stack-valued fiber
representable by a universe-small étale sheaf. -/
noncomputable def smallEtaleSheafRepresentation_fiberProduct
    [Ycat.p.IsFiberedInGroupoids]
    (hR : (fiberProduct F F).IsRepresentedByPresheaf R)
    [(fiberProduct F g).p.Faithful]
    [BasedCategory.IsStack Scheme.etaleTopology (fiberProduct F g)] :
    SmallEtaleSheafRepresentation (fiberProduct F g) := by
  let C := fiberComponents (𝒳 := fiberProduct F g)
  have hsmall : FunctorToTypes.Small.{u} C := by
    intro S
    exact small_connectedComponents_fiberProduct F g hR S.unop
  let _ : FunctorToTypes.Small.{u} C := hsmall
  let X := FunctorToTypes.shrink.{u} C
  let E : ofPresheaf X ⥤ᵇ fiberProduct F g :=
    { toFunctor :=
        (CategoryOfElements.costructuredArrowYonedaEquivalence X).inverse ⋙
          (shrinkElementsComparison C).toFunctor ⋙
          (componentPrestackComparison (𝒳 := fiberProduct F g)).toFunctor
      w := by
        rw [Functor.assoc, Functor.assoc,
          (componentPrestackComparison (𝒳 := fiberProduct F g)).w,
          (shrinkElementsComparison C).w]
        rfl }
  have hE : E.toFunctor.IsEquivalence := by
    have h₁ :=
      (CategoryOfElements.costructuredArrowYonedaEquivalence X).isEquivalence_inverse
    have h₂ := isEquivalence_shrinkElementsComparison C
    have h₃ := isEquivalence_componentPrestackComparison
      (𝒳 := fiberProduct F g)
    have h₁₂ :
        ((CategoryOfElements.costructuredArrowYonedaEquivalence X).inverse ⋙
          (shrinkElementsComparison C).toFunctor).IsEquivalence :=
      Functor.isEquivalence_trans _ _
    exact Functor.isEquivalence_trans _ _
  exact
    { X := X
      isSheaf := FunctorToTypes.isSheaf_shrink C
        (fiberComponents_isSheaf (X := fiberProduct F g))
      representation := E
      representation_isEquivalence := hE }

end BasedFunctor

end AlgebraicGeometry
