module

public import StacksAndModuli.API.PrincipalBundleQuotient
public import StacksAndModuli.API.ClassifyingStackCartesianSupport

/-!
# Exact sequences of smooth group schemes

Fppf exactness of `1 ⟶ K ⟶ G ⟶ Q ⟶ 1` is packaged by requiring
`G ⟶ Q` to be a principal `K`-bundle for the right-coset action.  This
formulation simultaneously records the kernel and quotient conditions and gives
the representable equivalence `Q ≃ [G/K]`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme

open CategoryTheory.BasedCategory

namespace PrincipalBundleExactSequence

variable {S : Scheme.{u}} (K G Q : Over S)
  [GrpObj K] [GrpObj G] [GrpObj Q]

/-- Fppf exactness of `1 ⟶ K ⟶ G ⟶ Q ⟶ 1`, expressed by saying
that `G ⟶ Q` is a principal `K`-bundle for right multiplication through
`K ⟶ G`. -/
structure Data where
  inclusion : K ⟶ G
  projection : G ⟶ Q
  inclusion_isMonHom : IsMonHom inclusion
  projection_isMonHom : IsMonHom projection
  invariant :
    letI : ModObj K G := ModObj.rightCoset inclusion
    γ[K, G] ≫ projection = snd K G ≫ projection
  flat : Flat projection.left
  surjective : Surjective projection.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation projection.left
  smooth : Smooth projection.left
  torsor :
    letI : ModObj K G := ModObj.rightCoset inclusion
    IsIso (ModObj.torsorMap projection invariant)

variable {K G Q}

namespace Data

attribute [instance] inclusion_isMonHom projection_isMonHom

/-- The kernel quotient map as a principal bundle. -/
noncomputable def bundle (E : Data K G Q) : GlobalPrincipalBundle K Q := by
  letI : ModObj K G := ModObj.rightCoset E.inclusion
  exact
    { P := G
      p := E.projection
      action := inferInstance
      invariant := E.invariant
      flat := E.flat
      surjective := E.surjective
      locallyOfFinitePresentation := E.locallyOfFinitePresentation
      smooth := E.smooth
      torsor := E.torsor }

/-- The homogeneous-space quotient prestack attached to the kernel inclusion. -/
noncomputable abbrev quotientPrestack (E : Data K G Q) :
    BasedCategory (Over S) :=
  ClassifyingStackCartesian.quotientPrestack E.inclusion

variable [Smooth K.hom] [IsAffineHom K.hom]

/-- The quotient map `Q ⟶ [G/K]` classified by the principal bundle
`G ⟶ Q`. -/
noncomputable def quotientFamily (E : Data K G Q) :
    BasedFunctor (overBased Q) E.quotientPrestack := by
  letI : ModObj K G := ModObj.rightCoset E.inclusion
  exact PrincipalBundleQuotient.family E.bundle

/-- The classifying morphism `Q ⟶ BK` of the kernel torsor `G ⟶ Q`. -/
noncomputable def kernelClassifyingFamily (E : Data K G Q) :
    BasedFunctor (overBased Q) (classifyingPrestack K) := by
  letI : ModObj K G := ModObj.rightCoset E.inclusion
  exact E.quotientFamily.comp actionQuotientPrestack.forget

lemma kernelClassifyingFamily_eq (E : Data K G Q) :
    E.kernelClassifyingFamily = PrincipalBundleQuotient.classifyingFamily E.bundle :=
  rfl

/-- Fppf exactness identifies `Q` with the quotient `[G/K]`. -/
theorem quotientFamily_isEquivalence (E : Data K G Q) :
    E.quotientFamily.toFunctor.IsEquivalence := by
  letI : ModObj K G := ModObj.rightCoset E.inclusion
  exact PrincipalBundleQuotient.family_isEquivalence E.bundle

end Data

end PrincipalBundleExactSequence

end AlgebraicGeometry.Scheme
