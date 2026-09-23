module

public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.6-isom-presheaves»
public import StacksAndModuli.API.PrincipalBundleInductionQuotientFiber
public import StacksAndModuli.API.PrincipalBundleExactSequence

/-!
# Cartesian diagrams of classifying prestacks

This module develops `exer:classifying-stack-cartesian-diagrams` (Exercise
3.4.40) of §3.4 (Prestacks) of *Stacks and Moduli*,
section label `sec:prestacks`.

The contracted product is represented by `PrincipalBundleInduction.EffectiveInduction`:
its fpqc-local transition datum and all functoriality and uniqueness assertions are
proved in the API.  For any such effective induction, the canonical comparison
`[G/H] ⟶ BH ×_BG S` is fully faithful.  Its essential-surjectivity assertion is the
remaining geometric effectivity step needed to close part (b).  The exact-sequence
API also supplies the quotient identification `Q ≃ [G/K]` used in part (c).

Main declarations:

* `ClassifyingStackCartesian.inductionMorphism`: part (a)'s extension-of-structure-group
  morphism from effective contracted products;
* `PrincipalBundleExactSequence.exactSequence_quotient_isEquivalence`: the quotient
  equivalence used in part (c).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ExerClassifyingStackCartesianDiagrams

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonObj
open scoped CategoryTheory.Obj CategoryTheory.ModObj

universe u

namespace AlgebraicGeometry.Scheme

open CategoryTheory.BasedCategory

namespace ClassifyingStackCartesian

variable {S : Scheme.{u}} {H G : Over S} [GrpObj H] [GrpObj G]
  (phi : H ⟶ G) [IsMonHom phi]
  [Smooth H.hom] [IsAffineHom H.hom] [Smooth G.hom] [IsAffineHom G.hom]

/-- **Exercise 3.4.40** (`exer:classifying-stack-cartesian-diagrams`) (part (a)):
an effective contracted-product construction along `H ⟶ G` defines the morphism
of prestacks `BH ⟶ BG` that extends the structure group of a principal bundle. -/
noncomputable abbrev inductionMorphism
    (I : PrincipalBundleInduction.EffectiveInduction phi) :
    classifyingPrestack H ⥤ᵇ classifyingPrestack G :=
  I.toBasedFunctor

/-- Alternative API construction for Exercise 3.4.40 (part (a),
effective-descent interface): compatible effective fpqc gluings of all local
contracted-product diagrams supply the extension-of-structure-group morphism. -/
noncomputable def inductionMorphismOfCocones
    (hC : ∀ x : ClassifyingObj H,
      Nonempty (PrincipalBundleInduction.Cocone phi x.bundle)) :
    classifyingPrestack H ⥤ᵇ classifyingPrestack G :=
  (PrincipalBundleInduction.effectiveInductionOfCocones phi hC).toBasedFunctor

/-- Background comparison for Exercise 3.4.40 (part (b),
the comparison): the canonical comparison from the homogeneous-space quotient to the
fiber of extension of structure group over the trivial `G`-bundle. -/
noncomputable abbrev homogeneousSpaceComparison
    (I : PrincipalBundleInduction.EffectiveInduction phi) :
    quotientPrestack phi ⥤ᵇ
      fiberProduct I.toBasedFunctor (pointFamily (G := G)) :=
  quotientFiberComparison phi I

/-- Partial proof lemma for Exercise 3.4.40 (part (b),
fully faithful half): morphisms of `H`-bundles compatible after induction with the
chosen trivializations are exactly morphisms in `[G/H]`. -/
theorem homogeneousSpaceComparison_full_and_faithful
    (I : PrincipalBundleInduction.EffectiveInduction phi) :
    (homogeneousSpaceComparison phi I).toFunctor.Full ∧
      (homogeneousSpaceComparison phi I).toFunctor.Faithful :=
  ⟨inferInstance, inferInstance⟩

end ClassifyingStackCartesian

namespace PrincipalBundleExactSequence

variable {S : Scheme.{u}} {K G Q : Over S}
  [GrpObj K] [GrpObj G] [GrpObj Q]
  [Smooth K.hom] [IsAffineHom K.hom]

/-- **Exercise 3.4.40** (`exer:classifying-stack-cartesian-diagrams`) (part (c),
quotient identification): the quotient identification used for the left cartesian
square: an fppf exact sequence `1 ⟶ K ⟶ G ⟶ Q ⟶ 1` identifies `Q` with `[G/K]`. -/
theorem exactSequence_quotient_isEquivalence
    (E : Data K G Q) : E.quotientFamily.toFunctor.IsEquivalence :=
  E.quotientFamily_isEquivalence

end PrincipalBundleExactSequence

end AlgebraicGeometry.Scheme

end ExerClassifyingStackCartesianDiagrams
