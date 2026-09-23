module

public import StacksAndModuli.«Section6.4-Stack».«part6.4.1-algebraicity-and-boundedness-of-mgbar»

/-!
# An interface to families of stable curves

`StableCurveFamily g S` bundles an unpointed stable family of genus `g` over `S`.
Its total space may be an algebraic space. Each geometric fibre is presented by a
scheme; `geometricFiber` chooses such a presentation and exposes its stability and genus.
The choice does not assert that the total space is a scheme.

`toModuli` regards a family as an object of the existing moduli category. Properties of
that category over `Spec ℤ` are stated through the absolute predicates of
`StacksAndModuli/API/BasedCategoryAbsoluteProperties.lean`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.BasedCategory

universe u

namespace AlgebraicGeometry

/-- A stable, unpointed, genus-`g` family over a scheme, with algebraic-space total space. -/
abbrev StableCurveFamily (g : ℕ) (S : Scheme.{u}) :=
  {F : MarkedAlgebraicSpaceOver (Fin 0) S // IsFamilyOfStableCurvesOfGenus g F}

namespace StableCurveFamily

variable {g : ℕ} {S : Scheme.{u}} (F : StableCurveFamily g S)

/-- The same family regarded as an object of the moduli category. -/
def toModuli : (moduliOfStableCurves g).obj :=
  ⟨S, F.val, F.property⟩

/-- The moduli projection sends a family over `S` to `S`. -/
@[simp] theorem base_toModuli : (moduliOfStableCurves g).p.obj F.toModuli = S := rfl

/-- The structure morphism of a stable family is proper. -/
theorem proper : BasedFunctor.IsProper F.val.toBaseFunctor :=
  F.property.1.isProper

/-- The structure morphism of a stable family is flat. -/
theorem flat : BasedFunctor.Flat F.val.toBaseFunctor :=
  F.property.1.flat

/-- The structure morphism of a stable family is finitely presented. -/
theorem finitePresentation : BasedFunctor.FinitePresentation F.val.toBaseFunctor :=
  F.property.1.finitePresentation

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Choose a scheme presentation of the geometric fibre at a geometric point. -/
def geometricFiberPresentation (s : Spec (CommRingCat.of k) ⟶ S) :
    F.val.PresentedGeometricFiber k s :=
  Classical.choose (F.property.2 k s)

/-- The geometric fibre, presented as a scheme over its algebraically closed field. -/
abbrev geometricFiber (s : Spec (CommRingCat.of k) ⟶ S) : Scheme.{u} :=
  (F.geometricFiberPresentation s).scheme

instance geometricFiber_over (s : Spec (CommRingCat.of k) ⟶ S) :
    (F.geometricFiber s).Over (Spec (CommRingCat.of k)) :=
  ⟨(F.geometricFiberPresentation s).toBase⟩

/-- Every geometric fibre is a stable curve of the specified genus. -/
theorem geometricFiber_stable (s : Spec (CommRingCat.of k) ⟶ S) :
    Scheme.IsStableCurveOfGenusOver k g (F.geometricFiber s) := by
  exact (Scheme.isStableNMarkedCurveOfGenusOver_zero_iff
    (F.geometricFiberPresentation s).marking).mp
      (Classical.choose_spec (F.property.2 k s))

/-- The genus of every geometric fibre is the genus of the family. -/
theorem geometricFiber_genus (s : Spec (CommRingCat.of k) ⟶ S) :
    Scheme.genusOver k (F.geometricFiber s) = g :=
  (F.geometricFiber_stable s).genus_eq

end StableCurveFamily


end AlgebraicGeometry

end
