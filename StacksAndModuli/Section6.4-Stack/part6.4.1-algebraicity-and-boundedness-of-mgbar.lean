module

public import StacksAndModuli.API.AlgebraicSpaceCartesianFamily
public import StacksAndModuli.API.AlgebraicSpaceFamilyBaseChange
public import StacksAndModuli.API.BasedCategoryAbsoluteProperties
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.2-deligne-mumford-and-algebraic-stacks»
public import StacksAndModuli.«Section6.3-Stable».«part6.3.5-families-of-stable-curves»

/-!
# The stack of stable curves

This module formalizes the unpointed material from the subsection “Algebraicity and
boundedness of `\overline{\mathcal M}_{g,n}`” in §6.4 (The stack of all curves) of
*Stacks and Moduli*. Formalization state per
label: see this folder's `STATUS.md`.

The book allows the total space of a family of curves to be an algebraic space.  Thus the
objects of `moduliOfStableCurves g` use `MarkedAlgebraicSpaceOver (Fin 0) S`, rather than
the computationally stronger scheme-total-space specialization.  Morphisms are cartesian
squares over morphisms of base schemes.

The unpointed moduli construction and the Deligne–Mumford and finite-type conclusions are
included as inputs to unpointed properness. Properties over `Spec ℤ` are stated for the
moduli category itself, through the absolute predicates of
`StacksAndModuli/API/BasedCategoryAbsoluteProperties.lean` (properties of the structure morphism
`𝒳.toBase` to `Sch = Sch/Spec ℤ`). They are useful special cases, but no declaration here
yet states Equation 6.4.14 or Theorem 6.4.16 at the book's full `(g,n)`-pointed
generality.

## Supporting special cases

- `AlgebraicGeometry.moduliOfStableCurves`: the unpointed moduli category
  `\overline{\mathcal M}_g`.
- `AlgebraicGeometry.moduliOfStableCurves_isFiberedInGroupoids`: it is a prestack for
  every `g`, its cartesian lifts being base changes of families.
- `AlgebraicGeometry.isDeligneMumfordStack_moduliOfStableCurves`: for `g ≥ 2`, this
  moduli category is a Deligne–Mumford stack.
- `AlgebraicGeometry.finiteType_moduliOfStableCurves`: boundedness, i.e. finite type over
  `Spec ℤ`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CategoryTheory.BasedCategory

universe u

namespace AlgebraicGeometry

section EqnInclusionsOfStacksOfCurves

/-- Background definition used toward Equation 6.4.14 (unpointed stable-curve moduli
category): `moduliOfStableCurves g`, denoted
`\overline{\mathcal M}_g`, has as objects over a scheme `S` the proper, flat, finitely
presented algebraic-space families whose geometric fibres are stable curves of genus `g`.
Its morphisms are cartesian squares over morphisms of base schemes. The equation itself is
the inclusion chain for all `n`-pointed curve substacks. -/
abbrev moduliOfStableCurves (g : ℕ) : BasedCategory Scheme.{u} :=
  moduliOfAllCurves
    (fun _ F ↦ IsFamilyOfStableCurvesOfGenus g F)

/-- Background result for Equation 6.4.14: being a family of stable curves of genus `g` is
stable under arbitrary base change.  Properness, flatness and finite presentation are
preserved by base change, and every geometric fibre of a base change is a geometric fibre
of the original family.

The fibre clauses are discharged by
`AlgebraicGeometry.MarkedAlgebraicSpaceOver.hasPresentedGeometricFibers_unpointedBaseChange`,
which is proved by pasting the base-change and fibre pullback squares.  The three
conditions on the structure morphism are the recorded obligations
`AlgebraicGeometry.MarkedAlgebraicSpaceOver.isProper_unpointedBaseChange`,
`…flat_unpointedBaseChange` and `…finitePresentation_unpointedBaseChange` of
`StacksAndModuli/API/AlgebraicSpaceFamilyBaseChange.lean`. -/
theorem isFamilyOfStableCurvesOfGenus_stableUnderBaseChange (g : ℕ) :
    UnpointedAlgebraicSpaceFamilyProperty.StableUnderBaseChange.{u}
      (fun _ F ↦ IsFamilyOfStableCurvesOfGenus g F) := by
  intro S T F f hF
  obtain ⟨⟨hproper, hflat, hfp, hcurve⟩, hstable⟩ := hF
  exact ⟨⟨F.isProper_unpointedBaseChange f hproper,
      F.flat_unpointedBaseChange f hflat,
      F.finitePresentation_unpointedBaseChange f hfp,
      MarkedAlgebraicSpaceOver.hasPresentedGeometricFibers_unpointedBaseChange hcurve f⟩,
    MarkedAlgebraicSpaceOver.hasPresentedGeometricFibers_unpointedBaseChange hstable f⟩

/-- Background instance for Equation 6.4.14: `\overline{\mathcal M}_g` is fibered in
groupoids over schemes, its cartesian lifts being base changes of families.  This holds
for every `g`, with no stability bound, and it is what lets properties of the moduli
category be stated at all. -/
instance moduliOfStableCurves_isFiberedInGroupoids (g : ℕ) :
    (moduliOfStableCurves.{u} g).p.IsFiberedInGroupoids :=
  isFiberedInGroupoids_moduliOfAllCurves
    (isFamilyOfStableCurvesOfGenus_stableUnderBaseChange g)

end EqnInclusionsOfStacksOfCurves

section ThmMgnbarIsSmoothDM

/-- Partial result toward Theorem 6.4.16 (unpointed Deligne–Mumford clause): if `g ≥ 2`,
then `\overline{\mathcal M}_g` is a Deligne–Mumford stack.

The non-emptiness, smoothness, and dimension clauses, and all marked cases,
are not stated here. Finite type is recorded separately below. -/
theorem isDeligneMumfordStack_moduliOfStableCurves (g : ℕ) (hg : 2 ≤ g) :
    IsDeligneMumfordStack (moduliOfStableCurves.{u} g) := by
  sorry

/-- Partial result toward Theorem 6.4.16: boundedness and local finite presentation
make the unpointed stable-curve moduli stack `\overline{\mathcal M}_g` of finite type over
`Spec ℤ`.

Recorded obligation: construct the bounded pluricanonical Hilbert presentation. -/
theorem finiteType_moduliOfStableCurves (g : ℕ) (hg : 2 ≤ g) :
    BasedCategory.FiniteType (moduliOfStableCurves.{u} g) := by
  sorry

end ThmMgnbarIsSmoothDM

end AlgebraicGeometry
