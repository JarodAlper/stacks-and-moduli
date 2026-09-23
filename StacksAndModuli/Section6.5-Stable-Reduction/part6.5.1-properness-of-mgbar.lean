module

public import StacksAndModuli.«Section6.4-Stack».«part6.4.1-algebraicity-and-boundedness-of-mgbar»

/-!
# Properness of the unpointed stable-curve stack

This module records the unpointed separatedness and properness conclusions from
§6.5 (Stable reduction),
section `sec:stable-reduction`.

The final proof uses the library's standard definition: proper means universally
closed, separated, and of finite type. Boundedness supplies finite type; uniqueness
of stable limits supplies separatedness; existence of stable limits supplies universal
closedness. The latter two geometric inputs are recorded obligations below, and
boundedness and the Deligne–Mumford assertion remain obligations in §6.4.

All properties are stated for the moduli category `moduliOfStableCurves g` itself and are
understood over `Spec ℤ`, the final scheme, through the absolute predicates of
`StacksAndModuli/API/BasedCategoryAbsoluteProperties.lean` (properties of the structure morphism
`𝒳.toBase` to `Sch = Sch/Spec ℤ`).

These unpointed supporting statements do not formalize the marked or coarse-space
clauses of Theorem 6.5.23. In particular, the short final proof is not axiom-clean.

## Supporting special cases

* `AlgebraicGeometry.isSeparated_moduliOfStableCurves`;
* `AlgebraicGeometry.universallyClosed_moduliOfStableCurves`;
* `AlgebraicGeometry.isProper_moduliOfStableCurves`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry

section PropMgSeparated

/-- Partial result toward Proposition 6.5.20: the unpointed stack of stable curves of
genus at least two is separated over `Spec ℤ`.

Recorded obligation: extend isomorphisms uniquely across stable limits and apply the
valuative criterion for the diagonal. -/
theorem isSeparated_moduliOfStableCurves (g : ℕ) (hg : 2 ≤ g) :
    BasedCategory.IsSeparated (moduliOfStableCurves.{u} g) := by
  sorry

end PropMgSeparated

section ThmMgIsProper

/-- Supporting universal-closedness consequence of stable reduction for Theorem 6.5.23:
the unpointed stack of stable curves of genus at least two is universally closed over
`Spec ℤ`.

Recorded obligation: existence of stable limits after extension of valuation rings,
together with the stack valuative criterion. The statement is over the integers, as
in the book; the book proves its stable-reduction input only in characteristic zero. -/
theorem universallyClosed_moduliOfStableCurves (g : ℕ) (hg : 2 ≤ g) :
    BasedCategory.UniversallyClosed (moduliOfStableCurves.{u} g) := by
  sorry

/-- Partial result toward Theorem 6.5.23: the unpointed stack of stable curves of genus
at least two is proper over `Spec ℤ`.

This uses the standard properness predicate. Its geometric inputs are the recorded
boundedness, separatedness, and stable-reduction obligations, not a finite-cover
replacement for properness. -/
theorem isProper_moduliOfStableCurves (g : ℕ) (hg : 2 ≤ g) :
    BasedCategory.IsProper (moduliOfStableCurves.{u} g) :=
  ⟨universallyClosed_moduliOfStableCurves g hg,
    isSeparated_moduliOfStableCurves g hg,
    finiteType_moduliOfStableCurves g hg⟩

end ThmMgIsProper

end AlgebraicGeometry

end
