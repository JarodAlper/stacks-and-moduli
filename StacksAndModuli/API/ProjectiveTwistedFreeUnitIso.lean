module

public import StacksAndModuli.API.ProjectiveSpaceTwistZero
public import StacksAndModuli.API.ProjectiveSpaceTwistedFree
public import StacksAndModuli.API.QuotFunctorIso

/-!
# The one-summand zero-twisted ambient sheaf

The twisted-free sheaf with one summand and twist zero is canonically
isomorphic to the structure sheaf.  Consequently its fixed-polynomial Quot
functor is naturally isomorphic to the structure-sheaf Quot functor used for
Hilbert schemes.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme

/-- The canonical quotient map from one copy of `O(0)` to the structure sheaf
is an isomorphism. -/
instance projectiveSpaceOverStructureSheafQuotientMap_isIso
    (n : ℕ) (S : Scheme.{u}) :
    IsIso (projectiveSpaceOverStructureSheafQuotientMap n S) := by
  dsimp only [projectiveSpaceOverStructureSheafQuotientMap]
  exact IsIso.comp_isIso

/-- The one-summand, zero-twisted free sheaf is the structure sheaf. -/
noncomputable def projectiveSpaceOverTwistedFreeZeroOneIsoUnit
    (n : ℕ) (S : Scheme.{u}) :
    projectiveSpaceOverTwistedFree n S 0 1 ≅
      SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf := by
  simpa [projectiveSpaceOverTwistedFree] using
    asIso (projectiveSpaceOverStructureSheafQuotientMap n S)

/-- The fixed-polynomial Quot functor of the structure sheaf is naturally
isomorphic to that of the one-summand, zero-twisted free sheaf. -/
noncomputable def projectiveSpaceOverUnitQuotFunctorPIso
    (n : ℕ) (S : Scheme.{u}) (P : Polynomial ℚ) :
    quotFunctorP
        (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf) P ≅
      quotFunctorP (projectiveSpaceOverTwistedFree n S 0 1) P :=
  quotFunctorPIsoOfIso
    (projectiveSpaceOverTwistedFreeZeroOneIsoUnit n S).hom P

end AlgebraicGeometry.Scheme

end
