module

public import StacksAndModuli.API.NormalizationComponents

/-!
# Reduced closed subschemes with the same range

Two closed immersions with reduced sources and the same underlying image define the
same reduced closed subscheme.  This file packages the resulting canonical
isomorphism over the ambient scheme.

## Main results

* `AlgebraicGeometry.Scheme.Hom.ker_eq_of_isClosedImmersion_of_range_eq`: equality
  of the defining radical ideal sheaves.
* `AlgebraicGeometry.Scheme.isoOfReducedClosedImmersionsRangeEq`: the canonical
  isomorphism of the two sources.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- Closed immersions with reduced sources and the same underlying range have the
same kernel ideal sheaf on the target. -/
theorem Hom.ker_eq_of_isClosedImmersion_of_range_eq
    {X Y Z : Scheme.{u}} [IsReduced X] [IsReduced Y]
    (i : X ⟶ Z) (j : Y ⟶ Z)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (h : Set.range i = Set.range j) : i.ker = j.ker := by
  rw [← i.radical_ker_eq_self_of_isReduced,
    ← j.radical_ker_eq_self_of_isReduced,
    ← IdealSheafData.vanishingIdeal_support,
    ← IdealSheafData.vanishingIdeal_support]
  congr 1
  apply Closeds.ext
  rw [i.support_ker, j.support_ker, h]

/-- Two closed immersions with reduced sources and the same underlying range are
canonically isomorphic over their common target. -/
noncomputable def isoOfReducedClosedImmersionsRangeEq
    {X Y Z : Scheme.{u}} [IsReduced X] [IsReduced Y]
    (i : X ⟶ Z) (j : Y ⟶ Z)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (h : Set.range i = Set.range j) : X ≅ Y := by
  have hker := i.ker_eq_of_isClosedImmersion_of_range_eq j h
  let f : X ⟶ Y := IsClosedImmersion.lift j i hker.ge
  have hf : f ≫ j = i := IsClosedImmersion.lift_fac j i hker.ge
  let _ : IsIso f := IsClosedImmersion.isIso_of_ker_eq i j f hf hker
  exact asIso f

/-- The canonical isomorphism between reduced closed subschemes with the same range
commutes with their maps to the target. -/
@[reassoc (attr := simp)]
theorem isoOfReducedClosedImmersionsRangeEq_hom_comp
    {X Y Z : Scheme.{u}} [IsReduced X] [IsReduced Y]
    (i : X ⟶ Z) (j : Y ⟶ Z)
    [IsClosedImmersion i] [IsClosedImmersion j]
    (h : Set.range i = Set.range j) :
    (isoOfReducedClosedImmersionsRangeEq i j h).hom ≫ j = i :=
  IsClosedImmersion.lift_fac j i
    (i.ker_eq_of_isClosedImmersion_of_range_eq j h).ge

end AlgebraicGeometry.Scheme

end
