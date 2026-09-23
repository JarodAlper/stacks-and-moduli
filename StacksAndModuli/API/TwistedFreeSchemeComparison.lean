module

public import StacksAndModuli.API.TwistedFreeGlobalSectionsHomogeneous
public import StacksAndModuli.API.ProjectiveGradedSchemeComparison
public import StacksAndModuli.API.ProjectiveGradedRelativeExists

/-!
# The graded–scheme comparison for a twisted-free ambient sheaf

W4 of `PLAN-hilbert-quot.md`, for the ambient sheaf that Theorem 2.4.5 needs.  This file
assembles `RelativeCohomology.SchemeGlobalSectionsComparison` for

`M = ⨁_r S_R(-l)`  and  `Q = 𝒪(-l)^{⊕ULift (Fin r)}`

from the two comparisons proved in
`StacksAndModuli/API/TwistedFreeGlobalSectionsHomogeneous.lean`:

* `twistedFreeGradedGlobalSectionsEquiv` — over the base ring;
* `twistedFreeBaseChangeGlobalSectionsEquiv` — after base change, in particular to a
  residue field.

Both hold in the range `d ≥ l`, which is exactly what the structure's `bound` field asks for.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- **The `H⁰` comparison for a twisted-free ambient sheaf**: `W4` for
`Q = 𝒪(-l)^{⊕r}`. -/
noncomputable def twistedFreeSchemeGlobalSectionsComparison
    (n : ℕ) (R : Type u) [CommRing R] [IsNoetherianRing R] (l : ℤ) (r : ℕ) :
    (RelativeCohomology.cech R).SchemeGlobalSectionsComparison
      (((GradedModule.structureModule R n).twist (-l)).pow r)
      (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) where
  bound := l.toNat
  globalSectionsIso d hd := by
    have he : ((((d : ℤ) - l).toNat : ℕ) : ℤ) = (d : ℤ) - l := Int.toNat_of_nonneg (by omega)
    exact twistedFreeGradedGlobalSectionsEquiv n R l r d (((d : ℤ) - l).toNat) he
  fibreGlobalSectionsIso K _ f d hd := by
    letI : Algebra R K := f.toAlgebra
    have he : ((((d : ℤ) - l).toNat : ℕ) : ℤ) = (d : ℤ) - l := Int.toNat_of_nonneg (by omega)
    exact twistedFreeBaseChangeGlobalSectionsEquiv n R K l r d (((d : ℤ) - l).toNat) he

/-- **The twisted-free ambient sheaf has eventual finite-projective global sections whose
formation commutes with base change.**  This is the scheme-level output of `W1`–`W4` for
`Q = 𝒪(-l)^{⊕r}`, and it is an API construction used in the DVR half of
Proposition 2.4.2, through the
`…_of_eventualGlobalSectionsBaseChange` route of §2.4. -/
noncomputable def twistedFreeHasEventualFiniteProjectiveGlobalSectionsBaseChange
    (n : ℕ) (R : Type u) [CommRing R] [IsNoetherianRing R] (l : ℤ) (r : ℕ) :
    Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange
      (∐ fun _ : ULift.{u} (Fin r) =>
        Scheme.projectiveSpaceOverTwist n (Spec (.of R)) (-l)) := by
  let Crel := RelativeCohomology.cech R
  have hM : Crel.IsCoherent (((GradedModule.structureModule R n).twist (-l)).pow r) :=
    Crel.isCoherent_pow (Crel.isCoherent_twist Crel.isCoherent_structureModule (-l)) r
  have hflat : Crel.IsFlat (((GradedModule.structureModule R n).twist (-l)).pow r) :=
    Crel.isFlat_pow (Crel.isFlat_twist Crel.isFlat_structureModule (-l)) r
  exact (twistedFreeSchemeGlobalSectionsComparison n R l r
    ).toHasEventualFiniteProjectiveGlobalSectionsBaseChange hM hflat

end AlgebraicGeometry.ProjectiveSpace

end

end
