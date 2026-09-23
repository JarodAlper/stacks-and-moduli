module

public import StacksAndModuli.API.SheafCohomologyOpen
public import StacksAndModuli.API.SheafSlicePullbackExact

/-!
# Sheaf cohomology on an open object

Extension from a slice site preserves monomorphisms, so the derived adjunction
comparison identifies local sheaf cohomology at an object with global sheaf
cohomology on the corresponding slice site in every degree.  This file packages
that unconditional comparison and its naturality in the coefficient sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian
open Opposite

universe u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
variable [HasSheafify J AddCommGrpCat.{u}]
variable (F : Sheaf J AddCommGrpCat.{u}) (U : C)

/-- Local sheaf cohomology at an object is additively equivalent, in every
degree, to global sheaf cohomology of the restricted sheaf on the slice site. -/
noncomputable def HPrimeOpenEquivH (n : ℕ) :
    F.H' n U ≃+ (F.over U).H n :=
  HPrimeOpenEquivH_of_preservesMonomorphisms J F U n

/-- The all-degree local-to-slice cohomology equivalence is natural in the
coefficient sheaf. -/
theorem HPrimeOpenEquivH_naturality
    {F G : Sheaf J AddCommGrpCat.{u}} (f : F ⟶ G) (U : C) (n : ℕ)
    (x : F.H' n U) :
    H.map ((J.overPullback AddCommGrpCat.{u} U).map f) n
        (HPrimeOpenEquivH J F U n x) =
      HPrimeOpenEquivH J G U n
        (x.comp (Ext.mk₀ f) (add_zero n)) := by
  exact HPrimeOpenEquivH_of_preservesMonomorphisms_naturality J f U n x

/-- Vanishing of local cohomology at an object is equivalent, in every degree,
to vanishing of global cohomology on the corresponding slice site. -/
theorem subsingleton_HPrime_open_iff (n : ℕ) :
    Subsingleton (F.H' n U) ↔ Subsingleton ((F.over U).H n) :=
  (HPrimeOpenEquivH J F U n).toEquiv.subsingleton_congr

end CategoryTheory.Sheaf
