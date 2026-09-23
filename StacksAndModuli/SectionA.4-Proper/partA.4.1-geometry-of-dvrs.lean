module

public import StacksAndModuli.API.DVRSpecialization

/-!
# Properness and the valuative criterion: geometry of DVRs

This module corresponds to the geometry-of-DVRs proposition in §A.4 (Properness and
the Valuative Criterion) of Appendix A of *Stacks and Moduli*,
section label `sec:properness-schemes`.

Main result:
- `AlgebraicGeometry.Scheme.Hom.dvrRealizesSpecializations_of_finiteType`
  (**Proposition A.4.4**, `prop:geometry-dvrs`).
-/

@[expose] public section

section PropGeometryDvrs

open CategoryTheory AlgebraicGeometry

universe u

/-- **Proposition A.4.4** (`prop:geometry-dvrs`): a finite-type morphism of
noetherian schemes realizes every specialization from an image point by a
commutative valuative square over a DVR, with its generic point mapping to the
prescribed source point and its closed point mapping to the prescribed target
specialization.

Mathlib expresses "finite type" as the conjunction of `LocallyOfFiniteType`
and `QuasiCompact`. -/
theorem AlgebraicGeometry.Scheme.Hom.dvrRealizesSpecializations_of_finiteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    DVRRealizesSpecializations f :=
  f.dvrRealizesSpecializations_of_locallyOfFiniteType

end PropGeometryDvrs
