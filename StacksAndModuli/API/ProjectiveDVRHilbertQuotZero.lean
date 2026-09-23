module

public import StacksAndModuli.API.ProjectiveDVRQuotientClosedFiberSerre
public import StacksAndModuli.API.ProjectiveTwistedFreeUnitIso
public import StacksAndModuli.«Section2.1-Intro».«part2.1.4-hilbert-representability-via-quot»

/-!
# The fixed-polynomial DVR criterion on relative zero-dimensional projective space

The unconditional dimension-zero DVR result for twisted-free Quot transports
across `O(0) ≅ O` to the structure-sheaf Quot functor, and then across the
Hilbert--Quot natural isomorphism to the fixed-polynomial Hilbert functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.Scheme

/-- On relative `P⁰`, restriction from a DVR to any chosen fraction field is
bijective for fixed-polynomial quotients of the structure sheaf. -/
theorem structureSheafQuotFunctorP_map_bijective_isFractionRing_zero
    (S : Scheme.{u}) [IsLocallyNoetherian S] (P : Polynomial ℚ)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (σ : Spec (.of R) ⟶ S) :
    Function.Bijective
      ((quotFunctorP
        (SheafOfModules.unit (projectiveSpaceOver 0 S).ringCatSheaf) P).map
          (Quiver.Hom.op (Over.homMk
            (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl :
            Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) ⟶
              Over.mk σ))) := by
  let j :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) ⟶
        Over.mk σ :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl
  rw [CategoryTheory.Functor.map_bijective_iff_of_iso
    (projectiveSpaceOverUnitQuotFunctorPIso 0 S P) j.op]
  exact quotFunctorP_map_bijective_isFractionRing_zero S 0 1 P R K σ

/-- On relative `P⁰`, restriction from a DVR to any chosen fraction field is
bijective for the fixed-polynomial Hilbert functor. -/
theorem hilbFunctorP_map_bijective_isFractionRing_zero
    (S : Scheme.{u}) [IsLocallyNoetherian S] (P : Polynomial ℚ)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (σ : Spec (.of R) ⟶ S) :
    Function.Bijective
      ((hilbFunctorP 0 S P).map
        (Quiver.Hom.op (Over.homMk
          (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl :
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) ⟶
            Over.mk σ))) := by
  let j :
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ) ⟶
        Over.mk σ :=
    Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap R K))) rfl
  rw [← ULift.map_bijective]
  change Function.Bijective
    ((hilbFunctorP 0 S P ⋙ uliftFunctor.{u + 1, u}).map j.op)
  rw [CategoryTheory.Functor.map_bijective_iff_of_iso
    (hilbStructureSheafQuotientPNatIso 0 S P) j.op]
  exact structureSheafQuotFunctorP_map_bijective_isFractionRing_zero
    S P R K σ

end AlgebraicGeometry.Scheme

end
