module

public import StacksAndModuli.API.PullbackAdjoint
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»

/-!
# The zero twist on relative projective space

The zero twisting sheaf on relative projective space is its structure sheaf.  Consequently
the structure sheaf is a quotient of a one-summand twisted-free sheaf, supplying the printed
presentation hypothesis in the fixed-polynomial Quot theorem when it is specialized to
Hilbert schemes.

Main declarations:

* `AlgebraicGeometry.Scheme.projectiveSpaceOverTwistZeroIso`;
* `AlgebraicGeometry.Scheme.projectiveSpaceOverStructureSheafQuotientMap`;
* `AlgebraicGeometry.Scheme.Modules.unit_isQuotientOfTwistedFree_projectiveSpaceOver`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The zero twisting sheaf on relative projective space is canonically isomorphic to
its structure sheaf. -/
noncomputable def projectiveSpaceOverTwistZeroIso (n : ℕ) (S : Scheme.{u}) :
    projectiveSpaceOverTwist n S 0 ≅
      SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf := by
  let p : projectiveSpaceOver n S ⟶ projectiveSpace n := Limits.pullback.snd
      (specULiftZIsTerminal.from S)
      (specULiftZIsTerminal.from (projectiveSpace n))
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom) :=
    isIso_pullbackObjUnitToUnit p
  exact ((Modules.pullback p).mapIso
      (ProjectiveSpectrum.Twist.zeroIso
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)))) ≪≫
    asIso (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom)

/-- The canonical epimorphism from a one-summand zero-twisted free sheaf onto the
structure sheaf of relative projective space. -/
noncomputable def projectiveSpaceOverStructureSheafQuotientMap
    (n : ℕ) (S : Scheme.{u}) :
    (∐ fun _ : ULift.{u} (Fin 1) ↦ projectiveSpaceOverTwist n S 0) ⟶
      SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf :=
  (coproductUniqueIso
    (fun _ : ULift.{u} (Fin 1) ↦ projectiveSpaceOverTwist n S 0)).hom ≫
      (projectiveSpaceOverTwistZeroIso n S).hom

instance projectiveSpaceOverStructureSheafQuotientMap_epi
    (n : ℕ) (S : Scheme.{u}) :
    Epi (projectiveSpaceOverStructureSheafQuotientMap n S) := by
  dsimp only [projectiveSpaceOverStructureSheafQuotientMap]
  infer_instance

/-- The structure sheaf of relative projective space is a quotient of a finite
twisted-free sheaf: take one copy of `𝒪(0)`. -/
theorem Modules.unit_isQuotientOfTwistedFree_projectiveSpaceOver
    (n : ℕ) (S : Scheme.{u}) :
    Modules.IsQuotientOfTwistedFree
      (SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf) := by
  refine ⟨0, 1, ?_⟩
  simpa using
    (show ∃ p : (∐ fun _ : ULift.{u} (Fin 1) ↦
        projectiveSpaceOverTwist n S 0) ⟶
          SheafOfModules.unit (projectiveSpaceOver n S).ringCatSheaf,
        Epi p from
      ⟨projectiveSpaceOverStructureSheafQuotientMap n S, inferInstance⟩)

end AlgebraicGeometry.Scheme

end
