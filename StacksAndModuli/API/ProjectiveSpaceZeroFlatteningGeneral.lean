module

public import StacksAndModuli.API.ProjectiveSpaceZeroFlattening
public import StacksAndModuli.API.ProjectiveSpaceZeroEmptyQuot

/-!
# Projective flattening on projective zero-space for every polynomial

Over a nonempty base, a Hilbert polynomial on relative projective zero-space is a
constant polynomial with a natural value.  Thus the constant-polynomial case is the
rank condition proved in `ProjectiveSpaceZeroFlattening.lean`, while every other
polynomial gives a functor supported only on empty test schemes.  The latter functor
is the rank-zero flattening stratum of the structure sheaf: on a nonempty scheme the
structure sheaf has rank one, and on an empty scheme every rank condition is vacuous.

The final theorem gives a finite-rank presentation over an arbitrary base, for every
polynomial and every finitely presented quasicoherent sheaf on `P^0`.

Main declaration:

* `AlgebraicGeometry.Scheme.Modules.projectiveFlatteningHasFiniteRankPresentation_zero_all`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {T : Scheme.{u}}

/-- A rank-zero structure sheaf forces a scheme to be empty. -/
theorem isEmpty_of_isProjectiveOfRank_zero_unit
    {A : Scheme.{u}}
    (h : IsProjectiveOfRank 0 (SheafOfModules.unit A.ringCatSheaf)) :
    IsEmpty A := by
  constructor
  intro a
  obtain ⟨U, haU, _hfin, _hproj, hrank⟩ := h a
  let p : PrimeSpectrum Γ(A, U.1) :=
    U.2.isoSpec.hom.base ⟨a, haU⟩
  let _ := p.nontrivial
  have hp := hrank p
  change Module.rankAtStalk (R := Γ(A, U.1)) Γ(A, U.1) p = 0 at hp
  rw [Module.rankAtStalk_self] at hp
  have hone : (1 : ℕ) = 0 := by simpa only [Pi.one_apply] using hp
  exact Nat.one_ne_zero hone

/-- If the pullback of the structure sheaf has rank zero, the source scheme is
empty. -/
theorem isEmpty_of_isProjectiveOfRank_zero_pullbackUnit
    (A : Over T)
    (h : IsProjectiveOfRank 0
      ((pullback A.hom).obj (SheafOfModules.unit T.ringCatSheaf))) :
    IsEmpty A.left := by
  letI : IsIso
      (SheafOfModules.pullbackObjUnitToUnit A.hom.toRingCatSheafHom) :=
    isIso_pullbackObjUnitToUnit A.hom
  let e : (pullback A.hom).obj (SheafOfModules.unit T.ringCatSheaf) ≅
      SheafOfModules.unit A.left.ringCatSheaf :=
    asIso (SheafOfModules.pullbackObjUnitToUnit A.hom.toRingCatSheafHom)
  exact isEmpty_of_isProjectiveOfRank_zero_unit (h.of_iso e)

/-- Over an empty base, a projective zero-space family has every fibrewise Hilbert
polynomial, since there are no field-valued points. -/
theorem hasFiberwiseHilbertPolynomial_zero_of_isEmpty
    {A : Scheme.{u}} [IsEmpty A]
    (Q : (Scheme.projectiveSpaceOver 0 A).Modules) (P : Polynomial ℚ) :
    Scheme.HasFiberwiseHilbertPolynomial Q P := by
  intro K hK s
  letI : Field K := hK.toField
  letI : IsEmpty (Spec K) := s.base.hom.1.isEmpty
  exact isEmptyElim (Classical.arbitrary (Spec K))

variable (Q : (Scheme.projectiveSpaceOver 0 T).Modules) [Q.IsQuasicoherent]

/-- A rank-zero point for the structure sheaf has empty source, and hence gives a
point of every projective zero-space flattening functor. -/
noncomputable def projectiveFlatteningZeroPointOfUnitRankZeroPoint
    (_hfp : Q.IsFinitePresentation) (P : Polynomial ℚ) (A : Over T)
    (x : (flatRankFunctorOver (SheafOfModules.unit T.ringCatSheaf) 0).obj (op A)) :
    (projectiveFlatteningFunctor 0 Q (P := P)).obj (op A) := by
  have hfpUnit : (SheafOfModules.unit T.ringCatSheaf).IsFinitePresentation :=
    unit_isFinitePresentation_of_globalPresentation T
  have hRankPull : IsProjectiveOfRank 0
      ((pullback A.hom).obj (SheafOfModules.unit T.ringCatSheaf)) :=
    (locallyFactors_affineStratum_iff_isProjectiveOfRank
      (SheafOfModules.unit T.ringCatSheaf) hfpUnit 0 A).mp x.down.down
  letI : IsEmpty A.left :=
    isEmpty_of_isProjectiveOfRank_zero_pullbackUnit A hRankPull
  let QA := projectiveFamilyAt 0 Q A
  letI : IsEmpty (Scheme.projectiveSpaceOver 0 A.left) :=
    (Scheme.projectiveSpaceOverπ 0 A.left).base.hom.1.isEmpty
  exact ULift.up (PLift.up ⟨flatOver_of_isEmpty QA _,
    hasFiberwiseHilbertPolynomial_zero_of_isEmpty QA P⟩)

/-- If `P` is not a natural constant, a point of the corresponding projective
zero-space flattening functor has empty source and therefore gives the rank-zero
structure-sheaf condition. -/
noncomputable def unitRankZeroPointOfProjectiveFlatteningZeroPoint
    (_hfp : Q.IsFinitePresentation) (P : Polynomial ℚ)
    (hP : ∀ q : ℕ, P ≠ Polynomial.C (q : ℚ)) (A : Over T)
    (x : (projectiveFlatteningFunctor 0 Q (P := P)).obj (op A)) :
    (flatRankFunctorOver (SheafOfModules.unit T.ringCatSheaf) 0).obj (op A) := by
  have hne : ¬ Nonempty A.left := by
    intro hA
    letI : Nonempty A.left := hA
    obtain ⟨q, hq⟩ := Scheme.HasFiberwiseHilbertPolynomial.zero_eq_C_of_nonempty
      (projectiveFamilyAt 0 Q A) P x.down.down.2
    exact hP q hq
  letI : IsEmpty A.left := not_nonempty_iff.mp hne
  have hRankPull : IsProjectiveOfRank 0
      ((pullback A.hom).obj (SheafOfModules.unit T.ringCatSheaf)) := by
    intro a
    exact isEmptyElim a
  have hfpUnit : (SheafOfModules.unit T.ringCatSheaf).IsFinitePresentation :=
    unit_isFinitePresentation_of_globalPresentation T
  exact ULift.up (PLift.up
    ((locallyFactors_affineStratum_iff_isProjectiveOfRank
      (SheafOfModules.unit T.ringCatSheaf) hfpUnit 0 A).mpr hRankPull))

/-- For a polynomial which is not a natural constant, projective flattening on
relative projective zero-space is the rank-zero stratum of the structure sheaf. -/
noncomputable def projectiveFlatteningFunctorZeroNonconstantIso
    (hfp : Q.IsFinitePresentation) (P : Polynomial ℚ)
    (hP : ∀ q : ℕ, P ≠ Polynomial.C (q : ℚ)) :
    flatRankFunctorOver (SheafOfModules.unit T.ringCatSheaf) 0 ⋙
        uliftFunctor.{u + 1} ≅
      projectiveFlatteningFunctor 0 Q (P := P) where
  hom :=
    { app := fun A ↦ ↾fun x ↦
        projectiveFlatteningZeroPointOfUnitRankZeroPoint Q hfp P A.unop x.down
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        exact (projectiveFlatteningFunctor_subsingleton 0 Q P B).elim _ _ }
  inv :=
    { app := fun A ↦ ↾fun x ↦ ULift.up
        (unitRankZeroPointOfProjectiveFlatteningZeroPoint Q hfp P hP A.unop x)
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        haveI := Scheme.factorsFunctor_subsingleton
          (affineStratum (SheafOfModules.unit T.ringCatSheaf) 0) B
        haveI : Subsingleton
            ((flatRankFunctorOver (SheafOfModules.unit T.ringCatSheaf) 0 ⋙
              uliftFunctor.{u + 1}).obj B) := by
          change Subsingleton
            (ULift ((flatRankFunctorOver
              (SheafOfModules.unit T.ringCatSheaf) 0).obj B))
          infer_instance
        exact Subsingleton.elim _ _ }
  hom_inv_id := by
    ext A x
    haveI := Scheme.factorsFunctor_subsingleton
      (affineStratum (SheafOfModules.unit T.ringCatSheaf) 0) A
    haveI : Subsingleton
        ((flatRankFunctorOver (SheafOfModules.unit T.ringCatSheaf) 0 ⋙
          uliftFunctor.{u + 1}).obj A) := by
      change Subsingleton
        (ULift ((flatRankFunctorOver
          (SheafOfModules.unit T.ringCatSheaf) 0).obj A))
      infer_instance
    exact Subsingleton.elim _ _
  inv_hom_id := by
    ext A x
    exact (projectiveFlatteningFunctor_subsingleton 0 Q P A).elim _ _

/-- Every finitely presented quasicoherent sheaf on relative projective zero-space
has a finite-rank projective flattening presentation, for every polynomial and over
an arbitrary base scheme. -/
theorem projectiveFlatteningHasFiniteRankPresentation_zero_all
    (hfp : Q.IsFinitePresentation) (P : Polynomial ℚ) :
    ProjectiveFlatteningHasFiniteRankPresentation 0 Q (P := P) := by
  classical
  by_cases hP : ∃ q : ℕ, P = Polynomial.C (q : ℚ)
  · obtain ⟨q, rfl⟩ := hP
    exact projectiveFlatteningHasFiniteRankPresentation_zero Q hfp q
  · have hP' : ∀ q : ℕ, P ≠ Polynomial.C (q : ℚ) :=
      fun q hq ↦ hP ⟨q, hq⟩
    refine ⟨{
      count := 1
      sheaf := fun _ ↦ SheafOfModules.unit T.ringCatSheaf
      rank := fun _ ↦ 0
      isQuasicoherent := fun _ ↦ unit_isQuasicoherent T
      finite := fun _ U ↦ ?_
      iso := ?_ }⟩
    · have hfpUnit : (SheafOfModules.unit T.ringCatSheaf).IsFinitePresentation :=
        unit_isFinitePresentation_of_globalPresentation T
      have hfpPull : ((pullback U.1.ι).obj
          (SheafOfModules.unit T.ringCatSheaf)).IsFinitePresentation :=
        isFinitePresentation_pullback_of_isFinitePresentation U.1.ι hfpUnit
      have hfpSec : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
          Γ((pullback U.1.ι).obj
            (SheafOfModules.unit T.ringCatSheaf), ⊤) :=
        (Scheme.Modules.isFinitePresentation_iff_sections_affineOpens
          ((pullback U.1.ι).obj
            (SheafOfModules.unit T.ringCatSheaf))).mp
              hfpPull ⟨⊤, isAffineOpen_top _⟩
      letI : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
          Γ((pullback U.1.ι).obj
            (SheafOfModules.unit T.ringCatSheaf), ⊤) := hfpSec
      infer_instance
    · let F := flatRankFunctorOver
        (SheafOfModules.unit T.ringCatSheaf) 0 ⋙ uliftFunctor.{u + 1}
      have hF : ∀ A, Subsingleton (F.obj A) := by
        intro A
        change Subsingleton
          (ULift ((flatRankFunctorOver
            (SheafOfModules.unit T.ringCatSheaf) 0).obj A))
        haveI := Scheme.factorsFunctor_subsingleton
          (affineStratum (SheafOfModules.unit T.ringCatSheaf) 0) A
        infer_instance
      exact finProdFunctorLargeSingletonIso F hF ≪≫
        projectiveFlatteningFunctorZeroNonconstantIso Q hfp P hP'

end AlgebraicGeometry.Scheme.Modules

end
