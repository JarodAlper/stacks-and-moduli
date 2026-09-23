module

public import StacksAndModuli.API.TwistedFreeQuotGotzmannSeedBound

/-!
# The zero-ambient projective-line Gotzmann seed bound

When the twisted-free ambient rank is zero, all coefficient sheaves involved in
Grassmannian reconstruction are zero objects.  Consequently the reconstructed
quotient, its algebraic next-degree module, and every twisted pushforward of the
reconstruction are zero.  This proves the affine Gotzmann seed bound, with bound
zero, for every polynomial in this boundary case.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.free_isZero_of_isEmpty`;
* `AlgebraicGeometry.Scheme.reconstructedQuotient'_isZero_zero_ambient`;
* `AlgebraicGeometry.Scheme.twistedFreeNextDegreeModule_isZero_zero_ambient`;
* `AlgebraicGeometry.Scheme.Modules.projectiveTwistedPushforward_isZero`;
* `AlgebraicGeometry.Scheme.Modules.twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_zero`;
* `AlgebraicGeometry.Scheme.Modules.twistedFreeQuotProjectiveLineEpimorphicSeedBound_zero`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{u}}

/-- A free sheaf on an empty type is a zero object. -/
theorem free_isZero_of_isEmpty (I : Type u) [IsEmpty I] :
    IsZero (SheafOfModules.free (R := X.ringCatSheaf) I) := by
  rw [IsZero.iff_id_eq_zero]
  apply Cofan.IsColimit.hom_ext
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) I)
  intro i
  exact isEmptyElim i

/-- Tensoring a zero scheme module with any other scheme module gives a zero object. -/
theorem tensor_isZero_of_left_isZero (M N : X.Modules) (hM : IsZero M) :
    IsZero (tensor M N) := by
  change IsZero ((tensorRightFunctor N).obj M)
  exact Functor.map_isZero (tensorRightFunctor N) hM

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The zero-fold coproduct of projective twists is a zero object. -/
theorem twistedFreeAmbient_isZero_zero
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) :
    IsZero (∐ fun _ : ULift.{u} (Fin 0) ↦
      projectiveSpaceOverTwist n T (-l)) := by
  rw [IsZero.iff_id_eq_zero]
  apply Limits.Sigma.hom_ext
  intro i
  exact Fin.elim0 i.down

/-- With no twisted-free generators, the reconstructed quotient is zero. -/
theorem reconstructedQuotient'_isZero_zero_ambient
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin 0) × Fin ((n + e).choose n)) ⟶ E) :
    IsZero (reconstructedQuotient' n T l 0 d e he u) := by
  let f := reconstructedRelation' n T l 0 d e he u
  have hF : IsZero (∐ fun _ : ULift.{u} (Fin 0) ↦
      projectiveSpaceOverTwist n T (-l)) :=
    twistedFreeAmbient_isZero_zero n T l
  letI : Epi f := hF.epi f
  exact isZero_cokernel_of_epi f

/-- With no twisted-free generators, the algebraic next-degree module is zero. -/
theorem twistedFreeNextDegreeModule_isZero_zero_ambient
    (n : ℕ) (T : Scheme.{u}) (e : ℕ) {E : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin 0) × Fin ((n + e).choose n)) ⟶ E) :
    IsZero (twistedFreeNextDegreeModule n T 0 e u) := by
  let f := twistedFreeNextDegreeRelation n T 0 e u
  have hF : IsZero (SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin 0) × Fin ((n + (e + 1)).choose n))) :=
    Modules.free_isZero_of_isEmpty
      (X := T) (ULift.{u} (Fin 0) × Fin ((n + (e + 1)).choose n))
  letI : Epi f := hF.epi f
  exact isZero_cokernel_of_epi f

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every twisted projective pushforward of a zero module is zero. -/
theorem projectiveTwistedPushforward_isZero
    (n : ℕ) {T : Scheme.{u}}
    (Q : (Scheme.projectiveSpaceOver n T).Modules) (d : ℕ)
    (hQ : IsZero Q) :
    IsZero (projectiveTwistedPushforward n Q d) := by
  apply Functor.map_isZero (pushforward (Scheme.projectiveSpaceOverπ n T))
  exact tensor_isZero_of_left_isZero Q
    (Scheme.projectiveSpaceOverTwist n T (d : ℤ)) hQ

/-- Pulling a zero projective family to any test scheme leaves it zero. -/
theorem projectiveFamilyAt_isZero
    (n : ℕ) {T : Scheme.{u}}
    (Q : (Scheme.projectiveSpaceOver n T).Modules) (A : Over T)
    (hQ : IsZero Q) :
    IsZero (projectiveFamilyAt n Q A) :=
  Functor.map_isZero
    (pullback (Scheme.projectiveSpaceOverMap n A.hom)) hQ

/-- The affine Gotzmann seed bound is automatic when the prescribed twisted-free
ambient sheaf has rank zero.  The uniform bound is `0`, independently of `l` and `P`. -/
noncomputable def twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_zero
    (l : ℤ) (P : Polynomial ℚ) :
    TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound.{u} 0 l P where
  bound := 0
  affineSeedRanks T _ d e he E _ u _ _ hE hnext := by
    let hsource : IsZero (SheafOfModules.free (R := T.ringCatSheaf)
        (ULift.{u} (Fin 0) × Fin ((1 + e).choose 1))) :=
      free_isZero_of_isEmpty
        (X := T) (ULift.{u} (Fin 0) × Fin ((1 + e).choose 1))
    have hEzero : IsZero E :=
      IsZero.of_epi_eq_zero u (hsource.eq_zero_of_src u)
    let Q := reconstructedQuotient' 1 T l 0 d e he u
    have hQ : IsZero Q :=
      Scheme.reconstructedQuotient'_isZero_zero_ambient 1 T l d e he u
    have hQd : IsZero (projectiveTwistedPushforward 1 Q d) :=
      projectiveTwistedPushforward_isZero 1 Q d hQ
    have hQnext : IsZero (projectiveTwistedPushforward 1 Q (d + 1)) :=
      projectiveTwistedPushforward_isZero 1 Q (d + 1) hQ
    have hnextZero : IsZero (twistedFreeNextDegreeModule 1 T 0 e u) :=
      Scheme.twistedFreeNextDegreeModule_isZero_zero_ambient 1 T e u
    constructor
    · intro _
      exact hE.of_iso (hEzero.iso hQd)
    · intro _
      exact hnext.of_iso (hnextZero.iso hQnext)

/-- In particular, the missing affine seed-bound endpoint is inhabited in ambient
rank zero, without any admissibility assumption on the polynomial. -/
theorem nonempty_twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_zero
    (l : ℤ) (P : Polynomial ℚ) :
    Nonempty
      (TwistedFreeQuotProjectiveLineAffineGotzmannSeedBound.{u} 0 l P) :=
  ⟨twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_zero l P⟩

/-- The arbitrary-base-change Gotzmann seed bound is also automatic in ambient rank
zero. -/
noncomputable def twistedFreeQuotProjectiveLineGotzmannSeedBound_zero
    (l : ℤ) (P : Polynomial ℚ) :
    TwistedFreeQuotProjectiveLineGotzmannSeedBound.{u} 0 l P :=
  (twistedFreeQuotProjectiveLineAffineGotzmannSeedBound_zero l P).toGotzmannSeedBound

/-- The arbitrary-base-change seed-bound endpoint is inhabited in ambient rank zero. -/
theorem nonempty_twistedFreeQuotProjectiveLineGotzmannSeedBound_zero
    (l : ℤ) (P : Polynomial ℚ) :
    Nonempty (TwistedFreeQuotProjectiveLineGotzmannSeedBound.{u} 0 l P) :=
  ⟨twistedFreeQuotProjectiveLineGotzmannSeedBound_zero l P⟩

/-- In ambient rank zero, the two canonical twisted-pushforward base-change maps are
epimorphisms as well: their targets are zero objects. -/
noncomputable def twistedFreeQuotProjectiveLineEpimorphicSeedBound_zero
    (l : ℤ) (P : Polynomial ℚ) :
    TwistedFreeQuotProjectiveLineEpimorphicSeedBound.{u} 0 l P where
  toTwistedFreeQuotProjectiveLineGotzmannSeedBound :=
    twistedFreeQuotProjectiveLineGotzmannSeedBound_zero l P
  degreeBaseChangeEpi T d e he E _ u _ _ _ _ A := by
    let Q := reconstructedQuotient' 1 T l 0 d e he u
    have hQ : IsZero Q :=
      Scheme.reconstructedQuotient'_isZero_zero_ambient 1 T l d e he u
    have hQA : IsZero (projectiveFamilyAt 1 Q A) :=
      projectiveFamilyAt_isZero 1 Q A hQ
    have htarget : IsZero
        (projectiveTwistedPushforward 1 (projectiveFamilyAt 1 Q A) d) :=
      projectiveTwistedPushforward_isZero 1 (projectiveFamilyAt 1 Q A) d hQA
    exact htarget.epi _
  degreeSuccBaseChangeEpi T d e he E _ u _ _ _ _ A := by
    let Q := reconstructedQuotient' 1 T l 0 d e he u
    have hQ : IsZero Q :=
      Scheme.reconstructedQuotient'_isZero_zero_ambient 1 T l d e he u
    have hQA : IsZero (projectiveFamilyAt 1 Q A) :=
      projectiveFamilyAt_isZero 1 Q A hQ
    have htarget : IsZero
        (projectiveTwistedPushforward 1 (projectiveFamilyAt 1 Q A) (d + 1)) :=
      projectiveTwistedPushforward_isZero
        1 (projectiveFamilyAt 1 Q A) (d + 1) hQA
    exact htarget.epi _

/-- Even the stronger epimorphic seed-bound endpoint is inhabited in ambient rank
zero, without any admissibility assumption. -/
theorem nonempty_twistedFreeQuotProjectiveLineEpimorphicSeedBound_zero
    (l : ℤ) (P : Polynomial ℚ) :
    Nonempty
      (TwistedFreeQuotProjectiveLineEpimorphicSeedBound.{u} 0 l P) :=
  ⟨twistedFreeQuotProjectiveLineEpimorphicSeedBound_zero l P⟩

end AlgebraicGeometry.Scheme.Modules

end

end
