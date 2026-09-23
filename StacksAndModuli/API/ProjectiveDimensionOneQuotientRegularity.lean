module

public import StacksAndModuli.API.ProjectiveRegularityHilbertPersistence
public import StacksAndModuli.API.TwistedFreeQuotPushforwardRank
public import StacksAndModuli.API.ProjectiveOneStepIteratedBaseChange
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianUniversalFlatteningFiniteness

/-!
# Regular models for twisted-free quotients in projective dimension one

In projective dimension at most one, the regularity of the middle term in a
short exact sequence passes to its quotient without a regularity hypothesis on
the kernel: the next cohomology group is above the dimension.  Applied to the
kernel-route model of a quotient of a finite twisted-free sheaf, this constructs
the field regularity model used by one-step Hilbert-function persistence.

The positive-dimension hypothesis in the twisted-free constructor is exactly
the hypothesis of the existing comparison
`ProjectiveSpace.gammaStarPullTwistedFreeIso`.  Thus the constructor covers
projective dimension one; projective dimension zero has its separate exact
Grassmannian classification.

Main declarations:

* `ProjectiveSpace.Cohomology.isMRegular_pow`;
* `ProjectiveSpace.Cohomology.isMRegular_of_shortExact_of_dimension_le_one`;
* `Scheme.Modules.fieldRegularityModelOfIsField_of_twistedFreeQuotient_of_dimension_le_one`;
* `Scheme.Modules.ProjectiveOneStepFieldGrowthEpi.of_twistedFreeQuotient_of_dimension_le_one`;
* `Scheme.Modules.ProjectiveOneStepFieldGrowthEpi.of_familyAt_dimension_le_one`;
* `Scheme.exists_eventual_twistedFreeQuotUniversal_fieldGrowth_of_dimension_le_one`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

open GradedModule

variable {k : Type u} [Field k] (C : Cohomology k)

/-- Finite direct sums preserve Castelnuovo--Mumford regularity. -/
theorem isMRegular_pow {n : ℕ} {M : GradedModule k n} {m : ℤ}
    (hM : C.IsMRegular M m) (r : ℕ) :
    C.IsMRegular (M.pow r) m := by
  intro i hi
  haveI : Subsingleton ((C.Hgr M i).obj (m - i)) := hM i hi
  refine ⟨fun x y ↦ (C.HgrPowIso M r i (m - i)).toLinearEquiv.injective ?_⟩
  funext j
  exact Subsingleton.elim _ _

/-- In projective dimension at most one, a quotient of an `m`-regular
graded model is `m`-regular.  The connecting term is an `H^(i+1)` group,
which vanishes by dimension for every `i ≥ 1`. -/
theorem isMRegular_of_shortExact_of_dimension_le_one
    {n : ℕ} (hn : n ≤ 1) {K M Q : GradedModule k n}
    {f : K ⟶ M} {g : M ⟶ Q} (hfg : ShortExact f g) {m : ℤ}
    (hM : C.IsMRegular M m) : C.IsMRegular Q m := by
  intro i hi
  exact C.subsingleton_H_X₃ hfg i (m - i) (hM i hi)
    (C.subsingleton_of_lt K (i + 1) (m - i) (by omega))

end AlgebraicGeometry.ProjectiveSpace.Cohomology

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The kernel-route graded model of a quotient of
`O(-l)^⊕r` over a field is a regular comparison model in every degree
`d ≥ l`, provided the projective dimension is positive and at most one.

The comparison with actual twisted global sections is the quotient-model
Čech comparison.  Regularity follows from the short exact sequence
`Gamma_*(K) → Gamma_*(O(-l)^⊕r) → M`, the twisted-free normalization of
the middle term, and dimension vanishing for the connecting cohomology. -/
noncomputable def
    fieldRegularityModelOfIsField_of_twistedFreeQuotient_of_dimension_le_one
    (n r : ℕ) (hn : 0 < n) (hn₁ : n ≤ 1)
    (K : CommRingCat.{u}) (hK : IsField K) (l : ℤ) (d : ℕ)
    (hld : l ≤ (d : ℤ))
    (Q : (Scheme.projectiveSpaceOver n (Spec K)).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec K) (-l)) ⟶ Q)
    [Epi q] : FieldRegularityModelOfIsField n K hK Q d := by
  letI : Field K := hK.toField
  haveI hAmbientFp : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec K) (-l)).IsFinitePresentation :=
    Scheme.twistedFreeAmbient_isFinitePresentation n (Spec K) l r
  let E := ProjectiveSpace.projAmbient n r l (R := K)
  let G := (pullback (ProjectiveSpace.projectiveSpaceOverSpecIso n K).inv).obj Q
  let p := (pullback (ProjectiveSpace.projectiveSpaceOverSpecIso n K).inv).map q
  let M := Proj.kernelQuotientModule
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
    (ProjectiveSpace.projSpecπ n K) (ProjectiveSpace.stdVars n K) p
  haveI hp : Epi p := inferInstance
  haveI hEfp : E.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hGfp : G.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  haveI hEqc : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) E a).IsQuasicoherent :=
    fun a ↦ ProjectiveSpace.twistModule_std_isQuasicoherent _ a
  haveI hGqc : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) G a).IsQuasicoherent :=
    fun a ↦ ProjectiveSpace.twistModule_std_isQuasicoherent _ a
  have hKqc : (kernel p).IsQuasicoherent := Scheme.Modules.kernel_isQuasicoherent p
  letI hKqc' : (kernel p).IsQuasicoherent := hKqc
  haveI hKtwistQc : ∀ a : ℤ, (twistModule
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)
      (kernel p) a).IsQuasicoherent :=
    fun a ↦ ProjectiveSpace.twistModule_std_isQuasicoherent_of_isQuasicoherent n _ a
  let C := ProjectiveSpace.Cohomology.cech K
  let D := ProjectiveSpace.cechSchemeGlobalSectionsComparisonQuotientModel_arbitrary
    n K Q p
  refine
    { C := C
      M := M
      coherent := ?_
      infiniteBaseChange := ?_
      regular := ?_
      globalSectionsIso := ?_ }
  · change GradedModule.IsFG M
    exact ProjectiveSpace.isFG_kernelQuotientModule_twistedFree_arbitrary
      n r hn l K Q q
  · exact ProjectiveSpace.Cohomology.hasInfiniteBaseChange_cech K
  · have htwistAtL : C.IsMRegular
        (GradedModule.twistingModule K n (-l)) l := by
      simpa only [neg_neg] using C.isMRegular_twistingModule n (-l)
    have htwistCoherent : C.IsCoherent
        (GradedModule.twistingModule K n (-l)) := by
      change C.IsCoherent ((GradedModule.structureModule K n).twist (-l))
      exact C.isCoherent_twist C.isCoherent_structureModule (-l)
    have htwistAtD : C.IsMRegular
        (GradedModule.twistingModule K n (-l)) (d : ℤ) :=
      C.isMRegular_of_le_of_field htwistCoherent
        (ProjectiveSpace.Cohomology.hasInfiniteBaseChange_cech K)
        htwistAtL hld
    have hmiddle : C.IsMRegular
        (((GradedModule.structureModule K n).twist (-l)).pow r) (d : ℤ) :=
      by
        change C.IsMRegular ((GradedModule.twistingModule K n (-l)).pow r) (d : ℤ)
        exact C.isMRegular_pow htwistAtD r
    have hshort := Proj.shortExact_gammaStar_toCoker_kernel
      (ProjectiveSpace.projSpecπ n K) p
    have hshort' := GradedModule.ShortExact.congr_middle
      (ProjectiveSpace.gammaStarPullTwistedFreeIso n K hn (-l) r) hshort
    exact C.isMRegular_of_shortExact_of_dimension_le_one hn₁ hshort' hmiddle
  · intro t ht
    exact D.globalSectionsIso t (by
      change 0 ≤ t
      omega)

/-- A nonempty fixed-polynomial twisted-free quotient in projective dimension
at most one forces all of the numerical facts used by two-value persistence.
The degree bound comes from bounded Snapper on one residue-field fibre.  In
every regular degree, the value of the prescribed polynomial is the dimension
of actual global sections, and hence is the cast of its natural normalization.

This statement is deliberately based on one nonempty witness family.  The
resulting conclusions concern only `P`, so they can subsequently be used for
a different universal reconstructed family. -/
theorem hilbertPolynomial_numerics_of_nonempty_twistedFreeQuotient_of_dimension_le_one
    (n r : ℕ) (hn : 0 < n) (hn₁ : n ≤ 1)
    (T : Scheme.{u}) (hT : Nonempty T) (l : ℤ)
    (Q : (Scheme.projectiveSpaceOver n T).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi q] (P : Polynomial ℚ) (hP : Scheme.HasFiberwiseHilbertPolynomial Q P)
    (d : ℕ) (hld : l ≤ (d : ℤ)) :
    P.natDegree ≤ n ∧
      ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ) ∧
      ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
        P.eval ((d + 1 : ℕ) : ℚ) := by
  let x : T := Classical.choice hT
  let K := T.residueField x
  let hK : IsField K := Field.toIsField K
  let s : Spec K ⟶ T := T.fromSpecResidueField x
  let Qs := (pullback (Scheme.projectiveSpaceOverMap n s)).obj Q
  haveI hQsfp : Qs.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  let qs : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec K) (-l)) ⟶ Qs :=
    (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l s).inv ≫
      (pullback (Scheme.projectiveSpaceOverMap n s)).map q
  haveI hqsepi : Epi qs := epi_comp _ _
  let D : FieldRegularityModelOfIsField n K hK Qs d :=
    fieldRegularityModelOfIsField_of_twistedFreeQuotient_of_dimension_le_one
      n r hn hn₁ K hK l d hld Qs qs
  have hDP : Scheme.HasHilbertPolynomialOver Qs D.polynomial := by
    filter_upwards [Filter.eventually_ge_atTop d] with t ht
    exact D.hilbertFunctionOver_eq t ht
  have hPK : Scheme.HasHilbertPolynomialOver Qs P := hP K hK s
  have hpoly : D.polynomial = P := hDP.unique hPK
  have hdegree : P.natDegree ≤ n := by
    rw [← hpoly]
    exact D.polynomial_natDegree_le
  have hvalue (t : ℕ) (hdt : d ≤ t) :
      (Scheme.hilbertFunctionOver Qs (t : ℤ) : ℚ) = P.eval (t : ℚ) := by
    rw [D.hilbertFunctionOver_eq t hdt, hpoly]
  refine ⟨hdegree, ?_, ?_⟩
  · change (P.hilbertNatValue d : ℚ) = P.eval (d : ℚ)
    rw [Polynomial.hilbertNatValue_eq (hvalue d le_rfl)]
    exact hvalue d le_rfl
  · change (P.hilbertNatValue (d + 1) : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ)
    rw [Polynomial.hilbertNatValue_eq (hvalue (d + 1) (by omega))]
    exact hvalue (d + 1) (by omega)

/-- One nonempty fixed-polynomial twisted-free quotient supplies, uniformly in
all sufficiently large degrees, the twist inequality and the three numerical
hypotheses needed by dimension-one two-value persistence. -/
theorem exists_eventual_hilbertPolynomial_numerics_of_dimension_le_one
    (n r : ℕ) (hn : 0 < n) (hn₁ : n ≤ 1)
    (T : Scheme.{u}) (hT : Nonempty T) (l : ℤ)
    (Q : (Scheme.projectiveSpaceOver n T).Modules)
    [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q)
    [Epi q] (P : Polynomial ℚ) (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      l ≤ (d : ℤ) ∧ P.natDegree ≤ n ∧
        ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ) ∧
        ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
          P.eval ((d + 1 : ℕ) : ℚ) := by
  refine ⟨l.natAbs, ?_⟩
  intro d hd
  have hd' : (l.natAbs : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have hld : l ≤ (d : ℤ) := le_trans Int.le_natAbs hd'
  exact ⟨hld,
    hilbertPolynomial_numerics_of_nonempty_twistedFreeQuotient_of_dimension_le_one
      n r hn hn₁ T hT l Q q P hP d hld⟩

variable {T : Scheme.{u}} {n r d : ℕ} {l : ℤ}
  {Q : (Scheme.projectiveSpaceOver n T).Modules} [Q.IsQuasicoherent]
  [Q.IsFinitePresentation] {P : Polynomial ℚ}

omit [Q.IsQuasicoherent] in
/-- In positive projective dimension at most one, a twisted-free quotient has
the regular field models required by one-step persistence.  Consequently two
adjacent ranks determine all later Hilbert-function values, once the two
pushforwards satisfy field-valued base change.

The multiplication-epimorphism hypothesis in
`ProjectiveOneStepFieldGrowthEpi` is not needed for this low-dimensional
argument. -/
theorem ProjectiveOneStepFieldGrowthEpi.of_twistedFreeQuotient_of_dimension_le_one
    (hn : 0 < n) (hn₁ : n ≤ 1) (hld : l ≤ (d : ℤ))
    (hPdeg : P.natDegree ≤ n)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q) [Epi q]
    (hdegree : ∀ (K : CommRingCat.{u}) (_hK : IsField K)
      (s : Spec K ⟶ T),
      (pullback s).obj (projectiveTwistedPushforward n Q d) ≅
        projectiveTwistedPushforward n
          ((pullback (Scheme.projectiveSpaceOverMap n s)).obj Q) d)
    (hdegreeSucc : ∀ (K : CommRingCat.{u}) (_hK : IsField K)
      (s : Spec K ⟶ T),
      (pullback s).obj (projectiveTwistedPushforward n Q (d + 1)) ≅
        projectiveTwistedPushforward n
          ((pullback (Scheme.projectiveSpaceOverMap n s)).obj Q) (d + 1)) :
    ProjectiveOneStepFieldGrowthEpi n Q P d := by
  apply ProjectiveOneStepFieldGrowthEpi.of_regular_models_of_dimension_le_one
    hn₁ hPdeg hPd hPsucc hdegree hdegreeSucc
  intro K hK s _ _ _
  let Qs := (pullback (Scheme.projectiveSpaceOverMap n s)).obj Q
  haveI hQsfp : Qs.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  let qs : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n (Spec K) (-l)) ⟶ Qs :=
    (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l s).inv ≫
      (pullback (Scheme.projectiveSpaceOverMap n s)).map q
  haveI hqsepi : Epi qs := epi_comp _ _
  exact fieldRegularityModelOfIsField_of_twistedFreeQuotient_of_dimension_le_one
    n r hn hn₁ K hK l d hld Qs qs

omit [Q.IsQuasicoherent] in
/-- A one-step multiplication base-change package supplies the two field
base-change comparisons required by the preceding low-dimensional growth
theorem. -/
theorem
    ProjectiveOneStepFieldGrowthEpi.of_twistedFreeQuotient_of_dimension_le_one_of_baseChange
    (hn : 0 < n) (hn₁ : n ≤ 1) (hld : l ≤ (d : ℤ))
    (hPdeg : P.natDegree ≤ n)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q) [Epi q]
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison n Q d) :
    ProjectiveOneStepFieldGrowthEpi n Q P d :=
  ProjectiveOneStepFieldGrowthEpi.of_twistedFreeQuotient_of_dimension_le_one
    hn hn₁ hld hPdeg hPd hPsucc q
      (fun _ _ s ↦ C.degree (Over.mk s))
      (fun _ _ s ↦ C.degreeSucc (Over.mk s))

omit [Q.IsQuasicoherent] in
/-- A base-change package for a twisted-free quotient on `T` supplies
dimension-one field growth after every first base change `A ⟶ T`.  The two
pushforward comparisons on the resulting family are obtained by iterating the
original comparisons; multiplication coherence is not used. -/
theorem
    ProjectiveOneStepFieldGrowthEpi.of_familyAt_dimension_le_one
    (hn : 0 < n) (hn₁ : n ≤ 1) (hld : l ≤ (d : ℤ))
    (hPdeg : P.natDegree ≤ n)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q) [Epi q]
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison n Q d)
    (A : Over T) :
    ProjectiveOneStepFieldGrowthEpi n (projectiveFamilyAt n Q A) P d := by
  let QA := projectiveFamilyAt n Q A
  haveI hQAfP : QA.IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_pullback_of_isFinitePresentation _ inferInstance
  let qA : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n A.left (-l)) ⟶ QA :=
    (Scheme.projectiveSpaceOverTwistedFree_pullbackIso n r l A.hom).inv ≫
      (pullback (Scheme.projectiveSpaceOverMap n A.hom)).map q
  haveI hqAepi : Epi qA := epi_comp _ _
  exact
    ProjectiveOneStepFieldGrowthEpi.of_twistedFreeQuotient_of_dimension_le_one
      hn hn₁ hld hPdeg hPd hPsucc qA
        (fun _ _ s ↦ C.degree_familyAt A (Over.mk s))
        (fun _ _ s ↦ C.degreeSucc_familyAt A (Over.mk s))

omit [Q.IsQuasicoherent] in
/-- For a nonempty fixed-polynomial twisted-free quotient in projective
dimension one, eventual base change for adjacent pushforwards implies eventual
one-step field growth.  The regularity, polynomial-degree, natural-value, and
twist-bound hypotheses are all discharged internally. -/
theorem
    exists_eventual_fieldGrowth_of_nonempty_twistedFreeQuotient_of_dimension_le_one
    (hn : 0 < n) (hn₁ : n ≤ 1) (hT : Nonempty T)
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist n T (-l)) ⟶ Q) [Epi q]
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P)
    (hC : ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      Nonempty (ProjectiveOneStepMultiplicationBaseChangeComparison n Q d)) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ProjectiveOneStepFieldGrowthEpi n Q P d := by
  obtain ⟨DN, hN⟩ :=
    exists_eventual_hilbertPolynomial_numerics_of_dimension_le_one
      n r hn hn₁ T hT l Q q P hP
  obtain ⟨DC, hC⟩ := hC
  refine ⟨max DN DC, ?_⟩
  intro d hd
  obtain ⟨hld, hPdeg, hPd, hPsucc⟩ :=
    hN d (le_trans (le_max_left DN DC) hd)
  obtain ⟨C⟩ := hC d (le_trans (le_max_right DN DC) hd)
  exact
    ProjectiveOneStepFieldGrowthEpi.of_twistedFreeQuotient_of_dimension_le_one_of_baseChange
      hn hn₁ hld hPdeg hPd hPsucc q C

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

open Modules.QuotientPullbackData

/-- In projective dimension one, the outer adjacent-pushforward base-change
package for the universal Grassmannian reconstruction produces its complete
field-growth field after every test-scheme base change. -/
theorem twistedFreeQuotUniversal_fieldGrowth_of_dimension_le_one
    (n : ℕ) (hn : 0 < n) (hn₁ : n ≤ 1)
    (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
    (hPdeg : P.natDegree ≤ n)
    (hPd : ((P.eval (d : ℚ)).num.natAbs : ℚ) = P.eval (d : ℚ))
    (hPsucc : ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs : ℚ) =
      P.eval ((d + 1 : ℕ) : ℚ))
    (C : Modules.ProjectiveOneStepMultiplicationBaseChangeComparison n
      (twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he) d) :
    ∀ A : Over (grassmannianOverRepresentation S (P.hilbertNatValue d)
      (r * (n + e).choose n)).left,
      Modules.ProjectiveOneStepFieldGrowthEpi n
        (Modules.projectiveFamilyAt n
          (twistedFreeQuotUniversalReconstructedQuotient
            n S l r P d e he) A) P d := by
  let Q := twistedFreeQuotUniversalReconstructedQuotient n S l r P d e he
  haveI hQqc : Q.IsQuasicoherent :=
    freeGrassmannianUniversalReconstructedQuotient_isQuasicoherent
  haveI hQfp : Q.IsFinitePresentation :=
    freeGrassmannianUniversalReconstructedQuotient_isFinitePresentation
  let q := freeGrassmannianUniversalReconstructedQuotientMap S n r
    (P.hilbertNatValue d) (r * (n + e).choose n) l d e he
      (twistedFreeMonomialIndexEquiv r ((n + e).choose n))
  haveI hqepi : Epi q := inferInstance
  have hld : l ≤ (d : ℤ) := by omega
  intro A
  exact
    Modules.ProjectiveOneStepFieldGrowthEpi.of_familyAt_dimension_le_one
      hn hn₁ hld hPdeg hPd hPsucc q C A

/-- A single nonempty fixed-polynomial Quot family supplies the polynomial
numerics uniformly in large degree.  Consequently, in projective dimension
one, every outer base-change package for the universal reconstructed family
automatically supplies the `fieldGrowth` component of the one-step universal
geometry, for every test scheme `A` over its Grassmannian base. -/
theorem exists_eventual_twistedFreeQuotUniversal_fieldGrowth_of_dimension_le_one
    (n : ℕ) (hn : 0 < n) (hn₁ : n ≤ 1)
    (S : Scheme.{u}) (l : ℤ) (r : ℕ) (P : Polynomial ℚ)
    (T : Over S)
    (a : Modules.QuotientPullbackData
      (Modules.QuotientPullbackData.twistedFreeAmbient
        (n := n) (r := r) (l := l))
      (projectiveSpaceOverπ n S) T)
    (hP : a.HasFiberwiseHilbertPolynomial P) (hT : Nonempty T.left) :
    ∃ D : ℕ, ∀ d : ℕ, D ≤ d →
      ∀ (e : ℕ) (he : (d : ℤ) - l = (e : ℤ))
        (_C : Modules.ProjectiveOneStepMultiplicationBaseChangeComparison n
          (twistedFreeQuotUniversalReconstructedQuotient
            n S l r P d e he) d),
        ∀ A : Over (grassmannianOverRepresentation S (P.hilbertNatValue d)
          (r * (n + e).choose n)).left,
          Modules.ProjectiveOneStepFieldGrowthEpi n
            (Modules.projectiveFamilyAt n
              (twistedFreeQuotUniversalReconstructedQuotient
                n S l r P d e he) A) P d := by
  let Q := twistedFreeQuotientSheaf n S l r a
  haveI hQfp : Q.IsFinitePresentation :=
    quotDataOnProjectiveSpace_isFinitePresentation_over T a
  let q := twistedFreeQuotientOnProjectiveSpaceOver T a
  haveI hqepi : Epi q :=
    twistedFreeQuotientOnProjectiveSpaceOver_epi T a
  obtain ⟨D, hD⟩ :=
    Modules.exists_eventual_hilbertPolynomial_numerics_of_dimension_le_one
      n r hn hn₁ T.left hT l Q q P hP
  refine ⟨D, ?_⟩
  intro d hd e he C A
  obtain ⟨_, hPdeg, hPd, hPsucc⟩ := hD d hd
  exact twistedFreeQuotUniversal_fieldGrowth_of_dimension_le_one
    n hn hn₁ S l r P d e he hPdeg hPd hPsucc C A

end AlgebraicGeometry.Scheme

end

end
