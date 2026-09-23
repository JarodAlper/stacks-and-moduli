module

public import StacksAndModuli.API.ProjectiveFlatteningOneStepBaseChange
public import StacksAndModuli.API.ProjectiveSpaceZeroGrassmannianQuot
public import StacksAndModuli.API.QuotGrassmannianReconstruction
public import StacksAndModuli.API.SchemeModulesEmptyOpen

/-!
# The field and relative halves of reconstructed Gotzmann persistence

The reverse implication in the one-step construction has two logically
different parts.  Over a field, flatness is automatic and the remaining
statement is the Macaulay--Gotzmann growth theorem: the two adjacent Hilbert
function values, together with surjectivity of degree-one multiplication,
determine every later Hilbert-function value.  Over a general base there is
also a relative flatness assertion.

This file separates those two inputs without hiding any base-change condition.
`ProjectiveOneStepFieldPersistenceEpi` is phrased using the pullbacks of the
two pushforwards and of the multiplication map.  Consequently it applies
directly to every field-valued point of a test scheme: finite projective rank
and epimorphy are preserved by pullback, and no further gluing is required.

The genuinely missing algebra is thus exposed by two propositions:

* `ProjectiveOneStepFieldGrowthEpi`, the field-valued Macaulay--Gotzmann
  growth theorem (and its eventual reformulation
  `ProjectiveOneStepFieldPersistenceEpi`);
* `ProjectiveOneStepFlatnessPersistenceEpi`, its relative flatness half.

Their conjunction gives the exact `ProjectiveOneStepGotzmannPersistenceEpi`
consumed by `ProjectiveFlatteningOneStepBaseChange`.  The final declarations
specialize this reduction to `reconstructedQuotient'`.

The elementary facts needed at the endpoints are proved here as well: every
module sheaf over projective space over a field is flat over that field, and a
rank statement for a twisted pushforward computes the corresponding Hilbert
function value.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every module sheaf on projective space over a field is flat over the
coefficient field.  No finiteness or quasicoherence hypothesis is needed. -/
theorem flatOver_projectiveSpaceOver_of_isField
    (n : ℕ) (K : CommRingCat.{u}) (hK : IsField K)
    (M : (Scheme.projectiveSpaceOver n (Spec K)).Modules) :
    M.FlatOver (Scheme.projectiveSpaceOverπ n (Spec K)) := by
  letI : Field K := hK.toField
  intro U V hUV
  letI := Module.compHom Γ(M, U.1)
    (((Scheme.projectiveSpaceOver n (Spec K)).presheaf.map
      (homOfLE hUV).op).hom.comp
        ((Scheme.projectiveSpaceOverπ n (Spec K)).app V.1).hom)
  by_cases hV : V.1 = ⊥
  · have hU : U.1 = ⊥ := by
      apply le_bot_iff.mp
      exact hUV.trans_eq (by simp [hV])
    haveI : Subsingleton Γ(M, U.1) := by
      rw [hU]
      exact Scheme.Modules.subsingleton_sections_bot M
    exact Module.Flat.of_shrink.{u, u, u}
  · have hVtop : V.1 = ⊤ := by
      apply top_unique
      intro x _
      by_contra hx
      apply hV
      apply TopologicalSpace.Opens.ext
      ext y
      constructor
      · intro hy
        exact False.elim (hx (by
          have hxy : x = y := by
            apply PrimeSpectrum.ext
            rw [x.asIdeal.eq_bot_of_prime, y.asIdeal.eq_bot_of_prime]
          simpa [hxy] using hy))
      · intro hy
        simp at hy
    let e : K ≃+* Γ(Spec K, V.1) :=
      (Scheme.ΓSpecIso K).symm.commRingCatIsoToRingEquiv.trans
        (CategoryTheory.Iso.commRingCatIsoToRingEquiv
          ((Spec K).presheaf.mapIso (eqToIso hVtop).op))
    letI : Field Γ(Spec K, V.1) :=
      (e.symm.isField (Field.toIsField K)).toField
    infer_instance

/-- Over a field, the rank of the pushforward of `Q(d)` is the value of the
Hilbert function of `Q` in degree `d`. -/
theorem hilbertFunctionOver_eq_of_projectiveTwistedPushforward_isProjectiveOfRank
    (n : ℕ) (K : CommRingCat.{u}) (hK : IsField K)
    (Q : (Scheme.projectiveSpaceOver n (Spec K)).Modules)
    (d : ℤ) (q : ℕ)
    (hQ : IsProjectiveOfRank q
      ((pushforward (Scheme.projectiveSpaceOverπ n (Spec K))).obj
        (Scheme.projectiveSpaceOverTwistModule Q d))) :
    Scheme.hilbertFunctionOver Q d = q := by
  letI : Field K := hK.toField
  have h := hQ.finrank_globalSections_spec_of_isField hK
  let Qd := Scheme.projectiveSpaceOverTwistModule Q d
  let p := Scheme.projectiveSpaceOverπ n (Spec K)
  letI := globalSectionsModule p Qd
  change Module.finrank K Γ(Qd, ⊤) = q
  exact h

variable {T : Scheme.{u}} {n : ℕ}
  {Q : (Scheme.projectiveSpaceOver n T).Modules} [Q.IsQuasicoherent]
  {P : Polynomial ℚ} {d : ℕ}

/-- The field-valued Macaulay--Gotzmann input in the form seen by rank loci.
For a field-valued point `s`, the hypotheses concern the pullbacks of the two
twisted pushforwards and the pullback of the multiplication map. -/
def ProjectiveOneStepFieldPersistenceEpi
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (P : Polynomial ℚ) (d : ℕ) : Prop :=
  ∀ (K : CommRingCat.{u}) (_hK : IsField K) (s : Spec K ⟶ T),
    IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
        ((pullback s).obj (projectiveTwistedPushforward n Q d)) →
    IsProjectiveOfRank ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
        ((pullback s).obj (projectiveTwistedPushforward n Q (d + 1))) →
    Epi ((pullback s).map (projectiveTwistedPushforwardMul n Q d)) →
    Scheme.HasHilbertPolynomialOver
      ((pullback (Scheme.projectiveSpaceOverMap n s)).obj Q) P

/-- The irreducible field-valued Macaulay--Gotzmann growth statement.  Unlike
`ProjectiveOneStepFieldPersistenceEpi`, its conclusion is not packaged as an
eventual equality: it says that every Hilbert-function value from degree `d`
onward is the prescribed value. -/
def ProjectiveOneStepFieldGrowthEpi
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (P : Polynomial ℚ) (d : ℕ) : Prop :=
  ∀ (K : CommRingCat.{u}) (_hK : IsField K) (s : Spec K ⟶ T),
    IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
        ((pullback s).obj (projectiveTwistedPushforward n Q d)) →
    IsProjectiveOfRank ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
        ((pullback s).obj (projectiveTwistedPushforward n Q (d + 1))) →
    Epi ((pullback s).map (projectiveTwistedPushforwardMul n Q d)) →
    ∀ t : ℕ, d ≤ t →
      (Scheme.hilbertFunctionOver
        ((pullback (Scheme.projectiveSpaceOverMap n s)).obj Q) (t : ℤ) : ℚ) =
          P.eval (t : ℚ)

omit [Q.IsQuasicoherent] in
/-- Exact Gotzmann growth implies the eventual Hilbert-polynomial statement. -/
theorem ProjectiveOneStepFieldGrowthEpi.toFieldPersistenceEpi
    (h : ProjectiveOneStepFieldGrowthEpi n Q P d) :
    ProjectiveOneStepFieldPersistenceEpi n Q P d := by
  intro K hK s h₀ h₁ hmul
  filter_upwards [Filter.eventually_ge_atTop d] with t ht
  exact h K hK s h₀ h₁ hmul t ht

/-- The relative-flatness half of one-step Gotzmann persistence.  It is kept
separate from the field Hilbert-function theorem because flatness is not a
fibrewise property. -/
def ProjectiveOneStepFlatnessPersistenceEpi
    (n : ℕ) (Q : (Scheme.projectiveSpaceOver n T).Modules)
    (P : Polynomial ℚ) (d : ℕ) : Prop :=
  ∀ (A : Over T),
    IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) d) →
    IsProjectiveOfRank ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
        (projectiveTwistedPushforward n (projectiveFamilyAt n Q A) (d + 1)) →
    Epi (projectiveTwistedPushforwardMul n (projectiveFamilyAt n Q A) d) →
    (projectiveFamilyAt n Q A).FlatOver
      (Scheme.projectiveSpaceOverπ n A.left)

/-- A field-persistence theorem automatically supplies the fibrewise Hilbert
polynomial after the rank and multiplication conditions hold on the base. -/
theorem ProjectiveOneStepFieldPersistenceEpi.hasFiberwiseHilbertPolynomial
    (h : ProjectiveOneStepFieldPersistenceEpi n Q P d)
    (h₀ : IsProjectiveOfRank ((P.eval (d : ℚ)).num.natAbs)
      (projectiveTwistedPushforward n Q d))
    (h₁ : IsProjectiveOfRank ((P.eval ((d + 1 : ℕ) : ℚ)).num.natAbs)
      (projectiveTwistedPushforward n Q (d + 1)))
    (hmul : Epi (projectiveTwistedPushforwardMul n Q d)) :
    Scheme.HasFiberwiseHilbertPolynomial Q P := by
  intro K hK s
  apply h K hK s (h₀.pullback s) (h₁.pullback s)
  exact Functor.map_epi (pullback s) (projectiveTwistedPushforwardMul n Q d)

/-- The field Macaulay--Gotzmann theorem and the relative flatness theorem
assemble to the exact reverse implication consumed by one-step projective
flattening. -/
theorem ProjectiveOneStepGotzmannPersistenceEpi.of_field_and_flatness
    (hfield : ∀ (A : Over T),
      ProjectiveOneStepFieldPersistenceEpi n
        (projectiveFamilyAt n Q A) P d)
    (hflat : ProjectiveOneStepFlatnessPersistenceEpi n Q P d) :
    ProjectiveOneStepGotzmannPersistenceEpi n Q P d := by
  intro A h₀ h₁ hmul
  refine ⟨hflat A h₀ h₁ hmul, ?_⟩
  exact (hfield A).hasFiberwiseHilbertPolynomial h₀ h₁ hmul

/-- Complete finite-rank presentation from the faithful reverse-Gotzmann
inputs.  The field hypothesis is exact Hilbert-function growth from degree
`d` onward; the second hypothesis is only the genuinely relative flatness
assertion.  All base change, rank-locus, cokernel, and finite-intersection
bookkeeping is discharged by this theorem. -/
theorem projectiveFlatteningHasFiniteRankPresentation_of_gotzmannGrowthEpi
    (hfp₀ : (projectiveTwistedPushforward n Q d).IsFinitePresentation)
    (hfp₁ : (projectiveTwistedPushforward n Q (d + 1)).IsFinitePresentation)
    (C : ProjectiveOneStepMultiplicationBaseChangeComparison n Q d)
    (hranks : ProjectiveOneStepActualRanksAndEpi n Q P d)
    (hgrowth : ∀ (A : Over T),
      ProjectiveOneStepFieldGrowthEpi n
        (projectiveFamilyAt n Q A) P d)
    (hflat : ProjectiveOneStepFlatnessPersistenceEpi n Q P d) :
    ProjectiveFlatteningHasFiniteRankPresentation n Q (P := P) := by
  apply OneStepProjectiveFlatteningData.projectiveFlatteningHasFiniteRankPresentation_ofMultiplicationBaseChangeEpi
      hfp₀ hfp₁ C hranks
  apply ProjectiveOneStepGotzmannPersistenceEpi.of_field_and_flatness
    (fun A ↦ (hgrowth A).toFieldPersistenceEpi) hflat

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Field-valued Gotzmann persistence for the reconstructed twisted-free
quotient, stated separately from relative flatness. -/
abbrev ReconstructedQuotientFieldPersistenceEpi
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (P : Polynomial ℚ) : Prop :=
  letI : (reconstructedQuotient' n T l r d e he u).IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent n T l r d e he u
  Modules.ProjectiveOneStepFieldPersistenceEpi n
    (reconstructedQuotient' n T l r d e he u) P d

/-- Exact field-valued Macaulay--Gotzmann growth for the reconstructed
twisted-free quotient. -/
abbrev ReconstructedQuotientFieldGrowthEpi
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (P : Polynomial ℚ) : Prop :=
  letI : (reconstructedQuotient' n T l r d e he u).IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent n T l r d e he u
  Modules.ProjectiveOneStepFieldGrowthEpi n
    (reconstructedQuotient' n T l r d e he u) P d

/-- Exact field growth supplies the eventual field-persistence package for a
reconstructed quotient. -/
theorem ReconstructedQuotientFieldGrowthEpi.toFieldPersistenceEpi
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (P : Polynomial ℚ)
    (h : ReconstructedQuotientFieldGrowthEpi n T l r d e he u P) :
    ReconstructedQuotientFieldPersistenceEpi n T l r d e he u P := by
  letI : (reconstructedQuotient' n T l r d e he u).IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent n T l r d e he u
  exact Modules.ProjectiveOneStepFieldGrowthEpi.toFieldPersistenceEpi h

/-- Relative-flatness persistence for the reconstructed twisted-free quotient. -/
abbrev ReconstructedQuotientFlatnessPersistenceEpi
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules} [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (P : Polynomial ℚ) : Prop :=
  letI : (reconstructedQuotient' n T l r d e he u).IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent n T l r d e he u
  Modules.ProjectiveOneStepFlatnessPersistenceEpi n
    (reconstructedQuotient' n T l r d e he u) P d

/-- All surrounding geometry for reverse Gotzmann persistence of the
reconstructed quotient: once the field growth and relative-flatness halves are
known after arbitrary base change, the standard one-step persistence theorem
follows. -/
theorem reconstructedQuotient'_projectiveOneStepGotzmannPersistenceEpi
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (P : Polynomial ℚ)
    (hfield : ∀ (A : Over T),
      let QA := Modules.projectiveFamilyAt n
        (reconstructedQuotient' n T l r d e he u) A
      Modules.ProjectiveOneStepFieldPersistenceEpi n QA P d)
    (hflat : ReconstructedQuotientFlatnessPersistenceEpi
      n T l r d e he u P) :
    letI : (reconstructedQuotient' n T l r d e he u).IsQuasicoherent :=
      reconstructedQuotient'_isQuasicoherent n T l r d e he u
    Modules.ProjectiveOneStepGotzmannPersistenceEpi n
      (reconstructedQuotient' n T l r d e he u) P d := by
  letI : (reconstructedQuotient' n T l r d e he u).IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent n T l r d e he u
  exact Modules.ProjectiveOneStepGotzmannPersistenceEpi.of_field_and_flatness
    hfield hflat

/-- The complete one-step projective-flattening presentation for a
reconstructed twisted-free quotient, conditional only on the adjacent
finite-presentation/CBC input, the forward regularity theorem, exact
field-valued Gotzmann growth, and relative flatness persistence. -/
theorem reconstructedQuotient'_projectiveFlatteningHasFiniteRankPresentation_of_gotzmannGrowthEpi
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E : T.Modules}
    [E.IsQuasicoherent]
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (P : Polynomial ℚ)
    (hfp₀ : (Modules.projectiveTwistedPushforward n
      (reconstructedQuotient' n T l r d e he u) d).IsFinitePresentation)
    (hfp₁ : (Modules.projectiveTwistedPushforward n
      (reconstructedQuotient' n T l r d e he u) (d + 1)).IsFinitePresentation)
    (C : Modules.ProjectiveOneStepMultiplicationBaseChangeComparison n
      (reconstructedQuotient' n T l r d e he u) d)
    (hranks : Modules.ProjectiveOneStepActualRanksAndEpi n
      (reconstructedQuotient' n T l r d e he u) P d)
    (hgrowth : ∀ (A : Over T),
      let QA := Modules.projectiveFamilyAt n
        (reconstructedQuotient' n T l r d e he u) A
      Modules.ProjectiveOneStepFieldGrowthEpi n QA P d)
    (hflat : ReconstructedQuotientFlatnessPersistenceEpi
      n T l r d e he u P) :
    letI : (reconstructedQuotient' n T l r d e he u).IsQuasicoherent :=
      reconstructedQuotient'_isQuasicoherent n T l r d e he u
    Modules.ProjectiveFlatteningHasFiniteRankPresentation n
      (reconstructedQuotient' n T l r d e he u) (P := P) := by
  letI : (reconstructedQuotient' n T l r d e he u).IsQuasicoherent :=
    reconstructedQuotient'_isQuasicoherent n T l r d e he u
  exact Modules.projectiveFlatteningHasFiniteRankPresentation_of_gotzmannGrowthEpi
      hfp₀ hfp₁ C hranks hgrowth hflat

end AlgebraicGeometry.Scheme

end

end
