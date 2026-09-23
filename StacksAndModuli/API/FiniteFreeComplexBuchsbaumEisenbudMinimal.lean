module

public import StacksAndModuli.API.FiniteFreeComplexBuchsbaumEisenbudLocalization
public import StacksAndModuli.API.FiniteModuleComplexAcyclicity
public import StacksAndModuli.API.IdealRegularElementAssociatedPrimes
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Data.Nat.Find

/-!
# The minimal-complex step in Buchsbaum--Eisenbud acyclicity

This file packages the part of the local Buchsbaum--Eisenbud acyclicity argument that
applies after contractible identity summands have been removed.  The homological input
is the finite-complex depth lemma: if a largest nonexact positive degree existed, its
homology would have Ext-depth at least one.  If the complex is exact on the punctured
spectrum, that homology is supported only at the closed point.  A nonzero finite module
with that support has an associated prime equal to the maximal ideal, so no element of
the maximal ideal can be regular on it.  Rees's theorem gives the contradiction.

The final theorem extracts the required ring depth from the top expected-minor grade
condition when that minor ideal is proper.  In the usual proof, properness follows for a
minimal complex whose effective top term is nonzero.  The remaining general-complex
step is the unit-entry cancellation of Stacks Project tag 00MT; it is deliberately not
hidden in the hypotheses here.

Main declarations:

* `ModuleCat.ExtDepthAtLeast.pi`;
* `ModuleCat.ExtDepthAtLeast.false_of_support_subset_singleton_closedPoint`;
* `Matrix.FiniteFreeComplex.
  isExactInPositiveDegreesUpTo_of_extDepth_of_support_closedPoint`;
* `Matrix.FiniteFreeComplex.
  isExactInPositiveDegreesUpTo_of_extDepth_of_exact_localizedMap_at_nonclosedPoint`;
* `Matrix.FiniteFreeComplex.
  isExactInPositiveDegreesUpTo_succ_of_buchsbaumEisenbudGrade_of_topMinorIdeal_ne_top`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Module

namespace ModuleCat.ExtDepthAtLeast

variable {R : Type u} [CommRing R]

/-- Ext-depth of the coefficient ring passes to a finite standard free module. -/
theorem pi {I : Ideal R} {n : ℕ}
    (h : ModuleCat.ExtDepthAtLeast I (ModuleCat.of R R) n)
    (κ : Type) [Fintype κ] :
    ModuleCat.ExtDepthAtLeast I (ModuleCat.of R (κ → R)) n := by
  intro i hi
  let X : κ → ModuleCat.{u} R := fun _ ↦ ModuleCat.of R R
  have hpi : Subsingleton
      (∀ j, Ext (ModuleCat.extDepthTestObject I) (X j) i) :=
    ⟨fun a b ↦ funext fun j ↦
      @Subsingleton.elim _ (by
        dsimp only [X]
        exact h i hi) (a j) (b j)⟩
  have hbiproduct : Subsingleton
      (Ext (ModuleCat.extDepthTestObject I) (⨁ X) i) :=
    (Ext.addEquivBiproduct (ModuleCat.extDepthTestObject I)
      (biproduct.isBilimit X) i).subsingleton_congr.mpr hpi
  have htransport : Subsingleton
      (Ext (ModuleCat.extDepthTestObject I)
        (ModuleCat.of R (∀ j, X j)) i) :=
    (((extFunctorObj (ModuleCat.extDepthTestObject I) i).mapIso
      (ModuleCat.biproductIsoPi X)).addCommGroupIsoToAddEquiv.subsingleton_congr).mp
        hbiproduct
  simpa only [X] using htransport

/-- A nonzero finite module over a Noetherian local ring, supported only at the closed
point, cannot have Ext-depth at least one along the maximal ideal. -/
theorem false_of_support_subset_singleton_closedPoint
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : ModuleCat.{u} R} [Module.Finite R M] [Nontrivial M]
    (hdepth : ModuleCat.ExtDepthAtLeast (IsLocalRing.maximalIdeal R) M 1)
    (hsupport : Module.support R M ⊆
      ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R))) :
    False := by
  have hsmul : IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
    rw [← IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact Submodule.jacobson_smul_lt_top _
  obtain ⟨rs, hrsLength, hrsMem, hrsRegular⟩ :=
    (ModuleCat.extDepthAtLeast_iff_exists_isRegular
      (IsLocalRing.maximalIdeal R) M 1 hsmul).mp hdepth
  obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hrsLength
  have hzMaximal : z ∈ IsLocalRing.maximalIdeal R :=
    hrsMem z (by simp)
  have hzRegular : IsSMulRegular M z :=
    (RingTheory.Sequence.isWeaklyRegular_singleton_iff M z).mp
      hrsRegular.toIsWeaklyRegular
  obtain ⟨p, hp⟩ := associatedPrimes.nonempty R M
  have hpSupport :
      (⟨p, IsAssociatedPrime.isPrime hp⟩ : PrimeSpectrum R) ∈
        Module.support R M :=
    (Module.mem_support_iff_of_finite).mpr (by
      rw [← Submodule.annihilator_top]
      exact hp.annihilator_le)
  have hpPoint :
      (⟨p, IsAssociatedPrime.isPrime hp⟩ : PrimeSpectrum R) =
        IsLocalRing.closedPoint R :=
    Set.mem_singleton_iff.mp (hsupport hpSupport)
  have hpIdeal : p = IsLocalRing.maximalIdeal R :=
    congrArg PrimeSpectrum.asIdeal hpPoint
  have hzP : z ∈ p := by
    rw [hpIdeal]
    exact hzMaximal
  have hzUnion : z ∈ ⋃ q ∈ associatedPrimes R M, q :=
    Set.mem_iUnion₂.mpr ⟨p, hp, hzP⟩
  rw [biUnion_associatedPrimes_eq_compl_regular R M] at hzUnion
  exact hzUnion hzRegular

end ModuleCat.ExtDepthAtLeast

namespace Matrix.FiniteFreeComplex

variable {R : Type u} [CommRing R]

/-- The finite-complex acyclicity lemma in support form.  Ring Ext-depth through `N`
and support of every displayed homology module only at the closed point force exactness
in every positive degree through `N`. -/
theorem isExactInPositiveDegreesUpTo_of_extDepth_of_support_closedPoint
    [IsNoetherianRing R] [IsLocalRing R]
    (C : FiniteFreeComplex R) (N : ℕ)
    (hbounded : C.IsBoundedAbove N)
    (hdepthR : ModuleCat.ExtDepthAtLeast (IsLocalRing.maximalIdeal R)
      (ModuleCat.of R R) N)
    (hsupport : ∀ i : ℕ, i < N →
      Module.support R (C.homology i) ⊆
        ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R))) :
    C.IsExactInPositiveDegreesUpTo N := by
  cases N with
  | zero =>
      intro i hi
      omega
  | succ N =>
      by_contra hnotExact
      unfold IsExactInPositiveDegreesUpTo at hnotExact
      push_neg at hnotExact
      obtain ⟨k, hkBound, hkNotExact⟩ := hnotExact
      let P : ℕ → Prop := fun i ↦ ¬ Function.Exact
        (Matrix.toLin' (C.differential (i + 1)))
        (Matrix.toLin' (C.differential i))
      letI : DecidablePred P := Classical.decPred P
      let n := Nat.findGreatest P N
      have hkN : k ≤ N := by omega
      have hnNotExact : P n :=
        Nat.findGreatest_spec (P := P) hkN hkNotExact
      have hnN : n ≤ N := Nat.findGreatest_le (P := P) N
      have hexactAbove : ∀ j : ℕ, n < j → j ≤ N →
          Function.Exact
            (Matrix.toLin' (C.differential (j + 1)))
            (Matrix.toLin' (C.differential j)) := by
        intro j hnj hjN
        exact of_not_not
          (Nat.findGreatest_is_greatest (P := P) hnj hjN)
      have hzero : C.termRank (N + 2) = 0 :=
        hbounded (N + 2) (by omega)
      have hdepthTerms : ∀ j : ℕ, j ≤ N + 1 →
          ModuleCat.ExtDepthAtLeast (IsLocalRing.maximalIdeal R)
            (C.toChainComplex.X j) j := by
        intro j hj
        change ModuleCat.ExtDepthAtLeast (IsLocalRing.maximalIdeal R)
          (ModuleCat.of R (Fin (C.termRank j) → R)) j
        exact (ModuleCat.ExtDepthAtLeast.pi hdepthR
          (Fin (C.termRank j))).of_le hj
      have hhomologyDepth :=
        C.extDepthAtLeast_one_homology_of_exact_above
          (IsLocalRing.maximalIdeal R) hnN hzero hdepthTerms hexactAbove
      have hnonsubsingleton : ¬ Subsingleton (C.homology n) := by
        intro hsubsingleton
        exact hnNotExact
          ((C.isExactAt_iff_subsingleton_homology n).mpr hsubsingleton)
      letI : Nontrivial (C.homology n) :=
        not_subsingleton_iff_nontrivial.mp hnonsubsingleton
      exact ModuleCat.ExtDepthAtLeast.false_of_support_subset_singleton_closedPoint
        hhomologyDepth
          (hsupport n (by omega))

/-- Punctured-spectrum form of the finite-complex acyclicity lemma.  Exactness of every
localized pair away from the closed point says precisely that each homology module is
supported only at that point. -/
theorem isExactInPositiveDegreesUpTo_of_extDepth_of_exact_localizedMap_at_nonclosedPoint
    [IsNoetherianRing R] [IsLocalRing R]
    (C : FiniteFreeComplex R) (N : ℕ)
    (hbounded : C.IsBoundedAbove N)
    (hdepthR : ModuleCat.ExtDepthAtLeast (IsLocalRing.maximalIdeal R)
      (ModuleCat.of R R) N)
    (hpunctured : ∀ p : PrimeSpectrum R, p ≠ IsLocalRing.closedPoint R →
      ∀ i : ℕ, i < N →
        Function.Exact
          (LocalizedModule.map p.asIdeal.primeCompl
            (Matrix.toLin' (C.differential (i + 1))))
          (LocalizedModule.map p.asIdeal.primeCompl
            (Matrix.toLin' (C.differential i)))) :
    C.IsExactInPositiveDegreesUpTo N := by
  apply C.isExactInPositiveDegreesUpTo_of_extDepth_of_support_closedPoint
    N hbounded hdepthR
  intro i hi p hpSupport
  rw [Set.mem_singleton_iff]
  by_contra hp
  exact ((C.notMem_support_homology_iff_exact_localizedMap i p).mpr
    (hpunctured p hp i hi)) hpSupport

/-- The proper-top-minor form of the minimal-complex step.  The regular sequence of
length `N + 1` in the top expected-minor ideal supplies Ext-depth `N + 1` for the ring;
punctured exactness and the finite-complex depth lemma then give global exactness. -/
theorem isExactInPositiveDegreesUpTo_succ_of_buchsbaumEisenbudGrade_of_topMinorIdeal_ne_top
    [IsNoetherianRing R] [IsLocalRing R]
    (C : FiniteFreeComplex R) (N : ℕ) (r : C.ExpectedRanks (N + 1))
    (hbounded : C.IsBoundedAbove (N + 1))
    (hgrade : C.HasBuchsbaumEisenbudGrade r)
    (htop : minorIdeal (C.differential N) (r.rank N) ≠ ⊤)
    (hpunctured : ∀ p : PrimeSpectrum R, p ≠ IsLocalRing.closedPoint R →
      ∀ i : ℕ, i < N + 1 →
        Function.Exact
          (LocalizedModule.map p.asIdeal.primeCompl
            (Matrix.toLin' (C.differential (i + 1))))
          (LocalizedModule.map p.asIdeal.primeCompl
            (Matrix.toLin' (C.differential i)))) :
    C.IsExactInPositiveDegreesUpTo (N + 1) := by
  let I := minorIdeal (C.differential N) (r.rank N)
  have hgradeTop : I = ⊤ ∨
      ∃ f : Fin (N + 1) → R, (∀ j, f j ∈ I) ∧
        RingTheory.Sequence.IsRegular R (List.ofFn f) := by
    simpa only [I] using hgrade N (by omega)
  obtain ⟨f, hfI, hfRegular⟩ := hgradeTop.resolve_left htop
  have hImaximal : I ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal htop
  have hfMaximal : ∀ z ∈ List.ofFn f,
      z ∈ IsLocalRing.maximalIdeal R := by
    intro z hz
    rw [List.mem_ofFn'] at hz
    obtain ⟨j, rfl⟩ := hz
    exact hImaximal (hfI j)
  have hsmul : IsLocalRing.maximalIdeal R •
      (⊤ : Submodule R (ModuleCat.of R R)) < ⊤ := by
    rw [← IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact Submodule.jacobson_smul_lt_top _
  have hdepthR : ModuleCat.ExtDepthAtLeast
      (IsLocalRing.maximalIdeal R) (ModuleCat.of R R) (N + 1) :=
    (ModuleCat.extDepthAtLeast_iff_exists_isRegular
      (IsLocalRing.maximalIdeal R) (ModuleCat.of R R) (N + 1) hsmul).mpr
        ⟨List.ofFn f, by simp, hfMaximal, hfRegular⟩
  exact C.isExactInPositiveDegreesUpTo_of_extDepth_of_exact_localizedMap_at_nonclosedPoint
    (N + 1) hbounded hdepthR hpunctured

end Matrix.FiniteFreeComplex

end
