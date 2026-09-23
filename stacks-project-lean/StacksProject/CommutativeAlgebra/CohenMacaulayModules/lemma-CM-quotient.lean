module

public import StacksProject.CommutativeAlgebra.CohenMacaulayModules.«lemma-CM-good»
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Quotienting a Cohen--Macaulay module by a parameter

This file formalizes Stacks Project tag **00N5**.  If a maximal-ideal element lowers
the support dimension of a finite Cohen--Macaulay module by one, it is a nonzerodivisor
and its quotient is again Cohen--Macaulay.

The proof follows the elementary good-element argument in the Stacks Project.  A single
element is chosen by finite prime avoidance so that it is regular after every proper
prefix of a fixed maximal regular sequence, and so that it also lowers the dimension
after quotienting by the prescribed element.  Tag 00N4 applies to this auxiliary element;
induction and permutability of regular sequences then put the prescribed element first.

Main declaration:

* `Module.IsCohenMacaulayOfDimension.quotient`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open IsLocalRing
open scoped Pointwise

namespace Module

/-- Associated primes of the modules obtained after all proper prefixes of a list.
Avoiding this finite set makes an element regular after every such prefix. -/
private def prefixAssociatedPrimes
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] :
    List R → Set (Ideal R)
  | [] => ∅
  | f :: fs => associatedPrimes R M ∪
      prefixAssociatedPrimes R (QuotSMulTop f M) fs

@[simp]
private theorem prefixAssociatedPrimes_nil
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] :
    prefixAssociatedPrimes R M [] = ∅ :=
  rfl

@[simp]
private theorem prefixAssociatedPrimes_cons
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    (f : R) (fs : List R) :
    prefixAssociatedPrimes R M (f :: fs) =
      associatedPrimes R M ∪ prefixAssociatedPrimes R (QuotSMulTop f M) fs :=
  rfl

private theorem prefixAssociatedPrimes_finite
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (fs : List R) :
    (prefixAssociatedPrimes R M fs).Finite := by
  induction fs generalizing M with
  | nil => simp
  | cons f fs ih =>
      rw [prefixAssociatedPrimes_cons]
      exact (associatedPrimes.finite R M).union
        (ih (M := QuotSMulTop f M))

private theorem prefixAssociatedPrimes_isPrime
    {R : Type u} [CommRing R]
    {M : Type u} [AddCommGroup M] [Module R M]
    {fs : List R} {p : Ideal R}
    (hp : p ∈ prefixAssociatedPrimes R M fs) : p.IsPrime := by
  induction fs generalizing M with
  | nil => simp at hp
  | cons f fs ih =>
      rw [prefixAssociatedPrimes_cons, Set.mem_union] at hp
      exact hp.elim IsAssociatedPrime.isPrime (ih (M := QuotSMulTop f M))

/-- No associated prime occurring before the end of a maximal-ideal regular sequence
is the maximal ideal: the next regular element lies in the maximal ideal but in no
associated prime. -/
private theorem maximalIdeal_not_mem_prefixAssociatedPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (fs : List R) (hmem : ∀ x ∈ fs, x ∈ maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular M fs) :
    maximalIdeal R ∉ prefixAssociatedPrimes R M fs := by
  induction fs generalizing M with
  | nil => simp
  | cons f fs ih =>
      rw [prefixAssociatedPrimes_cons, Set.mem_union]
      push Not
      constructor
      · intro hp
        have hfUnion : f ∈ ⋃ p ∈ associatedPrimes R M, p :=
          Set.mem_iUnion₂.mpr ⟨maximalIdeal R, hp, hmem f (by simp)⟩
        rw [biUnion_associatedPrimes_eq_compl_regular R M] at hfUnion
        exact hfUnion
          ((RingTheory.Sequence.isRegular_cons_iff M f fs).mp hreg).1
      · apply ih (M := QuotSMulTop f M)
        · intro x hx
          exact hmem x (by simp [hx])
        · exact (RingTheory.Sequence.isRegular_cons_iff M f fs).mp hreg |>.2

/-- Avoiding all prefix associated primes produces exactly the recursive good-support
dimension conditions. -/
private theorem hasGoodSupportDimensions_of_avoids_prefixAssociatedPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (fs : List R) (h : R)
    (hdim : supportDim R M = (fs.length : WithBot ℕ∞))
    (hmem : ∀ x ∈ fs, x ∈ maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular M fs)
    (hhmem : h ∈ maximalIdeal R)
    (havoid : ∀ p ∈ prefixAssociatedPrimes R M fs, h ∉ p) :
    HasGoodSupportDimensions R M h fs := by
  induction fs generalizing M with
  | nil => simp
  | cons f fs ih =>
      have hsplit :=
        (RingTheory.Sequence.isRegular_cons_iff M f fs).mp hreg
      have hhreg : IsSMulRegular M h := by
        by_contra hn
        have hhUnion : h ∈ ⋃ p ∈ associatedPrimes R M, p := by
          rw [biUnion_associatedPrimes_eq_compl_regular R M]
          exact hn
        obtain ⟨p, hp, hhp⟩ := Set.mem_iUnion₂.mp hhUnion
        exact havoid p (by simp [hp]) hhp
      have hdimH : supportDim R (QuotSMulTop h M) =
          (fs.length : WithBot ℕ∞) := by
        apply ENat.WithBot.add_one_cancel.mp
        calc
          supportDim R (QuotSMulTop h M) + 1 = supportDim R M :=
            supportDim_quotSMulTop_succ_eq_supportDim hhreg hhmem
          _ = ((f :: fs).length : WithBot ℕ∞) := hdim
          _ = (fs.length : WithBot ℕ∞) + 1 := by simp
      have hdimTail : supportDim R (QuotSMulTop f M) =
          (fs.length : WithBot ℕ∞) := by
        apply ENat.WithBot.add_one_cancel.mp
        calc
          supportDim R (QuotSMulTop f M) + 1 = supportDim R M :=
            supportDim_quotSMulTop_succ_eq_supportDim hsplit.1
              (hmem f (by simp))
          _ = ((f :: fs).length : WithBot ℕ∞) := hdim
          _ = (fs.length : WithBot ℕ∞) + 1 := by simp
      refine ⟨hdimH, ih (M := QuotSMulTop f M) hdimTail ?_ hsplit.2 ?_⟩
      · intro x hx
        exact hmem x (by simp [hx])
      · intro p hp
        exact havoid p (by simp [hp])

/-- A positive-dimensional finite module cannot have the maximal ideal as a minimal
prime of its annihilator. -/
private theorem maximalIdeal_not_mem_minimalPrimes_annihilator_of_supportDim_eq_succ
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]
    {d : ℕ} (hdim : supportDim R M = ((d + 1 : ℕ) : WithBot ℕ∞)) :
    maximalIdeal R ∉ (annihilator R M).minimalPrimes := by
  intro hm
  letI : Nontrivial M :=
    (supportDim_ne_bot_iff_nontrivial R M).mp (by rw [hdim]; simp)
  have hsupport : support R M =
      ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)) := by
    apply Set.Subset.antisymm
    · intro p hp
      rw [Set.mem_singleton_iff]
      apply PrimeSpectrum.ext
      apply le_antisymm (le_maximalIdeal p.2.ne_top)
      exact hm.2 ⟨p.2, (mem_support_iff_of_finite.mp hp)⟩
        (le_maximalIdeal p.2.ne_top)
    · simpa using IsLocalRing.closedPoint_mem_support R M
  have hzero : supportDim R M = 0 := by
    rw [supportDim, hsupport]
    exact Order.krullDim_eq_zero
  have hne : (0 : WithBot ℕ∞) ≠ ((d + 1 : ℕ) : WithBot ℕ∞) := by
    exact_mod_cast Nat.zero_ne_add_one d
  exact hne (hzero.symm.trans hdim)

/-- Finite prime avoidance inside the maximal ideal. -/
private theorem exists_mem_maximalIdeal_avoiding_finite_primes
    {R : Type u} [CommRing R] [IsLocalRing R]
    (S : Set (Ideal R)) (hfinite : S.Finite)
    (hprime : ∀ p ∈ S, p.IsPrime)
    (hmax : maximalIdeal R ∉ S) :
    ∃ h ∈ maximalIdeal R, ∀ p ∈ S, h ∉ p := by
  by_contra hnone
  push Not at hnone
  have hsubset : (maximalIdeal R : Set R) ⊆ ⋃ p ∈ S, p := by
    intro h hh
    obtain ⟨p, hp, hhp⟩ := hnone h hh
    exact Set.mem_iUnion₂.mpr ⟨p, hp, hhp⟩
  have hmS : maximalIdeal R ∈ S :=
    (Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite
      (M := maximalIdeal R) hfinite (⊥ : Ideal R) ⊥
      (fun p hp _ _ ↦ hprime p hp) bot_ne_top bot_ne_top).mp hsubset
  exact hmax hmS

/-- The two orders of quotienting a finite module by two elements have the same support
dimension. -/
private theorem supportDim_quotSMulTop_comm
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (f g : R) :
    supportDim R (QuotSMulTop f (QuotSMulTop g M)) =
      supportDim R (QuotSMulTop g (QuotSMulTop f M)) := by
  have hsupport : support R (QuotSMulTop f (QuotSMulTop g M)) =
      support R (QuotSMulTop g (QuotSMulTop f M)) := by
    simp only [support_quotSMulTop]
    ac_rfl
  rw [supportDim, supportDim, hsupport]

namespace IsCohenMacaulayOfDimension

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- **Stacks 00N5** (`commalg-lemma-CM-quotient`).  Let `M` be a finite
Cohen--Macaulay module of dimension `d + 1`.  If `g` belongs to the maximal ideal and
`M/gM` has support dimension `d`, then `g` is a nonzerodivisor on `M` and `M/gM` is
Cohen--Macaulay of dimension `d`. -/
@[stacks 00N5]
theorem quotient {d : ℕ}
    (hCM : IsCohenMacaulayOfDimension R M (d + 1))
    {g : R} (hg : g ∈ maximalIdeal R)
    (hQdim : supportDim R (QuotSMulTop g M) = (d : WithBot ℕ∞)) :
    IsSMulRegular M g ∧
      IsCohenMacaulayOfDimension R (QuotSMulTop g M) d := by
  induction d generalizing M with
  | zero =>
      letI : Nontrivial M :=
        (supportDim_ne_bot_iff_nontrivial R M).mp (by rw [hCM.1]; simp)
      have hsmul : maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
        rw [← IsLocalRing.ringJacobson_eq_maximalIdeal]
        exact Submodule.jacobson_smul_lt_top _
      obtain ⟨rs, hrslen, hrsmem, hrsreg⟩ :=
        (ModuleCat.extDepthAtLeast_iff_exists_isRegular
          (maximalIdeal R) (ModuleCat.of R M) 1 hsmul).mp hCM.2
      obtain ⟨f, rfl⟩ : ∃ f : R, rs = [f] := by
        exact List.length_eq_one_iff.mp hrslen
      have hgood : IsGoodFor R M [f] g := by
        refine ⟨hg, ?_⟩
        simpa using hQdim
      have hout := IsGoodFor.isSMulRegular_and_isCohenMacaulay
        f [] g (by simpa using hCM) (by simpa using hrsmem) hrsreg hgood
      exact ⟨hout.1, hout.2.1⟩
  | succ d ih =>
      letI : Nontrivial M :=
        (supportDim_ne_bot_iff_nontrivial R M).mp (by rw [hCM.1]; simp)
      have hsmul : maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
        rw [← IsLocalRing.ringJacobson_eq_maximalIdeal]
        exact Submodule.jacobson_smul_lt_top _
      obtain ⟨rs, hrslen, hrsmem, hrsreg⟩ :=
        (ModuleCat.extDepthAtLeast_iff_exists_isRegular
          (maximalIdeal R) (ModuleCat.of R M) (d + 2) hsmul).mp (by
            simpa [Nat.succ_eq_add_one, add_assoc] using hCM.2)
      obtain ⟨f, fs, rfl⟩ : ∃ f fs, rs = f :: fs := by
        cases rs with
        | nil => simp at hrslen
        | cons f fs => exact ⟨f, fs, rfl⟩
      have hfslen : fs.length = d + 1 := by
        simpa using hrslen
      let P := prefixAssociatedPrimes R M (f :: fs)
      let Q := (annihilator R (QuotSMulTop g M)).minimalPrimes
      let S : Set (Ideal R) := P ∪ Q
      have hPfinite : P.Finite :=
        prefixAssociatedPrimes_finite (R := R) (M := M) (f :: fs)
      have hQfinite : Q.Finite :=
        (annihilator R (QuotSMulTop g M)).finite_minimalPrimes_of_isNoetherianRing R
      have hSfinite : S.Finite := hPfinite.union hQfinite
      have hSprime : ∀ p ∈ S, p.IsPrime := by
        intro p hp
        rcases hp with hp | hp
        · exact prefixAssociatedPrimes_isPrime hp
        · exact hp.isPrime
      have hmP : maximalIdeal R ∉ P := by
        exact maximalIdeal_not_mem_prefixAssociatedPrimes (f :: fs) hrsmem hrsreg
      have hmQ : maximalIdeal R ∉ Q := by
        apply maximalIdeal_not_mem_minimalPrimes_annihilator_of_supportDim_eq_succ
          (d := d)
        simpa [Nat.succ_eq_add_one] using hQdim
      have hmS : maximalIdeal R ∉ S := by
        simp only [S, Set.mem_union, not_or]
        exact ⟨hmP, hmQ⟩
      obtain ⟨h, hhmem, hhavoid⟩ :=
        exists_mem_maximalIdeal_avoiding_finite_primes S hSfinite hSprime hmS
      have hhavoidP : ∀ p ∈ P, h ∉ p := by
        intro p hp
        exact hhavoid p (Set.mem_union_left Q hp)
      have hhavoidQ : ∀ p ∈ Q, h ∉ p := by
        intro p hp
        exact hhavoid p (Set.mem_union_right P hp)
      have hgood : IsGoodFor R M (f :: fs) h := by
        refine ⟨hhmem, ?_⟩
        apply hasGoodSupportDimensions_of_avoids_prefixAssociatedPrimes
          (f :: fs) h
        · rw [hrslen]
          have hindex : d + 1 + 1 = d + 2 := by omega
          simpa only [hindex] using hCM.1
        · exact hrsmem
        · exact hrsreg
        · exact hhmem
        · exact hhavoidP
      have hCM' : IsCohenMacaulayOfDimension R M (f :: fs).length := by
        simpa [hrslen] using hCM
      obtain ⟨hhreg, hCMh, -⟩ :=
        IsGoodFor.isSMulRegular_and_isCohenMacaulay
          f fs h hCM' hrsmem hrsreg hgood
      have hdim_h_after_g : supportDim R
          (QuotSMulTop h (QuotSMulTop g M)) = (d : WithBot ℕ∞) := by
        apply ENat.WithBot.add_one_cancel.mp
        calc
          supportDim R (QuotSMulTop h (QuotSMulTop g M)) + 1 =
              supportDim R (QuotSMulTop g M) :=
            supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
              hhavoidQ hhmem
          _ = ((d + 1 : ℕ) : WithBot ℕ∞) := by
            simpa [Nat.succ_eq_add_one] using hQdim
          _ = (d : WithBot ℕ∞) + 1 := by simp
      have hdim_g_after_h : supportDim R
          (QuotSMulTop g (QuotSMulTop h M)) = (d : WithBot ℕ∞) := by
        rw [← supportDim_quotSMulTop_comm h g]
        exact hdim_h_after_g
      have hCMh' : IsCohenMacaulayOfDimension R (QuotSMulTop h M) (d + 1) := by
        simpa [hfslen] using hCMh
      obtain ⟨hgAfterH, hCMhg⟩ :=
        ih (M := QuotSMulTop h M) hCMh' hdim_g_after_h
      let N := QuotSMulTop g (QuotSMulTop h M)
      letI : Nontrivial N :=
        (supportDim_ne_bot_iff_nontrivial R N).mp (by rw [hCMhg.1]; simp)
      have hsmulN : maximalIdeal R • (⊤ : Submodule R N) < ⊤ := by
        rw [← IsLocalRing.ringJacobson_eq_maximalIdeal]
        exact Submodule.jacobson_smul_lt_top _
      obtain ⟨ts, htslen, htsmem, htsreg⟩ :=
        (ModuleCat.extDepthAtLeast_iff_exists_isRegular
          (maximalIdeal R) (ModuleCat.of R N) d hsmulN).mp hCMhg.2
      have hregAfterH : RingTheory.Sequence.IsRegular (QuotSMulTop h M)
          (g :: ts) := RingTheory.Sequence.IsRegular.cons hgAfterH htsreg
      have hregHG : RingTheory.Sequence.IsRegular M (h :: g :: ts) :=
        RingTheory.Sequence.IsRegular.cons hhreg hregAfterH
      have hregGH : RingTheory.Sequence.IsRegular M (g :: h :: ts) :=
        IsLocalRing.isRegular_of_perm hregHG (List.Perm.swap h g ts).symm
      obtain ⟨hgM, hregTail⟩ :=
        (RingTheory.Sequence.isRegular_cons_iff M g (h :: ts)).mp hregGH
      letI : Nontrivial (QuotSMulTop g M) := hregTail.nontrivial
      refine ⟨hgM, IsCohenMacaulayOfDimension.of_isRegular hQdim
        (h :: ts) ?_ ?_ hregTail⟩
      · simp [htslen]
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hhmem
        · exact htsmem x hx

end IsCohenMacaulayOfDimension

end Module

end

end
