module

public import StacksProject.CommutativeAlgebra.CohenMacaulayModules.«definition-CM»
public import StacksAndModuli.API.FiniteFreeComplexBuchsbaumEisenbudMinimal

/-!
# Good elements on Cohen--Macaulay modules

This file formalizes the elementary good-element argument of Stacks Project tag
**00N4**.  For a maximal regular sequence `f₁, …, f_d`, an element `g` is good when
successively quotienting by `g` after each proper prefix has the expected support
dimension.  The recursive definition below is the iterated-quotient form of the
definition in the Stacks Project.

The proof follows the Stacks induction.  In dimension one, the `g`-torsion submodule
is supported only at the closed point.  The first regular element gives that submodule
Ext-depth at least one, contradicting the closed-point depth lemma unless the torsion
is zero.  In higher dimension, induction after quotienting by the first regular element
and permutability of regular sequences swap that first element with `g`.

Main declarations:

* `Module.HasGoodSupportDimensions`;
* `Module.IsGoodFor`;
* `Module.IsGoodFor.isSMulRegular_and_isCohenMacaulay`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u v

open IsLocalRing
open scoped Pointwise

namespace Module

variable (R : Type u) [CommRing R]

/-- The support-dimension part of being good for a regular sequence.  For
`f :: fs`, quotienting the current module by `g` has dimension `fs.length`, and the
same condition continues after quotienting the current module by `f`. -/
def HasGoodSupportDimensions (M : Type v) [AddCommGroup M] [Module R M]
    (g : R) : List R → Prop
  | [] => True
  | f :: fs =>
      supportDim R (QuotSMulTop g M) = (fs.length : WithBot ℕ∞) ∧
        HasGoodSupportDimensions (QuotSMulTop f M) g fs

variable [IsLocalRing R]

/-- An element of the maximal ideal is good for `fs` on `M` when all the successive
support dimensions after quotienting by it have the expected values. -/
def IsGoodFor (M : Type v) [AddCommGroup M] [Module R M]
    (fs : List R) (g : R) : Prop :=
  g ∈ maximalIdeal R ∧ HasGoodSupportDimensions R M g fs

@[simp]
theorem hasGoodSupportDimensions_nil
    (M : Type v) [AddCommGroup M] [Module R M] (g : R) :
    HasGoodSupportDimensions R M g [] :=
  trivial

@[simp]
theorem hasGoodSupportDimensions_cons
    (M : Type v) [AddCommGroup M] [Module R M] (g f : R) (fs : List R) :
    HasGoodSupportDimensions R M g (f :: fs) ↔
      supportDim R (QuotSMulTop g M) = (fs.length : WithBot ℕ∞) ∧
        HasGoodSupportDimensions R (QuotSMulTop f M) g fs :=
  Iff.rfl

namespace IsGoodFor

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Dimension-one good-element step: if `f` is regular on `M`, while `M/gM` has
zero-dimensional support, then `g` is regular on `M`.

The proof isolates the `g`-torsion submodule.  It inherits regularity of `f`, but its
support is contained in the zero-dimensional support of `M/gM`; the closed-point
Ext-depth lemma therefore forces it to vanish. -/
private theorem isSMulRegular_of_supportDim_quotSMulTop_eq_zero
    {f g : R} (hf : IsSMulRegular M f) (hfmem : f ∈ maximalIdeal R)
    (hdim : supportDim R (QuotSMulTop g M) = 0) :
    IsSMulRegular M g := by
  rw [isSMulRegular_iff_torsionBy_eq_bot]
  by_contra hne
  let K : Submodule R M := Submodule.torsionBy R M g
  have hKne : K ≠ ⊥ := by
    simpa only [K] using hne
  letI : Nontrivial K := Submodule.nontrivial_iff_ne_bot.mpr hKne
  have hfiniteK : Module.Finite R K := inferInstance
  letI : Module.Finite R K := hfiniteK
  have hfK : IsSMulRegular K f := hf.submodule K f
  have hweakK : RingTheory.Sequence.IsWeaklyRegular K [f] :=
    (RingTheory.Sequence.isWeaklyRegular_singleton_iff K f).mpr hfK
  have hregK : RingTheory.Sequence.IsRegular K [f] :=
    RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
      (L := K) (by simpa using hfmem) hweakK
  have hsmulK : maximalIdeal R • (⊤ : Submodule R K) < ⊤ := by
    rw [← IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact Submodule.jacobson_smul_lt_top _
  have hdepthK : ModuleCat.ExtDepthAtLeast
      (maximalIdeal R) (ModuleCat.of R K) 1 := by
    apply (ModuleCat.extDepthAtLeast_iff_exists_isRegular
      (maximalIdeal R) (ModuleCat.of R K) 1 hsmulK).mpr
    exact ⟨[f], by simp, by simpa using hfmem, hregK⟩
  have hsupportK : support R K ⊆ support R (QuotSMulTop g M) := by
    rw [support_quotSMulTop]
    refine Set.subset_inter
      (support_subset_of_injective K.subtype K.injective_subtype) ?_
    intro p hp
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
    have hgann : g ∈ annihilator R K := by
      apply mem_annihilator.mpr
      intro x
      apply Subtype.ext
      change g • (x : M) = 0
      exact x.2
    exact (mem_support_iff_of_finite.mp hp) hgann
  have hsupportClosed : support R K ⊆
      ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)) := by
    have hQ := support_of_supportDim_eq_zero R (QuotSMulTop g M) hdim
    rw [PrimeSpectrum.zeroLocus_eq_singleton] at hQ
    exact hsupportK.trans hQ.subset
  exact ModuleCat.ExtDepthAtLeast.false_of_support_subset_singleton_closedPoint
    hdepthK hsupportClosed

/-- The regular-sequence content of the good-element induction.  If `g` is good for a
nonempty regular sequence, then `g` is regular and the sequence obtained by deleting
the last original element is regular after quotienting by `g`. -/
private theorem isSMulRegular_and_isRegular_dropLast
    (f : R) (fs : List R) (g : R)
    (hmem : ∀ x ∈ f :: fs, x ∈ maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular M (f :: fs))
    (hgood : IsGoodFor R M (f :: fs) g) :
    IsSMulRegular M g ∧
      RingTheory.Sequence.IsRegular (QuotSMulTop g M) (f :: fs).dropLast := by
  induction fs generalizing M f with
  | nil =>
      have hf : IsSMulRegular M f :=
        (RingTheory.Sequence.isRegular_cons_iff M f []).mp hreg |>.1
      have hg : IsSMulRegular M g :=
        isSMulRegular_of_supportDim_quotSMulTop_eq_zero hf
          (hmem f (by simp)) (by simpa [IsGoodFor] using hgood.2.1)
      haveI : Nontrivial M := hreg.nontrivial
      letI : Nontrivial (QuotSMulTop g M) :=
        nontrivial_quotSMulTop_of_mem_maximalIdeal M hgood.1
      exact ⟨hg, by simpa using
        (RingTheory.Sequence.IsRegular.nil R (QuotSMulTop g M))⟩
  | cons f₂ fs ih =>
      have hsplit :=
        (RingTheory.Sequence.isRegular_cons_iff M f (f₂ :: fs)).mp hreg
      have hmemTail : ∀ x ∈ f₂ :: fs, x ∈ maximalIdeal R := by
        intro x hx
        exact hmem x (by simp [hx])
      have hgoodTail : IsGoodFor R (QuotSMulTop f M) (f₂ :: fs) g :=
        ⟨hgood.1, by simpa [IsGoodFor] using hgood.2.2⟩
      obtain ⟨hgTail, htail⟩ :=
        ih (M := QuotSMulTop f M) f₂ hmemTail hsplit.2 hgoodTail
      have hregAfterF : RingTheory.Sequence.IsRegular (QuotSMulTop f M)
          (g :: (f₂ :: fs).dropLast) :=
        RingTheory.Sequence.IsRegular.cons hgTail htail
      have hregFG : RingTheory.Sequence.IsRegular M
          (f :: g :: (f₂ :: fs).dropLast) :=
        RingTheory.Sequence.IsRegular.cons hsplit.1 hregAfterF
      have hregGF : RingTheory.Sequence.IsRegular M
          (g :: f :: (f₂ :: fs).dropLast) :=
        IsLocalRing.isRegular_of_perm hregFG
          (List.Perm.swap f g (f₂ :: fs).dropLast).symm
      have hout :=
        (RingTheory.Sequence.isRegular_cons_iff M g
          (f :: (f₂ :: fs).dropLast)).mp hregGF
      simpa only [List.dropLast_cons_cons] using hout

/-- A good element for a nonempty regular sequence is a nonzerodivisor; its quotient
has the expected Cohen--Macaulay structure, exhibited by the original sequence with
its last element deleted.  This is the stronger regular-sequence API underlying the
faithful tagged endpoint below. -/
theorem isSMulRegular_and_isCohenMacaulay_of_isRegular
    (f : R) (fs : List R) (g : R)
    (hmem : ∀ x ∈ f :: fs, x ∈ maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular M (f :: fs))
    (hgood : IsGoodFor R M (f :: fs) g) :
    IsSMulRegular M g ∧
      IsCohenMacaulayOfDimension R (QuotSMulTop g M) fs.length ∧
      RingTheory.Sequence.IsRegular (QuotSMulTop g M) (f :: fs).dropLast := by
  obtain ⟨hg, hdrop⟩ :=
    isSMulRegular_and_isRegular_dropLast f fs g hmem hreg hgood
  haveI : Nontrivial M := hreg.nontrivial
  letI : Nontrivial (QuotSMulTop g M) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal M hgood.1
  refine ⟨hg, IsCohenMacaulayOfDimension.of_isRegular hgood.2.1
    (f :: fs).dropLast ?_ ?_ hdrop, hdrop⟩
  · simp
  · intro x hx
    exact hmem x (List.mem_of_mem_dropLast hx)

/-- **Stacks 00N4** (`commalg-lemma-CM-good`).  Let `f :: fs` be a maximal regular
sequence on a Cohen--Macaulay module.  If `g` is good with respect to this sequence,
then `g` is a nonzerodivisor and `M/gM` is Cohen--Macaulay of dimension one less, with
maximal regular sequence `(f :: fs).dropLast`. -/
@[stacks 00N4]
theorem isSMulRegular_and_isCohenMacaulay
    (f : R) (fs : List R) (g : R)
    (hCM : IsCohenMacaulayOfDimension R M (f :: fs).length)
    (hmem : ∀ x ∈ f :: fs, x ∈ maximalIdeal R)
    (hreg : RingTheory.Sequence.IsRegular M (f :: fs))
    (hgood : IsGoodFor R M (f :: fs) g) :
    IsSMulRegular M g ∧
      IsCohenMacaulayOfDimension R (QuotSMulTop g M) fs.length ∧
      RingTheory.Sequence.IsRegular (QuotSMulTop g M) (f :: fs).dropLast := by
  have _hmaximal : supportDim R M = ((f :: fs).length : WithBot ℕ∞) :=
    hCM.supportDim_eq
  exact isSMulRegular_and_isCohenMacaulay_of_isRegular f fs g hmem hreg hgood

end IsGoodFor

end Module

end

end
