module

public import StacksProject.CommutativeAlgebra.CohenMacaulayModules.«lemma-CM-quotient»
public import StacksAndModuli.API.ModuleSupportDimensionSequence

/-!
# Extending parameter sequences on Cohen--Macaulay modules

This file formalizes Stacks Project tag **00N6**.  A sequence in the maximal ideal of a
finite Cohen--Macaulay module is regular when its final quotient has the maximal possible
support-dimension drop.  The sequence then extends to one whose length is the support
dimension of the module.

The proof repeatedly applies the one-element Cohen--Macaulay quotient theorem.  The
support-dimension equality at each first step is supplied by the finite-sequence
dimension inequality in `ModuleSupportDimensionSequence`.

Main declarations:

* `Module.IsCohenMacaulayOfDimension.isRegular_of_supportDim_quotient_eq`;
* `Module.IsCohenMacaulayOfDimension.exists_isRegular_extension`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open IsLocalRing
open scoped Pointwise

namespace Module.IsCohenMacaulayOfDimension

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Inductive core of the parameter-sequence extension theorem. -/
private theorem exists_extension_core {d : ℕ} (rs : List R)
    (hCM : Module.IsCohenMacaulayOfDimension R M (d + rs.length))
    (hmem : ∀ x ∈ rs, x ∈ maximalIdeal R)
    (hquot :
      Module.supportDim R
        (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) = d) :
    ∃ ts : List R,
      (∀ x ∈ ts, x ∈ maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular M (rs ++ ts) ∧
          (rs ++ ts).length = d + rs.length := by
  induction rs generalizing M with
  | nil =>
      letI : Nontrivial M :=
        (Module.supportDim_ne_bot_iff_nontrivial R M).mp (by rw [hCM.1]; simp)
      have hsmul : maximalIdeal R • (⊤ : Submodule R M) < ⊤ := by
        rw [← IsLocalRing.ringJacobson_eq_maximalIdeal]
        exact Submodule.jacobson_smul_lt_top _
      obtain ⟨ts, htslen, htsmem, htsreg⟩ :=
        (ModuleCat.extDepthAtLeast_iff_exists_isRegular
          (maximalIdeal R) (ModuleCat.of R M) d hsmul).mp hCM.2
      exact ⟨ts, htsmem, htsreg, by simp [htslen]⟩
  | cons x rs ih =>
      have hx : x ∈ maximalIdeal R := hmem x (by simp)
      have hrs : ∀ y ∈ rs, y ∈ maximalIdeal R := by
        intro y hy
        exact hmem y (by simp [hy])
      have hfirstDim : Module.supportDim R (QuotSMulTop x M) =
          (d + rs.length : ℕ) :=
        Module.supportDim_quotSMulTop_eq_of_endpoint_eq_nat
          x rs d hx hrs hCM.1 hquot
      have hCM' : Module.IsCohenMacaulayOfDimension R M
          ((d + rs.length) + 1) := by
        simpa [add_assoc] using hCM
      obtain ⟨hxreg, hCMquot⟩ := hCM'.quotient hx hfirstDim
      have htailQuot :
          Module.supportDim R
            (QuotSMulTop x M ⧸
              (Ideal.ofList rs • (⊤ : Submodule R (QuotSMulTop x M)))) = d := by
        calc
          Module.supportDim R
              (QuotSMulTop x M ⧸
                (Ideal.ofList rs • (⊤ : Submodule R (QuotSMulTop x M)))) =
              Module.supportDim R
                (M ⧸ (Ideal.ofList (x :: rs) • (⊤ : Submodule R M))) :=
            Module.supportDim_eq_of_equiv
              (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs).symm
          _ = d := hquot
      obtain ⟨ts, htsmem, htailReg, hlength⟩ :=
        ih (M := QuotSMulTop x M) hCMquot hrs htailQuot
      refine ⟨ts, htsmem, ?_, ?_⟩
      · simpa only [List.cons_append] using
          RingTheory.Sequence.IsRegular.cons hxreg htailReg
      · simpa [add_assoc] using congrArg Nat.succ hlength

/-- **Proposition 10.103.4** (`00N6`), regularity part.  Let `M` be a finite
Cohen--Macaulay module of support dimension `d + rs.length`.  If the elements of `rs`
belong to the maximal ideal and the quotient by `rs` has support dimension `d`, then
`rs` is an `M`-regular sequence. -/
@[stacks 00N6]
theorem isRegular_of_supportDim_quotient_eq {d : ℕ} (rs : List R)
    (hCM : Module.IsCohenMacaulayOfDimension R M (d + rs.length))
    (hmem : ∀ x ∈ rs, x ∈ maximalIdeal R)
    (hquot :
      Module.supportDim R
        (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) = d) :
    RingTheory.Sequence.IsRegular M rs := by
  obtain ⟨ts, -, hfull, -⟩ := exists_extension_core rs hCM hmem hquot
  have hweak : RingTheory.Sequence.IsWeaklyRegular M rs :=
    ((RingTheory.Sequence.isWeaklyRegular_append_iff M rs ts).mp
      hfull.toIsWeaklyRegular).1
  refine ⟨hweak, ?_⟩
  intro htop
  apply hfull.top_ne_smul
  rw [Ideal.ofList_append]
  apply le_antisymm _ le_top
  calc
    (⊤ : Submodule R M) = Ideal.ofList rs • ⊤ := htop
    _ ≤ (Ideal.ofList rs ⊔ Ideal.ofList ts) • ⊤ :=
      Submodule.smul_mono le_sup_left le_rfl

/-- **Proposition 10.103.4** (`00N6`), extension part.  Under the same maximal
support-dimension-drop hypothesis, `rs` extends by maximal-ideal elements to an
`M`-regular sequence whose length is the support dimension of `M`. -/
@[stacks 00N6]
theorem exists_isRegular_extension {d : ℕ} (rs : List R)
    (hCM : Module.IsCohenMacaulayOfDimension R M (d + rs.length))
    (hmem : ∀ x ∈ rs, x ∈ maximalIdeal R)
    (hquot :
      Module.supportDim R
        (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) = d) :
    ∃ ts : List R,
      (∀ x ∈ ts, x ∈ maximalIdeal R) ∧
        RingTheory.Sequence.IsRegular M (rs ++ ts) ∧
          (rs ++ ts).length = d + rs.length :=
  exists_extension_core rs hCM hmem hquot

end Module.IsCohenMacaulayOfDimension

end

end
