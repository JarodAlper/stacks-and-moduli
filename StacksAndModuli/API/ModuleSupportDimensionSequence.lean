module

public import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Support dimension after quotienting by a finite sequence

Let `M` be a finite module over a Noetherian local ring.  Successively quotienting by
elements of the maximal ideal lowers support dimension by at most the length of the
sequence.  If equality holds after quotienting by a nonempty sequence, equality already
holds at its first step.

These are the dimension-bookkeeping lemmas used to iterate the one-element
Cohen--Macaulay quotient theorem.

Main declarations:

* `Module.supportDim_le_supportDim_quotient_ofList_add_length`;
* `Module.supportDim_quotSMulTop_add_one_eq_of_endpoint_eq`;
* `Module.supportDim_quotSMulTop_eq_of_endpoint_eq_nat`.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

universe u v

namespace Module

open Ideal IsLocalRing RingTheory Sequence Submodule

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Quotienting a finite module by a list of elements of the maximal ideal lowers its
support dimension by at most the length of the list. -/
theorem supportDim_le_supportDim_quotient_ofList_add_length
    (rs : List R) (hmem : ∀ x ∈ rs, x ∈ maximalIdeal R) :
    supportDim R M ≤
      supportDim R (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M))) + rs.length := by
  induction rs generalizing M with
  | nil =>
      rw [Ideal.ofList_nil, Submodule.bot_smul]
      simpa using (supportDim_eq_of_equiv
        (Submodule.quotEquivOfEqBot (⊥ : Submodule R M) rfl)).ge
  | cons x rs ih =>
      have hx : x ∈ maximalIdeal R := hmem x (by simp)
      have hrs : ∀ y ∈ rs, y ∈ maximalIdeal R := by
        intro y hy
        exact hmem y (by simp [hy])
      calc
        supportDim R M ≤ supportDim R (QuotSMulTop x M) + 1 :=
          supportDim_le_supportDim_quotSMulTop_succ hx
        _ ≤
            (supportDim R
                (QuotSMulTop x M ⧸
                  (Ideal.ofList rs • (⊤ : Submodule R (QuotSMulTop x M)))) +
              rs.length) + 1 :=
          add_le_add (ih (M := QuotSMulTop x M) hrs) le_rfl
        _ = supportDim R
              (M ⧸ (Ideal.ofList (x :: rs) • (⊤ : Submodule R M))) +
              (x :: rs).length := by
          rw [add_assoc]
          rw [supportDim_eq_of_equiv
            (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs)]
          simp

/-- If quotienting by a nonempty maximal-ideal sequence achieves the maximal possible
support-dimension drop, then its first element already drops support dimension by one. -/
theorem supportDim_quotSMulTop_add_one_eq_of_endpoint_eq
    (x : R) (rs : List R)
    (hx : x ∈ maximalIdeal R)
    (hrs : ∀ y ∈ rs, y ∈ maximalIdeal R)
    (hendpoint :
      supportDim R
          (M ⧸ (Ideal.ofList (x :: rs) • (⊤ : Submodule R M))) +
          (x :: rs).length =
        supportDim R M) :
    supportDim R (QuotSMulTop x M) + 1 = supportDim R M := by
  apply le_antisymm
  · calc
      supportDim R (QuotSMulTop x M) + 1 ≤
          (supportDim R
              (QuotSMulTop x M ⧸
                (Ideal.ofList rs • (⊤ : Submodule R (QuotSMulTop x M)))) +
            rs.length) + 1 :=
        add_le_add
          (supportDim_le_supportDim_quotient_ofList_add_length
            (M := QuotSMulTop x M) rs hrs) le_rfl
      _ = supportDim R
            (M ⧸ (Ideal.ofList (x :: rs) • (⊤ : Submodule R M))) +
            (x :: rs).length := by
        rw [add_assoc]
        rw [supportDim_eq_of_equiv
          (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner M x rs)]
        simp
      _ = supportDim R M := hendpoint
  · exact supportDim_le_supportDim_quotSMulTop_succ hx

/-- Natural-number form of first-step equality: if a module has support dimension equal
to `d` plus the length of a nonempty maximal-ideal sequence, and its quotient by the whole
sequence has support dimension `d`, then quotienting by the first element leaves support
dimension `d` plus the length of the tail. -/
theorem supportDim_quotSMulTop_eq_of_endpoint_eq_nat
    (x : R) (rs : List R) (d : ℕ)
    (hx : x ∈ maximalIdeal R)
    (hrs : ∀ y ∈ rs, y ∈ maximalIdeal R)
    (hM : supportDim R M = (d + (x :: rs).length : ℕ))
    (hendpoint :
      supportDim R
        (M ⧸ (Ideal.ofList (x :: rs) • (⊤ : Submodule R M))) = d) :
    supportDim R (QuotSMulTop x M) = (d + rs.length : ℕ) := by
  have hendpoint' :
      supportDim R
          (M ⧸ (Ideal.ofList (x :: rs) • (⊤ : Submodule R M))) +
          (x :: rs).length =
        supportDim R M := by
    rw [hendpoint, hM]
    simp
  exact ENat.WithBot.add_one_cancel.mp <| by
    calc
      supportDim R (QuotSMulTop x M) + 1 = supportDim R M :=
        supportDim_quotSMulTop_add_one_eq_of_endpoint_eq x rs hx hrs hendpoint'
      _ = (d + (x :: rs).length : ℕ) := hM
      _ = (d + rs.length : ℕ) + 1 := by simp [add_assoc]

end Module

end

end
