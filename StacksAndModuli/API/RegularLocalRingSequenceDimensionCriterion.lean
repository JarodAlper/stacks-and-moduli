module

public import StacksAndModuli.API.RegularLocalRingExtDepth
public import StacksProject.CommutativeAlgebra.CohenMacaulayModules.«proposition-CM-regular-sequence»

/-!
# A dimension criterion for regular sequences in regular local rings

In a regular local ring of finite Krull dimension `n`, a list in the maximal ideal is a
regular sequence as soon as the quotient has dimension at most `n` minus the list length.
The opposite dimension inequality is automatic, so the assumed upper bound gives the
exact support-dimension drop required by the Cohen--Macaulay parameter criterion.

Main declaration:

* `RingTheory.Sequence.isRegular_of_isRegularLocalRing_of_quotient_dimension_le_sub`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open scoped Pointwise

namespace RingTheory.Sequence

/-- A list in the maximal ideal of an `n`-dimensional regular local ring is regular if
its quotient has dimension at most `n` minus the list length. -/
theorem isRegular_of_isRegularLocalRing_of_quotient_dimension_le_sub
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (n : ℕ) (hdim : ringKrullDim R = (n : WithBot ℕ∞))
    (rs : List R) (hmem : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R)
    (hlength : rs.length ≤ n)
    (hquot : ringKrullDim (R ⧸ Ideal.ofList rs) ≤
      ((n - rs.length : ℕ) : WithBot ℕ∞)) :
    IsRegular R rs := by
  let e := n - rs.length
  have headd : e + rs.length = n := by
    dsimp only [e]
    exact Nat.sub_add_cancel hlength
  have hCM : Module.IsCohenMacaulayOfDimension R R n := by
    constructor
    · rw [Module.supportDim_self_eq_ringKrullDim, hdim]
    · exact
        IsRegularLocalRing.extDepthAtLeast_maximalIdeal_of_ringKrullDim R hdim
  have hlower :
      Module.supportDim R R ≤
        Module.supportDim R
            (R ⧸ (Ideal.ofList rs • (⊤ : Submodule R R))) + rs.length :=
    Module.supportDim_le_supportDim_quotient_ofList_add_length rs hmem
  have hsmul :
      Ideal.ofList rs • (⊤ : Submodule R R) = Ideal.ofList rs := by
    simpa using
      (Ideal.smul_top_eq_map (R := R) (S := R) (Ideal.ofList rs))
  have hsum :
      Module.supportDim R
          (R ⧸ (Ideal.ofList rs • (⊤ : Submodule R R))) + rs.length =
        (n : WithBot ℕ∞) := by
    apply le_antisymm
    · rw [hsmul, Module.supportDim_quotient_eq_ringKrullDim]
      calc
        ringKrullDim (R ⧸ Ideal.ofList rs) + rs.length ≤
            ((n - rs.length : ℕ) : WithBot ℕ∞) + rs.length :=
          add_le_add hquot le_rfl
        _ = (n : WithBot ℕ∞) := by
          norm_cast
    · rw [← hdim, ← Module.supportDim_self_eq_ringKrullDim]
      exact hlower
  have hquotExact :
      Module.supportDim R
          (R ⧸ (Ideal.ofList rs • (⊤ : Submodule R R))) =
        (e : WithBot ℕ∞) := by
    apply ENat.WithBot.add_natCast_cancel.mp
    calc
      Module.supportDim R
            (R ⧸ (Ideal.ofList rs • (⊤ : Submodule R R))) + rs.length =
          (n : WithBot ℕ∞) := hsum
      _ = (e : WithBot ℕ∞) + rs.length := by
        norm_cast
        exact headd.symm
  have hCM' : Module.IsCohenMacaulayOfDimension R R (e + rs.length) := by
    rw [headd]
    exact hCM
  exact hCM'.isRegular_of_supportDim_quotient_eq rs hmem hquotExact

end RingTheory.Sequence

end

end
