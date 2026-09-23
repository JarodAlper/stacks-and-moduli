module

public import StacksAndModuli.API.FiniteFreeComplexHomology
public import StacksAndModuli.API.FiniteFreeComplexTail
public import StacksAndModuli.API.PolynomialModelBaseChange
public import StacksProject.Algebra.RegularFiniteGlDim.ProjectiveDimension

/-!
# Projective dimension in bounded finite free complexes

For an exact finite free complex which vanishes above degree `N`, the cokernel of the
differential in degree `i + 1 ⟶ i` has projective dimension at most `N - i`.  The proof
deletes the bottom term and uses dimension shifting through the induced injection from the
next differential cokernel.

This file also records that exactness of a matrix finite free complex is preserved by a flat
change of coefficients.  The tensor-product exactness statement is transported to the
coefficientwise-mapped matrices through the canonical finite-free base-change equivalences.

Main declarations:

* `Matrix.FiniteFreeComplex.differentialCoker`;
* `Matrix.FiniteFreeComplex.hasProjectiveDimensionLE_differentialCoker`;
* `Matrix.FiniteFreeComplex.IsExactInPositiveDegreesUpTo.map_of_flat`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

namespace Matrix.FiniteFreeComplex

variable {R : Type u} [CommRing R]

/-- The concrete cokernel of the differential in degree `i + 1 ⟶ i`. -/
abbrev differentialCoker (C : FiniteFreeComplex R) (i : ℕ) : Type u :=
  (Fin (C.termRank i) → R) ⧸
    LinearMap.range (Matrix.toLin' (C.differential i))

instance differentialCoker_finite (C : FiniteFreeComplex R) (i : ℕ) :
    Module.Finite R (C.differentialCoker i) :=
  Module.Finite.of_surjective
    (LinearMap.range (Matrix.toLin' (C.differential i))).mkQ
    (Submodule.mkQ_surjective _)

/-- The cokernel of a differential in the tail is the next differential cokernel of the
original complex. -/
@[simp]
theorem tail_differentialCoker (C : FiniteFreeComplex R) (i : ℕ) :
    C.tail.differentialCoker i = C.differentialCoker (i + 1) :=
  rfl

/-- The differential in degree `i + 1 ⟶ i` descends to the cokernel of the next
differential. -/
def differentialCokerToTerm (C : FiniteFreeComplex R) (i : ℕ) :
    C.differentialCoker (i + 1) →ₗ[R] (Fin (C.termRank i) → R) :=
  (LinearMap.range (Matrix.toLin' (C.differential (i + 1)))).liftQ
    (Matrix.toLin' (C.differential i))
    (LinearMap.range_le_ker_iff.mpr (C.differential_comp i))

@[simp]
theorem differentialCokerToTerm_mk
    (C : FiniteFreeComplex R) (i : ℕ)
    (x : Fin (C.termRank (i + 1)) → R) :
    C.differentialCokerToTerm i (Submodule.Quotient.mk x) =
      Matrix.toLin' (C.differential i) x :=
  rfl

/-- Exactness at degree `i + 1` makes the map induced from the next differential cokernel
injective. -/
theorem differentialCokerToTerm_injective_of_exact
    {C : FiniteFreeComplex R} {i : ℕ}
    (h : Function.Exact
      (Matrix.toLin' (C.differential (i + 1)))
      (Matrix.toLin' (C.differential i))) :
    Function.Injective (C.differentialCokerToTerm i) := by
  exact LinearMap.injective_range_liftQ_of_exact h

/-- The induced map from the next differential cokernel and the quotient map onto the
current differential cokernel are exact. -/
theorem exact_differentialCokerToTerm_mkQ
    (C : FiniteFreeComplex R) (i : ℕ) :
    Function.Exact (C.differentialCokerToTerm i)
      (LinearMap.range (Matrix.toLin' (C.differential i))).mkQ := by
  rw [LinearMap.exact_iff, Submodule.ker_mkQ]
  exact (Submodule.range_liftQ
    (p := LinearMap.range (Matrix.toLin' (C.differential (i + 1))))
    (Matrix.toLin' (C.differential i)) _).symm

/-- In an exact finite free complex vanishing above `N`, the cokernel of the differential
at index `i ≤ N` has projective dimension at most `N - i`. -/
theorem hasProjectiveDimensionLE_differentialCoker
    (C : FiniteFreeComplex R) (N : ℕ)
    (hbounded : C.IsBoundedAbove N)
    (hexact : C.IsExactInPositiveDegreesUpTo N)
    {i : ℕ} (hi : i ≤ N) :
    Module.HasProjectiveDimensionLE R (N - i) (C.differentialCoker i) := by
  induction N generalizing C i with
  | zero =>
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      have hterm : C.termRank 1 = 0 := hbounded 1 (by omega)
      letI : Subsingleton (Fin (C.termRank 1) → R) := by
        rw [hterm]
        infer_instance
      have hrange :
          LinearMap.range (Matrix.toLin' (C.differential 0)) = ⊥ := by
        rw [LinearMap.range_eq_bot]
        apply LinearMap.ext
        intro x
        simpa only [map_zero, LinearMap.zero_apply] using
          congrArg (Matrix.toLin' (C.differential 0))
            (Subsingleton.elim x 0)
      have hprojective : Module.Projective R (C.differentialCoker 0) :=
        Module.Projective.of_equiv
          (Submodule.quotEquivOfEqBot _ hrange).symm
      exact (Module.hasProjectiveDimensionLE_zero_iff_projective R _).mpr
        hprojective
  | succ N ih =>
      cases i with
      | zero =>
          have htailPD :
              Module.HasProjectiveDimensionLE R N
                (C.differentialCoker 1) := by
            simpa only [tail_differentialCoker, Nat.sub_zero] using
              ih (C := C.tail) hbounded.tail hexact.tail (Nat.zero_le N)
          have hinjective : Function.Injective
              (C.differentialCokerToTerm 0) :=
            C.differentialCokerToTerm_injective_of_exact
              (hexact 0 (Nat.zero_lt_succ N))
          have hstep :=
            Module.hasProjectiveDimensionLE_codomain_of_projective R
              (LinearMap.range
                (Matrix.toLin' (C.differential 0))).mkQ
              (Submodule.mkQ_surjective _)
              (C.differentialCokerToTerm 0) hinjective
              (C.exact_differentialCokerToTerm_mkQ 0).linearMap_ker_eq.symm
              htailPD
          simpa only [Nat.sub_zero, Nat.succ_eq_add_one] using hstep
      | succ i =>
          have hi' : i ≤ N := Nat.succ_le_succ_iff.mp hi
          simpa only [tail_differentialCoker,
            Nat.succ_sub_succ_eq_sub] using
            ih (C := C.tail) hbounded.tail hexact.tail hi'

/-- Flat coefficient extension preserves exactness in every displayed positive degree. -/
theorem IsExactInPositiveDegreesUpTo.map_of_flat
    {S : Type v} [CommRing S] [Algebra R S] [Module.Flat R S]
    {C : FiniteFreeComplex R} {N : ℕ}
    (h : C.IsExactInPositiveDegreesUpTo N) :
    (C.map (algebraMap R S)).IsExactInPositiveDegreesUpTo N := by
  intro i hi
  let e₀ := TensorProduct.piScalarRight R S S (Fin (C.termRank i))
  let e₁ := TensorProduct.piScalarRight R S S (Fin (C.termRank (i + 1)))
  let e₂ := TensorProduct.piScalarRight R S S (Fin (C.termRank (i + 2)))
  have hbaseChange : Function.Exact
      ((Matrix.toLin' (C.differential (i + 1))).baseChange S)
      ((Matrix.toLin' (C.differential i)).baseChange S) := by
    rw [LinearMap.baseChange_eq_ltensor,
      LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_exact S (h i hi)
  change Function.Exact
    (Matrix.toLin'
      ((C.differential (i + 1)).map (algebraMap R S)))
    (Matrix.toLin' ((C.differential i).map (algebraMap R S)))
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (f₁₂ := (Matrix.toLin' (C.differential (i + 1))).baseChange S)
    (f₂₃ := (Matrix.toLin' (C.differential i)).baseChange S)
    (g₁₂ := Matrix.toLin'
      ((C.differential (i + 1)).map (algebraMap R S)))
    (g₂₃ := Matrix.toLin'
      ((C.differential i).map (algebraMap R S)))
    (e₁ := e₂) (e₂ := e₁) (e₃ := e₀)
    (Matrix.piScalarRight_toLin_map
      (A := S) (C.differential (i + 1))).symm
    (Matrix.piScalarRight_toLin_map
      (A := S) (C.differential i)).symm).mpr hbaseChange

end Matrix.FiniteFreeComplex

end

end
