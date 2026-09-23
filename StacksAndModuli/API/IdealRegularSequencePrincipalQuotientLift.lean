module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Lifting regular sequences from a principal quotient

Suppose that `x` is regular on a commutative ring `R` and belongs to an ideal `I`.
If the image of `I` in `R / (x)` contains a regular sequence of length `d`, then `I`
contains a regular sequence of length `d + 1`: lift the quotient sequence termwise
and prepend `x`.

This is the regular-sequence induction step used after reducing an exact finite-free
complex modulo a common regular element.

Main declaration:

* `Ideal.exists_family_mem_and_isRegular_succ_of_isRegular_map_quotient`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- A regular sequence in the image of an ideal modulo a regular element lifts, after
prepending that element, to a regular sequence in the original ideal. -/
theorem exists_family_mem_and_isRegular_succ_of_isRegular_map_quotient
    (I : Ideal R) (x : R) (hxI : x ∈ I) (hx : IsRegular x)
    {d : ℕ} (g : Fin d → R ⧸ Ideal.span {x})
    (hgI : ∀ i, g i ∈ I.map (Ideal.Quotient.mk (Ideal.span {x})))
    (hreg : RingTheory.Sequence.IsRegular (R ⧸ Ideal.span {x})
      (List.ofFn g)) :
    ∃ f : Fin (d + 1) → R, (∀ i, f i ∈ I) ∧
      RingTheory.Sequence.IsRegular R (List.ofFn f) := by
  let hw (i : Fin d) :=
    (Ideal.mem_map_iff_of_surjective
      (Ideal.Quotient.mk (Ideal.span {x}))
      Ideal.Quotient.mk_surjective).mp (hgI i)
  let a : Fin d → R := fun i ↦ (hw i).choose
  have haI (i : Fin d) : a i ∈ I := (hw i).choose_spec.1
  have haq (i : Fin d) :
      Ideal.Quotient.mk (Ideal.span {x}) (a i) = g i :=
    (hw i).choose_spec.2
  let eR : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} :=
    QuotSMulTop.equivQuotTensor x R ≪≫ₗ
      TensorProduct.rid R (R ⧸ Ideal.span {x})
  let e : QuotSMulTop x R ≃ₗ[R ⧸ Ideal.span {x}]
      R ⧸ Ideal.span {x} :=
    eR.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have hmap :
      (List.ofFn a).map (Ideal.Quotient.mk (Ideal.span {x})) =
        List.ofFn g := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext haq)
  have hregQuot : RingTheory.Sequence.IsRegular (QuotSMulTop x R)
      ((List.ofFn a).map (Ideal.Quotient.mk (Ideal.span {x}))) := by
    apply (e.isRegular_congr _).mpr
    rw [hmap]
    exact hreg
  have hcons : RingTheory.Sequence.IsRegular R (x :: List.ofFn a) :=
    (RingTheory.Sequence.isRegular_cons_iff' R x (List.ofFn a)).mpr
      ⟨hx.isSMulRegular, hregQuot⟩
  refine ⟨Fin.cons x a, ?_, ?_⟩
  · intro i
    exact Fin.cases hxI haI i
  · simpa only [List.ofFn_cons] using hcons

end Ideal

end

end
