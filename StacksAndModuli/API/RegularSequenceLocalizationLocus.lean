module

public import Mathlib.RingTheory.Regular.Flat
public import StacksAndModuli.API.NoetherianExactnessLocus

/-!
# Openness of weak regularity after localization

Let `M` be a finite module over a Noetherian ring `R` and let `rs` be a finite sequence in
`R`.  This file proves that the set of primes `p` where the image of `rs` is weakly regular
on `Rₚ ⊗[R] M` is open.

The proof is an induction on the sequence.  Regularity of the first term is the ordinary
localized exactness locus of multiplication by that term.  The remaining terms act on the
quotient by the first term, and `QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop`
identifies that quotient after base change with the base change of the original quotient.

Applied with `R` equal to one fibre ring, this supplies the fixed-fibre topological part of
the regular-sequence locus used in Stacks Project tag 00RA.  It does not assert the stronger
relative statement in which the contracted base prime, and hence the fibre ring, varies.

Main declarations:

* `RingTheory.Sequence.IsWeaklyRegularAfterLocalizationAt`;
* `RingTheory.Sequence.weaklyRegularAfterLocalizationLocus`;
* `RingTheory.Sequence.isOpen_weaklyRegularAfterLocalizationLocus`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open scoped Pointwise TensorProduct

universe u v

namespace RingTheory.Sequence

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Weak regularity of a sequence after scalar extension to the local ring at `p`. -/
def IsWeaklyRegularAfterLocalizationAt
    (M : Type v) [AddCommGroup M] [Module R M]
    (rs : List R) (p : PrimeSpectrum R) : Prop :=
  let Rp := Localization.AtPrime p.asIdeal
  IsWeaklyRegular (Rp ⊗[R] M) (rs.map (algebraMap R Rp))

/-- The locus where a sequence becomes weakly regular after localization. -/
def weaklyRegularAfterLocalizationLocus
    (M : Type v) [AddCommGroup M] [Module R M]
    (rs : List R) : Set (PrimeSpectrum R) :=
  {p | IsWeaklyRegularAfterLocalizationAt M rs p}

@[simp]
theorem mem_weaklyRegularAfterLocalizationLocus
    (rs : List R) (p : PrimeSpectrum R) :
    p ∈ weaklyRegularAfterLocalizationLocus M rs ↔
      IsWeaklyRegularAfterLocalizationAt M rs p :=
  Iff.rfl

/-- Scalar extension carries multiplication by `r` to multiplication by its image. -/
theorem baseChange_lsmul (r : R) (A : Type u) [CommRing A] [Algebra R A] :
    (LinearMap.lsmul R M r).baseChange A =
      LinearMap.lsmul A (A ⊗[R] M) (algebraMap R A r) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      simp [LinearMap.baseChange_tmul, LinearMap.lsmul_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Regularity of one scalar after localization is the ordinary localized exactness
locus of its multiplication map. -/
theorem isSMulRegular_baseChange_iff_mem_exactLocalizationLocus
    (r : R) (p : PrimeSpectrum R) :
    IsSMulRegular
        (Localization.AtPrime p.asIdeal ⊗[R] M)
        (algebraMap R (Localization.AtPrime p.asIdeal) r) ↔
      p ∈ LinearMap.exactLocalizationLocus
        (0 : M →ₗ[R] M) (LinearMap.lsmul R M r) := by
  rw [LinearMap.mem_exactLocalizationLocus]
  rw [LinearMap.exact_localizedMap_iff_baseChange]
  rw [LinearMap.baseChange_zero]
  rw [LinearMap.exact_zero_iff_injective]
  rw [baseChange_lsmul]
  rfl

/-- The localization locus for a nonempty sequence is the intersection of the first
multiplication-map exactness locus with the locus for the quotient and the tail. -/
theorem isWeaklyRegularAfterLocalizationAt_cons_iff
    (r : R) (rs : List R) (p : PrimeSpectrum R) :
    IsWeaklyRegularAfterLocalizationAt M (r :: rs) p ↔
      p ∈ LinearMap.exactLocalizationLocus
        (0 : M →ₗ[R] M) (LinearMap.lsmul R M r) ∧
      IsWeaklyRegularAfterLocalizationAt (QuotSMulTop r M) rs p := by
  let Rp := Localization.AtPrime p.asIdeal
  change IsWeaklyRegular (Rp ⊗[R] M)
      ((r :: rs).map (algebraMap R Rp)) ↔ _
  rw [List.map_cons, isWeaklyRegular_cons_iff]
  rw [isSMulRegular_baseChange_iff_mem_exactLocalizationLocus]
  apply and_congr_right'
  let e := QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop r M Rp
  exact e.isWeaklyRegular_congr (rs.map (algebraMap R Rp))

/-- Set-level recursion for the weak-regularity localization locus. -/
theorem weaklyRegularAfterLocalizationLocus_cons
    (r : R) (rs : List R) :
    weaklyRegularAfterLocalizationLocus M (r :: rs) =
      LinearMap.exactLocalizationLocus
          (0 : M →ₗ[R] M) (LinearMap.lsmul R M r) ∩
        weaklyRegularAfterLocalizationLocus (QuotSMulTop r M) rs := by
  ext p
  exact isWeaklyRegularAfterLocalizationAt_cons_iff r rs p

/-- For a finite module over a Noetherian ring, weak regularity of a fixed sequence after
localization is an open condition. -/
theorem isOpen_weaklyRegularAfterLocalizationLocus
    [IsNoetherianRing R] [Module.Finite R M] (rs : List R) :
    IsOpen (weaklyRegularAfterLocalizationLocus M rs) := by
  induction rs generalizing M with
  | nil =>
      have h : weaklyRegularAfterLocalizationLocus M ([] : List R) = Set.univ := by
        ext p
        simp [weaklyRegularAfterLocalizationLocus,
          IsWeaklyRegularAfterLocalizationAt]
      rw [h]
      exact isOpen_univ
  | cons r rs ih =>
      rw [weaklyRegularAfterLocalizationLocus_cons]
      haveI : Module.Finite R (QuotSMulTop r M) :=
        Module.Finite.of_surjective
          (Submodule.mkQ (r • (⊤ : Submodule R M)) : M →ₗ[R] QuotSMulTop r M)
          (Submodule.mkQ_surjective _)
      exact (LinearMap.isOpen_exactLocalizationLocus
        (0 : M →ₗ[R] M) (LinearMap.lsmul R M r) (by simp)).inter ih

end RingTheory.Sequence

end

end
