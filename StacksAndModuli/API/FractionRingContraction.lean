module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import StacksAndModuli.API.BaseChangePi

/-!
# Contraction of subspaces of `K^n` to submodules of `R^n` over a fraction ring

Supporting API with no Stacks Project counterpart.

Let `R` be a commutative ring with fraction ring `K` (in applications, a valuation ring
with fraction field `K`) and `W ⊆ K^n` a `K`-subspace. The *contraction* of `W` is the
submodule `N = {v ∈ R^n | v ∈ W} ⊆ R^n`; this file characterizes it as the unique
submodule of `R^n` with torsion-free quotient whose `K`-span recovers `W`, and shows
that over a valuation ring the quotient `R^n/N` is free of rank `dim_K (K^n/W)`.

This is the module-theoretic heart of the valuative criterion of properness for the
Grassmannian (`exer:grassmannian-valuative-criterion` in *Stacks and Moduli*): a
`K`-point of `Gr(q, n)` extends uniquely to an `R`-point.

All lemmas are stated for an arbitrary submodule `N` satisfying the membership
characterization `v ∈ N ↔ algebraMap ∘ v ∈ W`, so they apply to any definitional
spelling of the contraction.

Main declarations:
- `Submodule.span_algebraMapPi_eq_of_mem_iff`: the `K`-span of the contraction is `W`;
- `Submodule.quotient_torsion_eq_bot_of_mem_iff`: the quotient by the contraction is
  torsion free;
- `Submodule.mem_iff_of_span_algebraMapPi_eq`: conversely, a submodule with torsion-free
  quotient whose span is `W` is the contraction (the uniqueness half of the valuative
  criterion);
- `Submodule.quotient_free_of_mem_iff`, `Submodule.quotient_finrank_of_mem_iff`,
  `Submodule.quotient_projective_rankAtStalk_of_mem_iff`: over a valuation ring, the
  quotient by the contraction is finite free of rank `dim_K (K^n/W)` (the existence half).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open TensorProduct

universe u v

namespace Submodule

variable {R : Type u} {K : Type v} [CommRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] {n : ℕ} {W : Submodule K (Fin n → K)}
  {N : Submodule R (Fin n → R)}

/-- If `N ⊆ R^n` is the contraction of a `K`-subspace `W ⊆ K^n` over the fraction ring
`K` of `R`, then the `K`-span of the componentwise image of `N` recovers `W`: every
vector of `W` is a common denominator times a vector of `N`. -/
theorem span_algebraMapPi_eq_of_mem_iff
    (hN : ∀ v : Fin n → R, v ∈ N ↔ (fun i ↦ algebraMap R K (v i)) ∈ W) :
    Submodule.span K
      ((fun (v : Fin n → R) i ↦ algebraMap R K (v i)) '' (N : Set (Fin n → R))) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    exact (hN v).mp hv
  · intro w hw
    obtain ⟨b, hb⟩ :=
      IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) w
    choose r hr using hb
    have hbw : (fun i ↦ algebraMap R K (r i)) = algebraMap R K (b : R) • w := by
      funext i
      rw [hr i, Pi.smul_apply, algebraMap_smul]
    have hmem : (fun i ↦ algebraMap R K (r i)) ∈ W := by
      rw [hbw]
      exact W.smul_mem _ hw
    have hu : IsUnit (algebraMap R K (b : R)) :=
      IsLocalization.map_units K b
    have hw' : w = (↑hu.unit⁻¹ : K) •
        ((fun i ↦ algebraMap R K (r i)) : Fin n → K) := by
      rw [hbw, smul_smul, IsUnit.val_inv_mul, one_smul]
    rw [hw']
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨r, (hN r).mpr hmem, rfl⟩)

/-- The quotient of `R^n` by the contraction of a `K`-subspace of `K^n` is torsion
free: the contraction is saturated. -/
theorem quotient_torsion_eq_bot_of_mem_iff
    (hN : ∀ v : Fin n → R, v ∈ N ↔ (fun i ↦ algebraMap R K (v i)) ∈ W) :
    Submodule.torsion R ((Fin n → R) ⧸ N) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨b, hb⟩, hbx⟩
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective N x
  have hbv : b • v ∈ N := by
    rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hbx
  have hW : (fun i ↦ algebraMap R K ((b • v) i)) ∈ W := (hN _).mp hbv
  have hu : IsUnit (algebraMap R K b) := IsLocalization.map_units K ⟨b, hb⟩
  have hv : (fun i ↦ algebraMap R K (v i)) ∈ W := by
    have hsmul : (fun i ↦ algebraMap R K ((b • v) i)) =
        algebraMap R K b • (fun i ↦ algebraMap R K (v i)) := by
      funext i
      simp
    rw [hsmul] at hW
    have := W.smul_mem (hu.unit⁻¹ : Kˣ).1 hW
    rwa [smul_smul, IsUnit.val_inv_mul, one_smul] at this
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  exact (hN v).mpr hv

/-- **Uniqueness of the valuative extension**: a submodule `N ⊆ R^n` with torsion-free
quotient whose `K`-span is `W` is necessarily the contraction of `W`. Together with
`Submodule.span_algebraMapPi_eq_of_mem_iff` this says that the contraction is the unique
saturated submodule of `R^n` localizing to `W`. -/
theorem mem_iff_of_span_algebraMapPi_eq
    (htf : Submodule.torsion R ((Fin n → R) ⧸ N) = ⊥)
    (hspan : Submodule.span K
      ((fun (v : Fin n → R) i ↦ algebraMap R K (v i)) '' (N : Set (Fin n → R))) = W)
    (v : Fin n → R) :
    v ∈ N ↔ (fun i ↦ algebraMap R K (v i)) ∈ W := by
  constructor
  · intro hv
    rw [← hspan]
    exact Submodule.subset_span ⟨v, hv, rfl⟩
  · intro hv
    rw [← hspan] at hv
    rw [Submodule.mem_span_set'] at hv
    obtain ⟨m, c, g, hsum⟩ := hv
    choose w hw hφw using fun j ↦ (g j).2
    obtain ⟨b, hb⟩ :=
      IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) c
    choose r hr using hb
    -- clearing denominators identifies `b • v` with an element of `N`
    have hrj : ∀ j, algebraMap R K (r j) = algebraMap R K (b : R) * c j := fun j ↦ by
      rw [hr j, Algebra.smul_def]
    have hbvN : (b : R) • v ∈ N := by
      have hzero : ((b : R) • v) = ∑ j, r j • w j := by
        funext i
        apply IsFractionRing.injective R K
        have h1 : algebraMap R K (((b : R) • v) i) =
            algebraMap R K (b : R) * algebraMap R K (v i) := by
          rw [Pi.smul_apply, smul_eq_mul, map_mul]
        have h2 : algebraMap R K ((∑ j, r j • w j) i) =
            ∑ j, algebraMap R K (r j) * algebraMap R K (w j i) := by
          rw [Finset.sum_apply, map_sum]
          congr 1
          funext j
          rw [Pi.smul_apply, smul_eq_mul, map_mul]
        have h3 : ∑ j, c j • ((g j : Fin n → K) i) = algebraMap R K (v i) := by
          have := congrFun hsum i
          rwa [Finset.sum_apply] at this
        have hgw : ∀ j, (g j : Fin n → K) i = algebraMap R K (w j i) := fun j ↦ by
          rw [← hφw j]
        rw [h1, h2, ← h3, Finset.mul_sum]
        congr 1
        funext j
        rw [hrj j, hgw j, smul_eq_mul]
        ring
      rw [hzero]
      exact Submodule.sum_mem N fun j _ ↦ Submodule.smul_mem N (r j) (hw j)
    -- torsion-freeness upgrades `b • v ∈ N` to `v ∈ N`
    have hmk : ((b : R) • (Submodule.Quotient.mk v) :
        (Fin n → R) ⧸ N) = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hbvN
    have htors : (Submodule.Quotient.mk v : (Fin n → R) ⧸ N) ∈
        Submodule.torsion R ((Fin n → R) ⧸ N) :=
      ⟨b, hmk⟩
    rw [htf, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at htors
    exact htors

variable [IsDomain R]

/-- Over a valuation ring, the quotient of `R^n` by the contraction of a `K`-subspace is
flat: it is torsion free, and over a Bezout domain torsion-free modules are flat. -/
theorem quotient_flat_of_mem_iff [ValuationRing R]
    (hN : ∀ v : Fin n → R, v ∈ N ↔ (fun i ↦ algebraMap R K (v i)) ∈ W) :
    Module.Flat R ((Fin n → R) ⧸ N) :=
  (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr
    (quotient_torsion_eq_bot_of_mem_iff hN)

/-- Over a valuation ring, the quotient of `R^n` by the contraction of a `K`-subspace is
finite free: it is finite and flat over a local ring. -/
theorem quotient_free_of_mem_iff [ValuationRing R]
    (hN : ∀ v : Fin n → R, v ∈ N ↔ (fun i ↦ algebraMap R K (v i)) ∈ W) :
    Module.Free R ((Fin n → R) ⧸ N) :=
  haveI : Module.Finite R ((Fin n → R) ⧸ N) :=
    Module.Finite.of_surjective N.mkQ (Submodule.mkQ_surjective N)
  haveI : Module.Flat R ((Fin n → R) ⧸ N) := quotient_flat_of_mem_iff hN
  Module.free_of_flat_of_isLocalRing

/-- Over a valuation ring, the quotient of `R^n` by the contraction of `W ⊆ K^n` has
rank `dim_K (K^n/W)`: base change along `R → K` carries it to `K^n/W`. -/
theorem quotient_finrank_of_mem_iff [ValuationRing R]
    (hN : ∀ v : Fin n → R, v ∈ N ↔ (fun i ↦ algebraMap R K (v i)) ∈ W) :
    Module.finrank R ((Fin n → R) ⧸ N) = Module.finrank K ((Fin n → K) ⧸ W) := by
  have : Module.Free R ((Fin n → R) ⧸ N) := quotient_free_of_mem_iff hN
  have : Module.Finite R ((Fin n → R) ⧸ N) :=
    Module.Finite.of_surjective N.mkQ (Submodule.mkQ_surjective N)
  -- base change the presentation `R^n → R^n/N` to `K`
  have hker : LinearMap.ker (LinearMap.baseChangePi K N.mkQ) = W := by
    rw [LinearMap.ker_baseChangePi_eq_span K (Submodule.mkQ_surjective N),
      Submodule.ker_mkQ]
    exact span_algebraMapPi_eq_of_mem_iff hN
  let e : ((Fin n → K) ⧸ W) ≃ₗ[K] K ⊗[R] ((Fin n → R) ⧸ N) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans
      ((LinearMap.baseChangePi K N.mkQ).quotKerEquivOfSurjective
        (LinearMap.baseChangePi_surjective K (Submodule.mkQ_surjective N)))
  rw [← Module.finrank_baseChange (R := K) (S := R)
    (M' := (Fin n → R) ⧸ N)]
  exact (e.finrank_eq).symm

/-- **Existence of the valuative extension**: over a valuation ring `R` with fraction
field `K`, the quotient of `R^n` by the contraction of a `K`-subspace `W ⊆ K^n` with
`dim_K (K^n/W) = q` is projective with constant stalk rank `q`. This is the data needed
for the contraction to define an `R`-point of the Grassmannian `Gr(q, n)`. -/
theorem quotient_projective_rankAtStalk_of_mem_iff [ValuationRing R] {q : ℕ}
    (hN : ∀ v : Fin n → R, v ∈ N ↔ (fun i ↦ algebraMap R K (v i)) ∈ W)
    (hq : Module.finrank K ((Fin n → K) ⧸ W) = q) :
    Module.Projective R ((Fin n → R) ⧸ N) ∧
      ∀ p : PrimeSpectrum R,
        Module.rankAtStalk ((Fin n → R) ⧸ N) p = q := by
  have : Module.Free R ((Fin n → R) ⧸ N) := quotient_free_of_mem_iff hN
  have : Module.Finite R ((Fin n → R) ⧸ N) :=
    Module.Finite.of_surjective N.mkQ (Submodule.mkQ_surjective N)
  refine ⟨Module.Projective.of_free, fun p ↦ ?_⟩
  have hrank := congrFun (Module.rankAtStalk_eq_finrank_of_free
    (R := R) (M := (Fin n → R) ⧸ N)) p
  rw [hrank]
  change Module.finrank R ((Fin n → R) ⧸ N) = q
  rw [quotient_finrank_of_mem_iff hN, hq]

end Submodule
