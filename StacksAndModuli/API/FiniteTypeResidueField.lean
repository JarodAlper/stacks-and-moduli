module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Topology.LocallyClosed

/-!
# Finite-type residue fields and locally closed points

A point `p` of `Spec R` whose residue field is a finite-type `R`-algebra is a locally
closed point of `Spec R`. The commutative-algebra heart of this is the following
consequence of the Artin–Tate style argument: if `A` is a domain whose fraction field is a
finite-type `A`-algebra, then a single nonzero `b ∈ A` inverts every nonzero prime — every
prime not containing `b` is zero. Localizing at that `b` cuts `{p}` out of `V(p)`.

Mathlib has the Nullstellensatz-adjacent pieces (`Algebra.FiniteType`, `IsFractionRing`)
but not this statement, and not the resulting topological corollary.

## Main definitions

* `denomAlg`: the subalgebra of `K` of elements admitting a denominator that is a power
  of a fixed `b`.

## Main results

* `exists_key`: for a domain `A` with `Frac A` of finite type over `A`, some `b ≠ 0` lies
  outside no nonzero prime — every prime avoiding `b` is `⊥`.
* `isLocallyClosed_singleton_of_finiteType`: a point of `Spec R` with finite-type residue
  field is locally closed.
-/

@[expose] public section

universe u

variable (A : Type u) [CommRing A] [IsDomain A] (K : Type u) [Field K] [Algebra A K]
  [IsFractionRing A K]

/-- The subalgebra of `K` of elements `z` with `z * b^n ∈ A` for some `n`. -/
def denomAlg (b : A) : Subalgebra A K where
  carrier := {z | ∃ (n : ℕ) (c : A), z * (algebraMap A K b) ^ n = algebraMap A K c}
  mul_mem' := by
    rintro z w ⟨n, c, hc⟩ ⟨m, d, hd⟩
    refine ⟨n + m, c * d, ?_⟩
    rw [map_mul, ← hc, ← hd, pow_add]
    ring
  add_mem' := by
    rintro z w ⟨n, c, hc⟩ ⟨m, d, hd⟩
    refine ⟨n + m, c * b ^ m + d * b ^ n, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hc, ← hd, pow_add]
    ring
  algebraMap_mem' r := ⟨0, r, by simp⟩

/-- Unfolding of membership in `denomAlg`: an element of it admits a power of `b` as a
denominator. -/
theorem exists_denom (b : A) (z : K) (hz : z ∈ denomAlg A K b) :
    ∃ (n : ℕ) (c : A), z * (algebraMap A K b) ^ n = algebraMap A K c := hz

/-- **The key finiteness statement.** If the fraction field `K` of a domain `A` is a
finite-type `A`-algebra, then some `b ≠ 0` of `A` lies outside no nonzero prime: every prime
not containing `b` is `⊥`. Clearing the denominators of a finite generating set of `K`
produces such a `b`. -/
theorem exists_key [Algebra.FiniteType A K] :
    ∃ b : A, b ≠ 0 ∧ ∀ q : Ideal A, q.IsPrime → b ∉ q → q = ⊥ := by
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A K).FG)
  -- choose numerator/denominator for each generator
  choose num den hden hnd using fun z : K => IsFractionRing.div_surjective (K := K) A z
  classical
  set b : A := ∏ z ∈ s, den (z : K) with hb
  have hbne : b ≠ 0 := by
    rw [hb]
    exact Finset.prod_ne_zero_iff.mpr fun z _ =>
      nonZeroDivisors.ne_zero (hden z)
  refine ⟨b, hbne, ?_⟩
  -- the key: denomAlg A K b = ⊤
  have htop : denomAlg A K b = ⊤ := by
    rw [eq_top_iff, ← hs]
    refine Algebra.adjoin_le ?_
    intro z hz
    refine ⟨1, num z * ∏ w ∈ s.erase z, den (w : K), ?_⟩
    have hdz : algebraMap A K (den z) ≠ 0 := by
      have := nonZeroDivisors.ne_zero (hden z)
      simpa using ((IsFractionRing.injective A K).ne_iff (x := den z) (y := 0)).mpr this
    have hzz : z * algebraMap A K (den z) = algebraMap A K (num z) := by
      have h0 := hnd z
      rw [div_eq_iff hdz] at h0
      exact h0.symm
    have : b = den z * ∏ w ∈ s.erase z, den (w : K) := by
      rw [hb, ← Finset.mul_prod_erase s _ hz]
    rw [this, pow_one, map_mul, map_mul, ← mul_assoc, hzz]
  intro q hq hbq
  ext a
  simp only [Ideal.mem_bot]
  constructor
  · intro haq
    by_contra hane
    have ha0 : algebraMap A K a ≠ 0 := by
      simpa using ((IsFractionRing.injective A K).ne_iff (x := a) (y := 0)).mpr hane
    have hmem : (algebraMap A K a)⁻¹ ∈ denomAlg A K b := by rw [htop]; trivial
    obtain ⟨n, c, hc⟩ := hmem
    have : (algebraMap A K b) ^ n = algebraMap A K (a * c) := by
      have h2 : algebraMap A K a * ((algebraMap A K a)⁻¹ * (algebraMap A K b) ^ n) =
          algebraMap A K a * algebraMap A K c := by rw [hc]
      rw [map_mul, ← h2, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
    rw [← map_pow] at this
    have hbn : b ^ n = a * c := IsFractionRing.injective A K this
    have : b ^ n ∈ q := hbn ▸ Ideal.mul_mem_right _ _ haq
    exact hbq (hq.mem_of_pow_mem n this)
  · rintro rfl; exact q.zero_mem



/-- Step (c)+(e): translation to the prime spectrum. -/
theorem isLocallyClosed_singleton_of_finiteType (R : Type u) [CommRing R] (p : Ideal R)
    [hp : p.IsPrime] [Algebra.FiniteType R p.ResidueField] :
    IsLocallyClosed ({(⟨p, hp⟩ : PrimeSpectrum R)} : Set (PrimeSpectrum R)) := by
  haveI : Algebra.FiniteType (R ⧸ p) p.ResidueField :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ p) p.ResidueField
  obtain ⟨b, hb0, hb⟩ := exists_key (R ⧸ p) p.ResidueField
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  have hb'p : b' ∉ p := by
    intro h; exact hb0 ((Ideal.Quotient.eq_zero_iff_mem).mpr h)
  refine ⟨(PrimeSpectrum.basicOpen b' : Set (PrimeSpectrum R)),
    PrimeSpectrum.zeroLocus (p : Set R), (PrimeSpectrum.basicOpen b').2,
    PrimeSpectrum.isClosed_zeroLocus _, ?_⟩
  ext q
  simp only [Set.mem_singleton_iff, Set.mem_inter_iff, PrimeSpectrum.mem_zeroLocus,
    SetLike.coe_subset_coe, PrimeSpectrum.mem_basicOpen]
  constructor
  · rintro rfl; exact ⟨hb'p, le_refl _⟩
  · rintro ⟨hbq, hpq⟩
    have hker : RingHom.ker (Ideal.Quotient.mk p) ≤ q.asIdeal := by
      rw [Ideal.mk_ker]; exact hpq
    haveI : (q.asIdeal.map (Ideal.Quotient.mk p)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
    have hcm : (q.asIdeal.map (Ideal.Quotient.mk p)).comap (Ideal.Quotient.mk p) = q.asIdeal := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective]
      exact sup_eq_left.mpr hker
    have hbnot : Ideal.Quotient.mk p b' ∉ q.asIdeal.map (Ideal.Quotient.mk p) := by
      intro h
      exact hbq (by rw [← hcm]; exact h)
    have := hb _ inferInstance hbnot
    have : q.asIdeal = p := by
      rw [← hcm, this, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact PrimeSpectrum.ext this

