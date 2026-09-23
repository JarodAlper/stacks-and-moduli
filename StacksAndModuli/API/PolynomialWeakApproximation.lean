module

public import Mathlib.Algebra.Polynomial.PartialFractions
public import Mathlib.Algebra.Module.PID
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Weak approximation on the affine line

Let `K` be a fraction field of `k[X]`. A rational function is regular at a point
`p : Spec k[X]` when it admits a fraction presentation whose denominator is outside
the corresponding prime ideal. This file proves simultaneous weak approximation at
finitely many non-generic points: finitely many rational functions can be matched
modulo their respective local rings by one rational function having no other poles.

The proof is intrinsic to the affine line and works over an arbitrary field. Each
nonzero prime ideal has a prime generator `g`. A denominator is split into its maximal
power of `g` and a factor coprime to `g`; Bezout then isolates a rational function whose
only possible pole is at that prime. Summing these one-pole approximants gives the
simultaneous result.

## Main results

* `Polynomial.IsRegularAtPrime`: algebraic regularity of a fraction at a prime.
* `Polynomial.exists_sub_isRegularAtPrime_and_regular_away`: one-pole approximation.
* `Polynomial.exists_isRegularAtPrime_sub_and_regular_outside`: finite simultaneous
  weak approximation, including the generic point, with no extra poles.
-/

@[expose] public section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped Polynomial
open Set

noncomputable section

namespace Polynomial

variable {k K : Type*} [Field k] [Field K]
  [Algebra k[X] K] [IsFractionRing k[X] K]

/-- A fraction is regular at a prime when it has a denominator outside that prime. -/
def IsRegularAtPrime (p : PrimeSpectrum k[X]) (z : K) : Prop :=
  ∃ a b : k[X], b ∉ p.asIdeal ∧
    z = algebraMap k[X] K a / algebraMap k[X] K b

omit [IsFractionRing k[X] K] in
/-- A displayed fraction is regular wherever its denominator avoids the prime. -/
lemma isRegularAtPrime_of_fraction {p : PrimeSpectrum k[X]}
    {a b : k[X]} (hb : b ∉ p.asIdeal) :
    IsRegularAtPrime p
      (algebraMap k[X] K a / algebraMap k[X] K b) :=
  ⟨a, b, hb, rfl⟩

omit [IsFractionRing k[X] K] in
/-- Every polynomial is regular at every point of the affine line. -/
lemma isRegularAtPrime_algebraMap (p : PrimeSpectrum k[X]) (a : k[X]) :
    IsRegularAtPrime p (algebraMap k[X] K a) := by
  refine ⟨a, 1, ?_, by simp⟩
  exact fun h ↦ p.2.ne_top (p.asIdeal.eq_top_iff_one.mpr h)

/-- Every rational function is regular at the generic point of the affine line. -/
lemma isRegularAtPrime_bot (z : K) :
    IsRegularAtPrime (⊥ : PrimeSpectrum k[X]) z := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective k[X] z
  refine ⟨a, b, ?_, rfl⟩
  simpa using (mem_nonZeroDivisors_iff_ne_zero.mp hb)

omit [IsFractionRing k[X] K] in
/-- Regularity at a prime is preserved by negation. -/
lemma IsRegularAtPrime.neg {p : PrimeSpectrum k[X]} {z : K}
    (hz : IsRegularAtPrime p z) : IsRegularAtPrime p (-z) := by
  obtain ⟨a, b, hb, rfl⟩ := hz
  refine ⟨-a, b, hb, ?_⟩
  rw [map_neg, neg_div]

/-- Regularity at a prime is preserved by addition. -/
lemma IsRegularAtPrime.add {p : PrimeSpectrum k[X]} {x y : K}
    (hx : IsRegularAtPrime p x) (hy : IsRegularAtPrime p y) :
    IsRegularAtPrime p (x + y) := by
  obtain ⟨a, b, hb, rfl⟩ := hx
  obtain ⟨c, d, hd, rfl⟩ := hy
  refine ⟨a * d + c * b, b * d, ?_, ?_⟩
  · exact fun h ↦ (p.2.mem_or_mem h).elim hb hd
  · have hb0 : algebraMap k[X] K b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective k[X] K)).mpr
        (fun h ↦ hb (h ▸ p.asIdeal.zero_mem))
    have hd0 : algebraMap k[X] K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective k[X] K)).mpr
        (fun h ↦ hd (h ▸ p.asIdeal.zero_mem))
    simp only [map_add, map_mul]
    field_simp

/-- Regularity at a prime is preserved by subtraction. -/
lemma IsRegularAtPrime.sub {p : PrimeSpectrum k[X]} {x y : K}
    (hx : IsRegularAtPrime p x) (hy : IsRegularAtPrime p y) :
    IsRegularAtPrime p (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

/-- A finite sum of rational functions regular at a prime remains regular there. -/
lemma IsRegularAtPrime.sum {ι : Type*} {s : Finset ι}
    {p : PrimeSpectrum k[X]} {f : ι → K}
    (hf : ∀ i ∈ s, IsRegularAtPrime p (f i)) :
    IsRegularAtPrime p (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isRegularAtPrime_algebraMap (K := K) p 0
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- A canonical generator of the prime ideal corresponding to a point of the affine line. -/
def primeGenerator (p : PrimeSpectrum k[X]) : k[X] :=
  Submodule.IsPrincipal.generator p.asIdeal

/-- The ideal spanned by the canonical point generator is the point's prime ideal. -/
lemma span_primeGenerator (p : PrimeSpectrum k[X]) :
    Ideal.span {primeGenerator p} = p.asIdeal :=
  Ideal.span_singleton_generator p.asIdeal

/-- The canonical point generator belongs to the point's prime ideal. -/
lemma primeGenerator_mem (p : PrimeSpectrum k[X]) :
    primeGenerator p ∈ p.asIdeal := by
  rw [← span_primeGenerator p]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The generator of a nonzero prime ideal of `k[X]` is irreducible. -/
lemma primeGenerator_irreducible {p : PrimeSpectrum k[X]}
    (hp : p.asIdeal ≠ ⊥) : Irreducible (primeGenerator p) :=
  (Submodule.IsPrincipal.prime_generator_of_isPrime p.asIdeal hp).irreducible

/-- The generator of one non-generic point does not vanish at a different point. -/
lemma primeGenerator_not_mem_of_ne {p q : PrimeSpectrum k[X]}
    (hp : p.asIdeal ≠ ⊥) (hpq : p ≠ q) :
    primeGenerator p ∉ q.asIdeal := by
  intro h
  have hle : p.asIdeal ≤ q.asIdeal := by
    rw [← span_primeGenerator p, Ideal.span_le]
    simpa using h
  have hmax : p.asIdeal.IsMaximal := IsPrime.to_maximal_ideal hp
  exact hpq (PrimeSpectrum.ext (Ideal.IsMaximal.eq_of_le
    hmax q.2.ne_top hle))

/-- A rational function can be replaced, modulo functions regular at one non-generic
point, by a rational function whose only possible pole is that point. -/
lemma exists_sub_isRegularAtPrime_and_regular_away
    (p : PrimeSpectrum k[X]) (hp : p.asIdeal ≠ ⊥) (z : K) :
    ∃ w : K,
      IsRegularAtPrime p (z - w) ∧
        ∀ q : PrimeSpectrum k[X], q ≠ p → IsRegularAtPrime q w := by
  let g := primeGenerator p
  have hg : Irreducible g := primeGenerator_irreducible hp
  have hgprime : Prime g := hg.prime
  obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective k[X] z
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hfin : FiniteMultiplicity g b :=
    FiniteMultiplicity.of_not_isUnit hg.not_isUnit hb0
  obtain ⟨c, hbc, hgc⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  let n := multiplicity g b
  have hcop : IsCoprime (g ^ n) c :=
    (hgprime.coprime_iff_not_dvd.mpr hgc).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  let w : K := algebraMap k[X] K (a * v) /
    algebraMap k[X] K (g ^ n)
  refine ⟨w, ?_, ?_⟩
  · have hc_mem : c ∉ p.asIdeal := by
      rw [← span_primeGenerator p, Ideal.mem_span_singleton]
      exact hgc
    refine ⟨a * u, c, hc_mem, ?_⟩
    have hg0 : algebraMap k[X] K g ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective k[X] K)).mpr hg.ne_zero
    have hc0 : algebraMap k[X] K c ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective k[X] K)).mpr
        (fun hc0 ↦ hgc (hc0 ▸ dvd_zero g))
    rw [← hz, hbc]
    dsimp only [w, n]
    simp only [map_mul, map_pow]
    field_simp
    have hmap := congrArg (algebraMap k[X] K) huv
    simp only [map_add, map_mul, map_pow, map_one] at hmap
    calc
      algebraMap k[X] K a *
            (1 - algebraMap k[X] K c * algebraMap k[X] K v) =
          algebraMap k[X] K a *
            (1 - algebraMap k[X] K v * algebraMap k[X] K c) := by ring
      _ = algebraMap k[X] K a *
          (algebraMap k[X] K u * algebraMap k[X] K g ^ n) := by
        rw [(eq_sub_of_add_eq hmap).symm]
      _ = algebraMap k[X] K a *
          algebraMap k[X] K g ^ multiplicity g b *
            algebraMap k[X] K u := by
        dsimp only [n]
        ring
  · intro q hpq
    have hgq : g ∉ q.asIdeal := primeGenerator_not_mem_of_ne hp hpq.symm
    change IsRegularAtPrime q
      (algebraMap k[X] K (a * v) / algebraMap k[X] K (g ^ n))
    refine isRegularAtPrime_of_fraction (K := K) ?_
    intro hpow
    exact hgq (q.2.mem_of_pow_mem n hpow)

/-- Weak approximation on the affine line: finitely many prescribed rational
functions can be matched modulo the corresponding local rings by one rational
function, with no poles away from the prescribed points. -/
theorem exists_isRegularAtPrime_sub_and_regular_outside_of_nonzero
    (s : Finset (PrimeSpectrum k[X]))
    (hs : ∀ p ∈ s, p.asIdeal ≠ ⊥)
    (z : (p : s) → K) :
    ∃ r : K,
      (∀ p : s, IsRegularAtPrime p.1 (z p - r)) ∧
        ∀ q : PrimeSpectrum k[X], q ∉ s → IsRegularAtPrime q r := by
  classical
  choose w hw haway using fun p : s ↦
    exists_sub_isRegularAtPrime_and_regular_away
      p.1 (hs p.1 p.2) (z p)
  refine ⟨∑ p : s, w p, ?_, ?_⟩
  · intro p
    have hrest : IsRegularAtPrime p.1
        (∑ q ∈ Finset.univ.erase p, w q) := by
      apply IsRegularAtPrime.sum
      intro q hq
      exact haway q p.1 (by
        intro hqp
        exact (Finset.mem_erase.mp hq).1 (Subtype.ext hqp.symm))
    have hsum : (∑ q : s, w q) =
        (∑ q ∈ Finset.univ.erase p, w q) + w p := by
      exact (Finset.sum_erase_add Finset.univ w
        (Finset.mem_univ p)).symm
    have h := (hw p).sub hrest
    rw [hsum]
    convert h using 1
    ring
  · intro q hq
    apply IsRegularAtPrime.sum
    intro p _
    exact haway p q (fun h ↦ hq (h ▸ p.2))

/-- Weak approximation on the affine line, allowing the generic point among the
prescribed points. Since every rational function is regular at the generic point,
its prescription imposes no condition. -/
theorem exists_isRegularAtPrime_sub_and_regular_outside
    (s : Finset (PrimeSpectrum k[X])) (z : (p : s) → K) :
    ∃ r : K,
      (∀ p : s, IsRegularAtPrime p.1 (z p - r)) ∧
        ∀ q : PrimeSpectrum k[X], q ∉ s → IsRegularAtPrime q r := by
  classical
  let t := s.filter fun p ↦ p.asIdeal ≠ ⊥
  let z' : (p : t) → K := fun p ↦
    z ⟨p.1, (Finset.mem_filter.mp p.2).1⟩
  have ht : ∀ p ∈ t, p.asIdeal ≠ ⊥ := fun p hp ↦
    (Finset.mem_filter.mp hp).2
  obtain ⟨r, hmatch, haway⟩ :=
    exists_isRegularAtPrime_sub_and_regular_outside_of_nonzero t ht z'
  refine ⟨r, ?_, ?_⟩
  · intro p
    by_cases hp : p.1.asIdeal = ⊥
    · have hpbot : p.1 = (⊥ : PrimeSpectrum k[X]) :=
        PrimeSpectrum.ext hp
      simpa [hpbot] using isRegularAtPrime_bot (k := k) (K := K) (z p - r)
    · let pt : t := ⟨p.1, Finset.mem_filter.mpr ⟨p.2, hp⟩⟩
      simpa [pt, z'] using hmatch pt
  · intro q hq
    exact haway q fun hqt ↦ hq (Finset.mem_filter.mp hqt).1

end Polynomial
