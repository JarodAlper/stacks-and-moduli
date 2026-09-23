module

public import StacksAndModuli.API.IntegralExtensionKrullDimension
public import StacksAndModuli.API.PolynomialMaximalLocalizationDimension
public import StacksAndModuli.API.PrimeSpectrumBasicOpenNeighborhood
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.NoetherNormalization

/-!
# Dimension at closed points of affine schemes over a field

For an affine scheme of finite type over a field, pointwise topological dimension at a
closed point agrees with the Krull dimension of the corresponding local ring.  The proof
first establishes the equicodimensionality of a finite-type domain over a field using
Noether normalization and going down.  In the reducible case, a principal open is chosen
which removes exactly the irreducible components not passing through the given point.

Main declarations:

* `Ideal.ringKrullDim_eq_height_of_isMaximal_of_finiteType_over_field`;
* `Ideal.exists_minimalPrime_le_height_le_ringKrullDim_quotient`;
* `PrimeSpectrum.topologicalKrullDimAtPoint_eq_height_of_component_dimension_le`;
* `PrimeSpectrum.topologicalKrullDimAtPoint_eq_ringKrullDim_localizationAtPrime`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped BigOperators

universe u v

namespace Ideal

/-- Every maximal ideal of a finite-type domain over a field has height equal to the
global Krull dimension. -/
theorem ringKrullDim_eq_height_of_isMaximal_of_finiteType_over_field
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (m : Ideal A) [m.IsMaximal] :
    ringKrullDim A = (m.height : WithBot ℕ∞) := by
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨n, g, hg_injective, hg_integral⟩ :=
    exists_integral_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  letI : Algebra P A := g.toRingHom.toAlgebra
  letI : Algebra.IsIntegral P A := ⟨hg_integral⟩
  letI : FaithfulSMul P A :=
    (faithfulSMul_iff_algebraMap_injective P A).mpr hg_injective
  let p : Ideal P := m.under P
  letI : p.IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
  letI : Algebra.HasGoingDown P A := inferInstance
  let I : Ideal A := p.map (algebraMap P A)
  let mbar : Ideal (A ⧸ I) := m.map (Ideal.Quotient.mk I)
  have hm_min : m ∈ I.minimalPrimes := by
    simpa only [I, p] using Ideal.IsIntegral.mem_minimalPrimes_map_under m
  have hmbar_prime : mbar.IsPrime := by
    exact Ideal.isPrime_map_quotientMk_of_isPrime hm_min.le
  letI : mbar.IsPrime := hmbar_prime
  have hmbar_min : mbar ∈ minimalPrimes (A ⧸ I) := by
    refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
    intro J hJ hJm
    have hIJ : I ≤ J.comap (Ideal.Quotient.mk I) := by
      simpa only [Ideal.mk_ker] using
        (Ideal.ker_le_comap (K := J) (Ideal.Quotient.mk I))
    have hJm' : J.comap (Ideal.Quotient.mk I) ≤ m := by
      rw [← Ideal.comap_map_mk (I := I) (J := m) hm_min.le]
      exact Ideal.comap_mono hJm
    have hmJ : m ≤ J.comap (Ideal.Quotient.mk I) :=
      hm_min.2 ⟨hJ.1.comap (Ideal.Quotient.mk I), hIJ⟩ hJm'
    exact Ideal.map_le_iff_le_comap.mpr hmJ
  have hmbar_height : mbar.height = 0 :=
    Ideal.height_eq_zero_iff.mpr hmbar_min
  letI : m.LiesOver p := ⟨rfl⟩
  have hm_height : m.height = p.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p m]
    simpa only [I, mbar, hmbar_height, add_zero]
  have hp_height : p.height = (n : ℕ∞) := by
    simpa only [p, P, Nat.card_fin] using
      MvPolynomial.height_eq_natCard_of_isMaximal k (Fin n) p
  calc
    ringKrullDim A = ringKrullDim P :=
      Algebra.IsIntegral.ringKrullDim_eq_of_injective hg_injective
    _ = (n : WithBot ℕ∞) := by
      dsimp only [P]
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field, zero_add]
      simp
    _ = (p.height : WithBot ℕ∞) := by
      rw [hp_height]
      exact (ENat.WithBot.coe_eq_natCast n).symm
    _ = (m.height : WithBot ℕ∞) := by rw [hm_height]

/-- A prime in a Noetherian ring has a minimal-prime branch on which its height is
bounded by the dimension of the corresponding irreducible component. -/
theorem exists_minimalPrime_le_height_le_ringKrullDim_quotient
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (p : Ideal A) [p.IsPrime] :
    ∃ q ∈ minimalPrimes A, q ≤ p ∧
      (p.height : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) := by
  obtain ⟨l, hl_last, hl_length⟩ := p.exists_ltSeries_length_eq_height
  let q : Ideal A := l.head.asIdeal
  have hl_maximal : (l.length : ℕ∞) = Order.height l.last := by
    rw [← PrimeSpectrum.height_eq_orderHeight l.last, hl_last]
    exact hl_length
  have hq_height : q.height = 0 := by
    change l.head.asIdeal.height = 0
    rw [PrimeSpectrum.height_eq_orderHeight]
    simpa [RelSeries.head] using
      (Order.height_eq_index_of_length_eq_height_last hl_maximal
        (0 : Fin (l.length + 1)))
  have hq_min : q ∈ minimalPrimes A :=
    Ideal.height_eq_zero_iff.mp hq_height
  have hq_le (i : Fin (l.length + 1)) : q ≤ (l i).asIdeal := by
    exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr (l.head_le i)
  let lbar : LTSeries (PrimeSpectrum (A ⧸ q)) :=
    LTSeries.mk l.length
      (fun i ↦
        ⟨(l i).asIdeal.map (Ideal.Quotient.mk q),
          Ideal.isPrime_map_quotientMk_of_isPrime (hq_le i)⟩)
      (fun i j hij ↦ by
        change (l i).asIdeal.map (Ideal.Quotient.mk q) <
          (l j).asIdeal.map (Ideal.Quotient.mk q)
        refine lt_of_le_of_ne (Ideal.map_mono
          ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr (l.strictMono hij)).le) ?_
        intro heq
        have hcomap := congrArg (Ideal.comap (Ideal.Quotient.mk q)) heq
        have hij_eq : (l i).asIdeal = (l j).asIdeal := by
          simpa only [Ideal.comap_map_mk (I := q) (J := (l i).asIdeal) (hq_le i),
            Ideal.comap_map_mk (I := q) (J := (l j).asIdeal) (hq_le j)] using hcomap
        exact (ne_of_lt ((PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr
          (l.strictMono hij))) hij_eq)
  refine ⟨q, hq_min, ?_, ?_⟩
  · change l.head.asIdeal ≤ p
    exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr <| by
      simpa only [hl_last] using l.head_le_last
  · have hlength := Order.LTSeries.length_le_krullDim lbar
    calc
      (p.height : WithBot ℕ∞) = ((l.length : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hl_length.symm
      _ = (l.length : WithBot ℕ∞) := ENat.WithBot.coe_eq_natCast l.length
      _ ≤ ringKrullDim (A ⧸ q) := by
        simpa only [lbar, LTSeries.mk_length, ringKrullDim] using hlength

end Ideal

namespace PrimeSpectrum

/-- A componentwise dimension bound at a prime of a Noetherian affine scheme identifies
pointwise topological dimension with the height of that prime. -/
theorem topologicalKrullDimAtPoint_eq_height_of_component_dimension_le
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (x : PrimeSpectrum A)
    (hcomponent : ∀ q ∈ minimalPrimes A, q ≤ x.asIdeal →
      ringKrullDim (A ⧸ q) ≤ (x.asIdeal.height : WithBot ℕ∞)) :
    topologicalKrullDimAtPoint (PrimeSpectrum A) x =
      (x.asIdeal.height : WithBot ℕ∞) := by
  let bad : Set (Ideal A) :=
    {q | q ∈ minimalPrimes A ∧ ¬ q ≤ x.asIdeal}
  have hbad_finite : bad.Finite :=
    (minimalPrimes.finite_of_isNoetherianRing A).subset fun _ h ↦ h.1
  letI : Fintype bad := hbad_finite.fintype
  have hex : ∀ q : bad, ∃ a : A, a ∈ q.1 ∧ a ∉ x.asIdeal := by
    intro q
    simpa only [SetLike.not_le_iff_exists] using q.2.2
  choose a ha_mem ha_notMem using hex
  let f : A := ∏ q : bad, a q
  have hf_notMem : f ∉ x.asIdeal := by
    change (∏ q : bad, a q) ∉ x.asIdeal
    rw [Ideal.IsPrime.prod_mem_iff]
    simp only [Finset.mem_univ, true_and, not_exists]
    exact ha_notMem
  have hsurvives {q : Ideal A} (hq : q ∈ minimalPrimes A) (hfq : f ∉ q) :
      q ≤ x.asIdeal := by
    by_contra hqx
    let qbad : bad := ⟨q, hq, hqx⟩
    apply hfq
    change (∏ r : bad, a r) ∈ q
    exact Ideal.prod_mem q (Finset.mem_univ qbad) (ha_mem qbad)
  let L := Localization.Away f
  have hL : ringKrullDim L ≤ (x.asIdeal.height : WithBot ℕ∞) := by
    rw [ringKrullDim_le_iff_height_le]
    intro P hP
    letI : P.IsPrime := hP
    let p : Ideal A := P.under A
    have hp_data :=
      (IsLocalization.isPrime_iff_isPrime_disjoint (Submonoid.powers f) L P).mp hP
    letI : p.IsPrime := hp_data.1
    have hfp : f ∉ p :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mp hp_data.2
    obtain ⟨q, hq_min, hqp, hp_dim⟩ :=
      Ideal.exists_minimalPrime_le_height_le_ringKrullDim_quotient p
    have hfq : f ∉ q := fun hfq ↦ hfp (hqp hfq)
    have hqx : q ≤ x.asIdeal := hsurvives hq_min hfq
    calc
      (P.height : WithBot ℕ∞) = (p.height : WithBot ℕ∞) := by
        exact congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞))
          (IsLocalization.height_under (Submonoid.powers f) P).symm
      _ ≤ ringKrullDim (A ⧸ q) := hp_dim
      _ ≤ (x.asIdeal.height : WithBot ℕ∞) :=
        hcomponent q hq_min hqx
  apply le_antisymm
  · exact (topologicalKrullDimAtPoint_le (basicOpen f) hf_notMem).trans <| by
      rw [topologicalKrullDim_basicOpen_eq_ringKrullDim_away]
      exact hL
  · obtain ⟨g, hxg, hg⟩ :=
      exists_basicOpen_topologicalKrullDim_eq_atPoint x
    let G := Localization.Away g
    let M : Ideal G := x.asIdeal.map (algebraMap A G)
    have hg_notMem : g ∉ x.asIdeal := hxg
    have hdisjoint : Disjoint (Submonoid.powers g : Set A) x.asIdeal :=
      (Ideal.disjoint_powers_iff_notMem_of_isPrime g).mpr hg_notMem
    letI : M.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) G
        x.asIdeal inferInstance hdisjoint
    calc
      (x.asIdeal.height : WithBot ℕ∞) = (M.height : WithBot ℕ∞) := by
        exact congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞))
          (IsLocalization.height_map_of_disjoint (Submonoid.powers g)
            x.asIdeal hdisjoint).symm
      _ ≤ ringKrullDim G := Ideal.height_le_ringKrullDim_of_isPrime
      _ = topologicalKrullDim (basicOpen g) :=
        topologicalKrullDim_basicOpen_eq_ringKrullDim_away g |>.symm
      _ = topologicalKrullDimAtPoint (PrimeSpectrum A) x := hg

/-- At a closed point of an affine scheme of finite type over a field, pointwise
topological dimension equals the Krull dimension of the local ring. -/
theorem topologicalKrullDimAtPoint_eq_ringKrullDim_localizationAtPrime
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.FiniteType k A]
    (x : PrimeSpectrum A) [x.asIdeal.IsMaximal] :
    topologicalKrullDimAtPoint (PrimeSpectrum A) x =
      ringKrullDim (Localization.AtPrime x.asIdeal) := by
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal
    (Localization.AtPrime x.asIdeal)]
  apply topologicalKrullDimAtPoint_eq_height_of_component_dimension_le x
  intro q hq hqx
  letI : q.IsPrime := hq.isPrime
  let qmk : A →+* A ⧸ q := Ideal.Quotient.mk q
  let mbar : Ideal (A ⧸ q) := x.asIdeal.map qmk
  letI : mbar.IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le
      Ideal.Quotient.mk_surjective (by simpa only [qmk, Ideal.mk_ker] using hqx)
  have hmbar_height_le : mbar.height ≤ x.asIdeal.height := by
    have h := Order.height_le_height_apply_of_strictMono
      (PrimeSpectrum.comap qmk)
      (RingHom.strictMono_comap_of_surjective
        (f := qmk) Ideal.Quotient.mk_surjective)
      (⟨mbar, inferInstance⟩ : PrimeSpectrum (A ⧸ q))
    have hcomap : mbar.comap qmk = x.asIdeal := by
      exact Ideal.comap_map_mk (I := q) (J := x.asIdeal) hqx
    simpa only [← PrimeSpectrum.height_eq_orderHeight,
      PrimeSpectrum.comap_asIdeal, hcomap] using h
  calc
    ringKrullDim (A ⧸ q) = (mbar.height : WithBot ℕ∞) :=
      Ideal.ringKrullDim_eq_height_of_isMaximal_of_finiteType_over_field
        k (A ⧸ q) mbar
    _ ≤ (x.asIdeal.height : WithBot ℕ∞) :=
      WithBot.coe_le_coe.mpr hmbar_height_le

end PrimeSpectrum

end

end
