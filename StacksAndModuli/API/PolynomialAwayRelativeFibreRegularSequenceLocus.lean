module

public import StacksAndModuli.API.PolynomialAwayClosedFibreDimension
public import StacksAndModuli.API.PolynomialMatrixRelativeFibreExactLocus
public import StacksAndModuli.API.RegularLocalRingSequenceDimensionCriterion
public import StacksAndModuli.API.RelativeFibreClosedPointQuotientDimension
public import StacksAndModuli.API.RelativeFibreClosedSpecialization
public import StacksProject.CommutativeAlgebra.DimensionOfFibres.«lemma-dimension-fibres-bounded-open-upstairs»

/-!
# Relative regular-sequence loci in localized polynomial algebras

Let `S` be a principal localization of a polynomial algebra `A[xᵢ]` in finitely many
variables.  Relative-fibre regularity of a fixed finite sequence is open on its zero
locus.

Starting from a regular point, fixed-fibre openness supplies a closed specialization
where regularity persists.  At that closed fibre point, the regular-sequence dimension
formula and the known dimension of a polynomial fibre show that the quotient has the
expected finite relative dimension.  Upper semicontinuity of relative dimension then
gives one ambient principal neighbourhood.  At every point of that neighbourhood, a
closed specialization in the same fibre has the required quotient-dimension bound; the
regular-local Cohen--Macaulay criterion proves regularity there, and fixed-fibre openness
passes it back to the original point.

Main declarations:

* `isRelativeFibreRegularSequenceAt_away_of_quotient_dimension_le_sub_of_closedFibrePoint`
  in `Matrix.FiniteFreeComplex`;
* `MvPolynomial.hasOpenRelativeFibreRegularSequenceLociAfterAway`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u v

open Algebra TensorProduct

namespace Matrix.FiniteFreeComplex

/-- At a closed point of a localized polynomial residue fibre, the expected upper bound
on the relative dimension of the quotient implies relative-fibre regularity. -/
theorem
    isRelativeFibreRegularSequenceAt_away_of_quotient_dimension_le_sub_of_closedFibrePoint
    {A : Type u} {sigma : Type v} [CommRing A] [Finite sigma]
    (a : MvPolynomial sigma A) {d : ℕ}
    (f : Fin d → Localization.Away a)
    (q : PrimeSpectrum (Localization.Away a))
    (hmem : ∀ i, f i ∈ q.asIdeal)
    (hclosed :
      (PrimeSpectrum.relativeFibrePrime (R := A) q).asIdeal.IsMaximal)
    (hlength : d ≤ Nat.card sigma)
    (hquot :
      let rs := List.ofFn f
      let I := Ideal.ofList rs
      let hIq : I ≤ q.asIdeal := Ideal.span_le.mpr <|
        List.forall_mem_ofFn_iff.mpr hmem
      let qbar := PrimeSpectrum.quotientOfLE I q hIq
      Algebra.relativeKrullDimAt A (Localization.Away a ⧸ I) qbar ≤
        ((Nat.card sigma - d : ℕ) : WithBot ℕ∞)) :
    IsRelativeFibreRegularSequenceAt (R := A) q f := by
  let S := Localization.Away a
  let rs : List S := List.ofFn f
  let I : Ideal S := Ideal.ofList rs
  have hrs_mem : ∀ x ∈ rs, x ∈ q.asIdeal := by
    dsimp only [rs]
    exact List.forall_mem_ofFn_iff.mpr hmem
  have hIq : I ≤ q.asIdeal := Ideal.span_le.mpr hrs_mem
  let qbar : PrimeSpectrum (S ⧸ I) :=
    PrimeSpectrum.quotientOfLE I q hIq
  let p : PrimeSpectrum A := q.comap (algebraMap A S)
  let T := p.asIdeal.Fiber S
  let qF : PrimeSpectrum T :=
    PrimeSpectrum.relativeFibrePrime (R := A) q
  let rsF : List T :=
    rs.map (Algebra.TensorProduct.includeRight : S →ₐ[A] T)
  let L := Localization.AtPrime qF.asIdeal
  let commRingL : CommRing L := inferInstance
  letI : CommRing L := commRingL
  letI : CommSemiring L := commRingL.toCommSemiring
  letI : Semiring L := commRingL.toCommSemiring.toSemiring
  let rsL : List L := rsF.map (algebraMap T L)
  have hrsF_mem : ∀ x ∈ rsF, x ∈ qF.asIdeal := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    change s ∈ qF.asIdeal.comap
      (Algebra.TensorProduct.includeRight : S →ₐ[A] T).toRingHom
    rw [PrimeSpectrum.relativeFibrePrime_comap_includeRight (R := A) q]
    exact hrs_mem s hs
  have hrsL_mem : ∀ x ∈ rsL, x ∈ IsLocalRing.maximalIdeal L := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff L qF.asIdeal]
    exact hrsF_mem s hs
  have hbridge :
      Algebra.relativeKrullDimAt A (S ⧸ I) qbar =
        ringKrullDim (L ⧸ Ideal.ofList rsL) := by
    simpa only [S, rs, I, qbar, p, T, qF, rsF, L, rsL] using
      (relativeKrullDimAt_quotient_eq_ringKrullDim_localizedFibreQuotient_of_closedFibrePoint
        q rs hrs_mem hclosed)
  have hlocal :
      ringKrullDim (L ⧸ Ideal.ofList rsL) ≤
        ((Nat.card sigma - rsL.length : ℕ) : WithBot ℕ∞) := by
    have hquot' :
        Algebra.relativeKrullDimAt A (S ⧸ I) qbar ≤
          ((Nat.card sigma - d : ℕ) : WithBot ℕ∞) := by
      simpa only [S, rs, I, qbar] using hquot
    rw [hbridge] at hquot'
    simpa only [rsL, rsF, rs, List.length_map, List.length_ofFn] using hquot'
  letI : qF.asIdeal.IsMaximal := hclosed
  letI : IsRegularLocalRing L :=
    Ideal.Fiber.isRegularLocalRing_localizationAtPrime_mvPolynomial_away
      p.asIdeal a qF.asIdeal
  have hdimL : ringKrullDim L =
      (Nat.card sigma : WithBot ℕ∞) :=
    Ideal.Fiber.ringKrullDim_localizationAtPrime_mvPolynomial_away_eq_natCard
      p.asIdeal a qF.asIdeal
  have hregL : RingTheory.Sequence.IsRegular L rsL :=
    RingTheory.Sequence.isRegular_of_isRegularLocalRing_of_quotient_dimension_le_sub
      L (Nat.card sigma) hdimL rsL hrsL_mem
        (by simpa only [rsL, rsF, rs, List.length_map, List.length_ofFn] using hlength)
        hlocal
  rw [isRelativeFibreRegularSequenceAt_iff_isRegularAfterLocalizationAt]
  change RingTheory.Sequence.IsRegular L
    ((List.ofFn fun j ↦ Algebra.TensorProduct.includeRight (f j)).map
      (algebraMap T L))
  have hrsF_eq :
      rsF = List.ofFn fun j ↦ Algebra.TensorProduct.includeRight (f j) := by
    dsimp only [rsF, rs]
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext j
    rfl
  rw [← hrsF_eq]
  exact hregL

end Matrix.FiniteFreeComplex

namespace MvPolynomial

open Matrix.FiniteFreeComplex

/-- Relative-fibre regularity of every finite sequence is open on its zero locus after
principal localization of a polynomial algebra in finitely many variables. -/
theorem hasOpenRelativeFibreRegularSequenceLociAfterAway
    (A : Type u) (sigma : Type v) [CommRing A] [Finite sigma] :
    HasOpenRelativeFibreRegularSequenceLociAfterAway A sigma := by
  intro a d f
  let S := Localization.Away a
  let Z := PrimeSpectrum.zeroLocus (Set.range f)
  let Reg : Set Z :=
    {q | Matrix.FiniteFreeComplex.IsRelativeFibreRegularSequenceAt
      (R := A) q.1 f}
  change IsOpen Reg
  rw [isOpen_iff_forall_mem_open]
  intro q hregq
  have hmemq : ∀ i, f i ∈ q.1.asIdeal := by
    intro i
    exact q.2 (Set.mem_range_self i)
  obtain ⟨q₀, hqle, _hqcomap, hreg₀, hclosed₀⟩ :=
    exists_specialization_closedInFibre_isRelativeFibreRegularSequenceAt
      (R := A) q.1 f hmemq hregq
  have hmem₀ : ∀ i, f i ∈ q₀.asIdeal := by
    intro i
    exact hqle (hmemq i)
  let rs : List S := List.ofFn f
  let I : Ideal S := Ideal.ofList rs
  have hrs₀_mem : ∀ x ∈ rs, x ∈ q₀.asIdeal := by
    dsimp only [rs]
    exact List.forall_mem_ofFn_iff.mpr hmem₀
  have hIq₀ : I ≤ q₀.asIdeal := Ideal.span_le.mpr hrs₀_mem
  let qbar₀ : PrimeSpectrum (S ⧸ I) :=
    PrimeSpectrum.quotientOfLE I q₀ hIq₀
  have hdrop :
      Algebra.relativeKrullDimAt A (S ⧸ I) qbar₀ + d =
        Algebra.relativeKrullDimAt A S q₀ := by
    simpa only [S, rs, I, qbar₀] using
      (Algebra.relativeKrullDimAt_quotient_add_length_eq_of_regularSequenceAt_closedFibrePoint
        q₀ f hmem₀ hreg₀ hclosed₀)
  have hambient :
      Algebra.relativeKrullDimAt A S q₀ =
        (Nat.card sigma : WithBot ℕ∞) := by
    simpa only [S] using
      (MvPolynomial.relativeKrullDimAt_away_eq_natCard_of_closedFibrePoint
        a q₀ hclosed₀)
  have hsum :
      Algebra.relativeKrullDimAt A (S ⧸ I) qbar₀ + d =
        (Nat.card sigma : WithBot ℕ∞) := hdrop.trans hambient
  have hnotbot :
      Algebra.relativeKrullDimAt A (S ⧸ I) qbar₀ ≠ ⊥ := by
    intro hbot
    rw [hbot] at hsum
    simp at hsum
  have hlengthCast :
      (d : WithBot ℕ∞) ≤ (Nat.card sigma : WithBot ℕ∞) := by
    obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hnotbot
    calc
      (d : WithBot ℕ∞) = 0 + d := (zero_add _).symm
      _ ≤ (n : WithBot ℕ∞) + d := add_le_add (by simp) le_rfl
      _ = (Nat.card sigma : WithBot ℕ∞) := by rw [hn, hsum]
  have hlength : d ≤ Nat.card sigma := by
    exact ENat.natCast_le_natCast.mp <|
      WithBot.coe_le_coe.mp hlengthCast
  let e := Nat.card sigma - d
  have hquotientDimension :
      Algebra.relativeKrullDimAt A (S ⧸ I) qbar₀ =
        (e : WithBot ℕ∞) := by
    apply ENat.WithBot.add_natCast_cancel.mp
    calc
      Algebra.relativeKrullDimAt A (S ⧸ I) qbar₀ + d =
          (Nat.card sigma : WithBot ℕ∞) := hsum
      _ = (e : WithBot ℕ∞) + d := by
        norm_cast
        exact (Nat.sub_add_cancel hlength).symm
  obtain ⟨gbar, hgbar₀, hdimension⟩ :=
    Algebra.exists_notMem_forall_relativeKrullDimAt_le_of_eq_nat
      A (S ⧸ I) qbar₀ e hquotientDimension
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective gbar
  have hgq₀ : g ∉ q₀.asIdeal := by
    intro hgq₀
    apply hgbar₀
    rw [← hg]
    change g ∈ qbar₀.asIdeal.comap (Ideal.Quotient.mk I)
    have hcomap₀ :
        qbar₀.asIdeal.comap (Ideal.Quotient.mk I) = q₀.asIdeal := by
      dsimp only [qbar₀, PrimeSpectrum.quotientOfLE,
        PrimeSpectrum.asIdeal]
      exact Ideal.comap_map_mk (I := I) (J := q₀.asIdeal) hIq₀
    rw [hcomap₀]
    exact hgq₀
  have hgq : g ∉ q.1.asIdeal := fun hgq ↦ hgq₀ (hqle hgq)
  let W : Set Z :=
    Subtype.val ⁻¹' (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S))
  refine ⟨W, ?_, ?_, ?_⟩
  · intro q' hq'W
    change Matrix.FiniteFreeComplex.IsRelativeFibreRegularSequenceAt
      (R := A) q'.1 f
    have hgq' : g ∉ q'.1.asIdeal := hq'W
    obtain ⟨qM, hq'M, hqMcomap, hgqM, hclosedM⟩ :=
      PrimeSpectrum.exists_specialization_closedInFibre_avoiding
        (R := A) q'.1 hgq'
    have hmemq' : ∀ i, f i ∈ q'.1.asIdeal := by
      intro i
      exact q'.2 (Set.mem_range_self i)
    have hmemM : ∀ i, f i ∈ qM.asIdeal := by
      intro i
      exact hq'M (hmemq' i)
    have hrsM_mem : ∀ x ∈ rs, x ∈ qM.asIdeal := by
      dsimp only [rs]
      exact List.forall_mem_ofFn_iff.mpr hmemM
    have hIqM : I ≤ qM.asIdeal := Ideal.span_le.mpr hrsM_mem
    let qbarM : PrimeSpectrum (S ⧸ I) :=
      PrimeSpectrum.quotientOfLE I qM hIqM
    have hgbarM : gbar ∉ qbarM.asIdeal := by
      intro hgbarM
      apply hgqM
      rw [← hg] at hgbarM
      have hgM : g ∈
          qbarM.asIdeal.comap (Ideal.Quotient.mk I) := by
        exact hgbarM
      have hcomapM :
          qbarM.asIdeal.comap (Ideal.Quotient.mk I) = qM.asIdeal := by
        dsimp only [qbarM, PrimeSpectrum.quotientOfLE,
          PrimeSpectrum.asIdeal]
        exact Ideal.comap_map_mk (I := I) (J := qM.asIdeal) hIqM
      rw [hcomapM] at hgM
      exact hgM
    have hquotM :
        Algebra.relativeKrullDimAt A (S ⧸ I) qbarM ≤
          (e : WithBot ℕ∞) := hdimension qbarM hgbarM
    have hregM :
        Matrix.FiniteFreeComplex.IsRelativeFibreRegularSequenceAt
          (R := A) qM f := by
      apply
        isRelativeFibreRegularSequenceAt_away_of_quotient_dimension_le_sub_of_closedFibrePoint
        a f qM hmemM hclosedM hlength
      simpa only [S, rs, I, qbarM, e] using hquotM
    exact isRelativeFibreRegularSequenceAt_of_le_of_comap_eq
      (R := A) f hq'M hqMcomap hmemq' hregM
  · exact PrimeSpectrum.isOpen_basicOpen.preimage continuous_subtype_val
  · exact hgq

end MvPolynomial

end

end
