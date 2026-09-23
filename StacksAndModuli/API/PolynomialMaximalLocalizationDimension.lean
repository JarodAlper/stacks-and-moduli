module

public import StacksAndModuli.API.ModuleSupportDimensionSequence
public import StacksAndModuli.API.RegularLocalRingExtDepth
public import StacksAndModuli.API.RegularSequencePrimeSpecialization
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import StacksProject.CommutativeAlgebra.CohenMacaulayModules.«proposition-CM-regular-sequence»

/-!
# Dimension bounds after localization at polynomial maximal ideals

Localization does not increase Krull dimension, and this remains true after quotienting
by the image of an ideal.  For a polynomial ring in finitely many variables over a field,
every maximal ideal has height equal to the number of variables.  Consequently, a global
dimension bound for the quotient by a finite sequence gives the exact support-dimension
drop after localization at every maximal ideal containing that sequence.

This is the dimension-bookkeeping half of the maximal-ideal proof of regularity used for
polynomial fibres.  It avoids any catenary dimension-complement formula at arbitrary
primes: the exact ambient local dimension is needed only at maximal ideals.

Main declarations:

* `IsLocalization.ringKrullDim_le`;
* `IsLocalization.ringKrullDim_quotient_map_le`;
* `IsLocalization.AtPrime.supportDim_quotient_ofList_add_length_eq_height_of_local_le`;
* `IsLocalization.AtPrime.supportDim_quotient_ofList_add_length_eq_height_of_global_le`;
* `MvPolynomial.height_eq_natCard_of_isMaximal`;
* `MvPolynomial.supportDim_localizedQuotient_add_length_eq_natCard`.
* `MvPolynomial.isRegular_localizationAtPrime_of_quotient_dimension_le_sub`.
* `MvPolynomial.isRegular_localizationAtPrime_of_global_quotient_dimension_le_sub_of_isMaximal`.
* `MvPolynomial.isRegular_localizationAtPrime_of_global_quotient_dimension_le_sub`.
* `MvPolynomial.isRegular_localizationAtPrime_of_exists_maximal_quotient_dimension_le_sub`.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

universe u v

namespace IsLocalization

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Krull dimension does not increase under localization. -/
theorem ringKrullDim_le (M : Submonoid R) [IsLocalization M S] :
    ringKrullDim S ≤ ringKrullDim R := by
  change Order.krullDim (PrimeSpectrum S) ≤ Order.krullDim (PrimeSpectrum R)
  rw [Order.krullDim_eq_of_orderIso (primeSpectrumOrderIso M S)]
  exact Order.krullDim_le_of_strictMono (fun p ↦ p.1) fun {_ _} h ↦ h

/-- After localizing, the quotient by the image of an ideal has dimension at most the
dimension of the original quotient. -/
theorem ringKrullDim_quotient_map_le (M : Submonoid R) [IsLocalization M S]
    (I : Ideal R) :
    ringKrullDim (S ⧸ I.map (algebraMap R S)) ≤ ringKrullDim (R ⧸ I) := by
  exact IsLocalization.ringKrullDim_le
    (Algebra.algebraMapSubmonoid (R ⧸ I) M)

/-- List form of the quotient-localization dimension bound. -/
theorem ringKrullDim_quotient_ofList_map_le (M : Submonoid R) [IsLocalization M S]
    (rs : List R) :
    ringKrullDim (S ⧸ Ideal.ofList (rs.map (algebraMap R S))) ≤
      ringKrullDim (R ⧸ Ideal.ofList rs) := by
  rw [← Ideal.map_ofList]
  exact ringKrullDim_quotient_map_le M (Ideal.ofList rs)

namespace AtPrime

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Suppose a list lies in a maximal ideal.  If its quotient after localization has
dimension at most the height of the maximal ideal minus the length of the list, in
additive form, then the localized quotient has the exact maximal possible
support-dimension drop. -/
theorem supportDim_quotient_ofList_add_length_eq_height_of_local_le
    (m : Ideal R) [m.IsMaximal] (rs : List R)
    (hmem : ∀ x ∈ rs, x ∈ m)
    (hlocal :
      let L := Localization.AtPrime m
      let rsL := rs.map (algebraMap R L)
      ringKrullDim (L ⧸ Ideal.ofList rsL) + rsL.length ≤ m.height) :
    let L := Localization.AtPrime m
    let rsL := rs.map (algebraMap R L)
    Module.supportDim L
        (L ⧸ (Ideal.ofList rsL • (⊤ : Submodule L L))) + rsL.length =
      m.height := by
  dsimp only at hlocal ⊢
  let L := Localization.AtPrime m
  let rsL : List L := rs.map (algebraMap R L)
  have hmemL : ∀ x ∈ rsL, x ∈ IsLocalRing.maximalIdeal L := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff L m]
    exact hmem r hr
  have hlower :
      Module.supportDim L L ≤
        Module.supportDim L
            (L ⧸ (Ideal.ofList rsL • (⊤ : Submodule L L))) + rsL.length :=
    Module.supportDim_le_supportDim_quotient_ofList_add_length rsL hmemL
  have hsmul :
      Ideal.ofList rsL • (⊤ : Submodule L L) = Ideal.ofList rsL := by
    simpa using (Ideal.smul_top_eq_map (R := L) (S := L) (Ideal.ofList rsL))
  apply le_antisymm
  · rw [hsmul, Module.supportDim_quotient_eq_ringKrullDim]
    exact hlocal
  · rw [← IsLocalization.AtPrime.ringKrullDim_eq_height m L,
      ← Module.supportDim_self_eq_ringKrullDim]
    exact hlower

/-- Suppose a list lies in a maximal ideal.  If the dimension of its global quotient,
plus the length of the list, is at most the height of that maximal ideal, then after
localization the quotient has the exact maximal possible support-dimension drop. -/
theorem supportDim_quotient_ofList_add_length_eq_height_of_global_le
    (m : Ideal R) [m.IsMaximal] (rs : List R)
    (hmem : ∀ x ∈ rs, x ∈ m)
    (hglobal : ringKrullDim (R ⧸ Ideal.ofList rs) + rs.length ≤ m.height) :
    let L := Localization.AtPrime m
    let rsL := rs.map (algebraMap R L)
    Module.supportDim L
        (L ⧸ (Ideal.ofList rsL • (⊤ : Submodule L L))) + rsL.length =
      m.height := by
  dsimp only
  let L := Localization.AtPrime m
  let rsL : List L := rs.map (algebraMap R L)
  have hlocal :
      ringKrullDim (L ⧸ Ideal.ofList rsL) ≤
        ringKrullDim (R ⧸ Ideal.ofList rs) := by
    exact IsLocalization.ringKrullDim_quotient_ofList_map_le m.primeCompl rs
  apply supportDim_quotient_ofList_add_length_eq_height_of_local_le m rs hmem
  calc
    ringKrullDim (L ⧸ Ideal.ofList rsL) + rsL.length ≤
        ringKrullDim (R ⧸ Ideal.ofList rs) + rs.length := by
      simpa only [rsL, List.length_map] using add_le_add hlocal le_rfl
    _ ≤ m.height := hglobal

end AtPrime

end IsLocalization

namespace MvPolynomial

/-- Every maximal ideal of a polynomial ring in finitely many variables over a field has
height equal to the number of variables. -/
theorem height_eq_natCard_of_isMaximal
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (m : Ideal (MvPolynomial sigma K)) [hm : m.IsMaximal] :
    m.height = (Nat.card sigma : ℕ∞) := by
  refine Finite.induction_empty_option
    (P := fun tau ↦ ∀ (n : Ideal (MvPolynomial tau K)), n.IsMaximal →
      n.height = (Nat.card tau : ℕ∞)) ?_ ?_ ?_ sigma m hm
  · intro alpha beta e ih n hn
    let eR : MvPolynomial alpha K ≃+* MvPolynomial beta K :=
      (MvPolynomial.renameEquiv K e).toRingEquiv
    let n' : Ideal (MvPolynomial alpha K) := n.comap eR
    have hn' : n'.IsMaximal := by
      letI : n.IsMaximal := hn
      exact Ideal.comap_isMaximal_of_equiv eR
    calc
      n.height = n'.height := (eR.height_comap n).symm
      _ = (Nat.card alpha : ℕ∞) := ih n' hn'
      _ = (Nat.card beta : ℕ∞) := by rw [Nat.card_congr e]
  · intro n hn
    let e : MvPolynomial PEmpty K ≃+* K :=
      MvPolynomial.isEmptyRingEquiv K PEmpty
    letI : n.IsMaximal := hn
    letI : (n.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    calc
      n.height = (n.map e).height := (e.height_map n).symm
      _ = (⊥ : Ideal K).height := by rw [Ideal.eq_bot_of_prime (n.map e)]
      _ = 0 := Ideal.height_bot
      _ = (Nat.card PEmpty : ℕ∞) := by simp
  · intro alpha _ ih n hn
    let e : MvPolynomial (Option alpha) K ≃+*
        Polynomial (MvPolynomial alpha K) :=
      (MvPolynomial.optionEquivLeft K alpha).toRingEquiv
    let N : Ideal (Polynomial (MvPolynomial alpha K)) := n.map e
    let p : Ideal (MvPolynomial alpha K) := N.under (MvPolynomial alpha K)
    letI : n.IsMaximal := hn
    letI : N.IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hp : p.IsMaximal := by
      change (N.comap (algebraMap (MvPolynomial alpha K)
        (Polynomial (MvPolynomial alpha K)))).IsMaximal
      rw [Polynomial.algebraMap_eq]
      exact Polynomial.isMaximal_comap_C_of_isJacobsonRing N
    letI : p.IsMaximal := hp
    calc
      n.height = N.height := (e.height_map n).symm
      _ = p.height + 1 := Polynomial.height_eq_height_add_one p N
      _ = (Nat.card alpha : ℕ∞) + 1 := by rw [ih p inferInstance]
      _ = (Nat.card (Option alpha) : ℕ∞) := by simp

/-- The local ring at a maximal ideal of a finite-variable polynomial ring over a field
has dimension equal to the number of variables. -/
theorem ringKrullDim_localizationAtPrime_eq_natCard_of_isMaximal
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (m : Ideal (MvPolynomial sigma K)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = (Nat.card sigma : WithBot ℕ∞) := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m),
    height_eq_natCard_of_isMaximal K sigma m]
  exact ENat.WithBot.coe_eq_natCast _

/-- A global additive quotient-dimension bound becomes an exact support-dimension drop
after localizing at any maximal ideal containing the sequence. -/
theorem supportDim_localizedQuotient_add_length_eq_natCard
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (rs : List (MvPolynomial sigma K))
    (m : Ideal (MvPolynomial sigma K)) [m.IsMaximal]
    (hmem : ∀ x ∈ rs, x ∈ m)
    (hglobal :
      ringKrullDim (MvPolynomial sigma K ⧸ Ideal.ofList rs) + rs.length ≤
        (Nat.card sigma : WithBot ℕ∞)) :
    let L := Localization.AtPrime m
    let rsL := rs.map (algebraMap (MvPolynomial sigma K) L)
    Module.supportDim L
        (L ⧸ (Ideal.ofList rsL • (⊤ : Submodule L L))) + rsL.length =
      (Nat.card sigma : WithBot ℕ∞) := by
  simpa only [height_eq_natCard_of_isMaximal K sigma m,
    ENat.WithBot.coe_eq_natCast] using
    (IsLocalization.AtPrime.supportDim_quotient_ofList_add_length_eq_height_of_global_le
      m rs hmem (by
        simpa only [height_eq_natCard_of_isMaximal K sigma m,
          ENat.WithBot.coe_eq_natCast] using hglobal))

/-- Subtractive form of the polynomial maximal-local support-dimension equality. -/
theorem supportDim_localizedQuotient_add_length_eq_natCard_of_le_sub
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (rs : List (MvPolynomial sigma K))
    (m : Ideal (MvPolynomial sigma K)) [m.IsMaximal]
    (hmem : ∀ x ∈ rs, x ∈ m)
    (hlength : rs.length ≤ Nat.card sigma)
    (hglobal : ringKrullDim (MvPolynomial sigma K ⧸ Ideal.ofList rs) ≤
      ((Nat.card sigma - rs.length : ℕ) : WithBot ℕ∞)) :
    let L := Localization.AtPrime m
    let rsL := rs.map (algebraMap (MvPolynomial sigma K) L)
    Module.supportDim L
        (L ⧸ (Ideal.ofList rsL • (⊤ : Submodule L L))) + rsL.length =
      (Nat.card sigma : WithBot ℕ∞) := by
  apply supportDim_localizedQuotient_add_length_eq_natCard K sigma rs m hmem
  calc
    ringKrullDim (MvPolynomial sigma K ⧸ Ideal.ofList rs) + rs.length ≤
        ((Nat.card sigma - rs.length : ℕ) : WithBot ℕ∞) + rs.length :=
      add_le_add hglobal le_rfl
    _ = (Nat.card sigma : WithBot ℕ∞) := by
      norm_cast
      exact Nat.sub_add_cancel hlength

/-- Local subtractive form of the polynomial maximal-local support-dimension equality.
This is the form directly supplied at a closed fibre point by a relative-dimension bound. -/
theorem supportDim_localizedQuotient_add_length_eq_natCard_of_local_le_sub
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (rs : List (MvPolynomial sigma K))
    (m : Ideal (MvPolynomial sigma K)) [m.IsMaximal]
    (hmem : ∀ x ∈ rs, x ∈ m)
    (hlength : rs.length ≤ Nat.card sigma)
    (hlocal :
      let L := Localization.AtPrime m
      let rsL := rs.map (algebraMap (MvPolynomial sigma K) L)
      ringKrullDim (L ⧸ Ideal.ofList rsL) ≤
        ((Nat.card sigma - rs.length : ℕ) : WithBot ℕ∞)) :
    let L := Localization.AtPrime m
    let rsL := rs.map (algebraMap (MvPolynomial sigma K) L)
    Module.supportDim L
        (L ⧸ (Ideal.ofList rsL • (⊤ : Submodule L L))) + rsL.length =
      (Nat.card sigma : WithBot ℕ∞) := by
  dsimp only at hlocal ⊢
  simpa only [height_eq_natCard_of_isMaximal K sigma m,
    ENat.WithBot.coe_eq_natCast] using
    (IsLocalization.AtPrime.supportDim_quotient_ofList_add_length_eq_height_of_local_le
      m rs hmem (by
        calc
          ringKrullDim
                (Localization.AtPrime m ⧸
                  Ideal.ofList
                    (rs.map (algebraMap (MvPolynomial sigma K)
                      (Localization.AtPrime m)))) +
              (rs.map (algebraMap (MvPolynomial sigma K)
                (Localization.AtPrime m))).length ≤
              ((Nat.card sigma - rs.length : ℕ) : WithBot ℕ∞) + rs.length := by
            simpa only [List.length_map] using add_le_add hlocal le_rfl
          _ = (Nat.card sigma : WithBot ℕ∞) := by
            norm_cast
            exact Nat.sub_add_cancel hlength
          _ = (m.height : WithBot ℕ∞) := by
            rw [height_eq_natCard_of_isMaximal K sigma m]
            exact (ENat.WithBot.coe_eq_natCast _).symm))

/-- A sequence in a maximal ideal of a finite-variable polynomial ring over a field is
regular after localization if its localized quotient has dimension at most the number of
variables minus the sequence length.  This is the maximal-point Cohen--Macaulay criterion
used after applying relative-dimension upper semicontinuity. -/
theorem isRegular_localizationAtPrime_of_quotient_dimension_le_sub
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (rs : List (MvPolynomial sigma K))
    (m : Ideal (MvPolynomial sigma K)) [m.IsMaximal]
    (hmem : ∀ x ∈ rs, x ∈ m)
    (hlength : rs.length ≤ Nat.card sigma)
    (hlocal :
      let L := Localization.AtPrime m
      let rsL := rs.map (algebraMap (MvPolynomial sigma K) L)
      ringKrullDim (L ⧸ Ideal.ofList rsL) ≤
        ((Nat.card sigma - rs.length : ℕ) : WithBot ℕ∞)) :
    let L := Localization.AtPrime m
    let rsL := rs.map (algebraMap (MvPolynomial sigma K) L)
    RingTheory.Sequence.IsRegular L rsL := by
  dsimp only at hlocal ⊢
  let P := MvPolynomial sigma K
  let L := Localization.AtPrime m
  let rsL : List L := rs.map (algebraMap P L)
  let e := Nat.card sigma - rs.length
  letI : IsRegularRing P := MvPolynomial.isRegularRing_of_isRegularRing K
  letI : IsRegularLocalRing L := inferInstance
  have hdimL : ringKrullDim L = (Nat.card sigma : WithBot ℕ∞) :=
    ringKrullDim_localizationAtPrime_eq_natCard_of_isMaximal K sigma m
  have hCM : Module.IsCohenMacaulayOfDimension L L (Nat.card sigma) := by
    constructor
    · rw [Module.supportDim_self_eq_ringKrullDim, hdimL]
    · exact
        IsRegularLocalRing.extDepthAtLeast_maximalIdeal_of_ringKrullDim L hdimL
  have hmemL : ∀ x ∈ rsL, x ∈ IsLocalRing.maximalIdeal L := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff L m]
    exact hmem r hr
  have hsum :
      Module.supportDim L
          (L ⧸ (Ideal.ofList rsL • (⊤ : Submodule L L))) + rsL.length =
        (Nat.card sigma : WithBot ℕ∞) := by
    exact supportDim_localizedQuotient_add_length_eq_natCard_of_local_le_sub
      K sigma rs m hmem hlength hlocal
  have headd : e + rsL.length = Nat.card sigma := by
    dsimp only [e, rsL]
    rw [List.length_map]
    exact Nat.sub_add_cancel hlength
  have hCM' : Module.IsCohenMacaulayOfDimension L L (e + rsL.length) := by
    rw [headd]
    exact hCM
  have hquot :
      Module.supportDim L
          (L ⧸ (Ideal.ofList rsL • (⊤ : Submodule L L))) =
        (e : WithBot ℕ∞) := by
    apply ENat.WithBot.add_natCast_cancel.mp
    calc
      Module.supportDim L
            (L ⧸ (Ideal.ofList rsL • (⊤ : Submodule L L))) + rsL.length =
          (Nat.card sigma : WithBot ℕ∞) := hsum
      _ = (e : WithBot ℕ∞) + rsL.length := by
        norm_cast
        exact headd.symm
  exact hCM'.isRegular_of_supportDim_quotient_eq rsL hmemL hquot

/-- Global form of the polynomial maximal-point Cohen--Macaulay criterion: a dimension
bound for the affine quotient makes the sequence regular at every maximal ideal containing
it. -/
theorem isRegular_localizationAtPrime_of_global_quotient_dimension_le_sub_of_isMaximal
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (rs : List (MvPolynomial sigma K))
    (m : Ideal (MvPolynomial sigma K)) [m.IsMaximal]
    (hmem : ∀ x ∈ rs, x ∈ m)
    (hlength : rs.length ≤ Nat.card sigma)
    (hglobal : ringKrullDim (MvPolynomial sigma K ⧸ Ideal.ofList rs) ≤
      ((Nat.card sigma - rs.length : ℕ) : WithBot ℕ∞)) :
    let L := Localization.AtPrime m
    let rsL := rs.map (algebraMap (MvPolynomial sigma K) L)
    RingTheory.Sequence.IsRegular L rsL := by
  apply isRegular_localizationAtPrime_of_quotient_dimension_le_sub
    K sigma rs m hmem hlength
  exact (IsLocalization.ringKrullDim_quotient_ofList_map_le m.primeCompl rs).trans hglobal

/-- A global quotient-dimension bound makes the sequence regular after localization at
every prime containing it.  The proof chooses a maximal specialization of the prime,
uses the polynomial Cohen--Macaulay criterion there, and localizes once more. -/
theorem isRegular_localizationAtPrime_of_global_quotient_dimension_le_sub
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (rs : List (MvPolynomial sigma K))
    (q : Ideal (MvPolynomial sigma K)) [q.IsPrime]
    (hmem : ∀ x ∈ rs, x ∈ q)
    (hlength : rs.length ≤ Nat.card sigma)
    (hglobal : ringKrullDim (MvPolynomial sigma K ⧸ Ideal.ofList rs) ≤
      ((Nat.card sigma - rs.length : ℕ) : WithBot ℕ∞)) :
    let L := Localization.AtPrime q
    let rsL := rs.map (algebraMap (MvPolynomial sigma K) L)
    RingTheory.Sequence.IsRegular L rsL := by
  obtain ⟨m, hm, hqm, _⟩ :=
    Ideal.exists_isMaximal_over_notMem_of_isJacobsonRing q q.one_notMem
  letI : m.IsMaximal := hm
  have hmemm : ∀ x ∈ rs, x ∈ m := by
    intro x hx
    exact hqm (hmem x hx)
  have hregm :=
    isRegular_localizationAtPrime_of_global_quotient_dimension_le_sub_of_isMaximal
      K sigma rs m hmemm hlength hglobal
  exact RingTheory.Sequence.IsRegular.localizationAtPrime_of_le
    hqm rs hmem hregm

/-- To prove regularity at an arbitrary prime containing a sequence, it suffices to find
one maximal specialization where the corresponding localized quotient has the expected
dimension bound. -/
theorem isRegular_localizationAtPrime_of_exists_maximal_quotient_dimension_le_sub
    (K : Type u) [Field K] (sigma : Type v) [Finite sigma]
    (rs : List (MvPolynomial sigma K))
    (q : Ideal (MvPolynomial sigma K)) [q.IsPrime]
    (hmem : ∀ x ∈ rs, x ∈ q)
    (hlength : rs.length ≤ Nat.card sigma)
    (hexists : ∃ m : Ideal (MvPolynomial sigma K), ∃ hm : m.IsMaximal,
      letI : m.IsPrime := hm.isPrime
      q ≤ m ∧
        (let L := Localization.AtPrime m
         let rsL := rs.map (algebraMap (MvPolynomial sigma K) L)
         ringKrullDim (L ⧸ Ideal.ofList rsL) ≤
           ((Nat.card sigma - rs.length : ℕ) : WithBot ℕ∞))) :
    let L := Localization.AtPrime q
    let rsL := rs.map (algebraMap (MvPolynomial sigma K) L)
    RingTheory.Sequence.IsRegular L rsL := by
  obtain ⟨m, hm, hqm, hdim⟩ := hexists
  letI : m.IsMaximal := hm
  have hmemm : ∀ x ∈ rs, x ∈ m := by
    intro x hx
    exact hqm (hmem x hx)
  have hregm := isRegular_localizationAtPrime_of_quotient_dimension_le_sub
    K sigma rs m hmemm hlength hdim
  exact RingTheory.Sequence.IsRegular.localizationAtPrime_of_le
    hqm rs hmem hregm

end MvPolynomial

end

end
