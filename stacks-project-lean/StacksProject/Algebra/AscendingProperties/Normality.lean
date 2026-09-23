module

public import StacksProject.Algebra.NormalRings.«definition-ring-normal»
public import StacksProject.Algebra.RegularFiniteGlDim.ProjectiveDimension
public import StacksProject.Algebra.SmoothOverField.«lemma-separable-smooth»
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Regular.Flat

/-!
# Normality and flat local homomorphisms

This file supplies the commutative-algebra API used by Stacks Project tag **0C22**.  Mathlib
does not yet contain Serre's criterion or depth additivity, so the eventual normality ascent
argument is phrased in terms of two-element regular sequences.  The regular-local ascent lemma
below is Stacks Project tag **031E**.
-/

@[expose] public section

universe u

open IsLocalRing
open scoped Pointwise

/-- A normal ring is reduced. -/
lemma IsNormalRing.isReduced {R : Type u} [CommRing R] [IsNormalRing R] : IsReduced R := by
  apply IsReduced.mk
  intro x hx
  apply eq_zero_of_localization
  intro p hp
  letI : p.IsPrime := hp.isPrime
  letI : IsDomain (Localization.AtPrime p) :=
    IsNormalRing.isDomain_localization p
  exact (hx.map (algebraMap R (Localization.AtPrime p))).eq_zero

/-- A local normal ring is a domain. -/
lemma IsNormalRing.isDomain_of_isLocalRing {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNormalRing R] : IsDomain R := by
  let e : R ≃ₐ[R] Localization.AtPrime (maximalIdeal R) :=
    IsLocalization.atUnits R (maximalIdeal R).primeCompl
      (fun x ↦ by simpa using! fun a ↦ a)
  haveI : IsDomain (Localization.AtPrime (maximalIdeal R)) :=
    IsNormalRing.isDomain_localization (maximalIdeal R)
  exact e.injective.isDomain

/-- A local normal ring is integrally closed in its fraction field. -/
lemma IsNormalRing.isIntegrallyClosed_of_isLocalRing {R : Type u} [CommRing R]
    [IsLocalRing R] [IsNormalRing R] : IsIntegrallyClosed R := by
  let e : R ≃ₐ[R] Localization.AtPrime (maximalIdeal R) :=
    IsLocalization.atUnits R (maximalIdeal R).primeCompl
      (fun x ↦ by simpa using! fun a ↦ a)
  haveI : IsIntegrallyClosed (Localization.AtPrime (maximalIdeal R)) :=
    IsNormalRing.isIntegrallyClosed_localization (maximalIdeal R)
  exact IsIntegrallyClosed.of_equiv e.toRingEquiv.symm

/-- A Noetherian integrally closed local domain of dimension at most one is regular. -/
lemma IsIntegrallyClosed.isRegularLocalRing_of_ringKrullDim_le_one
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    [IsIntegrallyClosed R]
    (hR : ringKrullDim R ≤ 1) : IsRegularLocalRing R := by
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hR
  have hcond : IsIntegrallyClosed R ∧
      ∀ p : Ideal R, p ≠ ⊥ → p.IsPrime → p = maximalIdeal R := by
    refine ⟨inferInstance, fun p hp hprime ↦ ?_⟩
    exact eq_maximalIdeal
      ((Ring.krullDimLE_one_iff_of_isPrime_bot.mp inferInstance) p hp hprime)
  have hpid : IsPrincipalIdealRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 3 0).mp hcond
  letI : IsPrincipalIdealRing R := hpid
  infer_instance

/-- A Noetherian normal local domain of dimension at most one is regular. -/
lemma IsNormalRing.isRegularLocalRing_of_ringKrullDim_le_one
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsNormalRing R]
    (hR : ringKrullDim R ≤ 1) : IsRegularLocalRing R := by
  letI : IsDomain R := IsNormalRing.isDomain_of_isLocalRing
  letI : IsIntegrallyClosed R := IsNormalRing.isIntegrallyClosed_of_isLocalRing
  exact IsIntegrallyClosed.isRegularLocalRing_of_ringKrullDim_le_one hR

/-- A regular Noetherian local ring of dimension at most one is integrally closed. -/
lemma IsRegularLocalRing.isIntegrallyClosed_of_ringKrullDim_le_one
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsRegularLocalRing R] (hR : ringKrullDim R ≤ 1) : IsIntegrallyClosed R := by
  letI : IsDomain R := IsRegularLocalRing.isDomain
  have hcot := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
  have hfin : Module.finrank (ResidueField R) (CotangentSpace R) ≤ 1 := by
    have hfin' : (Module.finrank (ResidueField R) (CotangentSpace R) :
        WithBot ℕ∞) ≤ 1 := by
      rw [hcot]
      exact hR
    exact_mod_cast hfin'
  have hpid : IsPrincipalIdealRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 5 0).mp hfin
  letI : IsPrincipalIdealRing R := hpid
  infer_instance

/-- Let `R → S` be a flat local homomorphism, with `S` Noetherian.  If `R` and the closed
fiber are regular local rings, then `S` is regular.  This is Stacks Project tag **031E**. -/
@[stacks 031E]
theorem IsRegularLocalRing.of_flat_of_isRegularLocalRing_quotient
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing S]
    [IsNoetherianRing S] [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    [IsRegularLocalRing R]
    [IsRegularLocalRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))] :
    IsRegularLocalRing S := by
  classical
  set I : Ideal S := Ideal.map (algebraMap R S) (maximalIdeal R)
  have hsurj : Function.Surjective (Ideal.Quotient.mk I) :=
    Ideal.Quotient.mk_surjective
  have hmax : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal S) =
      maximalIdeal (S ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) hsurj
  have hheight : (maximalIdeal S).height =
      (maximalIdeal R).height + (maximalIdeal (S ⧸ I)).height := by
    rw [← hmax]
    exact Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (maximalIdeal R) (maximalIdeal S)
  obtain ⟨s, hs_span, hs_card⟩ :=
    IsRegularLocalRing.maximalIdeal_generated_by_dim (R := R)
  obtain ⟨t, ht_span, ht_card⟩ :=
    IsRegularLocalRing.maximalIdeal_generated_by_dim (R := S ⧸ I)
  have hs_height : (maximalIdeal R).height = (s.card : ℕ∞) := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [← hs_card] at h
    exact_mod_cast h
  have ht_height : (maximalIdeal (S ⧸ I)).height = (t.card : ℕ∞) := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := S ⧸ I)
    rw [← ht_card] at h
    exact_mod_cast h
  choose lift hlift using (Ideal.Quotient.mk_surjective (I := I))
  set t' : Finset S := t.image lift with ht'_def
  have ht'_card : t'.card = t.card :=
    Finset.card_image_of_injective t (Function.LeftInverse.injective hlift)
  have ht'_image : t'.image (Ideal.Quotient.mk I) = t := by
    rw [ht'_def, Finset.image_image]
    calc
      t.image ((Ideal.Quotient.mk I) ∘ lift) = t.image id :=
        Finset.image_congr (fun y _ ↦ hlift y)
      _ = t := Finset.image_id
  set w : Finset S := s.image (algebraMap R S) ∪ t' with hw_def
  have hw_span : Ideal.span (w : Set S) = maximalIdeal S := by
    rw [hw_def, Finset.coe_union, Ideal.span_union]
    have e1 : Ideal.span (↑(s.image (algebraMap R S)) : Set S) = I := by
      rw [Finset.coe_image, ← Ideal.map_span, hs_span]
    have e2 : Ideal.map (Ideal.Quotient.mk I) (Ideal.span (t' : Set S)) =
        maximalIdeal (S ⧸ I) := by
      rw [Ideal.map_span, ← Finset.coe_image, ht'_image, ht_span]
    have e3 : (maximalIdeal (S ⧸ I)).comap (Ideal.Quotient.mk I) = maximalIdeal S := by
      refine le_antisymm
        (le_maximalIdeal (Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top)) ?_
      rw [← hmax]
      exact Ideal.le_comap_map
    rw [e1, ← e3, ← e2, Ideal.comap_map_of_surjective _ hsurj,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_comm _ _
  have hle_card : (maximalIdeal S).height ≤ (w.card : ℕ∞) := by
    refine Ideal.height_le_card_of_mem_minimalPrimes_span_finset ?_
    rw [hw_span]
    exact ⟨⟨inferInstance, le_rfl⟩, fun _ hy _ ↦ hy.2⟩
  have hcard_le : w.card ≤ s.card + t.card :=
    (Finset.card_union_le _ _).trans
      (add_le_add Finset.card_image_le ht'_card.le)
  have hheight_eq : (maximalIdeal S).height =
      ((s.card + t.card : ℕ) : ℕ∞) := by
    rw [hheight, hs_height, ht_height]
    push_cast
    rfl
  have hcard_eq : w.card = s.card + t.card := by
    have h1 : ((s.card + t.card : ℕ) : ℕ∞) ≤ (w.card : ℕ∞) :=
      hheight_eq ▸ hle_card
    exact le_antisymm hcard_le (by exact_mod_cast h1)
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hw_le : (maximalIdeal S).spanFinrank ≤ w.card := by
    rw [← hw_span]
    have h := Submodule.spanFinrank_span_le_ncard_of_finite
      (R := S) w.finite_toSet
    rwa [Set.ncard_coe_finset] at h
  have hdim : (w.card : WithBot ℕ∞) = ringKrullDim S := by
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hheight_eq, hcard_eq]
    push_cast
    rfl
  have : ((maximalIdeal S).spanFinrank : WithBot ℕ∞) ≤ ringKrullDim S := by
    rw [← hdim]
    exact_mod_cast hw_le
  exact_mod_cast this

/-- A flat map remains flat after localizing at a prime of the target and its inverse
image in the source. -/
lemma Module.Flat.atPrime
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S)) :
    letI : q.LiesOver p := ⟨hpq⟩
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := by
  rw [← RingHom.Flat]
  exact RingHom.Flat.localRingHom
    (RingHom.flat_algebraMap_iff.mpr inferInstance) q p hpq

/-- A prime of `S` over `p` determines a prime of the fiber whose localization is the
closed fiber of the corresponding local homomorphism. -/
lemma Ideal.Fiber.exists_localizationRingEquivQuotient
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S)) :
    ∃ qf : Ideal (p.Fiber S), ∃ _ : qf.IsPrime,
      Nonempty (Localization.AtPrime qf ≃+*
        Localization.AtPrime q ⧸
          p.map (algebraMap R (Localization.AtPrime q))) := by
  obtain ⟨qf, hqf, hq⟩ : ∃ qf : Ideal (p.Fiber S), qf.IsPrime ∧
      qf.comap Algebra.TensorProduct.includeRight = q := by
    let qs : PrimeSpectrum S := ⟨q, inferInstance⟩
    let ps : PrimeSpectrum R := ⟨p, inferInstance⟩
    have hqs : PrimeSpectrum.comap (algebraMap R S) qs = ps := by
      apply PrimeSpectrum.ext
      exact hpq.symm
    let qf : PrimeSpectrum (p.Fiber S) :=
      PrimeSpectrum.preimageEquivFiber R S ps ⟨qs, hqs⟩
    refine ⟨qf.asIdeal, qf.isPrime, ?_⟩
    exact congrArg (fun z ↦ z.1.asIdeal)
      ((PrimeSpectrum.preimageEquivFiber R S ps).left_inv ⟨qs, hqs⟩)
  letI : qf.IsPrime := hqf
  letI : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  letI : (qf.comap Algebra.TensorProduct.includeRight).IsPrime :=
    Ideal.IsPrime.comap _
  letI : (qf.comap Algebra.TensorProduct.includeRight).LiesOver p :=
    Ideal.under_liesOver_of_liesOver S qf p
  letI : Algebra (Localization.AtPrime p)
      (Localization.AtPrime (qf.comap Algebra.TensorProduct.includeRight)) :=
    Localization.AtPrime.algebraOfLiesOver p _
  let e := Ideal.Fiber.localizationAlgEquivQuotient p qf
  exact ⟨qf, inferInstance, ⟨hq ▸ e.toRingEquiv⟩⟩

/-- An integrally closed domain is a normal ring in the local-at-every-prime sense. -/
lemma IsNormalRing.of_isDomain_of_isIntegrallyClosed
    {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] :
    IsNormalRing A := by
  constructor
  · intro p hp
    letI : p.IsPrime := hp
    infer_instance
  · intro p hp
    letI : p.IsPrime := hp
    exact isIntegrallyClosed_of_isLocalization (Localization.AtPrime p)
      p.primeCompl p.primeCompl_le_nonZeroDivisors

/-- Normality of a fiber makes the closed fiber of the corresponding flat-local setup an
integrally closed domain. -/
lemma IsNormalRing.closedFiber_isDomain_and_isIntegrallyClosed
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S)) (hn : IsNormalRing (p.Fiber S)) :
    IsDomain (Localization.AtPrime q ⧸
        p.map (algebraMap R (Localization.AtPrime q))) ∧
      IsIntegrallyClosed (Localization.AtPrime q ⧸
        p.map (algebraMap R (Localization.AtPrime q))) := by
  obtain ⟨qf, hqf, ⟨e⟩⟩ :=
    Ideal.Fiber.exists_localizationRingEquivQuotient p q hpq
  letI : qf.IsPrime := hqf
  letI : IsDomain (Localization.AtPrime qf) := hn.isDomain_localization qf
  letI : IsIntegrallyClosed (Localization.AtPrime qf) :=
    hn.isIntegrallyClosed_localization qf
  have hdomain : IsDomain (Localization.AtPrime q ⧸
      p.map (algebraMap R (Localization.AtPrime q))) := e.symm.injective.isDomain
  have hclosed : IsIntegrallyClosed (Localization.AtPrime q ⧸
      p.map (algebraMap R (Localization.AtPrime q))) :=
    @IsIntegrallyClosed.of_equiv (Localization.AtPrime qf)
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))
      inferInstance inferInstance e inferInstance
  exact ⟨hdomain, hclosed⟩

/-- A closed fiber coming from a normal fiber is regular when its dimension is at most one. -/
lemma IsNormalRing.closedFiber_isRegularLocalRing_of_ringKrullDim_le_one
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S)) (hn : IsNormalRing (p.Fiber S))
    (hdim : ringKrullDim (Localization.AtPrime q ⧸
      p.map (algebraMap R (Localization.AtPrime q))) ≤ 1) :
    IsRegularLocalRing (Localization.AtPrime q ⧸
      p.map (algebraMap R (Localization.AtPrime q))) := by
  obtain ⟨hdomain, hclosed⟩ :=
    hn.closedFiber_isDomain_and_isIntegrallyClosed p q hpq
  letI : IsDomain (Localization.AtPrime q ⧸
      p.map (algebraMap R (Localization.AtPrime q))) := hdomain
  letI : IsLocalRing (Localization.AtPrime q ⧸
      p.map (algebraMap R (Localization.AtPrime q))) :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  letI : IsIntegrallyClosed (Localization.AtPrime q ⧸
      p.map (algebraMap R (Localization.AtPrime q))) := hclosed
  exact IsIntegrallyClosed.isRegularLocalRing_of_ringKrullDim_le_one hdim

/-- If `p` is associated to `A/I`, it is the colon ideal of one element outside `I`. -/
lemma Ideal.exists_notMem_forall_mem_iff_mul_mem_of_mem_associatedPrimes
    {A : Type u} [CommRing A] [IsNoetherianRing A] {I p : Ideal A}
    (h : p ∈ associatedPrimes A (A ⧸ I)) :
    ∃ y ∉ I, ∀ r : A, r ∈ p ↔ r * y ∈ I := by
  obtain ⟨hprime, ybar, hann⟩ :=
    Submodule.isAssociatedPrime_iff.mp (AssociatedPrimes.mem_iff.mp h)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective ybar
  have hmem : ∀ r : A, r ∈ p ↔ r * y ∈ I := by
    intro r
    rw [hann, Submodule.mem_colon_singleton]
    have hsmul : r • Ideal.Quotient.mk I y =
        Ideal.Quotient.mk I (r * y) := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
    rw [hsmul, Submodule.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨y, fun hy ↦ hprime.ne_top ?_, hmem⟩
  rw [Ideal.eq_top_iff_one, hmem, one_mul]
  exact hy

/-- If multiplication by a fraction sends the maximal ideal into the ring and sends one
element of that ideal to `1`, then that element generates the maximal ideal. -/
lemma IsLocalRing.maximalIdeal_eq_span_of_mul_algebraMap_eq_one
    {A K : Type u} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
    [IsFractionRing A K] {z : K}
    (hz : ∀ r ∈ maximalIdeal A, ∃ k : A,
      z * algebraMap A K r = algebraMap A K k)
    {g : A} (hg : g ∈ maximalIdeal A) (hzg : z * algebraMap A K g = 1) :
    maximalIdeal A = Ideal.span {g} := by
  refine le_antisymm (fun r hr ↦ ?_) ?_
  · obtain ⟨k, hk⟩ := hz r hr
    rw [Ideal.mem_span_singleton']
    refine ⟨k, IsFractionRing.injective A K ?_⟩
    rw [map_mul, ← hk]
    calc
      z * algebraMap A K r * algebraMap A K g =
          (z * algebraMap A K g) * algebraMap A K r := by ring
      _ = algebraMap A K r := by rw [hzg, one_mul]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hg

/-- The determinant trick for an integrally closed Noetherian local ring: a fraction
preserving the image of a nonzero maximal ideal already belongs to the ring. -/
lemma IsIntegrallyClosed.exists_algebraMap_eq_of_smul_map_maximalIdeal_le
    {A K : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hbot : maximalIdeal A ≠ ⊥) {z : K}
    (hz : ∀ w ∈ Submodule.map (Algebra.linearMap A K) (maximalIdeal A),
      z • w ∈ Submodule.map (Algebra.linearMap A K) (maximalIdeal A)) :
    ∃ w : A, algebraMap A K w = z := by
  have hint : IsIntegral A z := by
    refine isIntegral_of_smul_mem_submodule
      (Submodule.map (Algebra.linearMap A K) (maximalIdeal A)) ?_ ?_ z hz
    · obtain ⟨x, hx, hx0⟩ := Submodule.ne_bot_iff _ |>.mp hbot
      rw [Submodule.ne_bot_iff]
      exact ⟨algebraMap A K x, ⟨x, hx, rfl⟩,
        fun h0 ↦ hx0 (IsFractionRing.injective A K (by rw [h0, map_zero]))⟩
    · exact Submodule.FG.map _ (IsNoetherian.noetherian _)
  exact IsIntegrallyClosed.algebraMap_eq_of_integral hint

/-- If the maximal ideal of an integrally closed Noetherian local domain is associated to
`A/xA` for nonzero `x`, then the ring is a discrete valuation ring. -/
lemma IsDiscreteValuationRing.of_maximalIdeal_mem_associatedPrimes
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [IsIntegrallyClosed A] {x : A} (hx : x ≠ 0)
    (h : maximalIdeal A ∈ associatedPrimes A (A ⧸ Ideal.span {x})) :
    IsDiscreteValuationRing A := by
  obtain ⟨y, hy_notmem, hmem⟩ :=
    Ideal.exists_notMem_forall_mem_iff_mul_mem_of_mem_associatedPrimes h
  have hx_mem : x ∈ maximalIdeal A :=
    (hmem x).mpr (Ideal.mem_span_singleton.mpr ⟨y, rfl⟩)
  have hm_ne : maximalIdeal A ≠ ⊥ := fun h0 ↦
    hx (by rwa [h0, Submodule.mem_bot] at hx_mem)
  have hxK : algebraMap A (FractionRing A) x ≠ 0 :=
    IsFractionRing.to_map_eq_zero_iff.not.mpr hx
  set z : FractionRing A :=
    algebraMap A (FractionRing A) y / algebraMap A (FractionRing A) x with hz_def
  have hz_mul : ∀ r ∈ maximalIdeal A, ∃ k : A,
      z * algebraMap A (FractionRing A) r = algebraMap A (FractionRing A) k := by
    intro r hr
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton.mp ((hmem r).mp hr)
    refine ⟨k, ?_⟩
    rw [hz_def, div_mul_eq_mul_div, ← map_mul, mul_comm y r, hk, map_mul,
      mul_comm (algebraMap A (FractionRing A) x), mul_div_assoc,
      div_self hxK, mul_one]
  by_cases hzM : ∀ w ∈ Submodule.map (Algebra.linearMap A (FractionRing A))
      (maximalIdeal A), z • w ∈ Submodule.map
        (Algebra.linearMap A (FractionRing A)) (maximalIdeal A)
  · exfalso
    obtain ⟨w, hw⟩ :=
      IsIntegrallyClosed.exists_algebraMap_eq_of_smul_map_maximalIdeal_le hm_ne hzM
    apply hy_notmem
    rw [Ideal.mem_span_singleton']
    refine ⟨w, IsFractionRing.injective A (FractionRing A) ?_⟩
    rw [map_mul, hw, hz_def]
    exact div_mul_cancel₀ _ hxK
  · push Not at hzM
    obtain ⟨w₀, hw₀, hzw₀⟩ := hzM
    obtain ⟨r₀, hr₀, rfl⟩ := hw₀
    obtain ⟨c₀, hc₀⟩ := hz_mul r₀ hr₀
    have hc₀_unit : IsUnit c₀ := by
      by_contra hcu
      refine hzw₀ ⟨c₀, (mem_maximalIdeal _).mpr hcu, ?_⟩
      rw [Algebra.linearMap_apply, ← hc₀]
      rfl
    obtain ⟨v, hv⟩ := hc₀_unit
    have hg_mem : (↑v⁻¹ : A) * r₀ ∈ maximalIdeal A :=
      Ideal.mul_mem_left _ _ hr₀
    have hzg : z * algebraMap A (FractionRing A) ((↑v⁻¹ : A) * r₀) = 1 := by
      rw [map_mul, mul_comm (algebraMap A (FractionRing A) (↑v⁻¹ : A)),
        ← mul_assoc, hc₀, ← hv, ← map_mul, v.mul_inv, map_one]
    have hspan := maximalIdeal_eq_span_of_mul_algebraMap_eq_one hz_mul hg_mem hzg
    have hnf : ¬ IsField A := fun hf ↦
      hm_ne (isField_iff_maximalIdeal_eq.mp hf)
    have hprincipal : (maximalIdeal A).IsPrincipal := ⟨⟨_, hspan⟩⟩
    exact ((IsDiscreteValuationRing.TFAE A hnf).out 0 4).mpr hprincipal

/-- Quotienting a nonzero finite module by an element of the maximal ideal leaves a
nonzero module. -/
lemma QuotSMulTop.nontrivial_of_mem_maximalIdeal
    {R M : Type u} [CommRing R] [IsLocalRing R] [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Nontrivial M]
    (r : R) (hr : r ∈ maximalIdeal R) : Nontrivial (QuotSMulTop r M) := by
  have htop : r • (⊤ : Submodule R M) ≠ ⊤ := by
    intro h
    have hspan : Ideal.span {r} • (⊤ : Submodule R M) = ⊤ := by
      rw [Submodule.ideal_span_singleton_smul, h]
    obtain ⟨f, hf, hzero⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
        (Ideal.span {r}) ⊤ (Module.finite_def.mp inferInstance)
        (by rw [hspan])
    have hf_m : f - 1 ∈ maximalIdeal R := by
      apply (Ideal.span_le.mpr _ : Ideal.span {r} ≤ maximalIdeal R) hf
      rintro _ rfl
      exact hr
    have hf_not_m : f ∉ maximalIdeal R := by
      intro hf_in_m
      have h1 : f - (f - 1) ∈ maximalIdeal R :=
        Ideal.sub_mem _ hf_in_m hf_m
      rw [sub_sub_cancel] at h1
      exact (maximalIdeal.isMaximal R).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    have hf_unit : IsUnit f := notMem_maximalIdeal.mp hf_not_m
    have hM_zero : (⊤ : Submodule R M) = ⊥ := by
      rw [eq_bot_iff]
      intro x _
      have : f • x = 0 := hzero x trivial
      exact (IsUnit.smul_eq_zero hf_unit).mp this
    obtain ⟨x, hx⟩ : ∃ x : M, x ≠ 0 := exists_ne 0
    have : x ∈ (⊤ : Submodule R M) := trivial
    rw [hM_zero, Submodule.mem_bot] at this
    exact hx this
  exact Submodule.Quotient.nontrivial_iff.mpr htop

/-- A Noetherian ring satisfies the two-element form of Serre's condition `(S₂)` when every
prime of height at least two admits a regular sequence of length two in its localization. -/
def SerreTwo (R : Type u) [CommRing R] [IsNoetherianRing R] : Prop :=
  ∀ (p : Ideal R) (_ : p.IsPrime), 2 ≤ p.height →
    ∃ a b : Localization.AtPrime p,
      a ∈ maximalIdeal (Localization.AtPrime p) ∧
      b ∈ maximalIdeal (Localization.AtPrime p) ∧
      RingTheory.Sequence.IsRegular (Localization.AtPrime p) [a, b]

/-- A Noetherian ring satisfies Serre's condition `(R₁)` when its localizations at primes
of height at most one are regular local rings. -/
def SerreOne (R : Type u) [CommRing R] [IsNoetherianRing R] : Prop :=
  ∀ (p : Ideal R) (_ : p.IsPrime), p.height ≤ 1 →
    IsRegularLocalRing (Localization.AtPrime p)

/-- A normal Noetherian ring satisfies `(R₁)`. -/
lemma IsNormalRing.serreOne {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsNormalRing R] : SerreOne R := by
  intro p hp hheight
  letI : p.IsPrime := hp
  letI : IsDomain (Localization.AtPrime p) :=
    IsNormalRing.isDomain_localization p
  letI : IsIntegrallyClosed (Localization.AtPrime p) :=
    IsNormalRing.isIntegrallyClosed_localization p
  apply IsIntegrallyClosed.isRegularLocalRing_of_ringKrullDim_le_one
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
  exact_mod_cast hheight

/-- A normal Noetherian ring satisfies the two-element form of `(S₂)`. -/
lemma IsNormalRing.serreTwo {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsNormalRing R] : SerreTwo R := by
  intro p hp hheight
  letI : p.IsPrime := hp
  let A := Localization.AtPrime p
  letI : IsDomain A := IsNormalRing.isDomain_localization p
  letI : IsIntegrallyClosed A :=
    IsNormalRing.isIntegrallyClosed_localization p
  have hm_ne : maximalIdeal A ≠ ⊥ := by
    intro hm
    have hdim : ringKrullDim A = 0 := by
      rw [← maximalIdeal_height_eq_ringKrullDim, hm]
      simp
    have hpheight : p.height = 0 := by
      have hloc := IsLocalization.AtPrime.ringKrullDim_eq_height p A
      rw [hdim] at hloc
      exact_mod_cast hloc.symm
    simpa [hpheight] using hheight
  obtain ⟨a, ha_mem, ha⟩ := Submodule.ne_bot_iff _ |>.mp hm_ne
  have hnot : maximalIdeal A ∉ associatedPrimes A (A ⧸ Ideal.span {a}) := by
    intro hass
    have hdvr : IsDiscreteValuationRing A :=
      IsDiscreteValuationRing.of_maximalIdeal_mem_associatedPrimes ha hass
    have hdim := IsDiscreteValuationRing.ringKrullDim_eq_one A
    have hloc := IsLocalization.AtPrime.ringKrullDim_eq_height p A
    have hpheight : p.height = 1 := by
      rw [hdim] at hloc
      exact_mod_cast hloc.symm
    simpa [hpheight] using hheight
  let e : (A ⧸ Ideal.span {a}) ≃ₗ[A] QuotSMulTop a A :=
    Submodule.quotEquivOfEq _ _ (by
      simpa using (Submodule.ideal_span_singleton_smul a
        (⊤ : Submodule A A)))
  have hnot' : maximalIdeal A ∉ associatedPrimes A (QuotSMulTop a A) := by
    rwa [← LinearEquiv.AssociatedPrimes.eq e]
  obtain ⟨b, hb_mem, -, hb⟩ :=
    IsLocalRing.exists_notMem_pow_two_isSMulRegular
      (QuotSMulTop a A) hnot' hm_ne
  letI : Nontrivial (QuotSMulTop a A) :=
    QuotSMulTop.nontrivial_of_mem_maximalIdeal a ha_mem
  letI : Nontrivial (QuotSMulTop b (QuotSMulTop a A)) :=
    QuotSMulTop.nontrivial_of_mem_maximalIdeal b hb_mem
  refine ⟨a, b, ha_mem, hb_mem, ?_⟩
  rw [RingTheory.Sequence.isRegular_cons_iff A a [b],
    RingTheory.Sequence.isRegular_cons_iff (QuotSMulTop a A) b []]
  exact ⟨IsSMulRegular.of_ne_zero ha, hb,
    RingTheory.Sequence.IsRegular.nil A _⟩

/-- An integrally closed Noetherian local domain of dimension at least two contains a
regular pair in its maximal ideal. -/
lemma IsIntegrallyClosed.exists_regularPair_of_ringKrullDim_ge_two
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsDomain A] [IsIntegrallyClosed A] (hdim : 2 ≤ ringKrullDim A) :
    ∃ a b : A, a ∈ maximalIdeal A ∧ b ∈ maximalIdeal A ∧
      RingTheory.Sequence.IsRegular A [a, b] := by
  have hmheight : 2 ≤ (maximalIdeal A).height := by
    have h := hdim
    rw [← maximalIdeal_height_eq_ringKrullDim] at h
    exact WithBot.coe_le_coe.mp (by simpa using h)
  have hm_ne : maximalIdeal A ≠ ⊥ := by
    intro hm
    rw [hm] at hmheight
    simp at hmheight
  obtain ⟨a, ha_mem, ha⟩ := Submodule.ne_bot_iff _ |>.mp hm_ne
  have hnot : maximalIdeal A ∉ associatedPrimes A (A ⧸ Ideal.span {a}) := by
    intro hass
    have hdvr : IsDiscreteValuationRing A :=
      IsDiscreteValuationRing.of_maximalIdeal_mem_associatedPrimes ha hass
    have hdim' := IsDiscreteValuationRing.ringKrullDim_eq_one A
    rw [hdim'] at hdim
    norm_num at hdim
  let e : (A ⧸ Ideal.span {a}) ≃ₗ[A] QuotSMulTop a A :=
    Submodule.quotEquivOfEq _ _ (by
      simpa using (Submodule.ideal_span_singleton_smul a
        (⊤ : Submodule A A)))
  have hnot' : maximalIdeal A ∉ associatedPrimes A (QuotSMulTop a A) := by
    rwa [← LinearEquiv.AssociatedPrimes.eq e]
  obtain ⟨b, hb_mem, -, hb⟩ :=
    IsLocalRing.exists_notMem_pow_two_isSMulRegular
      (QuotSMulTop a A) hnot' hm_ne
  letI : Nontrivial (QuotSMulTop a A) :=
    QuotSMulTop.nontrivial_of_mem_maximalIdeal a ha_mem
  letI : Nontrivial (QuotSMulTop b (QuotSMulTop a A)) :=
    QuotSMulTop.nontrivial_of_mem_maximalIdeal b hb_mem
  refine ⟨a, b, ha_mem, hb_mem, ?_⟩
  rw [RingTheory.Sequence.isRegular_cons_iff A a [b],
    RingTheory.Sequence.isRegular_cons_iff (QuotSMulTop a A) b []]
  exact ⟨IsSMulRegular.of_ne_zero ha, hb,
    RingTheory.Sequence.IsRegular.nil A _⟩

/-- The projection `M/rⁿ⁺¹M → M/rⁿM`. -/
def QuotSMulTop.projPow {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) (n : ℕ) : QuotSMulTop (r ^ (n + 1)) M →ₗ[R] QuotSMulTop (r ^ n) M :=
  Submodule.liftQ _ (Submodule.mkQ (r ^ n • ⊤)) <| by
    intro x hx
    obtain ⟨y, -, rfl⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists x (r ^ (n + 1)) ⊤).mp hx
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      pow_succ, mul_smul]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨r • y, trivial, rfl⟩

/-- The projection `M/rⁿ⁺¹M → M/rⁿM` is surjective. -/
lemma QuotSMulTop.projPow_surjective
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) (n : ℕ) : Function.Surjective (QuotSMulTop.projPow (M := M) r n) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact ⟨Submodule.Quotient.mk x, rfl⟩

/-- Multiplication by `rⁿ` induces `M/rM → M/rⁿ⁺¹M`. -/
def QuotSMulTop.liftPow {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) (n : ℕ) : QuotSMulTop r M →ₗ[R] QuotSMulTop (r ^ (n + 1)) M :=
  Submodule.liftQ _ ((Submodule.mkQ (r ^ (n + 1) • ⊤)).comp (r ^ n • LinearMap.id)) <| by
    intro x hx
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x r ⊤).mp hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      ← mul_smul, pow_succ]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y, trivial, rfl⟩

/-- If `r` is regular on `M`, multiplication by `rⁿ` embeds `M/rM` in `M/rⁿ⁺¹M`. -/
lemma QuotSMulTop.liftPow_injective
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) (n : ℕ) (hr : IsSMulRegular M r) :
    Function.Injective (QuotSMulTop.liftPow (M := M) r n) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (r ^ n • x) = 0 at hx
  rw [Submodule.Quotient.mk_eq_zero] at hx
  obtain ⟨y, -, hy⟩ :=
    (Submodule.mem_smul_pointwise_iff_exists _ (r ^ (n + 1)) ⊤).mp hx
  have heq : r ^ n • x = r ^ n • (r • y) := by
    rw [← hy, pow_succ, mul_smul]
  have hxy : x = r • y := by
    apply hr.pow n
    exact heq
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
    ⟨y, trivial, hxy.symm⟩

/-- The sequence `M/rM → M/rⁿ⁺¹M → M/rⁿM` is exact. -/
lemma QuotSMulTop.exact_pow
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (r : R) (n : ℕ) :
    LinearMap.range (QuotSMulTop.liftPow (M := M) r n) =
      LinearMap.ker (QuotSMulTop.projPow (M := M) r n) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Submodule.Quotient.mk (r ^ n • y) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨y, trivial, rfl⟩
  · intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    change Submodule.Quotient.mk x = 0 at hx
    rw [Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨y, -, hy⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists _ (r ^ n) ⊤).mp hx
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    change Submodule.Quotient.mk (r ^ n • y) = Submodule.Quotient.mk x
    rw [Submodule.Quotient.eq, hy, sub_self]
    exact zero_mem _

/-- Weak regularity on the outer terms of a short exact sequence implies weak regularity on
the middle term. -/
lemma RingTheory.Sequence.isWeaklyRegular_of_shortExact
    {R M₁ M₂ M₃ : Type*} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hinj : Function.Injective f) (hexact : Function.Exact f g)
    (hsurj : Function.Surjective g) (rs : List R)
    (h₁ : RingTheory.Sequence.IsWeaklyRegular M₁ rs)
    (h₃ : RingTheory.Sequence.IsWeaklyRegular M₃ rs) :
    RingTheory.Sequence.IsWeaklyRegular M₂ rs := by
  induction rs generalizing M₁ M₂ M₃ with
  | nil => simp
  | cons r rs ih =>
      simp only [RingTheory.Sequence.isWeaklyRegular_cons_iff] at h₁ h₃ ⊢
      have hr₂ : IsSMulRegular M₂ r := by
        intro x y hxy
        have hsub : r • (x - y) = 0 := by
          change r • x = r • y at hxy
          rw [smul_sub, hxy, sub_self]
        have hgsub : r • g (x - y) = r • 0 := by
          rw [← map_smul, hsub, map_zero, smul_zero]
        have hgzero : g (x - y) = 0 := h₃.1 hgsub
        have hxrange : x - y ∈ LinearMap.range f := by
          rw [← hexact.linearMap_ker_eq]
          exact hgzero
        obtain ⟨z, hz⟩ := hxrange
        have hfz : f (r • z) = f 0 := by rw [map_smul, hz, hsub, f.map_zero]
        have hzsmul : r • z = r • 0 := by
          rw [hinj hfz, smul_zero]
        have hzzero : z = 0 := h₁.1 hzsmul
        rw [← sub_eq_zero, ← hz, hzzero, map_zero]
      refine ⟨hr₂, ?_⟩
      have hinjmap : Function.Injective (QuotSMulTop.map r f) := by
        have hzeroexact : Function.Exact (0 : M₁ →ₗ[R] M₁) f := by
          intro x
          constructor
          · intro hx
            have : x = 0 := hinj (by simpa using hx)
            rw [this]
            exact ⟨0, rfl⟩
          · rintro ⟨y, hy⟩
            simpa [← hy]
        have hmapexact : Function.Exact
            (QuotSMulTop.map r (0 : M₁ →ₗ[R] M₁)) (QuotSMulTop.map r f) :=
          QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
            hzeroexact hexact h₃.1
        have hmapzero : QuotSMulTop.map r (0 : M₁ →ₗ[R] M₁) = 0 := by
          ext
          simp
        rw [hmapzero] at hmapexact
        intro x y hxy
        have hker : x - y ∈ LinearMap.ker (QuotSMulTop.map r f) := by
          rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
        rw [hmapexact.linearMap_ker_eq] at hker
        obtain ⟨w, hw⟩ := hker
        rw [← sub_eq_zero, ← hw, LinearMap.zero_apply]
      exact ih (QuotSMulTop.map r f) (QuotSMulTop.map r g) hinjmap
        (QuotSMulTop.map_exact r hexact hsurj)
        (QuotSMulTop.map_surjective r hsurj) h₁.2 h₃.2

/-- Regularity on the outer terms of a short exact sequence implies regularity on the middle
term. -/
lemma RingTheory.Sequence.IsRegular.of_shortExact
    {R M₁ M₂ M₃ : Type*} [CommRing R]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hinj : Function.Injective f)
    (hexact : LinearMap.range f = LinearMap.ker g)
    (hsurj : Function.Surjective g) (rs : List R)
    (h₁ : RingTheory.Sequence.IsRegular M₁ rs)
    (h₃ : RingTheory.Sequence.IsRegular M₃ rs) :
    RingTheory.Sequence.IsRegular M₂ rs := by
  have he : Function.Exact f g := by
    intro x
    rw [← LinearMap.mem_ker, ← hexact]
    rfl
  refine ⟨RingTheory.Sequence.isWeaklyRegular_of_shortExact f g hinj he hsurj rs h₁.1 h₃.1,
    ?_⟩
  intro htop
  have hne := h₃.top_ne_smul
  apply hne
  have hrange : (⊤ : Submodule R M₃) = LinearMap.range g := by
    ext z
    simp [hsurj z]
  symm
  calc
    Ideal.ofList rs • (⊤ : Submodule R M₃) =
        Submodule.map g (Ideal.ofList rs • (⊤ : Submodule R M₂)) := by
          rw [hrange, ← Submodule.map_top, Submodule.map_smul'']
    _ = ⊤ := by rw [← htop, Submodule.map_top, ← hrange]

/-- A regular sequence modulo `r` stays regular modulo every positive power of `r`. -/
lemma RingTheory.Sequence.IsRegular.quotSMulTop_pow
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (rs : List R) (r : R) (n : ℕ) (hn : 0 < n)
    (hbase : RingTheory.Sequence.IsRegular (QuotSMulTop r M) rs)
    (hr : IsSMulRegular M r) :
    RingTheory.Sequence.IsRegular (QuotSMulTop (r ^ n) M) rs := by
  induction n with
  | zero => contradiction
  | succ n ih =>
      cases n with
      | zero =>
          let e : QuotSMulTop (r ^ 1) M ≃ₗ[R] QuotSMulTop r M :=
            Submodule.quotEquivOfEq _ _ (by rw [pow_one])
          exact (LinearEquiv.isRegular_congr e.symm rs).mp hbase
      | succ m =>
          exact RingTheory.Sequence.IsRegular.of_shortExact
            (QuotSMulTop.liftPow r (m + 1)) (QuotSMulTop.projPow r (m + 1))
            (QuotSMulTop.liftPow_injective r (m + 1) hr)
            (QuotSMulTop.exact_pow r (m + 1))
            (QuotSMulTop.projPow_surjective r (m + 1)) rs hbase
            (ih (by simp))

/-- Replacing every member of a regular sequence by a positive power preserves regularity. -/
lemma RingTheory.Sequence.IsRegular.pow_of_isRegular
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (rs : List R) (e : List ℕ) (hlen : rs.length = e.length)
    (hpos : ∀ i : Fin e.length, 0 < e[i]) :
    RingTheory.Sequence.IsRegular M rs →
      RingTheory.Sequence.IsRegular M (List.zipWith (fun x n ↦ x ^ n) rs e) := by
  revert M e
  induction rs with
  | nil =>
      intro M _ _ e hlen _ hM
      cases e with
      | nil => exact hM
      | cons _ _ => contradiction
  | cons r rs ih =>
      intro M _ _ e hlen hpos hM
      cases e with
      | nil => contradiction
      | cons n e =>
          simp only [List.length_cons, Nat.succ.injEq] at hlen
          have hn : 0 < n := hpos ⟨0, by simp⟩
          have hepos : ∀ i : Fin e.length, 0 < e[i] :=
            fun i ↦ hpos ⟨i.val + 1, by simp⟩
          rw [RingTheory.Sequence.isRegular_cons_iff] at hM
          rw [show List.zipWith (fun x n ↦ x ^ n) (r :: rs) (n :: e) =
              r ^ n :: List.zipWith (fun x n ↦ x ^ n) rs e from rfl,
            RingTheory.Sequence.isRegular_cons_iff]
          refine ⟨hM.1.pow n, ?_⟩
          exact RingTheory.Sequence.IsRegular.quotSMulTop_pow
            (List.zipWith (fun x n ↦ x ^ n) rs e) r n hn
            (ih e hlen hepos hM.2) hM.1

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- Regularity of a scalar is preserved by a semilinear equivalence. -/
lemma IsSMulRegular.of_semiLinearEquiv
    {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (e₁ : R ≃+* S) (e₂ : M ≃ₛₗ[(e₁ : R →+* S)] N) {x : R}
    (hx : IsSMulRegular M x) : IsSMulRegular N (e₁ x) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := e₂.surjective a
  obtain ⟨b, rfl⟩ := e₂.surjective b
  change (e₁ : R →+* S) x • e₂.toLinearMap a =
    (e₁ : R →+* S) x • e₂.toLinearMap b at hab
  have habm : e₂.toLinearMap (x • a) = e₂.toLinearMap (x • b) :=
    (map_smulₛₗ e₂.toLinearMap x a).trans
      (hab.trans (map_smulₛₗ e₂.toLinearMap x b).symm)
  have hab' : a = b := hx (e₂.injective habm)
  exact congrArg e₂.toAddEquiv.toFun hab'

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- A semilinear equivalence sends `x • ⊤` to `e(x) • ⊤`. -/
lemma Submodule.map_smul_top_semiLinearEquiv
    {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (e₁ : R ≃+* S) (e₂ : M ≃ₛₗ[(e₁ : R →+* S)] N) (x : R) :
    Submodule.map e₂.toLinearMap (x • (⊤ : Submodule R M)) =
      e₁ x • (⊤ : Submodule S N) := by
  ext n
  rw [Submodule.mem_map,
    Submodule.mem_smul_pointwise_iff_exists _ (e₁ x) (⊤ : Submodule S N)]
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨c, -, rfl⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists _ x (⊤ : Submodule R M)).mp hm
    exact ⟨e₂.toAddEquiv.toFun c, trivial, by simp [map_smulₛₗ]⟩
  · rintro ⟨c, -, rfl⟩
    obtain ⟨c, rfl⟩ := e₂.surjective c
    refine ⟨x • c, ?_, ?_⟩
    · exact (Submodule.mem_smul_pointwise_iff_exists _ x _).mpr
        ⟨c, trivial, rfl⟩
    · exact map_smulₛₗ e₂.toLinearMap x c

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- A semilinear equivalence descends to quotient-by-one-element modules. -/
def QuotSMulTop.semiLinearEquiv
    {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (e₁ : R ≃+* S) (e₂ : M ≃ₛₗ[(e₁ : R →+* S)] N) (x : R) :
    QuotSMulTop x M ≃ₛₗ[(e₁ : R →+* S)] QuotSMulTop (e₁ x) N :=
  Submodule.Quotient.equiv (x • ⊤) (e₁ x • ⊤) e₂
    (Submodule.map_smul_top_semiLinearEquiv e₁ e₂ x)

attribute [local instance] RingHomInvPair.of_ringEquiv in
/-- A regular sequence is preserved by a semilinear equivalence and the corresponding ring
equivalence. -/
lemma RingTheory.Sequence.IsRegular.of_semiLinearEquiv
    {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (e₁ : R ≃+* S) (e₂ : M ≃ₛₗ[(e₁ : R →+* S)] N)
    {rs : List R} (h : RingTheory.Sequence.IsRegular M rs) :
    RingTheory.Sequence.IsRegular N (rs.map e₁) := by
  induction rs generalizing M N with
  | nil =>
      rw [List.map_nil]
      haveI : Nontrivial M := h.nontrivial
      haveI : Nontrivial N := e₂.injective.nontrivial
      exact RingTheory.Sequence.IsRegular.nil S N
  | cons x xs ih =>
      rw [List.map_cons, RingTheory.Sequence.isRegular_cons_iff]
      rw [RingTheory.Sequence.isRegular_cons_iff] at h
      exact ⟨h.1.of_semiLinearEquiv e₁ e₂,
        ih (QuotSMulTop.semiLinearEquiv e₁ e₂ x) h.2⟩

/-- Serre's condition `(R₁)` is preserved by localization. -/
lemma SerreOne.localization
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R]
    [IsNoetherianRing A] [Algebra R A] {M : Submonoid R} [IsLocalization M A]
    (h : SerreOne R) : SerreOne A := by
  intro q hq hheight
  letI : q.IsPrime := hq
  let r : Ideal R := q.under R
  letI : r.IsPrime := Ideal.IsPrime.comap (algebraMap R A)
  have hrheight : r.height ≤ 1 := by
    rw [show r = q.under R from rfl, IsLocalization.height_under M q]
    exact hheight
  letI : IsRegularLocalRing (Localization.AtPrime r) := h r inferInstance hrheight
  letI : IsLocalization.AtPrime (Localization.AtPrime q) r :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      M (Localization.AtPrime q) q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv r.primeCompl (Localization.AtPrime r)
      (Localization.AtPrime q)).toRingEquiv

/-- The two-element form of Serre's condition `(S₂)` is preserved by localization. -/
lemma SerreTwo.localization
    {R A : Type u} [CommRing R] [CommRing A] [IsNoetherianRing R]
    [IsNoetherianRing A] [Algebra R A] {M : Submonoid R} [IsLocalization M A]
    (h : SerreTwo R) : SerreTwo A := by
  intro q hq hheight
  letI : q.IsPrime := hq
  let r : Ideal R := q.under R
  letI : r.IsPrime := Ideal.IsPrime.comap (algebraMap R A)
  have hrheight : 2 ≤ r.height := by
    rw [show r = q.under R from rfl, IsLocalization.height_under M q]
    exact hheight
  obtain ⟨a, b, ha, hb, hab⟩ := h r inferInstance hrheight
  letI : IsLocalization.AtPrime (Localization.AtPrime q) r :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      M (Localization.AtPrime q) q
  let e : Localization.AtPrime r ≃ₐ[R] Localization.AtPrime q :=
    IsLocalization.algEquiv r.primeCompl _ _
  have hab' : RingTheory.Sequence.IsRegular (Localization.AtPrime q)
      [e a, e b] := by
    simpa using RingTheory.Sequence.IsRegular.of_semiLinearEquiv
      e.toRingEquiv e.toRingEquiv.toSemilinearEquiv hab
  have hea : e a ∈ maximalIdeal (Localization.AtPrime q) := by
    rw [← map_ringEquiv_maximalIdeal e.toRingEquiv]
    exact Ideal.mem_map_of_mem e.toRingEquiv ha
  have heb : e b ∈ maximalIdeal (Localization.AtPrime q) := by
    rw [← map_ringEquiv_maximalIdeal e.toRingEquiv]
    exact Ideal.mem_map_of_mem e.toRingEquiv hb
  exact ⟨e a, e b, hea, heb, hab'⟩

/-- If `a` is regular and the image of `b` in a domain quotient by `(a)` is nonzero,
then `[a, b]` is a regular pair. -/
lemma RingTheory.Sequence.IsRegular.pair_of_quotient
    {B : Type u} [CommRing B] [IsLocalRing B] {a b : B} (I : Ideal B)
    [IsDomain (B ⧸ I)] (hI : I = Ideal.span {a})
    (ha : IsSMulRegular B a) (hbmax : b ∈ maximalIdeal B)
    (hb : Ideal.Quotient.mk I b ≠ 0) :
    RingTheory.Sequence.IsRegular B [a, b] := by
  let e : (B ⧸ I) ≃ₗ[B] QuotSMulTop a B :=
    Submodule.quotEquivOfEq _ _ (hI.trans (by
      simpa using Submodule.ideal_span_singleton_smul a
        (⊤ : Submodule B B)))
  have hbC : IsSMulRegular (B ⧸ I) b := by
    intro x y hxy
    change Ideal.Quotient.mk I b * x = Ideal.Quotient.mk I b * y at hxy
    exact mul_left_cancel₀ hb hxy
  have hbQ : IsSMulRegular (QuotSMulTop a B) b :=
    (e.isSMulRegular_congr b).mp hbC
  haveI : Nontrivial (QuotSMulTop a B) := e.injective.nontrivial
  haveI : Nontrivial (QuotSMulTop b (QuotSMulTop a B)) :=
    QuotSMulTop.nontrivial_of_mem_maximalIdeal b hbmax
  rw [RingTheory.Sequence.isRegular_cons_iff B a [b],
    RingTheory.Sequence.isRegular_cons_iff (QuotSMulTop a B) b []]
  exact ⟨ha, hbQ, RingTheory.Sequence.IsRegular.nil B _⟩

/-- Positive powers of the members of a regular pair again form a regular pair. -/
lemma RingTheory.Sequence.IsRegular.pow_pair
    {R : Type*} [CommRing R] {a b : R}
    (h : RingTheory.Sequence.IsRegular R [a, b])
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    RingTheory.Sequence.IsRegular R [a ^ n, b ^ m] := by
  apply RingTheory.Sequence.IsRegular.pow_of_isRegular [a, b] [n, m]
    (by simp) _ h
  intro i
  fin_cases i
  · simpa using hn
  · simpa using hm

/-- The two-denominator form of the Hartogs argument: if a fraction becomes integral after
multiplication by both members of a regular pair, then it is already integral. -/
lemma exists_algebraMap_eq_of_regularPair
    {A : Type u} [CommRing A] [Nontrivial A] {x : FractionRing A} {a b c d : A}
    (hreg : RingTheory.Sequence.IsRegular A [a, b])
    (ha : algebraMap A (FractionRing A) a * x =
      algebraMap A (FractionRing A) c)
    (hb : algebraMap A (FractionRing A) b * x =
      algebraMap A (FractionRing A) d) :
    ∃ w : A, algebraMap A (FractionRing A) w = x := by
  have hseq := (RingTheory.Sequence.isRegular_cons_iff A a [b]).mp hreg
  have hbuad : b * c = a * d := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_mul, map_mul]
    calc
      algebraMap A (FractionRing A) b * algebraMap A (FractionRing A) c =
          algebraMap A (FractionRing A) b *
            (algebraMap A (FractionRing A) a * x) := by rw [ha]
      _ = algebraMap A (FractionRing A) a *
            (algebraMap A (FractionRing A) b * x) := by ring
      _ = algebraMap A (FractionRing A) a *
            algebraMap A (FractionRing A) d := by rw [hb]
  have hquot : (Submodule.Quotient.mk c : QuotSMulTop a A) = 0 := by
    apply ((RingTheory.Sequence.isRegular_cons_iff (QuotSMulTop a A) b []).mp hseq.2).1
    simp only [zero_smul]
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, smul_zero,
      Submodule.Quotient.mk_eq_zero]
    rw [hbuad]
    simpa [smul_eq_mul] using
      Submodule.smul_mem_pointwise_smul d a (⊤ : Submodule A A) trivial
  have hc : c ∈ a • (⊤ : Submodule A A) :=
    (Submodule.Quotient.mk_eq_zero (a • (⊤ : Submodule A A))).mp hquot
  obtain ⟨w, -, hw⟩ := hc
  refine ⟨w, ?_⟩
  have haA : a ∈ nonZeroDivisors A :=
    isRegular_iff_mem_nonZeroDivisors.mp
      ((Commute.isRegular_iff (fun _ ↦ mul_comm a _)).mpr hseq.1)
  have haK : IsUnit (algebraMap A (FractionRing A) a) :=
    IsLocalization.map_units (FractionRing A) ⟨a, haA⟩
  apply haK.mul_left_cancel
  calc
    algebraMap A (FractionRing A) a * algebraMap A (FractionRing A) w =
        algebraMap A (FractionRing A) (a * w) := (map_mul _ _ _).symm
    _ = algebraMap A (FractionRing A) c := by
      simpa [smul_eq_mul] using
        congrArg (algebraMap A (FractionRing A)) hw
    _ = algebraMap A (FractionRing A) a * x := ha.symm

/-- The denominator ideal of a fraction `x`: its elements are precisely the scalars whose
product with `x` comes from the original ring. -/
def fractionDenominatorIdeal {R : Type u} [CommRing R]
    (x : FractionRing R) : Ideal R where
  carrier := {r | ∃ y : R, algebraMap R (FractionRing R) y =
    algebraMap R (FractionRing R) r * x}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c + d, by rw [map_add, map_add, add_mul, hc, hd]⟩
  smul_mem' := by
    rintro a b ⟨c, hc⟩
    exact ⟨a * c, by rw [smul_eq_mul, map_mul, map_mul, mul_assoc, hc]⟩

/-- An idempotent in the total ring of fractions of an integrally closed ring comes from
the original ring. -/
lemma exists_idempotent_in_ring_of_fractionRing
    {R : Type u} [CommRing R] [Nontrivial R] [IsIntegrallyClosed R]
    (e : FractionRing R) (he : e ^ 2 = e) :
    ∃ r : R, algebraMap R (FractionRing R) r = e := by
  have hint : IsIntegral R e := by
    use Polynomial.X ^ 2 - Polynomial.X
    constructor
    · apply Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow 2)
      rw [Polynomial.degree_X, Polynomial.degree_X_pow]
      decide
    · simp [he]
  exact (isIntegrallyClosed_iff (FractionRing R)).mp inferInstance hint

/-- Distinct minimal primes of a reduced integrally closed ring with finitely many minimal
primes are coprime. -/
lemma isCoprime_of_minimalPrimes_of_isIntegrallyClosed
    {R : Type u} [CommRing R] [IsReduced R]
    (hmin : (⊥ : Ideal R).minimalPrimes.Finite) (hclosed : IsIntegrallyClosed R)
    (p q : Ideal R) (hp : p ∈ (⊥ : Ideal R).minimalPrimes)
    (hq : q ∈ (⊥ : Ideal R).minimalPrimes) (hpq : p ≠ q) :
    IsCoprime p q := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hsup
  obtain ⟨m, hmmax, hsup_le⟩ := Ideal.exists_le_maximal _ hsup
  haveI : m.IsMaximal := hmmax
  haveI : m.IsPrime := Ideal.IsMaximal.isPrime hmmax
  have hpm : p ≤ m := le_sup_left.trans hsup_le
  have hqm : q ≤ m := le_sup_right.trans hsup_le
  let P := { r : Ideal R // r ∈ (⊥ : Ideal R).minimalPrimes }
  letI : DecidableEq P := Classical.decEq P
  letI : Finite P := hmin.to_subtype
  letI : Fintype P := Fintype.ofFinite P
  let I (r : P) : Ideal R := Finset.inf (Finset.univ.erase r) (fun r' ↦ r'.1)
  have hI_le (r r' : P) (hne : r' ≠ r) : I r ≤ r'.1 :=
    Finset.inf_le (Finset.mem_erase_of_ne_of_mem hne (Finset.mem_univ _))
  have hI_not_le (r : P) : ¬ I r ≤ r.1 := by
    intro hle
    obtain ⟨r', hr'mem, hr'le⟩ :=
      (Ideal.IsPrime.inf_le' r.2.1.1).mp hle
    have hr'ne : r' ≠ r := Finset.ne_of_mem_erase hr'mem
    have hrmin : Minimal (fun J : Ideal R ↦ J.IsPrime ∧ ⊥ ≤ J) r.1 := r.2
    have hr'eq : r'.1 = r.1 :=
      Minimal.eq_of_le hrmin ⟨r'.2.1.1, bot_le⟩ hr'le
    exact hr'ne (Subtype.ext hr'eq)
  have hexists (r : P) : ∃ a ∈ I r, a ∉ r.1 := by
    by_contra h
    push_neg at h
    exact hI_not_le r h
  choose a haI hanot using hexists
  have hmul_zero (r r' : P) (hne : r ≠ r') : a r * a r' = 0 := by
    have hmem : a r * a r' ∈ r'.1 * I r' :=
      Ideal.mul_mem_mul (hI_le r r' hne.symm (haI r)) (haI r')
    have hinf : r'.1 ⊓ I r' = ⊥ := by
      apply eq_bot_iff.mpr
      intro x hx
      have hxall : x ∈ sInf (⊥ : Ideal R).minimalPrimes := by
        apply Ideal.mem_sInf.mpr
        intro J hJ
        let j : P := ⟨J, hJ⟩
        by_cases hj : j = r'
        · have hJr : J = r'.1 := congrArg Subtype.val hj
          rw [hJr]
          exact hx.1
        · exact hI_le r' j hj hx.2
      rw [Ideal.sInf_minimalPrimes] at hxall
      exact IsNilpotent.eq_zero hxall
    exact Ideal.mem_bot.mp (hinf ▸ Ideal.mul_le_inf hmem)
  let s := ∑ r : P, a r
  have has (r : P) : a r * s = (a r) ^ 2 := by
    dsimp [s]
    rw [Finset.mul_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ r)]
    have hz : ∑ r' ∈ Finset.univ.erase r, a r * a r' = 0 := by
      apply Finset.sum_eq_zero
      intro r' hr'
      exact hmul_zero r r' (Finset.ne_of_mem_erase hr').symm
    rw [hz, zero_add, sq]
  have hs_regular (x : R) (hx : s * x = 0) : x = 0 := by
    have hax (r : P) : (a r) ^ 2 * x = 0 := by
      have : a r * (s * x) = 0 := by rw [hx, mul_zero]
      rwa [← mul_assoc, has r] at this
    have hxprime (r : P) : x ∈ r.1 := by
      have hm : (a r) ^ 2 * x ∈ r.1 := by rw [hax r]; exact r.1.zero_mem
      rcases r.2.1.1.mem_or_mem hm with ha | hx
      · have haa : a r * a r ∈ r.1 := by simpa [sq] using ha
        rcases r.2.1.1.mem_or_mem haa with ha | ha <;>
          exact False.elim (hanot r ha)
      · exact hx
    have hxall : x ∈ sInf (⊥ : Ideal R).minimalPrimes := by
      apply Ideal.mem_sInf.mpr
      intro J hJ
      exact hxprime ⟨J, hJ⟩
    rw [Ideal.sInf_minimalPrimes] at hxall
    exact IsNilpotent.eq_zero hxall
  have hs : s ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff.mpr
    ⟨hs_regular, fun x hx ↦ hs_regular x (by rw [mul_comm, hx])⟩
  let K := FractionRing R
  let su : IsUnit (algebraMap R K s) :=
    IsLocalization.map_units K ⟨s, hs⟩
  let sinv := su.unit⁻¹
  have hs_inv : algebraMap R K s * sinv = 1 := IsUnit.mul_val_inv su
  let pp : P := ⟨p, hp⟩
  let e : K := algebraMap R K (a pp) * sinv
  have he : e ^ 2 = e := by
    dsimp [e]
    rw [mul_pow, ← map_pow, ← has pp, map_mul]
    calc
      algebraMap R K (a pp) * algebraMap R K s * sinv ^ 2 =
          algebraMap R K (a pp) * (algebraMap R K s * sinv) * sinv := by
            rw [sq]
            ring
      _ = algebraMap R K (a pp) * sinv := by rw [hs_inv, mul_one]
  letI : Nontrivial R := by
    have hpne : p ≠ ⊤ := hp.1.1.ne_top
    exact nontrivial_of_ne 0 1 fun h01 ↦ hpne <| by
      apply Ideal.eq_top_of_isUnit_mem p p.zero_mem
      rw [h01]
      exact isUnit_one
  letI : IsIntegrallyClosed R := hclosed
  obtain ⟨c, hc⟩ := exists_idempotent_in_ring_of_fractionRing e he
  have hcs : c * s = a pp := by
    apply IsFractionRing.injective R K
    rw [map_mul, hc]
    dsimp [e]
    calc
      algebraMap R K (a pp) * sinv * algebraMap R K s =
          algebraMap R K (a pp) * (algebraMap R K s * sinv) := by ring
      _ = algebraMap R K (a pp) := by rw [hs_inv, mul_one]
  have hca : c * (a pp) ^ 2 = (a pp) ^ 2 := by
    calc
      c * (a pp) ^ 2 = c * (a pp * s) := by rw [has]
      _ = (c * s) * a pp := by ring
      _ = (a pp) ^ 2 := by rw [hcs, sq]
  have hOneSub : 1 - c ∈ p := by
    have hm : (1 - c) * (a pp) ^ 2 ∈ p := by
      rw [sub_mul, one_mul, hca, sub_self]
      exact p.zero_mem
    rcases hp.1.1.mem_or_mem hm with hc' | ha
    · exact hc'
    · have haa : a pp * a pp ∈ p := by simpa [sq] using ha
      rcases hp.1.1.mem_or_mem haa with ha | ha <;>
        exact False.elim (hanot pp ha)
  let qq : P := ⟨q, hq⟩
  have hcqzero : c * (a qq) ^ 2 = 0 := by
    calc
      c * (a qq) ^ 2 = c * (a qq * s) := by rw [has]
      _ = (c * s) * a qq := by ring
      _ = a pp * a qq := by rw [hcs]
      _ = 0 := hmul_zero pp qq (fun heq ↦ hpq (Subtype.ext_iff.mp heq))
  have hcq : c ∈ q := by
    have hm : c * (a qq) ^ 2 ∈ q := by rw [hcqzero]; exact q.zero_mem
    rcases hq.1.1.mem_or_mem hm with hc' | ha
    · exact hc'
    · have haa : a qq * a qq ∈ q := by simpa [sq] using ha
      rcases hq.1.1.mem_or_mem haa with ha | ha <;>
        exact False.elim (hanot qq ha)
  have hOne : (1 : R) ∈ m := by
    have := m.add_mem (hpm hOneSub) (hqm hcq)
    simpa using this
  exact hmmax.ne_top (Ideal.eq_top_of_isUnit_mem m hOne isUnit_one)

/-- A reduced Noetherian local ring that is integrally closed in its total ring of
fractions is a domain. -/
lemma IsIntegrallyClosed.isDomain_of_isLocalRing_of_isReduced
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsReduced R] [IsIntegrallyClosed R] : IsDomain R := by
  have hmin : (⊥ : Ideal R).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing R ⊥
  obtain ⟨p, hp⟩ :=
    Ideal.nonempty_minimalPrimes (R := R) (I := ⊥) bot_ne_top
  have huniq (q : Ideal R) (hq : q ∈ (⊥ : Ideal R).minimalPrimes) : q = p := by
    by_contra hqp
    have hcop := isCoprime_of_minimalPrimes_of_isIntegrallyClosed
      hmin inferInstance p q hp hq (fun hpq ↦ hqp hpq.symm)
    rw [Ideal.isCoprime_iff_sup_eq] at hcop
    have hle : p ⊔ q ≤ maximalIdeal R := sup_le
      (le_maximalIdeal hp.1.1.ne_top) (le_maximalIdeal hq.1.1.ne_top)
    have : (⊤ : Ideal R) ≤ maximalIdeal R := hcop ▸ hle
    exact (maximalIdeal.isMaximal R).ne_top (top_unique this)
  have hsInf : sInf (⊥ : Ideal R).minimalPrimes = p := by
    apply le_antisymm (sInf_le hp)
    intro x hx
    apply Ideal.mem_sInf.mpr
    intro q hq
    rw [huniq q hq]
    exact hx
  have hpbot : p = ⊥ := by
    rw [← hsInf, Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced]
  letI : (⊥ : Ideal R).IsPrime := hpbot ▸ hp.1.1
  exact IsDomain.of_bot_isPrime R

/-- Serre's conditions `(R₁)` and `(S₂)` make a reduced Noetherian ring integrally
closed in its total ring of fractions.  This is the denominator-ideal core of Serre's
criterion. -/
lemma isIntegrallyClosed_of_serreOne_serreTwo
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsReduced R]
    (hR₁ : SerreOne R) (hS₂ : SerreTwo R) : IsIntegrallyClosed R := by
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro x hx
  let I := fractionDenominatorIdeal x
  by_contra hone
  have hIne : I ≠ ⊤ := by
    intro htop
    apply hone
    have h1 : (1 : R) ∈ I := by rw [htop]; trivial
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, by simpa using hy⟩
  obtain ⟨p, hpmin⟩ := Ideal.nonempty_minimalPrimes hIne
  letI : p.IsPrime := hpmin.isPrime
  let A := Localization.AtPrime p
  have hNZ : nonZeroDivisors R ≤
      (nonZeroDivisors A).comap (algebraMap R A) := by
    intro s hs
    exact IsLocalization.map_nonZeroDivisors_le p.primeCompl A ⟨s, hs, rfl⟩
  let φ : FractionRing R →ₐ[R] FractionRing A :=
    AlgHom.mk' (IsLocalization.map _ (algebraMap R A) hNZ) (fun r y ↦ by
      simp only [Algebra.smul_def, map_mul]
      congr 1
      rw [IsLocalization.map_eq hNZ r,
        IsScalarTower.algebraMap_apply R A (FractionRing A)])
  have hxA : IsIntegral A (φ x) := (hx.map φ).tower_top
  have hmapI : I.map (algebraMap R A) ≤ fractionDenominatorIdeal (φ x) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    obtain ⟨y, hy⟩ := hr
    refine ⟨algebraMap R A y, ?_⟩
    rw [← IsScalarTower.algebraMap_apply R A (FractionRing A), ← φ.commutes,
      ← IsScalarTower.algebraMap_apply R A (FractionRing A), ← φ.commutes,
      ← map_mul, hy]
  have hlocal : ∃ y : A, algebraMap A (FractionRing A) y = φ x := by
    by_cases hpheight : p.height ≤ 1
    · letI : IsRegularLocalRing A := hR₁ p inferInstance hpheight
      letI : IsDomain A := IsRegularLocalRing.isDomain
      have hdim : ringKrullDim A ≤ 1 := by
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
        exact_mod_cast hpheight
      letI : IsIntegrallyClosed A :=
        IsRegularLocalRing.isIntegrallyClosed_of_ringKrullDim_le_one hdim
      exact (isIntegrallyClosed_iff (FractionRing A)).mp inferInstance hxA
    · have hpheight' : 2 ≤ p.height := by
        have hlt : (1 : ℕ∞) < p.height := lt_of_not_ge hpheight
        convert ENat.natCast_add_one_le_iff.mpr hlt using 1 <;> norm_num
      obtain ⟨a, b, ha, hb, hab⟩ := hS₂ p inferInstance hpheight'
      have hrad : (I.map (algebraMap R A)).radical = maximalIdeal A := by
        rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A]
        exact IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes A p I hpmin
      obtain ⟨n, hn⟩ := (I.map (algebraMap R A)).exists_radical_pow_le_of_fg
        (IsNoetherian.noetherian _)
      have hn' : (maximalIdeal A) ^ (n + 1) ≤ I.map (algebraMap R A) := by
        rw [← hrad]
        exact (Ideal.pow_le_pow_right n.le_succ).trans hn
      have han : a ^ (n + 1) ∈ fractionDenominatorIdeal (φ x) :=
        hmapI (hn' (Ideal.pow_mem_pow ha _))
      have hbn : b ^ (n + 1) ∈ fractionDenominatorIdeal (φ x) :=
        hmapI (hn' (Ideal.pow_mem_pow hb _))
      obtain ⟨c, hc⟩ := han
      obtain ⟨d, hd⟩ := hbn
      exact exists_algebraMap_eq_of_regularPair
        (hab.pow_pair (by omega) (by omega)) hc.symm hd.symm
  obtain ⟨y, hy⟩ := hlocal
  obtain ⟨⟨b, ⟨u, hu⟩⟩, hy'⟩ := IsLocalization.surj p.primeCompl y
  have hφeq : φ (algebraMap R (FractionRing R) u * x) =
      φ (algebraMap R (FractionRing R) b) := by
    simp only [map_mul, AlgHom.commutes]
    rw [← hy, show algebraMap R (FractionRing A) u =
      algebraMap A (FractionRing A) (algebraMap R A u) from
        (IsScalarTower.algebraMap_apply R A (FractionRing A) u).symm,
      ← map_mul, mul_comm, hy', show algebraMap A (FractionRing A) (algebraMap R A b) =
        algebraMap R (FractionRing A) b from
          (IsScalarTower.algebraMap_apply R A (FractionRing A) b).symm]
  set z := algebraMap R (FractionRing R) u * x -
    algebraMap R (FractionRing R) b with hz
  have hφzero : φ z = 0 := by rw [hz, map_sub, hφeq, sub_self]
  obtain ⟨⟨c, s⟩, hcz⟩ := IsLocalization.surj (M := nonZeroDivisors R) z
  have hczero : algebraMap R (FractionRing A) c = 0 := by
    have hmul : φ z * φ (algebraMap R (FractionRing R) (s : R)) =
        φ (algebraMap R (FractionRing R) c) := by rw [← map_mul, hcz]
    rw [hφzero, zero_mul, AlgHom.commutes] at hmul
    exact hmul.symm
  have hcA : algebraMap R A c = 0 := by
    apply IsFractionRing.injective A (FractionRing A)
    rw [map_zero, ← IsScalarTower.algebraMap_apply R A]
    exact hczero
  obtain ⟨⟨t, ht⟩, htc⟩ :=
    (IsLocalization.map_eq_zero_iff p.primeCompl A c).mp hcA
  have htz : algebraMap R (FractionRing R) t * z = 0 := by
    have hzero : algebraMap R (FractionRing R) t * z *
        algebraMap R (FractionRing R) (s : R) = 0 := by
      rw [mul_assoc, hcz, ← map_mul, htc, map_zero]
    exact (mul_right_mem_nonZeroDivisors_eq_zero_iff
      (IsLocalization.map_nonZeroDivisors_le (nonZeroDivisors R) (FractionRing R)
        ⟨(s : R), s.2, rfl⟩)).mp hzero
  have htu : algebraMap R (FractionRing R) (t * u) * x =
      algebraMap R (FractionRing R) (t * b) := by
    have hsub : algebraMap R (FractionRing R) t *
        (algebraMap R (FractionRing R) u * x) -
        algebraMap R (FractionRing R) t * algebraMap R (FractionRing R) b = 0 := by
      rw [← mul_sub]
      exact htz
    have heq := sub_eq_zero.mp hsub
    rwa [map_mul, map_mul, mul_assoc]
  exact p.primeCompl.mul_mem ht hu (hpmin.le ⟨t * b, htu.symm⟩)

/-- Serre's conditions `(R₁)` and `(S₂)` imply normality for a reduced Noetherian ring. -/
lemma IsNormalRing.of_serreOne_serreTwo
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsReduced R]
    (hR₁ : SerreOne R) (hS₂ : SerreTwo R) : IsNormalRing R := by
  constructor
  · intro p hp
    letI : p.IsPrime := hp
    let A := Localization.AtPrime p
    have hR₁A : SerreOne A := hR₁.localization (M := p.primeCompl)
    have hS₂A : SerreTwo A := hS₂.localization (M := p.primeCompl)
    letI : IsIntegrallyClosed A :=
      isIntegrallyClosed_of_serreOne_serreTwo hR₁A hS₂A
    exact IsIntegrallyClosed.isDomain_of_isLocalRing_of_isReduced
  · intro p hp
    letI : p.IsPrime := hp
    let A := Localization.AtPrime p
    exact isIntegrallyClosed_of_serreOne_serreTwo
      (hR₁.localization (A := A) (M := p.primeCompl))
      (hS₂.localization (A := A) (M := p.primeCompl))

/-- Serre's condition `(R₁)` ascends along a flat map of Noetherian rings when the
base and all fibers are normal. -/
lemma SerreOne.of_flat_of_fibers_normal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [IsNormalRing R]
    (hf : ∀ (p : Ideal R) [p.IsPrime], IsNormalRing (p.Fiber S)) :
    SerreOne S := by
  intro q hq hqheight
  letI : q.IsPrime := hq
  let p := q.comap (algebraMap R S)
  letI : p.IsPrime := Ideal.IsPrime.comap (algebraMap R S)
  letI : q.LiesOver p := ⟨rfl⟩
  let A := Localization.AtPrime p
  let B := Localization.AtPrime q
  letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver p q
  letI : Module.Flat A B := Module.Flat.atPrime p q rfl
  let I := Ideal.map (algebraMap A B) (maximalIdeal A)
  let C := B ⧸ I
  have hI : I = p.map (algebraMap R B) := by
    change Ideal.map (algebraMap A B) (maximalIdeal A) =
      p.map (algebraMap R B)
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A, Ideal.map_map,
      IsScalarTower.algebraMap_eq R A B]
  obtain ⟨hCdomain₀, hCclosed₀⟩ :=
    (hf p).closedFiber_isDomain_and_isIntegrallyClosed p q rfl
  have hCdomain : IsDomain C := by
    change IsDomain (B ⧸ I)
    exact hI ▸ hCdomain₀
  have hCclosed : IsIntegrallyClosed C := by
    change IsIntegrallyClosed (B ⧸ I)
    exact hI ▸ hCclosed₀
  letI : IsDomain C := hCdomain
  letI : IsLocalRing C :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hmax : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B) =
      maximalIdeal C :=
    IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hheight : (maximalIdeal B).height =
      (maximalIdeal A).height + (maximalIdeal C).height := by
    rw [← hmax]
    exact Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (maximalIdeal A) (maximalIdeal B)
  have hBdim : ringKrullDim B ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q]
    exact_mod_cast hqheight
  have hBheight : (maximalIdeal B).height ≤ 1 := by
    have h := hBdim
    rw [← maximalIdeal_height_eq_ringKrullDim] at h
    exact_mod_cast h
  have hAheight : (maximalIdeal A).height ≤ 1 := by
    calc
      (maximalIdeal A).height ≤
          (maximalIdeal A).height + (maximalIdeal C).height := le_add_right le_rfl
      _ = (maximalIdeal B).height := hheight.symm
      _ ≤ 1 := hBheight
  have hCheight : (maximalIdeal C).height ≤ 1 := by
    calc
      (maximalIdeal C).height ≤
          (maximalIdeal A).height + (maximalIdeal C).height := le_add_left le_rfl
      _ = (maximalIdeal B).height := hheight.symm
      _ ≤ 1 := hBheight
  have hAdim : ringKrullDim A ≤ 1 := by
    rw [← maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast hAheight
  have hCdim : ringKrullDim C ≤ 1 := by
    rw [← maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast hCheight
  letI : IsDomain A := IsNormalRing.isDomain_localization p
  letI : IsIntegrallyClosed A := IsNormalRing.isIntegrallyClosed_localization p
  letI : IsRegularLocalRing A :=
    IsIntegrallyClosed.isRegularLocalRing_of_ringKrullDim_le_one hAdim
  letI : IsIntegrallyClosed C := hCclosed
  letI : IsRegularLocalRing C :=
    IsIntegrallyClosed.isRegularLocalRing_of_ringKrullDim_le_one hCdim
  change IsRegularLocalRing B
  exact IsRegularLocalRing.of_flat_of_isRegularLocalRing_quotient (R := A) (S := B)

/-- The two-element form of Serre's condition `(S₂)` ascends along a flat map of
Noetherian rings when the base and all fibers are normal. -/
lemma SerreTwo.of_flat_of_fibers_normal
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    [IsNormalRing R]
    (hf : ∀ (p : Ideal R) [p.IsPrime], IsNormalRing (p.Fiber S)) :
    SerreTwo S := by
  intro q hq hqheight
  letI : q.IsPrime := hq
  let p := q.comap (algebraMap R S)
  letI : p.IsPrime := Ideal.IsPrime.comap (algebraMap R S)
  letI : q.LiesOver p := ⟨rfl⟩
  let A := Localization.AtPrime p
  let B := Localization.AtPrime q
  letI : Algebra A B := Localization.AtPrime.algebraOfLiesOver p q
  letI : Module.Flat A B := Module.Flat.atPrime p q rfl
  letI : Module.FaithfullyFlat A B :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let I := Ideal.map (algebraMap A B) (maximalIdeal A)
  let C := B ⧸ I
  have hI : I = p.map (algebraMap R B) := by
    change Ideal.map (algebraMap A B) (maximalIdeal A) =
      p.map (algebraMap R B)
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p A, Ideal.map_map,
      IsScalarTower.algebraMap_eq R A B]
  obtain ⟨hCdomain₀, hCclosed₀⟩ :=
    (hf p).closedFiber_isDomain_and_isIntegrallyClosed p q rfl
  have hCdomain : IsDomain C := by
    change IsDomain (B ⧸ I)
    exact hI ▸ hCdomain₀
  have hCclosed : IsIntegrallyClosed C := by
    change IsIntegrallyClosed (B ⧸ I)
    exact hI ▸ hCclosed₀
  letI : IsDomain C := hCdomain
  letI : IsLocalRing C :=
    IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  letI : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  letI : IsIntegrallyClosed C := hCclosed
  have hmax : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal B) =
      maximalIdeal C :=
    IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hheight : (maximalIdeal B).height =
      (maximalIdeal A).height + (maximalIdeal C).height := by
    rw [← hmax]
    exact Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (maximalIdeal A) (maximalIdeal B)
  have hBdim : 2 ≤ ringKrullDim B := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q]
    simpa using WithBot.coe_le_coe.mpr hqheight
  have hBheight : 2 ≤ (maximalIdeal B).height := by
    have h := hBdim
    rw [← maximalIdeal_height_eq_ringKrullDim] at h
    exact WithBot.coe_le_coe.mp (by simpa using h)
  letI : IsDomain A := IsNormalRing.isDomain_localization p
  letI : IsIntegrallyClosed A := IsNormalRing.isIntegrallyClosed_localization p
  by_cases hA2 : 2 ≤ (maximalIdeal A).height
  · have hAdim2 : 2 ≤ ringKrullDim A := by
      rw [← maximalIdeal_height_eq_ringKrullDim]
      simpa using WithBot.coe_le_coe.mpr hA2
    obtain ⟨a, b, ha, hb, hab⟩ :=
      IsIntegrallyClosed.exists_regularPair_of_ringKrullDim_ge_two hAdim2
    have habB : RingTheory.Sequence.IsRegular B
        [algebraMap A B a, algebraMap A B b] := by
      simpa using hab.of_faithfullyFlat (S := B)
    have hmap : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B :=
      ((local_hom_TFAE (algebraMap A B)).out 0 2 rfl rfl).mp inferInstance
    exact ⟨algebraMap A B a, algebraMap A B b,
      hmap (Ideal.mem_map_of_mem _ ha), hmap (Ideal.mem_map_of_mem _ hb), habB⟩
  · have hAle : (maximalIdeal A).height ≤ 1 :=
      ENat.lt_two_iff.mp (lt_of_not_ge hA2)
    by_cases hA1 : 1 ≤ (maximalIdeal A).height
    · have hAeq : (maximalIdeal A).height = 1 := le_antisymm hAle hA1
      have hC1 : 1 ≤ (maximalIdeal C).height := by
        by_contra hC1
        have hC0 : (maximalIdeal C).height = 0 :=
          Order.lt_one_iff.mp (lt_of_not_ge hC1)
        have hB1 : (maximalIdeal B).height = 1 := by
          rw [hheight, hAeq, hC0, add_zero]
        have : (2 : ℕ∞) ≤ 1 := hB1 ▸ hBheight
        norm_num at this
      have hAdim : ringKrullDim A ≤ 1 := by
        rw [← maximalIdeal_height_eq_ringKrullDim]
        simpa using WithBot.coe_le_coe.mpr hAle
      letI : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr hAdim
      have hcond : IsIntegrallyClosed A ∧
          ∀ r : Ideal A, r ≠ ⊥ → r.IsPrime → r = maximalIdeal A := by
        refine ⟨inferInstance, fun r hr hprime ↦ ?_⟩
        exact eq_maximalIdeal
          ((Ring.krullDimLE_one_iff_of_isPrime_bot.mp inferInstance) r hr hprime)
      letI : IsPrincipalIdealRing A :=
        ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain A).out 3 0).mp hcond
      obtain ⟨a, ha_span⟩ := IsPrincipalIdealRing.principal (maximalIdeal A)
      have hmAne : maximalIdeal A ≠ ⊥ := by
        intro hm
        rw [hm] at hAeq
        simp at hAeq
      have ha : a ∈ maximalIdeal A := by
        rw [ha_span]
        exact Submodule.subset_span (Set.mem_singleton a)
      have hane : a ≠ 0 := by
        intro ha0
        apply hmAne
        rw [ha_span, ha0]
        simp
      let aa := algebraMap A B a
      have haa : aa ∈ maximalIdeal B := by
        have hmap : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B :=
          ((local_hom_TFAE (algebraMap A B)).out 0 2 rfl rfl).mp inferInstance
        exact hmap (Ideal.mem_map_of_mem _ ha)
      have hregA : RingTheory.Sequence.IsRegular A [a] := by
        letI : Nontrivial (QuotSMulTop a A) :=
          QuotSMulTop.nontrivial_of_mem_maximalIdeal a ha
        rw [RingTheory.Sequence.isRegular_cons_iff A a []]
        exact ⟨IsSMulRegular.of_ne_zero hane,
          RingTheory.Sequence.IsRegular.nil A _⟩
      have hregB : RingTheory.Sequence.IsRegular B [aa] := by
        simpa [aa] using hregA.of_faithfullyFlat (S := B)
      have haaReg : IsSMulRegular B aa :=
        ((RingTheory.Sequence.isRegular_cons_iff B aa []).mp hregB).1
      have hIspan : I = Ideal.span {aa} := by
        change Ideal.map (algebraMap A B) (maximalIdeal A) = Ideal.span {aa}
        rw [ha_span, Ideal.map_span]
        simp [aa]
      have hmCne : maximalIdeal C ≠ ⊥ := by
        intro hm
        rw [hm] at hC1
        simp at hC1
      obtain ⟨c, hc, hcne⟩ := Submodule.ne_bot_iff _ |>.mp hmCne
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
      have hb : b ∈ maximalIdeal B := by
        rw [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk I)]
        exact hc
      exact ⟨aa, b, haa, hb,
        RingTheory.Sequence.IsRegular.pair_of_quotient I hIspan haaReg hb hcne⟩
    · have hA0 : (maximalIdeal A).height = 0 :=
        Order.lt_one_iff.mp (lt_of_not_ge hA1)
      have hC2 : 2 ≤ (maximalIdeal C).height := by
        calc
          2 ≤ (maximalIdeal B).height := hBheight
          _ = (maximalIdeal C).height := by simpa [hA0] using hheight
      have hCdim2 : 2 ≤ ringKrullDim C := by
        rw [← maximalIdeal_height_eq_ringKrullDim]
        simpa using WithBot.coe_le_coe.mpr hC2
      obtain ⟨c, d, hc, hd, hcd⟩ :=
        IsIntegrallyClosed.exists_regularPair_of_ringKrullDim_ge_two hCdim2
      have hmAbot : maximalIdeal A = ⊥ :=
        Ideal.height_eq_zero_iff_eq_bot.mp hA0
      have hIbot : I = ⊥ := by
        change Ideal.map (algebraMap A B) (maximalIdeal A) = ⊥
        rw [hmAbot, Ideal.map_bot]
      let e : C ≃+* B := by
        change (B ⧸ I) ≃+* B
        exact hIbot ▸ RingEquiv.quotientBot B
      have hcdB : RingTheory.Sequence.IsRegular B [e c, e d] := by
        simpa using RingTheory.Sequence.IsRegular.of_semiLinearEquiv
          e e.toSemilinearEquiv hcd
      have hec : e c ∈ maximalIdeal B := by
        rw [← map_ringEquiv_maximalIdeal e]
        exact Ideal.mem_map_of_mem e hc
      have hed : e d ∈ maximalIdeal B := by
        rw [← map_ringEquiv_maximalIdeal e]
        exact Ideal.mem_map_of_mem e hd
      exact ⟨e c, e d, hec, hed, hcdB⟩
