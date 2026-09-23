module

public import StacksAndModuli.API.DVRValuativeCriterion
public import StacksAndModuli.API.KrullAkizuki
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.FinTrdeg
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Localization.AsSubring
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Discrete-valuation factorizations of specializations

This file separates the commutative-algebra input in the noetherian geometry of
discrete valuation rings from the scheme-theoretic construction which uses it.

* `IsLocalRing.DiscreteValuationFactorization` packages a factorization of a map
  from a local ring to a field through a DVR and its fraction field.
* `IsLocalRing.NoetherianValuationFactorization` packages the output one gets
  just before applying the fact that a noetherian non-field valuation ring is a
  DVR.
* `Scheme.Hom.specializationStalkToResidueField` is the canonical local-ring map
  associated to a specialization in the target of a scheme morphism.
* `Scheme.Hom.dvrRealizationOfFactorization` turns a discrete-valuation
  factorization of that map into the valuative square realizing the
  specialization.

The file proves the required factorization by a one-dimensional affine-chart
reduction and Krull--Akizuki.  Consequently a locally finite-type morphism into
a locally noetherian scheme satisfies `DVRRealizesSpecializations`.
-/

@[expose] public section

open CategoryTheory IsLocalRing
open scoped LaurentSeries PowerSeries

namespace IsLocalRing

universe u

/-- A factorization of a homomorphism from a local ring to a field through a
discrete valuation ring and an identified fraction field. -/
structure DiscreteValuationFactorization {A K : Type u} [CommRing A] [IsLocalRing A]
    [Field K] (f : A →+* K) where
  /-- The discrete valuation ring. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [dvr : IsDiscreteValuationRing R]
  /-- A fraction field of `R` receiving the original target field. -/
  L : Type u
  [field : Field L]
  [algebra : Algebra R L]
  [isFractionRing : IsFractionRing R L]
  /-- The local homomorphism from the original local ring to the DVR. -/
  toRing : A →+* R
  isLocalHom : IsLocalHom toRing
  /-- The homomorphism from the original target field to the DVR's fraction
  field. -/
  toFractionField : K →+* L
  /-- The factorization commutes after passage to the fraction field. -/
  comm : (algebraMap R L).comp toRing = toFractionField.comp f

namespace DiscreteValuationFactorization

attribute [instance] commRing domain dvr field algebra isFractionRing

/-- If a map from a local ring to a field has maximal kernel, it factors
through the power-series DVR over that field.  This supplies the constant
DVR realization needed for a reflexive specialization. -/
noncomputable def of_ker_eq_maximal
    {A K : Type u} [CommRing A] [IsLocalRing A] [Field K]
    (f : A →+* K) (hker : RingHom.ker f = maximalIdeal A) :
    DiscreteValuationFactorization f := by
  let toRing : A →+* K⟦X⟧ := PowerSeries.C.comp f
  have hlocal : IsLocalHom toRing := by
    apply ((IsLocalRing.local_hom_TFAE toRing).out 4 0).mp
    ext a
    rw [Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal,
      mem_nonunits_iff, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff]
    simp only [toRing, RingHom.coe_comp, Function.comp_apply,
      PowerSeries.constantCoeff_C]
    change (¬ IsUnit (f a)) ↔ a ∈ maximalIdeal A
    rw [← hker]
    simp [RingHom.mem_ker, isUnit_iff_ne_zero]
  exact
    { R := K⟦X⟧
      L := K⸨X⸩
      toRing := toRing
      isLocalHom := hlocal
      toFractionField := (algebraMap K⟦X⟧ K⸨X⸩).comp PowerSeries.C
      comm := by ext; rfl }

end DiscreteValuationFactorization

/-- A factorization through a noetherian valuation subring of the target field.
For an injective map from a non-field, this is precisely the input needed to
obtain a `DiscreteValuationFactorization` with unchanged target field. -/
structure NoetherianValuationFactorization {A K : Type u} [CommRing A]
    [IsLocalRing A] [Field K] (f : A →+* K) where
  /-- The valuation subring of the target field. -/
  V : ValuationSubring K
  /-- The image of the original local ring lies in `V`. -/
  map_mem : ∀ a, f a ∈ V
  /-- The induced map to `V` is local. -/
  isLocalHom : IsLocalHom (f.codRestrict V.toSubring map_mem)
  /-- The chosen valuation subring is noetherian. -/
  isNoetherianRing : IsNoetherianRing V

namespace NoetherianValuationFactorization

/-- A noetherian valuation factor which is not a field is a DVR factor.  The
only non-formal step is Mathlib's DVR TFAE: a noetherian local domain which is
a valuation ring and is not a field is a DVR. -/
noncomputable def toDiscreteValuationFactorization
    {A K : Type u} [CommRing A] [IsLocalRing A] [Field K] {f : A →+* K}
    (D : NoetherianValuationFactorization f) (hV : ¬ IsField D.V) :
    DiscreteValuationFactorization f := by
  letI : IsNoetherianRing D.V := D.isNoetherianRing
  let toRing : A →+* D.V := f.codRestrict D.V.toSubring D.map_mem
  letI : IsLocalHom toRing := D.isLocalHom
  letI : IsDiscreteValuationRing D.V :=
    ((IsDiscreteValuationRing.TFAE D.V hV).out 1 0).mp
      (inferInstance : ValuationRing D.V)
  exact
    { R := D.V
      L := K
      toRing := toRing
      isLocalHom := inferInstance
      toFractionField := RingHom.id K
      comm := by ext; rfl }

/-- For an injective map from a non-field, the valuation factor is automatically
not a field, so a noetherian valuation factor is a DVR factor. -/
noncomputable def toDiscreteValuationFactorizationOfInjective
    {A K : Type u} [CommRing A] [IsLocalRing A] [Field K] {f : A →+* K}
    (D : NoetherianValuationFactorization f) (hf : Function.Injective f)
    (hA : ¬ IsField A) : DiscreteValuationFactorization f := by
  let toRing : A →+* D.V := f.codRestrict D.V.toSubring D.map_mem
  letI : IsLocalHom toRing := D.isLocalHom
  have htoRing : Function.Injective toRing := by
    intro a b hab
    apply hf
    exact congrArg Subtype.val hab
  exact D.toDiscreteValuationFactorization
    (fun h ↦ hA (IsLocalHom.isField htoRing h))

/-- Existence form of
`NoetherianValuationFactorization.toDiscreteValuationFactorizationOfInjective`. -/
theorem exists_discreteValuationFactorization
    {A K : Type u} [CommRing A] [IsLocalRing A] [Field K] {f : A →+* K}
    (hf : Function.Injective f) (hA : ¬ IsField A)
    (h : Nonempty (NoetherianValuationFactorization f)) :
    Nonempty (DiscreteValuationFactorization f) :=
  h.map fun D ↦ D.toDiscreteValuationFactorizationOfInjective hf hA

end NoetherianValuationFactorization

/-- A local-ring map to a field admits a noetherian valuation factor which is
not itself a field.  Krull--Akizuki supplies this property for the local maps
arising from nontrivial specializations in Proposition A.4.4. -/
def AdmitsNonfieldNoetherianValuationFactorization
    {A K : Type u} [CommRing A] [IsLocalRing A] [Field K] (f : A →+* K) : Prop :=
  ∃ D : NoetherianValuationFactorization f, ¬ IsField D.V

/-- A non-field noetherian valuation factor yields a discrete-valuation
factorization. -/
theorem exists_discreteValuationFactorization_of_admitsNonfieldNoetherian
    {A K : Type u} [CommRing A] [IsLocalRing A] [Field K] {f : A →+* K}
    (h : AdmitsNonfieldNoetherianValuationFactorization f) :
    Nonempty (DiscreteValuationFactorization f) := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D.toDiscreteValuationFactorization hD⟩

/-- If `K` is a fraction field of `A` and a field `E` is generated over `K`
by `S`, then `E` is a fraction field of the `A`-algebra generated by `S`.
This is the denominator-clearing step used when passing from a finite
transcendence basis to a noetherian affine model. -/
theorem isFractionRing_adjoin_of_intermediateField_adjoin_eq_top
    (A K E : Type u) [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    (S : Set E) (hS : IntermediateField.adjoin K S = ⊤) :
    IsFractionRing (Algebra.adjoin A S) E := by
  classical
  let B := Algebra.adjoin A S
  have hinjAE : Function.Injective (algebraMap A E) := by
    intro a b hab
    apply IsFractionRing.injective A K
    apply (algebraMap K E).injective
    simpa only [IsScalarTower.algebraMap_apply A K E] using hab
  apply IsFractionRing.of_field B E
  have hrep (x : E) (hx : x ∈ Algebra.adjoin K S) :
      ∃ p q : B, (q : E) ≠ 0 ∧ x = (p : E) / (q : E) := by
    apply Algebra.adjoin_induction (R := K) (A := E) (s := S) (p := fun x _ ↦
      ∃ p q : B, (q : E) ≠ 0 ∧ x = (p : E) / (q : E))
    · intro x hx
      exact ⟨⟨x, Algebra.subset_adjoin hx⟩, 1, one_ne_zero, by simp⟩
    · intro k
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A k
      refine ⟨algebraMap A B a, algebraMap A B b, ?_, ?_⟩
      · exact (map_ne_zero_iff _ hinjAE).mpr
          (nonZeroDivisors.ne_zero hb)
      · have he := congrArg (algebraMap K E) hab
        change algebraMap K E k = algebraMap A E a / algebraMap A E b
        calc
          _ = algebraMap K E (algebraMap A K a / algebraMap A K b) := he.symm
          _ = algebraMap K E (algebraMap A K a) /
              algebraMap K E (algebraMap A K b) := map_div₀ _ _ _
          _ = _ := by rw [← IsScalarTower.algebraMap_apply A K E,
            ← IsScalarTower.algebraMap_apply A K E]
    · intro x y hx hy
      rintro ⟨px, qx, hqx, ex⟩ ⟨py, qy, hqy, ey⟩
      refine ⟨px * qy + py * qx, qx * qy, mul_ne_zero hqx hqy, ?_⟩
      rw [ex, ey]
      change (px : E) / qx + (py : E) / qy =
        ((px : E) * qy + py * qx) / (qx * qy)
      simpa only [mul_comm (py : E) qx] using div_add_div (px : E) py hqx hqy
    · intro x y hx hy
      rintro ⟨px, qx, hqx, ex⟩ ⟨py, qy, hqy, ey⟩
      refine ⟨px * py, qx * qy, mul_ne_zero hqx hqy, ?_⟩
      rw [ex, ey]
      change (px : E) / qx * ((py : E) / qy) =
        ((px : E) * py) / (qx * qy)
      exact div_mul_div_comm (px : E) qx py qy
    exact hx
  intro z
  have hz : z ∈ IntermediateField.adjoin K S := by rw [hS]; trivial
  obtain ⟨r, hr, s, hs, ez⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  by_cases hs0 : s = 0
  · refine ⟨0, 1, ?_⟩
    rw [ez, hs0]
    simp
  obtain ⟨pr, qr, hqr, er⟩ := hrep r hr
  obtain ⟨ps, qs, hqs, es⟩ := hrep s hs
  have hps : (ps : E) ≠ 0 := by
    intro hps
    apply hs0
    rw [es, hps]
    simp
  refine ⟨pr * qs, qr * ps, ?_⟩
  rw [ez, er, es]
  change ((pr : E) / qr) / ((ps : E) / qs) =
    ((pr : E) * qs) / (qr * ps)
  exact div_div_div_eq (pr : E) qr ps qs

/-- A noetherian one-dimensional local overring of a local domain inside its
fraction field.  The structure records compatibility with both the original
local ring and the chosen fraction field. -/
structure OneDimensionalLocalOverring
    (A K : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] where
  /-- The one-dimensional local overring. -/
  R : Type u
  [commRing : CommRing R]
  [domain : IsDomain R]
  [localRing : IsLocalRing R]
  [noetherian : IsNoetherianRing R]
  [dimensionLEOne : Ring.DimensionLEOne R]
  [algebraBase : Algebra A R]
  [algebraFraction : Algebra R K]
  [tower : IsScalarTower A R K]
  [fractionRing : IsFractionRing R K]
  /-- The original local ring is dominated by the overring. -/
  isLocalHom : IsLocalHom (algebraMap A R)

namespace OneDimensionalLocalOverring

attribute [instance] commRing domain localRing noetherian dimensionLEOne
  algebraBase algebraFraction tower fractionRing

end OneDimensionalLocalOverring

/-- Every non-field noetherian local domain has a noetherian one-dimensional
local overring inside the same fraction field.

The construction is the affine-chart form of the blow-up argument.  Choose a
valuation overring dominating `A`, select among finitely many generators of the
maximal ideal one having maximal valuation, adjoin all ratios by that generator,
and localize at a prime minimal over the resulting principal ideal.  Krull's
principal ideal theorem bounds the dimension of that localization by one. -/
theorem exists_oneDimensionalLocalOverring
    (A K : Type u) [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    (hA : ¬ IsField A) : Nonempty (OneDimensionalLocalOverring A K) := by
  classical
  obtain ⟨V, hVmem, hVlocal⟩ :=
    IsLocalRing.exists_factor_valuationRing (algebraMap A K)
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing (maximalIdeal A))
  have hm0 : maximalIdeal A ≠ ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hA
  have hn : n ≠ 0 := by
    intro hn
    subst n
    apply hm0
    rw [← hs, Set.range_eq_empty, Submodule.span_empty]
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ
    (fun i ↦ V.valuation (algebraMap A K (s i))) Finset.univ_nonempty
  have hsne : ∃ i, s i ≠ 0 := by
    by_contra h
    push Not at h
    have hs0 : s = 0 := funext h
    subst s
    apply hm0
    rw [← hs]
    simp
  let a := s i₀
  have ha : a ≠ 0 := by
    obtain ⟨i, hi⟩ := hsne
    intro ha
    have hval_ne : V.valuation (algebraMap A K (s i)) ≠ 0 :=
      (V.valuation.ne_zero_iff).mpr ((map_ne_zero_iff _
        (IsFractionRing.injective A K)).mpr hi)
    have hle := hi₀ i (Finset.mem_univ i)
    have hva0 : V.valuation (algebraMap A K a) = 0 := by
      rw [ha, map_zero, V.valuation.map_zero]
    rw [hva0] at hle
    exact hval_ne (bot_unique hle)
  have haK : algebraMap A K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha
  let ratios : Fin n → K := fun i ↦
    algebraMap A K (s i) / algebraMap A K a
  have hratios (i : Fin n) : ratios i ∈ V := by
    obtain ⟨c, hc⟩ := (V.valuation_le_iff
      (algebraMap A K (s i)) (algebraMap A K a)).mp
        (hi₀ i (Finset.mem_univ i))
    have heq : ratios i = (c : K) := by
      apply (div_eq_iff haK).mpr
      exact hc.symm
    rw [heq]
    exact c.property
  let B := Algebra.adjoin A (Set.range ratios)
  letI : Algebra.FiniteType A B :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range ratios)
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hBmem (z : B) : (z : K) ∈ V := by
    apply Algebra.adjoin_induction (p := fun x _ ↦ x ∈ V)
      (fun _ hx ↦ ?_) (fun r ↦ hVmem r)
      (fun x y _ _ hx hy ↦ V.add_mem x y hx hy)
      (fun x y _ _ hx hy ↦ V.mul_mem x y hx hy) z.property
    obtain ⟨i, rfl⟩ := hx
    exact hratios i
  let g : A →+* V := (algebraMap A K).codRestrict V.toSubring hVmem
  letI : IsLocalHom g := hVlocal
  let j : B →+* V := B.val.toRingHom.codRestrict V.toSubring hBmem
  have ha_mem : a ∈ maximalIdeal A := by
    rw [← hs]
    exact Submodule.subset_span ⟨i₀, rfl⟩
  have ha_nonunit : ¬ IsUnit a :=
    (IsLocalRing.mem_maximalIdeal a).mp ha_mem
  let aB : B := algebraMap A B a
  have haB_nonunit : ¬ IsUnit aB := by
    intro haB_unit
    have hja : j aB = g a := rfl
    have hga_unit : IsUnit (g a) := hja ▸ haB_unit.map j
    exact ha_nonunit (IsUnit.of_map g a hga_unit)
  let rB : Fin n → B := fun i ↦
    ⟨ratios i, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  have hmul (i : Fin n) : rB i * aB = algebraMap A B (s i) := by
    apply Subtype.ext
    change ratios i * algebraMap A K a = algebraMap A K (s i)
    exact div_mul_cancel₀ _ haK
  let J : Ideal B := Ideal.map (algebraMap A B) (maximalIdeal A)
  have hJ : J = Ideal.span {aB} := by
    apply le_antisymm
    · rw [show J = Ideal.span (Set.range fun i ↦ algebraMap A B (s i)) by
        dsimp only [J]
        rw [← hs, Ideal.map_span]
        congr 1
        ext z
        simp]
      rw [Ideal.span_le]
      rintro z ⟨i, rfl⟩
      exact Ideal.mem_span_singleton'.mpr ⟨rB i, hmul i⟩
    · rw [Ideal.span_singleton_le_iff_mem]
      dsimp only [aB]
      apply Ideal.mem_map_of_mem
      exact ha_mem
  have hspan_ne_top : Ideal.span {aB} ≠ ⊤ := by
    intro htop
    exact haB_nonunit (Ideal.span_singleton_eq_top.mp htop)
  obtain ⟨P, hP⟩ := Ideal.nonempty_minimalPrimes hspan_ne_top
  letI : P.IsPrime := hP.isPrime
  have hheight : P.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
  let C := Localization.subalgebra.ofField K P.primeCompl
    P.primeCompl_le_nonZeroDivisors
  letI : IsLocalization P.primeCompl C :=
    Localization.subalgebra.isLocalization_ofField K P.primeCompl
      P.primeCompl_le_nonZeroDivisors
  letI : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C P
  letI : IsNoetherianRing C :=
    IsLocalization.isNoetherianRing P.primeCompl C (inferInstance : IsNoetherianRing B)
  letI : Ring.KrullDimLE 1 C := by
    constructor
    change ringKrullDim C ≤ 1
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P C]
    exact_mod_cast hheight
  letI : Ring.DimensionLEOne C :=
    { maximalOfPrime := fun hne hp ↦ hp.isMaximal_of_ne_bot hne }
  letI : Algebra A C := RingHom.toAlgebra
    ((algebraMap B C).comp (algebraMap A B))
  letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A C K := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap A K x = algebraMap B K (algebraMap A B x)
    rw [IsScalarTower.algebraMap_apply A B K])
  have hm_le : maximalIdeal A ≤ Ideal.comap (algebraMap A B) P := by
    rw [← Ideal.map_le_iff_le_comap]
    change J ≤ P
    rw [hJ]
    exact hP.le
  have hcomap : Ideal.comap (algebraMap A B) P = maximalIdeal A := by
    apply le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ hP.isPrime.ne_top))
    exact hm_le
  have hlocalAC : IsLocalHom (algebraMap A C) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap A C)).out 4 0).mp
    ext x
    change algebraMap A C x ∈ maximalIdeal C ↔ x ∈ maximalIdeal A
    rw [IsScalarTower.algebraMap_apply A B C,
      IsLocalization.AtPrime.to_map_mem_maximal_iff C P]
    change x ∈ Ideal.comap (algebraMap A B) P ↔ x ∈ maximalIdeal A
    rw [hcomap]
  exact ⟨{ R := C, isLocalHom := hlocalAC }⟩

/-- If the integral closure in a finite fraction-field extension is noetherian,
then a one-dimensional local domain admits the required non-field noetherian
valuation factor.  This is the precise post-Krull--Akizuki step: no separability
or normality hypothesis on the original domain is needed. -/
theorem admitsNonfieldNoetherianValuationFactorization_of_integralClosure_isNoetherian
    {A K L : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
    [Ring.DimensionLEOne A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    (hA : ¬ IsField A)
    (hC : IsNoetherianRing (integralClosure A L)) :
    AdmitsNonfieldNoetherianValuationFactorization (algebraMap A L) := by
  let C := integralClosure A L
  letI : IsNoetherianRing C := hC
  letI : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
  letI : IsIntegrallyClosed C := integralClosure.isIntegrallyClosedOfFiniteExtension K
  letI : IsDedekindDomain C := (isDedekindDomain_iff (A := C) L).mpr
    ⟨inferInstance, inferInstance, inferInstance,
      (isIntegrallyClosed_iff L).mp (inferInstance : IsIntegrallyClosed C)⟩
  have hinjAL : Function.Injective (algebraMap A L) := by
    intro a b hab
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    simpa only [IsScalarTower.algebraMap_apply A K L] using hab
  have hinjAC : Function.Injective (algebraMap A C) := by
    intro a b hab
    apply hinjAL
    simpa only [IsScalarTower.algebraMap_apply A C L] using
      congrArg (algebraMap C L) hab
  letI : FaithfulSMul A C :=
    (faithfulSMul_iff_algebraMap_injective A C).mpr hinjAC
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := C) (maximalIdeal A)
  letI : P.IsMaximal := hPmax
  letI : P.IsPrime := hPmax.isPrime
  letI : P.LiesOver (maximalIdeal A) := hPover
  have hm0 : maximalIdeal A ≠ ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hA
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hm0 P
  let v : IsDedekindDomain.HeightOneSpectrum C := ⟨P, inferInstance, hP0⟩
  let V : ValuationSubring L := v.valuationSubringAtPrime L
  letI : Algebra C V := by dsimp [V]; infer_instance
  letI : IsScalarTower C V L := by dsimp [V]; infer_instance
  letI : IsLocalization v.asIdeal.primeCompl V := by
    dsimp [V, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime]
    exact Localization.subalgebra.isLocalization_ofField L v.asIdeal.primeCompl
      v.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsDedekindDomain V := by dsimp [V]; infer_instance
  have hcompat (a : A) :
      algebraMap A L a = ((algebraMap C V (algebraMap A C a) : V) : L) := by
    rw [IsScalarTower.algebraMap_apply A C L,
      IsScalarTower.algebraMap_apply C V L, ValuationSubring.algebraMap_apply]
  have hmem : ∀ a : A, algebraMap A L a ∈ V := by
    intro a
    rw [hcompat a]
    exact (algebraMap C V (algebraMap A C a)).property
  let g : A →+* V := (algebraMap A L).codRestrict V.toSubring hmem
  have hg : IsLocalHom g := by
    apply ((IsLocalRing.local_hom_TFAE g).out 4 0).mp
    ext a
    change g a ∈ maximalIdeal V ↔ a ∈ maximalIdeal A
    have hga : g a = algebraMap C V (algebraMap A C a) := by
      apply Subtype.ext
      exact hcompat a
    rw [hga, IsLocalization.AtPrime.to_map_mem_maximal_iff V v.asIdeal]
    exact (P.mem_of_liesOver (maximalIdeal A) a).symm
  let D : NoetherianValuationFactorization (algebraMap A L) :=
    { V := V
      map_mem := hmem
      isLocalHom := hg
      isNoetherianRing := inferInstance }
  refine ⟨D, ?_⟩
  exact IsLocalization.AtPrime.not_isField C hP0 V

/-- The post-Krull--Akizuki factorization under the stronger hypothesis that
the integral closure is module-finite.  This applies to finite normalization
settings, but that finiteness is unavailable for arbitrary noetherian domains. -/
theorem admitsNonfieldNoetherianValuationFactorization_of_finite_integralClosure
    {A K L : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsNoetherianRing A] [Ring.DimensionLEOne A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Module.Finite A (integralClosure A L)]
    (hA : ¬ IsField A) :
    AdmitsNonfieldNoetherianValuationFactorization (algebraMap A L) :=
  admitsNonfieldNoetherianValuationFactorization_of_integralClosure_isNoetherian
    (A := A) (K := K) (L := L) hA
      (IsNoetherianRing.of_finite A (integralClosure A L))

/-- The exact Krull--Akizuki finite-length input needed for the general
one-dimensional factorization.  Stacks Project tag 00PF supplies precisely the
hypothesis below for the integral closure viewed inside the finite-dimensional
`K`-vector space `L`. -/
theorem admitsNonfieldNoetherianValuationFactorization_of_finiteLength_quotients
    {A K L : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
    [Ring.DimensionLEOne A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    (hA : ¬ IsField A)
    (hfiniteLength : ∀ (x : A), x ≠ 0 →
      IsFiniteLength A (QuotSMulTop x (integralClosure A L))) :
    AdmitsNonfieldNoetherianValuationFactorization (algebraMap A L) := by
  have hC : IsNoetherianRing (integralClosure A L) :=
    IsNoetherianRing.of_finiteLength_quotients_of_isAlgebraic fun x hx ↦
      IsFiniteLength.idealQuotient_span_algebraMap x (hfiniteLength x hx)
  exact
    admitsNonfieldNoetherianValuationFactorization_of_integralClosure_isNoetherian
      (A := A) (K := K) (L := L) hA hC

/-- Krull--Akizuki gives the noetherian non-field valuation factor for every
finite extension of the fraction field of a one-dimensional noetherian local
domain.

Stacks Project tag 00PE, formalized as
`isFiniteLength_quotSMulTop_of_submodule_fractionField`, supplies the formerly
missing finite-length hypothesis for the integral closure, viewed as an
arbitrary `A`-submodule of the finite-dimensional `K`-vector space `L`. -/
theorem admitsNonfieldNoetherianValuationFactorization_of_krullAkizuki
    {A K L : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsNoetherianRing A] [Ring.DimensionLEOne A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    (hA : ¬ IsField A) :
    AdmitsNonfieldNoetherianValuationFactorization (algebraMap A L) := by
  apply
    admitsNonfieldNoetherianValuationFactorization_of_finiteLength_quotients
      (A := A) (K := K) (L := L) hA
  intro x hx
  have hx' : x ∈ nonZeroDivisors A :=
    mem_nonZeroDivisors_iff_ne_zero.mpr hx
  have hsub :=
    isFiniteLength_quotSMulTop_of_submodule_fractionField
      (R := A) (K := K) (V := L)
      (integralClosure A L).toSubmodule hx'
  exact (QuotSMulTop.congr x
    (integralClosure A L).toSubmoduleEquiv).isFiniteLength hsub

/-- A finite extension of the fraction field of a non-field one-dimensional
noetherian local domain admits a discrete-valuation factorization. -/
theorem exists_discreteValuationFactorization_of_krullAkizuki
    {A K L : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsNoetherianRing A] [Ring.DimensionLEOne A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L]
    (hA : ¬ IsField A) :
    Nonempty (DiscreteValuationFactorization (algebraMap A L)) :=
  exists_discreteValuationFactorization_of_admitsNonfieldNoetherian
    (admitsNonfieldNoetherianValuationFactorization_of_krullAkizuki
      (A := A) (K := K) (L := L) hA)

/-- A finite extension of the fraction field of an arbitrary non-field
noetherian local domain admits a non-field noetherian valuation factorization.

The one-dimensional local overring supplied by
`exists_oneDimensionalLocalOverring` reduces this to Krull--Akizuki. -/
theorem admitsNonfieldNoetherianValuationFactorization_of_finiteExtension
    {A K L : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] (hA : ¬ IsField A) :
    AdmitsNonfieldNoetherianValuationFactorization (algebraMap A L) := by
  classical
  obtain ⟨O⟩ := exists_oneDimensionalLocalOverring A K hA
  letI : Algebra O.R L := RingHom.toAlgebra
    ((algebraMap K L).comp (algebraMap O.R K))
  letI : IsScalarTower O.R K L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A O.R L := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap A L x = algebraMap K L
      (algebraMap O.R K (algebraMap A O.R x))
    rw [IsScalarTower.algebraMap_apply A K L,
      IsScalarTower.algebraMap_apply A O.R K])
  have hinj : Function.Injective (algebraMap A O.R) := by
    intro x y hxy
    apply IsFractionRing.injective A K
    simpa only [IsScalarTower.algebraMap_apply A O.R K] using
      congrArg (algebraMap O.R K) hxy
  have hO : ¬ IsField O.R := fun hfield ↦
    hA (@IsLocalHom.isField A O.R _ _ _ _ _ (algebraMap A O.R)
      O.isLocalHom hinj hfield)
  obtain ⟨D, hD⟩ :=
    admitsNonfieldNoetherianValuationFactorization_of_krullAkizuki
      (A := O.R) (K := K) (L := L) hO
  have hmem : ∀ a : A, algebraMap A L a ∈ D.V := by
    intro a
    rw [IsScalarTower.algebraMap_apply A O.R L]
    exact D.map_mem (algebraMap A O.R a)
  let gR : O.R →+* D.V :=
    (algebraMap O.R L).codRestrict D.V.toSubring D.map_mem
  let gA : A →+* D.V :=
    (algebraMap A L).codRestrict D.V.toSubring hmem
  have hg_eq : gA = gR.comp (algebraMap A O.R) := by
    ext a
    exact IsScalarTower.algebraMap_apply A O.R L a
  have hlocal : IsLocalHom gA := by
    rw [hg_eq]
    letI : IsLocalHom gR := D.isLocalHom
    letI : IsLocalHom (algebraMap A O.R) := O.isLocalHom
    exact RingHom.isLocalHom_comp gR (algebraMap A O.R)
  let E : NoetherianValuationFactorization (algebraMap A L) :=
    { V := D.V
      map_mem := hmem
      isLocalHom := hlocal
      isNoetherianRing := D.isNoetherianRing }
  exact ⟨E, hD⟩

/-- A finite extension of the fraction field of an arbitrary non-field
noetherian local domain admits a discrete-valuation factorization. -/
theorem exists_discreteValuationFactorization_of_finiteExtension
    {A K L : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] (hA : ¬ IsField A) :
    Nonempty (DiscreteValuationFactorization (algebraMap A L)) :=
  exists_discreteValuationFactorization_of_admitsNonfieldNoetherian
    (admitsNonfieldNoetherianValuationFactorization_of_finiteExtension
      (A := A) (K := K) (L := L) hA)

set_option maxHeartbeats 800000 in
-- Elaborating the nested transcendence-basis and localization models exceeds the default budget.
/-- Every finitely generated extension of the fraction field of a non-field
noetherian local domain admits a non-field noetherian valuation factorization.

Here finite generation of fields is expressed by `Algebra.EssFiniteType`.
Choose a finite transcendence basis and replace each basis element by its
inverse when necessary so that it lies in a valuation ring dominating `A`.
The resulting finite-type affine model is noetherian and has the purely
transcendental intermediate field as fraction field.  Its localization at the
valuation center is local, and the remaining field extension is finite, so
`admitsNonfieldNoetherianValuationFactorization_of_finiteExtension` applies. -/
theorem admitsNonfieldNoetherianValuationFactorization_of_essFiniteType
    {A K L : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra.EssFiniteType K L] (hA : ¬ IsField A) :
    AdmitsNonfieldNoetherianValuationFactorization (algebraMap A L) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis K L
  let x : s → L := fun i ↦ i
  let E := IntermediateField.adjoin K (Set.range x)
  letI : Algebra A E := RingHom.toAlgebra
    ((algebraMap K E).comp (algebraMap A K))
  letI : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A E L := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap A L a = algebraMap K L (algebraMap A K a)
    rw [IsScalarTower.algebraMap_apply A K L])
  letI : Algebra.IsAlgebraic E L := by
    dsimp only [E, x]
    exact hs.isAlgebraic_field
  letI : Algebra.EssFiniteType E L := Algebra.EssFiniteType.of_comp K E L
  letI : Module.Finite E L :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  obtain ⟨V, hVmem, hVlocal⟩ :=
    IsLocalRing.exists_factor_valuationRing (algebraMap A E)
  let xE : s → E := fun i ↦
    ⟨x i, IntermediateField.subset_adjoin K (Set.range x) ⟨i, rfl⟩⟩
  have hxE_top : IntermediateField.adjoin K (Set.range xE) = ⊤ := by
    apply E.lift_injective
    rw [IntermediateField.lift_top,
      IntermediateField.lift_adjoin]
    change IntermediateField.adjoin K (Subtype.val '' Set.range xE) = E
    change IntermediateField.adjoin K (Subtype.val '' Set.range xE) =
      IntermediateField.adjoin K (Set.range x)
    congr 1
    ext z
    constructor
    · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨xE i, ⟨i, rfl⟩, rfl⟩
  let t : s → E := fun i ↦ if xE i ∈ V then xE i else (xE i)⁻¹
  have htV (i : s) : t i ∈ V := by
    by_cases hi : xE i ∈ V
    · simpa only [t, hi, ↓reduceIte] using hi
    · simpa only [t, hi, ↓reduceIte] using (V.mem_or_inv_mem (xE i)).resolve_left hi
  have ht_top : IntermediateField.adjoin K (Set.range t) = ⊤ := by
    apply top_unique
    rw [← hxE_top]
    rw [IntermediateField.adjoin_le_iff]
    rintro z ⟨i, rfl⟩
    by_cases hi : xE i ∈ V
    · have hi' : t i ∈ IntermediateField.adjoin K (Set.range t) :=
        IntermediateField.subset_adjoin K (Set.range t) ⟨i, rfl⟩
      have hit : t i = xE i := by simp only [t, hi, ↓reduceIte]
      rw [← hit]
      exact hi'
    · have hi' : t i ∈ IntermediateField.adjoin K (Set.range t) :=
        IntermediateField.subset_adjoin K (Set.range t) ⟨i, rfl⟩
      have hit : (t i)⁻¹ = xE i := by simp only [t, hi, ↓reduceIte, inv_inv]
      rw [← hit]
      exact IntermediateField.inv_mem _ hi'
  let B := Algebra.adjoin A (Set.range t)
  letI : Algebra.FiniteType A B :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range t)
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  letI : IsFractionRing B E :=
    isFractionRing_adjoin_of_intermediateField_adjoin_eq_top A K E
      (Set.range t) ht_top
  have hBmem (z : B) : (z : E) ∈ V := by
    apply Algebra.adjoin_induction (p := fun x _ ↦ x ∈ V)
      (fun _ hz ↦ ?_) (fun a ↦ hVmem a)
      (fun a b _ _ ha hb ↦ V.add_mem a b ha hb)
      (fun a b _ _ ha hb ↦ V.mul_mem a b ha hb) z.property
    obtain ⟨i, rfl⟩ := hz
    exact htV i
  let g : A →+* V := (algebraMap A E).codRestrict V.toSubring hVmem
  let j : B →+* V := B.val.toRingHom.codRestrict V.toSubring hBmem
  let P : Ideal B := Ideal.comap j (maximalIdeal V)
  letI : P.IsPrime := Ideal.IsPrime.comap j
  have hPcomap : Ideal.comap (algebraMap A B) P = maximalIdeal A := by
    rw [show Ideal.comap (algebraMap A B) P =
        Ideal.comap g (maximalIdeal V) by
      ext a
      change j (algebraMap A B a) ∈ maximalIdeal V ↔ g a ∈ maximalIdeal V
      rfl]
    exact ((IsLocalRing.local_hom_TFAE g).out 0 4).mp hVlocal
  let C := Localization.subalgebra.ofField E P.primeCompl
    P.primeCompl_le_nonZeroDivisors
  letI : IsLocalization P.primeCompl C :=
    Localization.subalgebra.isLocalization_ofField E P.primeCompl
      P.primeCompl_le_nonZeroDivisors
  letI : IsLocalRing C := IsLocalization.AtPrime.isLocalRing C P
  letI : IsNoetherianRing C :=
    IsLocalization.isNoetherianRing P.primeCompl C (inferInstance : IsNoetherianRing B)
  letI : Algebra A C := RingHom.toAlgebra
    ((algebraMap B C).comp (algebraMap A B))
  letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower B C E := IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  letI : IsScalarTower A C E := IsScalarTower.of_algebraMap_eq' (by ext; rfl)
  have hlocalAC : IsLocalHom (algebraMap A C) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap A C)).out 4 0).mp
    ext a
    change algebraMap A C a ∈ maximalIdeal C ↔ a ∈ maximalIdeal A
    rw [IsScalarTower.algebraMap_apply A B C,
      IsLocalization.AtPrime.to_map_mem_maximal_iff C P]
    change a ∈ Ideal.comap (algebraMap A B) P ↔ a ∈ maximalIdeal A
    rw [hPcomap]
  have hinjAC : Function.Injective (algebraMap A C) := by
    intro a b hab
    apply IsFractionRing.injective A K
    apply (algebraMap K E).injective
    rw [← IsScalarTower.algebraMap_apply A K E,
      ← IsScalarTower.algebraMap_apply A K E]
    simpa only [IsScalarTower.algebraMap_apply A C E] using
      congrArg (algebraMap C E) hab
  have hC : ¬ IsField C := fun hfield ↦
    hA (@IsLocalHom.isField A C _ _ _ _ _ (algebraMap A C)
      hlocalAC hinjAC hfield)
  letI : Algebra C L := RingHom.toAlgebra
    ((algebraMap E L).comp (algebraMap C E))
  letI : IsScalarTower C E L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A C L := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change algebraMap A L a = algebraMap E L
      (algebraMap C E (algebraMap A C a))
    rw [IsScalarTower.algebraMap_apply A E L,
      IsScalarTower.algebraMap_apply A C E])
  have hcompatACL (a : A) :
      algebraMap A L a = algebraMap C L (algebraMap A C a) := by
    change algebraMap A L a = algebraMap E L
      (algebraMap C E (algebraMap A C a))
    rw [IsScalarTower.algebraMap_apply A E L,
      IsScalarTower.algebraMap_apply A C E]
  have htowerCEL : IsScalarTower C E L := by exact inferInstance
  obtain ⟨D, hD⟩ :=
    @admitsNonfieldNoetherianValuationFactorization_of_finiteExtension
      C E L inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      htowerCEL inferInstance hC
  have hmem : ∀ a : A, algebraMap A L a ∈ D.V := by
    intro a
    rw [hcompatACL]
    exact D.map_mem (algebraMap A C a)
  let gC : C →+* D.V :=
    (algebraMap C L).codRestrict D.V.toSubring D.map_mem
  let gA : A →+* D.V :=
    (algebraMap A L).codRestrict D.V.toSubring hmem
  have hg_eq : gA = gC.comp (algebraMap A C) := by
    ext a
    exact hcompatACL a
  have hlocal : IsLocalHom gA := by
    rw [hg_eq]
    letI : IsLocalHom gC := D.isLocalHom
    letI : IsLocalHom (algebraMap A C) := hlocalAC
    exact RingHom.isLocalHom_comp gC (algebraMap A C)
  let D' : NoetherianValuationFactorization (algebraMap A L) :=
    { V := D.V
      map_mem := hmem
      isLocalHom := hlocal
      isNoetherianRing := D.isNoetherianRing }
  exact ⟨D', hD⟩

/-- Every finitely generated extension of the fraction field of a non-field
noetherian local domain admits a discrete-valuation factorization. -/
theorem exists_discreteValuationFactorization_of_essFiniteType
    {A K L : Type u} [CommRing A] [IsLocalRing A] [IsDomain A]
    [IsNoetherianRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra.EssFiniteType K L] (hA : ¬ IsField A) :
    Nonempty (DiscreteValuationFactorization (algebraMap A L)) :=
  exists_discreteValuationFactorization_of_admitsNonfieldNoetherian
    (admitsNonfieldNoetherianValuationFactorization_of_essFiniteType
      (A := A) (K := K) (L := L) hA)

set_option maxHeartbeats 400000 in
-- Quotienting by the kernel and reconstructing the factorization needs extra elaboration time.
/-- A finite-type map from a noetherian local ring to a field admits a
non-field noetherian valuation factor whenever its kernel is not the maximal
ideal.  Passing to the quotient by the kernel reduces this to the domain case
of `admitsNonfieldNoetherianValuationFactorization_of_essFiniteType`. -/
theorem admitsNonfieldNoetherianValuationFactorization_of_essFiniteType_of_ker_ne_maximal
    {A L : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Field L] (f : A →+* L) (hf : f.EssFiniteType)
    (hker : RingHom.ker f ≠ maximalIdeal A) :
    AdmitsNonfieldNoetherianValuationFactorization f := by
  classical
  let I := RingHom.ker f
  letI : I.IsPrime := RingHom.ker_isPrime f
  let B := A ⧸ I
  let q : A →+* B := Ideal.Quotient.mk I
  letI : IsLocalRing B := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  letI : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  let g : B →+* L := RingHom.kerLift f
  have hg_inj : Function.Injective g := RingHom.kerLift_injective f
  letI : Algebra B L := RingHom.toAlgebra g
  letI : FaithfulSMul B L :=
    (faithfulSMul_iff_algebraMap_injective B L).mpr hg_inj
  have hgft : g.EssFiniteType := by
    apply RingHom.EssFiniteType.of_comp q
    rw [show g.comp q = f by ext a; exact RingHom.kerLift_mk f a]
    exact hf
  letI : Algebra.EssFiniteType B L :=
    RingHom.essFiniteType_algebraMap.mp hgft
  let K := FractionRing B
  letI : Algebra K L := FractionRing.liftAlgebra B L
  letI : IsScalarTower B K L := FractionRing.isScalarTower_liftAlgebra B L
  letI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.of_comp B K L
  have hB : ¬ IsField B := by
    intro hfield
    apply hker
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient I |>.mpr hfield)
  obtain ⟨D, hD⟩ :=
    admitsNonfieldNoetherianValuationFactorization_of_essFiniteType
      (A := B) (K := K) (L := L) hB
  have hmem : ∀ a : A, f a ∈ D.V := by
    intro a
    change g (q a) ∈ D.V
    exact D.map_mem (q a)
  let gB : B →+* D.V :=
    (algebraMap B L).codRestrict D.V.toSubring D.map_mem
  let gA : A →+* D.V := f.codRestrict D.V.toSubring hmem
  have hg_eq : gA = gB.comp q := by ext a; rfl
  have hlocal : IsLocalHom gA := by
    rw [hg_eq]
    letI : IsLocalHom gB := D.isLocalHom
    exact RingHom.isLocalHom_comp gB q
  let D' : NoetherianValuationFactorization f :=
    { V := D.V
      map_mem := hmem
      isLocalHom := hlocal
      isNoetherianRing := D.isNoetherianRing }
  exact ⟨D', hD⟩

/-- A finite-type map from a noetherian local ring to a field whose kernel is
not maximal admits a discrete-valuation factorization. -/
theorem exists_discreteValuationFactorization_of_essFiniteType_of_ker_ne_maximal
    {A L : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Field L] (f : A →+* L) (hf : f.EssFiniteType)
    (hker : RingHom.ker f ≠ maximalIdeal A) :
    Nonempty (DiscreteValuationFactorization f) :=
  exists_discreteValuationFactorization_of_admitsNonfieldNoetherian
    (admitsNonfieldNoetherianValuationFactorization_of_essFiniteType_of_ker_ne_maximal
      f hf hker)

/-- Mathlib's integral-closure and Dedekind-domain API supplies the missing
noetherian valuation factor when the original local domain is already
Dedekind and the fraction-field extension is finite separable.  This is the
finite-separable, already-normal special case of the algebraic proposition
used in the geometry of DVRs. -/
theorem admitsNonfieldNoetherianValuationFactorization_of_isDedekindDomain
    {A K L : Type u} [CommRing A] [IsLocalRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hA : ¬ IsField A) :
    AdmitsNonfieldNoetherianValuationFactorization (algebraMap A L) := by
  let C := integralClosure A L
  letI : IsDedekindDomain C := integralClosure.isDedekindDomain A K L
  letI : IsFractionRing C L := integralClosure.isFractionRing_of_finite_extension K L
  have hinjAL : Function.Injective (algebraMap A L) := by
    intro a b hab
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    simpa only [IsScalarTower.algebraMap_apply A K L] using hab
  have hinjAC : Function.Injective (algebraMap A C) := by
    intro a b hab
    apply hinjAL
    simpa only [IsScalarTower.algebraMap_apply A C L] using
      congrArg (algebraMap C L) hab
  letI : FaithfulSMul A C :=
    (faithfulSMul_iff_algebraMap_injective A C).mpr hinjAC
  obtain ⟨P, hPmax, hPover⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := C) (maximalIdeal A)
  letI : P.IsMaximal := hPmax
  letI : P.IsPrime := hPmax.isPrime
  letI : P.LiesOver (maximalIdeal A) := hPover
  have hm0 : maximalIdeal A ≠ ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hA
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hm0 P
  let v : IsDedekindDomain.HeightOneSpectrum C := ⟨P, inferInstance, hP0⟩
  let V : ValuationSubring L := v.valuationSubringAtPrime L
  letI : Algebra C V := by dsimp [V]; infer_instance
  letI : IsScalarTower C V L := by dsimp [V]; infer_instance
  letI : IsLocalization v.asIdeal.primeCompl V := by
    dsimp [V, IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime]
    exact Localization.subalgebra.isLocalization_ofField L v.asIdeal.primeCompl
      v.asIdeal.primeCompl_le_nonZeroDivisors
  letI : IsDedekindDomain V := by dsimp [V]; infer_instance
  have hcompat (a : A) :
      algebraMap A L a = ((algebraMap C V (algebraMap A C a) : V) : L) := by
    rw [IsScalarTower.algebraMap_apply A C L,
      IsScalarTower.algebraMap_apply C V L, ValuationSubring.algebraMap_apply]
  have hmem : ∀ a : A, algebraMap A L a ∈ V := by
    intro a
    rw [hcompat a]
    exact (algebraMap C V (algebraMap A C a)).property
  let g : A →+* V := (algebraMap A L).codRestrict V.toSubring hmem
  have hg : IsLocalHom g := by
    apply ((IsLocalRing.local_hom_TFAE g).out 4 0).mp
    ext a
    change g a ∈ maximalIdeal V ↔ a ∈ maximalIdeal A
    have hga : g a = algebraMap C V (algebraMap A C a) := by
      apply Subtype.ext
      exact hcompat a
    rw [hga, IsLocalization.AtPrime.to_map_mem_maximal_iff V v.asIdeal]
    exact (P.mem_of_liesOver (maximalIdeal A) a).symm
  let D : NoetherianValuationFactorization (algebraMap A L) :=
    { V := V
      map_mem := hmem
      isLocalHom := hg
      isNoetherianRing := inferInstance }
  refine ⟨D, ?_⟩
  exact IsLocalization.AtPrime.not_isField C hP0 V

/-- A finite separable extension of the fraction field of a non-field local
Dedekind domain admits a DVR factorization. -/
theorem exists_discreteValuationFactorization_of_isDedekindDomain
    {A K L : Type u} [CommRing A] [IsLocalRing A] [IsDedekindDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hA : ¬ IsField A) :
    Nonempty (DiscreteValuationFactorization (algebraMap A L)) :=
  exists_discreteValuationFactorization_of_admitsNonfieldNoetherian
    (admitsNonfieldNoetherianValuationFactorization_of_isDedekindDomain
      (A := A) (K := K) (L := L) hA)

end IsLocalRing

namespace AlgebraicGeometry

universe u

namespace Scheme

/-- The map on stalks along a specialization is essentially of finite type.
On an affine neighborhood of the specialized point, both stalks are
localizations of the same ring of sections. -/
theorem stalkSpecializes_essFiniteType {X : Scheme.{u}} {x y : X}
    (h : Specializes x y) :
    (X.presheaf.stalkSpecializes h).hom.EssFiniteType := by
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset
      (show y ∈ (⊤ : X.Opens) from trivial)
  have hxU : x ∈ U := h.mem_open U.isOpen hyU
  let gy := X.presheaf.germ U y hyU
  let gx := X.presheaf.germ U x hxU
  have hgx : gx.hom.EssFiniteType := by
    letI := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
    change (algebraMap Γ(X, U) (X.presheaf.stalk x)).EssFiniteType
    rw [RingHom.essFiniteType_algebraMap]
    exact @Algebra.EssFiniteType.of_isLocalization _ _ _ _ _
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
      (hU.isLocalization_stalk ⟨x, hxU⟩)
  apply RingHom.EssFiniteType.of_comp gy.hom
  rw [show (X.presheaf.stalkSpecializes h).hom.comp gy.hom = gx.hom by
    exact CommRingCat.hom_ext_iff.mp
      (X.presheaf.germ_stalkSpecializes hyU h)]
  exact hgx

end Scheme

namespace Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical map from the stalk at a specialization `y` of `f(x)` to the
residue field at `x`. -/
noncomputable def specializationStalkToResidueField {x : X} {y : Y}
    (h : Specializes (f x) y) : Y.presheaf.stalk y ⟶ X.residueField x :=
  Y.presheaf.stalkSpecializes h ≫ f.stalkMap x ≫ X.residue x

/-- For a locally finite-type morphism, the canonical map from the stalk at a
target specialization to the source residue field is essentially of finite
type. -/
theorem specializationStalkToResidueField_essFiniteType
    [LocallyOfFiniteType f] {x : X} {y : Y}
    (h : Specializes (f x) y) :
    (f.specializationStalkToResidueField h).hom.EssFiniteType := by
  apply RingHom.EssFiniteType.comp
  · exact Scheme.stalkSpecializes_essFiniteType h
  apply RingHom.EssFiniteType.comp
  · exact LocallyOfFiniteType.stalkMap f x
  · exact (RingHom.FiniteType.of_surjective _
      (X.residue_surjective x)).essFiniteType

/-- The map from the residue-field point at `x` to `Y` factors through the
stalk at any specialization `y` of `f(x)`. -/
@[reassoc]
theorem fromSpecResidueField_comp_of_specializes {x : X} {y : Y}
    (h : Specializes (f x) y) :
    X.fromSpecResidueField x ≫ f =
      Spec.map (f.specializationStalkToResidueField h) ≫ Y.fromSpecStalk y := by
  rw [Scheme.fromSpecResidueField, Category.assoc,
    ← Scheme.SpecMap_stalkMap_fromSpecStalk,
    ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
  simp only [specializationStalkToResidueField, Spec.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- For a strict target specialization, the canonical stalk-to-residue-field
map has nonmaximal kernel. -/
theorem specializationStalkToResidueField_ker_ne_maximal_of_ne
    {x : X} {y : Y} (h : Specializes (f x) y) (hne : f x ≠ y) :
    RingHom.ker (f.specializationStalkToResidueField h).hom ≠
      maximalIdeal (Y.presheaf.stalk y) := by
  intro hker
  let φ := f.specializationStalkToResidueField h
  have hpoint :
      Spec.map φ (closedPoint (X.residueField x)) =
        closedPoint (Y.presheaf.stalk y) := by
    change PrimeSpectrum.comap φ.hom (closedPoint (X.residueField x)) =
      closedPoint (Y.presheaf.stalk y)
    apply PrimeSpectrum.ext
    change Ideal.comap φ.hom (maximalIdeal (X.residueField x)) =
      maximalIdeal (Y.presheaf.stalk y)
    rw [IsLocalRing.maximalIdeal_eq_bot]
    simpa [RingHom.ker] using hker
  apply hne
  have hw := congrArg
    (fun (q : Spec (X.residueField x) ⟶ Y) ↦
      q (closedPoint (X.residueField x)))
    (f.fromSpecResidueField_comp_of_specializes h)
  simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hw
  rw [Scheme.fromSpecResidueField_apply, hpoint,
    Scheme.fromSpecStalk_closedPoint] at hw
  exact hw

/-- A discrete-valuation factorization of the canonical stalk-to-residue-field
map produces a DVR-valuative square realizing the specialization. -/
noncomputable def dvrRealizationOfFactorization {x : X} {y : Y}
    (h : Specializes (f x) y)
    (D : IsLocalRing.DiscreteValuationFactorization
      (f.specializationStalkToResidueField h).hom) :
    DVRRealization f x y := by
  letI : IsLocalHom D.toRing := D.isLocalHom
  let sq : ValuativeCommSq f :=
    { R := D.R
      K := D.L
      i₁ := Spec.map (CommRingCat.ofHom D.toFractionField) ≫ X.fromSpecResidueField x
      i₂ := Spec.map (CommRingCat.ofHom D.toRing) ≫ Y.fromSpecStalk y
      commSq := ⟨by
        rw [Category.assoc, f.fromSpecResidueField_comp_of_specializes h]
        simp only [← Spec.map_comp_assoc]
        have hcomm :
            f.specializationStalkToResidueField h ≫
                CommRingCat.ofHom D.toFractionField =
              CommRingCat.ofHom D.toRing ≫
                CommRingCat.ofHom (algebraMap D.R D.L) :=
          CommRingCat.hom_ext D.comm.symm
        exact congrArg (fun q ↦ Spec.map q ≫ Y.fromSpecStalk y) hcomm⟩ }
  exact
    { sq := sq
      dvr := inferInstance
      generic_eq := by
        change X.fromSpecResidueField x
          (Spec.map (CommRingCat.ofHom D.toFractionField)
            (IsLocalRing.closedPoint D.L)) = x
        exact Scheme.fromSpecResidueField_apply _ _
      closed_eq := by
        change Y.fromSpecStalk y
          (Spec.map (CommRingCat.ofHom D.toRing)
            (IsLocalRing.closedPoint D.R)) = y
        rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint] }

/-- If every canonical stalk-to-residue-field map associated to a target
specialization admits a discrete-valuation factorization, then DVRs realize all
specializations of `f`. -/
theorem dvrRealizesSpecializations_of_factorizations
    (hfac : ∀ (x : X) (y : Y) (h : Specializes (f x) y),
      Nonempty (IsLocalRing.DiscreteValuationFactorization
        (f.specializationStalkToResidueField h).hom)) :
    DVRRealizesSpecializations f := by
  intro x y h
  exact (hfac x y h).map (f.dvrRealizationOfFactorization h)

/-- The exact noetherian commutative-algebra endpoint for the geometry of DVRs:
non-field noetherian valuation factorizations of the canonical local-ring maps
imply `DVRRealizesSpecializations`. -/
theorem dvrRealizesSpecializations_of_noetherianValuationFactorizations
    (hfac : ∀ (x : X) (y : Y) (h : Specializes (f x) y),
      IsLocalRing.AdmitsNonfieldNoetherianValuationFactorization
        (f.specializationStalkToResidueField h).hom) :
    DVRRealizesSpecializations f := by
  apply f.dvrRealizesSpecializations_of_factorizations
  intro x y h
  exact IsLocalRing.exists_discreteValuationFactorization_of_admitsNonfieldNoetherian
    (hfac x y h)

/-- API theorem used in Proposition A.4.4: a locally finite-type morphism into a locally
noetherian scheme realizes every target specialization by a DVR. This is a slightly more
local form than the book's finite-type/noetherian hypotheses. -/
theorem dvrRealizesSpecializations_of_locallyOfFiniteType
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    DVRRealizesSpecializations f := by
  apply f.dvrRealizesSpecializations_of_factorizations
  intro x y h
  let φ := (f.specializationStalkToResidueField h).hom
  by_cases hker : RingHom.ker φ = maximalIdeal (Y.presheaf.stalk y)
  · exact ⟨IsLocalRing.DiscreteValuationFactorization.of_ker_eq_maximal
      φ hker⟩
  · exact
      IsLocalRing.exists_discreteValuationFactorization_of_essFiniteType_of_ker_ne_maximal
        φ (f.specializationStalkToResidueField_essFiniteType h) hker

end Scheme.Hom

end AlgebraicGeometry
