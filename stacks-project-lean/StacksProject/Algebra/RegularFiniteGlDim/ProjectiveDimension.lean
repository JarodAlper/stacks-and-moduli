module

public import StacksProject.Algebra.SmoothOverField.«lemma-separable-smooth»
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.RingTheory.Regular.ProjectiveDimension
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Regular.Free
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Finite projective dimension over regular local rings

This file supplies the homological commutative-algebra API needed for Stacks Project tag
`00OF`.  It develops finite partial projective resolutions and flat base change, proves the
finite-module form of the regular-local global-dimension bound, and proves the residue-field
criterion for regularity by minimal free resolutions and the Kaplansky retract argument.

The main declarations are:

* `Module.hasProjectiveDimensionLE_of_isRegularLocalRing`;
* `IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField`;
* `Module.IsPartialProjectiveResolution.baseChange`.
-/

@[expose] public section

universe u v w

open CategoryTheory Pointwise

/-- A module has projective dimension at most `d` when its object in `ModuleCat` does. -/
abbrev Module.HasProjectiveDimensionLE (R : Type u) [CommRing R] (d : ℕ)
    (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  CategoryTheory.HasProjectiveDimensionLE (ModuleCat.of R M) d

/-- Projective dimension at most zero is equivalent to projectivity. -/
lemma Module.hasProjectiveDimensionLE_zero_iff_projective
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    [Small.{v} R] :
    Module.HasProjectiveDimensionLE R 0 M ↔ Module.Projective R M := by
  constructor
  · intro h
    have hdim : CategoryTheory.HasProjectiveDimensionLT (ModuleCat.of R M) 1 := h
    haveI : CategoryTheory.Projective (ModuleCat.of R M) :=
      CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr hdim
    exact ModuleCat.projective_of_module_projective (ModuleCat.of R M)
  · intro h
    letI : Module.Projective R M := h
    exact CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp
      (ModuleCat.projective_of_categoryTheory_projective _)

/-- A finite initial segment of a projective resolution, retaining its final syzygy. -/
inductive Module.IsPartialProjectiveResolution (R : Type u) [CommRing R] :
    (e : ℕ) → (M : Type v) → [AddCommGroup M] → [Module R M] →
    (K : Type v) → [AddCommGroup K] → [Module R K] → Prop
  | zero {M : Type v} [AddCommGroup M] [Module R M]
      {K : Type v} [AddCommGroup K] [Module R K]
      {F : Type v} [AddCommGroup F] [Module R F] [Module.Projective R F]
      (f : F →ₗ[R] M) (hf : Function.Surjective f)
      (i : K →ₗ[R] F) (hi : Function.Injective i)
      (hexact : LinearMap.range i = LinearMap.ker f) :
      Module.IsPartialProjectiveResolution R 0 M K
  | succ {e : ℕ} {M : Type v} [AddCommGroup M] [Module R M]
      {K' : Type v} [AddCommGroup K'] [Module R K']
      {K : Type v} [AddCommGroup K] [Module R K]
      (h : Module.IsPartialProjectiveResolution R e M K')
      {F : Type v} [AddCommGroup F] [Module R F] [Module.Projective R F]
      (f : F →ₗ[R] K') (hf : Function.Surjective f)
      (i : K →ₗ[R] F) (hi : Function.Injective i)
      (hexact : LinearMap.range i = LinearMap.ker f) :
      Module.IsPartialProjectiveResolution R (e + 1) M K

/-- Dimension shifting from the cokernel to the kernel of a projective presentation. -/
lemma Module.hasProjectiveDimensionLE_domain_of_projective
    (R : Type u) [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {F : Type v} [AddCommGroup F] [Module R F] [Module.Projective R F]
    {K : Type v} [AddCommGroup K] [Module R K]
    (f : F →ₗ[R] M) (hf : Function.Surjective f)
    (i : K →ₗ[R] F) (hi : Function.Injective i)
    (hexact : LinearMap.range i = LinearMap.ker f) {d : ℕ}
    (h : Module.HasProjectiveDimensionLE R (d + 1) M) :
    Module.HasProjectiveDimensionLE R d K := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (ModuleCat.ofHom i) (ModuleCat.ofHom f) (by
      ext x
      have hx : i x ∈ LinearMap.range i := LinearMap.mem_range_self i x
      rw [hexact] at hx
      exact LinearMap.mem_ker.mp hx)
  haveI : Mono S.f := (ModuleCat.mono_iff_injective _).mpr hi
  haveI : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr hf
  have hS : S.ShortExact := ShortComplex.ShortExact.mk (by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact hexact)
  haveI : CategoryTheory.Projective S.X₂ :=
    ModuleCat.projective_of_categoryTheory_projective _
  exact (hS.hasProjectiveDimensionLT_X₃_iff d inferInstance).mp h

/-- Dimension shifting from the kernel to the cokernel of a projective presentation. -/
lemma Module.hasProjectiveDimensionLE_codomain_of_projective
    (R : Type u) [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {F : Type v} [AddCommGroup F] [Module R F] [Module.Projective R F]
    {K : Type v} [AddCommGroup K] [Module R K]
    (f : F →ₗ[R] M) (hf : Function.Surjective f)
    (i : K →ₗ[R] F) (hi : Function.Injective i)
    (hexact : LinearMap.range i = LinearMap.ker f) {d : ℕ}
    (h : Module.HasProjectiveDimensionLE R d K) :
    Module.HasProjectiveDimensionLE R (d + 1) M := by
  let S : ShortComplex (ModuleCat R) :=
    ShortComplex.mk (ModuleCat.ofHom i) (ModuleCat.ofHom f) (by
      ext x
      have hx : i x ∈ LinearMap.range i := LinearMap.mem_range_self i x
      rw [hexact] at hx
      exact LinearMap.mem_ker.mp hx)
  haveI : Mono S.f := (ModuleCat.mono_iff_injective _).mpr hi
  haveI : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr hf
  have hS : S.ShortExact := ShortComplex.ShortExact.mk (by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact hexact)
  haveI : CategoryTheory.Projective S.X₂ :=
    ModuleCat.projective_of_categoryTheory_projective _
  exact (hS.hasProjectiveDimensionLT_X₃_iff d inferInstance).mpr h

/-- A projective-dimension bound on the resolved module bounds the final syzygy. -/
lemma Module.IsPartialProjectiveResolution.hasProjectiveDimensionLE_ker
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {e : ℕ} {K : Type v} [AddCommGroup K] [Module R K]
    (hres : Module.IsPartialProjectiveResolution R e M K) {d : ℕ}
    (h : Module.HasProjectiveDimensionLE R (d + e + 1) M) :
    Module.HasProjectiveDimensionLE R d K := by
  induction hres generalizing d with
  | @zero M _ _ K _ _ F _ _ _ f hf i hi hexact =>
      apply Module.hasProjectiveDimensionLE_domain_of_projective R f hf i hi hexact
      simpa only [Nat.add_zero] using h
  | @succ e M _ _ K' _ _ K _ _ hres F _ _ _ f hf i hi hexact ih =>
      apply Module.hasProjectiveDimensionLE_domain_of_projective R f hf i hi hexact
      apply ih
      convert h using 1 <;> omega

/-- A sufficiently long partial resolution has projective final syzygy. -/
lemma Module.IsPartialProjectiveResolution.projective_of_projectiveDimension_le
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Small.{v} R] {d e : ℕ} (hle : d - 1 ≤ e)
    (h : Module.HasProjectiveDimensionLE R d M)
    {K : Type v} [AddCommGroup K] [Module R K]
    (hres : Module.IsPartialProjectiveResolution R e M K) :
    Module.Projective R K := by
  have h' : Module.HasProjectiveDimensionLE R (0 + e + 1) M :=
    show CategoryTheory.HasProjectiveDimensionLT (ModuleCat.of R M) (0 + e + 1 + 1) from
      CategoryTheory.hasProjectiveDimensionLT_of_ge (ModuleCat.of R M) (d + 1)
        (0 + e + 1 + 1) (by omega)
  have hK := hres.hasProjectiveDimensionLE_ker h'
  haveI : CategoryTheory.Projective (ModuleCat.of R K) :=
    CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mpr hK
  exact ModuleCat.projective_of_module_projective (ModuleCat.of R K)

/-- A bound on the final syzygy gives a bound on the module resolved by a partial resolution. -/
lemma Module.IsPartialProjectiveResolution.hasProjectiveDimensionLE
    {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {e : ℕ} {K : Type v} [AddCommGroup K] [Module R K]
    (hres : Module.IsPartialProjectiveResolution R e M K) {d : ℕ}
    (h : Module.HasProjectiveDimensionLE R d K) :
    Module.HasProjectiveDimensionLE R (d + e + 1) M := by
  induction hres generalizing d with
  | @zero M _ _ K _ _ F _ _ _ f hf i hi hexact =>
      simpa only [Nat.add_zero] using
        Module.hasProjectiveDimensionLE_codomain_of_projective R f hf i hi hexact h
  | @succ e M _ _ K' _ _ K _ _ hres F _ _ _ f hf i hi hexact ih =>
      have h' := Module.hasProjectiveDimensionLE_codomain_of_projective
        R f hf i hi hexact h
      convert ih h' using 1 <;> omega

/-- Every finite module over a Noetherian ring has finite partial resolutions of any length. -/
lemma Module.exists_isPartialProjectiveResolution_finite
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (d : ℕ) :
    ∃ (K : Type u) (_ : AddCommGroup K) (_ : Module R K) (_ : Module.Finite R K),
      Module.IsPartialProjectiveResolution R d M K := by
  induction d with
  | zero =>
      obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
      refine ⟨LinearMap.ker f, inferInstance, inferInstance, ?_, ?_⟩
      · exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      · exact Module.IsPartialProjectiveResolution.zero f hf (LinearMap.ker f).subtype
          (Submodule.injective_subtype _) (Submodule.range_subtype _)
  | succ e ih =>
      obtain ⟨K', _, _, _, hres⟩ := ih
      obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R K'
      refine ⟨LinearMap.ker f, inferInstance, inferInstance, ?_, ?_⟩
      · exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      · exact Module.IsPartialProjectiveResolution.succ hres f hf
          (LinearMap.ker f).subtype (Submodule.injective_subtype _)
          (Submodule.range_subtype _)

open TensorProduct

/-- Flat base change preserves partial projective resolutions. -/
lemma Module.IsPartialProjectiveResolution.baseChange
    {R : Type u} [CommRing R] (S : Type w) [CommRing S] [Algebra R S]
    [Module.Flat R S] {e : ℕ} {M K : Type v}
    [AddCommGroup M] [Module R M] [AddCommGroup K] [Module R K]
    (h : Module.IsPartialProjectiveResolution R e M K) :
    Module.IsPartialProjectiveResolution S e (S ⊗[R] M) (S ⊗[R] K) := by
  induction h with
  | @zero M _ _ K _ _ F _ _ _ f hf i hi hexact =>
      have hsurj : Function.Surjective (f.baseChange S) := by
        rw [LinearMap.baseChange_eq_ltensor]
        exact LinearMap.lTensor_surjective S hf
      have hinj : Function.Injective (i.baseChange S) := by
        rw [LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_preserves_injective_linearMap i hi
      have hex : Function.Exact (i.baseChange S) (f.baseChange S) := by
        rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_exact S (LinearMap.exact_iff.mpr hexact.symm)
      exact Module.IsPartialProjectiveResolution.zero (f.baseChange S) hsurj
        (i.baseChange S) hinj (LinearMap.exact_iff.mp hex).symm
  | @succ e M _ _ K _ _ K' _ _ hres F _ _ _ f hf i hi hexact ih =>
      have hsurj : Function.Surjective (f.baseChange S) := by
        rw [LinearMap.baseChange_eq_ltensor]
        exact LinearMap.lTensor_surjective S hf
      have hinj : Function.Injective (i.baseChange S) := by
        rw [LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_preserves_injective_linearMap i hi
      have hex : Function.Exact (i.baseChange S) (f.baseChange S) := by
        rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
        exact Module.Flat.lTensor_exact S (LinearMap.exact_iff.mpr hexact.symm)
      exact Module.IsPartialProjectiveResolution.succ ih (f.baseChange S) hsurj
        (i.baseChange S) hinj (LinearMap.exact_iff.mp hex).symm

/-- Quotienting a projective presentation by a regular element remains short exact. -/
lemma QuotSMulTop.isShortExact_map_ker
    {R : Type u} [CommRing R] {x : R}
    {M F : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup F] [Module R F] (f : F →ₗ[R] M)
    (hf : Function.Surjective f) (hreg : IsSMulRegular M x) :
    Function.Injective (QuotSMulTop.map x (LinearMap.ker f).subtype) ∧
      Function.Exact (QuotSMulTop.map x (LinearMap.ker f).subtype)
        (QuotSMulTop.map x f) ∧
      Function.Surjective (QuotSMulTop.map x f) := by
  have hzero : Function.Exact (0 : Unit →ₗ[R] LinearMap.ker f)
      (LinearMap.ker f).subtype :=
    (LinearMap.exact_zero_iff_injective Unit (LinearMap.ker f).subtype).mpr
      Subtype.val_injective
  have hker : Function.Exact (LinearMap.ker f).subtype f :=
    LinearMap.exact_subtype_ker_map f
  have hzero' := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
    hzero hker hreg
  have hinj : Function.Injective
      (QuotSMulTop.map x (LinearMap.ker f).subtype) := by
    rw [← LinearMap.exact_zero_iff_injective (QuotSMulTop x Unit)]
    simpa using hzero'
  exact ⟨hinj, QuotSMulTop.map_exact x hker hf,
    QuotSMulTop.map_surjective x hf⟩

/-- Projective dimension does not increase after quotienting by a regular element. -/
lemma Module.HasProjectiveDimensionLE.quotSMulTop
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ nonZeroDivisors R) {k : ℕ} :
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      IsSMulRegular M x → Module.HasProjectiveDimensionLE R k M →
      Module.HasProjectiveDimensionLE (R ⧸ Ideal.span {x}) k (QuotSMulTop x M) := by
  induction k with
  | zero =>
      intro M _ _ _ hreg h
      haveI : Module.Projective R M :=
        (Module.hasProjectiveDimensionLE_zero_iff_projective R M).mp h
      haveI : Module.Flat R M := inferInstance
      haveI : Module.Free R M := Module.free_of_flat_of_isLocalRing
      exact (Module.hasProjectiveDimensionLE_zero_iff_projective
        (R ⧸ Ideal.span {x}) (QuotSMulTop x M)).mpr Module.Projective.of_free
  | succ k ih =>
      intro M _ _ _ hreg h
      obtain ⟨t, f, hf⟩ := Module.Finite.exists_fin' R M
      haveI : Module.Finite R (LinearMap.ker f) :=
        Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      have hregR : IsSMulRegular R x :=
        (isLeftRegular_iff_right_eq_zero_of_mul.mpr hx.1).isSMulRegular
      have hregF : IsSMulRegular (Fin t → R) x :=
        Function.Injective.piMap fun _ => hregR
      have hregK : IsSMulRegular (LinearMap.ker f) x := hregF.submodule _ x
      have hKdim : Module.HasProjectiveDimensionLE R k (LinearMap.ker f) :=
        Module.hasProjectiveDimensionLE_domain_of_projective R f hf
          (LinearMap.ker f).subtype Subtype.val_injective
          (Submodule.range_subtype _) h
      have ihK := ih (LinearMap.ker f) hregK hKdim
      obtain ⟨hinj, hexact, hsurj⟩ := QuotSMulTop.isShortExact_map_ker f hf hreg
      let i' : QuotSMulTop x (LinearMap.ker f) →ₗ[R ⧸ Ideal.span {x}]
          QuotSMulTop x (Fin t → R) :=
        (QuotSMulTop.map x (LinearMap.ker f).subtype).extendScalarsOfSurjective
          Ideal.Quotient.mk_surjective
      let p' : QuotSMulTop x (Fin t → R) →ₗ[R ⧸ Ideal.span {x}]
          QuotSMulTop x M :=
        (QuotSMulTop.map x f).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      have hexact' : Function.Exact i' p' := hexact
      exact Module.hasProjectiveDimensionLE_codomain_of_projective
        (R ⧸ Ideal.span {x}) p' hsurj i' hinj
        ((LinearMap.exact_iff.mp hexact').symm) ihK

/-- Lift a projective-dimension bound across quotient by a regular element. -/
lemma Module.HasProjectiveDimensionLE.of_quotSMulTop
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hxm : x ∈ IsLocalRing.maximalIdeal R)
    (hx : x ∈ nonZeroDivisors R) {k : ℕ} :
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      IsSMulRegular M x →
      Module.HasProjectiveDimensionLE (R ⧸ Ideal.span {x}) k (QuotSMulTop x M) →
      Module.HasProjectiveDimensionLE R k M := by
  haveI : Nontrivial (R ⧸ Ideal.span {x}) :=
    Submodule.Quotient.nontrivial_iff.mpr fun h =>
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        (top_le_iff.mp (h ▸ Ideal.span_le.mpr (by simpa using hxm)))
  haveI : IsLocalRing (R ⧸ Ideal.span {x}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
      Ideal.Quotient.mk_surjective
  induction k with
  | zero =>
      intro M _ _ _ hreg h
      haveI : Module.Projective (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
        (Module.hasProjectiveDimensionLE_zero_iff_projective
          (R ⧸ Ideal.span {x}) (QuotSMulTop x M)).mp h
      haveI : Module.Finite R (QuotSMulTop x M) :=
        Module.Finite.of_surjective (x • (⊤ : Submodule R M)).mkQ
          (Submodule.mkQ_surjective _)
      haveI : Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
        Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) _
      haveI : Module.Flat (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
        inferInstance
      have hfree : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
        Module.free_of_flat_of_isLocalRing
      haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
      haveI : Module.Free R M :=
        (Module.free_quotSMulTop_iff_free R M
          (IsLocalRing.maximalIdeal_le_jacobson ⊥ hxm) hreg).mp hfree
      exact (Module.hasProjectiveDimensionLE_zero_iff_projective R M).mpr
        Module.Projective.of_free
  | succ k ih =>
      intro M _ _ _ hreg h
      obtain ⟨t, f, hf⟩ := Module.Finite.exists_fin' R M
      haveI : Module.Finite R (LinearMap.ker f) :=
        Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      have hregR : IsSMulRegular R x :=
        (isLeftRegular_iff_right_eq_zero_of_mul.mpr hx.1).isSMulRegular
      have hregF : IsSMulRegular (Fin t → R) x :=
        Function.Injective.piMap fun _ => hregR
      have hregK : IsSMulRegular (LinearMap.ker f) x := hregF.submodule _ x
      obtain ⟨hinj, hexact, hsurj⟩ := QuotSMulTop.isShortExact_map_ker f hf hreg
      let i' : QuotSMulTop x (LinearMap.ker f) →ₗ[R ⧸ Ideal.span {x}]
          QuotSMulTop x (Fin t → R) :=
        (QuotSMulTop.map x (LinearMap.ker f).subtype).extendScalarsOfSurjective
          Ideal.Quotient.mk_surjective
      let p' : QuotSMulTop x (Fin t → R) →ₗ[R ⧸ Ideal.span {x}]
          QuotSMulTop x M :=
        (QuotSMulTop.map x f).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      have hexact' : Function.Exact i' p' := hexact
      have hKq : Module.HasProjectiveDimensionLE (R ⧸ Ideal.span {x}) k
          (QuotSMulTop x (LinearMap.ker f)) :=
        Module.hasProjectiveDimensionLE_domain_of_projective
          (R ⧸ Ideal.span {x}) p' hsurj i' hinj
          ((LinearMap.exact_iff.mp hexact').symm) h
      have hK := ih (LinearMap.ker f) hregK hKq
      exact Module.hasProjectiveDimensionLE_codomain_of_projective R f hf
        (LinearMap.ker f).subtype Subtype.val_injective
        (Submodule.range_subtype _) hK

/-- Every finite module over a regular local ring of dimension `d` has projective dimension
at most `d`.  This is the finite-module portion of Stacks Project tag `00O7`. -/
theorem Module.hasProjectiveDimensionLE_of_isRegularLocalRing :
    ∀ (d : ℕ) (R : Type u) [CommRing R] [IsLocalRing R]
      [IsNoetherianRing R] [IsRegularLocalRing R],
      ringKrullDim R = (d : WithBot ℕ∞) →
      ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
        Module.HasProjectiveDimensionLE R d M := by
  intro d
  induction d with
  | zero =>
      intro R _ _ _ _ hdim M _ _ _
      have hfin : Module.finrank (IsLocalRing.ResidueField R)
          (IsLocalRing.CotangentSpace R) = 0 := by
        have h := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
        rw [hdim] at h
        exact_mod_cast h
      letI : Field R :=
        (IsLocalRing.finrank_cotangentSpace_eq_zero_iff.mp hfin).toField
      haveI : Module.Free R M := Module.Free.of_divisionRing R M
      exact (Module.hasProjectiveDimensionLE_zero_iff_projective R M).mpr
        Module.Projective.of_free
  | succ d ih =>
      intro R _ _ _ _ hdim M _ _ _
      obtain ⟨x, hxm, hxm2, -⟩ :=
        IsLocalRing.exists_mem_maximalIdeal_notMem_pow_two_notMem_minimalPrimes hdim
      haveI : IsDomain R := IsRegularLocalRing.isDomain
      have hx0 : x ≠ 0 := fun h => hxm2 (h ▸ Submodule.zero_mem _)
      have hx : x ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hx0
      haveI : Nontrivial (R ⧸ Ideal.span {x}) :=
        Submodule.Quotient.nontrivial_iff.mpr fun h =>
          (IsLocalRing.maximalIdeal.isMaximal R).ne_top
            (top_le_iff.mp (h ▸ Ideal.span_le.mpr (by simpa using hxm)))
      haveI : IsLocalRing (R ⧸ Ideal.span {x}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
          Ideal.Quotient.mk_surjective
      obtain ⟨hregQ, hdimQ⟩ :=
        IsRegularLocalRing.quotient_of_notMem_pow_two hdim x hxm hxm2
      letI : IsRegularLocalRing (R ⧸ Ideal.span {x}) := hregQ
      obtain ⟨t, f, hf⟩ := Module.Finite.exists_fin' R M
      haveI : Module.Finite R (LinearMap.ker f) :=
        Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      have hregR : IsSMulRegular R x :=
        (isLeftRegular_iff_right_eq_zero_of_mul.mpr hx.1).isSMulRegular
      have hregF : IsSMulRegular (Fin t → R) x :=
        Function.Injective.piMap fun _ => hregR
      have hregK : IsSMulRegular (LinearMap.ker f) x := hregF.submodule _ x
      haveI : Module.Finite R (QuotSMulTop x (LinearMap.ker f)) :=
        Module.Finite.of_surjective (x • (⊤ : Submodule R (LinearMap.ker f))).mkQ
          (Submodule.mkQ_surjective _)
      haveI : Module.Finite (R ⧸ Ideal.span {x})
          (QuotSMulTop x (LinearMap.ker f)) :=
        Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) _
      have hKq : Module.HasProjectiveDimensionLE (R ⧸ Ideal.span {x}) d
          (QuotSMulTop x (LinearMap.ker f)) :=
        ih (R ⧸ Ideal.span {x}) hdimQ _
      have hK : Module.HasProjectiveDimensionLE R d (LinearMap.ker f) :=
        Module.HasProjectiveDimensionLE.of_quotSMulTop hxm hx
          (LinearMap.ker f) hregK hKq
      exact Module.hasProjectiveDimensionLE_codomain_of_projective R f hf
        (LinearMap.ker f).subtype Subtype.val_injective
        (Submodule.range_subtype _) hK

/-- A finite module over a local ring has a finite free cover whose kernel lies in `mF`. -/
lemma Module.exists_minimal_finite_free_cover
    (R : Type u) [CommRing R] [IsLocalRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (ι : Type u) (_ : Finite ι)
      (f : (ι →₀ R) →ₗ[R] M), Function.Surjective f ∧
        LinearMap.ker f ≤ IsLocalRing.maximalIdeal R • ⊤ := by
  classical
  let k := IsLocalRing.ResidueField R
  let ι := Module.Free.ChooseBasisIndex k (k ⊗[R] M)
  let b : Basis ι k (k ⊗[R] M) := Module.Free.chooseBasis k (k ⊗[R] M)
  let v : ι → M := fun i =>
    (TensorProduct.mk_surjective R M k IsLocalRing.residue_surjective (b i)).choose
  have hv (i : ι) : 1 ⊗ₜ[R] v i = b i :=
    (TensorProduct.mk_surjective R M k IsLocalRing.residue_surjective (b i)).choose_spec
  let f : (ι →₀ R) →ₗ[R] M := Finsupp.linearCombination R v
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis v b hv
  letI : Finite ι := Module.Finite.finite_basis b
  refine ⟨ι, inferInstance, f, hf, ?_⟩
  intro c hc
  have hc_t : (1 : k) ⊗ₜ[R] (f c) = 0 := by rw [LinearMap.mem_ker.mp hc, tmul_zero]
  have hcoeff (i : ι) : algebraMap R k (c i) = 0 := by
    change (1 : k) ⊗ₜ[R] (Finsupp.linearCombination R v c) = 0 at hc_t
    rw [Finsupp.linearCombination_apply] at hc_t
    change (TensorProduct.mk R k M 1) (c.sum fun i a => a • v i) = 0 at hc_t
    have hsmul (a : R) (z : k ⊗[R] M) : a • z = algebraMap R k a • z :=
      (IsScalarTower.algebraMap_smul R a z).symm
    simp only [map_finsuppSum] at hc_t
    have hc_t' : c.sum (fun i a => algebraMap R k a • b i) = 0 := by
      convert hc_t using 1
      apply Finsupp.sum_congr
      intro j hj
      rw [map_smul, hsmul]
      exact congrArg (fun z => algebraMap R k (c j) • z) (hv j).symm
    let ck : ι →₀ k := Finsupp.mapRange.linearMap (Algebra.linearMap R k) c
    have hck : Finsupp.linearCombination k b ck = 0 := by
      rw [Finsupp.linearCombination_apply]
      simpa [ck, Finsupp.sum_mapRange_index] using hc_t'
    have hzero := (linearIndependent_iff.mp b.linearIndependent ck) hck
    exact DFunLike.congr_fun hzero i
  have htop : Finsupp.submodule (fun _ : ι => (⊤ : Submodule R R)) = ⊤ := by
    ext c
    simp
  rw [← htop, ← Finsupp.submodule_smul R ι (fun _ => (⊤ : Submodule R R))]
  rw [Finsupp.mem_submodule_iff]
  intro i
  rw [show c i = c i • (1 : R) by simp]
  apply Submodule.smul_mem_smul
  · rw [← IsLocalRing.ker_residue, ← IsLocalRing.ResidueField.algebraMap_eq]
    exact hcoeff i
  · trivial

/-- A partial finite free resolution all of whose displayed differentials are minimal. -/
inductive Module.IsMinimalPartialFreeResolution (R : Type u) [CommRing R]
    [IsLocalRing R] :
    (e : ℕ) → (M : Type u) → [AddCommGroup M] → [Module R M] →
    (K : Type u) → [AddCommGroup K] → [Module R K] → Prop
  | zero {M : Type u} [AddCommGroup M] [Module R M]
      {K : Type u} [AddCommGroup K] [Module R K]
      {F : Type u} [AddCommGroup F] [Module R F] [Module.Free R F]
      (f : F →ₗ[R] M) (hf : Function.Surjective f)
      (i : K →ₗ[R] F) (hi : Function.Injective i)
      (hexact : LinearMap.range i = LinearMap.ker f)
      (hminimal : LinearMap.range i ≤ IsLocalRing.maximalIdeal R • ⊤) :
      Module.IsMinimalPartialFreeResolution R 0 M K
  | succ {e : ℕ} {M : Type u} [AddCommGroup M] [Module R M]
      {K' : Type u} [AddCommGroup K'] [Module R K']
      {K : Type u} [AddCommGroup K] [Module R K]
      (h : Module.IsMinimalPartialFreeResolution R e M K')
      {F : Type u} [AddCommGroup F] [Module R F] [Module.Free R F]
      (f : F →ₗ[R] K') (hf : Function.Surjective f)
      (i : K →ₗ[R] F) (hi : Function.Injective i)
      (hexact : LinearMap.range i = LinearMap.ker f)
      (hminimal : LinearMap.range i ≤ IsLocalRing.maximalIdeal R • ⊤) :
      Module.IsMinimalPartialFreeResolution R (e + 1) M K

/-- Forget minimality and regard a minimal free resolution as a projective resolution. -/
lemma Module.IsMinimalPartialFreeResolution.toIsPartialProjectiveResolution
    {R : Type u} [CommRing R] [IsLocalRing R]
    {e : ℕ} {M K : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K]
    (h : Module.IsMinimalPartialFreeResolution R e M K) :
    Module.IsPartialProjectiveResolution R e M K := by
  induction h with
  | @zero M _ _ K _ _ F _ _ _ f hf i hi hexact hminimal =>
      exact Module.IsPartialProjectiveResolution.zero f hf i hi hexact
  | @succ e M _ _ K' _ _ K _ _ hres F _ _ _ f hf i hi hexact hminimal ih =>
      exact Module.IsPartialProjectiveResolution.succ ih f hf i hi hexact

/-- Finite modules over Noetherian local rings possess minimal partial free resolutions. -/
lemma Module.exists_isMinimalPartialFreeResolution_finite
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (d : ℕ) :
    ∃ (K : Type u) (_ : AddCommGroup K) (_ : Module R K) (_ : Module.Finite R K),
      Module.IsMinimalPartialFreeResolution R d M K := by
  induction d with
  | zero =>
      obtain ⟨ι, _, f, hf, hmin⟩ := Module.exists_minimal_finite_free_cover R M
      refine ⟨LinearMap.ker f, inferInstance, inferInstance, ?_, ?_⟩
      · exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      · exact Module.IsMinimalPartialFreeResolution.zero f hf
          (LinearMap.ker f).subtype Subtype.val_injective
          (Submodule.range_subtype _) (by simpa using hmin)
  | succ e ih =>
      obtain ⟨K', _, _, _, hres⟩ := ih
      obtain ⟨ι, _, f, hf, hmin⟩ := Module.exists_minimal_finite_free_cover R K'
      refine ⟨LinearMap.ker f, inferInstance, inferInstance, ?_, ?_⟩
      · exact Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      · exact Module.IsMinimalPartialFreeResolution.succ hres f hf
          (LinearMap.ker f).subtype Subtype.val_injective
          (Submodule.range_subtype _) (by simpa using hmin)

/-- A partial resolution with zero final syzygy can be shortened by one step. -/
lemma Module.IsPartialProjectiveResolution.hasProjectiveDimensionLE_of_subsingleton
    {R : Type u} [CommRing R] {e : ℕ}
    {M K : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K] [Subsingleton K] [Small.{u} R]
    (h : Module.IsPartialProjectiveResolution R e M K) :
    Module.HasProjectiveDimensionLE R e M := by
  cases h with
  | @zero M _ _ K _ _ F _ _ hproj f hf i hi hexact =>
      have hfi : Function.Injective f := by
        rw [← LinearMap.ker_eq_bot, ← hexact]
        apply LinearMap.range_eq_bot.mpr
        ext x
        simpa using congrArg i (Subsingleton.elim x 0)
      let e : F ≃ₗ[R] M := LinearEquiv.ofBijective f ⟨hfi, hf⟩
      haveI : Module.Projective R M := Module.Projective.of_equiv e
      exact (Module.hasProjectiveDimensionLE_zero_iff_projective R M).mpr inferInstance
  | @succ e M _ _ K' _ _ K _ _ hres F _ _ hproj f hf i hi hexact =>
      have hfi : Function.Injective f := by
        rw [← LinearMap.ker_eq_bot, ← hexact]
        apply LinearMap.range_eq_bot.mpr
        ext x
        simpa using congrArg i (Subsingleton.elim x 0)
      let ef : F ≃ₗ[R] K' := LinearEquiv.ofBijective f ⟨hfi, hf⟩
      haveI : Module.Projective R K' := Module.Projective.of_equiv ef
      simpa using hres.hasProjectiveDimensionLE
        ((Module.hasProjectiveDimensionLE_zero_iff_projective R K').mpr inferInstance)

/-- A nonzero free module minimally embedded in a free module forces the ring's socle to vanish. -/
lemma Module.not_exists_annihilated_by_maximalIdeal_of_minimal_injection
    {R : Type u} [CommRing R] [IsLocalRing R]
    {K F : Type u} [AddCommGroup K] [Module R K] [Module.Free R K] [Nontrivial K]
    [AddCommGroup F] [Module R F]
    (i : K →ₗ[R] F) (hi : Function.Injective i)
    (hminimal : LinearMap.range i ≤ IsLocalRing.maximalIdeal R • ⊤) :
    ¬ ∃ r : R, r ≠ 0 ∧ ∀ a ∈ IsLocalRing.maximalIdeal R, a • r = 0 := by
  classical
  rintro ⟨r, hr, hkill⟩
  let b := Module.Free.chooseBasis R K
  obtain ⟨j⟩ := b.index_nonempty
  have hrb : r • b j ≠ 0 := by
    intro hz
    have hz' := congrArg b.repr hz
    have hzj := DFunLike.congr_fun hz' j
    apply hr
    simpa only [map_smul, Basis.repr_self, Finsupp.smul_single,
      smul_eq_mul, mul_one, map_zero, Finsupp.zero_apply,
      Finsupp.single_eq_same] using hzj
  have hib_mem : i (b j) ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R F) :=
    hminimal (LinearMap.mem_range_self i (b j))
  have hrib : r • i (b j) = 0 := by
    refine Submodule.smul_induction_on (p := fun z : F => r • z = 0) hib_mem ?_ ?_
    · intro a ha y hy
      rw [smul_smul, mul_comm, ← smul_eq_mul, hkill a ha, zero_smul]
    · intro x y hx hy
      rw [smul_add, hx, hy, add_zero]
  apply hrb
  apply hi
  rw [map_smul, hrib, map_zero]

/-- A minimal resolution with nonzero free last syzygy forces the ring's socle to vanish. -/
lemma Module.IsMinimalPartialFreeResolution.not_exists_annihilated_by_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    {e : ℕ} {M K : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K] [Module.Free R K] [Nontrivial K]
    (h : Module.IsMinimalPartialFreeResolution R e M K) :
    ¬ ∃ r : R, r ≠ 0 ∧ ∀ a ∈ IsLocalRing.maximalIdeal R, a • r = 0 := by
  cases h with
  | @zero M _ _ K _ _ F _ _ _ f hf i hi hexact hminimal =>
      exact Module.not_exists_annihilated_by_maximalIdeal_of_minimal_injection i hi hminimal
  | @succ e M _ _ K' _ _ K _ _ hres F _ _ _ f hf i hi hexact hminimal =>
      exact Module.not_exists_annihilated_by_maximalIdeal_of_minimal_injection i hi hminimal

/-- The maximal ideal is associated to a module exactly when it annihilates a nonzero element. -/
lemma Module.maximalIdeal_mem_associatedPrimes_iff
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type u} [AddCommGroup M] [Module R M] :
    IsLocalRing.maximalIdeal R ∈ associatedPrimes R M ↔
      ∃ s : M, s ≠ 0 ∧ ∀ a ∈ IsLocalRing.maximalIdeal R, a • s = 0 := by
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
  constructor
  · rintro ⟨_, s, hs⟩
    have hkill : ∀ a ∈ IsLocalRing.maximalIdeal R, a • s = 0 := by
      intro a ha
      have : a ∈ (⊥ : Submodule R M).colon {s} := hs ▸ ha
      exact Submodule.mem_colon_singleton.mp this
    refine ⟨s, fun h0 => (IsLocalRing.maximalIdeal.isMaximal R).ne_top ?_, hkill⟩
    rw [hs, h0]
    exact Submodule.colon_singleton_zero
  · rintro ⟨s, hs_ne, hkill⟩
    refine ⟨(IsLocalRing.maximalIdeal.isMaximal R).isPrime, s, le_antisymm ?_ ?_⟩
    · intro a ha
      exact Submodule.mem_colon_singleton.mpr (hkill a ha)
    · refine IsLocalRing.le_maximalIdeal ?_
      intro htop
      have h1 : (1 : R) ∈ (⊥ : Submodule R M).colon {s} := by rw [htop]; trivial
      have hs0 := Submodule.mem_colon_singleton.mp h1
      rw [one_smul] at hs0
      exact hs_ne hs0

/-- Positive finite projective dimension of the residue field excludes the maximal ideal from
the associated primes of the ring. -/
lemma Module.maximalIdeal_not_mem_associatedPrimes_of_residueField_projectiveDimension
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {e : ℕ}
    (hle : Module.HasProjectiveDimensionLE R (e + 1) (IsLocalRing.ResidueField R))
    (hnot : ¬ Module.HasProjectiveDimensionLE R e (IsLocalRing.ResidueField R)) :
    IsLocalRing.maximalIdeal R ∉ associatedPrimes R R := by
  letI : Module.Finite R (IsLocalRing.ResidueField R) :=
    Module.Finite.of_surjective (IsLocalRing.maximalIdeal R).mkQ
      (Submodule.mkQ_surjective _)
  obtain ⟨K, _, _, _, hres⟩ := Module.exists_isMinimalPartialFreeResolution_finite
    R (IsLocalRing.ResidueField R) e
  have hpartial := hres.toIsPartialProjectiveResolution
  haveI : Module.Projective R K :=
    hpartial.projective_of_projectiveDimension_le (by omega) hle
  haveI : Module.FinitePresentation R K := Module.finitePresentation_of_finite R K
  haveI : Module.Free R K := Module.free_of_flat_of_isLocalRing
  have hK : Nontrivial K := by
    by_contra hK
    letI : Subsingleton K := not_nontrivial_iff_subsingleton.mp hK
    exact hnot hpartial.hasProjectiveDimensionLE_of_subsingleton
  letI : Nontrivial K := hK
  rw [Module.maximalIdeal_mem_associatedPrimes_iff]
  exact hres.not_exists_annihilated_by_maximalIdeal

/-- Nakayama's lemma: if `m ⊆ m²` in a Noetherian local ring, then `m = 0`. -/
lemma IsLocalRing.maximalIdeal_eq_bot_of_le_pow_two
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (h : IsLocalRing.maximalIdeal R ≤ IsLocalRing.maximalIdeal R ^ 2) :
    IsLocalRing.maximalIdeal R = ⊥ := by
  refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal R)
    (IsNoetherian.noetherian _) ?_ ?_
  · rwa [Ideal.smul_eq_mul, ← sq]
  · rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]

/-- Prime avoidance produces an element of `m \ m²` regular on a finite module when `m` is
nonzero and is not associated to that module. -/
lemma IsLocalRing.exists_notMem_pow_two_isSMulRegular
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : IsLocalRing.maximalIdeal R ∉ associatedPrimes R M)
    (hm : IsLocalRing.maximalIdeal R ≠ ⊥) :
    ∃ x ∈ IsLocalRing.maximalIdeal R,
      x ∉ IsLocalRing.maximalIdeal R ^ 2 ∧ IsSMulRegular M x := by
  classical
  have h_fin : (insert (IsLocalRing.maximalIdeal R ^ 2)
      (associatedPrimes R M)).Finite := (associatedPrimes.finite R M).insert _
  have h_not_subset : ¬ (IsLocalRing.maximalIdeal R : Set R) ⊆
      ⋃ p ∈ insert (IsLocalRing.maximalIdeal R ^ 2)
        (associatedPrimes R M), (p : Set R) := by
    intro hsub
    obtain ⟨p, hp_mem, hp_le⟩ := (Ideal.subset_union_prime_finite h_fin
      (IsLocalRing.maximalIdeal R ^ 2) (IsLocalRing.maximalIdeal R ^ 2)
      (fun q hq hq1 _ => by
        rcases hq with rfl | hq_ass
        · exact absurd rfl hq1
        · exact hq_ass.1)).mp hsub
    rcases hp_mem with rfl | hp_ass
    · exact hm (IsLocalRing.maximalIdeal_eq_bot_of_le_pow_two hp_le)
    · have hp_prime : p.IsPrime := hp_ass.1
      have hp_eq : IsLocalRing.maximalIdeal R = p :=
        le_antisymm hp_le (IsLocalRing.le_maximalIdeal hp_prime.ne_top)
      exact hM (hp_eq ▸ hp_ass)
  obtain ⟨x, hx_mem, hx_not⟩ := Set.not_subset.mp h_not_subset
  refine ⟨x, hx_mem,
    fun hcon => hx_not (Set.mem_biUnion (Set.mem_insert _ _) hcon), ?_⟩
  by_contra h_not_reg
  have hx_union : x ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_zero_divisors R M]
    change ¬ Function.Injective (x • ·) at h_not_reg
    obtain ⟨y, z, heq, hyz⟩ := Function.not_injective_iff.mp h_not_reg
    exact ⟨y - z, sub_ne_zero.mpr hyz, by rw [smul_sub, heq, sub_self]⟩
  obtain ⟨p, hp_ass, hxp⟩ := Set.mem_iUnion₂.mp hx_union
  exact hx_not (Set.mem_biUnion (Set.mem_insert_of_mem _ hp_ass) hxp)

/-- Dimension shifting for the left term of a short exact sequence. -/
lemma Module.hasProjectiveDimensionLE_of_exact_sequence_left
    (R : Type u) [CommRing R]
    {M' M M'' : Type u} [AddCommGroup M'] [Module R M']
    [AddCommGroup M] [Module R M] [AddCommGroup M''] [Module R M'']
    {f : M' →ₗ[R] M} {g : M →ₗ[R] M''}
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hexact : LinearMap.range f = LinearMap.ker g)
    {n : ℕ} (hM : Module.HasProjectiveDimensionLE R n M)
    (hM'' : Module.HasProjectiveDimensionLE R (n + 1) M'') :
    Module.HasProjectiveDimensionLE R n M' := by
  have hcomp : ModuleCat.ofHom f ≫ ModuleCat.ofHom g = 0 := by
    ext x
    have hx : f x ∈ LinearMap.range f := LinearMap.mem_range_self f x
    rw [hexact] at hx
    exact LinearMap.mem_ker.mp hx
  let S := ShortComplex.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g) hcomp
  haveI : Mono S.f := (ModuleCat.mono_iff_injective _).mpr hf
  haveI : Epi S.g := (ModuleCat.epi_iff_surjective _).mpr hg
  have hS : S.ShortExact := ShortComplex.ShortExact.mk (by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact hexact)
  exact hS.hasProjectiveDimensionLT_X₁ (n + 1) hM hM''

/-- A Noetherian local ring is regular when its quotient by a regular element of the maximal
ideal is regular. -/
lemma IsRegularLocalRing.of_quotient_span_singleton
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hreg : IsSMulRegular R x)
    (hxm : x ∈ IsLocalRing.maximalIdeal R)
    [IsLocalRing (R ⧸ Ideal.span {x})]
    (hS : IsRegularLocalRing (R ⧸ Ideal.span {x})) :
    IsRegularLocalRing R := by
  classical
  obtain ⟨s, hs_span, hs_card⟩ := hS.maximalIdeal_generated_by_dim
  have hI_le : Ideal.span {x} ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hxm
  have h_map : (IsLocalRing.maximalIdeal R).map
      (Ideal.Quotient.mk (Ideal.span {x})) =
      IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x}) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have h_dim : ringKrullDim R = ((s.card + 1 : ℕ) : WithBot ℕ∞) := by
    have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hreg hxm
    rw [← hs_card] at h
    rw [← h]
    norm_cast
  have hf_spec : ∀ z : R ⧸ Ideal.span {x},
      Ideal.Quotient.mk (Ideal.span {x})
        (Ideal.Quotient.mk_surjective z).choose = z :=
    fun z => (Ideal.Quotient.mk_surjective z).choose_spec
  set t : Finset R := insert x
    (s.image fun z => (Ideal.Quotient.mk_surjective z).choose) with ht
  have h_span : Ideal.span (t : Set R) = IsLocalRing.maximalIdeal R := by
    apply le_antisymm
    · rw [Ideal.span_le, ht, Finset.coe_insert]
      rintro a (rfl | ha)
      · exact hxm
      · rw [Finset.coe_image] at ha
        obtain ⟨z, hz, rfl⟩ := ha
        have hz_mem : z ∈ IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x}) := by
          rw [← hs_span]
          exact Ideal.subset_span hz
        rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hunit
        have hz_unit : IsUnit z := by
          rw [← hf_spec z]
          exact hunit.map _
        exact (IsLocalRing.maximalIdeal.isMaximal
          (R ⧸ Ideal.span {x})).ne_top
          (Ideal.eq_top_of_isUnit_mem _ hz_mem hz_unit)
    · intro a ha
      have h1 : Ideal.Quotient.mk (Ideal.span {x}) a ∈ Ideal.map
          (Ideal.Quotient.mk (Ideal.span {x}))
          (Ideal.span ((s.image fun z =>
            (Ideal.Quotient.mk_surjective z).choose : Finset R) : Set R)) := by
        have himg : (Ideal.Quotient.mk (Ideal.span {x})) ''
            ((s.image fun z =>
              (Ideal.Quotient.mk_surjective z).choose : Finset R) : Set R) =
            (s : Set (R ⧸ Ideal.span {x})) := by
          ext w
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
          constructor
          · rintro ⟨-, ⟨z, hz, rfl⟩, rfl⟩
            rw [hf_spec z]
            exact hz
          · intro hw
            exact ⟨_, ⟨w, hw, rfl⟩, hf_spec w⟩
        rw [Ideal.map_span, himg, hs_span, ← h_map]
        exact Ideal.mem_map_of_mem _ ha
      obtain ⟨b, hb, hab⟩ :=
        (Ideal.mem_map_iff_of_surjective _
          Ideal.Quotient.mk_surjective).mp h1
      have hsub : a - b ∈ Ideal.span {x} := by
        rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
        exact hab.symm
      have haeq : a = b + (a - b) := by ring
      rw [haeq, ht]
      refine Ideal.add_mem _ ?_ ?_
      · refine Ideal.span_mono ?_ hb
        rw [Finset.coe_insert]
        exact Set.subset_insert _ _
      · refine Ideal.span_mono ?_ hsub
        rw [Finset.coe_insert]
        exact Set.singleton_subset_iff.mpr (Set.mem_insert _ _)
  have h_card_le : t.card ≤ s.card + 1 := by
    have h1 := Finset.card_insert_le x
      (s.image fun z => (Ideal.Quotient.mk_surjective z).choose)
    have h2 : (s.image fun z =>
      (Ideal.Quotient.mk_surjective z).choose).card ≤ s.card :=
      Finset.card_image_le
    rw [← ht] at h1
    omega
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have ht_le : (IsLocalRing.maximalIdeal R).spanFinrank ≤ t.card := by
    rw [← h_span]
    have h := Submodule.spanFinrank_span_le_ncard_of_finite
      (R := R) t.finite_toSet
    rwa [Set.ncard_coe_finset] at h
  have hle : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤
      ringKrullDim R := by
    rw [h_dim]
    exact_mod_cast ht_le.trans h_card_le
  exact_mod_cast hle

/-- Kaplansky's retract transfers a projective-dimension bound from `m/xm` to the residue field
of `R/(x)` when `x ∈ m \ m²`. -/
lemma Module.hasProjectiveDimensionLE_residueField_quotient_of_retract
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hxm : x ∈ IsLocalRing.maximalIdeal R)
    (hxm2 : x ∉ IsLocalRing.maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ Ideal.span {x})] {k : ℕ}
    (h : Module.HasProjectiveDimensionLE (R ⧸ Ideal.span {x}) k
      (QuotSMulTop x ↥(IsLocalRing.maximalIdeal R))) :
    Module.HasProjectiveDimensionLE (R ⧸ Ideal.span {x}) k
      (IsLocalRing.ResidueField (R ⧸ Ideal.span {x})) := by
  classical
  have hI_le : Ideal.span {x} ≤ IsLocalRing.maximalIdeal R := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hxm
  have hsurj : Function.Surjective
      (algebraMap R (R ⧸ Ideal.span {x})) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  set u : R →ₗ[R] QuotSMulTop x ↥(IsLocalRing.maximalIdeal R) :=
    (x • (⊤ : Submodule R ↥(IsLocalRing.maximalIdeal R))).mkQ ∘ₗ
      LinearMap.toSpanSingleton R ↥(IsLocalRing.maximalIdeal R) ⟨x, hxm⟩ with hu
  have hu_apply : ∀ r : R,
      u r = Submodule.Quotient.mk
        (r • (⟨x, hxm⟩ : ↥(IsLocalRing.maximalIdeal R))) := fun r => rfl
  have hu_ker : Ideal.span {x} ≤ LinearMap.ker u := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      LinearMap.mem_ker, hu_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ x ⊤ trivial
  set u' : (R ⧸ Ideal.span {x}) →ₗ[R]
      QuotSMulTop x ↥(IsLocalRing.maximalIdeal R) :=
    Submodule.liftQ (Ideal.span {x}) u hu_ker with hu'
  set u'' : (R ⧸ Ideal.span {x}) →ₗ[R ⧸ Ideal.span {x}]
      QuotSMulTop x ↥(IsLocalRing.maximalIdeal R) :=
    u'.extendScalarsOfSurjective hsurj with hu''
  have hu''_apply : ∀ r : R,
      u'' (Ideal.Quotient.mk (Ideal.span {x}) r) = u r := fun r => rfl
  have hker2 : IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x}) ≤
      LinearMap.ker u'' := by
    intro z hz
    rw [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk (Ideal.span {x}))
      Ideal.Quotient.mk_surjective] at hz
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hz
    rw [LinearMap.mem_ker, hu''_apply, hu_apply,
      Submodule.Quotient.mk_eq_zero]
    have hax : a • (⟨x, hxm⟩ : ↥(IsLocalRing.maximalIdeal R)) =
        x • ⟨a, ha⟩ := by
      ext
      simp [mul_comm]
    rw [hax]
    exact Submodule.smul_mem_pointwise_smul _ x ⊤ trivial
  set iota : IsLocalRing.ResidueField (R ⧸ Ideal.span {x})
      →ₗ[R ⧸ Ideal.span {x}]
      QuotSMulTop x ↥(IsLocalRing.maximalIdeal R) :=
    Submodule.liftQ (IsLocalRing.maximalIdeal (R ⧸ Ideal.span {x}))
      u'' hker2 with hiota
  have hxbar_ne : (IsLocalRing.maximalIdeal R).toCotangent ⟨x, hxm⟩ ≠ 0 :=
    fun hzero => hxm2 ((Ideal.toCotangent_eq_zero _ _).mp hzero)
  haveI : Module.Projective (IsLocalRing.ResidueField R)
      (IsLocalRing.CotangentSpace R) := Module.Projective.of_free
  obtain ⟨σ, hσ⟩ := Module.Projective.exists_dual_eq_one
    (IsLocalRing.ResidueField R) hxbar_ne
  have hg_ker : IsLocalRing.maximalIdeal R ≤ LinearMap.ker
      (Algebra.linearMap R
        (IsLocalRing.ResidueField (R ⧸ Ideal.span {x}))) := by
    intro a ha
    rw [LinearMap.mem_ker, Algebra.linearMap_apply,
      IsScalarTower.algebraMap_apply R (R ⧸ Ideal.span {x})
        (IsLocalRing.ResidueField (R ⧸ Ideal.span {x})),
      Ideal.Quotient.algebraMap_eq,
      IsLocalRing.ResidueField.algebraMap_eq,
      IsLocalRing.residue_eq_zero_iff,
      ← IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk (Ideal.span {x}))
        Ideal.Quotient.mk_surjective]
    exact Ideal.mem_map_of_mem _ ha
  set g : IsLocalRing.ResidueField R →ₗ[R]
      IsLocalRing.ResidueField (R ⧸ Ideal.span {x}) :=
    Submodule.liftQ (IsLocalRing.maximalIdeal R)
      (Algebra.linearMap R
        (IsLocalRing.ResidueField (R ⧸ Ideal.span {x}))) hg_ker with hg
  set rho0 : ↥(IsLocalRing.maximalIdeal R) →ₗ[R]
      IsLocalRing.ResidueField (R ⧸ Ideal.span {x}) :=
    g ∘ₗ (σ.restrictScalars R) ∘ₗ
      (IsLocalRing.maximalIdeal R).toCotangent with hrho0
  have hrho0_ker : x • (⊤ : Submodule R
      ↥(IsLocalRing.maximalIdeal R)) ≤ LinearMap.ker rho0 := by
    intro z hz
    obtain ⟨m', -, rfl⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists z x ⊤).mp hz
    have hcot : (IsLocalRing.maximalIdeal R).toCotangent (x • m') = 0 := by
      rw [Ideal.toCotangent_eq_zero]
      have hxm' : ((x • m' : ↥(IsLocalRing.maximalIdeal R)) : R) =
          x * (m' : R) := rfl
      rw [hxm', pow_two]
      exact Ideal.mul_mem_mul hxm m'.2
    rw [LinearMap.mem_ker, hrho0]
    simp only [LinearMap.coe_comp, Function.comp_apply, hcot, map_zero]
  set rho : QuotSMulTop x ↥(IsLocalRing.maximalIdeal R) →ₗ[R]
      IsLocalRing.ResidueField (R ⧸ Ideal.span {x}) :=
    Submodule.liftQ _ rho0 hrho0_ker with hrho
  set rho' : QuotSMulTop x ↥(IsLocalRing.maximalIdeal R)
      →ₗ[R ⧸ Ideal.span {x}]
      IsLocalRing.ResidueField (R ⧸ Ideal.span {x}) :=
    rho.extendScalarsOfSurjective hsurj with hrho'
  have hcomp : ∀ z, rho' (iota z) = z := by
    intro z
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective w
    have h1 : iota (Submodule.Quotient.mk
        (Ideal.Quotient.mk (Ideal.span {x}) r)) =
        Submodule.Quotient.mk
          (r • (⟨x, hxm⟩ : ↥(IsLocalRing.maximalIdeal R))) := rfl
    have h2 : rho' (Submodule.Quotient.mk
        (r • (⟨x, hxm⟩ : ↥(IsLocalRing.maximalIdeal R)))) =
        g ((σ.restrictScalars R)
          ((IsLocalRing.maximalIdeal R).toCotangent
            (r • (⟨x, hxm⟩ : ↥(IsLocalRing.maximalIdeal R))))) := rfl
    have h3 : (σ.restrictScalars R)
        ((IsLocalRing.maximalIdeal R).toCotangent ⟨x, hxm⟩) = 1 := hσ
    rw [h1, h2, map_smul, map_smul, h3, map_smul]
    have h4 : g 1 = 1 := map_one
      (algebraMap R
        (IsLocalRing.ResidueField (R ⧸ Ideal.span {x})))
    rw [h4, ← Algebra.algebraMap_eq_smul_one,
      IsScalarTower.algebraMap_apply R (R ⧸ Ideal.span {x})
        (IsLocalRing.ResidueField (R ⧸ Ideal.span {x})),
      Ideal.Quotient.algebraMap_eq,
      IsLocalRing.ResidueField.algebraMap_eq]
    rfl
  have hcomp' : ModuleCat.ofHom iota ≫ ModuleCat.ofHom rho' =
      𝟙 (ModuleCat.of (R ⧸ Ideal.span {x})
        (IsLocalRing.ResidueField (R ⧸ Ideal.span {x}))) := by
    ext z
    exact hcomp z
  let ret : Retract
      (ModuleCat.of (R ⧸ Ideal.span {x})
        (IsLocalRing.ResidueField (R ⧸ Ideal.span {x})))
      (ModuleCat.of (R ⧸ Ideal.span {x})
        (QuotSMulTop x ↥(IsLocalRing.maximalIdeal R))) :=
    { i := ModuleCat.ofHom iota
      r := ModuleCat.ofHom rho'
      retract := hcomp' }
  haveI : HasProjectiveDimensionLT
      (ModuleCat.of (R ⧸ Ideal.span {x})
        (QuotSMulTop x ↥(IsLocalRing.maximalIdeal R))) (k + 1) := h
  exact ret.hasProjectiveDimensionLT (k + 1)

/-- A Noetherian local ring whose residue field has finite projective dimension is regular.
This is the difficult implication in Stacks Project tag `00OC`. -/
theorem IsRegularLocalRing.of_hasProjectiveDimensionLE_residueField :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsLocalRing R]
      [IsNoetherianRing R],
      Module.HasProjectiveDimensionLE R n (IsLocalRing.ResidueField R) →
        IsRegularLocalRing R := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro R _ _ _ hpd
    classical
    haveI : Module.Finite R (IsLocalRing.ResidueField R) :=
      Module.Finite.of_surjective (IsLocalRing.maximalIdeal R).mkQ
        (Submodule.mkQ_surjective _)
    by_cases h0 : Module.HasProjectiveDimensionLE R 0
        (IsLocalRing.ResidueField R)
    · haveI : Module.Projective R (IsLocalRing.ResidueField R) :=
        (Module.hasProjectiveDimensionLE_zero_iff_projective R _).mp h0
      haveI : Module.FinitePresentation R (IsLocalRing.ResidueField R) :=
        Module.finitePresentation_of_finite R _
      haveI : Module.Flat R (IsLocalRing.ResidueField R) :=
        Module.Flat.of_projective
      haveI : Module.Free R (IsLocalRing.ResidueField R) :=
        Module.free_of_flat_of_isLocalRing
      haveI : Nontrivial (IsLocalRing.ResidueField R) :=
        Submodule.Quotient.nontrivial_iff.mpr
          (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      have hm_bot : IsLocalRing.maximalIdeal R = ⊥ := by
        rw [eq_bot_iff]
        intro a ha
        obtain ⟨i⟩ :=
          (Module.Free.chooseBasis R
            (IsLocalRing.ResidueField R)).index_nonempty
        have hkill : a • Module.Free.chooseBasis R
            (IsLocalRing.ResidueField R) i = 0 := by
          obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective
            (Module.Free.chooseBasis R (IsLocalRing.ResidueField R) i)
          rw [← hr]
          change IsLocalRing.residue R (a * r) = 0
          rw [IsLocalRing.residue_eq_zero_iff]
          exact Ideal.mul_mem_right r _ ha
        have hrepr := congrArg
          (Module.Free.chooseBasis R
            (IsLocalRing.ResidueField R)).repr hkill
        rw [map_smul, Module.Basis.repr_self, map_zero] at hrepr
        have hi := DFunLike.congr_fun hrepr i
        rw [Submodule.mem_bot]
        simpa using hi
      have hdim0 : ringKrullDim R = 0 :=
        IsLocalRing.ringKrullDim_eq_zero_of_maximalIdeal_le_pow_two
          (by rw [hm_bot]; exact bot_le)
      apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
      rw [hm_bot, Submodule.spanFinrank_bot, hdim0]
      rfl
    · have hEx : ∃ k : ℕ, Module.HasProjectiveDimensionLE R k
          (IsLocalRing.ResidueField R) := ⟨n, hpd⟩
      obtain ⟨e', he'⟩ : ∃ e', Nat.find hEx = e' + 1 :=
        ⟨Nat.find hEx - 1, by
          have hn0 : Nat.find hEx ≠ 0 :=
            fun hz => h0 (hz ▸ Nat.find_spec hEx)
          omega⟩
      have hle : Module.HasProjectiveDimensionLE R (e' + 1)
          (IsLocalRing.ResidueField R) := he' ▸ Nat.find_spec hEx
      have hnot : ¬ Module.HasProjectiveDimensionLE R e'
          (IsLocalRing.ResidueField R) := fun hcon => by
        have hmin := Nat.find_min' hEx hcon
        omega
      have he_le_n : e' + 1 ≤ n := he' ▸ Nat.find_min' hEx hpd
      have hAssR : IsLocalRing.maximalIdeal R ∉ associatedPrimes R R :=
        Module.maximalIdeal_not_mem_associatedPrimes_of_residueField_projectiveDimension
          hle hnot
      have hm_ne_bot : IsLocalRing.maximalIdeal R ≠ ⊥ := by
        intro hbot
        apply h0
        haveI : Module.Free R (IsLocalRing.ResidueField R) :=
          Module.Free.of_equiv (Submodule.quotEquivOfEqBot _ hbot).symm
        exact (Module.hasProjectiveDimensionLE_zero_iff_projective R _).mpr
          Module.Projective.of_free
      obtain ⟨x, hxm, hxm2, hregR⟩ :=
        IsLocalRing.exists_notMem_pow_two_isSMulRegular R hAssR hm_ne_bot
      have hx_nzd : x ∈ nonZeroDivisors R := by
        refine mem_nonZeroDivisors_iff.mpr ⟨fun z hz => ?_, fun z hz => ?_⟩
        · have hzz : x • z = x • (0 : R) := by
            rw [smul_eq_mul, smul_eq_mul, mul_zero]
            exact hz
          exact hregR hzz
        · have hzz : x • z = x • (0 : R) := by
            rw [smul_eq_mul, smul_eq_mul, mul_zero, mul_comm]
            exact hz
          exact hregR hzz
      haveI : Nontrivial (R ⧸ Ideal.span {x}) :=
        Submodule.Quotient.nontrivial_iff.mpr fun htop =>
          (IsLocalRing.maximalIdeal.isMaximal R).ne_top
            (top_le_iff.mp (htop ▸ Ideal.span_le.mpr (by simpa using hxm)))
      haveI : IsLocalRing (R ⧸ Ideal.span {x}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
          Ideal.Quotient.mk_surjective
      have hR_pd : Module.HasProjectiveDimensionLE R e' R := by
        haveI : HasProjectiveDimensionLT (ModuleCat.of R R) 1 :=
          CategoryTheory.projective_iff_hasProjectiveDimensionLT_one.mp inferInstance
        exact CategoryTheory.hasProjectiveDimensionLT_of_ge
          (ModuleCat.of R R) 1 (e' + 1) (by omega)
      have hpd_m : Module.HasProjectiveDimensionLE R e'
          ↥(IsLocalRing.maximalIdeal R) :=
        Module.hasProjectiveDimensionLE_of_exact_sequence_left R
          (Submodule.injective_subtype (IsLocalRing.maximalIdeal R))
          (Submodule.mkQ_surjective _)
          (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hR_pd hle
      haveI : Module.Finite R ↥(IsLocalRing.maximalIdeal R) :=
        Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
      have hreg_m : IsSMulRegular ↥(IsLocalRing.maximalIdeal R) x :=
        hregR.submodule _ x
      have hpd_q : Module.HasProjectiveDimensionLE
          (R ⧸ Ideal.span {x}) e'
          (QuotSMulTop x ↥(IsLocalRing.maximalIdeal R)) :=
        Module.HasProjectiveDimensionLE.quotSMulTop hx_nzd
          ↥(IsLocalRing.maximalIdeal R) hreg_m hpd_m
      have hpd_kS : Module.HasProjectiveDimensionLE
          (R ⧸ Ideal.span {x}) e'
          (IsLocalRing.ResidueField (R ⧸ Ideal.span {x})) :=
        Module.hasProjectiveDimensionLE_residueField_quotient_of_retract
          hxm hxm2 hpd_q
      have hSreg : IsRegularLocalRing (R ⧸ Ideal.span {x}) :=
        ih e' (by omega) (R ⧸ Ideal.span {x}) hpd_kS
      exact IsRegularLocalRing.of_quotient_span_singleton hregR hxm hSreg
